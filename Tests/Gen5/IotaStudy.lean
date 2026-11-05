import Lean
import Sparkle
import Tests.AllTests
/-! # Recursors as iota rules: what `RecursorVal.rules` gives (D.D-4, issue sparkle-ledger-dd4-res)
Measurement only. For the recursors of the sample residue, print the data an iota rule is built from
(`numParams/numIndices/numMotives/numMinors/k`, the rules `(ctor, nfields, rhs)`), the sort the motive
ranges over, and whether the major premise is a proposition. Output: `logInfo` aggregates; raw rows go to
`$KJOB_REPORT_PATH.iota` if set. No theorem, no sorry. -/
open Lean Meta Elab Command

namespace Tests.Gen5.IotaStudy

def recNames : List Name :=
  [`Nat.rec, `Bool.rec, `Eq.rec, `False.rec, `Decidable.rec, `Nat.le.rec, `List.rec, `BitVec.rec,
   `PSigma.rec, `Prod.rec, `Int.rec, `And.rec, `Or.rec, `Exists.rec, `Option.rec, `Fin.rec, `Unit.rec, `PUnit.rec,
   `Sum.rec, `Sigma.rec, `Subtype.rec, `HEq.rec, `Acc.rec, `WellFounded.rec]

/-- Sort of the motive: the result sort of the type of the first motive binder. -/
def motiveSort (rv : RecursorVal) : MetaM String := do
  forallTelescope rv.type fun xs _ => do
    let i := rv.numParams
    if h : i < xs.size then
      let mty ← inferType xs[i]
      forallTelescope mty fun _ r => do
        return toString (← ppExpr r)
    else return "?"

elab "#iota_study" : command => do
  let env ← getEnv
  let mut msg := ""
  let mut raw := ""
  for n in recNames do
    match env.find? n with
    | some (.recInfo rv) =>
      let ms ← liftTermElabM (motiveSort rv)
      let ind := rv.getMajorInduct
      let isProp ← liftTermElabM do
        let some (.inductInfo iv) := env.find? ind | return "?"
        forallTelescope iv.type fun _ r => return toString (← ppExpr r)
      let rs := rv.rules.map fun r => s!"{r.ctor}/{r.nfields}"
      let line := s!"{n}: params={rv.numParams} indices={rv.numIndices} motives={rv.numMotives} minors={rv.numMinors} k={rv.k} lvls={rv.levelParams} motiveSort={ms} majorInductSort={isProp} rules={rs}"
      msg := msg ++ line ++ "\n"
      raw := raw ++ line ++ "\n"
      for r in rv.rules do
        let rhs ← liftTermElabM (do return toString (← ppExpr r.rhs))
        raw := raw ++ s!"  rule {r.ctor} nfields={r.nfields}: {rhs}\n"
    | _ => msg := msg ++ s!"{n}: not a recursor in this environment\n"
  logInfo msg
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    IO.FS.writeFile (path ++ ".iota") raw

#iota_study

/-! ## Probe: does the syntactic iota step (`Tools.ShippingGen5IotaDraft.IotaStep`) fire on the unfolded corpus?
`red` applies exactly the rules of the draft to an OPEN term (the parameters of a root are loose bvars): unfold of a `defnInfo`
spine (syntactic beta), iota when the major is a constructor application or a Nat literal, projection of a constructor.
A recursor whose major is anything else is STUCK; its major class is recorded.  Fuel-bounded per root. -/
structure St where
  fuel : Nat
  fired : Nat := 0
  outOfFuel : Bool := false
  stuck : Std.HashMap String Nat := {}
  firedBy : Std.HashMap String Nat := {}

abbrev M := StateM St

def majorShape (e : Expr) : String :=
  match e.getAppFn with
  | .bvar _ => if e.isApp then "stuck:bvar-app" else "stuck:bvar"
  | .const c _ => s!"stuck:const-app"
  | .proj .. => "stuck:proj"
  | .lam .. => "stuck:lambda"
  | .lit _ => "stuck:lit"
  | _ => "stuck:other"

partial def red (env : Environment) (e : Expr) : M Expr := do
  let st ← get
  if st.fuel == 0 then
    modify fun s => { s with outOfFuel := true }
    return e
  modify fun s => { s with fuel := s.fuel - 1 }
  match e with
  | .mdata _ b => red env b
  | .lam n t b bi => return .lam n t (← red env b) bi
  | .letE n t v b nd => return .letE n t (← red env v) (← red env b) nd
  | .forallE .. | .sort _ | .bvar _ | .lit _ | .fvar _ | .mvar _ => return e
  | .proj s i b =>
    let b' ← red env b
    match b'.getAppFn with
    | .const c _ =>
      match env.find? c with
      | some (.ctorInfo cv) =>
        if cv.numParams + i < b'.getAppNumArgs then
          red env (b'.getAppArgs[cv.numParams + i]!)
        else return .proj s i b'
      | _ => return .proj s i b'
    | _ => return .proj s i b'
  | .const c ls =>
    match env.find? c with
    | some (.defnInfo d) => red env (d.value.instantiateLevelParams d.levelParams ls)
    | _ => return e
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c ls =>
      match env.find? c with
      | some (.thmInfo _) => return e
      | some (.defnInfo d) =>
        red env ((d.value.instantiateLevelParams d.levelParams ls).beta args)
      | some (.recInfo rv) =>
        let mi := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices
        if h : mi < args.size then
          let major ← red env args[mi]
          -- constructor application or Nat literal
          let mj : Option (Name × Array Expr) :=
            match major with
            | .lit (.natVal 0) => some (``Nat.zero, #[])
            | .lit (.natVal (k+1)) => some (``Nat.succ, #[.lit (.natVal k)])
            | _ => match major.getAppFn with
                   | .const cn _ => match env.find? cn with
                       | some (.ctorInfo cv) => some (cn, major.getAppArgs.extract cv.numParams major.getAppNumArgs)
                       | _ => none
                   | _ => none
          match mj with
          | some (cn, fields) =>
            match rv.rules.find? (·.ctor == cn) with
            | some rule =>
              modify fun s => { s with fired := s.fired + 1, firedBy := s.firedBy.insert rv.name.toString (s.firedBy.getD rv.name.toString 0 + 1) }
              let params := args.extract 0 rv.numParams
              let mm := args.extract rv.numParams (rv.numParams + rv.numMotives + rv.numMinors)
              let extra := args.extract (mi + 1) args.size
              red env (mkAppN ((rule.rhs.instantiateLevelParams rv.levelParams ls).beta (params ++ mm ++ fields)) extra)
            | none =>
              modify fun s => { s with stuck := s.stuck.insert "stuck:ctor-without-rule" (s.stuck.getD "stuck:ctor-without-rule" 0 + 1) }
              return e
          | none =>
            let k := majorShape major
            modify fun s => { s with stuck := s.stuck.insert k (s.stuck.getD k 0 + 1) }
            let mut out := #[]
            for a in args do out := out.push (← red env a)
            return mkAppN f (out.set! mi major)
        else
          modify fun s => { s with stuck := s.stuck.insert "stuck:under-applied" (s.stuck.getD "stuck:under-applied" 0 + 1) }
          return e
      | _ =>
        let mut out := #[]
        for a in args do out := out.push (← red env a)
        return mkAppN f out
    | _ =>
      let f' ← red env f
      let mut out := #[]
      for a in args do out := out.push (← red env a)
      -- head became a lambda after reduction: beta
      return (mkAppN f' out).headBeta

elab "#iota_probe" : command => do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let .str p "machine_source" := n then
      if (env.find? p).any (·.isDefinition) then roots := roots.push p
  roots := roots.qsort (fun a b => a.toString < b.toString)
  let mut tot : St := { fuel := 0 }
  let mut done := 0
  let mut oof := 0
  let mut rootsStuck := 0
  let mut raw := ""
  for r in roots.toList.take 30 do
    let (_, st) := (red env (.const r []) : M Expr).run { fuel := 400000 }
    done := done + 1
    if st.outOfFuel then oof := oof + 1
    if st.stuck.toList.any (fun (_, v) => v > 0) then rootsStuck := rootsStuck + 1
    tot := { tot with fired := tot.fired + st.fired }
    for (k, v) in st.stuck.toList do tot := { tot with stuck := tot.stuck.insert k (tot.stuck.getD k 0 + v) }
    for (k, v) in st.firedBy.toList do tot := { tot with firedBy := tot.firedBy.insert k (tot.firedBy.getD k 0 + v) }
    raw := raw ++ s!"{r}\tfired={st.fired}\toutOfFuel={st.outOfFuel}\tstuck={st.stuck.toList}\tfiredBy={st.firedBy.toList}\n"
  logInfo s!"IOTA PROBE over {done} machine roots (first 30 by name; fuel 400000 reduction steps each; out of fuel: {oof}; roots with a stuck recursor site: {rootsStuck})\niota fired: {tot.fired} by {tot.firedBy.toList}\nstuck recursor sites by major shape: {tot.stuck.toList}"
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    IO.FS.writeFile (path ++ ".iotaprobe") raw

#iota_probe

end Tests.Gen5.IotaStudy
