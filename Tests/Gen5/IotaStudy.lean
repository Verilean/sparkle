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
A recursor whose major is anything else is STUCK; its major class is recorded.
Revision 2 (reviewer: the 30-root probe ran out of fuel on every root, so its numbers were only a trend):
* **fuel exhaustion is a FAILURE of the root** (`ExceptT`): a root that runs out of fuel contributes NOTHING to the counts and is
  listed by name; there is no partial result;
* the kernel's Nat-literal acceleration is part of the reduction: `Nat.add/sub/mul/div/mod/pow/gcd/land/lor/xor/shiftLeft/shiftRight/log2`
  on two literals, `Nat.beq/ble` (to `Bool` constants), `Nat.decEq/decLt/decLe` (to `Decidable.isTrue/isFalse` of an opaque proof
  placeholder), `Nat.succ` of a literal.  Without it `2^256`-style widths unfold through `Nat.rec` one step at a time;
* `red` is a pure function of the term, so results are memoised per distinct term (also open terms): the counts below are per
  DISTINCT reduced term, not per dynamic occurrence.
No axiom, no sorry; the proof placeholder is only an `Expr` constant name in a measurement. -/
structure St where
  fuel : Nat
  steps : Nat := 0
  fired : Nat := 0
  stuck : Std.HashMap String Nat := {}
  firedBy : Std.HashMap String Nat := {}
  natAccel : Nat := 0
  cache : Std.HashMap Expr Expr := {}

abbrev M := ExceptT String (StateM St)

def tick : M Unit := do
  let st ← get
  if st.fuel == 0 then throw "out of fuel"
  set { st with fuel := st.fuel - 1, steps := st.steps + 1 }

def bump (k : String) : M Unit :=
  modify fun s => { s with stuck := s.stuck.insert k (s.stuck.getD k 0 + 1) }

def majorShape (e : Expr) : String :=
  match e.getAppFn with
  | .bvar _ => if e.isApp then "stuck:bvar-app" else "stuck:bvar"
  | .const _ _ => s!"stuck:const-app"
  | .proj .. => "stuck:proj"
  | .lam .. => "stuck:lambda"
  | .lit _ => "stuck:lit"
  | _ => "stuck:other"

def natBin? (c : Name) : Option (Nat → Nat → Nat) :=
  if c == ``Nat.add then some Nat.add else if c == ``Nat.sub then some Nat.sub
  else if c == ``Nat.mul then some Nat.mul else if c == ``Nat.div then some Nat.div
  else if c == ``Nat.mod then some Nat.mod else if c == ``Nat.pow then some Nat.pow
  else if c == ``Nat.gcd then some Nat.gcd else if c == ``Nat.land then some Nat.land
  else if c == ``Nat.lor then some Nat.lor else if c == ``Nat.xor then some Nat.xor
  else if c == ``Nat.shiftLeft then some Nat.shiftLeft else if c == ``Nat.shiftRight then some Nat.shiftRight
  else none

def natCmp? (c : Name) : Option (Nat → Nat → Bool) :=
  if c == ``Nat.beq then some (· == ·) else if c == ``Nat.ble then some Nat.ble else none

def natDec? (c : Name) : Option (Nat → Nat → Bool) :=
  if c == ``Nat.decEq then some (· == ·) else if c == ``Nat.decLt then some (· < ·)
  else if c == ``Nat.decLe then some (· ≤ ·) else none

def boolE (b : Bool) : Expr := .const (if b then ``Bool.true else ``Bool.false) []

/-- Kernel Nat acceleration: `c` applied to (reduced) literals. -/
def natAccelStep (c : Name) (args : Array Expr) : Option Expr :=
  if args.size == 2 then
    match args[0]!, args[1]! with
    | .lit (.natVal a), .lit (.natVal b) =>
      match natBin? c with
      | some f => some (.lit (.natVal (f a b)))
      | none =>
        match natCmp? c with
        | some f => some (boolE (f a b))
        | none =>
          match natDec? c with
          | some f =>
            let pf := Expr.const `Tests.Gen5.IotaStudy.opaqueProof []
            if f a b then some (mkApp2 (.const ``Decidable.isTrue []) (.sort levelZero) pf)
            else some (mkApp2 (.const ``Decidable.isFalse []) (.sort levelZero) pf)
          | none => none
    | _, _ => none
  else if args.size == 1 && c == ``Nat.succ then
    match args[0]! with
    | .lit (.natVal a) => some (.lit (.natVal (a + 1)))
    | _ => none
  else if args.size == 1 && c == ``Nat.log2 then
    match args[0]! with
    | .lit (.natVal a) => some (.lit (.natVal (Nat.log2 a)))
    | _ => none
  else none

mutual
partial def red (env : Environment) (e : Expr) : M Expr := do
  if let some r := (← get).cache[e]? then return r
  tick
  let r ← redCore env e
  modify fun s => { s with cache := s.cache.insert e r }
  return r

partial def redArgs (env : Environment) (args : Array Expr) : M (Array Expr) := do
  let mut out := #[]
  for a in args do out := out.push (← red env a)
  return out

partial def redCore (env : Environment) (e : Expr) : M Expr := do
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
      -- kernel Nat acceleration first
      let isAcc := (natBin? c).isSome || (natCmp? c).isSome || (natDec? c).isSome || c == ``Nat.succ || c == ``Nat.log2
      let accRes : Option Expr ← if isAcc then
          do let a' ← redArgs env args
             match natAccelStep c a' with
             | some r => (modify fun s => { s with natAccel := s.natAccel + 1 }); pure (some r)
             | none => pure none
        else pure none
      if let some r := accRes then return r
      match env.find? c with
      | some (.thmInfo _) => return e
      | some (.defnInfo d) =>
        red env ((d.value.instantiateLevelParams d.levelParams ls).beta args)
      | some (.recInfo rv) =>
        let mi := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices
        if h : mi < args.size then
          let major ← red env args[mi]
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
              bump "stuck:ctor-without-rule"
              return e
          | none =>
            bump (majorShape major)
            let out ← redArgs env args
            return mkAppN f (out.set! mi major)
        else
          bump "stuck:under-applied"
          return e
      | _ => return mkAppN f (← redArgs env args)
    | _ =>
      let f' ← red env f
      let out ← redArgs env args
      return (mkAppN f' out).headBeta
end

/-- Roots of the probe: `PRIM_PROBE_ROOTS` (a file, one definition per line) if set, else every `X.machine_source`. -/
def probeRoots (env : Environment) : IO (Array Name) := do
  if let some f ← IO.getEnv "PRIM_PROBE_ROOTS" then
    let mut r := #[]
    for l in ← IO.FS.lines f do
      let l := l.trimAscii.toString
      if !l.isEmpty && (env.find? l.toName).any (·.isDefinition) then r := r.push l.toName
    return r.qsort (fun a b => a.toString < b.toString)
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let .str p "machine_source" := n then
      if (env.find? p).any (·.isDefinition) then roots := roots.push p
  return roots.qsort (fun a b => a.toString < b.toString)

elab "#iota_probe" fuel:num take:num : command => do
  let env ← getEnv
  let roots := (← liftIO (probeRoots env))
  let roots := if take.getNat == 0 then roots else roots.extract 0 take.getNat
  let mut tot : St := { fuel := 0 }
  let mut finished := 0
  let mut failed : Array String := #[]
  let mut rootsStuck := 0
  let mut raw := ""
  for r in roots.toList do
    let (res, st) := (red env (.const r []) : M Expr).run.run { fuel := fuel.getNat }
    match res with
    | .error msg =>
      failed := failed.push r.toString
      raw := raw ++ s!"{r}\tFAILED({msg}) after {st.steps} steps\n"
    | .ok _ =>
      finished := finished + 1
      if st.stuck.toList.any (fun (_, v) => v > 0) then rootsStuck := rootsStuck + 1
      tot := { tot with fired := tot.fired + st.fired, steps := tot.steps + st.steps, natAccel := tot.natAccel + st.natAccel }
      for (k, v) in st.stuck.toList do tot := { tot with stuck := tot.stuck.insert k (tot.stuck.getD k 0 + v) }
      for (k, v) in st.firedBy.toList do tot := { tot with firedBy := tot.firedBy.insert k (tot.firedBy.getD k 0 + v) }
      raw := raw ++ s!"{r}\tOK steps={st.steps}\tfired={st.fired}\tnatAccel={st.natAccel}\tstuck={st.stuck.toList}\tfiredBy={st.firedBy.toList}\n"
  logInfo s!"IOTA PROBE: {roots.size} roots, fuel {fuel.getNat} reduction steps each. FINISHED within fuel: {finished}; FAILED (out of fuel, no partial result): {failed.size}; finished roots with a stuck recursor site: {rootsStuck}\nfailed roots: {failed.toList}\nover the FINISHED roots only (per distinct reduced term): steps {tot.steps}, Nat-literal accelerations {tot.natAccel}, iota fired {tot.fired} by {tot.firedBy.toList}\nstuck recursor sites by major shape: {tot.stuck.toList}"
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    IO.FS.writeFile (path ++ ".iotaprobe") raw

end Tests.Gen5.IotaStudy
