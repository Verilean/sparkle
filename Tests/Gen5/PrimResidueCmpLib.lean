import Lean
import Sparkle
import Tools.ShippingGen5ConstValueELS
import Tests.Gen5.PrimResidueKeyLib
import Tests.Gen5.PrimResidueStopLib
import Tests.Gen5.PrimResidueTraceLib
/-! # Carrier comparison (issue sparkle-ledger-dd4-final, Q-A (ii)): shared measurement
Measurement only. Same traversal, roots, stages and residue as `PrimResidueTrace` (unchanged, reused: `traceReach`, `stopAt`). For every residue key and every
stopped key, at every stage, the declared type (instantiated at the key's levels) gets a PROFILE, so that each carrier extension can be counted on the real keys:
* `need`: the least `k` such that `Dyn.{k}` (`ty : Type k`) holds every non-erasable binder and the result (binder `x : t` with `t : Sort s`, `s ≥ 1`, needs `k ≥ s - 1`;
  a type binder `α : Sort l` is the same with `s := l`); `0` is today's `Dyn`. `nEra`: the number of binders whose sort is `Prop` (proofs, `p : Prop`), erased by a Prop rule;
  `resEra`: the result is Prop-sorted. `sym`: a level that is not a numeral (never expected: levels are closed).
* row-obligation shape classes on the instantiated declared type (syntactic, no unfolding): codomain class `R0` (no binder, constant result) / `R1` (constant result without loose bvars)
  / `R2` (`D (bvar n-1)`: a type former applied to the FIRST binder, the shape of `rowTypedAtV_depFirst`) / `R3a` (a type former applied to bound variables only, e.g. `Signal dom α`: the generalization of `R2` to several binders) / `R1x` (closed result, not a constant) / `R3v` (the result is a bound variable: a type variable, e.g. `Prod.snd : β`) / `R3p` (the result is itself a Pi) / `R3c` (constant head with some argument that is not a bound variable, e.g. `Inhabited (BitVec n)`) / `R3` (the head is a bound variable, e.g. `f α`, `motive t`);
  telescope class `T0` (no binder) / `T1` (every binder a bare constant, nothing depends on a binder: the shape of `ConstPi`) / `T2` (closed, but some binder is not a bare constant)
  / `T3` (some binder or the result depends on an earlier binder).
* recursor occurrences: in the unfolded body of every reached, non-stopped definition, an application of a recursor whose MAJOR premise is a constructor application / literal / bound variable / other
  (as written in the body, before the caller's arguments are substituted: an UPPER-bound style estimate for an iota rule restricted to constructors).
Fuel exhausted => `throwError`. No axiom, no sorry, no theorem.
Raw rows: `$KJOB_REPORT_PATH.cmpkeys.<tag>` (stage, name, kind, lvl, roots, profile), `.cmpstopped.<tag>` (stage, name, lvl, roots, dyn verdict, profile), `.cmprec.<tag>` (stage, node, recursor, major class), `.cmpclos.<tag>` (stage, name, kind, lvl, in the residue of that stage / extra: the residue constants in the declared types of the stopped definitions). -/
open Lean Meta Elab Command
open Tests.Gen5.PrimResidueKey
open Tests.Gen5.PrimResidueTrace
open Tests.Gen5.PrimResidueStop (dynFit)
open Tools.ShippingGen5ConstValueE (LS)

namespace Tests.Gen5.PrimResidueCmp

partial def evalLvl : Level → Option Nat
  | .zero => some 0
  | .succ l => (evalLvl l).map (· + 1)
  | .max a b => do let x ← evalLvl a; let y ← evalLvl b; pure (max x y)
  | .imax a b => do let x ← evalLvl a; let y ← evalLvl b; pure (if y == 0 then 0 else max x y)
  | _ => none

/-- (tag, need): tag 0 fits `Dyn.{need}`, 1 Prop-sorted (erasable by a Prop rule), 2 level not a numeral / no sort -/
def classOf (t0 : Expr) : MetaM (Nat × Nat) := do
  let t ← whnf t0
  let lv? : Option Level ← match t with
    | .sort l => pure (some l.normalize)
    | _ => do match ← whnf (← inferType t) with | .sort s => pure (some s.normalize) | _ => pure none
  match lv? with
  | none => pure (2, 0)
  | some l => match evalLvl l with
    | none => pure (2, 0)
    | some 0 => pure (1, 0)
    | some n => pure (0, n - 1)

def shapeClasses (ty : Expr) : String × String :=
  let rec go (e : Expr) (doms : Array Expr) : Array Expr × Expr :=
    match e with
    | .forallE _ d b _ => go b (doms.push d)
    | _ => (doms, e)
  let (doms, r) := go ty #[]
  let n := doms.size
  let anyDep := doms.any (·.hasLooseBVars) || r.hasLooseBVars
  let allConst := doms.all (·.isConst)
  let rc :=
    if n == 0 then (if r.isConst then "R0" else "R0x")
    else if !r.hasLooseBVars && r.isConst then "R1"
    else
      let args := r.getAppArgs
      if r.getAppFn.isConst && args.size > 0 && args.all (·.isBVar) then
        (match args[0]! with
         | .bvar i => if args.size == 1 && i + 1 == n then "R2" else "R3a"
         | _ => "R3a")
      else if !r.hasLooseBVars then "R1x"
      else if r.isBVar then "R3v"
      else if r.isForall then "R3p"
      else if r.getAppFn.isConst then "R3c"
      else "R3"
  let tc := if n == 0 then "T0" else if !anyDep && allConst then "T1" else if !anyDep then "T2" else "T3"
  (rc, tc)

/-- profile row (tab separated): need, sym, nEra, resEra, arity, nTy, R-class, T-class -/
def profileOf (c : Name) (ls : List Level) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? c | return "nodecl"
  if ls.length != ci.levelParams.length || ls.any (fun l => l.hasParam || l.hasMVar) then return "badlevels"
  let ty := ci.type.instantiateLevelParams ci.levelParams ls
  let (rc, tc) := shapeClasses ty
  forallTelescope ty fun xs r => do
    let mut need := 0
    let mut sym := false
    let mut nEra := 0
    let mut nTy := 0
    for x in xs do
      let t ← inferType x
      if (← whnf t).isSort then nTy := nTy + 1
      match ← classOf t with
      | (0, n) => need := max need n
      | (1, _) => nEra := nEra + 1
      | _ => sym := true
    let mut resEra := false
    match ← classOf r with
    | (0, n) => need := max need n
    | (1, _) => resEra := true
    | _ => sym := true
    return s!"{need}\t{sym}\t{nEra}\t{resEra}\t{xs.size}\t{nTy}\t{rc}\t{tc}"

def majorClass (env : Environment) (m0 : Expr) : String :=
  let m := m0.consumeMData
  match m.getAppFn with
  | .const n _ => (match env.find? n with | some (.ctorInfo _) => "ctor" | _ => "const")
  | .lit _ => "lit"
  | .bvar _ => "bvar"
  | .lam .. => "lam"
  | _ => "other"

partial def recOccs (env : Environment) (e : Expr) (acc : Array (Name × String)) : Array (Name × String) :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n _ =>
      if (env.find? n).any (·.isTheorem) then acc
      else
        let acc := match env.find? n with
          | some (.recInfo rv) =>
            let mi := rv.getMajorIdx
            acc.push (n, if args.size > mi then majorClass env args[mi]! else "partial")
          | _ => acc
        args.foldl (fun a x => recOccs env x a) acc
    | _ => args.foldl (fun a x => recOccs env x a) (recOccs env f acc)
  | .lam _ t b _ | .forallE _ t b _ => recOccs env b (recOccs env t acc)
  | .letE _ t v b _ => recOccs env b (recOccs env v (recOccs env t acc))
  | .mdata _ b | .proj _ _ b => recOccs env b acc
  | _ => acc

/-- the residue constants (kind /= none) in the closure of the DECLARED TYPE of `(c, ls)`: constants of the type, and (for definitions) of their unfolded bodies. These are the type formers a row for `c` needs in `hty`. -/
def typeClosure (env : Environment) (c : Name) (ls : List Level) (fuel0 : Nat) : Array (Name × List Level) × Nat := Id.run do
  let some ci := env.find? c | return (#[], 0)
  if ls.length != ci.levelParams.length then return (#[], 0)
  let ty := ci.type.instantiateLevelParams ci.levelParams ls
  let mut seen : Std.HashSet (Name × String) := {}
  let mut todo : Array (Name × List Level) := #[]
  let mut out : Array (Name × List Level) := #[]
  for (n, nl) in occs env ty #[] do
    if !seen.contains (n, lvlKey nl) then seen := seen.insert (n, lvlKey nl); todo := todo.push (n, nl)
  let mut fuel := fuel0
  while fuel > 0 && todo.size > 0 do
    fuel := fuel - 1
    let (n, nl) := todo.back!
    todo := todo.pop
    if kindOf env n != "none" then out := out.push (n, nl)
    match env.find? n with
    | some (.defnInfo d) =>
      let body := d.value.instantiateLevelParams d.levelParams nl
      for (m, ml) in occs env body #[] do
        if !seen.contains (m, lvlKey ml) then seen := seen.insert (m, lvlKey ml); todo := todo.push (m, ml)
    | _ => pure ()
  return (out, todo.size)

def measureC (tag : String) (fuel : Nat) (rootList : Array (Name × String)) : CommandElabM Unit := do
  let env ← getEnv
  let mut keyRows := ""
  let mut stoppedRows := ""
  let mut recRows := ""
  let mut closRows := ""
  let mut profCache : Std.HashMap (Name × String) String := {}
  let prof (n : Name) (k : String) (ls : List Level) (cache : Std.HashMap (Name × String) String) :
      CommandElabM (String × Std.HashMap (Name × String) String) := do
    match cache[(n, k)]? with
    | some v => pure (v, cache)
    | none => do
      let v ← liftTermElabM (profileOf n ls)
      pure (v, cache.insert (n, k) v)
  for st in List.range stageCount do
    let mut keys : Std.HashMap (Name × String) (Nat × List Level) := {}
    let mut stoppedAgg : Std.HashMap (Name × String) (Nat × List Level) := {}
    let mut recSeen : Std.HashSet (String × Name × String) := {}
    for (r, _) in rootList do
      let (nodes, stopped, left) := traceReach env r fuel st
      if left > 0 then throwError "fuel={fuel} exhausted: stage {st} root {r}: {left} todo left"
      for i in [0:nodes.size] do
        let nd : TNode := nodes[i]!
        let k := (nd.name, lvlKey nd.ls)
        if stopped[i]! then
          stoppedAgg := stoppedAgg.insert k ((stoppedAgg.getD k (0, nd.ls)).1 + 1, nd.ls)
        else
          if kindOf env nd.name != "none" then
            keys := keys.insert k ((keys.getD k (0, nd.ls)).1 + 1, nd.ls)
          match env.find? nd.name with
          | some (.defnInfo d) =>
            let body := d.value.instantiateLevelParams d.levelParams nd.ls
            for (rn, cls) in recOccs env body #[] do
              let key := (keyStr nd.name nd.ls, rn, cls)
              if !recSeen.contains key then
                recSeen := recSeen.insert key
                recRows := recRows ++ s!"{st}\t{key.1}\t{rn}\t{cls}\n"
          | _ => pure ()
    for ((n, k), (c, ls)) in keys.toList do
      let (p, cache) ← prof n k ls profCache
      profCache := cache
      keyRows := keyRows ++ s!"{st}\t{n}\t{kindOf env n}\t{k}\t{c}\t{p}\n"
    let mut clos : Std.HashMap (Name × String) (List Level) := {}
    for ((n, _), (_, ls)) in stoppedAgg.toList do
      let (ks, left) := typeClosure env n ls fuel
      if left > 0 then throwError "fuel={fuel} exhausted in the type closure of {n}"
      for (m, ml) in ks do clos := clos.insert (m, lvlKey ml) ml
    for ((m, k), _) in clos.toList do
      closRows := closRows ++ s!"{st}\t{m}\t{kindOf env m}\t{k}\t{if keys.contains (m, k) then "inresidue" else "extra"}\n"
    for ((n, k), (c, ls)) in stoppedAgg.toList do
      let (p, cache) ← prof n k ls profCache
      profCache := cache
      let v := match ← liftTermElabM (dynFit n ls) with | none => "fits" | some w => "NO: " ++ w
      stoppedRows := stoppedRows ++ s!"{st}\t{n}\t{k}\t{c}\t{v}\t{p}\n"
  logInfo m!"[{tag}] {rootList.size} roots, fuel {fuel}, {stageCount} stages, all worklists empty"
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    IO.FS.writeFile (path ++ ".cmpkeys." ++ tag) keyRows
    IO.FS.writeFile (path ++ ".cmpstopped." ++ tag) stoppedRows
    IO.FS.writeFile (path ++ ".cmprec." ++ tag) recRows
    IO.FS.writeFile (path ++ ".cmpclos." ++ tag) closRows

elab "#prim_residue_cmp " tag:str fuel:num : command => do
  let env ← getEnv
  measureC tag.getString fuel.getNat ((machineRoots env).map fun (r, _) => (r, toString (rootModule env r)))

elab "#prim_residue_cmp_named " tag:str fuel:num roots:ident* : command => do
  let env ← getEnv
  let rs := roots.map fun i => (i.getId, "named")
  for (r, _) in rs do unless (env.find? r).any (·.isDefinition) do throwError "{r} is not a definition"
  measureC tag.getString fuel.getNat rs

/-- negative control: a too small fuel must make the measurement fail -/
elab "#prim_residue_cmp_neg " fuel:num : command => do
  let env ← getEnv
  let roots := (machineRoots env).map fun (r, _) => (r, toString (rootModule env r))
  let failed ← try measureC "neg" fuel.getNat roots; pure none
    catch e => pure (some (← e.toMessageData.toString))
  match failed with
  | some m => logInfo s!"negative control ok: fuel={fuel.getNat} fails as required; first line: {(m.splitOn "\n").head!}"
  | none => throwError "negative control FAILED: fuel={fuel.getNat} did not exhaust"

/-- control for the profiles: known declared types must get the stated profile -/
elab "#prim_residue_cmp_ctl" : command => do
  let chk (c : Name) (ls : List Level) (want : String) : CommandElabM Unit := do
    let p ← liftTermElabM (profileOf c ls)
    if p != want then throwError "profile control failed for {c}: got {p.replace "\t" "|"} wanted {want.replace "\t" "|"}"
    logInfo m!"profile control {c}: {p.replace "\t" "|"}"
  chk ``Nat.succ [] "0\tfalse\t0\tfalse\t1\t0\tR1\tT1"
  chk ``Nat.zero [] "0\tfalse\t0\tfalse\t0\t0\tR0\tT0"
  chk ``Fin.mk [] "0\tfalse\t1\tfalse\t3\t0\tR2\tT3"
  chk ``Nat.rec [Level.one] "1\tfalse\t0\tfalse\t4\t0\tR3\tT3"
  chk ``Functor.map [Level.zero, Level.zero] "1\tfalse\t0\tfalse\t6\t2\tR3\tT3"
  chk ``Eq.refl [Level.one] "0\tfalse\t0\ttrue\t2\t1\tR3a\tT3"
  chk ``BitVec.ofNat [] "0\tfalse\t0\tfalse\t2\t0\tR2\tT3"

end Tests.Gen5.PrimResidueCmp
