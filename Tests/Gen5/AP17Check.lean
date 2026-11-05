import Lean
import Tools.ShippingGen5AP17
set_option autoImplicit false
-- A.P-17 audit check (Issue sparkle-ledger-ap17): structural Expr comparison, with controls.

/-! # A.P-17: the final theorems no longer bind `T1Hyp` (so no `dec`)

For each old final theorem `old` (with `hT : T1Hyp …`) and its ND replacement `new` (at `P := genGP lvl hs genData₀ env`), one telescope
walk of `old`'s type, with `P` instantiated to `genGP …` and every other binder instantiated with the same-named binder of `new`:

* a binder of `old` that has a same-named binder in `new` must have a `==` type (`mism` must be empty);
* `hT` of `old` (`T1Hyp L P Reach DataOk`) is replaced by `H` of `new` (`T1HypND` with the same four arguments);
* the binders of `new` that `old` does not have (`extra`) are exactly the `genGP` inputs and the four rows `hMEM hARGS hOW hkidW`;
* the conclusions are `==` (for `t1`, after unfolding `T1Stmt` and dropping its `T1Hyp →`).

CONST: no binder type of any `new` mentions `T1Hyp`; CONTROL: the `old` ones do. VALUE: the `Tools.*` constants reachable from the value
of each `new` do not include `T1Hyp.dec`; CONTROL: the ones reachable from `old` do. Negative control for the comparison: `ihKI_of_rows`
against `closingRun0_of_runT1_ND` is not accepted. -/
open Lean Meta

namespace Tests.Gen5.AP17Check

def T1Hyp' : Name := ``Tools.ShippingGen2.T1Hyp
def T1HypND' : Name := ``Tools.ShippingGen2.T1HypND
def decName : Name := ``Tools.ShippingGen2.T1Hyp.dec

def gpInputs : List Name := [`lvl, `initsOf, `hs, `genData₀, `env]
def rows : List Name := [`hMEM, `hARGS, `hOW, `hkidW]

structure Cmp where
  mism : Array Name := #[]
  dropped : Array Name := #[]
  replaced : Bool := false
  extra : Array Name := #[]
  concl : Bool := false

/-- Telescope walk of `old` against `new` (see the header). `unfoldT1` unfolds `T1Stmt` in the old conclusion. -/
def compare (old new : Name) (unfoldT1 : Bool := false) : MetaM Cmp := do
  let oi ← getConstInfo old
  let ni ← getConstInfo new
  forallTelescope ni.type fun xs ncon => do
    let mut byName : Std.HashMap Name Expr := {}
    for x in xs do byName := byName.insert (← x.fvarId!.getDecl).userName x
    let some gpTbl := byName[`env]? | throwError "no env"
    let gp ← mkAppOptM ``Tools.ShippingGenFGLedgerPremises.genGP
      #[some byName[`ι]!, some byName[`dom]!, some byName[`lvl]!, some byName[`initsOf]!, some byName[`hs]!,
        some byName[`genData₀]!, some gpTbl]
    let mut ty := oi.type
    let mut r : Cmp := {}
    let mut seen : Array Name := #[]
    while ty.isForall do
      let .forallE n d b _ := ty | break
      if n == `P then
        ty := b.instantiate1 gp
      else if n == `hT then
        seen := seen.push `H
        let nx := byName[`H]!
        let nt ← instantiateMVars (← inferType nx)
        let ok := d.getAppFn.constName? == some T1Hyp' && nt.getAppFn.constName? == some T1HypND' &&
          d.getAppArgs == nt.getAppArgs
        r := { r with replaced := ok }
        ty := b.instantiate1 (← mkFreshExprMVar d)
      else
        -- the old start-world binder `hs` is `hs0` in the new theorem (`hs` is the generator soundness input)
        let n' := if n == `hs && byName.contains `hs0 then `hs0 else n
        match byName[n']? with
        | some x =>
          seen := seen.push n'
          let xt ← instantiateMVars (← inferType x)
          unless d == xt do r := { r with mism := r.mism.push n }
          ty := b.instantiate1 x
        | none =>
          r := { r with dropped := r.dropped.push n }
          ty := b.instantiate1 (← mkFreshExprMVar d)
    if unfoldT1 then
      let some u ← unfoldDefinition? ty | throwError "T1Stmt does not unfold"
      match u.headBeta with
      | .forallE _ d b _ =>
        unless d.getAppFn.constName? == some T1Hyp' do throwError "T1Stmt does not start with T1Hyp"
        ty := b
      | _ => throwError "T1Stmt shape"
    -- for `t1` the new conclusion is the ∀ after the last row binder `hkidW`
    let ncon ← if unfoldT1 then do
        let mut k := 0
        for i in [0:xs.size] do
          if (← xs[i]!.fvarId!.getDecl).userName == `hkidW then k := i + 1
        mkForallFVars (xs.extract k xs.size) ncon
      else pure ncon
    r := { r with concl := (← instantiateMVars ty) == (← instantiateMVars ncon) }
    let mut extra := #[]
    for x in xs do
      let n := (← x.fvarId!.getDecl).userName
      unless seen.contains n do extra := extra.push n
    if unfoldT1 then extra := extra.filter (fun n => (`H :: gpInputs ++ rows).contains n)
    return { r with extra }

def mentions (c : Name) (e : Expr) : Bool := e.getUsedConstants.contains c

/-- Binder types (premises) of `c` mentioning the constant `k`. -/
def binderMentions (c : Name) (k : Name) : MetaM (List Name) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if mentions k (← instantiateMVars d.type) then out := out ++ [d.userName]
    return out

/-- `Tools.*` constants reachable from the value of `c` (through `Tools.*` values only); true if `target` is among them. -/
partial def reaches (c target : Name) : MetaM Bool := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[c]
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if n == target then return true
    if !((`Tools).isPrefixOf n) then continue
    if let some ci := env.find? n then
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
      for m in cs do
        unless seen.contains m do todo := todo.push m
  return false

def expectOk (what : String) (r : Cmp) (extraWant : List Name) (dropWant : List Name := []) : MetaM Unit := do
  logInfo m!"{what}: mism {r.mism}, dropped {r.dropped}, hT→H {r.replaced}, extra {r.extra}, conclusion {r.concl}"
  unless r.mism.isEmpty do throwError "{what}: binder type mismatch {r.mism}"
  unless r.replaced do throwError "{what}: hT : T1Hyp is not replaced by H : T1HypND with the same arguments"
  unless r.concl do throwError "{what}: conclusions differ"
  unless r.dropped.toList == dropWant do throwError "{what}: dropped binders {r.dropped}, expected {dropWant}"
  unless r.extra.toList.toArray.qsort Name.lt == (extraWant.toArray.qsort Name.lt) do
    throwError "{what}: extra binders {r.extra}, expected {extraWant}"

run_meta do
  let R4 := `Tools.ShippingGen5ClosingRun4
  let G2 := `Tools.ShippingGen2
  let extraAll := gpInputs ++ rows
  -- 1. comparisons
  expectOk "ihKI_of_rows ~ ih_allPF_ND"
    (← compare (R4 ++ `ihKI_of_rows) (G2 ++ `ih_allPF_ND)) extraAll
  expectOk "closingRun0_of_runT1 ~ closingRun0_of_runT1_ND"
    (← compare (R4 ++ `closingRun0_of_runT1) (G2 ++ `closingRun0_of_runT1_ND)) extraAll
  expectOk "closingRun_of_runT1 ~ closingRun_of_runT1_ND"
    (← compare (R4 ++ `closingRun_of_runT1) (G2 ++ `closingRun_of_runT1_ND)) extraAll
  -- t1: the old statement is `T1Stmt` (its `T1Hyp →` is inside the conclusion) with no `hT` binder
  let rt ← compare (G2 ++ `t1_of_step_rows_run) (G2 ++ `t1_of_stepPF_ND) (unfoldT1 := true)
  logInfo m!"t1_of_step_rows_run ~ t1_of_stepPF_ND: mism {rt.mism}, dropped {rt.dropped}, extra {rt.extra}, conclusion {rt.concl}"
  unless rt.mism.isEmpty && rt.dropped.isEmpty && rt.concl do throwError "t1: comparison failed"
  unless rt.extra.toList.toArray.qsort Name.lt == ((`H :: extraAll).toArray.qsort Name.lt) do
    throwError "t1: extra binders {rt.extra}"
  -- negative control for the comparison
  let bad ← compare (R4 ++ `ihKI_of_rows) (G2 ++ `closingRun0_of_runT1_ND)
  unless !bad.mism.isEmpty || !bad.concl || !bad.dropped.isEmpty do throwError "CONTROL: a wrong pairing was accepted"
  logInfo m!"CONTROL pairing: mism {bad.mism}, dropped {bad.dropped}, conclusion {bad.concl}"
  -- 2. CONST: no binder mentions T1Hyp (also not in the conclusion)
  for n in [`ih_allPF_ND, `ihAt_stepPF_ND, `decAt_ND, `t1_of_stepPF_ND, `closingRun0_of_runT1_ND, `closingRun_of_runT1_ND] do
    let c := G2 ++ n
    let b ← binderMentions c T1Hyp'
    let ci ← getConstInfo c
    if mentions T1Hyp' ci.type then throwError "{n}: the type mentions T1Hyp (binders {b})"
    unless b.isEmpty do throwError "{n}: T1Hyp binders {b}"
  let ctrl ← binderMentions (R4 ++ `closingRun_of_runT1) T1Hyp'
  unless ctrl == [`hT] do throwError "CONTROL: old closingRun_of_runT1 should have exactly hT : T1Hyp, got {ctrl}"
  logInfo m!"CONST: no T1Hyp in the 6 new types; control old binders {ctrl}"
  -- 3. VALUE: `T1Hyp.dec` is not reachable from the new values (through Tools.*)
  for n in [`ih_allPF_ND, `t1_of_stepPF_ND, `closingRun0_of_runT1_ND, `closingRun_of_runT1_ND] do
    if (← reaches (G2 ++ n) decName) then throwError "{n}: T1Hyp.dec is reachable from its value"
  unless (← reaches (R4 ++ `closingRun_of_runT1) decName) do
    throwError "CONTROL: T1Hyp.dec is not reachable from the old closingRun_of_runT1"
  logInfo m!"VALUE: T1Hyp.dec unreachable from the 4 new values; control (old closingRun_of_runT1) reaches it"

#print axioms Tools.ShippingGen2.ih_allPF_ND
#print axioms Tools.ShippingGen2.t1_of_stepPF_ND
#print axioms Tools.ShippingGen2.closingRun0_of_runT1_ND
#print axioms Tools.ShippingGen2.closingRun_of_runT1_ND

end Tests.Gen5.AP17Check
