import Lean
import Tools.ShippingGen5SM7
set_option autoImplicit false
-- C.SM-7 audit check (Issue sparkle-ledger-sm7): structural Expr comparisons, with controls.

/-! # C.SM-7: no top-level ordinary-guard binder; the guard comes from `stepDec_of_ties`'s `hT2_TIE`

1. GUARD: a binder is a "guard binder" when its type is `Eq (… .child?) none` at the top (not under a `∀`/`→`), detected by the
   constant `InstOrigin.child?` in the left side of an `Eq`. `hT2Tie_of_genGP` must have NONE; the ND root
   `callTie_of_served_oneOut_t1ND` (control) must have one (`hord`).
2. CONSUMER: the conclusion of `hT2Tie_of_genGP` is `==` (structural Expr) to the type of the `hT2_TIE` premise of
   `stepDec_of_ties` at `P := genGP lvl hs genData₀ env` and the same `p`. Control: at a different table (`genGP` of a fresh
   environment) it is not `==`.
3. USES: every `Tools.*` constant of this environment whose value uses `genExtAtCall_of_genSem` is listed; it must be exactly
   `[hDT1_of_genGP]` (so the only remaining `hord` argument of `genExtAtCall_of_genSem` is fed by `h_D_T1`'s guard). -/
open Lean Meta

namespace Tests.Gen5.SM7Check

def isGuard (ty : Expr) : Bool :=
  match ty.eq? with
  | some (_, lhs, _) => lhs.getUsedConstants.contains ``Sparkle.Compiler.MachInstOrigin.InstOrigin.child?
  | none => false

def guardBinders (c : Name) : MetaM (List Name) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if isGuard (← instantiateMVars d.type) then out := out ++ [d.userName]
    return out

/-- Opens the binders of `ty` up to and including the one named `last`, then runs `k` on the fvars and the rest. -/
partial def openUntil (last : Name) (ty : Expr) (acc : Array Expr) (k : Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  match ty with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      let acc := acc.push x
      if n == last then k acc (b.instantiate1 x) else openUntil last (b.instantiate1 x) acc k
  | _ => throwError "binder {last} not found"

def fv (xs : Array Expr) (n : Name) : MetaM Expr := do
  for x in xs do
    if (← x.fvarId!.getDecl).userName == n then return x
  throwError "no binder {n}"

/-- The `hT2_TIE` premise type of `stepDec_of_ties` at table `P` and package `p`. -/
def hT2TieTy (ι dom P p : Expr) : MetaM Expr := do
  let t ← inferType (← mkAppOptM ``Tools.ShippingGen2.stepDec_of_ties #[some ι, some dom, some P, some p])
  match t with
  | .forallE n d b bi => withLocalDecl n bi d fun x => do
      match b.instantiate1 x with
      | .forallE m d2 _ _ =>
        unless m == `hT2_TIE do throwError "second premise of stepDec_of_ties is {m}, not hT2_TIE"
        return d2
      | _ => throwError "stepDec_of_ties shape"
  | _ => throwError "stepDec_of_ties shape"

run_meta do
  -- 1. GUARD
  let g ← guardBinders ``Tools.ShippingGen5SM7.hT2Tie_of_genGP
  let gc ← guardBinders ``Tools.ShippingGen2.callTie_of_served_oneOut_t1ND
  logInfo m!"GUARD binders: hT2Tie_of_genGP {g}; control callTie_of_served_oneOut_t1ND {gc}"
  unless g.isEmpty do throwError "hT2Tie_of_genGP has a guard binder {g}"
  unless gc == [`hord] do throwError "CONTROL: the ND root should have exactly the guard binder hord, got {gc}"
  -- 2. CONSUMER
  let ci ← getConstInfo ``Tools.ShippingGen5SM7.hT2Tie_of_genGP
  openUntil `hkidW ci.type #[] fun xs concl => do
    let gp ← mkAppOptM ``Tools.ShippingGenFGLedgerPremises.genGP
      #[some (← fv xs `ι), some (← fv xs `dom), some (← fv xs `lvl), some (← fv xs `initsOf), some (← fv xs `hs),
        some (← fv xs `genData₀), some (← fv xs `env)]
    let expected ← hT2TieTy (← fv xs `ι) (← fv xs `dom) gp (← fv xs `p)
    let same := concl == expected
    -- control: the same premise at the table of another environment
    let envTy ← inferType (← fv xs `env)
    let ctrl ← withLocalDecl `env' .default envTy fun env' => do
      let gp' ← mkAppOptM ``Tools.ShippingGenFGLedgerPremises.genGP
        #[some (← fv xs `ι), some (← fv xs `dom), some (← fv xs `lvl), some (← fv xs `initsOf), some (← fv xs `hs),
          some (← fv xs `genData₀), some env']
      return concl == (← hT2TieTy (← fv xs `ι) (← fv xs `dom) gp' (← fv xs `p))
    logInfo m!"CONSUMER: conclusion == stepDec_of_ties.hT2_TIE at genGP env: {same}; control at env': {ctrl}"
    unless same && !ctrl do throwError "CONSUMER comparison unexpected"
  -- 3. USES
  let env ← getEnv
  let mut users : List Name := []
  for (n, c) in env.constants.toList do
    if (`Tools).isPrefixOf n then
      if let some v := c.value? then
        if v.getUsedConstants.contains ``Tools.ShippingGen5Sem.genExtAtCall_of_genSem then users := users ++ [n]
  logInfo m!"USES of genExtAtCall_of_genSem in Tools.*: {users}"
  unless users == [``Tools.ShippingGenFGLedgerPremises.hDT1_of_genGP] do throwError "unexpected users {users}"
  logInfo m!"SM7 COUNTS: guard 1 + control 1, consumer 1 + control 1, uses 1"

#print axioms Tools.ShippingGen5SM7.hT2Tie_of_genGP

end Tests.Gen5.SM7Check
