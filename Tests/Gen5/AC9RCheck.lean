import Tools.ShippingGen5AccServedR
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: Tools.ShippingGen5AccKeep (an import of AccServed) does not elaborate on this base (Gen2KeepChild change 00c93ab7), so this file was never elaborated. No sorry / axiom / native_decide.
/-! # C.AC-9 checks (Tools/ShippingGen5AccServedR.lean; scripts/gen5/AC9CV5_FREEZE.md §3)

TYPE: Expected statements are written from the freeze text. MUTANT: signature / defeq rejection, NOT a semantic counterexample.
BINDERS: Prop binders of `accServed0_of_coverR` = those of `accServed0_of_cover` with `hDS` replaced by `hK`, compared mechanically.
AXIOMS: standard only. -/
namespace Tests.Gen5.AC9RCheck
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen5Acc Tests.Gen3.ExpectedType
open Tools.ShippingGen2 (Laws)

def ExpDS : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (lvl : Lean.Expr → Nat) (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl), DataOfShape K

def ExpCoverR : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) (lvl : Lean.Expr → Nat)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hRoute : MachineRouteAt env₀ L Reach) (hcov : ReachCover K Reach)
    (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl)
    (hRS : ReadsSupplyAt env₀ L Reach), AccServed0Stmt K L Reach

/-- Mutant: `hK` dropped. -/
def MutNoHK : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) (lvl : Lean.Expr → Nat)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hRoute : MachineRouteAt env₀ L Reach) (hcov : ReachCover K Reach)
    (hRS : ReadsSupplyAt env₀ L Reach), AccServed0Stmt K L Reach

/-- Mutant: `hcl` dropped. -/
def MutNoHcl : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) (lvl : Lean.Expr → Nat)
    (hRoute : MachineRouteAt env₀ L Reach) (hcov : ReachCover K Reach)
    (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl)
    (hRS : ReadsSupplyAt env₀ L Reach), AccServed0Stmt K L Reach

/-- Mutant: `hDS` kept in addition (old premise not removed). -/
def MutKeepDS : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) (lvl : Lean.Expr → Nat)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hRoute : MachineRouteAt env₀ L Reach) (hcov : ReachCover K Reach)
    (hDS : DataOfShape K) (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl)
    (hRS : ReadsSupplyAt env₀ L Reach), AccServed0Stmt K L Reach

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``dataOfShape_of_dataOfAt ``ExpDS
  checkExpected ``accServed0_of_coverR ``ExpCoverR
  logInfo m!"AC9 TYPE: 2 theorems against Expected"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``accServed0_of_coverR ``MutNoHK
  checkMutant ``accServed0_of_coverR ``MutNoHcl
  checkMutant ``accServed0_of_coverR ``MutKeepDS
  logInfo m!"AC9 MUTANT: 3 rejected (signature/defeq, not semantic)"

def propBinders (thm : Name) : MetaM (List Name) := do
  forallTelescope (← stmtOf thm) fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if ← isProp d.type then out := out ++ [d.userName.eraseMacroScopes]
    pure out

run_cmd Lean.Elab.Command.liftTermElabM do
  let got ← propBinders ``accServed0_of_coverR
  let old ← propBinders ``accServed0_of_cover
  unless old.contains `hDS do throwError "AC9 BINDERS CONTROL: old statement lacks hDS"
  let exp := old.map fun b => if b == `hDS then `hK else b
  unless got == exp do throwError "AC9 BINDERS FAILED: expected {exp}, got {got}"
  logInfo m!"AC9 BINDERS: {got} = old {old} with hDS replaced by hK"
  for n in [``dataOfShape_of_dataOfAt, ``accServed0_of_coverR] do checkAxioms n
  logInfo m!"AC9 COUNTS: TYPE 2, MUTANT 3, BINDERS 1, AXIOMS 2"
end Tests.Gen5.AC9RCheck
