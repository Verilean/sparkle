import Tools.ShippingGenFGLedgerPremisesG
set_option autoImplicit false
-- D.D-4 carrier finding: `CV` is universally quantified in FGLedgerPremisesStmtR/G but `ConstValueFunctional CV` is a CONCLUSION.

/-! # `∀ CV, … → ConstValueFunctional CV ∧ …` is refuted at `CV := ⊤`

`FGLedgerPremisesStmtG` binds `CV : ConstValueRel` with no hypothesis on it, and its first conclusion conjunct is
`ConstValueFunctional CV`. At the full relation `cvTop := fun _ _ _ _ => True` this conjunct is false (it relates a `Unit` and
a `Bool` value, and `Unit ≠ Bool`). So `FGLedgerPremisesStmtG` implies that its three outer hypotheses (`h_C_EN4`,
`h_C_RK6`, `h_C_CV4`) are jointly unsatisfiable at every carrier instance: as stated, G (and R, by `fgLedgerPremisesStmtG_of_R`)
is either false or vacuous. No sorry / axiom. -/

namespace Tests.Gen5.CVTopCheck
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5Acc Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Core Sparkle.Core.Signal

def cvTop : ConstValueRel := fun _ _ _ _ => True

theorem unit_ne_bool : (Unit : Type) ≠ Bool := by
  intro e
  have h : ∀ a b : Bool, a = b := e ▸ (fun (a b : Unit) => Subsingleton.elim a b)
  exact Bool.noConfusion (h true false)

theorem cvTop_not_functional (env : Environment) : ¬ ConstValueFunctional cvTop := by
  intro h
  exact unit_ne_bool (h env .anonymous Unit Bool () true trivial trivial).1

/-- G refutes its three outer hypotheses at every carrier instance with `CV := cvTop` (the other carriers are arguments). -/
theorem fgG_refutes_outer (hG : FGLedgerPremisesStmtG) {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp))
    (env : Environment) : False := by
  unfold FGLedgerPremisesStmtG at hG
  exact cvTop_not_functional env
    (hG (ι := ι) (dom := dom) ReflectsAll Post lvl hs genData₀ cvTop L h_C_EN4 h_C_RK6 h_C_CV4).1

end Tests.Gen5.CVTopCheck

#print axioms Tests.Gen5.CVTopCheck.cvTop_not_functional
#print axioms Tests.Gen5.CVTopCheck.fgG_refutes_outer
