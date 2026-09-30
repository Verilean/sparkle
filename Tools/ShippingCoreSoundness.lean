import Tools.ShippingMemoryEntrySoundness
import Tools.ShippingVectorMuxSoundness

/-! # S7-1: the single shipping soundness statement at the core entry

Every certified family so far — the mixed Bool/BitVec sources, the
unified combinational terms, vector muxes, the five register shapes,
the two `circuit do` shapes and the two memory shapes — carries its own
`…Preserves` contract at the real `synthesizeCombinationalCore` entry.
This file RECONCILES them: one run of the entry satisfies ALL of the
family contracts simultaneously (each is conditional on its own quoted
shape, so the conjunction is the honest disjonction-free composition),
so every per-shape endpoint in the test suite routes through this ONE
statement. -/

namespace Tools.ShippingCoreSoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingVectorMuxSoundness
open Tools.ShippingRegisterSoundness
open Tools.ShippingMemoryEntrySoundness
open Tools.ShippingEntrySoundness

/-- Everything the shipping core entry guarantees for a gate-accepted
declaration, in one statement. -/
def ShippingPreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  MixedPreserves declName bs body m ∧
  TermPreserves declName bs body m ∧
  VectorPreserves declName bs body m ∧
  RegisterPreserves declName bs body m ∧
  RegisterEnablePreserves declName bs body m ∧
  LoopRegisterPreserves declName bs body m ∧
  Register2Preserves declName bs body m ∧
  CdoPreserves declName bs body m ∧
  Cdo2Preserves declName bs body m ∧
  MemoryPreserves declName bs body m ∧
  MemoryConePreserves declName bs body m

/-- **The shipping core soundness.** One successful run of the real
entry satisfies every family contract at once; each family's quoted
shape selects the applicable one. -/
theorem synthesizeCombinationalCore_shipping_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) →
        ShippingPreserves declName bs body m := by
  obtain ⟨logProf, ci, w1, w2, w3, get, run⟩ := synthesizeCombinationalCore_reads hr
  refine ⟨ci, w1, w2, get, fun bs body old shape => ?_⟩
  exact ⟨synthesizeFromConst_mixed_sound old shape run.mreturns,
    synthesizeFromConst_term_sound old shape run.mreturns,
    synthesizeFromConst_vector_sound old shape run.mreturns,
    synthesizeFromConst_register_sound old shape run.mreturns,
    synthesizeFromConst_registerEnable_sound old shape run.mreturns,
    synthesizeFromConst_loopRegister_sound old shape run.mreturns,
    synthesizeFromConst_register2_sound old shape run.mreturns,
    synthesizeFromConst_cdo_sound old shape run.mreturns,
    synthesizeFromConst_cdo2_sound old shape run.mreturns,
    synthesizeFromConst_memory_sound old shape run.mreturns,
    synthesizeFromConst_memoryCone_sound old shape run.mreturns⟩

end Tools.ShippingCoreSoundness
