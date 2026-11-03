-- NOT BUILT: rt142 implementation of scripts/gen5/RT_FINAL_FREEZE.md §2 (conditional stage; clean build is the coder's).
import Tools.ShippingGen5ReaderTraceU2Compose
import Tools.ShippingGen5ReaderTraceAbbrevS1
set_option autoImplicit false
namespace Tools.ShippingGen5ReaderTraceFinal
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel
open Tools.ShippingGen5Cover3 Tools.ShippingGen5GDCover1 Tools.ShippingGen5Cover3Canon Tools.ShippingMachineAuto Tools.ShippingGen5Sem
open Tools.ShippingGen5ReaderTraceU2 Tools.ShippingGen5Cover6

theorem readerTrace_final
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hfb : FuelBridge)
    {ci0 E : ConstantInfo} (hci : Tools.ShippingGen5ReaderTrace.CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d) :
    (∀ n : Nat, TraceGood (structEnv env) (nDeclOfCi E) (readF (structEnv env) n)) ∧
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧
      FReachC (nDeclOfCi E) ({} : MachRead) st0 ∧ FReachC (nDeclOfCi E) st0 st1 ∧ FReachC (nDeclOfCi E) st1 st ∧
      TrInv (structEnv env) (nDeclOfCi E) st ∧
      ShapeAgree d st ∧ FullInv (kDOf d) st ∧ LetsNoLoose st := by
  have hz := Tools.ShippingGen5ReaderTraceAbbrevS1.zeroLitAgrees0_of_replace hr
  have hIn : ∀ n : Nat, ShapeInputs' (nDeclOfCi E) (structEnv env) false [] E n := by
    rcases hbranch with rfl | rfl
    · exact fun n => shapeInputs_of_direct' hz hla hi1 env hv hci hbr hraw hnode
    · obtain ⟨c, hc⟩ := hci
      exact fun n => Tools.ShippingGen5ReaderTrace.shapeInputs_of_inline' hz hla hi1 env hv hrr hr hh hbt hEq hc rfl hbr hraw hnode
  have hT := readF_traceGood_of_premises env hK hC hla (Tools.PartialTotal.Agree.rootFloatAgrees hla) hi1 hD (nDeclOfCi E)
  refine ⟨hT, ?_⟩
  obtain ⟨n, hn⟩ := hfb E (structEnv env) sp h
  obtain ⟨p, en, st0, env1, st1, st, v, w⟩ := Tools.ShippingGen5Cover5.machineShapeF_state_side hn
  obtain ⟨R0, R1, R2, Tr, -⟩ := reach'_of_witness hE (hT n) hn (hIn n) w
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11⟩ := w
  obtain ⟨hsp, hss', hls, hn'⟩ := dims_of_dataOfAt hd
  have hkd' : kDOf d = nDeclOfCi E := by
    subst hEd
    exact kDOf_eq_nDeclOfCi lvl hd
  refine ⟨n, p, en, st0, env1, st1, st, v, ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11⟩, R0, R1, R2, Tr,
    Tools.ShippingGen5Cover5.shapeAgree_of_sides ⟨hw8, hw9, hw10, hw11⟩ hsp hss' hls hn', ?_, Tr.2.2.2.2.2.1⟩
  rw [hkd']
  exact Tr.1

end Tools.ShippingGen5ReaderTraceFinal
