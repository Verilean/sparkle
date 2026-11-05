import Tools.ShippingGen5ReaderTraceFinal
import Tools.ShippingGen5Cover3R
set_option autoImplicit false
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # C.CV-5 and C.CV-6 at the reader root (scripts/gen5/CV56_FREEZE.md)

`readerTrace_final_b1` has EXACTLY the binders of `readerTrace_final` (Tools/ShippingGen5ReaderTraceFinal.lean, the root whose
assumptions the ledger counts since §12.8). Its conclusion is that of `readerTrace_final` plus the GenWF row b1
(`∀ k < insts.length, callKind d k ≠ .domain`). The b1 fact comes from `rowB1_of_dataE` with `hms := h` (the root's
`machineShape? false [] E (structEnv env) = some sp`) and `hd := hd` (the root's `dataOfAt lvl E (structEnv env) sp = some d`,
the same `E`, `sp`), so `hcb` (C.CV-6) is not a binder. C.CV-5 (`hsp hss hls hn`): the root already derives them from `hd`
(`dims_of_dataOfAt`); they are not binders of the root either. Nothing else is claimed (no GenWF assembly, no FG). -/

namespace Tools.ShippingGen5ReaderTraceFinalB1
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel
open Tools.ShippingGen5Cover3 Tools.ShippingGen5GDCover1 Tools.ShippingGen5Cover3Canon Tools.ShippingMachineAuto Tools.ShippingGen5Sem
open Tools.ShippingGen5ReaderTraceU2 Tools.ShippingGen5Cover6

theorem readerTrace_final_b1
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
    (    (∀ n : Nat, TraceGood (structEnv env) (nDeclOfCi E) (readF (structEnv env) n)) ∧
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧
      FReachC (nDeclOfCi E) ({} : MachRead) st0 ∧ FReachC (nDeclOfCi E) st0 st1 ∧ FReachC (nDeclOfCi E) st1 st ∧
      TrInv (structEnv env) (nDeclOfCi E) st ∧
      ShapeAgree d st ∧ FullInv (kDOf d) st ∧ LetsNoLoose st) ∧
    (∀ k, k < d.shape.insts.length → callKind d k ≠ .domain) := by
  have R := Tools.ShippingGen5ReaderTraceFinal.readerTrace_final hE hla hi1 hr hh hbt hEq env hK hC hD hv hbr hraw hnode hrr hfb hci hbranch hEd h hd
  obtain ⟨n, p, en, st0, env', st1, st, v, -, -, -, -, -, hag, hfi, -⟩ := R.2
  exact ⟨R, Tools.ShippingGen5Cover3R.rowB1_of_dataE hag hfi h hd⟩

end Tools.ShippingGen5ReaderTraceFinalB1

#print axioms Tools.ShippingGen5ReaderTraceFinalB1.readerTrace_final_b1
