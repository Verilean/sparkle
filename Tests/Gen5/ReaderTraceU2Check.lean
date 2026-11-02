import Tools.ShippingGen5ReaderTraceU2Compose
import Tools.PartialTotal.Agree
import Tests.Gen3.ExpectedType
import Tools.Prototype.PreprocLetOk
import Tools.Assume.N3Extern
import Tools.Prototype.RawNodeRangeLetOk
import Tools.Prototype.LiftScalarModelLetOk
import Tools.Prototype.BoolMapModelLetOk
import Tools.Assume.ExprEqv
import Tools.Assume.AbbrevExtern
set_option autoImplicit false
-- rt127: Check follows pass_ph (BINDERS' 22, CLOSURE' 13228); `kjob lake build Tests.Gen5.ReaderTraceU2Check` exit 0 on the tree of 2d56a2a55959000514ddd8bf487515d6640282f8 (this line comment-only).
-- rt61: added leaf-free checks (TYPE' 5 / BINDERS' 21 / AXIOMS 5 / CLOSURE' 11912), `kjob lake build Tests.Gen5.ReaderTraceU2Check` exit 0 on the Lean content of 5c6177007416f405d661c6057f5178cbb6dea0ac (comment-only line). Clean build is the coder's.
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceU2Check, exit 0; TYPE 13 (+2 twin by type) / MUTANT 9 (signature/defeq rejections, not semantic counterexamples) / BINDERS 20 (16 named, full Name) / LEAVES 4 / AXIOMS 5 standard only / CLOSURE 11730 constants OK / WATCH 28 full names (25 constants + 3 prose-only), 1 decoy + 1 binder decoy) on the Lean content of 2b771482e278441fbc250ef0bd5e962a81358be6 (this header is comment-only). Clean build is the coder's.

/-! # RT U2 checks (`scripts/gen5/RT_U2_FREEZE.md` §7): registration of N1-a / N2-b / N3-b and the composition `u2_compose`

TYPE: the 4 registered `def`s (statements, in `Tools/Assume/`), the two twin definitions `lamDepth` / `packTupleInputsF` (types, plus value samples by `rfl`),
the 4 leaf/auxiliary `def`s and the theorems `u2_core` / `u2_compose_direct` / `u2_compose_inline` / `u2_compose` / `u2_rowC` are compared by `checkExpected`
against `Exp…` statements written here (own spelling, from the code and the consumer `rowC_of_reader_canon`, not copied from the freeze `#check` text).
NOTE (freeze text vs code): the freeze §3.1 prints `FuelBridge` as `machineShapeF n false [] E senv = some (some sp)`; the code has the trailing default
argument `allowInsts := true` (`… senv true = …`, the form `machineShapeF_reach'` takes). This Check expects the code's form.
Mutants are well-typed single changes rejected by signature / defeq (NOT semantic counterexamples).
BINDERS: the Prop binders of `u2_compose` are matched by fully qualified `Lean.Name` (ordered list, and both directions as sets); a same-tail decoy in another
namespace is rejected (negative control).
LEAVES: the hypotheses that are leaves of other Issues are listed below with their supplier; they are theorem hypotheses, not shown to hold.
Nothing here proves that any premise holds, and the name scan does not show absence of premises under names outside the watchlist. -/

namespace Tests.Gen5.ReaderTraceU2Check
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingGen5Cover3
open Tools.ShippingGen5GDCover1 Tools.ShippingMachineAuto Tools.ShippingGen5Sem

section Expected

-- registered statements (N1-a / N2-b / N3-b x2)
def ExpDeclValuePh : Lean.Environment → Prop := fun env =>
  ∀ (n : Lean.Name) (d : Lean.DefinitionVal), env.find? n = some (Lean.ConstantInfo.defnInfo d) →
    NoPh d.value = true ∧ BvarLt 0 d.value = true
def ExpPackTupleInputsBridge : Prop :=
  ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachTupleIn.packTupleInputs e =
      Tools.ShippingGen5ReaderTracePack.packTupleInputsF (Tools.ShippingGen5ReaderTracePack.lamDepth e) e
def ExpRawNodePh : StructEnv → Prop := fun senv =>
  ∀ (L : Nat) (f a e' : Lean.Expr), NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch (Lean.Expr.app f a) = some e' →
    NoPh e' = true ∧ BvarLt L e' = true
def ExpNormNodePh : StructEnv → Prop := fun senv =>
  ∀ (L : Nat) (f a : Lean.Expr), NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    NoPh (machNormNode senv (Lean.Expr.app f a)) = true ∧ BvarLt L (machNormNode senv (Lean.Expr.app f a)) = true

-- leaf / auxiliary definitions of the composition
def ExpFuelBridge : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
    machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)
def ExpKDOfLeaf : Prop :=
  ∀ (lvl : Lean.Expr → Nat) (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape) (d : MachineData) (dd : DefinitionVal),
    E = ConstantInfo.defnInfo dd → Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d → kDOf d = nDeclOfCi E
def ExpSameStLeaf : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape) (n : Nat)
    (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr)
    (p' : ShapePre) (en' : Lean.Expr) (st0' : MachRead) (env' : List MachVal) (st1' st' : MachRead) (v' : Lean.Expr),
    StateSideWitness E senv sp n p en st0 env st1 st v → StateSideWitness E senv sp n p' en' st0' env' st1' st' v' → st = st'
def ExpInlineInputs : Lean.Environment → Prop := fun env =>
  ∀ ci0 : ConstantInfo, CiDirect env ci0 → ∀ (sm : Bool) (ps : List (String × Nat)) (n : Nat),
    ShapeInputs' (nDeclOfCi (inlinedConst (userInliner env) ci0)) (structEnv env) sm ps (inlinedConst (userInliner env) ci0) n

-- consumer-side facts (the conclusion shared by all compositions)
def ExpU2Core : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge) (hkd : Tools.ShippingGen5ReaderTraceU2.KDOfLeaf)
    (hss : Tools.ShippingGen5ReaderTraceU2.SameStLeaf)
    {E : ConstantInfo} {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    (hIn : ∀ n : Nat, ShapeInputs' (nDeclOfCi E) (structEnv env) false [] E n)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st
def ExpU2Direct : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge) (hkd : Tools.ShippingGen5ReaderTraceU2.KDOfLeaf)
    (hss : Tools.ShippingGen5ReaderTraceU2.SameStLeaf)
    {E : ConstantInfo} {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd) (hci : CiDirect env E)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st
def ExpU2Inline : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hInl : Tools.ShippingGen5ReaderTraceU2.InlineInputs env)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge) (hkd : Tools.ShippingGen5ReaderTraceU2.KDOfLeaf)
    (hss : Tools.ShippingGen5ReaderTraceU2.SameStLeaf)
    {ci0 : ConstantInfo} (hci : CiDirect env ci0)
    {dd : DefinitionVal} (hEd : inlinedConst (userInliner env) ci0 = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] (inlinedConst (userInliner env) ci0) (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl (inlinedConst (userInliner env) ci0) (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness (inlinedConst (userInliner env) ci0) (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st
def ExpU2Compose : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hInl : Tools.ShippingGen5ReaderTraceU2.InlineInputs env)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge) (hkd : Tools.ShippingGen5ReaderTraceU2.KDOfLeaf)
    (hss : Tools.ShippingGen5ReaderTraceU2.SameStLeaf)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st
def ExpU2RowC : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hInl : Tools.ShippingGen5ReaderTraceU2.InlineInputs env)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge) (hkd : Tools.ShippingGen5ReaderTraceU2.KDOfLeaf)
    (hss : Tools.ShippingGen5ReaderTraceU2.SameStLeaf)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d)
    (hqC : ∀ st : MachRead, ShapeAgree d st → Tools.ShippingGen5Cover3Canon.LetQuoteEqC d st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hvv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length),
    ∃ st : MachRead, ShapeAgree d st ∧
      ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

-- mutants (single changes; rejected by signature / defeq, NOT semantic counterexamples)
def MutDeclValueBvar1 : Lean.Environment → Prop := fun env =>
  ∀ (n : Lean.Name) (d : Lean.DefinitionVal), env.find? n = some (Lean.ConstantInfo.defnInfo d) →
    NoPh d.value = true ∧ BvarLt 1 d.value = true
def MutPackNoGuard : Prop :=
  ∀ e : Lean.Expr, Sparkle.Compiler.MachTupleIn.packTupleInputs e =
      Tools.ShippingGen5ReaderTracePack.packTupleInputsF (Tools.ShippingGen5ReaderTracePack.lamDepth e) e
def MutRawNodeOtherL : StructEnv → Prop := fun senv =>
  ∀ (L : Nat) (f a e' : Lean.Expr), NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch (Lean.Expr.app f a) = some e' →
    NoPh e' = true ∧ BvarLt (L + 1) e' = true
def MutNormNodeNoPh : StructEnv → Prop := fun senv =>
  ∀ (L : Nat) (f a : Lean.Expr), NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    BvarLt L (machNormNode senv (Lean.Expr.app f a)) = true
def MutKDOfFlip : Prop :=
  ∀ (lvl : Lean.Expr → Nat) (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape) (d : MachineData) (dd : DefinitionVal),
    E = ConstantInfo.defnInfo dd → Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d → nDeclOfCi E = kDOf d
def MutInlineNoInlined : Lean.Environment → Prop := fun env =>
  ∀ ci0 : ConstantInfo, CiDirect env ci0 → ∀ (sm : Bool) (ps : List (String × Nat)) (n : Nat),
    ShapeInputs' (nDeclOfCi ci0) (structEnv env) sm ps ci0 n
def MutFuelBridgeAnd : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
    machineShape? false [] E senv = some sp → machineShapeF 0 false [] E senv true = some (some sp)
def MutComposeBranchAnd : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hInl : Tools.ShippingGen5ReaderTraceU2.InlineInputs env)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge) (hkd : Tools.ShippingGen5ReaderTraceU2.KDOfLeaf)
    (hss : Tools.ShippingGen5ReaderTraceU2.SameStLeaf)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∧ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st
def MutComposeNDecl : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hInl : Tools.ShippingGen5ReaderTraceU2.InlineInputs env)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge) (hkd : Tools.ShippingGen5ReaderTraceU2.KDOfLeaf)
    (hss : Tools.ShippingGen5ReaderTraceU2.SameStLeaf)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (nDeclOfCi E) st ∧ LetsNoLoose st

-- leaf-free versions (rt61): KDOfLeaf / SameStLeaf / InlineInputs replaced by theorems
def ExpU2Core' : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge)
    {E : ConstantInfo} {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    (hIn : ∀ n : Nat, ShapeInputs' (nDeclOfCi E) (structEnv env) false [] E n)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st
def ExpU2Direct' : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge)
    {E : ConstantInfo} {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd) (hci : CiDirect env E)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st
def ExpU2Inline' : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge)
    {ci0 : ConstantInfo} (hci : CiDirect env ci0)
    {dd : DefinitionVal} (hEd : inlinedConst (userInliner env) ci0 = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] (inlinedConst (userInliner env) ci0) (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl (inlinedConst (userInliner env) ci0) (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness (inlinedConst (userInliner env) ci0) (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st
def ExpU2Compose' : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d),
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st
def ExpU2RowC' : Prop :=
  ∀ (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (hfb : Tools.ShippingGen5ReaderTraceU2.FuelBridge)
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d)
    (hqC : ∀ st : MachRead, ShapeAgree d st → Tools.ShippingGen5Cover3Canon.LetQuoteEqC d st)
    (hbb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hvv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length),
    ∃ st : MachRead, ShapeAgree d st ∧
      ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

end Expected

-- value samples for the twin definitions (by `rfl`, no `native_decide`)
example : Tools.ShippingGen5ReaderTracePack.lamDepth (Lean.Expr.bvar 0) = 0 := rfl
example (b : Lean.Expr) (n : Lean.Name) (t : Lean.Expr) (bi : Lean.BinderInfo) :
    Tools.ShippingGen5ReaderTracePack.lamDepth (Lean.Expr.lam n t b bi) = Tools.ShippingGen5ReaderTracePack.lamDepth b + 1 := rfl
example (e : Lean.Expr) : Tools.ShippingGen5ReaderTracePack.packTupleInputsF 0 e = e := rfl

def tyOf (n : Name) : MetaM Expr := do pure (← getConstInfo n).type

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``Tools.Assume.EnvDeclValue.DeclValuePh ``ExpDeclValuePh
  checkExpected ``Tools.Assume.PackTupleBridge.PackTupleInputsBridge ``ExpPackTupleInputsBridge
  checkExpected ``Tools.Assume.NormNodePh.RawNodePh ``ExpRawNodePh
  checkExpected ``Tools.Assume.NormNodePh.NormNodePh ``ExpNormNodePh
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.FuelBridge ``ExpFuelBridge
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.KDOfLeaf ``ExpKDOfLeaf
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.SameStLeaf ``ExpSameStLeaf
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.InlineInputs ``ExpInlineInputs
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_core ``ExpU2Core
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_compose_direct ``ExpU2Direct
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_compose_inline ``ExpU2Inline
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_compose ``ExpU2Compose
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_rowC ``ExpU2RowC
  -- twin definitions: types only (recursive definitions compile to `brecOn`; values are sampled by `rfl` above)
  let t1 ← tyOf ``Tools.ShippingGen5ReaderTracePack.lamDepth
  let t2 ← tyOf ``Tools.ShippingGen5ReaderTracePack.packTupleInputsF
  unless (← isDefEq t1 (mkForall `a .default (mkConst ``Lean.Expr) (mkConst ``Nat))) do
    throwError "GEN5 U2CHECK TYPE FAILED: lamDepth type {t1}"
  unless (← isDefEq t2 (mkForall `a .default (mkConst ``Nat) (mkForall `b .default (mkConst ``Lean.Expr) (mkConst ``Lean.Expr)))) do
    throwError "GEN5 U2CHECK TYPE FAILED: packTupleInputsF type {t2}"
  logInfo m!"GEN5 U2CHECK TYPE 13 declarations compared by checkExpected + 2 twin definitions by type (values sampled by rfl)"
  checkMutant ``Tools.Assume.EnvDeclValue.DeclValuePh ``MutDeclValueBvar1
  checkMutant ``Tools.Assume.PackTupleBridge.PackTupleInputsBridge ``MutPackNoGuard
  checkMutant ``Tools.Assume.NormNodePh.RawNodePh ``MutRawNodeOtherL
  checkMutant ``Tools.Assume.NormNodePh.NormNodePh ``MutNormNodeNoPh
  checkMutant ``Tools.ShippingGen5ReaderTraceU2.KDOfLeaf ``MutKDOfFlip
  checkMutant ``Tools.ShippingGen5ReaderTraceU2.InlineInputs ``MutInlineNoInlined
  checkMutant ``Tools.ShippingGen5ReaderTraceU2.FuelBridge ``MutFuelBridgeAnd
  checkMutant ``Tools.ShippingGen5ReaderTraceU2.u2_compose ``MutComposeBranchAnd
  checkMutant ``Tools.ShippingGen5ReaderTraceU2.u2_compose ``MutComposeNDecl
  logInfo m!"GEN5 U2CHECK MUTANT 9 statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

/-! ## Binder set: full `Lean.Name` matching -/

/-- Allowed head constants of the Prop binders of `u2_compose`, in binder order. -/
def allowedBinders : List Name :=
  [``Tools.Assume.ExprEqv.EqvAtom, ``Tools.Assume.N3Extern.ZeroLitAgrees0, ``Tools.ShippingLetsReaderInv.LiftAgrees,
   ``Tools.ShippingLetsReaderInv.Inst1Agrees, ``Tools.ShippingLetsReaderInv.EnvTypesFVarFree,
   ``Tools.Assume.EnvSigTy.SigTyClosed, ``Tools.Assume.EnvInstS.InstSFieldsDet,
   ``Tools.Assume.EnvDeclValue.DeclValuePh, ``Tools.Assume.PackTupleBridge.PackTupleInputsBridge,
   ``Tools.Assume.NormNodePh.RawNodePh, ``Tools.Assume.NormNodePh.NormNodePh,
   ``Tools.ShippingGen5ReaderTraceU2.InlineInputs, ``Tools.ShippingGen5ReaderTraceU2.FuelBridge,
   ``Tools.ShippingGen5ReaderTraceU2.KDOfLeaf, ``Tools.ShippingGen5ReaderTraceU2.SameStLeaf,
   ``Tools.ShippingGen5ReaderTrace.CiDirect, ``Or, ``Eq, ``Eq, ``Eq]

/-- Leaf hypotheses and who supplies them (they are hypotheses of the composition, not shown to hold). -/
def leafSuppliers : List (Name × String) :=
  [(``Tools.ShippingGen5ReaderTraceU2.InlineInputs, "sparkle-rt-inline-compose (rt44); its own hypotheses RecRulePh / pass_ph / S1 are not binders here"),
   (``Tools.ShippingGen5ReaderTraceU2.FuelBridge, "ledger row C.CV-4 (stays; not supplied by an Issue of this stream)"),
   (``Tools.ShippingGen5ReaderTraceU2.KDOfLeaf, "sparkle-rt-kdof (rt46)"),
   (``Tools.ShippingGen5ReaderTraceU2.SameStLeaf, "sparkle-rt-samest (rt47)")]

/-- Head constants of the binder types that are propositions, in binder order (fully qualified). -/
def propBinderHeads (thm : Name) : MetaM (List Name) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut out : List Name := []
    for x in xs do
      let t ← inferType x
      if (← isProp t) then
        match t.getAppFn.constName? with
        | some c => out := out ++ [c]
        | none => throwError "GEN5 U2CHECK BINDERS FAILED: Prop binder with non-constant head {t}"
    pure out

/-- Ordered, and as sets in both directions, the heads equal `allowed` (full-name equality). -/
def bindersMatch (heads allowed : List Name) : Bool :=
  heads == allowed && allowed.all heads.contains && heads.all allowed.contains

namespace Decoy
-- same tails as the registered / leaf names, other namespace (negative controls only)
def RawNodePh (_ : StructEnv) : Prop := True
def KDOfLeaf : Prop := True
theorem useDecoy (s : StructEnv) (_ : RawNodePh s) (_ : KDOfLeaf) : True := trivial
end Decoy

run_cmd Lean.Elab.Command.liftTermElabM do
  let heads ← propBinderHeads ``Tools.ShippingGen5ReaderTraceU2.u2_compose
  unless bindersMatch heads allowedBinders do
    throwError "GEN5 U2CHECK BINDERS FAILED: heads {heads}, allowed {allowedBinders}"
  -- direct branch takes no InlineInputs / Or; inline branch takes none of the direct-only premises
  let hd ← propBinderHeads ``Tools.ShippingGen5ReaderTraceU2.u2_compose_direct
  let hi ← propBinderHeads ``Tools.ShippingGen5ReaderTraceU2.u2_compose_inline
  unless !hd.contains ``Tools.ShippingGen5ReaderTraceU2.InlineInputs do throwError "GEN5 U2CHECK BINDERS FAILED: direct branch takes InlineInputs"
  for n in [``Tools.Assume.EnvDeclValue.DeclValuePh, ``Tools.Assume.PackTupleBridge.PackTupleInputsBridge,
      ``Tools.Assume.NormNodePh.RawNodePh, ``Tools.Assume.NormNodePh.NormNodePh, ``Tools.Assume.N3Extern.ZeroLitAgrees0] do
    unless !hi.contains n do throwError "GEN5 U2CHECK BINDERS FAILED: inline branch takes {n}"
  -- negative control: decoy binders (same tail, other namespace) are rejected by the full-name match
  let dh ← propBinderHeads ``Decoy.useDecoy
  unless dh == [``Decoy.RawNodePh, ``Decoy.KDOfLeaf] do throwError "GEN5 U2CHECK BINDERS CONTROL FAILED: decoy heads {dh}"
  let swapped := allowedBinders.map fun n =>
    if n == ``Tools.Assume.NormNodePh.RawNodePh then ``Decoy.RawNodePh
    else if n == ``Tools.ShippingGen5ReaderTraceU2.KDOfLeaf then ``Decoy.KDOfLeaf else n
  if bindersMatch swapped allowedBinders then throwError "GEN5 U2CHECK BINDERS CONTROL FAILED: decoy binders accepted"
  -- tail-only matching would have accepted the decoys
  let tails := allowedBinders.map Name.getString!
  unless swapped.all fun n => tails.contains n.getString! do throwError "GEN5 U2CHECK BINDERS CONTROL FAILED: tail contrast"
  for (n, who) in leafSuppliers do
    unless heads.contains n do throwError "GEN5 U2CHECK LEAVES FAILED: leaf {n} is not a binder"
    logInfo m!"GEN5 U2CHECK LEAF {n} <- {who}"
  logInfo m!"GEN5 U2CHECK BINDERS OK: {heads.length} Prop binders (16 named + Or + 3 Eq) match by full name; direct branch without InlineInputs; inline branch without the 5 direct-only premises; 1 decoy rejected (tail-only matching would accept)"

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingGen5ReaderTraceU2.u2_core, ``Tools.ShippingGen5ReaderTraceU2.u2_compose_direct,
      ``Tools.ShippingGen5ReaderTraceU2.u2_compose_inline, ``Tools.ShippingGen5ReaderTraceU2.u2_compose,
      ``Tools.ShippingGen5ReaderTraceU2.u2_rowC] do checkAxioms n

def closureRoots : List Name :=
  [``Tools.ShippingGen5ReaderTraceU2.u2_core, ``Tools.ShippingGen5ReaderTraceU2.u2_compose_direct,
   ``Tools.ShippingGen5ReaderTraceU2.u2_compose_inline, ``Tools.ShippingGen5ReaderTraceU2.u2_compose,
   ``Tools.ShippingGen5ReaderTraceU2.u2_rowC]

/-! ## Closure audit -/

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (NameSet × NameSet × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (closureOf env)).run ({}, {})
  pure (seen, unk, forbiddenConsts.filter seen.contains)

-- Negative controls (built in memory, no `sorry` token in this file)
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    let ok := mkConst ``True.intro
    addDecl (.thmDecl { name := `ReaderTraceU2Check.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceU2Check.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.thmDecl { name := `ReaderTraceU2Check.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceU2Check.direct, `ReaderTraceU2Check.viaHelper] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 U2CHECK CLOSURE CONTROL FAILED: {n} not detected"
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 U2CHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceU2Check.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 U2CHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 U2CHECK CLOSURE CONTROLS OK: 2 negative controls detected, 3 forbidden roots hit themselves, 2 unrelated clean controls clean"

/-! ## Watchlist (full `Lean.Name` equality; name scan only)

Premise-like names that must NOT be reached from the composition: the S1 externs (`ReplaceAgrees` `HeadBetaAgrees0`), the U1-era T1 rows that U1/U2 did not
re-enter, and the prose-only names `RecRulePh` `PassPh` `ShapeFuelBridge` (no constant of these names exists in this repository; the Check fails if one appears). -/

def watchOut : List Name :=
  [`Tools.Assume.AbbrevExtern.ReplaceAgrees, `Tools.Assume.AbbrevExtern.HeadBetaAgrees0,
   `Tools.Prototype.PreprocLetOk.ZeroLitAgrees,
   `Tools.Prototype.RawNodeRangeLetOk.LiftLooseRange, `Tools.Prototype.RawNodeRangeLetOk.LowerLooseRange,
   `Tools.Prototype.RawNodeRangeLetOk.BetaRange, `Tools.Prototype.LiftScalarModelLetOk.LiftScalarCorr,
   `Tools.Prototype.BoolMapModelLetOk.BoolMapCorr]
def watchProse : List Name := [`RecRulePh, `PassPh, `ShapeFuelBridge]
/-- Allowed premise constants (the named binder heads; `Or` / `Eq` are logic). -/
def allowedPremises : List Name := allowedBinders.filter fun n => n != ``Or && n != ``Eq
/-- Reached but not a binder: derived inside the proof (`RootFloatAgrees` is obtained from `LiftAgrees` by `rootFloatAgrees`, as in U1). -/
def derivedPremises : List Name := [`Tools.ShippingLetsReaderInv.RootFloatAgrees]
def watchAll : List Name := allowedPremises ++ derivedPremises ++ watchOut ++ watchProse

def watchReached (seen : NameSet) : List Name := watchAll.filter fun w => seen.contains w
/-- Reached constants with a watched last component but another full name. -/
def lookalikes (seen : NameSet) : List Name :=
  let tails := watchAll.map Name.getString!
  seen.toList.filter fun n => n.isStr && tails.contains n.getString! && !watchAll.contains n

namespace Decoy2
def Inst1Agrees : Prop := True
theorem useDecoy : Inst1Agrees := trivial
end Decoy2

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let missing := (allowedPremises ++ watchOut).filter fun w => !env.contains w
  unless missing.isEmpty do throwError "GEN5 U2CHECK WATCH FAILED: watched names that are not constants: {missing}"
  for w in watchProse do
    if env.contains w then throwError "GEN5 U2CHECK WATCH FAILED: prose-only name {w} now exists as a constant"
  logInfo m!"GEN5 U2CHECK WATCH NAMES OK: {allowedPremises.length + watchOut.length} constants (+ {derivedPremises.length} derived, checked at the closure) exist (env.contains); {watchProse} prose-only"

run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let prp : Lean.Expr := mkSort Level.zero
    addDecl (.defnDecl { name := `ReaderTraceU2Check.watchRef, levelParams := [], type := prp, value := mkConst ``Tools.Assume.AbbrevExtern.ReplaceAgrees, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceU2Check.watchClean, levelParams := [], type := tru, value := mkConst ``True.intro })
    let env ← getEnv
    let (s1, _, _) ← closureHits env [`ReaderTraceU2Check.watchRef]
    unless (watchReached s1).contains `Tools.Assume.AbbrevExtern.ReplaceAgrees do throwError "GEN5 U2CHECK WATCH CONTROL FAILED: reference not detected"
    let (s2, _, _) ← closureHits env [`ReaderTraceU2Check.watchClean]
    unless (watchReached s2).isEmpty && (lookalikes s2).isEmpty do throwError "GEN5 U2CHECK WATCH CONTROL FAILED: clean control flagged"
    let (s3, _, _) ← closureHits env [``Decoy2.useDecoy]
    unless (watchReached s3).isEmpty do throwError "GEN5 U2CHECK WATCH CONTROL FAILED: decoy matched a watched full name"
    unless (lookalikes s3).contains ``Decoy2.Inst1Agrees do throwError "GEN5 U2CHECK WATCH CONTROL FAILED: decoy not flagged"
    logInfo m!"GEN5 U2CHECK WATCH CONTROLS OK: 1 negative detected, 1 clean not, 1 same-tail decoy flagged"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  for n in closureRoots do
    unless seen.contains n do throwError "GEN5 U2CHECK CLOSURE FAILED: root {n} not in seen"
  unless hits.isEmpty do throwError "GEN5 U2CHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    if ((n.toString).splitOn "native_decide").length > 1 then
      throwError "GEN5 U2CHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 U2CHECK CLOSURE FAILED: unknown constants {unk.toList}"
  let reached := watchReached seen
  for a in allowedPremises do
    unless reached.contains a do throwError "GEN5 U2CHECK WATCH FAILED: allowed premise {a} not reached"
  for r in reached do
    unless allowedPremises.contains r || derivedPremises.contains r do throwError "GEN5 U2CHECK WATCH FAILED: unexpected premise name reached: {r}"
  let lk := lookalikes seen
  unless lk.isEmpty do throwError "GEN5 U2CHECK WATCH FAILED: same-tail constants in other namespaces reached: {lk}"
  let notReached := watchAll.filter (fun w => !reached.contains w)
  logInfo m!"GEN5 U2CHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots; no forbidden constant"
  logInfo m!"GEN5 U2CHECK WATCH OK: reached {reached.length} of {watchAll.length} watched full names (exactly the {allowedPremises.length} allowed + {derivedPremises.length} derived; no same-tail lookalike); not reached: {notReached}"
  logInfo m!"GEN5 U2CHECK COUNTS: TYPE 13 (+2 twin by type) / MUTANT 9 / BINDERS {allowedBinders.length} ({allowedPremises.length} named) / LEAVES 4 / AXIOMS 5 / WATCH {watchAll.length} full names ({allowedPremises.length + derivedPremises.length + watchOut.length} constants + {watchProse.length} prose-only) / WATCH-NEG 1 decoy + 1 binder decoy"

/-! ## Leaf-free theorems (rt61): TYPE / BINDERS / AXIOMS / CLOSURE for `u2_core'` `u2_compose_direct'` `u2_compose_inline'` `u2_compose'` `u2_rowC'`

Hypotheses of `u2_compose'` that are not registered N1-a / N2-b / N3-b / U1 rows: `FuelBridge` (C.CV-4), `RecRulePhU`, `ReplaceAgrees`, `HeadBetaAgreesL`, `BetaNonTargetAgrees`, `ExprEqvLaws` (pass_ph version; `PassPh` and `HeadBetaAgrees0` are no longer binders).
`KDOfLeaf` / `SameStLeaf` / `InlineInputs` are not binders and are not reached. Name matching is by full `Lean.Name`; nothing here shows that any hypothesis holds. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_core' ``ExpU2Core'
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_compose_direct' ``ExpU2Direct'
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_compose_inline' ``ExpU2Inline'
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_compose' ``ExpU2Compose'
  checkExpected ``Tools.ShippingGen5ReaderTraceU2.u2_rowC' ``ExpU2RowC'
  logInfo m!"GEN5 U2CHECK TYPE' 5 leaf-free theorems compared by checkExpected"

def allowedBinders2 : List Name :=
  [``Tools.Assume.ExprEqv.EqvAtom, ``Tools.Assume.N3Extern.ZeroLitAgrees0, ``Tools.ShippingLetsReaderInv.LiftAgrees,
   ``Tools.ShippingLetsReaderInv.Inst1Agrees, ``Tools.ShippingLetsReaderInv.EnvTypesFVarFree,
   ``Tools.Assume.EnvSigTy.SigTyClosed, ``Tools.Assume.EnvInstS.InstSFieldsDet,
   ``Tools.Assume.EnvDeclValue.DeclValuePh, ``Tools.Assume.PackTupleBridge.PackTupleInputsBridge,
   ``Tools.Assume.NormNodePh.RawNodePh, ``Tools.Assume.NormNodePh.NormNodePh,
   ``Tools.PassPh.RecRulePhU, ``Tools.Assume.AbbrevExtern.ReplaceAgrees, ``Tools.Assume.AbbrevExtern.HeadBetaAgreesL,
   ``Tools.PassPh.BetaNonTargetAgrees, ``Tools.Assume.ExprEqvGL.ExprEqvLaws,
   ``Tools.ShippingGen5ReaderTraceU2.FuelBridge, ``Tools.ShippingGen5ReaderTrace.CiDirect, ``Or, ``Eq, ``Eq, ``Eq]

def removedLeaves : List Name := [``Tools.ShippingGen5ReaderTraceU2.KDOfLeaf, ``Tools.ShippingGen5ReaderTraceU2.SameStLeaf, ``Tools.ShippingGen5ReaderTraceU2.InlineInputs]
def closureRoots2 : List Name :=
  [``Tools.ShippingGen5ReaderTraceU2.u2_core', ``Tools.ShippingGen5ReaderTraceU2.u2_compose_direct', ``Tools.ShippingGen5ReaderTraceU2.u2_compose_inline',
   ``Tools.ShippingGen5ReaderTraceU2.u2_compose', ``Tools.ShippingGen5ReaderTraceU2.u2_rowC']

run_cmd Lean.Elab.Command.liftTermElabM do
  let heads ← propBinderHeads ``Tools.ShippingGen5ReaderTraceU2.u2_compose'
  unless bindersMatch heads allowedBinders2 do
    throwError "GEN5 U2CHECK BINDERS' FAILED: heads {heads}, allowed {allowedBinders2}"
  for r in removedLeaves do
    if heads.contains r then throwError "GEN5 U2CHECK BINDERS' FAILED: removed leaf {r} is still a binder"
  -- direct branch takes no inline-only premises; inline branch none of the direct-only premises
  let hd ← propBinderHeads ``Tools.ShippingGen5ReaderTraceU2.u2_compose_direct'
  let hi ← propBinderHeads ``Tools.ShippingGen5ReaderTraceU2.u2_compose_inline'
  for n in [``Tools.PassPh.RecRulePhU, ``Tools.Assume.AbbrevExtern.ReplaceAgrees, ``Tools.Assume.AbbrevExtern.HeadBetaAgreesL,
      ``Tools.PassPh.BetaNonTargetAgrees, ``Tools.Assume.ExprEqvGL.ExprEqvLaws] do
    if hd.contains n then throwError "GEN5 U2CHECK BINDERS' FAILED: direct branch takes {n}"
    unless hi.contains n do throwError "GEN5 U2CHECK BINDERS' FAILED: inline branch lacks {n}"
  -- negative control: a decoy in another namespace is rejected by the full-name match
  let swapped := allowedBinders2.map fun n => if n == ``Tools.PassPh.BetaNonTargetAgrees then ``Decoy.KDOfLeaf else n
  if bindersMatch swapped allowedBinders2 then throwError "GEN5 U2CHECK BINDERS' CONTROL FAILED: decoy accepted"
  logInfo m!"GEN5 U2CHECK BINDERS' OK: {heads.length} Prop binders of u2_compose' match by full name; KDOfLeaf / SameStLeaf / InlineInputs are not binders of u2_compose' (u2_rowC' is covered by the closure)"
  logInfo m!"GEN5 U2CHECK REMAINING HYPOTHESES (u2_compose', besides the registered rows): {[``Tools.ShippingGen5ReaderTraceU2.FuelBridge, ``Tools.PassPh.RecRulePhU, ``Tools.Assume.AbbrevExtern.ReplaceAgrees, ``Tools.Assume.AbbrevExtern.HeadBetaAgreesL, ``Tools.PassPh.BetaNonTargetAgrees, ``Tools.Assume.ExprEqvGL.ExprEqvLaws]}"

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in closureRoots2 do checkAxioms n

def allowedPremises2 : List Name := allowedBinders2.filter fun n => n != ``Or && n != ``Eq
def watchOut2 : List Name := watchOut.filter fun n =>
  n != `Tools.Assume.AbbrevExtern.ReplaceAgrees && n != `Tools.Assume.AbbrevExtern.HeadBetaAgrees0
def watchAll2 : List Name := allowedPremises2 ++ derivedPremises ++ watchOut2 ++ removedLeaves ++ [`RecRulePh, `ShapeFuelBridge]

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots2
  for n in closureRoots2 do
    unless seen.contains n do throwError "GEN5 U2CHECK CLOSURE' FAILED: root {n} not in seen"
  unless hits.isEmpty do throwError "GEN5 U2CHECK CLOSURE' FAILED: forbidden constants {hits}"
  unless unk.isEmpty do throwError "GEN5 U2CHECK CLOSURE' FAILED: unknown constants {unk.toList}"
  let reached := watchAll2.filter fun w => seen.contains w
  for a in allowedPremises2 do
    unless reached.contains a do throwError "GEN5 U2CHECK WATCH' FAILED: allowed premise {a} not reached"
  for r in reached do
    unless allowedPremises2.contains r || derivedPremises.contains r do throwError "GEN5 U2CHECK WATCH' FAILED: unexpected name reached: {r}"
  let tails := watchAll2.map Name.getString!
  let lk := seen.toList.filter fun n => n.isStr && tails.contains n.getString! && !watchAll2.contains n
  unless lk.isEmpty do throwError "GEN5 U2CHECK WATCH' FAILED: same-tail constants in other namespaces reached: {lk}"
  logInfo m!"GEN5 U2CHECK CLOSURE' OK: {seen.toList.length} constants from {closureRoots2.length} roots; no forbidden constant; reached watched names = the {allowedPremises2.length} allowed + {derivedPremises.length} derived; KDOfLeaf / SameStLeaf / InlineInputs not reached; no same-tail lookalike"

end Tests.Gen5.ReaderTraceU2Check
