import Tools.Assume.EnvDeclValue
import Tools.Assume.PackTupleBridge
import Tools.Assume.NormNodePh
import Tools.ShippingGen5ReaderTraceDirect2
import Tools.ShippingGen5ReaderTraceDispatch
import Tools.ShippingGen5GDCover1
import Tools.ShippingGen5Cover3Canon
import Tools.ShippingGen5ReaderTraceKDOf
import Tools.ShippingGen5ReaderTraceSameSt
import Tools.ShippingGen5ReaderTraceInlineCompose
set_option autoImplicit false
-- rt127: follows the pass_ph inline composition (hp : PassPh gone; hh/hbt/hEq added); `kjob lake build Tools.ShippingGen5ReaderTraceU2Compose` exit 0 on the tree of 2d56a2a55959000514ddd8bf487515d6640282f8 (this line comment-only). Clean build is the coder's.
-- rt61: leaf-free theorems u2_core' / u2_compose_direct' / u2_compose_inline' / u2_compose' / u2_rowC' added (old ones kept); `kjob lake build Tools.ShippingGen5ReaderTraceU2Compose` exit 0 on the Lean content of 5c6177007416f405d661c6057f5178cbb6dea0ac (this line comment-only). Remaining hypotheses of u2_compose': registered rows, FuelBridge, PassPh, RecRulePhU, ReplaceAgrees, HeadBetaAgrees0. Clean build is the coder's.
-- Skeleton (exploration branch): `kjob lake build Tools.ShippingGen5ReaderTraceU2Compose` exit 0 on the Lean content of 2b771482e278441fbc250ef0bd5e962a81358be6 (cached target build; Assume imports added; this header is comment-only). No sorry / axiom / native_decide in source; the leaves are theorem HYPOTHESES (`KDOfLeaf` `SameStLeaf` `InlineInputs` `FuelBridge`), so this is NOT counted as accepted / approved / ledger subtraction. Clean build is the coder's.

/-! # RT U2 compose (skeleton; freeze `scripts/gen5/RT_U2_FREEZE.md`)

Composes, for BOTH entry branches (`entryConst` returns the original `ci0` or `inlinedConst (userInliner env) ci0`):
`readF_traceGood_of_premises` (U1) + `ShapeInputs'` (direct: `shapeInputs_of_direct'`; inline: hypothesis `InlineInputs env`, supplied by `sparkle-rt-inline-compose`)
+ `machineShapeF_reach'` + the two leaf identifications `KDOfLeaf` (`sparkle-rt-kdof`) and `SameStLeaf` (`sparkle-rt-samest`),
into the consumer facts `FullInv (kDOf d) st` and `LetsNoLoose st` of `rowC_of_reader_canon`.
N1-a / N2-b / N3-b are theorem hypotheses here, registered in `Tools/Assume/{EnvDeclValue,PackTupleBridge,NormNodePh}.lean` (moved verbatim from `Direct.lean`).
Conditional (intermediate) result: no hypothesis is shown to hold for accepted sources. -/

namespace Tools.ShippingGen5ReaderTraceU2
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel
open Tools.ShippingGen5Cover3 Tools.ShippingGen5GDCover1 Tools.ShippingGen5Cover3Canon Tools.ShippingMachineAuto Tools.ShippingGen5Sem

/-- The fuel bridge (C.CV-4, stays as a ledger row): a production `machineShape?` success has a fuel `n` with a `machineShapeF` success. -/
def FuelBridge : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
    machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)

/-- Leaf `sparkle-rt-kdof` (C.CV-3 side): the consumer's `kDOf d` is the reach side's `nDeclOfCi E`. -/
def KDOfLeaf : Prop :=
  ∀ (lvl : Lean.Expr → Nat) (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape) (d : MachineData) (dd : DefinitionVal),
    E = ConstantInfo.defnInfo dd → Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d → kDOf d = nDeclOfCi E

/-- Leaf `sparkle-rt-samest` (C.CV-2 side): two `StateSideWitness` for the same `(E, senv, sp, n)` have the same final state. -/
def SameStLeaf : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape) (n : Nat)
    (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr)
    (p' : ShapePre) (en' : Lean.Expr) (st0' : MachRead) (env' : List MachVal) (st1' st' : MachRead) (v' : Lean.Expr),
    StateSideWitness E senv sp n p en st0 env st1 st v → StateSideWitness E senv sp n p' en' st0' env' st1' st' v' → st = st'

/-- Inline branch input (supplied by `sparkle-rt-inline-compose`, whose own hypotheses `RecRulePh` / `pass_ph` / S1 are NOT taken here):
`ShapeInputs'` for the inlined constant. -/
def InlineInputs (env : Lean.Environment) : Prop :=
  ∀ ci0 : ConstantInfo, Tools.ShippingGen5ReaderTrace.CiDirect env ci0 → ∀ (sm : Bool) (ps : List (String × Nat)) (n : Nat),
    ShapeInputs' (nDeclOfCi (inlinedConst (userInliner env) ci0)) (structEnv env) sm ps (inlinedConst (userInliner env) ci0) n

theorem dims_of_dataOfAt {lvl : Lean.Expr → Nat} {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d) :
    d.shape = sp ∧ d.ss.length = sp.layout.slots.length ∧ d.ls.length = sp.layout.lets ∧ sp.insts.length ≤ d.nIn := by
  unfold Tools.ShippingGen5DataOf.dataOfAt at hd
  split at hd
  · cases hd
  · exact Tools.ShippingGen5DataOf.dataOfFrom_dims lvl hd

/-- Core: `ShapeInputs'` for the entry constant `E` at every fuel gives the consumer facts. -/
theorem u2_core
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hfb : FuelBridge) (hkd : KDOfLeaf) (hss : SameStLeaf)
    {E : ConstantInfo} {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    (hIn : ∀ n : Nat, ShapeInputs' (nDeclOfCi E) (structEnv env) false [] E n)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st := by
  obtain ⟨n, hn⟩ := hfb E (structEnv env) sp h
  obtain ⟨p, en, st0, env1, st1, st, v, w⟩ := Tools.ShippingGen5Cover5.machineShapeF_state_side hn
  have hT := readF_traceGood_of_premises env hK hC hla (Tools.PartialTotal.Agree.rootFloatAgrees hla) hi1 hD (nDeclOfCi E) n
  obtain ⟨p', en', st0', env1', st1', st', v', hp', hen', h0', h1', h2', h3', l2', i1', i2', i3', i4', -, -, -, hTr, -⟩ :=
    machineShapeF_reach' hE hT hn (hIn n)
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11⟩ := w
  have w' : StateSideWitness E (structEnv env) sp n p' en' st0' env1' st1' st' v' :=
    ⟨hp', hen', h0', h1', h2', h3', l2', i1', i2', i3', i4'⟩
  have w0 : StateSideWitness E (structEnv env) sp n p en st0 env1 st1 st v :=
    ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11⟩
  have hst : st = st' := hss E (structEnv env) sp n p en st0 env1 st1 st v p' en' st0' env1' st1' st' v' w0 w'
  subst hst
  obtain ⟨hsp, hss', hls, hn'⟩ := dims_of_dataOfAt hd
  have hkd' : kDOf d = nDeclOfCi E := hkd lvl E (structEnv env) sp d dd hEd hd
  refine ⟨n, p, en, st0, env1, st1, st, v, w0, Tools.ShippingGen5Cover5.shapeAgree_of_sides ⟨hw8, hw9, hw10, hw11⟩ hsp hss' hls hn', ?_, hTr.2.2.2.2.2.1⟩
  rw [hkd']
  exact hTr.1

/-- Direct branch (`entryConst` returns the original constant; `CiDirect env E`). -/
theorem u2_compose_direct
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hfb : FuelBridge) (hkd : KDOfLeaf) (hss : SameStLeaf)
    {E : ConstantInfo} {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    (hci : Tools.ShippingGen5ReaderTrace.CiDirect env E)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st :=
  u2_core hE hla hi1 env hK hC hD hfb hkd hss hEd
    (fun n => shapeInputs_of_direct' hz hla hi1 env hv hci hbr hraw hnode) h hd

/-- Inline branch (`entryConst` returns `inlinedConst (userInliner env) ci0`); `InlineInputs env` is the inline-compose theorem's conclusion. -/
theorem u2_compose_inline
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hInl : InlineInputs env)
    (hfb : FuelBridge) (hkd : KDOfLeaf) (hss : SameStLeaf)
    {ci0 : ConstantInfo} (hci : Tools.ShippingGen5ReaderTrace.CiDirect env ci0)
    {dd : DefinitionVal} (hEd : inlinedConst (userInliner env) ci0 = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] (inlinedConst (userInliner env) ci0) (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl (inlinedConst (userInliner env) ci0) (structEnv env) sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness (inlinedConst (userInliner env) ci0) (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st :=
  u2_core hE hla hi1 env hK hC hD hfb hkd hss hEd (fun n => hInl ci0 hci false [] n) h hd

/-- Both branches. The entry constant is the original `ci0` or its inlining. `InlineInputs env` is needed only for the second. -/
theorem u2_compose
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hInl : InlineInputs env)
    (hfb : FuelBridge) (hkd : KDOfLeaf) (hss : SameStLeaf)
    {ci0 E : ConstantInfo} (hci : Tools.ShippingGen5ReaderTrace.CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st := by
  rcases hbranch with rfl | rfl
  · exact u2_compose_direct hE hz hla hi1 env hK hC hD hv hbr hraw hnode hfb hkd hss hEd hci h hd
  · exact u2_compose_inline hE hla hi1 env hK hC hD hInl hfb hkd hss hci hEd h hd

/-- The consumer: `rowC_of_reader_canon` with its `hi` / `hnl` produced by `u2_compose` (the remaining binders `hqC` `hb` `hv` are other rows). -/
theorem u2_rowC
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hInl : InlineInputs env)
    (hfb : FuelBridge) (hkd : KDOfLeaf) (hss : SameStLeaf)
    {ci0 E : ConstantInfo} (hci : Tools.ShippingGen5ReaderTrace.CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d)
    (hqC : ∀ st : MachRead, ShapeAgree d st → LetQuoteEqC d st)
    (hb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hvv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length) :
    ∃ st : MachRead, ShapeAgree d st ∧
      ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true := by
  obtain ⟨n, p, en, st0, env', st1, st, v, -, hag, hi, hnl⟩ :=
    u2_compose hE hz hla hi1 env hK hC hD hv hbr hraw hnode hInl hfb hkd hss hci hbranch hEd h hd
  exact ⟨st, hag, rowC_of_reader_canon hag hi (hqC st hag) hnl hb hvv⟩

/-! ## Leaf-free versions (`KDOfLeaf` / `SameStLeaf` / `InlineInputs` replaced by theorems)

The old statements above are kept. Remaining hypotheses of the `'` versions: the registered N1-a / N2-b / N3-b (`DeclValuePh`, `PackTupleInputsBridge`, `RawNodePh`, `NormNodePh`),
`FuelBridge` (C.CV-4), and, on the inline branch only, `RecRulePhU`, `ReplaceAgrees`, `HeadBetaAgreesL`, `BetaNonTargetAgrees`, `ExprEqvLaws` (the pass_ph version of the inline composition; `PassPh` is gone). -/

/-- `u2_core` with `KDOfLeaf` ↦ `kDOf_eq_nDeclOfCi` and `SameStLeaf` ↦ `reach'_of_witness` (via `stateSide_functional`). -/
theorem u2_core'
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hfb : FuelBridge)
    {E : ConstantInfo} {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    (hIn : ∀ n : Nat, ShapeInputs' (nDeclOfCi E) (structEnv env) false [] E n)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st := by
  obtain ⟨n, hn⟩ := hfb E (structEnv env) sp h
  obtain ⟨p, en, st0, env1, st1, st, v, w⟩ := Tools.ShippingGen5Cover5.machineShapeF_state_side hn
  have hT := readF_traceGood_of_premises env hK hC hla (Tools.PartialTotal.Agree.rootFloatAgrees hla) hi1 hD (nDeclOfCi E) n
  obtain ⟨-, -, -, hTr, -⟩ := reach'_of_witness hE hT hn (hIn n) w
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11⟩ := w
  obtain ⟨hsp, hss', hls, hn'⟩ := dims_of_dataOfAt hd
  have hkd' : kDOf d = nDeclOfCi E := by
    subst hEd
    exact kDOf_eq_nDeclOfCi lvl hd
  refine ⟨n, p, en, st0, env1, st1, st, v, ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11⟩,
    Tools.ShippingGen5Cover5.shapeAgree_of_sides ⟨hw8, hw9, hw10, hw11⟩ hsp hss' hls hn', ?_, hTr.2.2.2.2.2.1⟩
  rw [hkd']
  exact hTr.1

/-- Direct branch, leaf-free. -/
theorem u2_compose_direct'
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hfb : FuelBridge)
    {E : ConstantInfo} {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    (hci : Tools.ShippingGen5ReaderTrace.CiDirect env E)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st :=
  u2_core' hE hla hi1 env hK hC hD hfb hEd
    (fun n => shapeInputs_of_direct' hz hla hi1 env hv hci hbr hraw hnode) h hd

/-- Inline branch, leaf-free: `InlineInputs env` ↦ `shapeInputs_of_inline'`; its hypotheses `RecRulePhU` `ReplaceAgrees` `HeadBetaAgreesL` `BetaNonTargetAgrees` `ExprEqvLaws` appear here. -/
theorem u2_compose_inline'
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (hfb : FuelBridge)
    {ci0 : ConstantInfo} (hci : Tools.ShippingGen5ReaderTrace.CiDirect env ci0)
    {dd : DefinitionVal} (hEd : inlinedConst (userInliner env) ci0 = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] (inlinedConst (userInliner env) ci0) (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl (inlinedConst (userInliner env) ci0) (structEnv env) sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness (inlinedConst (userInliner env) ci0) (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st := by
  obtain ⟨c, hc⟩ := hci
  exact u2_core' hE hla hi1 env hK hC hD hfb hEd
    (fun n => Tools.ShippingGen5ReaderTrace.shapeInputs_of_inline' hz hla hi1 env hv hrr hr hh hbt hEq hc rfl hbr hraw hnode) h hd

/-- Both branches, leaf-free. -/
theorem u2_compose'
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (hfb : FuelBridge)
    {ci0 E : ConstantInfo} (hci : Tools.ShippingGen5ReaderTrace.CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧ ShapeAgree d st ∧
      FullInv (kDOf d) st ∧ LetsNoLoose st := by
  rcases hbranch with rfl | rfl
  · exact u2_compose_direct' hE hz hla hi1 env hK hC hD hv hbr hraw hnode hfb hEd hci h hd
  · exact u2_compose_inline' hE hz hla hi1 env hK hC hD hv hbr hraw hnode hrr hr hh hbt hEq hfb hci hEd h hd

/-- The consumer with the leaf-free composition. -/
theorem u2_rowC'
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (hfb : FuelBridge)
    {ci0 E : ConstantInfo} (hci : Tools.ShippingGen5ReaderTrace.CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d)
    (hqC : ∀ st : MachRead, ShapeAgree d st → LetQuoteEqC d st)
    (hbb : ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length) (hvv : ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length) :
    ∃ st : MachRead, ShapeAgree d st ∧
      ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true := by
  obtain ⟨n, p, en, st0, env', st1, st, v, -, hag, hi, hnl⟩ :=
    u2_compose' hE hz hla hi1 env hK hC hD hv hbr hraw hnode hrr hr hh hbt hEq hfb hci hbranch hEd h hd
  exact ⟨st, hag, rowC_of_reader_canon hag hi (hqC st hag) hnl hbb hvv⟩

end Tools.ShippingGen5ReaderTraceU2
