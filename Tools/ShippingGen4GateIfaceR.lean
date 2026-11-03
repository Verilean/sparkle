import Tools.ShippingGen4IfaceR
import Tools.ShippingGen4GateLeafR
set_option autoImplicit false
-- BUILT by kjob lake build (focused, exit 0) at 6153c0ef; clean build is the coder's. U-GC0 (scripts/gen2/GATE_GC0_FREEZE.md): transfer of kjob/g4gate-g6 to base 15cd9d1f. No sorry / axiom / native_decide.

/-! # M4 gate supply, U-G2: the combinational mixed-gate leaf at the child interface
`GateLeaf` carries the premises of `gate_combChildRunN`; `entry` and the run `RealChildA` are hypotheses, not fields.
The accepted producer is reused unchanged. Intermediate result: no route 1, width-1, sequential, instance-parent or Top. -/

namespace Tools.ShippingGen2
open Sparkle.IR.Type (HWType)
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildInv (Res)
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInvA (RefLawsAOps)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingUnifiedSource (SType Term quote)
open Tools.ShippingMixedSourceBridge (inputExpr)

variable {ι : Type}
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- The premises of `gate_combChildRunN` as per-declaration data. `entry` and the run `RealChildA` are NOT fields. -/
structure GateLeaf (ι : Type) where
  decl : Name
  value : Lean.Expr
  domE : Lean.Expr
  bs : List (Name × MixedGateBinder)
  kb : Nat
  kv : Nat
  vw : Nat → Nat
  bpos : Nat → Nat
  vpos : Nat → Nat
  srt : SType
  e : Term srt
  old  : ∀ d : Lean.DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none
  peel : mixedGatePeel value = some (bs, quote domE (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e)
  he   : e.WF kb kv vw
  hb   : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool)
  hv   : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))

def GateLeaf.outField (ty : HWType) : OutField := ⟨"out", 0, ty.bitWidth, ty⟩

noncomputable def GateLeaf.ifaceOf (g : GateLeaf ι) (ty : HWType) : ChildIface ι :=
  ⟨g.decl, g.bs, [GateLeaf.outField ty], fun _ => gateS g.bs g.e g.bpos g.vpos⟩

theorem combChildRunN_out_congr (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (dsn : Design) (n : Nat)
    (mc : Sparkle.IR.AST.Module) (bsC : List (Name × MixedGateBinder)) (o₁ o₂ : OutField)
    (S : (Nat → List Nat) → List (Nat → Nat)) (hn : o₁.name = o₂.name) (ht : o₁.ty = o₂.ty) :
    CombChildRunN children dsn n mc bsC [o₁] S → CombChildRunN children dsn n mc bsC [o₂] S := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, h2, h3, h4, h5, h6, ?_⟩
  · rw [h1]; simp [hn, ht]
  intro T ins s vals hrange hports hreset
  obtain ⟨envs, hr, hl, hk⟩ := h7 T ins s vals hrange hports hreset
  refine ⟨envs, hr, hl, ?_⟩
  intro j hj k o f ho hf
  cases k with
  | succ k => simp at ho
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
    subst ho
    rw [← hn]
    exact hk j hj 0 o₁ f (by simp) hf

theorem gateLeaf_childPortWidthsI (O : RefLawsAOps MkRefd mref cref) (g : GateLeaf ι)
    (entry : EntryDefines mctx mref cctx cref g.decl g.value) {y : Res} (h : RealChildA O g.decl y) (ty : HWType) :
    ChildPortWidthsI (g.ifaceOf ty) y.1 := by
  have hfull := Tools.ShippingCallsGateA.childFull_of_realA O entry g.old g.peel g.he g.hb g.hv h
  have harg : Tools.ShippingMachineCompose.argPorts y.1 = y.1.inputs := by
    have h0 := Tools.ShippingGateChildIfaceP.inPortsOf_of_alloc hfull.comb.inputAlloc
    first
      | exact h0
      | (unfold Tools.ShippingMachineCompose.argPorts; unfold Tools.ShippingInstStmtG.inPortsOf at h0; exact h0)
  unfold ChildPortWidthsI
  rw [harg]
  have ht := congrArg (List.map HWType.bitWidth) hfull.tys
  simp only [List.map_map] at ht
  exact ht


/-- U-G2. Same premises as `gate_combChildRunN` (route 2, G2a-c only). -/
theorem gateLeaf_childShips (O : RefLawsAOps MkRefd mref cref) (g : GateLeaf ι)
    (entry : EntryDefines mctx mref cctx cref g.decl g.value) {y : Res} (h : RealChildA O g.decl y) :
    y.2.modules = [] ∧ ∃ ty : HWType, y.1.outputs = [{ name := "out", ty := ty }] ∧
      ∀ n, ChildShipsI (g.ifaceOf ty) n y.1 y.2 := by
  obtain ⟨hm, o, ho, hout, hrun⟩ := gate_combChildRunN O entry g.old g.peel g.he g.hb g.hv h
  refine ⟨hm, o.ty, ?_, ?_⟩
  · rw [hout, ho]
  · intro n
    refine ⟨gateLeaf_childPortWidthsI O g entry h o.ty, ?_⟩
    intro dsn _ _ i
    exact Or.inr (combChildRunN_out_congr _ dsn n _ _ o (GateLeaf.outField o.ty) _ ho rfl (hrun dsn n))

/-- U-G2. `Q` is an INPUT. The supplier of `Q g.decl = some (g.ifaceOf ty)` is the assembler of the route table, not this unit. -/
theorem gateLeaf_shipsResI (L : Laws mref cref) (g : GateLeaf ι) (Q : IfaceMap ι) {y : Res} {ty : HWType}
    (hQ : Q g.decl = some (g.ifaceOf ty)) (h : RealChildA L.O g.decl y)
    (hchild : ∀ n, ChildShipsI (g.ifaceOf ty) n y.1 y.2) (hinst : InstClosed y) : ShipsResI L Q g.decl y :=
  ⟨h, ⟨g.ifaceOf ty, 0, hQ, rfl, hchild 0⟩, hinst⟩

theorem instClosed_of_nil (y : Res) (hm : y.2.modules = []) : InstClosed y := by
  intro g hg
  rw [hm] at hg
  exact absurd hg (List.not_mem_nil)

theorem gateLeaf_shipsResI_of_real (L : Laws mref cref) (g : GateLeaf ι) (Q : IfaceMap ι)
    (entry : EntryDefines mctx mref cctx cref g.decl g.value) {y : Res} (h : RealChildA L.O g.decl y)
    (hQ : ∀ ty : HWType, y.1.outputs = [{ name := "out", ty := ty }] → Q g.decl = some (g.ifaceOf ty)) :
    ShipsResI L Q g.decl y := by
  obtain ⟨hm, ty, hty, hchild⟩ := gateLeaf_childShips L.O g entry h
  exact gateLeaf_shipsResI L g Q (hQ ty hty) h hchild (instClosed_of_nil y hm)

end Tools.ShippingGen2
