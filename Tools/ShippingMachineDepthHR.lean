import Tools.ShippingMachineDepthH
import Tools.ShippingMachineComposeR
import Tools.ShippingMachineDepthRunR

/-! # A child with one-output combinational calls, at depth 0, the boundary derived

`composedN0_of_H` turns a combinational parent's composed theorem into the
depth-0 form a parent of it composes, given `BndH` — the calls' premise and
`kidsComb` of the run. With the derived composed theorem
(`machine_composedR`: no calls' premise, `ChildSynthIs` and reflection facts
in the run's contexts), `BoundH` is trivial, and `kidsComb` of the run comes
from the run itself: its closing CHECKS it (`kidsCombB`, `closeInsts_kidsComb`). -/
namespace Tools.ShippingMachineDepthHR
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingEntrySoundness
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

theorem readsClosedB_eq : ∀ (S : List String) (body : List Stmt),
    readsClosedB S body = Tools.ShippingHierOptRunH.readsClosed S body
  | _, [] => rfl
  | S, st :: rest => by
    simp only [readsClosedB, Tools.ShippingHierOptRunH.readsClosed, readsClosedB_eq]

theorem kidsComb_of_B {ms : List Sparkle.IR.AST.Module} {body : List Stmt} (h : kidsCombB ms body = true) :
    Tools.ShippingMachineDepthH.kidsComb ms body = true := by
  unfold kidsCombB at h
  unfold Tools.ShippingMachineDepthH.kidsComb
  rw [List.all_eq_true] at h ⊢
  intro st hst
  have := h st hst
  cases st with
  | inst mn iname conns =>
    simp only [readsClosedB_eq] at this
    exact this
  | _ => rfl

/-- **A one-output combinational parent at depth 0, the run boundary derived.** -/
theorem composedN0_of_HR {declName : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    (Rest : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    (hsimple : d.shape.instFields = []) (hi : d.shape.insts ≠ [])
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      Tools.ShippingChildSynth.ChildSynthIs mctx mref cctx cref ∧ Rest mctx mref cctx cref →
      Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) declName d kD m design dom src ext) :
    ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      Tools.ShippingChildSynth.ChildSynthIs mctx mref cctx cref ∧ Rest mctx mref cctx cref →
      Tools.ShippingMachineDepthRun.ComposedNW 0 declName d kD m design dom src ext
        (fun _ bools _ => bools) := by
  intro mctx mref cctx cref w w' m design hr entry closes hb
  have hC := composed hr entry closes hb
  obtain ⟨t, t', d₀, children, _, hcc, _⟩ :=
    Tools.ShippingChildSynth.machine_children_real hr entry closes hb.1 hi
  have hcomb : Tools.ShippingMachineDepthH.kidsComb design.modules m.body = true := by
    rcases hcc with ⟨_, h⟩ | ⟨hfe, _, _⟩
    · exact kidsComb_of_B (Tools.ShippingChildServe.closeInsts_kidsComb h)
    · exact absurd hsimple hfe
  exact Tools.ShippingMachineDepthH.composedNW0_of_H hC
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) hcomb

end Tools.ShippingMachineDepthHR
