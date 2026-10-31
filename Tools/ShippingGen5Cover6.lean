import Tools.ShippingGen5Cover3
import Tools.ShippingReaderLenOk
set_option autoImplicit false
-- Built in g5cv-r13 at ef0612b5 (Pod `kjob lake build Tools.ShippingGen5Cover6`, exit 0). Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # DG-COVER rev7 unit U-E3a: `FReachC` — the step closure extended by `CtrlEq` steps, and the `machReserve` step

Statements are those of `scripts/gen5/DG_COVER_FREEZE_REV7.md` §2.1 (U-E3a only; U-E3b is a roadmap and is not implemented here).
`CtrlEq` fixes the fields read by `FullInv` and leaves every other field of `MachRead` (`dom`, `nested`, `loops`, `inInner`, `runs`, …) FREE.
Consequently `fullInv_reachC` says nothing about `dom` (R-dom is a separate obligation), and nothing here connects any `readF` call to `FReachC`.
Not supplied: R-trace for `readF` calls, R-in, R-nl, R-dom, `TraceGood`, row 6b, `hbr`, real reader coverage. `fullInv_empty` is the specialisation of Cover3's `fullInv_of_empty`. -/

namespace Tools.ShippingGen5Cover6
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingReaderLenOk

/-- The fields read by `FullInv` are unchanged; every other field of `MachRead` is free. -/
def CtrlEq (st st' : MachRead) : Prop :=
  st'.lets = st.lets ∧ st'.insts = st.insts ∧ st'.instOrigins = st.instOrigins ∧
  st'.kinds = st.kinds ∧ st'.inits = st.inits ∧ st'.names = st.names ∧ st'.ws = st.ws

inductive FReachC (nDecl : Nat) : MachRead → MachRead → Prop
  | refl (st : MachRead) : FReachC nDecl st st
  | tail {a b c : MachRead} : FReachC nDecl a b → FStep nDecl b c → FReachC nDecl a c
  | ctrl {a b c : MachRead} : FReachC nDecl a b → CtrlEq b c → FReachC nDecl a c

theorem reachC_of_reach {nDecl : Nat} {a b : MachRead} (h : FReach nDecl a b) : FReachC nDecl a b := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .tail ih hs

theorem reachC_trans {nDecl : Nat} {a b c : MachRead} (h1 : FReachC nDecl a b) (h2 : FReachC nDecl b c) :
    FReachC nDecl a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact .tail ih hs
  | ctrl _ hc ih => exact .ctrl ih hc

/-- helper (not one of the six frozen statements): a `CtrlEq` step preserves `FullInv`. -/
theorem fullInv_ctrl {nDecl : Nat} {b c : MachRead} (h : FullInv nDecl b) (hc : CtrlEq b c) :
    FullInv nDecl c := by
  obtain ⟨hl, hi, ho, hk, _, _, hw⟩ := hc
  obtain ⟨hC, hR, hO, hK⟩ := h
  refine ⟨callOrderInv_congr hl hi hC,
    rangeInv_mono_aux hR (by rw [hi]; exact Nat.le_refl _) (by rw [hk]; exact Nat.le_refl _) hl hw, ?_, ?_⟩
  · simp only [OrigAligned, ho, hi] at hO ⊢
    exact hO
  · simp only [EntryKinds, hi, ho]
    exact hK

theorem fullInv_reachC {nDecl : Nat} {st0 st : MachRead} (h : FullInv nDecl st0) (hr : FReachC nDecl st0 st) :
    FullInv nDecl st := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact fullInv_step ih hs
  | ctrl _ hc ih => exact fullInv_ctrl ih hc

theorem reachC_sizes_mono {nDecl : Nat} {a b : MachRead} (hr : FReachC nDecl a b) :
    a.lets.size ≤ b.lets.size ∧ a.insts.size ≤ b.insts.size ∧ a.kinds.size ≤ b.kinds.size := by
  induction hr with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | tail _ hs ih =>
    have := fStep_sizes_mono hs
    exact ⟨Nat.le_trans ih.1 this.1, Nat.le_trans ih.2.1 this.2.1, Nat.le_trans ih.2.2 this.2.2⟩
  | ctrl _ hc ih =>
    obtain ⟨hl, hi, _, hk, _⟩ := hc
    rw [hl, hi, hk]
    exact ih

/-- the empty state satisfies `FullInv`: the specialisation of Cover3's `fullInv_of_empty` (not reproved). -/
theorem fullInv_empty {nDecl : Nat} : FullInv nDecl ({} : MachRead) :=
  fullInv_of_empty nDecl ({} : MachRead) rfl rfl rfl rfl

/-- `machReserve` is a slot append plus writes to fields outside `CtrlEq`'s list: premise-free. -/
theorem reserved_reachC {nDecl : Nat} {st : MachRead} {dom' body : Lean.Expr} {kinds : List MixedGateBinder}
    {inits : List Nat} :
    FReachC nDecl st (reserved st dom' body kinds inits) :=
  .ctrl (.tail (.refl st) (FStep.slots st kinds inits (machSlotNames st.runs.size body kinds st.kinds.size)))
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Tools.ShippingGen5Cover6
