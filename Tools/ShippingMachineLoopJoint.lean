import Tools.ShippingMachineLoopCausal

/-! # The joint causality of a loop child's calls, from its context form (round par/c-1)

WRITTEN, NOT BUILT.

`src_causal_of_loop_causal` (`Tools/ShippingMachineLoopCausal.lean`) takes

    hjoint : inputs agree up to t → the ENCODED states agree up to t →
             the calls' values agree at t

The generator of a hand-written loop with calls (`loopCalls`,
`Tools/ShippingMachineCommand.lean`) already proves, per call entry `k`, the
theorem `f.machine_causal_{k}`: the entry is causal over CONTEXTS
`Ctx D α` — the two input families AND the loop's RAW state signal
(`CtxAgree`). The endpoint's `hcausal` is those facts at equal inputs
(`CtxAgree.of_state`). So the joint fact over contexts is the same chain at
differing inputs (`hctx` below, generated as `f.machine_ext_ctx`).

What is left between `hctx` and `hjoint` is the state premise: `hjoint` has
the encoded states equal, `CtxAgree` the raw ones. The encoding of a loop
state (`treeSigma`: the leaves of the tree of pairs, as a right-nested tuple)
has a LEFT INVERSE (the tree rebuilt from the tuple's components), hence is
injective (`eq_of_leftInv`; the inverse and its equation `fun x => rfl` are
generated per declaration, as `f.machine_sigma_inj`).

* `eq_of_leftInv`: a function with a left inverse is injective.
* `ext_joint_of_ctx`: `hjoint` from the injectivity of the encoding and the
  causality of the extensions over contexts. Its conclusion is, binder for
  binder, the `hjoint` of `src_causal_of_loop_causal`. -/
namespace Tools.ShippingMachineLoopJoint
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCausal

/-- A function with a left inverse is injective. -/
theorem eq_of_leftInv {α β : Type} (σ : α → β) (τ : β → α) (hτ : ∀ x, τ (σ x) = x)
    (x x' : α) (h : σ x = σ x') : x = x' :=
  (hτ x).symm.trans ((congrArg τ h).trans (hτ x'))

/-- **The `hjoint` of `src_causal_of_loop_causal`**, from the injectivity of
the state encoding (`hinj`) and the causality of the calls' extensions over
contexts — the inputs and the raw state (`hctx`). -/
theorem ext_joint_of_ctx (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) {α : ι → Type}
    (σ : (i : ι) → α i → HList (tys d.ss))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Nat → Signal (dom i) Bool)
    (hinj : ∀ (i : ι) (x x' : α i), σ i x = σ i x' → x = x')
    (hctx : ∀ (i : ι) (x x' : Ctx (dom i) (α i)) (t : Nat), CtxAgree x x' t →
      (∀ p w, (ext i x.B x.V x.S p w).val t = (ext i x'.B x'.V x'.S p w).val t) ∧
      (∀ p, (extB i x.B x.V x.S p).val t = (extB i x'.B x'.V x'.S p).val t)) :
    ∀ (i : ι) (B B' : Nat → Signal (dom i) Bool)
      (V V' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (l l' : Signal (dom i) (α i)) (t : Nat),
      (∀ p c, c ≤ t → (B p).val c = (B' p).val c) →
      (∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) →
      (∀ c, c ≤ t → σ i (l.val c) = σ i (l'.val c)) →
      (∀ p w, (ext i B V l p w).val t = (ext i B' V' l' p w).val t) ∧
      (∀ p, (extB i B V l p).val t = (extB i B' V' l' p).val t) := by
  intro i B B' V V' l l' t hb hv hs
  have hag : CtxAgree (⟨B, V, l⟩ : Ctx (dom i) (α i)) ⟨B', V', l'⟩ t :=
    ⟨hb, hv, fun c hc => hinj i (l.val c) (l'.val c) (hs c hc)⟩
  exact hctx i ⟨B, V, l⟩ ⟨B', V', l'⟩ t hag

end Tools.ShippingMachineLoopJoint
