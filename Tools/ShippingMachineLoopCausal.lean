import Tools.ShippingMachineCausalCtx

/-! # The source of a hand-written `Signal.loop` WITH calls is causal in its inputs (round par/b-39)

WRITTEN, NOT BUILT.

A parent's endpoint needs, of every sequential child, that the child's
source is causal in its inputs. The built theorems give it for four endpoint
heads (`src_causal_of_data`, `_data_ext`, `_data_causal`,
`src_causal_of_loop`). A loop child with calls (a memory read inside a
hand-written loop: `memCounterH`) has the head `machine_trace_of_loop_causal`
and no such theorem. This file is that theorem.

`machine_trace_of_loop_causal` has no separate state-stream lemma: its proof
unfolds the loop one step (`Signal.loopGo_eq`) to the step function applied
to the loop TRUNCATED after `t`, and uses `hcausal` (the calls' values agree
on loop states that agree up to `t`, at the SAME inputs). Here the truncated
loop is named (`truncLoop`), and `hcausal` is replaced by

    hjoint : inputs agree up to t → the ENCODED states agree up to t →
             the calls' values agree at t

— joint in the inputs and the state, and about the encoded state `σ i (l.val
c)` (what the induction gives: the raw states of two runs on different
inputs are equal only through `σ`). At equal inputs and equal raw states it
is `hcausal`. It is a hypothesis of the general theorem, to be DISCHARGED by
the generator per child; it must not surface as a premise of any endpoint.

The binders up to `_hcausal` are, in order, those of
`machine_trace_of_loop_causal` before its run (so the arguments of a child's
endpoint apply positionally, as `causalFactE` does for the other heads);
`hjoint` follows.

* `truncLoop`, `truncLoop_val`, `loop_val_succ` (pure).
* `src_causal_of_loop_causal`: the conclusion of `src_causal_of_loop`. -/
namespace Tools.ShippingMachineLoopCausal
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCausal

/-- The loop truncated after `c`: its values up to `c`, the default after. -/
def truncLoop {D : DomainConfig} {α : Type} [Inhabited α] (g : Signal D α → Signal D α)
    (c : Nat) : Signal D α :=
  ⟨fun s => if s < c + 1 then Signal.loopGo g s else default⟩

/-- The truncated loop is the loop up to `c`. -/
theorem truncLoop_val {D : DomainConfig} {α : Type} [Inhabited α] (g : Signal D α → Signal D α)
    (c : Nat) {s : Nat} (hs : s ≤ c) : (truncLoop g c).val s = (Signal.loop g).val s := by
  show (if s < c + 1 then Signal.loopGo g s else default) = Signal.loopGo g s
  rw [if_pos (by omega)]

/-- One step of the loop: the step function on the loop truncated after `c`. -/
theorem loop_val_succ {D : DomainConfig} {α : Type} [Inhabited α] (g : Signal D α → Signal D α)
    (c : Nat) : (Signal.loop g).val (c + 1) = (g (truncLoop g c)).val (c + 1) := by
  show Signal.loopGo g (c + 1) = (g (truncLoop g c)).val (c + 1)
  rw [Signal.loopGo_eq]
  all_goals rfl

set_option maxHeartbeats 2000000 in
/-- **The source of a hand-written `Signal.loop` with calls is causal in its
inputs**, from its endpoint's facts (the arguments of
`machine_trace_of_loop_causal`) and the joint causality of the calls'
extensions (`hjoint`, file header). -/
theorem src_causal_of_loop_causal {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) {α : ι → Type} [∀ i, Inhabited (α i)] {ρ : ι → Type}
    (σ : (i : ι) → α i → HList (tys d.ss))
    (inits : HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Signal (dom i) (α i))
    (res : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → ρ i)
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (_ok : d.ok = true)
    (_hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (_hinit : d.initOk inits = true)
    (h0 : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i)),
      σ i ((f i bools bits l).val 0) = inits)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i))
      (t : Nat),
      σ i ((f i bools bits l).val (t + 1)) =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (L : Signal (dom i) (α i))
      (t : Nat),
      (obsR i (res i bools bits L)).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (res i bools bits (Signal.loop (f i bools bits))))
    (_hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (l l' : Signal (dom i) (α i)) (t : Nat), (∀ c, c ≤ t → l.val c = l'.val c) →
      (∀ p w, (ext i bools bits l p w).val t = (ext i bools bits l' p w).val t) ∧
      (∀ p, (extB i bools bits l p).val t = (extB i bools bits l' p).val t))
    (hjoint : ∀ (i : ι) (B B' : Nat → Signal (dom i) Bool)
      (V V' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (l l' : Signal (dom i) (α i)) (t : Nat),
      (∀ p c, c ≤ t → (B p).val c = (B' p).val c) →
      (∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) →
      (∀ c, c ≤ t → σ i (l.val c) = σ i (l'.val c)) →
      (∀ p w, (ext i B V l p w).val t = (ext i B' V' l' p w).val t) ∧
      (∀ p, (extB i B V l p).val t = (extB i B' V' l' p).val t))
    (i : ι) (B B' : Nat → Signal (dom i) Bool)
    (V V' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat)
    (hb : ∀ p c, c ≤ t → (B p).val c = (B' p).val c)
    (hv : ∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) :
    ∀ (k : Nat) (f₁ f₂ : Nat → Nat), (src i B V)[k]? = some f₁ → (src i B' V')[k]? = some f₂ →
      f₁ t = f₂ t := by
  -- the encoded state at 0, and one step of it (the loop truncated after `c`)
  have zero : ∀ (Bx : Nat → Signal (dom i) Bool)
      (Vx : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      σ i ((Signal.loop (f i Bx Vx)).val 0) = inits := by
    intro Bx Vx
    show σ i (Signal.loopGo (f i Bx Vx) 0) = inits
    rw [Signal.loopGo_eq]
    exact h0 i Bx Vx _
  have step : ∀ (Bx : Nat → Signal (dom i) Bool)
      (Vx : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (c : Nat),
      σ i ((Signal.loop (f i Bx Vx)).val (c + 1)) =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls
            (extB i Bx Vx (truncLoop (f i Bx Vx) c)) (ext i Bx Vx (truncLoop (f i Bx Vx) c)) c
            (σ i ((Signal.loop (f i Bx Vx)).val c))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls
            (extB i Bx Vx (truncLoop (f i Bx Vx) c)) (ext i Bx Vx (truncLoop (f i Bx Vx) c)) c
            (σ i ((Signal.loop (f i Bx Vx)).val c))).v (d.vpos j) w) d.nexts := by
    intro Bx Vx c
    rw [loop_val_succ (f i Bx Vx) c, writes i Bx Vx (truncLoop (f i Bx Vx) c) c,
      truncLoop_val (f i Bx Vx) c (Nat.le_refl c)]
  -- the encoded states agree up to `t`
  have hall : ∀ c, c ≤ t → ∀ c', c' ≤ c →
      σ i ((Signal.loop (f i B V)).val c') = σ i ((Signal.loop (f i B' V')).val c') := by
    intro c
    induction c with
    | zero =>
      intro _ c' hc'
      have e0 : c' = 0 := by omega
      subst e0
      rw [zero B V, zero B' V']
    | succ c ih =>
      intro hc c' hc'
      rcases Nat.lt_or_ge c' (c + 1) with hlt | hge
      · exact ih (by omega) c' (by omega)
      · have e1 : c' = c + 1 := by omega
        subst e1
        have ihc := ih (by omega)
        obtain ⟨hv', hb'⟩ := hjoint i B B' V V' (truncLoop (f i B V) c)
          (truncLoop (f i B' V') c) c
          (fun p c2 h2 => hb p c2 (by omega)) (fun p n c2 h2 => hv p n c2 (by omega))
          (fun c2 h2 => by
            rw [truncLoop_val (f i B V) c h2, truncLoop_val (f i B' V') c h2]
            exact ihc c2 h2)
        rw [step B V c, step B' V' c, ihc c (Nat.le_refl c),
          typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls _ _ _ _ c _ hb' hv']
  intro k f₁ f₂ hf hf'
  rw [hsrc i B V] at hf
  rw [hsrc i B' V'] at hf'
  have e1 := congrArg (fun l => l[k]?) (hres i B V (Signal.loop (f i B V)) t)
  have e2 := congrArg (fun l => l[k]?) (hres i B' V' (Signal.loop (f i B' V')) t)
  simp only [List.getElem?_map, hf, hf', Option.map_some] at e1 e2
  obtain ⟨hv', hb'⟩ := hjoint i B B' V V' (Signal.loop (f i B V)) (Signal.loop (f i B' V')) t
    hb hv (fun c h => hall t (Nat.le_refl t) c h)
  rw [hall t (Nat.le_refl t) t (Nat.le_refl t),
    typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls _ _ _ _ t _ hb' hv'] at e1
  exact Option.some.inj (e1.trans e2.symm)

end Tools.ShippingMachineLoopCausal
