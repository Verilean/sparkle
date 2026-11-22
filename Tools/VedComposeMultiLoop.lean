import Tools.VedU2HierMultiLoop

/-!
# VED compose, multi-circuit parent: fusion of two wired loops (unit 9, lemma only)

`loop_pair`: two `Signal.loop`s wired feed-forward, `A = loop FA` and `B = loop (FB A)` (the shape of two `circuit do` blocks
wired by `let` outside each other), are the two components of ONE loop over the product state, whose body is
`(FA (fst p), FB (fst p) (snd p))`.  Both bodies must be causal (a register delays by one cycle): `hA`, `hB`, the same kind of fact
as `hcF` of `genOpenMulti`.  The proof is `loop_unique` (a causal body has a unique fixed point) at the pair of the two loops.

Not wired into the generator: the open parent of `genOpenMulti` is still one `runCircuitH`.  See docs/VED-COMPOSE-CONNECT.md, unit 9.
-/

open Sparkle.Core.Domain Sparkle.Core.Signal

namespace Tools.VedComposeMulti

theorem loop_pair {dom : DomainConfig} {α β : Type} [Inhabited α] [Inhabited β] [Inhabited (α × β)]
    (FA : Signal dom α → Signal dom α) (FB : Signal dom α → Signal dom β → Signal dom β)
    (hA : ∀ t (x y : Signal dom α), (∀ i, i < t → x.val i = y.val i) → (FA x).val t = (FA y).val t)
    (hB : ∀ t (x x' : Signal dom α) (y y' : Signal dom β), (∀ i, i < t → x.val i = x'.val i) →
       (∀ i, i < t → y.val i = y'.val i) → (FB x y).val t = (FB x' y').val t) :
    ∀ t, (Signal.loop (fun p : Signal dom (α × β) =>
          (⟨fun i => ((FA (Signal.map Prod.fst p)).val i, (FB (Signal.map Prod.fst p) (Signal.map Prod.snd p)).val i)⟩ : Signal dom (α × β)))).val t
      = ((Signal.loop FA).val t, (Signal.loop (FB (Signal.loop FA))).val t) := by
  intro t
  have hfixA : ∀ t, (FA (Signal.loop FA)).val t = (Signal.loop FA).val t := by
    intro t
    show _ = Signal.loopGo FA t
    rw [Signal.loopGo_eq]
    exact (hA t _ _ (fun i hi => by
      show (if i < t then Signal.loopGo FA i else default) = (Signal.loop FA).val i
      rw [if_pos hi]; rfl)).symm
  have hfixB : ∀ t, (FB (Signal.loop FA) (Signal.loop (FB (Signal.loop FA)))).val t
      = (Signal.loop (FB (Signal.loop FA))).val t := by
    intro t
    show _ = Signal.loopGo (FB (Signal.loop FA)) t
    rw [Signal.loopGo_eq]
    exact (hB t _ _ _ _ (fun _ _ => rfl) (fun i hi => by
      show (if i < t then Signal.loopGo (FB (Signal.loop FA)) i else default) = (Signal.loop (FB (Signal.loop FA))).val i
      rw [if_pos hi]; rfl)).symm
  refine Tools.VedU2HierMulti.loop_unique (fun p : Signal dom (α × β) =>
          (⟨fun i => ((FA (Signal.map Prod.fst p)).val i, (FB (Signal.map Prod.fst p) (Signal.map Prod.snd p)).val i)⟩ : Signal dom (α × β)))
      ?_ (⟨fun i => ((Signal.loop FA).val i, (Signal.loop (FB (Signal.loop FA))).val i)⟩ : Signal dom (α × β)) ?_ t
  · intro t x y h
    show ((FA (Signal.map Prod.fst x)).val t, (FB (Signal.map Prod.fst x) (Signal.map Prod.snd x)).val t)
       = ((FA (Signal.map Prod.fst y)).val t, (FB (Signal.map Prod.fst y) (Signal.map Prod.snd y)).val t)
    have h1 : ∀ i, i < t → (Signal.map Prod.fst x).val i = (Signal.map Prod.fst y).val i := fun i hi => by
      show (x.val i).1 = (y.val i).1; rw [h i hi]
    have h2 : ∀ i, i < t → (Signal.map Prod.snd x).val i = (Signal.map Prod.snd y).val i := fun i hi => by
      show (x.val i).2 = (y.val i).2; rw [h i hi]
    rw [hA t _ _ h1, hB t _ _ _ _ h1 h2]
  · intro t
    show ((FA (Signal.loop FA)).val t, (FB (Signal.loop FA) (Signal.loop (FB (Signal.loop FA)))).val t) = _
    rw [hfixA t, hfixB t]
end Tools.VedComposeMulti
