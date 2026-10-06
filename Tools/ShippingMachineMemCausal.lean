import Tools.ShippingMachineCausalCtx

/-! # A memory's read is causal

A memory call on the machine route is an instance of a memory-only child
(`Sparkle.Compiler.MachMemory`); the endpoint needs its value at a cycle to
be fixed by its operands up to that cycle, over contexts like any call entry
(`Tools.ShippingMachineCausalCtx`). The contents after the writes of the
cycles `< n` depend on the write operands at those cycles only
(`memState_congr`); a combinational read adds the read address at the cycle,
a registered read the one of the cycle before. -/
namespace Tools.ShippingMachineCausal
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Signal.Signal

theorem memState_congr {D : DomainConfig} {aw dw : Nat} (init : BitVec aw → BitVec dw)
    (wa wa' : Signal D (BitVec aw)) (wd wd' : Signal D (BitVec dw)) (we we' : Signal D Bool)
    (n : Nat)
    (h : ∀ c, c < n → wa.val c = wa'.val c ∧ wd.val c = wd'.val c ∧ we.val c = we'.val c) :
    memState init wa wd we n = memState init wa' wd' we' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext addr
    obtain ⟨ha, hd, he⟩ := h n (Nat.lt_succ_self n)
    rw [memState_succ, memState_succ, ha, hd, he,
      ih (fun c hc => h c (Nat.lt_succ_of_lt hc))]

/-- A combinational-read memory over contexts is causal when its operands are. -/
theorem memoryComboRead_causal_ctx {D : DomainConfig} {σ : Type} {aw dw : Nat}
    (wa : Ctx D σ → Signal D (BitVec aw)) (wd : Ctx D σ → Signal D (BitVec dw))
    (we : Ctx D σ → Signal D Bool) (ra : Ctx D σ → Signal D (BitVec aw))
    (hwa : ∀ x x' t, CtxAgree x x' t → (wa x).val t = (wa x').val t)
    (hwd : ∀ x x' t, CtxAgree x x' t → (wd x).val t = (wd x').val t)
    (hwe : ∀ x x' t, CtxAgree x x' t → (we x).val t = (we x').val t)
    (hra : ∀ x x' t, CtxAgree x x' t → (ra x).val t = (ra x').val t) :
    ∀ x x' t, CtxAgree x x' t →
      (memoryComboRead (wa x) (wd x) (we x) (ra x)).val t =
        (memoryComboRead (wa x') (wd x') (we x') (ra x')).val t := by
  intro x x' t h
  show memState _ (wa x) (wd x) (we x) t ((ra x).val t) =
    memState _ (wa x') (wd x') (we x') t ((ra x').val t)
  rw [memState_congr _ (wa x) (wa x') (wd x) (wd x') (we x) (we x') t (fun c hc =>
      ⟨hwa x x' c (h.mono (Nat.le_of_lt hc)), hwd x x' c (h.mono (Nat.le_of_lt hc)),
       hwe x x' c (h.mono (Nat.le_of_lt hc))⟩), hra x x' t h]

/-- A registered-read memory over contexts is causal when its operands are. -/
theorem memory_causal_ctx {D : DomainConfig} {σ : Type} {aw dw : Nat}
    (wa : Ctx D σ → Signal D (BitVec aw)) (wd : Ctx D σ → Signal D (BitVec dw))
    (we : Ctx D σ → Signal D Bool) (ra : Ctx D σ → Signal D (BitVec aw))
    (hwa : ∀ x x' t, CtxAgree x x' t → (wa x).val t = (wa x').val t)
    (hwd : ∀ x x' t, CtxAgree x x' t → (wd x).val t = (wd x').val t)
    (hwe : ∀ x x' t, CtxAgree x x' t → (we x).val t = (we x').val t)
    (hra : ∀ x x' t, CtxAgree x x' t → (ra x).val t = (ra x').val t) :
    ∀ x x' t, CtxAgree x x' t →
      (memory (wa x) (wd x) (we x) (ra x)).val t =
        (memory (wa x') (wd x') (we x') (ra x')).val t := by
  intro x x' t h
  cases t with
  | zero => rfl
  | succ n =>
    have hn : CtxAgree x x' n := h.mono (Nat.le_succ n)
    rw [memory_val_succ, memory_val_succ,
      memState_congr _ (wa x) (wa x') (wd x) (wd x') (we x) (we x') n (fun c hc =>
        ⟨hwa x x' c (hn.mono (Nat.le_of_lt hc)), hwd x x' c (hn.mono (Nat.le_of_lt hc)),
         hwe x x' c (hn.mono (Nat.le_of_lt hc))⟩), hra x x' n hn]

end Tools.ShippingMachineCausal
