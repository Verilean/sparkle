import Tools.ShippingGen5ReaderTraceCtl
import Tools.ShippingGen5ReaderTraceReg
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceExtract, exit 0) on the tree of 1e130cf552b475ea1b1d6ccab006d54bd4dcaca0 (Lean content identical; this header is comment-only). Written against freeze rev9 `scripts/gen5/DG_READERTRACE_FREEZE_REV9.md` §2 (U-R4e1: extractor Ph lemmas, no premise); clean issue-linked build pending (coder). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R4e1: `machRunApp?` / `machInstCall?` / `machInstCallS?` (args) / `memCall?` results are `NoPh ∧ BvarLt`

The call spine's components are subterms of the input, so `NoPh e ∧ BvarLt L e` passes to them. No `senv` condition. The `ty` component of `machInstCallS?` (U-R4e2) is NOT here: it comes from the environment
table, not from the input (freeze rev9 §3, a candidate named condition awaiting reviewer approval). -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

theorem inlSpine_ph {L : Nat} : ∀ (e : Lean.Expr) (acc : List Lean.Expr), NoPh e = true → BvarLt L e = true →
    (∀ a ∈ acc, NoPh a = true ∧ BvarLt L a = true) →
    ∀ a ∈ (inlSpine e acc).2, NoPh a = true ∧ BvarLt L a = true
  | .app f a, acc, hn, hb, hacc => by
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    unfold inlSpine
    refine inlSpine_ph f (a :: acc) hn.1 hb.1 ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hn.2, hb.2⟩
    · exact hacc x hx
  | .bvar _, _, _, _, hacc => hacc
  | .fvar _, _, _, _, hacc => hacc
  | .mvar _, _, _, _, hacc => hacc
  | .sort _, _, _, _, hacc => hacc
  | .const _ _, _, _, _, hacc => hacc
  | .lit _, _, _, _, hacc => hacc
  | .lam _ _ _ _, _, _, _, hacc => hacc
  | .forallE _ _ _ _, _, _, _, hacc => hacc
  | .letE _ _ _ _ _, _, _, _, hacc => hacc
  | .mdata _ _, _, _, _, hacc => hacc
  | .proj _ _ _, _, _, _, hacc => hacc

theorem inlSpine_ph0 {L : Nat} {e : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true) :
    ∀ a ∈ (inlSpine e []).2, NoPh a = true ∧ BvarLt L a = true :=
  inlSpine_ph e [] hn hb (by simp)

theorem machInstCall?_ph {L : Nat} {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : machInstCall? senv e = some (c, kinds, res, args)) :
    ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true := by
  have hs := inlSpine_ph0 hn hb
  unfold machInstCall? at h
  split at h
  · next c' _ args' hsp =>
    split at h
    · next kinds' res' hi =>
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, _, rfl⟩ := h
        intro a ha
        exact hs a (by rw [hsp]; exact ha)
      · simp at h
    · simp at h
  · simp at h

theorem machInstCallS?_args_ph {L : Nat} {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : machInstCallS? senv e = some (c, kinds, ty, args)) :
    ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true := by
  have hs := inlSpine_ph0 hn hb
  unfold machInstCallS? at h
  split at h
  · next c' _ args' hsp =>
    split at h
    · next kinds' ty' hi =>
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, _, rfl⟩ := h
        intro a ha
        exact hs a (by rw [hsp]; exact ha)
      · simp at h
    · simp at h
  · simp at h

theorem machRunApp?_ph {L : Nat} {e dom αs inits body : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : machRunApp? e = some (dom, αs, inits, body)) :
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh αs = true ∧ BvarLt L αs = true) ∧
    (NoPh inits = true ∧ BvarLt L inits = true) ∧ (NoPh body = true ∧ BvarLt (L + 1) body = true) := by
  have hs := inlSpine_ph0 hn hb
  unfold machRunApp? at h
  split at h
  · next x us dom' αs' h1 h2 h3 h4 inits' bn bt body' bi hsp =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    have hm : ∀ a, a ∈ (inlSpine e []).2 → NoPh a = true ∧ BvarLt L a = true := hs
    rw [hsp] at hm
    refine ⟨hm dom' (by simp), hm αs' (by simp), hm inits' (by simp), ?_⟩
    have hl := hm (.lam bn bt body' bi) (by simp)
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hl
    exact ⟨hl.1.2, hl.2.2⟩
  · simp at h

theorem argsAcc_length_of_arity : ∀ (e : Lean.Expr) (n : Name) (k : Nat) (acc : List Lean.Expr),
    e.isAppOfArity n k = true → (Tools.ShippingReaderMatcherArity.argsAcc e acc).length = k + acc.length
  | .app f a, n, k + 1, acc, h => by
    have := argsAcc_length_of_arity f n k (a :: acc) h
    unfold Tools.ShippingReaderMatcherArity.argsAcc
    rw [this]; simp; omega
  | .const _ _, _, 0, acc, _ => by unfold Tools.ShippingReaderMatcherArity.argsAcc; simp
  | .bvar _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .fvar _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .mvar _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .sort _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .lit _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .lam _ _ _ _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .forallE _ _ _ _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .letE _ _ _ _ _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .mdata _ _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .proj _ _ _, _, _, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .const _ _, _, k + 1, _, h => by simp [Lean.Expr.isAppOfArity] at h
  | .app _ _, _, 0, _, h => by simp [Lean.Expr.isAppOfArity] at h

theorem getAppArgs_size_of_arity {e : Lean.Expr} {n : Name} {k : Nat} (h : e.isAppOfArity n k = true) :
    e.getAppArgs.size = k := by
  rw [Tools.ShippingReaderMatcherArityArray.getAppArgs_eq]
  have := argsAcc_length_of_arity e n k [] h
  simpa [Tools.ShippingReaderMatcherArity.argsT] using this

theorem memCall?_ph {L : Nat} {natOf : Lean.Expr → Option Nat} {e : Lean.Expr} {combo : Bool} {aw dw : Nat}
    {dom : Lean.Expr} {ops : List Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops)) :
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ ∀ a ∈ ops, NoPh a = true ∧ BvarLt L a = true := by
  have hall := phArgs_getAppArgs hn hb
  have hget : ∀ i, i < e.getAppArgs.size → NoPh e.getAppArgs[i]! = true ∧ BvarLt L e.getAppArgs[i]! = true := by
    intro i hi
    rw [getElem!_pos e.getAppArgs i hi]
    exact hall _ (Array.getElem_mem hi)
  unfold Sparkle.Compiler.MachMemory.memCall? at h
  have hsz : e.getAppArgs.size = 7 := by
    by_cases h1 : e.isAppOfArity ``Sparkle.Core.Signal.Signal.memory 7 = true
    · exact getAppArgs_size_of_arity h1
    · by_cases h2 : e.isAppOfArity ``Sparkle.Core.Signal.Signal.memoryComboRead 7 = true
      · exact getAppArgs_size_of_arity h2
      · simp [h1, h2] at h
  simp only [] at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, _, rfl, rfl⟩ := h
        refine ⟨hget 0 (by omega), ?_⟩
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> exact hget _ (by omega)
    · simp at h

end Tools.ShippingGen5ReaderTrace
