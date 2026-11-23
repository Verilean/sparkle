import Tools.VedMemOrder

/-!
# A kernel-cheap leaf order check `OrderOkLeafFast` (`sparkle-ved-multiout`, unit 7)

`Tools.VedU1Contract.OrderOk m b` is a closed `Bool` that the struct script (`Tools/VedU1StructSeq.lean`) proves by
`decide +kernel`.  Its cost is quadratic in the number of statements (`isPermOf` erases, `woCheck` scans the rest for
every read, the read-definedness conjunct scans `m.inputs`, `regsOf b`, `writesOf b` for every read, all with `String`
comparison as the unit step): on the 560 statements of the R184 child `wPointOp` the kernel check is killed at 23 GB.

`OrderOkLeafFast m b` is the leaf-module analogue of `Tools.VedCompose.OrderOkFast`: the same single-pass hashed-tree
check as the memory rows (`Tools.VedMemOrder.OrderOkM'`: names as exact Nat codes, a search tree of the names with their
kind and writing statement, a one-pass permutation search keyed by cheap statement keys), plus the conjunct "no memory
statement" (the leaf scope: `OrderOk` speaks about register outputs, `OrderOkM` about `nextKeys`; they agree exactly when
the body has no memory).

`orderOkLeafFast_sound : OrderOkLeafFast m b = true → OrderOk m b = true`.  Every conjunct of `OrderOk` is covered:
`isPermOf`, `woCheck`, `nextKeys` Nodup, memory names Nodup, no self-read, reads defined, outputs defined, writes /
registers disjoint from the inputs.  The hash is never trusted (soundness goes through the exact name codes): a bad
hash can only cost time or refuse, never accept.  No axiom beyond std3, no `native_decide`.
-/

namespace Tools.VedU1OrderFast

open Sparkle.IR.AST Sparkle.IR.Reorder Tools.VedU1Contract Tools.VedMem Tools.VedMemOrder

/-- No statement is a memory (the leaf scope). -/
def noMem (b : List Stmt) : Bool := b.all (fun s => (stmtMemName s).isNone)

theorem nextKeys_noMem : ∀ b : List Stmt, noMem b = true → nextKeys b = (regsOf b).map (·.1)
  | [], _ => rfl
  | s :: rest, h => by
    simp only [noMem, List.all_cons, Bool.and_eq_true] at h
    have ih := nextKeys_noMem rest (by simpa [noMem] using h.2)
    cases s with
    | register o c r e i => simp [nextKeys, regsOf, List.flatMap_cons] at ih ⊢; exact ih
    | memory => simp [stmtMemName] at h
    | assign l e => simpa [nextKeys, regsOf, List.flatMap_cons] using ih
    | _ => simpa [nextKeys, regsOf, List.flatMap_cons] using ih

theorem allReadsM_noMem (s : Stmt) (h : (stmtMemName s).isNone = true) : allReadsM s = allReads s := by
  cases s <;> simp_all [allReadsM, allReads, stmtMemName]

/-- the leaf fast order check: the memory-row hashed check and "no memory statement" -/
def OrderOkLeafFast (m : Module) (b : List Stmt) : Bool := noMem b && OrderOkM' m b

theorem orderOk_of_orderOkM (m : Module) (b : List Stmt) (hn : noMem b = true) (h : OrderOkM m b = true) :
    OrderOk m b = true := by
  have hk := nextKeys_noMem b hn
  have hr : ∀ s ∈ b, allReadsM s = allReads s := fun s hs =>
    allReadsM_noMem s (List.all_eq_true.mp hn s hs)
  unfold OrderOkM at h
  unfold OrderOk
  rw [hk] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  rw [← hk] at h3
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, ?_⟩, h7⟩, h8⟩, h9⟩
  intro s hs n hn
  rw [← hr s hs] at hn
  exact h6 s hs n hn

theorem orderOkLeafFast_sound {m : Module} {b : List Stmt} (h : OrderOkLeafFast m b = true) :
    OrderOk m b = true := by
  unfold OrderOkLeafFast at h
  rw [Bool.and_eq_true] at h
  exact orderOk_of_orderOkM m b h.1 (OrderOkM'_sound m b h.2)

end Tools.VedU1OrderFast
