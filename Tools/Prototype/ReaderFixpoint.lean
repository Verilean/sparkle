import Sparkle.Compiler.Elab

/-! # Unit LC8 prototype: `machLoopBody` as a kernel-visible `partial_fixpoint` definition

ISOLATED PROTOTYPE.  Nothing under `Sparkle/Compiler/*` is changed; no production function is switched.
`loopBodyP` is a COPY of `Sparkle.Compiler.Elab.machLoopBody` (Elab 4182-4200).

BUILT: lc8c exit 0, lc8i exit 0 (Tools.Prototype.ReaderFixpoint; axioms propext, Classical.choice, Quot.sound).
No `sorry`, no axiom, no `native_decide`.

PROVED: `loopBodyP_letE` / `loopBodyP_tail` (the unfolding equation, one per arm), `loopBodyP_lets_mono`
(success invariant by `partial_correctness`).  The partner reader is the ARGUMENT `conv` (hypothesis
`hconv`: it never shrinks the table on a success).  Why `machLoopBody`: smallest of the seven (2 arms), has
the self-recursion on the `let` body AND the `foldlM` over a closure that calls the partner reader
(`machConv`), which is the pattern of `machChain` / `machInstance` / `machInstanceS`.  It has no `findSome?`
probe (that pattern, in `machNested` / `machLoopRoot`, is treated in `ReaderFixpointMutual`).
-/
namespace Tools.Prototype.ReaderFixpoint
open Lean Sparkle.Compiler.Elab

/-- The partner reader `machConv` as an ARGUMENT (open recursion across the mutual group). -/
abbrev Conv := List MachVal → Nat → Lean.Expr → MachRead → Option (Lean.Expr × MachRead)

/-- Copy of `machLoopBody`, `partial def` → `partial_fixpoint`. -/
def loopBodyP (conv : Conv) (base : Nat) :
    List MachVal → Lean.Expr → MachRead → Option MachRead
  | env, .letE nm ty v b _, st => do
    let (v', st) ← conv env 0 v st
    let (x, lets) := if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets
    loopBodyP conv base (.val x :: env) b { st with lets := lets }
  | env, tail, st => do
    let regs ← machLoopRegs tail
    let (ws, st) ← regs.foldlM (init := (([] : List (Nat × Lean.Expr)), st))
      fun (ws, st) (_, _, nx) => do
        let (nx', st) ← conv env 0 nx st
        pure (ws ++ [(base + ws.length, nx')], st)
    some { st with ws := st.ws ++ ws.toArray }
partial_fixpoint

/-! ## The unfolding equation (what `partial def` does not give in the kernel) -/

/-- `let` arm. -/
theorem loopBodyP_letE (conv : Conv) (base : Nat) (env : List MachVal) (nm : Name)
    (ty v b : Lean.Expr) (nd : Bool) (st : MachRead) :
    loopBodyP conv base env (.letE nm ty v b nd) st =
      (conv env 0 v st).bind fun (v', st) =>
        let (x, lets) := if machIsSlot v' then machBindLetNamed nm ty v' st.lets
          else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
          else machBindLet nm ty v' st.lets
        loopBodyP conv base (.val x :: env) b { st with lets := lets } := by
  rw [loopBodyP]; rfl

/-- tail arm (every other expression). -/
theorem loopBodyP_tail (conv : Conv) (base : Nat) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) (he : ∀ nm ty v b nd, e ≠ .letE nm ty v b nd) :
    loopBodyP conv base env e st = (do
      let regs ← machLoopRegs e
      let (ws, st) ← regs.foldlM (init := (([] : List (Nat × Lean.Expr)), st))
        fun (ws, st) (_, _, nx) => do
          let (nx', st) ← conv env 0 nx st
          pure (ws ++ [(base + ws.length, nx')], st)
      some { st with ws := st.ws ++ ws.toArray }) := by
  rw [loopBodyP]
  exact fun nm ty v b nd h => he nm ty v b nd h

/-! ## `let`-table growth of the three binders (size only) -/

theorem machBindLetNamed_size {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} :
    lets.size ≤ (machBindLetNamed nm ty v' lets).2.size := by
  unfold machBindLetNamed
  split
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · simp

theorem machBindLet_size {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} :
    lets.size ≤ (machBindLet nm ty v' lets).2.size := by
  unfold machBindLet
  split
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · simp

theorem machBindLetAlias_size {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} :
    lets.size ≤ (machBindLetAlias nm ty v' lets).2.size := by
  unfold machBindLetAlias
  by_cases hc : machIsLetVar (machBindLetAlias.resolve lets lets.size v') = true
  · rw [if_pos hc]; exact machBindLetNamed_size
  · rw [if_neg hc]
    split
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · dsimp only
      split
      · exact Nat.le_refl _
      · simp

theorem foldlM_lets {α : Type} (f : (List (Nat × Lean.Expr)) × MachRead → α →
      Option ((List (Nat × Lean.Expr)) × MachRead))
    (hf : ∀ s a s', f s a = some s' → s.2.lets.size ≤ s'.2.lets.size) :
    ∀ (xs : List α) (s s' : (List (Nat × Lean.Expr)) × MachRead),
      xs.foldlM f s = some s' → s.2.lets.size ≤ s'.2.lets.size
  | [], s, s', h => by simp [List.foldlM] at h; subst h; exact Nat.le_refl _
  | a :: as, s, s', h => by
    simp only [List.foldlM] at h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    exact Nat.le_trans (hf s a s1 h1) (foldlM_lets f hf as s1 s' h2)

/-! ## The invariant on successes, by fixpoint induction (`partial_correctness`) -/

/-- Joint-invariant shape for ONE reader: if the partner reader never shrinks the `let` table on a
success, neither does `loopBodyP`.  (The full invariant `RdOk` of LC3 is the same induction with a
larger motive.) -/
theorem loopBodyP_lets_mono (conv : Conv)
    (hconv : ∀ env d e st v st1, conv env d e st = some (v, st1) → st.lets.size ≤ st1.lets.size)
    (base : Nat) :
    ∀ env e st st', loopBodyP conv base env e st = some st' → st.lets.size ≤ st'.lets.size := by
  intro env e st st' h
  refine loopBodyP.partial_correctness conv base
    (fun _ _ st r => st.lets.size ≤ r.lets.size) ?_ env e st st' h
  intro f ih env e st r h
  split at h
  · rename_i nm ty v b nd
    obtain ⟨⟨v', st1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have hc := hconv _ _ _ _ _ _ h1
    have hb : st1.lets.size ≤ (if machIsSlot v' then machBindLetNamed nm ty v' st1.lets
          else if machIsLetVar v' then machBindLetAlias nm ty v' st1.lets
          else machBindLet nm ty v' st1.lets).2.size := by
      split
      · exact machBindLetNamed_size
      · split
        · exact machBindLetAlias_size
        · exact machBindLet_size
    have := ih _ _ _ _ h2
    exact Nat.le_trans hc (Nat.le_trans hb this)
  · obtain ⟨regs, -, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ws, st1⟩, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
    have hf := foldlM_lets _ (fun s a s' hs => by
      obtain ⟨ws0, st0⟩ := s
      obtain ⟨a1, a2, nx⟩ := a
      obtain ⟨⟨nx', st2⟩, h5, h6⟩ := Option.bind_eq_some_iff.mp hs
      cases h6
      exact hconv _ _ _ _ _ _ h5) regs _ _ h3
    cases h4
    exact hf

#print axioms loopBodyP_letE
#print axioms loopBodyP_tail
#print axioms loopBodyP_lets_mono

end Tools.Prototype.ReaderFixpoint
