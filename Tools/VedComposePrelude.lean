import Lean
import Tools.VedU1Contract

/-!
# VED compose, parent prelude (unit `sparkle-ved-compose-connect`, option `ved.compose.connect`)

The generated parent proof reads the contract's input bounds `hin := hok.1 t : ∀ p ∈ c.dataInputs, ins t p.name < 2 ^ declWidth m p.name`
and turns them, by `simp [contractOf, dataInputs, declWidth, ..]`, into the conjunction of the per-input facts
`ins t "_gen_x" < 2 ^ w` (the rewrite facts of the later `simp` calls).  That `simp` unfolds the contract's table and looks every
input up in the module's wire list: observed cost grows with the number of inputs AND of wires.

Here the step is a once-proved lemma and ONE kernel-evaluated equation: `hin_bnd` takes the equation
`c.dataInputs.map (fun p => (p.name, declWidth m p.name)) = L` (closed, `decide +kernel`; `L` is read off the declaration
table by the generator, and the equation is CHECKED, not assumed) and the bound `hok.1 t`, and returns the conjunction
`bndConj (ins t) L`; `simp only [bndConj, bndConjAux, Nat.reducePow]` unfolds it to the same literal conjunction as before.
Nothing here is a statement; `U2HRStmt` is untouched.
-/

namespace Tools.VedComposePrelude

open Tools.VedU1Contract

/-- `f n₀ < 2 ^ w₀ ∧ f n₁ < 2 ^ w₁ ∧ ..` (right nested, no trailing `True`), the shape `simp` gave. -/
def bndConjAux (f : String → Nat) (n : String) (w : Nat) : List (String × Nat) → Prop
  | [] => f n < 2 ^ w
  | (m, v) :: r => f n < 2 ^ w ∧ bndConjAux f m v r

def bndConj (f : String → Nat) : List (String × Nat) → Prop
  | [] => True
  | (n, w) :: r => bndConjAux f n w r

theorem bndConjAux_of (f : String → Nat) (n : String) (w : Nat) (r : List (String × Nat))
    (h : ∀ pw ∈ (n, w) :: r, f pw.1 < 2 ^ pw.2) : bndConjAux f n w r := by
  induction r generalizing n w with
  | nil => exact h _ (List.mem_singleton_self _)
  | cons x r ih =>
    refine ⟨h _ (List.mem_cons_self ..), ih x.1 x.2 fun pw hpw => h pw ?_⟩
    rcases List.mem_cons.mp hpw with rfl | hr
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)

theorem bndConj_of (f : String → Nat) (L : List (String × Nat)) (h : ∀ pw ∈ L, f pw.1 < 2 ^ pw.2) :
    bndConj f L := by
  cases L with
  | nil => trivial
  | cons x r => exact bndConjAux_of f x.1 x.2 r h

/-- The input bounds of the contract as the conjunction over the literal list `L` (checked equal to the contract's). -/
theorem hin_bnd {c : Contract} {m : Sparkle.IR.AST.Module} (f : String → Nat) {L : List (String × Nat)}
    (hL : c.dataInputs.map (fun p => (p.name, declWidth m p.name)) = L)
    (h : ∀ p ∈ c.dataInputs, f p.name < 2 ^ declWidth m p.name) : bndConj f L := by
  refine bndConj_of f L fun pw hpw => ?_
  rw [← hL] at hpw
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hpw
  exact h p hp

/-- A one-bit output port: the trace theorem reads `(Signal.map (fun b => bif b then 1 else 0) x).val t` as a `BitVec 1`; the
goal after the entry's `simp` reads `Bool.toNat (x.val t)`. -/
theorem bit_obs (b : Bool) : (bif b then (1 : BitVec 1) else 0).toNat = Bool.toNat b := by
  cases b <;> rfl

end Tools.VedComposePrelude
