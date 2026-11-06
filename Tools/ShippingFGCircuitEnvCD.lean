import Tools.ShippingFGCircuitFunc
import Tools.ShippingFGCircuitRootsAt
set_option autoImplicit false
-- FG circuit pilot S1c, unit 4: environment-aware `CD` for the arbiter's auxiliary `abbrev`s (prototype). No `sorry`, no `axiom`, no `native_decide`, no new TRUSTED.

/-! # `bvAbbrev` tied to the environment by unfolding

`CD.bvAbbrev` gives `stIdle/stGrantA/stGrantB` the fixed values of `bvAbbrevRow` without reading the environment. Design chosen (a prototype beside `CD`, `CD` itself is unchanged):

* `AbbrevDenotes env c n v` — the environment's own declaration `c` is a level-monomorphic definition whose VALUE is denoted by `CD` (in the empty valuation) as `v : BitVec n`.
  This is the environment-aware unfold: the meaning of the constant is what the environment's definition denotes, not a table entry.
* `abbrevDenotes_of_boundary`: the explicit condition `BoundaryRowsInEnv env` (the three auxiliary declarations are the literals `bvAbbrevRow` assumes) gives
  `AbbrevDenotes env c n v` for every table row — so under the condition the table row IS the env-unfold denotation.
* `abbrevDenotes_unique`: two env-unfold denotations of the same constant agree (this uses `cd_fun`, functionality of `CD`). With the above, ANY env-unfold denotation
  of a boundary constant equals the table value (`abbrev_unfold_eq_row`), so the `bvAbbrev` rule cannot disagree with the environment once `BoundaryRowsInEnv env` holds.
* `boundaryRows_iff_unfold`: the explicit condition is exactly "the env-unfold denotation exists with the table's value and the literal shape" (it is not weakened).

What this does NOT do: it does not remove the condition (the env's definition could be another expression with another value), it states the condition at the level of the
environment's definition. No `bvAbbrevRow` entry is trusted without `BoundaryRowsInEnv env`. Not a new TRUSTED. -/
namespace Tools.ShippingFGCircuitEnvCD
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots

/-- the environment-aware unfold of a `BitVec n` constant: the env's definition, read by `CD`. -/
def AbbrevDenotes (env : Environment) (c : Name) (n : Nat) (v : BitVec n) : Prop :=
  ∃ d : DefinitionVal, env.find? c = some (.defnInfo d) ∧ d.levelParams = [] ∧ CD [] d.value (BitVec n) v

theorem cd_eBV (w : Nat) : TD [] (eBV w) (BitVec w) :=
  TD.bitvec rfl (CD.natLit rfl)

theorem cd_eBVLit (n k : Nat) : CD [] (eBVLit n k) (BitVec n) (BitVec.ofNat n k) :=
  CD.bvOfNat rfl (CD.natLit rfl) (CD.natLit rfl)

theorem abbrevDenotes_of_boundary {env : Environment} (hB : BoundaryRowsInEnv env) {nm : Name} {k : Nat}
    (hk : (nm, k) ∈ [(`stIdle, 0), (`stGrantA, 1), (`stGrantB, 2)]) :
    AbbrevDenotes env (privAbbrev nm) 2 (BitVec.ofNat 2 k) := by
  obtain ⟨d, hf, hl, -, hv⟩ := hB nm k hk
  exact ⟨d, hf, hl, by rw [hv]; exact cd_eBVLit 2 k⟩

/-- the table rows are the `BitVec.ofNat` of the literal (so the row value is the env-unfold value) -/
theorem row_stIdle : bvAbbrevRow (privAbbrev `stIdle) = some ⟨2, BitVec.ofNat 2 0⟩ := by decide
theorem row_stGrantA : bvAbbrevRow (privAbbrev `stGrantA) = some ⟨2, BitVec.ofNat 2 1⟩ := by decide
theorem row_stGrantB : bvAbbrevRow (privAbbrev `stGrantB) = some ⟨2, BitVec.ofNat 2 2⟩ := by decide

theorem abbrevDenotes_unique {env : Environment} {c : Name} {n : Nat} {v v' : BitVec n}
    (h : AbbrevDenotes env c n v) (h' : AbbrevDenotes env c n v') : v = v' := by
  obtain ⟨d, hf, -, hv⟩ := h
  obtain ⟨d', hf', -, hv'⟩ := h'
  rw [hf] at hf'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hf')
  subst this
  exact cd_eq hv hv'

/-- Under the explicit condition, ANY env-unfold denotation of a boundary constant is the table value: the `bvAbbrev` rule cannot disagree with the environment. -/
theorem abbrev_unfold_eq_row {env : Environment} (hB : BoundaryRowsInEnv env) {nm : Name} {k : Nat}
    (hk : (nm, k) ∈ [(`stIdle, 0), (`stGrantA, 1), (`stGrantB, 2)]) {v : BitVec 2}
    (h : AbbrevDenotes env (privAbbrev nm) 2 v) : v = BitVec.ofNat 2 k :=
  abbrevDenotes_unique h (abbrevDenotes_of_boundary hB hk)

/-- The explicit condition is exactly the env-level statement (type and literal shape of the definition), nothing weaker: the definition read by `CD` gives the row value. -/
theorem boundaryRows_iff_unfold (env : Environment) :
    BoundaryRowsInEnv env ↔ ∀ (nm : Name) (k : Nat), (nm, k) ∈ [(`stIdle, 0), (`stGrantA, 1), (`stGrantB, 2)] →
      ∃ d : DefinitionVal, env.find? (privAbbrev nm) = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = eBV 2 ∧ d.value = eBVLit 2 k ∧
        CD [] d.value (BitVec 2) (BitVec.ofNat 2 k) := by
  constructor
  · intro hB nm k hk
    obtain ⟨d, hf, hl, ht, hv⟩ := hB nm k hk
    exact ⟨d, hf, hl, ht, hv, by rw [hv]; exact cd_eBVLit 2 k⟩
  · intro h nm k hk
    obtain ⟨d, hf, hl, ht, hv, -⟩ := h nm k hk
    exact ⟨d, hf, hl, ht, hv⟩

end Tools.ShippingFGCircuitEnvCD

#print axioms Tools.ShippingFGCircuitEnvCD.abbrevDenotes_of_boundary
#print axioms Tools.ShippingFGCircuitEnvCD.abbrev_unfold_eq_row
#print axioms Tools.ShippingFGCircuitEnvCD.boundaryRows_iff_unfold
