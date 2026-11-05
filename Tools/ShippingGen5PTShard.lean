import Lean
import Tools.ShippingGen5PTCorpus
import Tools.ShippingGen5CVFinal
import Tools.ShippingGen5FG
set_option autoImplicit false
-- D.D-4 final, Q-B: extension shards of the primitive table (Issue sparkle-ledger-dd4-shard). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Ordinary definitions and theorems checked by the kernel.

/-! # `PTcore ⊕ shard`: extension shards of `PTcorpus`

`PTcorpus` (`Tools/ShippingGen5PTCorpus.lean`) is the shared core `PTcore`: it holds only the rows that `Tools` can state (the declarations of `Init` / `Sparkle.Core`).
The declarations of the corpus modules (output structures, test types) cannot be imported into `Tools`, and four of those modules cannot be imported together.
A `PTShard` is a small table of the same shape as the core tables (`TyTele` / `TmTele` rows keyed by `(Name, numeral levels)`), generated for ONE declaration or module
by `#pt_shard` and living in a file that imports only its owner module. A root composes the core with exactly the shards it needs: `PTcore ⊕ S₁ ⊕ … ⊕ Sₙ`.

* `PTShard.toPT` reads a shard as a `PrimTableK` (the same lookup as `PTcorpus`).
* `comp A B` (`A ⊕ B`) is the left-biased union of two tables. `Excl A B` says the key sets are disjoint (at every key one side has no row); `comp_*` show that under `Excl` no row of either side is lost or changed.
* `FreshAgainst PT S` is the decidable check of `Excl PT S.toPT` on the finitely many keys of `S` (a `rfl`/`decide` proof for each generated shard).
* `cvFinal_comp_functional`: `ConstValueFunctional (CVFinal (A ⊕ B))`. It holds for EVERY `PrimTableK` (`cvFinal_functional`), so composition keeps the functionality; the theorem does not use `Excl`.
  `Excl` is what makes the composition faithful (rows of both sides stay), not what makes it functional.
* Nothing here adopts `PTcorpus`, G-PRIM or TRUSTED, and nothing here proves a row sound. -/

namespace Tools.ShippingGen5PTShard
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5PTCorpus

/-- A shard: finite tables of rows, keyed like `tysTable` / `tmsTable`. -/
structure PTShard where
  tys : List (Name × List Nat × (ks : List Bool) × TyTele ks)
  tms : List (Name × List Nat × (ks : List Bool) × TmTele ks)

namespace PTShard

def empty : PTShard := ⟨[], []⟩

def tyKeys (S : PTShard) : List (Name × List Nat) := S.tys.map fun e => (e.1, e.2.1)
def tmKeys (S : PTShard) : List (Name × List Nat) := S.tms.map fun e => (e.1, e.2.1)

/-- The shard as a primitive table (the lookup of `PTcorpus`). -/
noncomputable def toPT (S : PTShard) : PrimTableK where
  tys c ls :=
    match lvNats ls with
    | none => none
    | some ns => (S.tys.find? fun e => e.1 == c && e.2.1 == ns).map fun e => e.2.2.2.row
  tms c ls :=
    match lvNats ls with
    | none => none
    | some ns => (S.tms.find? fun e => e.1 == c && e.2.1 == ns).map fun e => e.2.2.2.row

end PTShard

/-- The core is the shard made of its two tables (`rfl`). -/
def PTcoreShard : PTShard := ⟨tysTable, tmsTable⟩
noncomputable abbrev PTcore : PrimTableK := PTcorpus
theorem ptcore_eq : PTcore = PTcoreShard.toPT := rfl

/-! ## Numeral levels -/

def natLv (n : Nat) : Level := Nat.repeat Level.succ n Level.zero

theorem lvNat_eq : ∀ {l : Level} {n : Nat}, lvNat l = some n → l = natLv n
  | .zero, n, h => by
      simp only [lvNat, Option.some.injEq] at h; subst h; rfl
  | .succ l, n, h => by
      simp only [lvNat, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      have := lvNat_eq hm
      subst this; rfl
  | .param _, _, h => by simp [lvNat] at h
  | .mvar _, _, h => by simp [lvNat] at h
  | .max _ _, _, h => by simp [lvNat] at h
  | .imax _ _, _, h => by simp [lvNat] at h

theorem lvNats_eq : ∀ {ls : List Level} {ns : List Nat}, lvNats ls = some ns → ls = ns.map natLv
  | [], ns, h => by simp only [lvNats, Option.some.injEq] at h; subst h; rfl
  | l :: ls, ns, h => by
      simp only [lvNats] at h
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨lvNat_eq ha, lvNats_eq hb⟩
      · cases h

/-! ## Composition and exclusivity -/

/-- `A ⊕ B`: the left-biased union of two tables. -/
def comp (A B : PrimTableK) : PrimTableK where
  tys c ls := (A.tys c ls).or (B.tys c ls)
  tms c ls := (A.tms c ls).or (B.tms c ls)

infixl:65 " ⊕ₚ " => comp

/-- The key sets are disjoint: at every key at least one side has no row (types and terms separately). -/
def Excl (A B : PrimTableK) : Prop :=
  (∀ c ls, A.tys c ls = none ∨ B.tys c ls = none) ∧ (∀ c ls, A.tms c ls = none ∨ B.tms c ls = none)

theorem Excl.symm {A B : PrimTableK} (h : Excl A B) : Excl B A :=
  ⟨fun c ls => (h.1 c ls).symm, fun c ls => (h.2 c ls).symm⟩

theorem Excl.comp_left {A B C : PrimTableK} (hA : Excl A C) (hB : Excl B C) : Excl (A ⊕ₚ B) C := by
  refine ⟨fun c ls => ?_, fun c ls => ?_⟩
  · rcases hA.1 c ls with h | h
    · rcases hB.1 c ls with h' | h'
      · exact Or.inl (by simp [comp, h, h'])
      · exact Or.inr h'
    · exact Or.inr h
  · rcases hA.2 c ls with h | h
    · rcases hB.2 c ls with h' | h'
      · exact Or.inl (by simp [comp, h, h'])
      · exact Or.inr h'
    · exact Or.inr h

/-- A row of the left table stays in the composition (no hypothesis). -/
theorem comp_tys_left {A B : PrimTableK} {c : Name} {ls : List Level} {r : TyRow} (h : A.tys c ls = some r) : (A ⊕ₚ B).tys c ls = some r := by
  simp [comp, h]
theorem comp_tms_left {A B : PrimTableK} {c : Name} {ls : List Level} {r : TmRow} (h : A.tms c ls = some r) : (A ⊕ₚ B).tms c ls = some r := by
  simp [comp, h]

/-- A row of the right table stays in the composition when the left table has no row at that key. -/
theorem comp_tys_right {A B : PrimTableK} {c : Name} {ls : List Level} {r : TyRow} (hA : A.tys c ls = none) (h : B.tys c ls = some r) :
    (A ⊕ₚ B).tys c ls = some r := by simp [comp, hA, h]
theorem comp_tms_right {A B : PrimTableK} {c : Name} {ls : List Level} {r : TmRow} (hA : A.tms c ls = none) (h : B.tms c ls = some r) :
    (A ⊕ₚ B).tms c ls = some r := by simp [comp, hA, h]

/-- Under `Excl` the right row is kept whatever the left side is. -/
theorem comp_tys_right_excl {A B : PrimTableK} (hx : Excl A B) {c : Name} {ls : List Level} {r : TyRow} (h : B.tys c ls = some r) :
    (A ⊕ₚ B).tys c ls = some r := comp_tys_right ((hx.1 c ls).resolve_right (by simp [h])) h
theorem comp_tms_right_excl {A B : PrimTableK} (hx : Excl A B) {c : Name} {ls : List Level} {r : TmRow} (h : B.tms c ls = some r) :
    (A ⊕ₚ B).tms c ls = some r := comp_tms_right ((hx.2 c ls).resolve_right (by simp [h])) h

/-- Under `Excl` the composition is commutative (the order of the shards of a root does not matter). -/
theorem comp_comm {A B : PrimTableK} (hx : Excl A B) : (A ⊕ₚ B) = (B ⊕ₚ A) := by
  obtain ⟨h1, h2⟩ := hx
  cases A; cases B
  simp only [comp, PrimTableK.mk.injEq]
  constructor
  · funext c ls
    rcases h1 c ls with h | h <;> simp_all
  · funext c ls
    rcases h2 c ls with h | h <;> simp_all

theorem comp_assoc (A B C : PrimTableK) : ((A ⊕ₚ B) ⊕ₚ C) = (A ⊕ₚ (B ⊕ₚ C)) := by
  simp only [comp, Option.or_assoc]

/-- Composition keeps the functionality of the final carrier. It holds for every table (`cvFinal_functional`), so it does not need `Excl`. -/
theorem cvFinal_comp_functional (A B : PrimTableK) : Tools.ShippingGen5FG.ConstValueFunctional (Tools.ShippingGen5CVFinal.CVFinal (A ⊕ₚ B)) :=
  Tools.ShippingGen5CVFinal.cvFinal_functional (A ⊕ₚ B)

theorem cvFinal_core_shard_functional (S : PTShard) : Tools.ShippingGen5FG.ConstValueFunctional (Tools.ShippingGen5CVFinal.CVFinal (PTcore ⊕ₚ S.toPT)) :=
  cvFinal_comp_functional _ _

/-! ## The decidable freshness check of a shard -/

/-- A shard row is found only at one of the shard's own keys, with numeral levels. -/
theorem PTShard.toPT_tys_some {S : PTShard} {c : Name} {ls : List Level} {r : TyRow} (h : S.toPT.tys c ls = some r) :
    ∃ ns, ls = ns.map natLv ∧ (c, ns) ∈ S.tyKeys := by
  simp only [PTShard.toPT] at h
  cases hl : lvNats ls with
  | none => rw [hl] at h; cases h
  | some ns =>
    rw [hl] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨e, he, _⟩ := h
    have h1 := List.find?_some he
    have hm := List.mem_of_find?_eq_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    refine ⟨ns, lvNats_eq hl, List.mem_map.2 ⟨e, hm, ?_⟩⟩
    rw [h1.1, h1.2]

theorem PTShard.toPT_tms_some {S : PTShard} {c : Name} {ls : List Level} {r : TmRow} (h : S.toPT.tms c ls = some r) :
    ∃ ns, ls = ns.map natLv ∧ (c, ns) ∈ S.tmKeys := by
  simp only [PTShard.toPT] at h
  cases hl : lvNats ls with
  | none => rw [hl] at h; cases h
  | some ns =>
    rw [hl] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨e, he, _⟩ := h
    have h1 := List.find?_some he
    have hm := List.mem_of_find?_eq_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    refine ⟨ns, lvNats_eq hl, List.mem_map.2 ⟨e, hm, ?_⟩⟩
    rw [h1.1, h1.2]

/-- Every key of the shard (at its numeral levels) has no row in `PT`. A `Bool` statement, proved by `rfl`. -/
def FreshAgainst (PT : PrimTableK) (S : PTShard) : Prop :=
  S.tyKeys.all (fun k => (PT.tys k.1 (k.2.map natLv)).isNone) = true ∧
  S.tmKeys.all (fun k => (PT.tms k.1 (k.2.map natLv)).isNone) = true

theorem FreshAgainst.excl {PT : PrimTableK} {S : PTShard} (h : FreshAgainst PT S) : Excl PT S.toPT := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun c ls => ?_, fun c ls => ?_⟩
  · cases hS : S.toPT.tys c ls with
    | none => exact Or.inr rfl
    | some r =>
      obtain ⟨ns, rfl, hk⟩ := PTShard.toPT_tys_some hS
      have := List.all_eq_true.1 h1 _ hk
      exact Or.inl (Option.isNone_iff_eq_none.1 this)
  · cases hS : S.toPT.tms c ls with
    | none => exact Or.inr rfl
    | some r =>
      obtain ⟨ns, rfl, hk⟩ := PTShard.toPT_tms_some hS
      have := List.all_eq_true.1 h2 _ hk
      exact Or.inl (Option.isNone_iff_eq_none.1 this)

/-- Pairwise freshness of two shards (the same statement, read on the shard table). -/
theorem FreshAgainst.shard_excl {S T : PTShard} (h : FreshAgainst S.toPT T) : Excl S.toPT T.toPT := h.excl

/-- No key occurs twice inside one shard. -/
def Nodup (S : PTShard) : Prop := S.tyKeys.Nodup ∧ S.tmKeys.Nodup

end Tools.ShippingGen5PTShard

#print axioms Tools.ShippingGen5PTShard.cvFinal_comp_functional
#print axioms Tools.ShippingGen5PTShard.FreshAgainst.excl
#print axioms Tools.ShippingGen5PTShard.comp_comm
#print axioms Tools.ShippingGen5PTShard.Excl.comp_left
