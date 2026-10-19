import Tools.ShippingKid

/-! # The call entries with their origins (`MachineShape.instTagged`), for the origin-dispatch closing

The compiler change "explicit call-entry origin" (`Sparkle/Compiler/MachInstOrigin.lean`,
`docs/parallel/S-memname-collision.md` §5) records an origin next to every call
entry (`MachineShape.instOrigins`) and makes the general closing `closeInstsGM`
map

    shape.instTagged = shape.insts.zipIdx.map fun (i, k) => (i.1, shape.instOrigins.getD k .ord)

dispatching on the ORIGIN (`InstOrigin.child?`): a memory-origin entry gets the
built memory module, every other entry the compile of its declaration
(`synthesizeChild c`), whatever its name.

This file: the bookkeeping that relates `instTagged` to `insts`
(`instTagged_length`, `instTagged_getElem`, `instTagged_map_fst`,
`instTagged_getElem?_fst`), the per-entry origin `originAt`, the tag-based
"no memory entry" condition and its one TRUE bridge (`noMemTag_of_origins`:
origins without a memory origin), the tag-based kid `KidT` (the origin decides,
not the name) and the memory fact of a memory origin (`child?_eq_memModule`).

There is deliberately NO bridge from the old name-based
`∀ c ∈ shape.insts, memChild? c.1 = none`: `instOrigins` is an independent field
of `MachineShape`, so the name says nothing about the origin.

BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md). -/
namespace Tools.ShippingInstTagged
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachInstOrigin
open Tools.ShippingChildInv

/-- The origin of entry `k` as the closing reads it (`.ord` when unrecorded). -/
abbrev originAt (shape : MachineShape) (k : Nat) : InstOrigin :=
  shape.instOrigins.getD k .ord

theorem instTagged_length (shape : MachineShape) :
    shape.instTagged.length = shape.insts.length := by
  simp [MachineShape.instTagged]

theorem instTagged_getElem (shape : MachineShape) {k : Nat}
    (h : k < shape.instTagged.length) :
    shape.instTagged[k] =
      ((shape.insts[k]'(by rw [← instTagged_length]; exact h)).1, originAt shape k) := by
  simp [MachineShape.instTagged, originAt]

theorem instTagged_getElem_fst (shape : MachineShape) {k : Nat}
    (h : k < shape.instTagged.length) :
    (shape.instTagged[k]).1 = (shape.insts[k]'(by rw [← instTagged_length]; exact h)).1 := by
  rw [instTagged_getElem]

theorem instTagged_getElem_snd (shape : MachineShape) {k : Nat}
    (h : k < shape.instTagged.length) :
    (shape.instTagged[k]).2 = originAt shape k := by
  rw [instTagged_getElem]

theorem instTagged_map_fst (shape : MachineShape) :
    shape.instTagged.map (·.1) = shape.insts.map (·.1) := by
  apply List.ext_getElem
  · simp [instTagged_length]
  · intro k h1 h2
    simp only [List.getElem_map]
    exact instTagged_getElem_fst shape (by simpa using h1)

theorem instTagged_getElem?_fst (shape : MachineShape) (k : Nat) :
    (shape.instTagged[k]?).map (·.1) = (shape.insts[k]?).map (·.1) := by
  rw [← List.getElem?_map, ← List.getElem?_map, instTagged_map_fst]

/-- A callee of a tagged entry is a callee of a call entry. -/
theorem fst_mem_of_instTagged {shape : MachineShape} {x : Name × InstOrigin}
    (hx : x ∈ shape.instTagged) : ∃ i ∈ shape.insts, i.1 = x.1 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  refine ⟨shape.insts[k]'(by rw [← instTagged_length]; exact hk),
    List.getElem_mem _, ?_⟩
  rw [instTagged_getElem_fst]

/-- A condition on every callee transfers to the callees of the tagged entries. -/
theorem forall_instTagged_of_insts {shape : MachineShape} {K : Name → Prop}
    (h : ∀ x ∈ shape.insts, K x.1) : ∀ x ∈ shape.instTagged, K x.1 := by
  intro x hx
  obtain ⟨i, hi, e⟩ := fst_mem_of_instTagged hx
  rw [← e]
  exact h i hi

/-- **No memory entry, by the tag** (decidable: `decide` on the shape). -/
abbrev NoMemTag (shape : MachineShape) : Prop :=
  ∀ o ∈ shape.instTagged, o.2.child?.isNone = true

theorem child?_none_of_noMemTag {shape : MachineShape} (h : NoMemTag shape)
    {k : Nat} (hk : k < shape.insts.length) : (originAt shape k).child? = none := by
  have hkT : k < shape.instTagged.length := by rw [instTagged_length]; exact hk
  have := h _ (List.getElem_mem hkT)
  rw [instTagged_getElem_snd] at this
  exact Option.isNone_iff_eq_none.mp this

/-- **The TRUE bridge**: origins without a memory origin give `NoMemTag` (an
unrecorded origin is `.ord`, not a memory). -/
theorem noMemTag_of_origins {shape : MachineShape}
    (h : ∀ o ∈ shape.instOrigins, o.child?.isNone = true) : NoMemTag shape := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [instTagged_getElem_snd]
  show (shape.instOrigins.getD k .ord).child?.isNone = true
  rw [List.getD_eq_getElem?_getD]
  cases hg : shape.instOrigins[k]? with
  | none => rfl
  | some o => exact h o (List.mem_of_getElem? hg)

/-- A memory origin's child is a built memory module. -/
theorem child?_eq_memModule {o : InstOrigin} {md : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (h : o.child? = some md) :
    ∃ cb aw dw, md = Sparkle.Compiler.MachMemory.memModule cb aw dw := by
  cases o with
  | ord => cases h
  | field i => cases h
  | mem cb aw dw => exact ⟨cb, aw, dw, (Option.some.inj h).symm⟩

theorem child?_mem (cb : Bool) (aw dw : Nat) :
    (InstOrigin.mem cb aw dw).child? = some (Sparkle.Compiler.MachMemory.memModule cb aw dw) :=
  rfl

theorem child?_of_not_mem {o : InstOrigin} (h : ∀ cb aw dw, o ≠ .mem cb aw dw) :
    o.child? = none := by
  cases o with
  | ord => rfl
  | field i => rfl
  | mem cb aw dw => exact absurd rfl (h cb aw dw)

/-- **A call entry's child as the patched general closing takes it**: the
built memory module when the ORIGIN is a memory, a real child of the entry's
declaration otherwise — whatever the declaration's name. -/
def KidT (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (o : InstOrigin) (c : Name) (y : Res) : Prop :=
  o.child? = some y ∨ (o.child? = none ∧ RealChild mref cref c y)

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem KidT.real {o : InstOrigin} {c : Name} {y : Res} (h : KidT mref cref o c y)
    (ho : o.child? = none) : RealChild mref cref c y := by
  rcases h with h | ⟨-, h⟩
  · rw [ho] at h
    cases h
  · exact h

theorem KidT.mem {o : InstOrigin} {c : Name} {y md : Res} (h : KidT mref cref o c y)
    (ho : o.child? = some md) : y = md := by
  rcases h with h | ⟨hn, -⟩
  · rw [ho] at h
    exact (Option.some.inj h).symm
  · rw [ho] at hn
    cases hn

/-- **The name-based `Kid` from the tag-based one**, for an entry whose name
decodes to what its origin builds (`memChild? c = o.child?`). This is a
per-entry DATA condition, decided on the shape — it fails exactly for a
collision (a declaration carrying a memory placeholder name), which the
patched compiler compiles; theorems that ask it do not cover such shapes. -/
theorem kid_of_kidT {o : InstOrigin} {c : Name} {y : Res} (h : KidT mref cref o c y)
    (hagree : Sparkle.Compiler.MachMemory.memChild? c = o.child?) :
    Tools.ShippingMemKid.Kid mref cref c y := by
  unfold Tools.ShippingMemKid.Kid
  rw [hagree]
  exact h

/-! ## `TagsAgree` (`tagAgrees`, `memChild_ofName`, `memChild_of_tagAgrees`,
`agree_at`, `tagsAgree_of_nomem`) is in `Tools/ShippingKid.lean`, same namespace,
so the `core_*M` chain below `ShippingChecksCore` can ask it. -/

/-- Without a memory name and without a memory origin, names and origins agree. -/
theorem tagsAgree_of_nomem_notag {shape : MachineShape}
    (hnomem : ∀ c ∈ shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hnotag : NoMemTag shape) : TagsAgree shape := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hk' : k < shape.insts.length := by rw [← instTagged_length]; exact hk
  have hn := hnomem _ (List.getElem_mem hk')
  have ho := child?_none_of_noMemTag hnotag hk'
  rw [instTagged_getElem_fst shape hk, instTagged_getElem_snd shape hk]
  revert ho
  cases originAt shape k with
  | ord => intro _; simp [tagAgrees, hn]
  | field i => intro _; simp [tagAgrees, hn]
  | mem cb aw dw => intro ho; cases ho

end Tools.ShippingInstTagged
