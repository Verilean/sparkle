import Tools.ShippingChildInv

/-! # A call entry's child as the general closing takes it (`Kid`), and its bridge to `RealChild` (round par/b-24)

MOVED here, statements and proofs unchanged, names and namespaces unchanged:

* from `Tools/ShippingMemKidCore.lean` (namespace `Tools.ShippingMemKid`):
  `Kid`, `kid_of`, `Kid.real`, `Kid.mem`;
* from `Tools/ShippingCoreFromM.lean` (namespace `Tools.ShippingCoreFromM`):
  `kid_iff_real_of_nomem`, `real_of_kid`, `kid_of_real`.

Why an early file: the `core_*M` theorems of the check-free chain are being
moved next to the old `core_*` theorems they generalise
(`docs/parallel/B-unify-core.md`, 4.3), and the old theorems' proofs become
calls of them through `real_of_kid`. Both need `Kid` below
`Tools/ShippingChecksCore.lean`. This file needs `RealChild`, `Res`
(`Tools/ShippingChildInv.lean`) and `MemChildren`
(`Tools/ShippingMachineEntry.lean`) only.

The `open` lines are the subset of the two source files' `open` lines whose
namespaces these declarations read.

UNVERIFIED at the time of writing: this file was not built.

ORIGIN DISPATCH (par/o-close): `MemChildren` and `ChildrenReal` are stated on
the entry's origin; `kid_of` asks the per-entry agreement `hag` (name decodes
to what the origin builds) and `kidT_of` gives the tag-based kid without it.
`real_of_kid` / `kid_of_real` (name-based `hnomem`) are unchanged. BUILT
(integration run ig4, exit 0) against the origin-tag compiler. -/
/-! ## Names that say what the origin builds (`TagsAgree`; namespace `Tools.ShippingInstTagged`)

Placed here (below `Tools/ShippingChecksCore.lean`) so the `core_*M` chain can
ask it. The name-based statements of the memory chain (`Kid`, `memNameAt`,
`hsep` over declaration names) stay sound under the origin dispatch for a
shape whose every entry's NAME decodes (`memChild?`) to what its ORIGIN builds.
`tagAgrees` is that test per entry, decidable; it is false exactly for a
collision entry, so for a collision shape the endpoints that ask `TagsAgree`
are simply not generated (`decide` fails). That narrows PROOF coverage only,
not what the compiler accepts. Migrating the `M` chain to the tag-based kid
(`KidT`) is a later unit. -/
namespace Tools.ShippingInstTagged
open Lean Sparkle.Compiler.Elab
open Sparkle.Compiler.MachInstOrigin (InstOrigin)

/-- A memory placeholder decodes to its own memory module (the proof of
`Tools.ShippingMemDispatch.memChild_memChildName`, BUILT there). -/
theorem memChild_ofName (combo : Bool) (aw dw : Nat) :
    Sparkle.Compiler.MachMemory.memChild? (Sparkle.Compiler.MachMemory.memChildName combo aw dw) =
      some (Sparkle.Compiler.MachMemory.memModule combo aw dw) := by
  cases combo
  · first
      | rfl
      | simp [Sparkle.Compiler.MachMemory.memChild?, Sparkle.Compiler.MachMemory.memChildName]
      | decide
  · first
      | rfl
      | simp [Sparkle.Compiler.MachMemory.memChild?, Sparkle.Compiler.MachMemory.memChildName]
      | decide

/-- The entry's name says what its origin builds. -/
def tagAgrees (c : Name) : InstOrigin → Bool
  | .mem cb aw dw => decide (c = Sparkle.Compiler.MachMemory.memChildName cb aw dw)
  | .ord => (Sparkle.Compiler.MachMemory.memChild? c).isNone
  | .field _ => (Sparkle.Compiler.MachMemory.memChild? c).isNone

theorem memChild_of_tagAgrees {c : Name} {o : InstOrigin} (h : tagAgrees c o = true) :
    Sparkle.Compiler.MachMemory.memChild? c = o.child? := by
  cases o with
  | ord =>
    exact Option.isNone_iff_eq_none.mp
      (show (Sparkle.Compiler.MachMemory.memChild? c).isNone = true from h)
  | field i =>
    exact Option.isNone_iff_eq_none.mp
      (show (Sparkle.Compiler.MachMemory.memChild? c).isNone = true from h)
  | mem cb aw dw =>
    have e : c = Sparkle.Compiler.MachMemory.memChildName cb aw dw :=
      of_decide_eq_true
        (show decide (c = Sparkle.Compiler.MachMemory.memChildName cb aw dw) = true from h)
    rw [e]
    exact memChild_ofName cb aw dw

/-- Every entry's name says what its origin builds (decidable: `decide`). -/
abbrev TagsAgree (shape : MachineShape) : Prop :=
  ∀ x ∈ shape.instTagged, tagAgrees x.1 x.2 = true

theorem agree_at {shape : MachineShape} (h : TagsAgree shape) {k : Nat}
    (hk : k < shape.insts.length) :
    Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 =
      (shape.instOrigins.getD k .ord).child? := by
  obtain ⟨hkT, he⟩ := Tools.ShippingChildInv.instTagged_getAt shape hk
  have := h _ (List.getElem_mem hkT)
  rw [he] at this
  exact memChild_of_tagAgrees this

/-- **The `hnomem` premise (no memory origin, no memory name) gives
`TagsAgree`.** -/
theorem tagsAgree_of_nomem {shape : MachineShape}
    (h : ∀ x ∈ shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true) :
    TagsAgree shape := by
  intro x hx
  obtain ⟨h1, h2⟩ := h x hx
  obtain ⟨c, o⟩ := x
  cases o with
  | ord => exact h2
  | field i => exact h2
  | mem cb aw dw => simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h1

/-! ## The origin-based kid (`originAt`, `KidT`; MOVED here from `Tools/ShippingInstTagged.lean`,
definitions and proofs unchanged, so the `core_*M` chain can state its kids by ORIGIN) -/

open Tools.ShippingChildInv in
/-- The origin of entry `k` as the closing reads it (`.ord` when unrecorded). -/
abbrev originAt (shape : MachineShape) (k : Nat) : InstOrigin :=
  shape.instOrigins.getD k .ord

open Tools.ShippingChildInv

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

end Tools.ShippingInstTagged

namespace Tools.ShippingMemKid
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv

/-- **A call entry's child as the general closing takes it**: the built
memory module for a memory placeholder name, a real child of the declaration
otherwise. -/
def Kid (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (c : Name) (y : Res) : Prop :=
  Sparkle.Compiler.MachMemory.memChild? c = some y ∨
    (Sparkle.Compiler.MachMemory.memChild? c = none ∧ RealChild mref cref c y)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A child of the general closing's run is a kid** — origin dispatch
(patched compiler): the closing's `MemChildren` and the witness `hor` are
stated on the entry's ORIGIN; the name-based `Kid` follows for an entry whose
name decodes to what its origin builds (`hag`, decided per declaration:
`Tools.ShippingInstTagged.agree_at`; false for a collision entry). -/
theorem kid_of {shape : MachineShape} {children : List Res} {k : Nat}
    (hk : k < shape.insts.length) (hMC : MemChildren shape children) {y : Res}
    (hy : children[k]? = some y)
    (hor : (shape.instOrigins.getD k .ord).child? = some y ∨
      RealChild mref cref (shape.insts[k]).1 y)
    (hag : Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 =
      (shape.instOrigins.getD k .ord).child?) :
    Kid mref cref (shape.insts[k]).1 y := by
  unfold Kid
  rw [hag]
  rcases hor with h | h
  · exact Or.inl h
  · cases hm : (shape.instOrigins.getD k .ord).child? with
    | none => exact Or.inr ⟨rfl, h⟩
    | some md =>
      have h1 : children[k]? = some md := hMC k hk md hm
      rw [hy] at h1
      have e : y = md := Option.some.inj h1
      rw [e]
      exact Or.inl rfl

/-- **The tag-based kid of a child of the general closing's run** (no
premise): `(origin).child? = some y`, or no built child and a real child of
the entry's declaration. -/
theorem kidT_of {shape : MachineShape} {children : List Res} {k : Nat}
    (hk : k < shape.insts.length) (hMC : MemChildren shape children) {y : Res}
    (hy : children[k]? = some y)
    (hor : (shape.instOrigins.getD k .ord).child? = some y ∨
      RealChild mref cref (shape.insts[k]).1 y) :
    (shape.instOrigins.getD k .ord).child? = some y ∨
      ((shape.instOrigins.getD k .ord).child? = none ∧ RealChild mref cref (shape.insts[k]).1 y) := by
  rcases hor with h | h
  · exact Or.inl h
  · cases hm : (shape.instOrigins.getD k .ord).child? with
    | none => exact Or.inr ⟨rfl, h⟩
    | some md =>
      have h1 : children[k]? = some md := hMC k hk md hm
      rw [hy] at h1
      rw [Option.some.inj h1]
      exact Or.inl rfl

/-- **`kidT_of` in `KidT` form**: a child of the general closing's run is the
tag-based kid of its entry (no name condition). -/
theorem kidT_ofO {shape : MachineShape} {children : List Res} {k : Nat}
    (hk : k < shape.insts.length) (hMC : MemChildren shape children) {y : Res}
    (hy : children[k]? = some y)
    (hor : (shape.instOrigins.getD k .ord).child? = some y ∨
      RealChild mref cref (shape.insts[k]).1 y) :
    Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt shape k)
      (shape.insts[k]).1 y :=
  kidT_of hk hMC hy hor

/-- A kid of a declaration that is not a memory placeholder is a real child. -/
theorem Kid.real {c : Name} {y : Res} (h : Kid mref cref c y)
    (hc : Sparkle.Compiler.MachMemory.memChild? c = none) : RealChild mref cref c y := by
  rcases h with h | ⟨-, h⟩
  · rw [hc] at h
    cases h
  · exact h

/-- A kid of a memory placeholder is the built module. -/
theorem Kid.mem {c : Name} {y md : Res} (h : Kid mref cref c y)
    (hc : Sparkle.Compiler.MachMemory.memChild? c = some md) : y = md := by
  rcases h with h | ⟨hn, -⟩
  · rw [hc] at h
    exact (Option.some.inj h).symm
  · rw [hc] at hn
    cases hn

end Tools.ShippingMemKid

namespace Tools.ShippingCoreFromM
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv
open Tools.ShippingMemKid

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The bridge -/

/-- **At a name that is not a memory placeholder, a kid is a real child and
conversely.** -/
theorem kid_iff_real_of_nomem {c : Name} {y : Res}
    (hc : Sparkle.Compiler.MachMemory.memChild? c = none) :
    Kid mref cref c y ↔ RealChild mref cref c y :=
  ⟨(fun h => Kid.real h hc), (fun h => Or.inr (And.intro hc h))⟩

/-- **Under `hnomem`, the kid of a call entry is a real child** — the form
every re-derivation below uses (hypotheses asked of kids are given by the
old hypotheses asked of real children; kids in a conclusion are real). -/
theorem real_of_kid {shape : MachineShape}
    (hnomem : ∀ x ∈ shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {k : Nat} (hk : k < shape.insts.length) {y : Res}
    (h : Kid mref cref (shape.insts[k]).1 y) :
    RealChild mref cref (shape.insts[k]).1 y :=
  Kid.real h (nomem_name hnomem hk)

/-- The converse: under `hnomem`, a real child of a call entry is a kid. -/
theorem kid_of_real {shape : MachineShape}
    (hnomem : ∀ x ∈ shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {k : Nat} (hk : k < shape.insts.length) {y : Res}
    (h : RealChild mref cref (shape.insts[k]).1 y) :
    Kid mref cref (shape.insts[k]).1 y :=
  Or.inr (And.intro (nomem_name hnomem hk) h)

end Tools.ShippingCoreFromM

namespace Tools.ShippingInstTagged
open Lean
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingChildInv

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

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

/-- The converse: a name-based `Kid` is the tag-based kid when the name decodes
to what the origin builds. -/
theorem kidT_of_kid {o : InstOrigin} {c : Name} {y : Res} (h : Tools.ShippingMemKid.Kid mref cref c y)
    (hagree : Sparkle.Compiler.MachMemory.memChild? c = o.child?) : KidT mref cref o c y := by
  unfold Tools.ShippingMemKid.Kid at h
  rw [hagree] at h
  exact h

end Tools.ShippingInstTagged
