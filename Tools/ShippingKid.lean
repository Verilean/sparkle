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
`real_of_kid` / `kid_of_real` (name-based `hnomem`) are unchanged. WRITTEN,
NOT BUILT against patched compiler. -/
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
    (hnomem : ∀ c ∈ shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {k : Nat} (hk : k < shape.insts.length) {y : Res}
    (h : Kid mref cref (shape.insts[k]).1 y) :
    RealChild mref cref (shape.insts[k]).1 y :=
  Kid.real h (hnomem _ (List.getElem_mem hk))

/-- The converse: under `hnomem`, a real child of a call entry is a kid. -/
theorem kid_of_real {shape : MachineShape}
    (hnomem : ∀ c ∈ shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {k : Nat} (hk : k < shape.insts.length) {y : Res}
    (h : RealChild mref cref (shape.insts[k]).1 y) :
    Kid mref cref (shape.insts[k]).1 y :=
  Or.inr (And.intro (hnomem _ (List.getElem_mem hk)) h)

end Tools.ShippingCoreFromM
