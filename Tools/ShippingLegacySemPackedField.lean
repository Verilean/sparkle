import Tools.ShippingLegacySemTupleEntry

/-! # SEM0 for packed products: the chain bridge

`Tools/ShippingLegacySemPacked.lean` defines the packing
`PShape.pack : (s : PShape) → s.Ty → BitVec s.width` (first component of a
product in the high bits) and proves the one-step bridges `pack_fst`,
`pack_snd`. Here: a whole chain of projections.

**Defined here**

* `Field s s' lo` (a `Type`: data, so that the projection can be computed
  from it without casts) — a path of projections from the shape `s` to its
  sub-shape `s'`, the step applied to the value FIRST outermost, with the low
  bit offset `lo` of `s'` in the packed `s`:
  - `here s : Field s s 0`;
  - `fst p : Field (prod a b) s' (b.width + lo)` for `p : Field a s' lo`;
  - `snd p : Field (prod a b) s' lo` for `p : Field b s' lo`.
* `Field.get : Field s s' lo → s.Ty → s'.Ty` — the projection of a source
  value along the path.

**Proved here**

* `Field.bound` — `lo + s'.width ≤ s.width`.
* `Field.pack_get` — THE CHAIN BRIDGE:
  `(s.pack x).extractLsb' lo s'.width = s'.pack (p.get x)`, by induction
  from `pack_fst` / `pack_snd` and `extract_extract`.
* `slice_is_field` — the link to the entry theorem's value: if a function
  `g` of the packed input is the slice at `(lo, s'.width)` (what
  `topNode_slice` / `subChain_slice` give for the chain's `g`) and the packed
  input is `s.pack val`, then `g (s.pack val) = s'.pack (p.get val)`: `out`
  carries the PACKED FIELD of the source value.

**Stated, not proved** (`OutIsField`, a definition): the conclusion of
`tuple_entry_output` read through the packing. What it still takes to apply
`slice_is_field` to a declaration, none of it in the development:

1. the path: `topNode_slice` gives SOME `lo` with `g v = v.extractLsb' lo w`;
   that this `lo` is the offset of the `Field` the SOURCE chain denotes
   needs the chain's shape facts — per node, that the argument's packed
   width `M` and the result's `w` are `(prod a b).width` and `a.width`
   (fst) / `b.width` (snd) for the shapes of the payload type. The census
   compares exactly these numbers (pass 4: composed range = type-derived
   range, 39 of 39; pass 5: node by node);
2. the shape: that the payload type of the Signal binder IS `s.Ty` for a
   `PShape` `s` (the oracle looks at the type's `whnf` at transparency
   `all`), and the result's is `s'.Ty`;
3. the source value: that the declaration's Signal, at a time `t`, is
   `p.get` of the input Signal at `t` — the denotation of `Signal.fst` /
   `Signal.snd` (`s.map Prod.fst`), a statement about `Signal.val`; and the
   admissible valuation's `bits x N` as `s.pack` of that input. `RawValueAt`
   is combinational: one environment, no time. -/
namespace Tools.ShippingLegacySem

/-- A path of projections from the shape `s` to its sub-shape `s'`, with the
low bit offset of `s'` in the packed `s`. -/
inductive Field : PShape → PShape → Nat → Type where
  | here (s : PShape) : Field s s 0
  | fst {a b s' : PShape} {lo : Nat} : Field a s' lo → Field (PShape.prod a b) s' (b.width + lo)
  | snd {a b s' : PShape} {lo : Nat} : Field b s' lo → Field (PShape.prod a b) s' lo

/-- The projection of a value along a path. -/
def Field.get : {s s' : PShape} → {lo : Nat} → Field s s' lo → s.Ty → s'.Ty
  | _, _, _, .here _, x => x
  | _, _, _, .fst p, x => p.get (Prod.fst x)
  | _, _, _, .snd p, x => p.get (Prod.snd x)

/-- The field lies inside the packed vector. -/
theorem Field.bound {s s' : PShape} {lo : Nat} (p : Field s s' lo) :
    lo + s'.width ≤ s.width := by
  induction p with
  | here s => exact Nat.le_of_eq (Nat.zero_add _)
  | @fst a b s' lo p ih =>
    show b.width + lo + s'.width ≤ a.width + b.width
    omega
  | @snd a b s' lo p ih =>
    show lo + s'.width ≤ a.width + b.width
    omega

/-- **The chain bridge**: the slice of the packed value at the field's
offset is the packed field. -/
theorem Field.pack_get {s s' : PShape} {lo : Nat} (p : Field s s' lo) :
    ∀ x : s.Ty, BitVec.extractLsb' lo s'.width (s.pack x) = s'.pack (p.get x) := by
  induction p with
  | here s =>
    intro x
    show BitVec.extractLsb' 0 s.width (s.pack x) = s.pack x
    first
      | exact BitVec.extractLsb'_eq_self
      | simp
  | @fst a b s' lo p ih =>
    intro x
    show BitVec.extractLsb' (b.width + lo) s'.width ((PShape.prod a b).pack x) =
      s'.pack (p.get (Prod.fst x))
    have e := extract_extract ((PShape.prod a b).pack x) b.width a.width lo s'.width p.bound
    have h2 : BitVec.extractLsb' lo s'.width
        (BitVec.extractLsb' b.width a.width ((PShape.prod a b).pack x)) =
        s'.pack (p.get (Prod.fst x)) := by
      rw [PShape.pack_fst a b x]
      exact ih (Prod.fst x)
    exact e.symm.trans h2
  | @snd a b s' lo p ih =>
    intro x
    show BitVec.extractLsb' lo s'.width ((PShape.prod a b).pack x) =
      s'.pack (p.get (Prod.snd x))
    have e := extract_extract ((PShape.prod a b).pack x) 0 b.width lo s'.width p.bound
    rw [Nat.zero_add] at e
    have h2 : BitVec.extractLsb' lo s'.width
        (BitVec.extractLsb' 0 b.width ((PShape.prod a b).pack x)) =
        s'.pack (p.get (Prod.snd x)) := by
      rw [PShape.pack_snd a b x]
      exact ih (Prod.snd x)
    exact e.symm.trans h2

/-- **The slice the entry theorem speaks of is the packed field**, when the
packed input is the packing of a source value. -/
theorem slice_is_field {s s' : PShape} {lo : Nat} (p : Field s s' lo)
    {g : BitVec s.width → BitVec s'.width}
    (hg : ∀ v : BitVec s.width, g v = BitVec.extractLsb' lo s'.width v) (val : s.Ty) :
    g (s.pack val) = s'.pack (p.get val) := by
  rw [hg (s.pack val)]
  exact p.pack_get val

/-- STATEMENT (a definition; not proved for any declaration): the output of
a tuple-projection declaration is the packed FIELD of the source value —
the conclusion of `tuple_entry_output` with `g (bits x N)` read through the
packing (`slice_is_field`), for every admissible valuation whose packed
input is the packing of `val`. -/
def OutIsField (bs : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (m : Sparkle.IR.AST.Module) {s s' : PShape} {lo : Nat} (p : Field s s' lo)
    (x : Lean.FVarId) : Prop :=
  ∀ (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n)
    (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv) (val : s.Ty),
    bits x s.width = s.pack val →
    Tools.ShippingMixedEntrySoundness.RawValueAt s'.width bs m initial mems
      (s'.pack (p.get val)).toNat

/-- From the entry theorem's conclusion at one valuation to the packed field
of the source value (the last step of the link; premises `hg` from
`topNode_slice` with the path's offset, `hpack` the valuation's packing). -/
theorem rawValue_is_field {bs : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {m : Sparkle.IR.AST.Module} {s s' : PShape} {lo : Nat} (p : Field s s' lo)
    {g : BitVec s.width → BitVec s'.width}
    (hg : ∀ v : BitVec s.width, g v = BitVec.extractLsb' lo s'.width v)
    {initial : Sparkle.IR.Semantics.Env} {mems : Sparkle.IR.Semantics.MEnv}
    {packed : BitVec s.width} {val : s.Ty} (hpack : packed = s.pack val)
    (h : Tools.ShippingMixedEntrySoundness.RawValueAt s'.width bs m initial mems
      (g packed).toNat) :
    Tools.ShippingMixedEntrySoundness.RawValueAt s'.width bs m initial mems
      (s'.pack (p.get val)).toNat := by
  rw [← slice_is_field p hg val, ← hpack]
  exact h

end Tools.ShippingLegacySem
