/-! # SEM0 for packed product payloads: the packing function (definitions)

The legacy route binds a Signal whose payload is a nested product
(`Signal dom (A × B × …)`) as ONE input port `bitVector N`, `N` the sum of the
leaf widths (the type oracle's product arm, `Sparkle/Compiler/Elab.lean`
560–570: `bitVector (w1 + w2)`, a `Bool` / `BitVec 1` leaf counting 1, `Unit`
counting 0), and lowers `Signal.fst` / `Signal.snd` to slices of it
(`Rec.handleTupleProjections`, 5662–5700: `fst` takes the HIGH
`width`-many bits `[total-1 : total-width]`, `snd` the LOW ones
`[width-1 : 0]`).

The entry statement of round 23 (`Tools/ShippingLegacySemFst.lean`) is about
the PACKED input: the port's value is a `BitVec N` and the result is a slice
of it. That statement needs no source value for a product. What it does NOT
say is that the slice is the source's FIELD; for that the source value of a
product-valued Signal has to be related to the packed vector. The certified
development has no such function on Lean product VALUES:

* `Tools.ShippingUnifiedMeaning.pack` packs a scalar (`SType.bool` /
  `SType.bits w`) into a `Value` — no product;
* `Tools.ShippingMachineDenote.packList` / `Tools.ShippingMachineEntry.packLets`
  concatenate a list of TERMS (`Term (.bits w)`), the first in the high bits
  — the machine route's packed state, a statement about terms, not about a
  value of type `A × B`;
* `Tools.ShippingMachineDenote.encState` encodes a state tuple slot by slot
  (one number per slot), not as one vector.

**Defined here** (the missing SEM0 piece; nothing in the compiler or in the
other proofs refers to it yet):

* `PShape` — the shape of a packable payload: `bool`, `bits w`, `unit`,
  `prod a b`; `PShape.width`; `PShape.Ty` (the Lean type);
* `PShape.pack : (s : PShape) → s.Ty → BitVec s.width` — the first component
  of a product in the HIGH bits (`pack a ++ pack b`), as the oracle's width
  sum and the two slices above require;
* `PStep`, `PShape.field` — the sub-shape and the low bit offset reached by a
  chain of projections (the step applied to the input FIRST first).

**Proved here** (the one-step bridge lemmas, pure `BitVec` facts):

* `PShape.pack_fst` — the high `a.width` bits of a packed pair are the packed
  first component: the slice the `Signal.fst` arm emits;
* `PShape.pack_snd` — the low `b.width` bits are the packed second component:
  the slice the `Signal.snd` arm emits.

**Not here**: the chain bridge (`field s p = some (s', lo)` implies
`(s.pack x).extractLsb' lo s'.width = s'.pack (the projection of x along p)`
— needs the dependently typed projection along a path), and the link between
`s.Ty` and the payload type the oracle sees (`whnf` at transparency `all`). -/
namespace Tools.ShippingLegacySem

/-- The shape of a packable payload. -/
inductive PShape where
  | bool
  | bits (w : Nat)
  | unit
  | prod (a b : PShape)

/-- The width of the packed vector. -/
def PShape.width : PShape → Nat
  | .bool => 1
  | .bits w => w
  | .unit => 0
  | .prod a b => a.width + b.width

/-- The Lean type of a payload of this shape. -/
def PShape.Ty : PShape → Type
  | .bool => Bool
  | .bits w => BitVec w
  | .unit => Unit
  | .prod a b => a.Ty × b.Ty

/-- **The packing function**: the first component of a product in the high
bits. -/
def PShape.pack : (s : PShape) → s.Ty → BitVec s.width
  | .bool, b => BitVec.ofBool b
  | .bits _, v => v
  | .unit, _ => 0#0
  | .prod a b, x => a.pack (Prod.fst x) ++ b.pack (Prod.snd x)

/-- One projection step. -/
inductive PStep where
  | fst
  | snd

/-- The sub-shape and the low bit offset reached by a chain of projections,
the step applied to the input first. -/
def PShape.field : PShape → List PStep → Option (PShape × Nat)
  | s, [] => some (s, 0)
  | .prod a b, .fst :: rest => (a.field rest).map fun r => (r.1, r.2 + b.width)
  | .prod _ b, .snd :: rest => b.field rest
  | _, _ => none

/-- **The slice of the `Signal.fst` arm is the packed first component.** -/
theorem PShape.pack_fst (a b : PShape) (p : (PShape.prod a b).Ty) :
    ((PShape.prod a b).pack p).extractLsb' b.width a.width = a.pack (Prod.fst p) := by
  first
    | exact BitVec.extractLsb'_append_eq_left
    | (show (a.pack (Prod.fst p) ++ b.pack (Prod.snd p)).extractLsb' b.width a.width =
         a.pack (Prod.fst p)
       exact BitVec.extractLsb'_append_eq_left)
    | (unfold PShape.pack
       exact BitVec.extractLsb'_append_eq_left)

/-- **The slice of the `Signal.snd` arm is the packed second component.** -/
theorem PShape.pack_snd (a b : PShape) (p : (PShape.prod a b).Ty) :
    ((PShape.prod a b).pack p).extractLsb' 0 b.width = b.pack (Prod.snd p) := by
  first
    | exact BitVec.extractLsb'_append_eq_right
    | (show (a.pack (Prod.fst p) ++ b.pack (Prod.snd p)).extractLsb' 0 b.width =
         b.pack (Prod.snd p)
       exact BitVec.extractLsb'_append_eq_right)
    | (unfold PShape.pack
       exact BitVec.extractLsb'_append_eq_right)

end Tools.ShippingLegacySem
