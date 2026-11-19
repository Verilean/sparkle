# U1 packed port: `Signal d (A × B)` (design, sparkle-ved-packed)

## 1. The compiler's packing rule (investigated, not assumed)

A `Signal d T` whose `T` is a product is ONE wire, the concatenation of its leaves.

* Type width: `inferHWType` (Sparkle/Compiler/Elab.lean:374-384) gives `Prod t1 t2` the width
  `w1 + w2` (`Bool` is one bit, `BitVec w` is `w`; nested products add up, so the width of a tree is the sum of
  its leaves).
* Construction: `bundle2 a b` is emitted as `assign res = concat [a, b]`
  (Elab.lean:1399-1406 and again 2285-2291).
* Bit order: `concat` is MSB-first, the FIRST element lands in the high bits
  (Sparkle/IR/Semantics.lean:142-156, `evalExpr` / `go`; comment "MSB-first").
  So **field 0 is the high part, field 1 the low part**: `res = a << wB | b`.
* Projection: `Signal.map Prod.fst s` is `slice s (W-1) (W-wA)` and `Prod.snd` is
  `slice s (wB-1) 0` (Elab.lean:2303-2335); the `.proj` path says the same ("field 0 occupies the
  high half, field 1 the low half", Elab.lean:1977).
* Nesting: `(A × B) × C` is `concat [concat [A, B], C]`, `A × (B × C)` is `concat [A, concat [B, C]]`; both
  are the left-first leaf order `A, B, C`, first leaf highest.  The leaf `i` therefore has
  `offset_i = Σ_{j>i} w_j` and `width_i = w_i` (the same for every tree shape).
* The port: the single output port of a `Signal d (A × B)` result is named `out`, of type
  `bitVector (wA + wB)` (never `bit`: a product has at least two leaves).

Lean's own `BitVec.append` (`a ++ b`) has the same order (`a` high), which is what the statement's
reference value uses (`OTy.pack`); the IR side is the generated proof's job, so a wrong order would not
be provable (control: slices swapped).

## 2. Contract

See `Tools/VedU1Packed.lean`.  The existing separate-port `U1Stmt` is NOT changed.  A packed result is
a new statement `PackedStmt` alongside it:

* `PContract`: the table of the original declaration (its type, `Prod` tree kept), the port name and the
  slice map `(offset, width)` per projection (left-first).
* `PackCover`: the slice map covers the port exactly: widths are the leaves' widths, offsets descend
  (field 0 high), every slice lies in the port, slices are pairwise disjoint, and the widths add up to the port
  width (so every bit is in a slice); and it is the packing rule's map.
* `PackedStmt pc m f := PackCover pc ∧ U1Stmt pc.core m (packedF pc.tbl f) ∧ SlicesStmt pc m f`.
  `pc.core` is an ordinary `Contract` whose table has ONE `bv W` output (so the old statement is reused,
  not weakened), `packedF` is the declaration with its result packed by `BitVec.append`;
  `SlicesStmt` says that on every run every slice of the port equals the declaration's own projection.

## 3. Entry, tests, results

* `Tools/VedU1PackedEntry.lean`: `#ved_u1_packed decl` (`vedU1PackedS`, checker `checkPackedE`).  The slice map is
  derived from the declaration's type (`OTy.slices`); the checker takes it as a parameter only for the controls.
  Order of checks: `PackCover` (decidable; refuses at `[packed]`), then the generated proof (`[proof]`), kernel, audit.
* Proof: the ordinary `U1Stmt` of the packed value (`PContract.core`, `packedF`) by the existing step lemma, then
  `slices_of_outputs` (general, proved once in `Tools/VedU1Packed.lean` from `OTy.slices_obs`) turns it into the slice statement.
* `Tests/Ved/U1PackedCheck.lean`: positives and negatives.
* Scope: `Bool` / `BitVec w` leaves, no params / structure / memory / hierarchy.  Registers: register-free bodies here; bodies with
  registers (`Signal.loop` state) are in docs/VED-U1-MULTISEQ.md (the statement is the same `PackedStmt`).
