# G2 — worker, round 23 (branch `par/g2-legacy-23`, base `fix/cache-rollback` = `429821d9`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §93–§100. (Round 22 has no note of its own;
its result — `proj_entry_output`, `PROJ CLASS: fits 45 of 45` — is in commit
`429821d9` and in the headers of `Tools/ShippingLegacySemProj.lean`,
`…TelescopeLams.lean`, `…InputAt.lean`.)

**Status in one line**: items 1 and 2 are written in full; item 3 (the walk
of the accepting `Signal.fst` / `Signal.snd` arms) STOPS at three points that
need a decision (§97); what is delivered for it is item 4 — the arm's program
text, the decomposed statements as type-checked definitions, and the entry
part proved against the walk's obligation.

## 93. Item 1 — evidence (census pass 4, `Tests/Compiler/LegacyArmCensusTest.lean`)

For each RETURNED declaration whose leaf has the head `Signal.fst` (39 in
round 20):

* source side (`fstObs`): the chain of `Signal.fst` / `Signal.snd`
  applications and what it is applied to (a `Signal.map` anywhere in the
  chain shows as the terminal head); `fallbackKind`; per binder the type
  oracle's outcome, and for a Signal binder the payload after `whnf` as a
  nesting shape, its number of leaves and the sum of the leaf widths; the
  result's payload and the oracle on the result type; the bit range
  `(lo, width)` the chain denotes in the packed payload with the FIRST
  component high (`chainRange`, from the types only);
* emitted side (`runEntryModule`, `sliceObs`): the entry is run again and
  the raw module read: every statement an assignment, and `out`, followed
  through the wire assignments, a slice `[hi:lo]` of ONE input port (slices
  of slices composed: `[hi:lo]` of `[h0:l0]` is `[l0+hi : l0+lo]`).

Log lines requested from the build (all start with `FST CLASS`):

1. `FST CLASS: slice-of-input N of M`
2. `FST CLASS, shapes (slice steps | assigns | input ports | wires): …`
3. `FST CLASS, composed range = type-derived range …: N of M`
4. `FST CLASS, NOT fitting or differing (n): …`
5. `FST CLASS, per declaration, port[hi:lo] of the port's type: …`
6. `FST CLASS, DETAIL (first with a Bool result): …`
7. `FST CLASS, DETAIL (first with a BitVec result): …`
8. `FST CLASS, DETAIL (deepest chain): …`
9. `FST CLASS, SMALLEST emitted module: …` (ports and body)

What the lines decide: (2) whether the result goes through intermediate
wires (expected: one wire and one slice per chain step, then `out`); (3)
whether the emitted slice is the field under "first component in the high
bits" — the packing of §95; the DETAIL lines whether the oracle gives a
single `bitVector N` with `N` = the sum of the leaf widths on the structured
binder.

## 94. Read: what the compiler does on this class

* **The binder** (`bindInputsLegacy`, 2110–2146): the payload is not looked
  at. `inferHWTypeFromSignal` on `Signal dom (A × B × …)` goes through the
  oracle's product arm (`inferHWTypeStep`, 560–570):
  `bitVector (w1 + w2)`, a `bit` component counting 1, `Unit` / `PUnit`
  counting 0 (553–559). So the structured Signal is ONE hardware binder, and
  `bindInputsLegacy_step` binds one port of that type: in the certified
  `prepare` it is a `.bits N` binder as it is — `TypeOk (.bits N) T` is
  `InfersHW T (bitVector N) ∧ InfersNoCatch T`, an oracle premise of the
  class already used. (To be confirmed by the DETAIL lines.) No new binder
  kind and no change of `prepare` / `Admissible`.
* **The leaf** `Signal.fst (Signal.snd (… x))`: head a constant, the core
  declines (not a canonical operator), `fallbackKind = other` (census round
  20: 39 of 39), the instance arm reads the environment (`PlainHead`), the
  shim (`isNamed = true` at the top: the body), the body's prefix
  (`pre_plain` applies: `Signal.fst` fails every test of `ImplName`; premise
  `HasMappedFVar`), `Rec.translateExprToWireApp`: `handleErrorPatterns`,
  the inline guards, `handleCircuitMonad` (returns `none`:
  `handleCircuitMonad_none`), then `handleTupleProjections` ACCEPTS (6820).
* **The accepting arm** (`Rec.handleTupleProjections`, 5647–5757):
  - 5654–5660: `isTupleName`, `unless … return none`;
  - `Signal.fst`, 5662–5684: `s := args[args.size-1]!`;
    `wireS ← translateExprToWire s "s" (isTopLevel := false)` (so
    `isNamed = false`); `wireWidth ← getWireWidth wireS`;
    `hwType ← inferHWTypeFromSignal (← cachedInferType e)`;
    `resWire ← makeWire hint hwType (named := isNamed)`;
    `width` from `hwType` (`bitVector w ↦ w`, `bit ↦ 1`, else 8);
    `typeTotal` from `inferHWTypeFromSignal (← cachedInferType s)`;
    `totalWidth := min wireWidth typeTotal`;
    `lo := if totalWidth ≥ width then totalWidth - width else 0`;
    `hi := if totalWidth ≥ 1 then totalWidth - 1 else 0`;
    `emitAssign resWire (.slice (.ref wireS) hi lo)`; `return some resWire`.
    The HIGH `width` bits.
  - `Signal.snd`, 5687–5700: the same up to `width`;
    `actualWidth := min width wireWidth`;
    `emitAssign resWire (.slice (.ref wireS) (actualWidth - 1) 0)`. The LOW
    bits.
  - `bundle2` (5705–5712) and `Signal.map Prod.fst / Prod.snd` (5718–5755)
    are the other accepting arms; not in this class unless pass 4 reports a
    `Signal.map` terminal.

  Transcriptions: `fstArmProg`, `sndArmProg`
  (`Tools/ShippingLegacySemFstArm.lean`).

## 95. Item 2 — the statement without a new value model

`Tools/ShippingLegacySemFst.lean`:

* the input binder is `.bits N`, its value `Value.bits N (bits x N)` — the
  PACKED vector;
* `sliceValue v lo rk`: `Value.bits w (v.extractLsb' lo w)` for a
  `bitVector w` result, `Value.bool (v.getLsbD lo)` for a `bit` result;
* `fst_entry_output_of_chain` (PROVED modulo the build): memo hit, or
  `RawValueAt rk.width bs m initial mems (sliceValue (bits x N) lo rk).toNat`,
  from the walk's obligation `FstChainLeaf declName bs leafOf i N lo rk` —
  "in every prepared setup that maps the variable at position `i` to the
  packed input, the leaf is in `LeafDom … "out" true` at the slice value".
  Everything of the ENTRY is discharged in it (any arity, the domain skip,
  the input fact, the harness); `FstChainLeaf` is a statement about the
  translator on the leaf only.

**The missing SEM0 piece** (`Tools/ShippingLegacySemPacked.lean`,
definitions): a packing of product VALUES does not exist in the certified
development — `Tools.ShippingUnifiedMeaning.pack` packs a scalar into a
`Value`; `packList` / `packLets` (machine route) concatenate lists of TERMS,
first in the high bits; `encState` encodes slot by slot. Defined: `PShape`
(`bool`, `bits w`, `unit`, `prod`), `PShape.width`, `PShape.Ty`,
`PShape.pack : (s : PShape) → s.Ty → BitVec s.width` (first component high:
`pack a ++ pack b`), `PShape.field` (sub-shape and low offset of a chain).
Bridge lemmas PROVED (one step each, pure `BitVec`):

```
PShape.pack_fst : ((prod a b).pack p).extractLsb' b.width a.width = a.pack p.1
PShape.pack_snd : ((prod a b).pack p).extractLsb' 0 b.width       = b.pack p.2
```

Not written: the chain bridge (needs the dependently typed projection of a
value along a path), the Bool leaf in `Value` form
(`((prod .bool b).pack p).getLsbD b.width = p.1`), and the link from `s.Ty`
to the payload type the oracle sees (its `whnf` is at transparency `all`).
Under it the statement of `fst_entry_output_of_chain` reads: `out` carries
the packed FIELD. The convention agrees with the machine route's `packList`
("the first in the high bits").

## 96. Item 3 — the decomposition of `FstChainLeaf`

For a chain `c₁ (c₂ (… (cₖ x)))`, `cⱼ ∈ {Signal.fst, Signal.snd}`, by
induction from the variable outwards. One step, for `e = Signal.fst … s`
(resp. `snd`) with the argument's packed value `Value.bits M u`:

1. to the arm: `step_run_fallback` (`NotCore`), `fallback_eq_arm`
   (`fallbackKind = other`), `arm_to_shim` (`PlainHead`), the shim
   (`legacyShim_returns`), `pre_plain` (`ImplName`, `HasMappedFVar`), the
   prefix of `Rec.translateExprToWireApp` up to 6820 with
   `handleErrorPatterns_frame` and `handleCircuitMonad_none` (a variant of
   `bodyReachesInline_of_walk`'s `hchain` that stops at the second handler
   and takes its `some w`) — existing lemmas except the last;
2. `FstArmIs` / `SndArmIs` (statements in
   `Tools/ShippingLegacySemFstArm.lean`): the handler's run is a run of the
   transcription;
3. the transcription's run, inverted: the argument's run at
   `("s", false, false)`; `getWireWidth` (premise `WireWidthReads … M`);
   two `cachedInferType` + oracle steps (premises `InfersHW` on the node's
   type — `bitVector w` or `bit` — and on the argument's type —
   `bitVector M`); `makeWire_returns`; `emitAssign_returns`;
4. semantics of the emitted assignment: `resWire := slice (ref wireS) hi lo`
   with `hi = M - 1`, `lo = M - w` (fst) or `hi = w - 1`, `lo = 0` (snd):
   frame, `Inv` preserved, the wire carries
   `Value.bits w (u.extractLsb' lo w)` (resp. the Bool form) — the certified
   slice lowering's lemmas (slice vertical, `054dcb6`) are the model; order
   statement as for one emitted assignment;
5. the offsets compose: `extractLsb'` of `extractLsb'`
   (`BitVec.extractLsb'_extractLsb'_of_le` and its shifted form).

The base is the input variable (`LegacyDom` input: `input_contract`).

## 97. The three points that need a decision

**D1 — `HandlerCase` fixes the sub-expressions' hint and name flag to the
node's.** `HandlerCase ctx inputs hint named e v subs` asks `ActionSpec` of
`translateFuelFix translateStep fuel e' hint false named` for the
sub-expressions; `LeafDom.handled` asks `LeafDom ctx inputs hint named e' v'`.
The arm translates its argument at `("s", false, false)` while the node is
at `("out", false, true)` (top of the chain) or `("s", false, false)`
(below). So the arm is not a `HandlerCase`. Options: (a) generalise
`HandlerCase` / `LeafDom` in `Tools/ShippingLegacySemLeaf.lean` so that
`subs` carries its own hint and flag (`subs : String → Bool → Expr → Value →
Prop`, the two fuel theorems re-proved — a change to an existing shared
file, mechanical); (b) a second domain in a new file with its own fuel
induction and its own harness connection (`leaf_translate_spec` /
`…_order` duplicated). (a) is smaller and keeps one domain.

**D2 — the argument call is cacheable.** `cacheable := !isNamed &&
!e.isFVar && !isTopLevel` (7920): for depth 1 the argument is the variable
(not cacheable; the core's variable arm), for depth ≥ 2 it is a
`Signal.snd`/`fst` application at `isNamed = false`: the shim reads the
`IO.Ref` expression cache (the entry always sets one) and on a hit returns
its wire unvalidated (`legacyShim_returns`' second disjunct: `t = s`, the
wire unknown). Options: (a) the premise `ArgRunsBody tr ctx e` per chain
node (the existing `ShimAt` at these flags; class: the run / the world;
false of a run that hits a stale entry — the same status as `NoSubModule`
has today); (b) the validated shim of the cache fix (variant A, isolated,
not merged) — then the hit's wire is `translateRecord`-validated and the
walk needs the record invariant; (c) depth 1 only (1 of the 39 at most).

**D3 — the slice bounds read the world.** `getWireWidth wireS` (210–233)
reads `sparkleWireWidthCache` (an `IO.Ref`) FIRST and the builder state's
ports only on a miss; `totalWidth := min wireWidth typeTotal` then fixes
`hi` / `lo`. `Returns` does not constrain the reference, so the emitted
slice is not determined by the run: with a stale entry `n < M` the `fst`
arm emits `[n-1 : n-w]`. Options: (a) the premise `WireWidthReads ctx s
wireS M` per chain node (class: the world; true when the cache agrees with
the builder state — it is written by `makeWire` / `addInput` / `addOutput`
only, and keyed by wire NAME, so a name reused across syntheses or after a
rollback is exactly the stale case of the cache-rollback line); (b) a
compiler change: read the declared width from the builder state (the
fallback branch) — then the width follows from `Inv`'s width clause; (c) a
world model carrying "width cache ⊆ builder state" through `Returns`
(large: every inversion lemma).

D2 and D3 are the same phenomenon as G2's cache gap: handler-visible
`IO.Ref` state that `Returns` abstracts. Under (a)/(a) the class's theorem
gets two more per-node premises of the class "the run"; under (b)/(b) none.

## 98. Coverage after this round

Of the 90 RETURNED declarations: 45 projections covered by
`proj_entry_output` (round 22; census `fits 45 of 45`). The 39 `Signal.fst`
chains: the entry part proved (`fst_entry_output_of_chain`), the walk's
obligation `FstChainLeaf` open pending D1–D3. The remaining 6: untouched.

## 99. Files

* `Tools/ShippingLegacySemPacked.lean` (new, no imports): SEM0 packing.
* `Tools/ShippingLegacySemFst.lean` (new): `sliceValue`, `FstChainLeaf`,
  `fst_entry_output_of_chain`.
* `Tools/ShippingLegacySemFstArm.lean` (new, statements only, imported by
  nothing): `fstArmProg`, `sndArmProg`, `FstArmIs`, `SndArmIs`,
  `WireWidthReads`, `ArgRunsBody`.
* `Tests/Compiler/LegacyArmCensusTest.lean`: pass 4.
* `Tests/Compiler/LegacySemInstanceTest.lean`: import, header, audit
  (`fst_entry_output_of_chain`, `PShape.pack_fst`, `PShape.pack_snd`).

## 100. Spots most likely not to elaborate, in order of risk

1. Census pass 4 (compiled code): `payloadShape` / `chainRange` (`partial`,
   `evalNat … |>.run`, `isAppOfArity`), `sliceOfInput` (structural on the
   fuel, nested `Except` patterns), the two consecutive `match`es with
   `let mut` updates inside the `for`.
2. `Tools/ShippingLegacySemFstArm.lean`: the two `do` transcriptions
   (`let width : Nat := match … with`, `tr s "s" false false`,
   `CompilerM.makeWire hint hwType named`), `args[args.size - 1]!` in a
   `Prop`.
3. `Tools/ShippingLegacySemPacked.lean`: `PShape.pack` (dependent match;
   `Prod.fst x` on `x : (prod a b).Ty`), the two bridge proofs (three
   alternatives each).
4. `Tools/ShippingLegacySemFst.lean`: `hchain ids x …` (applying a
   hypothesis whose type is a definition), `rw [sliceValue_width] at out`.
