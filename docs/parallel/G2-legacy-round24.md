# G2 — worker, round 24 (branch `par/g2-legacy-24`, base `par/g2-legacy-23` = `cf15eb9c`)

Nothing here was built (no Lean run from a worker; round 23's `cf15eb9c` was
itself not built when this was written). To be folded into
`docs/parallel/G2-legacy.md` as §101–§108.

**Status in one line**: with the three decisions of round 23 taken (D1 (a),
D2 (a), D3 (a)), the whole of item 3 is WRITTEN: the `HandlerCase`
generalisation with its dependents, the walk of the two accepting arms, the
arms as handler cases over the certified slice lowering, the chain induction,
offset composition, and `fst_entry_output`.

## 101. D1 — `HandlerCase` / `LeafDom` with per-sub-expression flags

`Tools/ShippingLegacySemLeaf.lean`:

* `HandlerCase … (subs : String → Bool → Lean.Expr → Value → Prop)`:
  `subs h' n' e' v'` — the arm translates `e'` (value `v'`) at hint `h'` and
  name flag `n'`; `spec` / `order` ask the sub-expressions' `ActionSpec` /
  `ActionOrder` at `translateFuelFix translateStep fuel e' h' false n'`. (No
  top flag: every sub-translation of the arms walked so far passes
  `isTopLevel := false`.)
* `LeafDom ctx inputs : String → Bool → Lean.Expr → Value → Prop` — the hint
  and the name flag are now INDICES (they were parameters); the applied form
  `LeafDom ctx inputs hint named e v` is unchanged, so no statement that
  mentions it changed. `handled` asks `LeafDom ctx inputs h' n' e' v'` of the
  sub-expressions.
* `leaf_fuel_spec` / `leaf_fuel_order`: the same inductions, the case
  patterns naming the indices (`@dom hint named e v hd`, …).

Dependents repaired: `…LeafHandled.lean` (`handlerCase_inline`,
`LeafDom.inline_handled`: `subs h' n' e' v' := h' = hint ∧ n' = named ∧
InlineUnfolds e e' ∧ v' = v` — the old meaning), `…Beta.lean`
(`handlerCase_wire`, `leafDom_betaWire`: `fun _ _ _ _ => False`). The other
files named by the integrator (`…EntryOne`, `…EntryBound`, `…EntryList`,
`…EntryListD`, `…Proj`, `…Fst`, the tests) only MENTION `LeafDom … hint named
e v` or use the constructors `dom` / `inlineAt` with inferred indices: read,
no change needed.

## 102. The arm, walked (`Tools/ShippingLegacySemFstArm.lean`, rewritten)

`FstArmIs` / `SndArmIs` of round 23 ("a run of the handler is a run of the
transcription") are DROPPED, with the transcriptions: a `match` written in a
Tools file is a different matcher constant from the handler's (lesson of
this project), so the transcription is not the handler's arm definitionally;
and a `Returns` of a composite program cannot be assembled from runs of its
parts (`Returns` hides the world). The walk ends in the PARTS instead:

* `fstArm_run` — name test `(name == Signal.fst) = true`, `1 ≤ args.size`,
  `args[args.size-1]! = a`, the oracles `ExprHW e (hwTypeFromWidth w)` and
  `ExprHW a (bitVector M)`, the width premise `ArgWidthReads tr ctx a M`,
  `0 < w ≤ M`: a successful run of the handler is a run of
  `tr a "s" false false` returning `sw` to `s1`, the result is `some res`
  with `res = (makeWire hint (hwTypeFromWidth w) named s1).1`, and the end
  state is `(emitAssign res (sliceRhs (M - w) w sw) (makeWire … s1).2).2`.
* `sndArm_run` — the same with `sliceRhs 0 w sw` (no oracle on the
  argument's type: the arm does not ask it).

Steps T0–T8 in the file's header. The two places written against an
UNOBSERVED shape: T0 (`unless isTupleName do return none` — handled for
either polarity of the `if`, and with or without a `pure ()` in front of the
arms), and the computation of the slice bounds after the substitutions
(`simp only [Nat.min_self, ge_iff_le, …, ↓reduceIte]`, with three fallbacks).

## 103. The arms as handler cases; reuse of the certified slice lowering

`slice_fresh` / `slice_order` are stated for `do let sw ← rec ae h false
false; emitSliceResult (sliceRhs start len sw) len hint named`. The legacy
arm emits the same wire and assignment but with two oracle calls BETWEEN the
allocation and the assignment (fst), so its run is not a run of
`emitSliceResult`. Reused AS THEY ARE: `allocate_assign_outcome`,
`sliceRhs_simple`, `sliceRhs_typed`, `sliceRhs_eval`, `sliceRhs_refs`,
`Frame.makeWire`, `Frame.emitAssign`, `hwTypeFromWidth_bitWidth`. Restated on
builder states (`Tools/ShippingLegacySemSliceEmit.lean`), their proofs the
certified ones with the `Returns` inversion removed: `frame_makeWire_bit`
(the allocation half of `emit_bool_frame`), `allocAssign_order`
(`emit_cast_order` with the wire's type general). On top:

* `SliceRuns action sub ctx hint named start w` — every run of `action` is a
  run of `sub`, then the allocation and the slice assignment;
* `sliceNode_spec` (`slice_fresh`'s proof), `sliceNode_order`
  (`slice_order`'s);
* `handlerCase_fst`, `handlerCase_snd` — `HandlerCase` with
  `subs h' n' e' v' := h' = "s" ∧ n' = false ∧ e' = a ∧ v' = Value.bits M u`,
  node value `Value.bits w (u.extractLsb' (M - w) w)` resp. `(… 0 w)`.

A one-bit result is carried as `Value.bits 1 _` (the wire is a `bit`):
`Outcome` and `RawValueAt` read a value only through `kind.width` and
`toNat`, so no `Value.bool` form is needed — `sliceValue`'s Bool case of
round 23 is not used by the new theorem.

The path from the node to the handler (`tuple_reach`): `step_run_fallback`,
`fallback_eq_arm`, `arm_to_shim`, the shim (`ShimBody`: PROVED for a named
node, `shimBody_named`; the premise `ArgRunsBody` at `("s", false)`),
`pre_plain`, `chain_tuple` (the walk of `chain_plain`, stopped at the second
handler).

## 104. The chain and the entry theorem (`Tools/ShippingLegacySemFstEntry.lean`)

* `SubChain ctx x N e M g` — the chain over the variable `x`, with its packed
  width `M` and its value as a function `g : BitVec N → BitVec M` of the
  packed input; constructors `var`, `fst`, `snd` carrying the node facts.
* `subChain_leaf` (induction): `LeafDom ctx inputs "s" false e
  (Value.bits M (g v))`. `topFst_leaf`: the top `Signal.fst` at the entry's
  flags.
* `extract_extract`, `subChain_slice` (offset composition): `g v =
  v.extractLsb' lo M`, `lo + M ≤ N`.
* `fst_entry_output`: memo hit, or
  `RawValueAt w bs m initial mems (g (bits x N)).toNat`.

## 105. Premises of `fst_entry_output`, classified

| Premise | Class |
|---|---|
| `old`, `mixed`, `hmach` | reflection of the environment |
| `htel : LamTelescopeND` | Meta-library fact |
| `hbody` | reflection + binder-type oracle (`TypesOkFrom`: `InfersHW T (bitVector N)` on the structured binder) |
| `hfield` | closed fact |
| `thF`, `thS : TupleHead …`, `hne` | closed name tests (proved in the instance test: `fst_tupleHead`, `snd_tupleHead`, `snd_ne_fst`) |
| `plainF`, `plainS : PlainHead …` | environment (not a hardware module, not a projection) |
| `hlam` | closed computation on the leaf |
| `hres` | result-type oracle |
| per node `head`, `arg`, `size`, `kind`, `notCore` | closed computations on the node |
| per node `mapped` | the body's `whnf` test (`Expr.find?`, kernel-opaque) |
| per node `nodeHW`, `ExprHW a (bitVector M)` | oracle (`cachedInferType` then `inferHWTypeFromSignal`) |
| per node `widthReads` → `WireWidthReads` | THE RUN / THE WORLD |
| per node below the top `ArgRunsBody` | THE RUN / THE WORLD |
| `hr` | the run |

## 106. FINDING for the user — the slice bounds are not determined by the builder state

`CompilerM.getWireWidth` (`Sparkle/Compiler/Elab.lean` 210–233) reads the
`IO.Ref` `sparkleWireWidthCache` FIRST (216–218) and looks at the builder
state's ports only on a miss (224–233). The `Signal.fst` arm computes its
slice from that number: `totalWidth := min wireWidth typeTotal` (5680),
`lo := totalWidth - width`, `hi := totalWidth - 1` (5681–5682); the
`Signal.snd` arm `actualWidth := min width wireWidth`, `hi := actualWidth - 1`
(5697–5698). (`Signal.map Prod.fst / Prod.snd`, 5725–5753, the same.) So the
emitted slice bounds depend on the CONTENTS OF A GLOBAL REFERENCE, not on
the builder state of the run; `Returns` (the run relation of this
development) says nothing about that reference.

Which stale values matter (`M` = the argument wire's true width, `w` = the
result's):

* a stale LARGER width is harmless in both arms: `min ww M = M` when
  `M ≤ ww` (fst), `min w ww = w` when `w ≤ ww` (snd);
* a stale SMALLER width is harmful. Smallest scenario for `fst`: the
  argument wire is declared `bitVector 16`, the field is the high 4 bits
  (`M = 16`, `w = 4`), the cache holds 8 for the wire's name: the arm emits
  `[7:4]` instead of `[15:12]` — well-typed RTL, wrong bits, no error. For
  `snd` with `ww < w`: `[ww-1:0]` assigned to a `w`-bit wire — the high bits
  are lost.

So the premise the theorem needs is only `M ≤ ww` (fst) / `w ≤ ww` (snd);
`WireWidthReads … M` (equality), as decided, is stronger than necessary.

When can the cache be stale? It is keyed by wire NAME and written by
`makeWire` (179–181), `addInput` (198–199), `addOutput`. A wire of type
`bit` / `bitVector` is entered by the very `makeWire` that allocates it, so
in a straight run the read is right. It goes stale when a name is allocated
again with another width without the entry being put back: after a `catch`
that restores the builder state (name counter included) but not the cache —
on this branch `restoreWireCaches` (5611–5622) restores `wireWidth`, which
closes that case for the catches that call it — or if nested / successive
syntheses share the reference (not checked this round where
`sparkleWireWidthCache` is reset). A `bitVectorDim` wire is not entered at
all (`legacyCacheWidth?` 167–171), an `array` wire is entered as 8.

The fix that would remove the premise (not assumed anywhere): read the
declared width from the builder state (the fallback branch) — then the width
follows from the invariant's width clause.

## 107. Coverage

Of the 90 RETURNED declarations: 45 projections (`proj_entry_output`,
census 45 of 45); the 39 `Signal.fst` chains now have their theorem
(`fst_entry_output`), with two premises of the class "the run / the world"
per node that the projection class does not have. Whether the 39 are all
chains over the variable ending in a top `Signal.fst` is what round 23's
`FST CLASS` lines say (not seen yet). The remaining 6: untouched.

## 108. Spots most likely not to elaborate, in order of risk

1. `…FstArm.lean`, `fstArm_run` / `sndArm_run`: T0 (the shape of `unless …
   return none`; `all_goals try (exfalso; revert hc0; simp [hn]; done)`),
   T1 (`returns_ite_pos` with the guard `(name == … && decide (args.size ≥
   1)) = true`), the binds T3–T8 through the pure `let`s, `rw [hwwM, hST] at
   hs8`, and above all the slice-bound computation (`simp only [Nat.min_self,
   ge_iff_le, hM1, ↓reduceIte] at hs8` reducing the handler's two `match`es
   on constructors and the two `if`s).
2. `…FstArm.lean`, `chain_tuple` (copy of `chain_plain` up to the second
   handler; the `Ensures` lemmas applied to `u s1 (profHandler_returns …)`).
3. `…SliceEmit.lean`: `frame_makeWire_bit` (the nine bullets),
   `allocAssign_order` (copy), name resolution under the copied `open` list.
4. `…Leaf.lean`: `induction h with | @dom hint named e v hd => …` with the
   hint and flag as indices.
5. `…FstEntry.lean`: `SubChain` (a dependent index `BitVec N → BitVec M`),
   the two inductions, `extract_extract` (`simp only` on `getLsbD`).
6. The instance test: `fst_implName` / `snd_implName` (27 closed tests each;
   the suffix tests on a four-component name through `cands`),
   `fst_binOp` / `snd_binOp`.
