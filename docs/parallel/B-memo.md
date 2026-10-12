# B — the memo `sparkleSubModuleCache` in the runtime boundary (branch `par/b-1`, base `fix/cache-rollback` = `d160afd4`)

**Nothing here was built** (no Lean run from a worker). Every proof below is
written against sources read, not against the elaborator. Line numbers:
`Sparkle/Compiler/Elab.lean` and `Tools/ShippingChildInv.lean` at `d160afd4`.

New files: `Tools/ShippingMemoLaws.lean`, `Tools/ShippingLegacySemMemoWalk.lean`,
`Tools/ShippingMemoInv.lean`, `Tests/Compiler/LegacySemMemoTest.lean`.
Edited (doc comment only): `Tools/ShippingLegacySemMemo.lean`.

The results are theorems under an EXTENDED trust base (last section). They are
not a completion of the general theorem.

## 1. Inventory

### 1a. The machine route's runtime boundary (`Tools/ShippingChildInv.lean`)

All of it is over the two state references `mref : ST.Ref IO.RealWorld
Meta.State`, `cref : ST.Ref IO.RealWorld Core.State` and worlds `Void
IO.RealWorld`; a run is `RunsTo m mctx mref cctx cref w a w'`
(`Tools/ShippingEntrySoundness.lean:935`: `m mctx mref cctx cref w =
EST.Out.ok a w'`).

* `RefLaws` (l. 331, `structure RefLaws where`, in a section with `variable
  (mref) (cref)`): value functions of THREE cells —
  `val : Void IO.RealWorld → Std.HashMap Name Res` (`sparkleChildCache`),
  `sval : Void IO.RealWorld → Option (Name → MetaM Res)` (`sparkleChildSynth`),
  `dval : Void IO.RealWorld → Nat` (`sparkleSynthDepth`); a proof parameter
  `aux` / `auxInsert`; `quiet : Void IO.RealWorld → Prop` (l. 349: "the worlds
  in which the diagnostic operations do not touch the three refs"); the laws
  `diag`, `frameT`, `excOk`, `frameQ`, `cacheSetQ`, `cacheModifyQ`,
  `depthSetQ`, `depthModifyQ`, `frame` (every `Framed` operation leaves `val`,
  `sval`, `dval` — on every outcome, through `endW`), `cacheGet`, `cacheSet`,
  `cacheModify`, `synthGet`, `depthGet`, `depthSet`, `depthModify`, and four
  continuation laws (`telescope`, `lamTelescope`, `localDecl`, `letDecl`).
  It speaks about the three cells only. The memo has no value function in it.
* `Framed` (l. 187, `inductive Framed : {α : Type} → MetaM α → Prop`): reads
  of the three cells; `sideGet` / `sideSet` / `sideModify` / `sideModifyGet`
  (and their `IO`-lifted forms) of ANY ref of `SideRef`; `ioEnv`,
  `constInfo`, `env`, Lean primitives (`whnf`, `inferType`, …), `monoMs`,
  run-local refs.
* **The memo inside `Framed`**: `SideRef.subModule : SideRef
  sparkleSubModuleCache` (l. 73). Hence `Framed.sideSet v .subModule` (l. 192)
  is the memo's `set`, `Framed.sideModify f .subModule` (l. 193) its
  `modify`, `Framed.sideGet .subModule` (l. 191) its read. They are used as
  such: the depth-0 reset `sparkleSubModuleCache.set {}` is the fourth `tset`
  of `core_keeps` (`Tools/ShippingChildKeeps.lean:416`) and a `peel_inv` step
  of `core_reads_inv` (`Tools/ShippingChildRun.lean:168`, through
  `inv_framed`); the legacy arm's read and the four `modify … insert` are
  discharged as `Framed` side goals by the `vc` tactic in `bodyRel`
  (`Tools/ShippingChildVC.lean:635–686`, `Tools/ShippingChildBody.lean`).
  `RefLaws.frame` is therefore TRUE of operations that change the memo: it
  cannot be read as "the memo is unchanged".
* `InvW` (l. 477): `CacheAt mref cref w ∧ SynthAt mref cref w ∧ QuietAt mref
  cref w` — the child cache's entries read in `w` are `RealChild`s, the
  synthesis ref reads `synthesizeChild`, `w` is quiet for some witness. Child
  cache and synthesis ref only.
* `StartV` (l. 508): `L.sval w = some synthesizeChild ∧ (L.dval w = 0 ∨
  CacheInv mref cref (L.val w))`.
* `ChildLaws` (l. 593): `Nonempty (RefLaws mref cref)`.
* `ChildBnd` (l. 600): `∃ L : RefLaws mref cref, StartV L w ∧ L.quiet w`.
* The comment at the head of that file and the project's own notes: the laws
  are a parameter; there is no runtime model; nothing says they are
  consistent with the real runtime.

### 1b. From the depth-0 reset to the legacy arm's read — every operation

`synthesizeCombinationalCoreWith` (l. 5388) at depth 0, not symbolic, then
`synthesizeFromConst` (l. 5263).

| Line | Operation | Class |
|---|---|---|
| 5469 | `sparkleSubModuleCache.set {}` | **the memo itself — the reset** |
| 5470 | `sparkleChildCache.set {}` | `IO.Ref` ≠ memo (SAME element type as the memo) |
| 5471 | `sparkleSubInstanceOutputs.set {}` | `IO.Ref` ≠ memo |
| 5472 | `sparkleSingleOutInstanceCache.set {}` | `IO.Ref` ≠ memo |
| 5473 | `sparkleFvarValueMap.set {}` | `IO.Ref` ≠ memo |
| 5474 | `sparkleWireWidthCache.set {}` | `IO.Ref` ≠ memo |
| 5475 | `sparkleLetWireCache.set {}` | `IO.Ref` ≠ memo |
| 5476 | `sparkleLoopWireCache.set {}` | `IO.Ref` ≠ memo |
| 5477 | `sparkleWireCanon.set {}` | `IO.Ref` ≠ memo |
| 5488 | `sparkleSynthDepth.set (depth + 1)` | `IO.Ref` ≠ memo |
| 5493–5501 | `let doSynth := …`, `try doSynth finally …` | pure / a combinator: the body starts in the world the `try` starts in (`RunsTo.try_finally`); the `finally` runs after the body |
| 5494 | `getConstInfo declName` | Core state (environment read; can throw) |
| 5495 | `getEnv` | Core state |
| 5498–5500 | `entryConst …`, `instancePredicate env`, `userInliner env`, `structEnv env` | pure |
| 5268 | `match (if cfe then certifiedShape? … else none)` | pure; `some` ⇒ the certified arm, the read is not reached |
| 5275 | `match (if cfe then mixedCertifiedShape? … else none)` | pure; `some` ⇒ the mixed arm, the read is not reached |
| 5286–5290 | `if cfe && !symbolicMode && parameters.isEmpty then (getEnv; pure (machineShape? …)) else pure none` | Core state (`getEnv`, only with the front end on), then pure |
| 5291–5294 | `match machine? with \| some shape => synthesizeMachineCertified … \| none => pure none` | `none`: pure. **`some shape`: a CALLBACK** — the harness runs the translator and `closeInstsM` / `closeInstsGM` call `synthesizeChild` (l. 5191–5192, 5208–5213), which reaches `synthesizeFromConst` and writes the memo. NOT in the frame class |
| 5295–5300 | `match machineResult?` | pure; `some` ⇒ the machine arm's write (5298), the read is not reached |
| 5309–5310 | `if !symbolicMode then let memo ← sparkleSubModuleCache.get` | **the memo itself — the read** |

No `logProf` call lies between the two (the "entering" log, l. 5408, is
before the reset; the next one, l. 5314, after the read). Before the reset
the run does `IO.getEnv "SPARKLE_PROFILE"` (5400), the logger (5408),
`sparkleSynthDepth.get` (5429), the depth guard (5430), two `pure`s at depth
0 (5447, 5462) and three `set`s (5466–5468): they matter only for knowing
that the depth read is the start world's (`RefLaws.frame` for `ioEnv`,
`RefLaws.diag` for the logger — this is why the start world must be quiet).

So with `machine? = none` the operations between reset and read are exactly:
nine `set`s of nine named refs other than the memo, `getConstInfo`, `getEnv`
(once, or twice with the front end on), and pure steps. That is the frame
class `MemoFrameOp` (§2).

### 1c. Who can write `declName ↦ r` before a nested read; which combinations collide

Writers (all in `synthesizeFromConst`, each after its arm succeeded): the
certified arm 5272, the mixed arm 5279, the machine arm 5298, the legacy arm
5363 (under `!symbolicMode`). One reset: 5469. One reader: 5310 (under
`!symbolicMode`, after the three gates). A memo HIT returns without writing
(5311–5313).

Callers of `synthesizeFromConst`: one, `synthesizeCombinationalCoreWith`
(5496). Callers of that, in `Sparkle/`:

* `synthesizeCombinationalWith translate declName` (5516): `[] false`, the
  front end defaulted to `true` — the shipping entry `synthesizeCombinational`
  (8836) and every command (8873, 8920, 8978, 9032, …);
* `Rec.synthesizeCombinationalWithParameters` (7954): `parameters true`,
  front end `true`. With `symbolicMode = true` the three gates return `none`
  (2314, 2875, 5059; the machine gate's own guard 5287), the read is skipped
  (5309) and the legacy write is skipped (5362): **a symbolic run neither
  reads nor writes the memo**;
* tests only: `(certifiedFrontEnd := false)` at depth 0
  (`Tests/Compiler/LegacySemInstanceTest.lean`, `…HierarchySoundnessTest`,
  `…InlineSoundnessTest`, `…BoolLiftSoundnessTest`), some with another
  translator (`fuelFix …`).

NESTED syntheses: every one goes through `sparkleChildSynth` =
`synthesizeChild` (8844–8849) — from the translator (`Rec.synthesizeCombinational`
= `childSynthEntry`, 6254–6256, used at 6508, 6520; `childSynthEntry` at
8645, 8663) and from the machine closings (5192, 5213). `synthesizeChild n`
answers from `sparkleChildCache` if it can and otherwise runs
`synthesizeCombinational n`. So **every nested run of `synthesizeFromConst`
has the same configuration: no parameters, not symbolic, front end ON, the
real translator, the entry's own logger.** The constant it is handed is
`entryConst true false [] (getConstInfo n) …` of the environment read by THAT
run (5494–5500).

Which combinations can collide under one name inside one depth-0 run:

1. *Different flags / parameters / translator*: only the OUTERMOST run can
   differ from the nested configuration, and it writes its own name as its
   last effectful step (after it no read happens in that run; the next
   depth-0 run resets). A collision "same name, different flags" inside one
   depth-0 run therefore needs the outermost declaration to be synthesised
   again as a child inside its own run (a by-name cycle). Even then every
   entry that a read can RETURN was written by a nested-configuration run:
   the outermost's own entry does not exist yet when anything reads. By
   reading — not proved.
2. *Different constant under one name*: the key ignores the constant and the
   instance predicate. Two nested runs on one name are handed the same
   constant only if `getConstInfo n` and `getEnv` return the same in both —
   nothing in the boundary says the environment is unchanged within a
   depth-0 run (`RefLaws` has no law about the content of `cref`). This is
   the collision that matters for the nested hit (§5).
3. *At the end of a non-shipping outermost run* (front end off, or another
   translator) the memo holds that run's own entry, written under a
   configuration no nested reader has. It is never read (reset first). An
   invariant "every entry was written in the nested configuration" is false
   at that world.

Observation (by reading, NOT proved, relevant to what the hit branch is
worth): a nested request for `n` is answered by `sparkleChildCache` whenever
an earlier nested run of `n` in this depth-0 run completed, because that run
wrote the memo (inside `synthesizeFromConst`) and then the child cache
(8847) with nothing fallible in between (the `finally`, `dropZeroWidthModule`,
`IO.getEnv`, `mergeChecked`). So the memo's read can hit only when an entry
for `n` exists while `n`'s own child-cache entry does not — a by-name cycle
(`n` requested inside its own synthesis, combined with the machine arm's
fall-through for the outer `n`). If that is right, the hit branch is dead on
every acyclic design, and deleting the read (a compiler change — not made,
not proposed as verified) would remove `MemoHit` from every legacy theorem
with no law at all. A cheap measurement: count `MEMO HIT` profile lines over
the corpus.

## 2. The boundary (`Tools/ShippingMemoLaws.lean`)

`RefLaws` is a structure over `(mref, cref)` with value functions on worlds;
it can be extended without editing its file. `RefLawsM mref cref extends
RefLaws mref cref`: the same references, the same worlds, the same `RunsTo`.

```lean
inductive MemoOther : {σ : Type} → IO.Ref σ → Prop
  | childCache : MemoOther sparkleChildCache
  | subInstOut : MemoOther sparkleSubInstanceOutputs
  | singleOut : MemoOther sparkleSingleOutInstanceCache
  | fvarValue : MemoOther sparkleFvarValueMap
  | wireWidth : MemoOther sparkleWireWidthCache
  | letWire : MemoOther sparkleLetWireCache
  | loopWire : MemoOther sparkleLoopWireCache
  | wireCanon : MemoOther sparkleWireCanon
  | synthDepth : MemoOther sparkleSynthDepth

inductive MemoFrameOp : {α : Type} → MetaM α → Prop
  | otherSet {σ : Type} (r : IO.Ref σ) (v : σ) : MemoOther r →
      ¬ HEq r sparkleSubModuleCache → MemoFrameOp (ST.Ref.set r v : MetaM Unit)
  | constInfo (n : Name) : MemoFrameOp (getConstInfo n : MetaM _)
  | env : MemoFrameOp (getEnv : MetaM Environment)

structure RefLawsM (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) extends RefLaws mref cref where
  mval : Void IO.RealWorld → Std.HashMap Name Res
  memoGet : ∀ {mctx : Meta.Context} {cctx : Core.Context} w m w',
    RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w m w' →
    m = mval w ∧ mval w' = mval w
  memoSet : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → mval w' = v
  memoModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}
    (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    mval w' = f (mval w)
  distinct : ∀ {σ : Type} (r : IO.Ref σ), MemoOther r → ¬ HEq r sparkleSubModuleCache
  memoFrame : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α),
    MemoFrameOp p → ∀ w a w', RunsTo p mctx mref cctx cref w a w' → mval w' = mval w
```

* The frame class has three constructors and nine enumerated refs. It
  contains no operation of the memo, no callback, no translator or harness
  run, no diagnostic operation, no ref outside the nine. It is asked on
  successful runs only (enough for a returning run's prefix).
* The side condition of `otherSet` is an argument of the constructor: the
  frame law says nothing of a `set` whose ref is not shown distinct from the
  memo. That the nine ARE distinct is the separate field `distinct` — an
  assumption (`sparkleChildCache` has the memo's type; the constants are
  opaque `initialize` declarations; the logic can neither prove nor refute
  it).
* No field speaks of what the memo contains.
* `ChildLaws` / `ChildBnd` re-read over the one structure: `ChildLawsM mref
  cref := Nonempty (RefLawsM mref cref)`, `ChildBndM mref cref w := ∃ L :
  RefLawsM mref cref, StartV L.toRefLaws w ∧ L.quiet w`, with
  `ChildLawsM.toChildLaws` and `ChildBndM.toChildBnd` by projection. A
  consumer holds one witness; the machine route's files are untouched.
* The round-13 sketch `MemoLaws` (`Tools/ShippingLegacySemMemo.lean`) is a
  standalone structure — a separate witness. It is marked superseded; nothing
  imports it.

## 3. Is the depth-0 miss true? — yes, with one side condition

From §1b: between the reset (5469) and the read (5310) of the SAME run there
is no call that can reach `synthesizeFromConst` **iff the run reaches the
read through `machine? = none`** (front end off, or `machineShape?` declines
the entry constant). Then the read returns the empty map: the miss holds for
the entry's own name and for every name.

If `machineShape?` ACCEPTS and `synthesizeMachineCertified` returns `none`
(5239: `closeLets` fails; or a closing returns `none`), the run falls through
to the read after the harness and after the children were synthesised and
written (each under its own name). Whether `declName` itself can be among
them is the by-name-cycle question of §1c: not decidable by the frame, not
proved. That case is OUTSIDE `outer_miss`. The legacy entry theorems already
carry the premise that excludes it (`hmach : ∀ projs, machineShape? false []
(.defnInfo dv) projs = none`).

Proved (written, not built):

* `outer_reset_reaches` (`Tools/ShippingMemoLaws.lean`): a returning run of
  `synthesizeCombinationalCore declName [] false` from `L.dval w = 0`,
  `L.quiet w` reaches `synthesizeFromConst … (entryConst …)` in a world `w3`
  with `L.mval w3 = {}`. `memoSet` at the reset, `memoFrame` eleven times.
* `legacy_entry_walk_at` (`Tools/ShippingLegacySemMemoWalk.lean`): the
  `RunsTo` counterpart of the prefix of `legacy_entry_walk_in` — the gates,
  the machine gate (five program shapes, as in the built walk), the read at a
  world `wr` with `L.mval wr = L.mval w`; after the read the continuation is
  handed to the existing walk by `RunsTo.mreturns` (no heap fact is needed
  after the read).
* `outer_miss`: the read of this run returns a map with no entry.

## 4. `proj_entry_output` without `MemoHit` at the outermost entry

`proj_entry_output_at`: the old statement for a `RunsTo` run, first disjunct
`(L.mval w).get? declName = some (m, d)` (THIS run's start world) instead of
`MemoHit`. `proj_entry_output_miss`: no disjunct given `(L.mval w).get?
declName = none`. `proj_entry_output_outer`: for `RunsTo
(synthesizeCombinationalCore declName [] false) … w (m, d) w'`, no disjunct.

The bridge "after the read only `MReturns` is available": none is needed
beyond `RunsTo.bind` (the prefix) and `RunsTo.mreturns` (the continuation
from the post-read world is a `RunsTo`, hence an `MReturns`); the old walk's
steps are repeated on it.

**Premises of `proj_entry_output_outer` beyond the old ones — two kinds, and
the second is NOT "the boundary":**

1. the boundary: `L : RefLawsM mref cref`, `L.dval w = 0`, `L.quiet w`;
2. `EntryConstIs mctx mref cctx cref declName dv` — the entry constant of
   this run is `.defnInfo dv`. The old theorem is about `synthesizeFromConst`
   on a GIVEN constant; the entry reads the declaration, so a statement about
   the entry needs the link. It is a reflection premise in the style of
   `EnvDefines`; `entryConstIs_of_reads` derives it from "every read of the
   declaration returns `.defnInfo dv`" and "no gate accepts the unfolding".
   For the same reason `mixed` is asked for the instance predicate of the
   environment the run read (the old one is for a caller-chosen `isInst`).

So "premises = the old ones + the boundary, nothing else" holds literally for
`proj_entry_output_miss` (old + `L` + the start-world miss) and NOT for
`proj_entry_output_outer`, which adds `EntryConstIs`.

## 5. The nested hit — statements only (`Tools/ShippingMemoInv.lean`)

A nested run does not start with a reset. Nothing here reuses the reset-miss.

**The invariant as worded is not true / not well-formed.** "Every entry `n ↦
(m, d)` was returned by a run of `synthesizeFromConst … n …` for which the
entry theorem's conclusion holds":

* the conclusion is about a constant (and an instance predicate); the key is
  the name. A stored entry is about the constant its storing run was handed
  (§1c.2). For the reader's constant it is false unless both runs read the
  same constant and environment — not a law;
* at the end of a non-shipping outermost run the memo holds an entry written
  outside the nested configuration (§1c.3).

**The weakest true form** (defined): `MemoInv L Φ w := ∀ n r, (L.mval w).get?
n = some r → Φ n r` with `Φ := stored Ψ`, `stored Ψ n r := ∃ ci isInst, Ψ n
ci isInst r` — the meaning `Ψ` holds for SOME constant and predicate. Proved
generically (from the memo's laws alone): `memoInv_of_empty`,
`memoInv_reset`, `memoInv_same`, `memoInv_frame`, `memoInv_read`,
`memoInv_write` (a write of a result satisfying the predicate keeps it),
`memoInv_hit`.

**Preservation obligations, per arm** (`ArmObligations L Ψ`, a structure of
statements; none proved), in the nested configuration:

* `certified`, `mixed`, `machine`: the arm's harness from an invariant world,
  on a constant its gate accepts, returns a result with `Ψ` and ends in an
  invariant world;
* `machineNone`: the machine arm declining after its harness ran leaves the
  invariant (the fall-through to the read);
* `legacy`: on a constant the three gates decline, a run that started with no
  entry under its name returns a result with `Ψ`;
* `legacyKeeps`: that run ends in an invariant world.

For `Ψ` = the projection class's statement ("for every `dv` with `ci =
.defnInfo dv` and every binder list / field / leaf function satisfying the
premises of `proj_entry_output` for `isInst`: the output statement"), the
three certified arms are vacuous (their gate accepting contradicts the
premises `old` / `mixed` / `hmach`), and `legacy` is `proj_entry_output_miss`.
What is left open is the invariant's transport THROUGH the arms' bodies (the
translator, the harness, nested children — every outcome): `MemoSound`.

**What a hit then gives, and the missing statement.** Under `MemoInv L
(stored Ψ)` at the read, a hit on `declName` gives `∃ ci' isInst', Ψ declName
ci' isInst' (m, d)` — the statement for the STORING run's constant. To state
it for the reader's `dv` one needs `ci' = .defnInfo dv` and `isInst' =
isInst`:

> (missing) *Constant stability inside one depth-0 run*: if two runs of the
> entry on `n` in the same depth-0 run read `ci₁, env₁` and `ci₂, env₂`, then
> `entryConst true false [] ci₁ (instancePredicate env₁) (userInliner env₁)
> (structEnv env₁) = entryConst … ci₂ …` and `instancePredicate env₁ =
> instancePredicate env₂`.

It needs a frame of the ENVIRONMENT (the `env` field of the Core state behind
`cref`) over everything a synthesis does — no such law exists, and the
translator's Lean primitives (`whnf`, `inferType`, …) write the Core state.

**The compiler change that would make the literal invariant true** (not
made): key the memo by what determines the result — at least `(declName,
parameters, symbolicMode, certifiedFrontEnd)`, and to remove the stability
premise, the constant handed over (or its hash) and the instance predicate's
environment. Alternatively delete the read (§1c, observation).

## 6. Not done, unverified, build order

**Not done** (exact statements):

1. The other entry theorems (`tuple_entry_output`, `fst_entry_output`,
   `one_binder_entry_output…`, `list_entry_output`, `useDbl_output`, the
   instances): each needs its `_at` form (proof = the old proof with
   `legacy_entry_walk_start` in place of `legacy_entry_walk_in`) and then
   `_outer`. Only the projection class is done.
2. The machine-arm fall-through: `∀ …, machineShape? false [] ci projs = some
   shape → RunsTo (synthesizeMachineCertified … declName shape) … w none w' →
   (L.mval w).get? declName = none → (L.mval w').get? declName = none`. False
   in general unless by-name cycles are excluded; no statement of
   "acyclic" exists.
3. The full entry: `outer_*` are about `synthesizeCombinationalCore declName
   [] false` (what the machine-route endpoints use), not about
   `synthesizeCombinational` (core + zero-width cleanup + checked merge).
4. `MemoSound`, `ArmObligations`, constant stability (§5).
5. An every-outcome version of `memoFrame` (the laws are for successful runs:
   enough for §3–§4, not for `KeepsMemo`).
6. Nothing relates `RefLawsM` to the runtime (as for `RefLaws`).

**Unverified steps, most likely to fail first:**

1. `legacy_entry_walk_at`: the five `first` alternatives of the machine-gate
   prefix in `RunsTo` form (copied shape for shape from the built
   `legacy_entry_walk_in`; `runsTo_pure` on a `match none with …`; the
   `rw [ey2, ey]` world rewrites; which alternative fires is not known to
   me); the `cases hget` placed before the existential is refined.
2. `outer_reset_reaches`: the count and order of the fifteen binds before the
   `try` (taken from the built `core_keeps`: 2 `pure`, 4 `set` — the fourth
   is the reset —, the child cache's `set`, 7 `set`, the depth's `set`); the
   unification of each step with `ST.Ref.set r v`; `hz` (`(d == 0) = true`).
3. `structure RefLawsM … extends RefLaws mref cref` (a parent declared under
   section variables; `L.dval`, `L.quiet`, `L.toRefLaws.sameQ`); the `HEq`
   between refs of different element types in `MemoFrameOp.otherSet`.
4. `get?_empty` (`simp` on `({} : Std.HashMap _ _).get? n`);
   `memoInv_write` (`Std.HashMap.get?_insert`, `split`, as in the built
   `cacheInv_insert`).
5. `entryConst_legacy_kept` (`unfold`, `split`, `rw`, `rfl` on a Boolean
   `if`); `entryConstIs_of_reads`.
6. `outer_miss` / `proj_entry_output_outer`: `rw [hconst …] at hrun` (the
   entry constant must be syntactically the one of `outer_reset_reaches`);
   `subst e` with `e : memo = {}`.
7. `ArmObligations` (statements only: argument types of the three harnesses).

**Build queue** (in order; each depends on the previous):

1. `Tools.ShippingMemoLaws` (imports `Tools.ShippingChildRun`)
2. `Tools.ShippingMemoInv`
3. `Tools.ShippingLegacySemMemoWalk` (imports 1 and
   `Tools.ShippingLegacySemProj`)
4. `Tools.ShippingLegacySemMemo` (doc comment changed; no dependents)
5. `Tests.Compiler.LegacySemMemoTest` (axiom audit; throws on a non-standard
   axiom)

`lakefile.lean` lines requested (not added by the worker):

```lean
lean_lib «Tools.ShippingMemoLaws» where
  roots := #[`Tools.ShippingMemoLaws]

lean_lib «Tools.ShippingMemoInv» where
  roots := #[`Tools.ShippingMemoInv]

lean_lib «Tools.ShippingLegacySemMemoWalk» where
  roots := #[`Tools.ShippingLegacySemMemoWalk]
```

and, in `Tests/AllTests.lean` (integrator's file): `import
Tests.Compiler.LegacySemMemoTest`.

## 7. Trust base extension

Every theorem of `Tools/ShippingMemoLaws.lean`,
`Tools/ShippingLegacySemMemoWalk.lean` and `Tools/ShippingMemoInv.lean` that
takes `L : RefLawsM mref cref` is stated under the following assumptions IN
ADDITION to those of `RefLaws`. Each is **ASSUMED — not proved against the
runtime; there is no runtime model.**

| # | Assumption | Where | Status |
|---|---|---|---|
| 1 | `mval`: the memo has a value in each world, a function of the world | `RefLawsM.mval` | ASSUMED |
| 2 | `memoGet`: a successful `sparkleSubModuleCache.get` returns `mval w` and leaves it | `RefLawsM.memoGet` | ASSUMED |
| 3 | `memoSet`: after a successful `sparkleSubModuleCache.set v`, `mval` is `v` | `RefLawsM.memoSet` | ASSUMED |
| 4 | `memoModify`: after a successful `sparkleSubModuleCache.modify f`, `mval` is `f` of the old value | `RefLawsM.memoModify` | ASSUMED (used only by the invariant lemmas of §5) |
| 5 | `distinct`: each of `sparkleChildCache`, `sparkleSubInstanceOutputs`, `sparkleSingleOutInstanceCache`, `sparkleFvarValueMap`, `sparkleWireWidthCache`, `sparkleLetWireCache`, `sparkleLoopWireCache`, `sparkleWireCanon`, `sparkleSynthDepth` is not the memo (`¬ HEq r sparkleSubModuleCache`) — i.e. distinct `initialize … ← IO.mkRef` declarations allocate distinct cells | `RefLawsM.distinct`, `MemoOther` | ASSUMED (not provable in the logic; `sparkleChildCache` has the memo's own type) |
| 6 | `memoFrame`, `otherSet`: a successful `set` of one of those nine refs — given it is not the memo — leaves `mval` | `MemoFrameOp.otherSet` | ASSUMED |
| 7 | `memoFrame`, `constInfo`: a successful `getConstInfo n` leaves `mval` | `MemoFrameOp.constInfo` | ASSUMED |
| 8 | `memoFrame`, `env`: a successful `getEnv` leaves `mval` | `MemoFrameOp.env` | ASSUMED |
| 9 | the laws hold for runs over these state references in every Meta and Core context (as in `RefLaws`) | all fields | ASSUMED |

Used from `RefLaws` itself by `outer_reset_reaches` (already in the trust
base, listed for completeness): `frame` / `frameQ` for `IO.getEnv`, `diag`
for the profile logger in a quiet world, `depthGet`. World-level premises of
the outermost theorems: `L.dval w = 0` (the run starts at synthesis depth 0)
and `L.quiet w`.

NOT assumed: anything about the memo's content (no "a stored result is
correct", no "a read misses"); a frame for the memo's own operations, for a
callback, for the translator or a harness, for a diagnostic operation, or
for any ref outside the nine; that aliasing refs do not interfere (the nine
are named, and their distinctness is assumption 5, not a consequence).
`RefLaws.frame` is not used as memo-invariance anywhere: its class `Framed`
contains the memo's own `set` / `modify` (§1a).

Not part of the boundary, but a premise the outermost theorem adds:
`EntryConstIs` (§4) — a reflection of the environment, not a heap law.

The joint satisfiability of `RefLawsM` (with `RefLaws`) by the real runtime
is not established, and no theorem here claims it.

**This extends the trust base. It is not a completion of the general
theorem**: the memo disjunct is removed for ONE class (projections, 45
declarations fitting by census) at the OUTERMOST entry only, under the
assumptions above, for runs that reach the read through `machine? = none`;
the nested hit is stated, not proved.
