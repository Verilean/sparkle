# B — class (c), pieces 2–5: the chain STOPS at piece 2 (round par/b-37)

Branch `par/b-37` from `4ca97548`. **No Lean file was written in this round**
and nothing was run. This document is the round's deliverable: why piece 2
cannot be completed from the material that exists, the exact statement that
is missing, and what was read for the later pieces (not started). Marks:
[R] read (file:line at 4ca97548), [P] predicted, [?] not known.

The instruction was: deliver each piece complete before the next; if one
cannot be completed, stop and say exactly what is missing rather than put a
hypothesis in its place. Pieces 3, 4, 5 are therefore NOT started.

## 1. Piece 2 as asked

"The generic instance-entry statement with the child read from the returned
design, at the FULL entry (not the core, not one cycle, not a hand-pinned
child module)", from the S6 material and `runModuleH_comb_total`.

## 2. Why the S6 material cannot give it

### 2.1 The S6 theorems pin the child by a GLOBAL determinism premise

Every S6 instance contract is conditional on [R:
`Tools/ShippingInstanceEntrySoundness.lean` 322–329]

    def HardwareTagged (mn : Name) : Prop :=
      ∀ env, MReturns instArmEnv env → isHardwareModule env mn = true
    def SubSynthDefines (mn : Name) (mc : Module) (dc : Design) : Prop :=
      ∀ r, MReturns (childSynthEntry mn) r → r = (mc, dc)

and `MReturns` is [R: `Tools/ShippingEntrySoundness.lean` 82–85]

    def MReturns (m : MetaM α) (a : α) : Prop :=
      ∃ mctx mref cctx cref w w', m mctx mref cctx cref w = EST.Out.ok a w'

— existential over ALL contexts, ALL state references and ALL worlds. So
`SubSynthDefines mn mc dc` says: in every world whatsoever, the child
synthesis of `mn`, if it returns, returns the one pair `(mc, dc)`. That is
determinism of the child compile over arbitrary reference states. It is

* not a fact about THE run (`RunsTo … w (b, design) w'`): no run can
  discharge a statement about all other worlds;
* not in the goal's ALLOWED list (`Tools.ShippingFinalGoalCommand.allowed`:
  `RunsTo`, `MachineDefines`, `EntryDefines`, `ChildBnd`);
* by the integrator's own Finding I (commit e6f68394, "Determinism of
  compiles: REFUTED in general on a constructed state") not true in
  general. `childSynthEntry` reads `sparkleChildSynth` and, through
  `synthesizeChild`, `sparkleChildCache` [R: `Sparkle/Compiler/Elab.lean`
  5575–5579, 8877–8881]: a world whose cache holds another pair for `mn`
  returns that pair.

Where the premise sits [R]:

| S6 statement | lines | the pinned-child premise |
|---|---|---|
| `InstancePreserves` / `Instance1Preserves` / `InstanceNPreserves` / `InstanceGPreserves` / `ProjInstancePreserves` | `ShippingInstanceEntrySoundness.lean` 414, 879, 1427, 1846, 2536 | inside the definition: `HardwareTagged mn → SubSynthDefines mn mc dc → dc.modules = [] → mc.inputs = ports → mc.outputs = [⟨"out", .bitVector wOut⟩] → …` — the conclusion `m.body = [.inst mc.name …, .assign "out" …] ∧ d.modules = [mc]` is about the PINNED `mc` |
| `HierConePreserves` | `ShippingHierTermSoundness.lean` 609 | no pin itself, but asks `LeafContract children C … (vE j) …` for each instance leaf — the translator's contract on the call expression, which the tests obtain from the pinned form (`parentMix_entry_observes`, `ShippingHierarchySoundnessTest.lean` 866–869: `htagAll : HardwareTagged`, `hsub : SubSynthDefinesAll ``childAdd childModule dc`, `hdc`) |

So "the child read from the returned design" cannot be obtained by
INSTANTIATING an S6 theorem at the run's child: its hypothesis would have to
be proved for all worlds. It needs the instance arm re-proved in a form
that tracks the world of the run.

### 2.2 What tracks the world of a run exists — but not for this arm

* The child framework of the machine route [R: `Tools/ShippingChildInv.lean`
  440–603]: `RealChild mref cref c r` ("`r` is returned by a run of the
  real full entry on `c`, over these references, from a world where the
  cache's entries are `RealChild`s"), `InvW`, `StartW`, `ChildBnd`
  (the ALLOWED runtime boundary), `childSynthEntry_keeps`
  (`Tools/ShippingChildFallback.lean` 27). The machine parents get their
  children's `RealChild` witnesses through `MachineClosesAt`
  (`Tools/ShippingCallsGate.lean` 240, `machineClosesAt_of_gateKids`) —
  proved for the MACHINE route's closing (`closeInsts`), a different code
  path from the mixed gate's instance arm.
* Worker A's world-level calculus over `CompilerM` [R:
  `Tools/ShippingWalkStill.lean` 72–148, 530–638]: `WHo` / `WSt`, one lemma
  per builder operation, `walk_still` for the fragment `wfrag` (inputs,
  literals, binary, compare, Bool operations, mux, setw, concat). Its
  invariant keeps the child-cache VALUE fixed (`mb`). The instance arm is
  outside the fragment — and it is exactly the operation that CHANGES the
  cache (`synthesizeChild` inserts the child's result).
* The instance arm itself, as an explicit bind chain [R:
  `instanceUncached_run`, `ShippingInstanceEntrySoundness.lean` 375–404]:
  `instAddModules`, `instRegisterChild`, `instClkRst`, `instArityCheck`,
  `instArgs rec …`, the single-out dedupe cache read
  (`instArmCacheGet`), `makeWire`, `instArmCachePut`, `freshName`,
  `instLinkCheck`, `emitInstance`. S6 analyses it with `Returns` /
  `MReturns` (no worlds).

### 2.3 The missing statement (piece 2, exactly)

For a declaration `f` whose entry value peels to an instance root or a cone
over instance leaves (the premises of `instanceN_entry_of_env` /
`hierCone_entry_of_env`, with `EntryDefines` in the place of `EnvDefines`):

    theorem gate_parent_run
        (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
        (entry : EntryDefines mctx mref cctx cref f value)
        (old …) (hscalar …) (peel …) (the term's well-formedness) :
        ChildBnd mref cref w →
        ∃ (M : Module) (kids : List (Name × Res)),
          (b = dropZeroWidthModule M ∨ b = mergeChecked (dropZeroWidthModule M)) ∧
          -- every call's child is a real full-entry run over these references
          (∀ c y, (c, y) ∈ kids → RealChild mref cref c y ∧ y.2.modules = []) ∧
          -- the returned design holds exactly those children's modules
          design.modules = kids.map (·.2.1) ∧
          -- the core module is the S6 shape over THOSE modules
          (the conclusion of InstanceNPreserves / HierConePreserves with
           `mc := y.1` and `children := childMap design.modules`)

Without the `HardwareTagged` / `SubSynthDefines` premises: the tag is read
from the run's own environment (`EntryDefines`-style reflection of the
child, an ALLOWED premise per child, as `GateRun` carries it), the child
from the run's own nested synthesis.

To prove it, three things are needed that do not exist:

1. **World-level lemmas for the instance arm's operations** in the style
   of `WHo` / `Keeps`: `instArmEnv`, `childSynthEntry` (exists:
   `childSynthEntry_keeps`, to be strengthened to RETURN the `RealChild`
   witness of what it returned — under `InvW` a cache hit is a `RealChild`
   by `CacheAt`, a miss is the run itself), `instAddModules`,
   `instRegisterChild`, `instClkRst`, `instArgs`, `instArmCacheGet/Put`,
   `instLinkCheck`, `emitInstance`.
2. **A calculus whose invariant lets the child cache GROW** (`WHo` fixes
   the map `mb`): before/after maps with `mb ⊆ mb'` and `CacheInv mb'`.
   For one call this is a single step; for `parentTwoCalls` /
   `parentRepeat` / `parentNested` the second call must find the first
   call's entry (a hit) — the "later call of a declaration is a cache hit
   of the entry the earlier call left" argument the machine route has as
   `synthesizeChild_pin` (`Tests/Compiler/ShippingCallsCloseTest.lean` 226).
3. **The S6 shape proof redone against that calculus**: the ~230 lines of
   `synthesizeMixedCertified_instanceN_sound` (1462–1690) and the cone's
   `LeafContract` for a call leaf, with "the pair the nested synthesis
   returned in this run" where they use the pinned `(mc, dc)`.

And for the FULL entry [R: `Sparkle/Compiler/Elab.lean` 5547–5561]: the
entry cleans only the top module (`top f d` maps `f` over the design's
modules NAMED like the parent, so the children are untouched — provided no
child has the parent's name, a `ModuleName.ofDecl` injectivity fact,
`Tools.ShippingModuleName.ofDecl_ne`). On a body with an instance:

* `dropZeroWidthModule` [R: `Sparkle/IR/ZeroWidth.lean` 91–118] keeps an
  `.inst` statement and rewrites its connections by `dzExpr`; it is the
  identity only if `allConcrete` fails or no wire has width 0 and `dzExpr`
  fixes the connection expressions. `dropZeroWidth_typed`
  (`Tools/ShippingTypedPostSoundness.lean` 271) proves the identity for
  `TypedPostReady` modules, whose statements are all assignments
  (`h.typed`): NOT applicable to an instance body. A new lemma is needed
  (piece 2, small, but its premise — the widths of the parent's wires — is
  a fact of item 3 above, so it cannot be stated usefully before it).
* `mergeChecked` [R: `Sparkle/IR/RefineCheck.lean` 260–275] on a body that
  is not assignment-only returns the merge only behind `refineCheck ∧
  masksKept ∧ printOk ∧ ¬ all isAssign`, else the module:
  `mergeChecked_cases` (280) gives the disjunction; which side is taken for
  an instance body is decided per module [?].

I did not write items 1–3: they are a proof unit of the size of worker A's
`ShippingWalkStill` (one lemma per operation plus the walk), over compiler
code I can read but not run, and their statements depend on the shape of a
calculus (item 2) that worker A is still extending for `mixDeep`. Writing
them blind would produce a large file with no evidence that any line holds.

### 2.4 What would NOT be honest

* `gate_parent_run` with `SubSynthDefines` kept as a premise: a NOT ALLOWED
  antecedent that is false in general — an open form that can never be
  closed in that shape.
* Starting piece 3 or 4 over a hypothesis "the children are `RealChild`s":
  the instruction excludes it.

## 3. Read for the later pieces (NOT started; for whoever continues)

**Piece 3 — the optimizer on a body with an instance** [R:
`Sparkle/IR/RefineCheck.lean` 387–401]. `checkedOptimize m`:

    simpleBody m            → optCheck ∧ assignmentOrderCheck ? o : m      (false here: an inst is not simple, OptCheck.lean 133–136)
    m.body.all seqStmtOk    → refineCheck ∧ printOk ? o : m                (false here: seqStmtOk rejects inst)
    hierBinds m             → hierRefineCheck m (deinline m o) ? deinline m o : m
    hierGate m              → m
    otherwise               → o        (the optimizer's output, UNCHECKED)

So for a gate-route parent three outcomes are possible and which one is
taken is decided per module today; existing lemmas: `checkedOptimize_binding`,
`checkedOptimize_not_binding`, `checkedOptimize_facts`
(`Tools/ShippingGuardsSound.lean` 291–328), `checkedOptimize_inst_iff`
(`ShippingChecksDerived2.lean` 72), `checkedOptimize_inst_iff_gate`
(`ShippingChecksDepthGate.lean` 33), `checkedOptimize_inputs`
(`ShippingHierShipsSV.lean` 34). What piece 3 would have to prove from the
run: `hierBinds b = true ∨ hierGate b = true` for the S6 shapes (so the
last, unchecked branch is never taken) — a statement about the SHAPE of
`b`, i.e. after piece 2.

**Piece 4** — the generic text theorem is
`Tools.ShippingHierSVRunH.linked_sv_of_runH` (193), fed by
`Tools.ShippingHierRunTotal.runModuleH_comb_total` (round b-36, NOT BUILT
at the time of writing); the children's closed runs are `c.gate_design0` /
`c.gate_design0S`, which are statements about a run of the CHILD's full
entry — connected to the parent's design only through the `RealChild`
witness of piece 2.

**Piece 5** — `#gate_child`'s reader (`unq`) reads no call; the reflected
data of a parent would be the S6 `quote dom bE vE e` with instance leaves
(`instEN`), which `mixedGatePeel` already yields.

## 4. How far the chain got

| piece | status |
|---|---|
| 1 (b-36) | written, not built: `runModuleH_comb_total` |
| 2 | NOT completed. Exact missing unit: §2.3 items 1–3 (a world-level treatment of the mixed gate's instance arm with a growing child cache, returning `RealChild` witnesses) and the two post-processing facts on instance bodies |
| 3, 4, 5 | not started (by instruction) |

No lean_lib line, no build order, no prediction of a measurement: there is
no new file.

## 5. Could not be determined by reading

* Whether worker A's calculus (`WHo`) is meant to be extended to a growing
  cache, or whether the `mixDeep` route (HarnessStill / EntryStill /
  outermost runs) will provide the instance arm differently — the two
  efforts need the SAME lemma ("a nested child synthesis in a run under
  `ChildBnd` returns a `RealChild` and leaves `InvW`"), and it should be
  written once.
* Which side of `mergeChecked_cases` and which branch of `checkedOptimize`
  the eight probe declarations take (the b-36 probe logs the compile, not
  these branches; two lines in the probe would measure it:
  `hierBinds b`, `hierGate b`, `mergeChecked b == b` on the returned
  module — I did not add them because the probe file is not built yet and
  is staged unchanged).
* Whether a child of a gate-route parent can ever have the parent's module
  name (the `top` map of the full entry).

---

# Continuation (same round, after the integrator's decision): the growing-cache calculus and the arm's child synthesis

**WRITTEN, NOT BUILT.** Nothing was run. The chain now stands at: item 1 of
§2.3 written; item 3 (the S6 shape proof against the calculus) NOT started
— its exact statement is in §8.

## 6. Files

| file | commit | what |
|---|---|---|
| `Tests/Compiler/SlotlessParentProbeTest.lean` | the small separate commit | three more values in the COMPILE line: `hierBinds b`, `hierGate b`, `mergeChecked b == b` on the returned module (droppable if b-36 needs fixes) |
| `Tools/ShippingWalkGrow.lean` (new) | the calculus commit | `WG` and its rules; `childSynthEntry_post`; `WG.child`; `WG.child_hit` |

`lakefile.lean`:

    lean_lib «Tools.ShippingWalkGrow» where
      roots := #[`Tools.ShippingWalkGrow]

Build order: `Tools.ShippingWalkGrow` alone (imports the BUILT
`Tools.ShippingCacheCoherentCert`, `Tools.ShippingChildFallback`,
`Tools.ShippingWalkStill`). No test file: every statement is general.

## 7. Statements (`Tools/ShippingWalkGrow.lean`)

    def WG L D ctx (P : HashMap Name Res → Prop) (c : CompilerM α) (Q : α → HashMap Name Res → Prop) : Prop :=
      ∀ st w p w', InvV L w → L.dval w = D → P (L.val w) → RunsTo (c ctx st) mctx mref cctx cref w p w' →
        InvV L w' ∧ L.dval w' = D ∧ SubMap (L.val w) (L.val w') ∧ Q p.1 (L.val w')

* `WG.pure`, `WG.bind`, `WG.conseq`, `WG.lift` (a lifted `MetaM` action).
* `WG.frame`: a predicate `R` of the cache with `SubMap m m' → R m → R m'`
  is carried across any action; instances `WG.grow mb` ("the cache only
  grows from `mb`", the form asked) and `WG.keepEntry k y` ("the entry `k ↦
  y` survives").
* `WG.ofKeeps`: `(∀ L' st, Keeps (J L' D) (c ctx st)) → WG L D ctx P c (fun _ _
  => True)` — invariant, depth and `SubMap` from the BUILT `@[keeps]` lemmas
  (the witness's auxiliary predicate set to `SubMap (L.val w)`, the device
  of the built `child_sub`).
* `WG.withReturns`: adds a world-free fact of the result from a
  `Returns`-level lemma (a run is a `Returns`) — the door to the S6 lemmas.
* `WG.ofStill`: `(∀ L' st, Keeps (J L' D) (c ctx st)) → (∀ mb, WHo L mb ctx c Q0)
  → WG L D ctx P c (fun a m => P m ∧ Q0 a)`.
* `childSynthEntry_post L hB (hw : InvV L w) (hd : L.dval w ≠ 0) (hr : RunsTo
  (childSynthEntry c) … w y w') : RealChild mref cref c y ∧ InvV L w' ∧ L.dval
  w' = L.dval w ∧ SubMap (L.val w) (L.val w') ∧ (L.val w').get? c = some y ∧ ∀
  y0, (L.val w).get? c = some y0 → y = y0`.
* `WG.child hB (hD : D ≠ 0) c : WG L D ctx P (CompilerM.liftMetaM
  (childSynthEntry c)) (fun y m => RealChild mref cref c y ∧ m.get? c = some y)`.
* `WG.child_hit hB hD c y0 : WG L D ctx (fun m => m.get? c = some y0)
  (liftMetaM (childSynthEntry c)) (fun y m => y = y0 ∧ RealChild … c y ∧
  m.get? c = some y)` — item 2's argument: the first call's entry is kept
  by `WG.keepEntry`, the second call is a hit of it.

`hB : ∀ L', BodyRel L'` is the PROVED `bodyRel`
(`Tools/ShippingChildBody.lean`), the premise the built `child_ok` /
`synthesizeChild_post` take.

### Two departures from the form asked, and why

1. **The transfer `WSt → WG` needs a second premise.** `WHo` says nothing
   about the synthesis DEPTH, and growth across a child synthesis is
   `child_sub_runs`, which asks `L.dval w ≠ 0` (at depth 0 the entry clears
   the cache). So the depth is in `WG`'s invariant and a still lemma alone
   does not transfer. `WG.ofStill` takes the still lemma AND the action's
   `Keeps (J L' D)` fact. That fact exists for every translator operation
   (the 76 `@[keeps]` lemmas behind `bodyRel`, including the instance arm's
   `instArgs_keepsC`, `instAddModules_keepsC`, `instClkRst_keepsC`,
   `instOutWires_keepsC`, `translateInstanceOrFallback_keepsC`), so nothing
   is lost — but each use site names two lemmas. In fact `WG.ofKeeps` alone
   already gives invariant + depth + `SubMap` for ALL of them; `WHo` adds
   only "the value is unchanged", which `WG` does not need.
2. **Pre/postconditions on the cache** instead of one fixed `mb`: needed to
   say "the result is an entry of the END cache" and to make a later hit
   provable.

So item 1 ("world-level lemmas for the instance arm's operations") is: the
invariant side of EVERY arm operation by `WG.ofKeeps` from the built keeps
lemmas; the one operation with a world-dependent RESULT, the child
synthesis, by `WG.child` / `WG.child_hit`.

## 8. Where it stops: item 3, and its exact statement

How S6 uses the pin [R]: in each of the five monolith proofs the pinned
child enters ONCE, as a rewrite of the nested synthesis's result
(`rw [hsub sub hSubM] at tr`, `ShippingInstanceEntrySoundness.lean` 481,
942, 1494, 1917, 2641), where `sub` is the witness of a `Returns.bind`
(existential, no world) for `CompilerM.liftMetaM (childSynthEntry mn)` in
`translateInstanceOrFallback` [R: `Sparkle/Compiler/Elab.lean` 8671–8684:
`let sub ← liftMetaM (childSynthEntry mn); match sub.1.outputs with |
[singleOut] => translateControlCachedWith (translateInstanceUncachedWith rec
mn sub.1 sub.2 singleOut) e hint top named`].

To put the run's child there, the decomposition down to that bind has to be
done at `RunsTo` level, so that the SAME `sub` is the one `WG.child` speaks
of. The next statement (for the N-ary root, the shape of `parentUse`,
`wrapAdd`, `wrapPick`):

    theorem instanceN_arm_grow (hB : ∀ L', BodyRel L') (hD : D ≠ 0)
        (hrecK : the recursive translator keeps J — the hypothesis of translateInstanceOrFallback_keepsC)
        (htag : in the run's environment mn is a hardware module)   -- see "the tag" below
        … (the non-`pure` / non-binary / fallbackKind premises of instanceN_step) :
        WG mctx cctx L D ctx P
          (translateInstanceOrFallback rec (instEN mn lvls dF argsF) hint top named)
          (fun wire m => ∃ y : Res, RealChild mref cref mn y ∧ m.get? mn = some y ∧
             ArmShape rec mn y.1 y.2 (instEN mn lvls dF argsF) hint top named wire)

where `ArmShape …` is the `Returns`-level conclusion S6 proves AFTER the
rewrite, with `(mc, dc) := y` — i.e. `Returns (translateControlCachedWith
(translateInstanceUncachedWith rec mn y.1 y.2 so) e hint top named) ctx s
wire s'` for the single output `so` of `y.1`. With it, the remainder of
`synthesizeMixedCertified_instanceN_sound` (1495–1690) applies verbatim to
`y` (it never looks at `hsub` again), and `gate_parent_run` follows by the
harness shell (`harnessStill_frag`'s `bind_S` / `emitLeaves_S` /
`finishSynth_world` redone with `WG.ofKeeps`) and the full entry
(`full_split`, `Tools/ShippingCacheCoherentRun.lean` 312, already gives the
core run and the unchanged cache for the post passes).

Proof plan of `instanceN_arm_grow`: unfold `translateInstanceOrFallback` at
the constant head (`instEN_getAppFn`); `WG.bind` of `WG.lift` for
`instArmEnv` with `WG.child`; then the `match sub.1.outputs` continuation
by `WG.ofKeeps` (from `translateInstanceOrFallback_keepsC`'s components)
plus `WG.withReturns`.

What I could not settle by reading, and why I stopped rather than write it:

* **the tag.** `HardwareTagged mn` is also a global (`∀ env, MReturns
  instArmEnv env → …`). At world level the arm reads `instArmEnv =
  Lean.getEnv`; the fact "this run's environment tags `mn`" must come from
  an ALLOWED premise. I did not find a lemma "the reflection of the child
  (`EntryDefines c v`) → the run's environment tags `c`"; the S6 tests take
  the tag as a separate hypothesis `tag : ∀ wE e wE', RunsTo getEnv mctx
  mref cctx cref wE e wE' → isHardwareModule e c = true`
  (`ShippingHierarchySoundnessTest.lean` 259), which IS about this run's
  contexts but is not in the ALLOWED list. This needs a ruling: either the
  classifier admits the tag premise in that `RunsTo getEnv` form (a
  reflection of the environment, of the same kind as `EntryDefines`), or
  `EntryDefines` is strengthened.
* **`translateControlCachedWith`** (the validated cache wrapper around the
  uncached arm): its still lemma exists (`controlCached_S`,
  `ShippingWalkStill.lean` 237) for a `lower` that is still. Whether it
  applies as is to this `lower` depends on its hypothesis' exact form,
  which I did not read.
* **the environment read**: which `Framed` / `Op` constructor covers
  `instArmEnv` (a `getEnv`).

These are three lookups plus about 250 lines of proof against S6's text;
they are the next unit. I did not start it: a half-written
`instanceN_arm_grow` would be the "hypothesis in its place" the instruction
excludes.

## 9. Risks of `Tools/ShippingWalkGrow.lean` (PREDICTED failure points, in order)

1. `WG.ofKeeps`: the anonymous constructor `⟨hw, hd, sub_refl _⟩` for
   `J (L.withAux …) D w` relies on `InvV (L.withAux A hA) w` and
   `(L.withAux A hA).dval w` reducing definitionally (the built `child_sub`
   uses the same term with `rfl` in the middle).
2. `childSynthEntry_post`: after `unfold childSynthEntry at hr`, that
   `RunsTo.bind hr` sees a `>>=` (the built `childSynthEntry_keeps` unfolds
   the same definition and applies a bind rule), and that `hrest` is
   accepted as `RunsTo (synthesizeChild c) …` after `subst` (a `match` on
   `some synthesizeChild`).
3. `WG.withReturns`: `⟨mctx, mref, cctx, cref, w, w', hr⟩ : Returns c ctx st
   p.1 p.2` needs `p = (p.1, p.2)` by eta.
4. `WG.ofStill`: the two `rw [hv]`.

## 10. How far the chain got

| piece | status |
|---|---|
| calculus `WG` + structural rules + transfers | written, not built |
| item 1 (arm operations at world level; the child synthesis returns a `RealChild` that is an entry of the end cache; a repeated call is a hit) | written, not built: `WG.ofKeeps` + built keeps lemmas; `childSynthEntry_post`, `WG.child`, `WG.child_hit` |
| item 2 (growing cache across calls) | the rules are there (`WG.keepEntry` + `WG.child_hit`); not yet USED by any arm lemma |
| item 3 (S6 shape against `WG`) | NOT started; exact next statement and three open lookups in §8 |
| the two full-entry facts, `gate_parent_run`, pieces 3–5 | not started |

---

# Second continuation: the tag, by the route reading — and where it STOPS (a boundary finding)

**WRITTEN, NOT BUILT.** Nothing was run. Ruling received: no new ALLOWED
premise, `EntryDefines` not strengthened; derive the tag from what the run
did; if the two environment reads cannot be related by a built law, stop and
report which law is missing. **They cannot. The chain stops here.**
`instanceN_arm_grow`, `gate_parent_run` and the two full-entry facts are NOT
started.

## 11. The answer on the environment reads

### 11.1 The first read, and what the route reading gives (written)

The entry reads the environment once [R: `core_reads_val`,
`Tools/ShippingCacheCoherentVia.lean` 163–177: `RunsTo getEnv … w5 envR w6`,
then `synthesizeFromConst … (entryConst … (instancePredicate envR) …)
(instancePredicate envR)`], and the mixed arm is taken with `isInst :=
instancePredicate envR` (`mixedCertifiedShape? false [] ci isInst = some (bs,
body)`, as in `sfc_mixed_val`, `Tools/ShippingHarnessStill.lean` 443).

`Tools/ShippingInstanceTag.lean` (new, pure):

    theorem instancePredicate_const (hfn : e.getAppFn = .const mn us)
        (h : instancePredicate env e = true) :
        isHardwareModule env mn = true ∨ (env.getProjectionStructureName? mn).isSome = true
    theorem unifiedInstanceRoot_isInst (h : unifiedInstanceRoot isInst kinds e = true) : isInst e = true
    theorem hierInstRoot_isInst       (h : hierInstRoot isInst kinds e = true)       : isInst e = true
    theorem root_tag (hfn : e.getAppFn = .const mn us)
        (h : unifiedInstanceRoot (instancePredicate envR) kinds e = true ∨
             hierInstRoot (instancePredicate envR) kinds e = true) :
        isHardwareModule envR mn = true ∨ (envR.getProjectionStructureName? mn).isSome = true

So for the two ROOT shapes the tag IN `envR` follows from the acceptance —
up to the predicate's own second disjunct [R: `Sparkle/Compiler/Elab.lean`
5374–5384]: `instancePredicate` is also true when the head is a structure
PROJECTION whose record argument is a tagged call. For an `instEN mn …` body
whose head `mn` is the child itself the right disjunct is excluded only by a
fact about `envR` ("`mn` is not a projection function"), which is again a
fact about the environment read — it is decidable per declaration in the
elaboration environment, but the run's `envR` is not that environment by any
theorem. (For `hierGateRoot`, the cone, the leaves are inside the body; the
corresponding lemma is an induction over `hierGateBoolBody` /
`hierGateBitsBody`, not written.)

### 11.2 The second read

The instance arm reads the environment AGAIN [R: `Elab.lean` 8675, `let env
← CompilerM.liftMetaM instArmEnv`; 8447: `def instArmEnv : MetaM Environment
:= Lean.getEnv`] and branches on `isHardwareModule env mn` (8676): tagged →
the child synthesis and the instance; not tagged → the projection arm or
the cached legacy translator (8684–8711). S6's shape proof needs the first
branch, so it needs the tag in THIS `env`.

Between the two reads the run performs: `getConstInfo`, the profile log,
the depth and cache ref operations, `synthesizeFromConst`'s prefix, the
harness (`bindMixedCertifiedInputs` under `withLocalDecl`, `emitLeaves`),
the translator's fuel steps down to the arm — and, for a later instance of
the same parent, complete nested child syntheses.

### 11.3 What the built material says about `getEnv` — everything I found

| where | what it gives | relates two reads? |
|---|---|---|
| `Framed.env : Framed (getEnv : MetaM Environment)` (`Tools/ShippingChildInv.lean` 207) with `RefLaws.frame` / `same` / `sameQ` | a `getEnv` leaves the three tracked VALUES (`val` cache, `sval` synthesis ref, `dval` depth) and quietness | NO — it is about what `getEnv` does to the refs, not about what it RETURNS |
| `RefLaws` (331–440) | tracked values `val`, `sval`, `dval`, `aux`, `quiet`; laws `cacheGet`, `cacheModify`, `synthGet`, `depthGet`, `frame`, `diag`, `frameT`, `excOk`, … | NO — there is no environment component and no law naming `Environment` (the only occurrence of the word is the comment on `excOk`: `OkEnv`, about printers) |
| `getEnv_ctx` (`Tools/ShippingReflectCtx.lean` 41) | a `getEnv` run in one pair of contexts is the same run in another, FROM THE SAME WORLD | NO — same world `w`; says nothing of a later world |
| `EntryDefines`, `MachineDefines` (`Tools/ShippingInlineSoundness.lean` 46–55; `ShippingMachineEntry`) | `∀ w1 ci w2 w5 envR w6, RunsTo getConstInfo … → RunsTo getEnv … w5 envR w6 → …` | they do not RELATE reads: they are stated for EVERY world's read. That is how the existing boundary copes with the question: the reflection is universally quantified over the worlds, so no constancy of the environment is ever needed — or proved |
| the machine route's instance reading (`MachineDefines … shape`, the shape contains the call entries) | the tag is inside the world-universal reflection of the SHAPE: in every world's environment the reader sees the calls as instances | same: world-universal premise, not a relation |
| S6 (`HardwareTagged`, the tests' `tag : ∀ wE e wE', RunsTo getEnv … wE e wE' → isHardwareModule e c = true`) | the tag as a separate world-universal premise | same |
| `core_reads_val` | names the entry's `envR` and its world `w5 → w6` | one read only |

`grep` of `Sparkle/Compiler/Elab.lean` for `addDecl`, `modifyEnv`, `setEnv`:
no occurrence. So by READING the compiler never writes the environment —
but that is my reading of one file, not a theorem, and the run also executes
Lean's own `Meta` operations (`withLocalDecl`, `whnf`, `inferType`,
`instantiateMVars`, the kernel's reduction in `machNorm`, …), of which
nothing built says that they leave `Core.State.env`.

### 11.4 The missing law (exactly)

    -- a fourth tracked value in the law bundle
    RefLaws.eval : Void IO.RealWorld → Environment
    RefLaws.envGet : ∀ {mctx cctx} w e w', RunsTo (getEnv : MetaM Environment) mctx mref cctx cref w e w' → e = eval w
    -- and `eval` in the frame laws: every operation class that is proved to
    -- leave `val`/`sval`/`dval` (`Framed`, `Diag`, `Throws`, `Op`, the cache
    -- and depth writes) also leaves `eval`

and, on top of it, `eval` carried through the `Keeps` proofs (`J` extended by
`L.eval w = E`): `bodyRel`, `legacyRel`, `childKeeps_all` and the 76
`@[keeps]` lemmas would each gain the conjunct. With that,

    tag at the arm  :=  root_tag at envR  +  envR = eval w5 = E = eval wX = env

A weaker law suffices for this use — "the hardware-module tag of every
constant is the same in the environment of any two worlds of one entry run"
— but it has the same shape and the same cost.

This is a change of the TRUSTED boundary (`RefLaws` is the bundle of laws
about the runtime the proofs assume: T-laws), in BUILT files I must not
edit, and its truth is a statement about Lean's `MetaM` primitives that no
proof in the tree addresses. It is a finding for the reviewer, not something
to supply as a hypothesis:

> **Finding (boundary):** no built law relates the values of two `getEnv`
> reads of one run. Every existing endpoint avoids the question by taking
> its reflections (`EntryDefines`, `MachineDefines`) for EVERY world. The
> gate-route parent is the first place where a fact read at the entry (the
> route was taken with `instancePredicate envR`) must be USED at a later
> read (`instArmEnv`), and it cannot be.

### 11.5 What would close it WITHOUT a new law (for the ruling; not done)

1. State the parent's reflection in the existing world-universal style for
   the READING the gate does: `∀ w5 envR w6, RunsTo getEnv … w5 envR w6 →
   mixedCertifiedShape? false [] (entryConst … ci (instancePredicate envR) …)
   (instancePredicate envR) = some (bs, body)` — the gate analogue of
   `MachineDefines` (whose `shape` already carries the calls). Then
   `root_tag` applies at the ARM's read directly. It IS a new premise form
   (ruled out as "strengthen `EntryDefines`"), though of exactly the kind
   `MachineDefines` already is for machine parents — I record it because it
   is the precise sense in which the machine route has the tag and the gate
   route does not.
2. Change the compiler to pass the entry's `envR` (or its predicate) to the
   arm instead of reading again — a compiler edit, outside a worker's scope.

## 12. The other two lookups (answered; nothing was built on them)

* **`controlCached_S`** [R: `Tools/ShippingWalkStill.lean` 237–253]:
  hypothesis `hlower : WSt … (lower e hint top named)` — the uncached
  lowering must be `WSt` (cache VALUE unchanged). For the instance arm
  `lower = translateInstanceUncachedWith rec mn sub.1 sub.2 so`: the child
  synthesis is BEFORE it, so by reading it does not touch the child cache,
  but its `WSt` proof does not exist (its operations — `instAddModules`,
  `instRegisterChild`, `instClkRst`, `instArgs`, the single-out cache,
  `instLinkCheck`, `emitInstance` — have `@[keeps]` lemmas, not `_S`
  lemmas, and `instArgs rec` recurses into the translator, which is `WSt`
  only on `wfrag`). So `controlCached_S` does not apply as is; the `WG`
  route is `WG.ofKeeps` from `translateInstanceOrFallback_keepsC`'s
  components (no `_S` lemma needed).
* **`instArmEnv`**: `unfold instArmEnv` then `Framed.env`
  (`Tools/ShippingChildInv.lean` 207) — refs and quietness kept by
  `L.same` / `invV_framed`, as for `synthGet` in `childSynthEntry_post`.

## 13. How far the chain got (final for this round)

| piece | status |
|---|---|
| calculus `WG`, child synthesis (`Tools/ShippingWalkGrow.lean`) | written, not built |
| the tag in the ENTRY's environment, for the two root shapes (`Tools/ShippingInstanceTag.lean`) | written, not built |
| the tag in the ARM's environment | **NOT derivable from built laws** — §11.4 |
| `instanceN_arm_grow`, `gate_parent_run`, the two full-entry facts, pieces 3–5 | not started |

`lakefile.lean` (in addition to §6):

    lean_lib «Tools.ShippingInstanceTag» where
      roots := #[`Tools.ShippingInstanceTag]

Builds alone (imports `Sparkle.Compiler.Elab` only). PREDICTED failure
points: `instancePredicate_const` — the `rw [hfn] at h` under the unfolded
`match e.getAppFn`, the `have h' … := h` (the `match` on a constant must
reduce by definitional unfolding, as the built `instancePredicate_instEN`
does with `show`), and the `simp at hp` in the `none` case.

## Integrator's build record (2026-10-13)

BUILT on poc 28adf9af + these files, cgrun 3 GiB swap 0; runs `backlog` (exit 0, peak 0.82 GB) and `backlog2`. `Tools.ShippingWalkGrow`: first attempt, as written.
`Tools.ShippingInstanceTag`: one error in `instancePredicate_const` (the restated `have h'` did not match
the reduced `match`); integrator fix: `dsimp only at h` then `rw [Bool.or_eq_true] at h`, no statement
changed. Probe (three new values), MEASURED for all eight (`parentUse`, `wrapAdd`, `parentMix`,
`parentTwoCalls`, `parentRepeat`, `parentCmp`, `parentNested`, `wrapPick`): `hierBinds b = true`,
`hierGate b = true` on the returned module (so `checkedOptimize` takes the checked-deinline branch).
STATE: the growing-cache calculus `WG` and the child-synthesis lemmas are theorems; the tag is derived in
the ENTRY's environment for two root shapes; the chain stops at the BOUNDARY FINDING (no law relates two
`getEnv` reads of one run) — `gate_parent_run` is not written; the class stays open pending a ruling.
