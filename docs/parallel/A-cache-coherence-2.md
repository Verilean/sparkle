# A: cache coherence, step (b) at the run level — round par/a-33

Base: `poc/roundtrip-proof` b7dc0ec4 (Finding H fixed at the compiler).
Branch `par/a-33`. **NOTHING here was built or run.** "READ" = the line was
read in the file named at b7dc0ec4; "PREDICTED" = concluded from READ lines;
every Lean file is WRITTEN, NOT BUILT. Line numbers:
`Sparkle/Compiler/Elab.lean` unless a file is named. Predecessor:
`docs/parallel/A-cache-coherence.md` (par/a-31), whose §1.2 counterexample
(two declarations, one module name) is what b7dc0ec4 removed.

## 0. Result in one paragraph

No counterexample to coherence was found in the current compiler for
kernel-checked declarations, and none is claimed absent by proof. Step (b)
is **NOT closed**. What changed: (1) the invariant that is actually
preserved is identified — `Prov` (provenance: an entry's module is named
after its key; every module of an entry's design is a built memory module or
the module of a cache entry) — and `Prov m → Coherent m` is a PURE theorem
whose only non-trivial input is the injectivity of module names; (2) the
premise `hE` of `synthesizeChild_coherent` is replaced by a strictly more
specific residual, `CoreFresh`, about the CORE entry's run; the post passes
and the insert are discharged; (3) from the EXISTING run laws alone
(`RefLaws`, `BodyRel`) it is shown that a run of the entry at positive depth
never removes, replaces or overwrites an entry that existed when it started
— on every outcome; (4) the machine route's own code (the closings,
`designWith`) is followed for `Prov`; the translator is not. The residual
has three parts (§3): result-level provenance through the translator (H1),
the recursion over nested children, and "a run does not insert its own key"
(H3, an acyclicity fact about the environment that `RunsTo`/`RefLaws` do not
model). For H3 a probe test is written that ASSERTS it on three cyclic
`unsafe` declarations (§1.3). No endpoint changes; no premise is added to
any endpoint; `ChildBndC` / `Fits` are not used to empty a gap.

## 1. Step 1: the three questions, against the current source

Facts used throughout (READ):

* F1. `sparkleChildCache` (declared 1030–1032) is touched at three places:
  the depth-0 clear 5498, the read 8878, the insert 8880 (`synthesizeChild`,
  8877–8881). Nothing else in `Sparkle/` reads or writes it (grep over
  `Sparkle/`; the other hits are comments 5610, 6283).
* F2. The inserted value is `synthesizeCombinational n` (8879) =
  `synthesizeCombinationalWith translate n` (8869) =
  `synthesizeCombinationalCoreWith translate n [] false` (5549;
  `certifiedFrontEnd` defaults to `true`, 5392) followed by pure post passes
  (5552–5561) and one `IO.getEnv` (5557).
* F3. Every nested synthesis goes through the memoised entry:
  `childSynthEntry` (5575–5579) reads `sparkleChildSynth`, set once to
  `synthesizeChild` (8882; no other `.set` in `Sparkle/`); its callers are
  `Rec.synthesizeCombinational` (6287–6289; used 6541, 6553) and the
  certified instance arms (8677–8678, 8695–8696); the machine closings read
  the same ref (5193–5194, 5210–5215).
* F4. The depth is read at 5431, bumped at 5517, released in the `finally`
  5532–5533; the clear 5493–5505 runs only when the read is 0. So inside a
  run the depth is positive and nothing clears the cache.
* F5. A design is built only from: the empty design (`CircuitM.init`,
  `Sparkle/IR/Builder.lean` 59–64; `Design.empty`, `Sparkle/IR/AST.lean`
  443–444: `modules := []` — the top module is NOT in its own design,
  `finishSynth` 2229–2230 returns `finalCircuitState.design` unchanged);
  `CompilerM.addModuleToDesign` at 6580, 6583, 8492, 8534 (all four on a
  child result `sub` of F3: 6577–6583 with `subResult?` of 6541/6553;
  `instAddModules` 8488–8493 and `instRegisterChild` 8529–8536, called
  8573–8574 and 8646–8647 with `sub` of 8677/8695); `designWith`
  (`Sparkle/IR/Machine.lean` 302–305) in `closeInsts` (399) and
  `closeInstsG` (`Sparkle/IR/MachineInstG.lean` 119), over `children` from
  `synth c` or `memChild?` (5194, 5212–5215); the post pass `top`
  (5552–5554), which rewrites the design's modules NAMED AS THE TOP; and
  `MachMemory.memModule` (`Sparkle/Compiler/MachMemory.lean` 47–62:
  `{ topModule := name, modules := [m] }`). Grep for `modules :=`,
  `.addModule`, `addModuleToDesign` over `Sparkle/Compiler`, `Machine*.lean`:
  no other writer inside the entry (`synthesizeHierarchical` and its parameterised variant, 9058–9067, append the top AFTER the entry).
* F6. Module names: `CircuitM.init (ModuleName.ofDecl declName)` at 2941,
  2966, 5358; `ofMem combo aw dw` at `MachMemory.lean` 51. No `setModule` /
  `module := …` with another name in the entry (the one `set { cs with
  module := cs.module.addWire p }`, 6728, adds a wire). `finalize`
  (`AST.lean` 403–410), `addClockResetIfSequential` (2204–2209),
  `closeMachine` (`Machine.lean` 98–, `{ t with … }`), `withClockFor`
  (`MachineInstG.lean` 73–78), `closeInsts*` (`{ m' with body := body }`)
  keep the name.

### 1.1 Q1 — can two runs for the SAME declaration name insert different module lists?

**Verdict: two RUNS of one declaration can return different results; at most
ONE of them is ever in the cache between two depth-0 clears — except if a
declaration's run re-enters itself and the inner run returns (H3, §1.3).
PROVED part (written): an entry that exists when a run starts is still
there, unchanged, when the run ends (`entry_sub`, `child_sub`).**

| mechanism | READ | verdict | proof / counterexample |
|---|---|---|---|
| key | 8878–8880: the key is `n` only | one entry per declaration name | — |
| parameters, `symbolicMode`, `cfe` | F2: the cached value is always the run with `[]`, `false`, `cfe = true`. `synthesizeCombinationalWithParameters` (7984–7988, `parameters true`) and `cfe := false` (tests only: `Tests/Compiler/ShippingInlineSoundnessTest.lean` 401–402, 452–453; `LegacyCacheFixCostTest.lean` 130) are OUTERMOST calls: they do not insert their own result, and their children go through F3 with the default flags | CANNOT differ by flag | by F1–F3 (reading); the statements below quantify over runs of `synthesizeCombinational c`, which fixes the flags |
| width-generic child | no argument of a call site enters 8879; one module per declaration; a call whose widths disagree is the link check's (`instLinkCheck`, called 8595, 8657) | one entry | — |
| route (gate / mixed / machine / legacy) | chosen INSIDE the entry, from the constant and the environment the run reads (5523–5529, `entryConst` 5249–5259) and from whether the machine closing returns `some` (5293–5302; `closeInsts*` return `none` on a failed check, then the legacy arm runs, 5302–5366). So the result of a run DOES depend on the world (e.g. on the cache content the closing sees) | two runs may differ; only the first to RETURN under a missing key is inserted, later calls are hits (8878) | `Tools.ShippingCallsSame.synthesizeChild_post` (BUILT): a hit returns the cached value; `child_sub` (written): every existing entry survives any later run |
| cache state / context | same: a run's result is a function of its start world; `RealChild` (`Tools/ShippingChildInv.lean` 451–459) records only that SOME run produced the entry | as above | two `RealChild`s of one name are not claimed equal anywhere; nothing here needs it |
| failed-then-retried | the catches that go on translating are `Rec.tryInlineUnfold` 6310–6331 (inline attempt, retry under reducible transparency, then 6551–6553 the helper as a module). 6540–6544 and 6552–6564 rethrow. `CompilerM` is `ReaderT CompilerState (StateT CircuitState MetaM)` (92): a `catch` resumes from the builder state at the `try` (the design registered by the failed attempt is dropped); the wire caches are restored by hand (`restoreWireCaches` 5644–5655), the child cache deliberately not (5610–5612). A run that THROWS inserts nothing for its own key (8879 threw before 8880); children it completed stay cached and a retry gets them as hits | CANNOT produce two entries for one name; a retried declaration is inserted once, by the run that returns | `child_sub` / `entry_sub` are stated for `endW` — the THROWING outcome included: what was cached before a failed attempt is cached after it |
| `sparkleSubModuleCache` memo (5311–5315) | holds the RAW core result, inserted at 5274 / 5281 / 5300 / 5365, i.e. at the end of a core run that returns; after that only pure passes and `IO.getEnv` (5552–5561) and the `finally` (5532–5541: ref writes) run before 8880. So at positive depth `c` in the memo implies `c` in the child cache, unless `c` is the outermost declaration (never looked up again) or on a cycle | the memo hit is NOT REACHED from `synthesizeChild` in an acyclic run | reading only; not a theorem (`sparkleSubModuleCache` is a `SideRef`: the laws frame it, they say nothing of its content) |
| overwrite of a key during its own run | §1.3 | needs a cycle through an `unsafe` definition AND a returning inner run | probe test, §1.3 |

### 1.2 Q2 (H1) — can a result contain a module named `ofDecl c'` that is not the cache's module under `c'` at that moment?

**Verdict: NOT by reading, for a run that does not re-enter its own
declaration. NOT PROVED at the run level for the translator; PROVED
(written) for the machine closings relative to the transition's design.**

By F5 every module of a design is (i) an element of `sub.2.modules` or
`sub.1` for a result `sub` of the memoised entry — which is in the cache
under its declaration when the call returns (`synthesizeChild_post`, BUILT)
and stays there (F4; `child_sub`) —, or (ii) `memModule`'s module (named
`ofMem …`, `MachMemory.lean` 51), or (iii) the image of such a module under
the post pass `top` — which changes only modules NAMED AS THE TOP
(5554: `if x.name == m.name`). By F6 the top is named `ofDecl declName`; a
module of kind (i) is named `ofDecl c'` for its cache key `c'`, of kind (ii)
`ofMem …`. With `ofDecl_injective` and `ofDecl_ne_ofMem`
(`Tools/ShippingModuleName.lean` 766, 778) case (iii) needs `c' = declName`,
i.e. the declaration's own key in the cache during its run — H3 again. The
name-deduplication (first of a name is kept: 6577–6583, 8491, 8532–8533,
`designWith`) only DROPS modules.

| mechanism | verdict | status |
|---|---|---|
| post passes (`top`, `dropZeroWidthModule`, `mergeChecked`) | identity on the design, name of the top kept | PROVED (written): `full_split` (run), `fresh_post` (pure). Re-used: `Tools.ShippingDesignWriterRun.fullEntry_name`, `Tools.ShippingKidsChildIface.map_other` (BUILT) |
| `designWith` in `closeInsts` / `closeInstsG` | a module of the join is of the parent design or of a child | PROVED (written, pure): `mem_designWith`, `closeInsts_design`, `closeInstsG_design` |
| general closing, no memory child (`closeInstsGM`) | every module of the closing's design is a memory module or the module of an entry of the END cache, if the transition's design is | PROVED (written, run level, from the existing `closeInstsGM_run_allF`): `closeInstsGM_design_prov` |
| one-output closing (`closeInstsM`); general closing WITH memory children | same by reading | NOT shown: the built run lemmas give `ChildrenReal` ("some real compile"), not "the end cache's entry"; `mapM_loop_final` (`Tools/ShippingCallsRunFinal.lean` 44–) is the tool |
| translator: legacy handler 6577–6583; certified arms 8573–8574, 8646–8647 | by reading (F5) | **NOT shown.** It is a statement about the BUILDER STATE (`cs.design.modules`) after a `CompilerM` run. `KeepsC` (`Tools/ShippingChildInv.lean` 527–531) and the proved `bodyRel` / `legacyRel` / `translateRel` / `harnessRel` quantify over every builder state and conclude about WORLDS only; none can carry it. The fuel fallback's `partial` handlers are opaque: for them nothing about the returned state can be proved at all |
| the top's name (F6) | by reading | **NOT shown** in general (same reason: the builder's `module.name` after the translator). Known per route only where an endpoint already derives it |

### 1.3 Q3 (H3) — is a cache entry ever overwritten?

**Verdict: an entry that EXISTS when a run starts is never overwritten or
removed by that run — PROVED (written) from the existing laws. An entry
inserted DURING a run can be overwritten only by the insert of the SAME
key's outer run, i.e. only if a declaration's entry is re-entered and the
inner run returns. For kernel-checked declarations that is excluded by the
environment (a definition's value does not reach itself), which is NOT a
theorem here. For `unsafe` declarations a cycle exists in the source;
PREDICTED no run on it returns; a probe ASSERTS it.**

READ: the insert 8880 is `m.insert n r` on the cache as it is AFTER the run
8879; the lookup 8878 was a miss BEFORE it. `RefLaws.auxInsert`
(`Tools/ShippingChildInv.lean` 342–343) has exactly this shape: `aux m0 →
m0.get? n = none → aux m1 → aux (m1.insert n r)`.

* Existing entries: `SubMap mb m` ("every entry of `mb` is an entry of `m`
  with its value") satisfies `auxInsert` (`sub_insert`: a key absent from
  `m0 ⊇ mb` is not a key of `mb`). `entry_keeps_all` / `childKeeps_all` at
  that auxiliary predicate give `entry_sub` / `child_sub` on every outcome.
  This is the all-keys form of `synthesizeChild_pin` (BUILT).
* Own key: nothing in `auxInsert` says `m1.get? n = none`. It is false iff
  `synthesizeChild n` returned inside the run of `n`'s entry. Sources of a
  cycle: a `defnInfo` whose value reaches itself — `unsafe def` (a
  `partial def` is an opaque constant: 6359–6363 and 5367–5368 refuse it;
  structural / well-founded recursion compiles to a value without a
  self-reference). The front-end inliner does not unfold `unsafe`
  definitions (`userDefinition?`, 3327–3339: `d.safety == .safe`).
* Why PREDICTED no run on a cycle returns: the FIRST run of `n` to return
  has had every nested `synthesizeChild n` throw (no earlier insert of `n`,
  so no hit); the only recovering `catch` (6313, 6329) retries the same
  expression (6318–6326) or synthesises the helper as a module (6553) whose
  body or arguments contain the same call; the innermost attempts fail at
  the depth limit (5431–5433). This is an argument, not a proof, and it does
  not cover a helper whose INLINE form drops an argument that the module
  form would translate (then the inline attempt succeeds first and there is
  no re-entry at all: probe `cyc3`).

**Probe (target-only, asserting): `Tests/Compiler/CacheOwnKeyProbe.lean`.**
Runs the full entry on a control and on three cyclic `unsafe`
`@[hardware_module]` declarations from reset refs with the synthesis depth
pre-set to `sparkleSynthDepthLimit - 6` (a cycle meets the limit after six
levels; the retry at 6553 doubles the attempts per level, so starting at
depth 0 could take 2^1024 attempts — PREDICTED, a finding of its own if
true: a cyclic `unsafe` hardware module would not fail fast). It writes
`CACHEOWN START …` to standard error (flushed) before each run and

    CACHEOWN <label>: returned=<T/F> ownKey=<T/F> depthAfter=<d> keys=[…] <message>

after it, and THROWS unless, for every top: not (`returned=T` and
`ownKey=T`); `depthAfter` = the start depth; and for the control:
`returned=T` and the cache holds `ctlKid`.

PREDICTED output: `ctl: returned=T ownKey=F depthAfter=1018 keys=[…ctlKid]`;
`cyc1`, `cyc2`: `returned=F ownKey=F depthAfter=1018` with the depth-limit message (5433) or, if the call went
through the legacy handler, `Sub-module synthesis failed for …` (6543–6544);
`cyc3`: `returned=T ownKey=F` or `returned=F`; `CACHEOWN RESULT: 0
violations`. A line `returned=T ownKey=T` is a counterexample to H3 and to
`CoreFresh`.

## 2. What is written (WRITTEN, NOT BUILT)

### `Tools/ShippingCacheCoherentRun.lean`

```lean
def IsMem (a : Module) : Prop := ∃ cb aw dw, a = (memModule cb aw dw).1
def IsTop (m : Std.HashMap Name Res) (a : Module) : Prop := ∃ c y, m.get? c = some y ∧ a = y.1
def Prov (m : Std.HashMap Name Res) : Prop :=
  ∀ c y, m.get? c = some y → y.1.name = ofDecl c ∧ ∀ a ∈ y.2.modules, IsMem a ∨ IsTop m a
def Fresh (m) (c : Name) (r : Res) : Prop :=
  m.get? c = none ∧ r.1.name = ofDecl c ∧ ∀ a ∈ r.2.modules, IsMem a ∨ IsTop m a
def SubMap (mb m : Std.HashMap Name Res) : Prop := ∀ k y, mb.get? k = some y → m.get? k = some y

-- pure
theorem memModule_name (cb aw dw) : (memModule cb aw dw).1.name = ofMem cb aw dw
theorem kind_of_mem (h : Prov m) (hy : m.get? c = some y) (ha : a ∈ mods y) : IsMem a ∨ IsTop m a
theorem eq_of_kinds (h : Prov m) (ha : IsMem a ∨ IsTop m a) (hb : IsMem b ∨ IsTop m b)
    (hn : a.name = b.name) : a = b
theorem coherent_of_prov (h : Prov m) : Coherent m
theorem prov_empty : Prov {}
theorem sub_refl / sub_trans / isTop_mono / sub_insert_absent
theorem prov_insert (h : Prov m) (hf : Fresh m c r) : Prov (m.insert c r)
theorem fits_of_fresh (h : Prov m) (hf : Fresh m c r) : Fits m r
theorem fresh_post (h : Prov m) (hf : Fresh m c (M, D)) (hname : M'.name = M.name)
    (hmods : (∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules) : Fresh m c (M', D')

-- from the existing run laws (hB : ∀ L', BodyRel L' — PROVED: `bodyRel`)
theorem sub_insert (mb) : ∀ m0 m1 n r, SubMap mb m0 → m0.get? n = none → SubMap mb m1 →
    SubMap mb (m1.insert n r)
theorem entry_sub (L) (hB) (hw : InvV L w) (hd : L.dval w ≠ 0) :
    SubMap (L.val w) (L.val (endW mctx mref cctx cref (synthesizeCombinational c) w))
theorem entry_sub_runs … (h : RunsTo (synthesizeCombinational c) … w r w') : SubMap (L.val w) (L.val w')
theorem child_sub (L) (hB) (hw : InvV L w) (hd : L.dval w ≠ 0) :
    SubMap (L.val w) (L.val (endW mctx mref cctx cref (synthesizeChild c) w))
theorem child_sub_runs … (h : RunsTo (synthesizeChild c) … w y w') : SubMap (L.val w) (L.val w')
theorem full_split (L) (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (M', D') w') :
    ∃ M D w1, RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 ∧
      L.val w' = L.val w1 ∧ M'.name = M.name ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → D'.modules = D.modules)

-- THE RESIDUAL (a statement)
def CoreFresh (L : RefLaws mref cref) (c : Name) : Prop :=
  ∀ mctx cctx w M D w1, InvV L w → L.dval w ≠ 0 → Prov (L.val w) → (L.val w).get? c = none →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 →
    Prov (L.val w1) ∧ Fresh (L.val w1) c (M, D)

-- relative to it
theorem synthesizeChild_prov (L) (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hR : CoreFresh L c) (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    Prov (L.val w')
theorem synthesizeChild_coherent_run … : Coherent (L.val w')
```

Where each is used: `coherent_of_prov` ← `eq_of_kinds`, `kind_of_mem`;
`prov_insert` ← `sub_insert_absent`, `isTop_mono`; `fits_of_fresh` ←
`coherent_of_prov`, `prov_insert` (it connects to the old vocabulary:
`coherent_insert`'s premise); `synthesizeChild_prov` ← `full_split`,
`fresh_post`, `prov_insert`, `CoreFresh`; `entry_sub` / `child_sub` are used
by nothing yet (they are the proved half of H3 and what a derivation of
`CoreFresh` needs to keep `IsTop` facts across nested runs: `isTop_mono`).

`hE` of `synthesizeChild_coherent` is NOT discharged as stated (it has no
invariant and no miss hypothesis on its start world, so it cannot follow
from a statement that needs them); `synthesizeChild_coherent_run` is its
replacement, with `Fits` recovered by `fits_of_fresh`.

### `Tools/ShippingCacheCoherentClose.lean`

```lean
theorem mem_foldl_addM : ∀ l acc x, x ∈ l.foldl addM acc → x ∈ acc ∨ x ∈ l
theorem mem_designWith (h : g ∈ (designWith children d).modules) : g ∈ d.modules ∨ g ∈ visited children
theorem closeInsts_design (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    d = designWith children d₀
theorem closeInstsG_design (h : closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)) :
    d = designWith children d₀
theorem closeInstsGM_design_prov (L) (hB) (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hnomem : ∀ c ∈ shape.insts, memChild? c.1 = none) (hp' : Prov (L.val w'))
    (h0 : ∀ a ∈ d₀.modules, IsMem a ∨ IsTop (L.val w') a)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∀ a ∈ d.modules, IsMem a ∨ IsTop (L.val w') a
def PInv (L) (w) : Prop := InvV L w ∧ L.dval w ≠ 0 ∧ Prov (L.val w)
theorem child_pinv (L) (hB) (hR : ∀ c, CoreFresh L c) (hp : PInv L w)
    (hy : RunsTo (synthesizeChild c) … w y w') : PInv L w'
theorem closeInstsM_prov / closeInstsGM_prov (L) (hB) (hR : ∀ c, CoreFresh L c)
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (closeInstsM / closeInstsGM shape t m₀ d₀) … w r w') : Prov (L.val w')
-- a STATEMENT, not derived
def HarnessProv (L) : Prop := ∀ mctx cctx b declName bs body w r w',
    InvV L w → L.dval w ≠ 0 → Prov (L.val w) →
    RunsTo (synthesizeMixedCertified (fun e hint top named => translateExprToWire e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w r w' → Prov (L.val w')
theorem machine_prov (L) (hB) (hH : ∀ L', HarnessRel L') (hHP : HarnessProv L)
    (hR : ∀ c, CoreFresh L c) (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (synthesizeMachineCertified … (profLogIO b) declName shape) … w r w') :
    Prov (L.val w')
theorem machine_closes_of_prov (decls) (hS : MachineClosesAtS mctx mref cctx cref declName shape decls)
    (L) (hB) (hH) (hHP) (hR) (hw) (hd) (hp) (hr : RunsTo (synthesizeMachineCertified …) … w r w') :
    r ≠ none
```

`machine_closes_of_prov` is the consumer (step (c)) in the `Prov`
vocabulary: with `machineClosesAtS_of_kids` (BUILT) it would give "`mixDeep`'s
machine synthesis does not fall back from a `Prov` start world" — RELATIVE
to `HarnessProv` and `CoreFresh`, neither derived. It is NOT
`MachineClosesAt mixDeep` and nothing consumes it. No endpoint changes.

## 3. PROVED (written) vs. NOT shown

| step | statement | state |
|---|---|---|
| (a) initial | `prov_empty`; with `coherent_after_clear`'s law (`L.cacheSet`) the world after the depth-0 clear satisfies `Prov` | PROVED (written) — pure part only; no `ProvAt`/boundary variant is written, deliberately (a stronger start premise is not progress) |
| invariant ⇒ clause | `coherent_of_prov` | PROVED (written), pure; uses `ofDecl_injective`, `ofDecl_ne_ofMem`, `ofMem_injective` (BUILT) |
| (b) insert | `prov_insert`, `fits_of_fresh` | PROVED (written), pure |
| (b) post passes | `full_split`, `fresh_post` | PROVED (written), run level, no new premise |
| (b) existing entries survive (H3, half) | `entry_sub`, `child_sub` | PROVED (written), run level, every outcome, from `RefLaws` + `BodyRel` only |
| (b) memoised entry | `synthesizeChild_prov`, `synthesizeChild_coherent_run` | PROVED (written) RELATIVE to `CoreFresh c` |
| (b) closings | `closeInstsM_prov`, `closeInstsGM_prov`; `closeInstsGM_design_prov` | PROVED (written) relative to `CoreFresh`; the design lemma from existing laws |
| (b) machine synthesis | `machine_prov` | PROVED (written) RELATIVE to `HarnessProv` and `CoreFresh` |
| (c) consumption | `machine_closes_of_prov` | PROVED (written) relative to the same |
| **`CoreFresh c`** | the core run of `c` keeps `Prov`, and its result is `Fresh` | **NOT shown** |
| **`HarnessProv`** | the translator on a transition keeps `Prov` | **NOT shown** |

Why `CoreFresh` / `HarnessProv` are not derivable today — exactly:

1. **H1, result level.** "Top named `ofDecl c`; design modules are memory
   modules or cache tops" is about the builder state the translator
   returns. Needed: a `KeepsC`-style statement that also relates the
   builder's `design.modules` / `module.name` before and after (through
   `instAddModules`, `instRegisterChild`, the legacy handler, every arm
   that only passes the state on, and the `catch`es). The proved relative
   theorems cannot be instantiated to it; the `partial` fuel-fallback
   handlers cannot be reasoned about at all (a hypothesis-free statement
   must exclude that the fuel runs out, or treat those handlers as a
   boundary).
2. **The recursion.** `Prov` of the END cache needs every nested
   `synthesizeChild` to keep `Prov`, i.e. `CoreFresh` of every nested
   declaration, closed by induction on the depth as `entry_keeps` does for
   `J`. `RefLaws.aux` cannot carry `Prov`: `auxInsert` is for EVERY inserted
   value `r`, and `Prov (m1.insert n r)` is false for an `r` without
   provenance. (`HarnessProv` is the same recursion seen from the machine
   route; in a real derivation both come from one relative theorem "the
   translator keeps `Prov` if the memoised entry does".)
3. **H3, own key.** `(L.val w1).get? c = none` after the core run of `c`.
   True of kernel-checked declarations by acyclicity of the environment;
   `RunsTo` / `RefLaws` have no model of the environment's dependency
   order. `entry_sub` is the other half. The probe (§1.3) tests it where a
   cycle exists in the source.

The checked insert of the predecessor's §4 (`synthesizeChildC`) would
discharge 1 and 3 by a decision at the insert and make 2 an `aux`; it is a
compiler change and is NOT proposed again here (this round does not touch
`Sparkle/`). Without it, the cheapest honest next unit is 1 for the
CERTIFIED instance arms only (`translateInstanceUncachedWith`,
`translateProjInstanceUncachedWith`: straight-line, non-`partial`, already
decomposed for `Tools/ShippingChildFallback.lean`), which covers the
machine route's transitions that have no legacy instance; and the
`closeInstsM` / memory-children analogue of `closeInstsGM_design_prov`.

## 4. Endpoint — premise — state

| endpoint | premise | state |
|---|---|---|
| `mixDeep.machine_design_noPortsNR2` (OPEN, BUILT) | `MachineClosesAt mixDeep` | STAYS |
| every other endpoint | — | unchanged |

No `…_closed` endpoint for `mixDeep` is written. Nothing here is a premise
of any endpoint.

## 5. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingCacheCoherentRun» where
      roots := #[`Tools.ShippingCacheCoherentRun]

    lean_lib «Tools.ShippingCacheCoherentClose» where
      roots := #[`Tools.ShippingCacheCoherentClose]

`Tests/AllTests.lean`: nothing to add (the probe is target-only; add
`import Tests.Compiler.CacheOwnKeyProbe` only after its first run, if it is
to become a regression — it asserts).

Order:

1. `Tools.ShippingCacheCoherentRun` (imports `Tools.ShippingCacheCoherent`,
   `Tools.ShippingModuleName`, `Tools.ShippingCallsSame`,
   `Tools.ShippingDesignWriterRun` — all BUILT). Axioms expected: standard.
2. `Tools.ShippingCacheCoherentClose` (imports 1,
   `Tools.ShippingCallsRunFinal`, `Tools.ShippingDesignWithG`). Independent
   of the probe. A failure here does not affect 1.
3. `Tests.Compiler.CacheOwnKeyProbe` — under `cgrun.sh`, alone; read the
   `CACHEOWN` lines on standard error. If it does not terminate quickly,
   that is the `cyc2` retry blow-up (§1.3): kill it and report; the START
   line says which top.

## 6. UNVERIFIED, in risk order

1. **The probe's declarations**: whether `@[hardware_module] unsafe def`
   (and the `mutual` pair) elaborate; whether the entry accepts an `unsafe`
   definition; `cyc2`'s run time; the control at a pre-set depth (the entry
   then takes the nested branch: no clear — the refs are reset by hand).
2. `full_split`: the shape of the `IO.getEnv` bind after `dsimp only`
   (`L.same (.ioEnv _) henv`, as `core_reads_inv` does for the profile
   variable); `RunsTo.pure_world` on the two `return`s; the rest is the text
   of `synthesizeCombinational_designTop` (BUILT).
3. `closeInstsGM_prov` / `closeInstsM_prov`: the `mapM_hoare` step
   functions (tactic blocks, so that `hch` fixes the mapped function first);
   `dsimp only at hy` on the tuple match; unification of
   `synthesizeChild ?c` with the mapped function applied to a variable (as
   `closeInstsM_inv` relies on).
4. `machine_prov`: the three `split at hr` in the order of
   `synthesizeMachineCertified_inv` (BUILT); `RunsTo.pure_world` where that
   proof uses `RunsTo.pure_eq`.
5. `eq_of_kinds`, `fresh_post`: chains of `rw [← …]` on names
   (`memModule_name` is `rfl`; if `rfl` fails there, unfold `memModule`).
6. `closeInstsGM_design_prov`: `List.mem_iff_getElem?`,
   `List.getElem?_eq_some_iff`; the destructuring of
   `closeInstsGM_run_allF`'s conclusion.
7. `closeInsts_design` / `closeInstsG_design`: the text of
   `closeInsts_names` / `closeInstsG_inputs` (BUILT) with `rfl` at the end.
8. `entry_sub` / `child_sub`: the text of `synthesizeChild_pin` /
   `entry_inv` (BUILT) with another auxiliary predicate.
9. `prov_insert`, `sub_insert`, `sub_insert_absent`: `get?_insert` + `split`
   (the text of `cacheInv_insert` / `pin_insert`).

## Integrator's build record (2026-10-13)

BUILT on tree `0907abb907f5426acdbabe5ae29f50ab502cb100` (poc 812061e5 + these files), cgrun 3 GiB swap 0, each first attempt, no change to
the worker's files: `a33-run` (`Tools.ShippingCacheCoherentRun`, exit 0, peak 0.82 GB), `a33-close`
(`Tools.ShippingCacheCoherentClose`, exit 0, 0.21 GB), `a33-ax` (`#print axioms` of coherent_of_prov,
prov_insert, entry_sub, child_sub, full_split, synthesizeChild_prov, synthesizeChild_coherent_run,
closeInstsGM_design_prov, machine_prov, machine_closes_of_prov: each `[propext, Classical.choice,
Quot.sound]`), `a33-probe` (`Tests.Compiler.CacheOwnKeyProbe`, target-only, exit 0, 0.33 GB).

Probe output (as predicted): `ctl returned=T ownKey=F keys=[ctlKid]`; `cyc1 returned=F ownKey=F` (depth
limit); `cyc2 returned=F ownKey=F` — but with "Cannot synthesise cycHelp: not inlinable and not a hardware
module", so cyc2 did NOT exercise the inline catch-and-retry path it was written for; `cyc3 returned=T
ownKey=F keys=[]`; `0 violations`. Three cyclic declarations, one start depth: an observation, not a proof
of own-key freshness.

STATE: step (b) is NOT closed. `CoreFresh` and `HarnessProv` are statements, not derived; every theorem
that concludes `Prov` / `Coherent` at run level has one of them as a hypothesis. No endpoint uses any of
this; no endpoint premise changed; `mixDeep` is still open.
