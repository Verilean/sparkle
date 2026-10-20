# A: the determinism route — refutation attempt first — round par/a-39

Base: `poc/roundtrip-proof` 11a2ee8f (par/a-38 BUILT and integrated).
Branch `par/a-39`. **NOTHING here was built or run**: WRITTEN, NOT BUILT.
"READ" = read at 11a2ee8f; line numbers `Sparkle/Compiler/Elab.lean` unless
a file is named. No built file, endpoint or generator is modified.

## 0. Result

`Det c := ∀ y y', RealChild c y → RealChild c y' → y.1 = y'.1`.

1. **Refuted in general** (PREDICTED; an asserting probe is written): for a
   declaration on the LEGACY route that instantiates an untagged helper
   compiled as a module, two compiles from two invariant worlds of positive
   depth return different modules — the legacy single-output instance cache
   is not reset at a nested entry and its hits are not validated (§1, item
   D). Not reachable in a real compile; reachable among the worlds
   `RealChild` and `MachineClosesAt` quantify over.
2. **Not refuted, and NOT proved, for the certified route** (`rcH`, `cnt`,
   `midH`, `mid2`): everything their result depends on is fixed by the
   entry EXCEPT one thing the present laws do not speak about — what a READ
   of the run-local translation cache returns (§1, item B). `RefLaws` has
   value laws for three refs only; the translation cache is a fourth, and
   whether the validated lookup hits or misses changes the emitted module.
   So `Det` is not derivable today for a body with a repeated non-variable
   subterm; no probe can show it false (the runtime's refs behave as refs).
3. **The consumer is written as a reduction** (`machineClosesAt_of_det`):
   `MachineClosesAt` at its FULL scope from the built relative closing,
   `Det` on the descendants, and "every module of a real compile of a
   callee is the module of a real compile of a descendant". It says exactly
   what the counter-world analysis needs: `.1` only — the design component
   is NOT needed as an equality.
4. `mixDeep` stays OPEN. No `_closed` endpoint is written. Step 2 of the
   task (the proof of `Det`) is NOT delivered: it needs a decision first
   (§3).

## 1. Refutation attempt: what a result can depend on besides the declaration

"World" = an invariant world: `CacheInv` of the child cache, the synthesis
ref set, quiet. Every OTHER ref is unconstrained by the invariant.

| | item | READ | verdict |
|---|---|---|---|
| A | the builder's start state (counter, used names, module, design, record) | every route starts from `CircuitM.init (ofDecl declName)` (2941, 2966, 5358; `Sparkle/IR/Builder.lean` 59–64): counter 0, nothing used | FIXED by the entry |
| B | **the translation cache** (`exprCache`) | a fresh `IO.mkRef {}` per harness run (2937, 2962, 5354); read by `cacheLookupValidated` (8003–8014), written by `recordTranslation` (8018–8024) and `emitLeaves` (2181). A hit is validated against the builder's record, so a hit is always SOUND — but hit or miss changes what is emitted (a miss lowers the node again: new wires, new assigns) | in the runtime: a function of the run. **In the laws: unconstrained** — `Framed.mkExprCache` / `exprCacheGet` / `exprCacheModify` (`Tools/ShippingChildInv.lean` 231–252) are FRAME facts about the three tracked refs; no law says what a read of this ref returns. For a node whose expression is not yet in the record the validation fails whatever the ref holds (a miss in every world); for a REPEATED non-variable subterm the laws allow a hit in one world and a miss in another. Not refutable by a probe |
| C | fresh variable ids (`mkFreshFVarId`, 2934, 2959; the legacy `lambdaTelescope`) | differ between runs; they are keys of the reader's map and occur in the translated expression and in the builder's RECORD (`translateRecord`), never in a wire name or a statement | the MODULE does not depend on them; the builder state does (the record). A proof of `Det` must be relational, modulo a renaming of the ids — not "the state is a function of the start state" |
| D | **`sparkleSingleOutInstanceCache`** | cleared at depth 0 only (5500); a nested entry resets the other wire caches (5511–5516) and not this one; the certified instance arm validates a hit against the record (8588–8589, `instHitValid`); the LEGACY handler does not (6642–6644: `if let some cachedW := instCache.get? instKey then return some cachedW`, before the wire and the instance are made); the key is `parent#child#connections` (6641) | **`Det` FALSE** for a legacy-route parent with a single-output instance emitted by the legacy handler (an untagged helper compiled as a module, 6551–6553): probe `Tests/Compiler/SingleOutStaleProbe.lean`. Certified route: no effect (transitions have no instance; the certified arm validates). Real compiles: not reachable — one compile per declaration per outermost synthesis, and the retrying catches restore this cache (`WireCaches.singleOut`, 5613–5655) |
| E | `sparkleSubModuleCache` (the legacy arm's memo) | read at 5311–5315 in the LEGACY arm only, after the certified arms declined; not reset at a nested entry (5497 is in the depth-0 block) | a world-dependent input of legacy-route results (a stale entry is returned as the result). Certified route: not read. The probe empties it (else it returns the first result and hides D) |
| F | `sparkleLetWireCache`, `sparkleLoopWireCache`, `sparkleWireCanon`, `sparkleSubInstanceOutputs`, `sparkleWireWidthCache`, `sparkleFvarValueMap` | reset at every entry (5501–5505 / 5511–5516), restored for the parent in the `finally` (5535–5541) — the F/G fixes | FIXED by the entry (the child starts from empty ones). No dependency |
| G | `sparkleTypeCache` (`cachedInferType`) | cleared at depth 0 only (5494); used by the legacy handlers and by `muxResultType` / `translateCanonicalSignalBinary` only when the canonical type is NOT literal (1790–1794, 1817–1820) | world-dependent for legacy-route results in principle (a cached type keyed by expression; I did not find a way two worlds give different TYPES for one key). Certified fragment: not read (the canonical branches are taken: `core_binary`, `mux_arm` with `pure ty`) |
| H | the route (certified / mixed / machine / legacy) | chosen from the constant and the environment the run reads (5523–5529) — the reflections fix these for every world and context — and, for a machine, from whether the closing returns `some` (5293–5302), which depends on the CHILD CACHE of the world | under the reflections and the built closings (`midH.closes_deep`, `mid2.closes_deep`, `cnt.machine_closes`: every invariant world), the route of `rcH`, `cnt`, `midH`, `mid2` is the same in every world. For `mixDeep` itself it is the open question |
| I | the children a parent gets | the memoised entry: a hit returns the world's cache entry (8878) — an arbitrary `RealChild` of the callee in an abstract world | the parent's module depends on the child's module only through its NAME and ports (the instance statement); its DESIGN holds the child's module. So `Det parent` (on `.1`) needs the child's interface, not the child's module — but `Agree` needs the modules: that is what `DetN` of the descendants is for |
| J | `cfe`, parameters, symbolic mode | `RealChild` is a run of `synthesizeCombinational c`: `[]`, `false`, `cfe = true` (5549, 5392) | FIXED |
| K | the profile flag, the clock, the call counter, the depth | logged only (5402–5410, 2161–2171); the counter and the depth can make a run THROW (5432, 6855–6868), not change what it returns | no dependency of the result |
| L | fresh instance names (`inst_<child>` + suffix) | `CompilerM.freshName` from the builder's used names (8594, 8656) | FIXED by A |
| M | parent-dependent state at a nested call | the entry gets only `declName` (8879); the reader and the builder are new (A); the per-module refs are reset (F) | none, apart from D, E, G |

Is `y.2 = y'.2` needed? No. The closing's check compares MODULES found by
name in the joined design (`Sparkle/IR/MachineInstG.lean`, the last
`children.all …` conjunct of `closeInstsG`); `Agree` is about modules. The
design component enters only as a list of modules, each of which is a
descendant's module.

### The probe (item D) — `Tests/Compiler/SingleOutStaleProbe.lean`

`hIrr` (untagged, `@[irreducible]`: neither `unfoldDefinition?` nor the
front end unfolds it) and `pTop x := hIrr x + x`. Run A: the full entry from
reset refs at depth 0. Run B: the full entry again with the depth pre-set to
1, the refs as A left them except the legacy memo (emptied, item E). It
writes START lines to standard error before each run and

    SINGLEOUT A: returned=<T/F> insts=<n> stmts=<n>
    SINGLEOUT B: returned=<T/F> insts=<n> stmts=<n>
    SINGLEOUT RESULT: equal=<T/F>

and THROWS unless: A returns with at least one instance statement; B
returns; the two modules DIFFER. PREDICTED: `A insts=1`, `B insts=0`,
`equal=F`. If `equal=T` the command throws and item D is not a refutation.
Unknown before the first run: whether an `@[irreducible]` helper is in fact
compiled as a module by the legacy handler (if A has no instance the probe
says so and shows nothing).

This is also a compiler observation in its own right (independent of the
proofs): a hit of the legacy single-output instance cache is not validated,
and the cache outlives a nested entry. No real compile is known to reach it.

## 2. What is written — `Tools/ShippingDetReduce.lean`

```lean
def DetN mref cref (c : Name) : Prop :=
  ∀ y y' : Res, RealChild mref cref c y → RealChild mref cref c y' → y.1 = y'.1
def RealMod mref cref (S : Name → Prop) (a : Module) : Prop :=
  ∃ c z, S c ∧ RealChild mref cref c z ∧ a = z.1 ∧ z.1.name = ofDecl c
theorem eq_of_realMod (hdet : ∀ c, S c → DetN mref cref c) (ha : RealMod mref cref S a)
    (hb : RealMod mref cref S b) (hn : a.name = b.name) : a = b
theorem agree_of_realMods (decls) (hdet)
    (hmods : ∀ c ∈ decls, ∀ y, m.get? c = some y → ∀ a ∈ mods y, RealMod mref cref S a) : Agree decls m
theorem machineClosesAt_of_det (decls) (hS : MachineClosesAtS mctx mref cctx cref declName shape decls)
    (hB : ∀ L', BodyRel L') (hH : ∀ L', HarnessRel L') (hdet : ∀ c, S c → DetN mref cref c)
    (hreal : ∀ c ∈ decls, ∀ y, RealChild mref cref c y → ∀ a ∈ mods y, RealMod mref cref S a) :
    MachineClosesAt mctx mref cctx cref declName shape
```

For `mixDeep`: `decls` = its callees, `S = {mid2, midH, rcH, cnt}`, `hS` =
`mixDeep.closes_shared` (BUILT). `hreal` is a fact about real compiles of
the three callees that the built route lemmas give (the module's name; the
design is `designWith` of real children over an empty harness design:
`machine_children_realA`, `closeInsts_design` / `closeInstsG_design`,
`closedBody_kinds_of_run`, the gate / leaf `iface`s) — NOT instantiated
here. `hdet` is `DetN` for the four descendants — NOT proved (§3).

`DetN` and `hreal` are hypotheses of a THEOREM about `MachineClosesAt`; they
are not offered as endpoint premises.

## 3. Why `Det` is not proved in this round, and what the decision is

For the certified fragment the result is a function of the entry's
arguments except for item B. Two honest ways on:

1. **A value law for run-local translation caches** — a fourth tracked
   value: what a read returns after `IO.mkRef v` and after `modify f`, and
   that the other listed operations leave it. It is ordinary ref semantics,
   but it EXTENDS the trust base (as `RefLawsM` did for the memo,
   `Tools/ShippingMemoLaws.lean` 5–18), and `ChildBnd` would have to carry
   it for the endpoint to lose its premise. Needs a ruling.
2. **A side condition instead of a law**: for a term with NO repeated
   non-variable subterm (a `Bool` on the term), every validated lookup
   misses whatever the ref holds — the record never has the node's
   expression before the node is lowered. Then no ref law is needed. It
   needs the record's invariant ("the record's values are the quotations of
   the nodes already lowered") and quotation's injectivity on distinct
   subterms; and the bodies of `rcH`, `cnt`, `midH`, `mid2` have to satisfy
   it — NOT checked (the packing of a machine may well repeat a subterm).

Either way the proof is the relational walk of item C: two runs, the same
term, two id lists; states related by "same module, design, counter, used
names; records equal up to the renaming"; per constructor the same arms as
`walk_still`. I estimate it at the size of `Tools/ShippingWalkStill.lean`
plus `Tools/ShippingHarnessStill.lean`, with a two-run logic in place of
`WHo`. Not started: starting it before choosing between 1 and 2 would fix
the wrong statement.

## 4. PROVED (written) vs. NOT shown

| statement | state |
|---|---|
| `eq_of_realMod`, `agree_of_realMods`, `machineClosesAt_of_det` | PROVED (written) |
| `Det` false for a legacy parent with a helper module (item D) | PREDICTED; asserting probe written |
| `Det` for `rcH`, `cnt`, `midH`, `mid2` | **NOT shown; not refuted** (item B is the one uncontrolled dependency) |
| `hreal` for `mixDeep`'s callees | NOT written (built ingredients named in §2) |
| `MachineClosesAt mixDeep`; `mixDeep.machine_design_noPortsNR2_closed` | **NOT shown; not written** |

## 5. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingDetReduce» where
      roots := #[`Tools.ShippingDetReduce]

`Tests/AllTests.lean`: nothing (the probe is target-only and ASSERTS a
difference; it is not a regression test).

Order: (1) `Tools.ShippingDetReduce` (imports
`Tools.ShippingCacheCoherentVia`); (2)
`Tests.Compiler.SingleOutStaleProbe`, alone; read the `SINGLEOUT` lines on
standard error.

## 6. UNVERIFIED, in risk order

1. The probe: whether `hIrr` is compiled as a module by the legacy handler
   and instantiated through the single-output path (run A `insts=1`);
   whether run B, at a pre-set depth with the memo emptied, takes the hit.
2. `machineClosesAt_of_det`: `machine_keeps` at `L.plain` through
   `keeps_runs` (as `coreVia_of`, BUILT); the `CacheAgrees` lambda.
3. `eq_of_realMod`: the chain of `rw [← …]`.
4. Item B's verdict rests on READING `RefLaws` (no value law for the
   translation cache) — a statement about what is NOT there; item G's on
   not having found a counterexample.

## Integrator's build record (2026-10-13) — the probe RAN

BUILT on tree `d91d66befedea19662f0795683e2307a53774dfc` (poc 11a2ee8f + these files), cgrun 3 GiB swap 0, run `a39` (exit 0, peak 0.80 GB),
worker's files unchanged, first attempt: `Tools.ShippingDetReduce`; `Tests.Compiler.SingleOutStaleProbe`
(target-only).

MEASURED (as predicted):
```
SINGLEOUT A: returned=T insts=1 stmts=3
SINGLEOUT START B (depth 1, refs as A left them, the sub-module memo emptied)
SINGLEOUT B: returned=T insts=0 stmts=2
SINGLEOUT RESULT: equal=F
```
FINDING I (constructed state, legacy route): the same declaration `pTop` (an untagged irreducible helper
compiled as a single-output module) is compiled to two DIFFERENT modules — in run B, started at depth 1
with `sparkleSingleOutInstanceCache` as run A left it, the legacy handler returns the cached wire and
emits NO instance (2 statements instead of 3). The cache is cleared at depth 0 only and a legacy hit is
not validated (the certified instance arm validates). So `Det` is false in general, and module B is not
a correct compile of `pTop` on its own (its body refers to a wire no instance drives — read from the
counts; the module text was not inspected and nothing was simulated).
NOT shown: that any real compile reaches this state. The state was built by the probe (depth pre-set,
one memo emptied). By the worker's reading a real compile does not (one compile per declaration per
outermost synthesis; the retry catches restore the cache). NOT fixed: a fix is a compiler change (reset the
cache at nested entries like the let / loop caches, or validate the legacy hit) and awaits a ruling.

STATE of the determinism route: `machineClosesAt_of_det` is a theorem (the all-worlds closing from
`DetN` of the shared descendants and provenance `hreal`). `DetN` for `rcH`, `cnt`, `midH`, `mid2` is
neither proved nor refuted; proving it needs either a value law for the run-local translation cache (a
trust-base extension) or a "no repeated subterm" side condition. `mixDeep` stays OPEN.
