# A: cache coherence for callees that share a descendant — round par/a-31

Base: `poc/roundtrip-proof` edd9496c. Branch `par/a-31`. NOTHING here was
built or run. "READ" = the line was read in the file named; "PREDICTED" =
concluded from READ lines, to be shown or refuted by the probe; every Lean
file is WRITTEN, NOT BUILT. Line numbers: `Sparkle/Compiler/Elab.lean` at
edd9496c unless a file is named.

## 0. Result in one paragraph

**A counterexample exists, and it comes first (§1).** The clause "two
modules of one name held by two different cache entries are equal" is NOT
true of the compiler in every reachable world. The cache is keyed by the
declaration `Name`; a module is identified by a STRING, and every design is
joined by that string, first come first kept. Two source-level programs make
two declarations yield one module name (§1.2: `Name.toString` is not
injective on names whose root starts with `#`/`?`; a declaration named like
a built memory module). For them the cache is incoherent after an OUTERMOST
run from an empty cache, and — PREDICTED — `MachineClosesAt` is FALSE for a
parent that satisfies every name hypothesis of
`Tools.ShippingCallsKidsS.closes_of_agree`. The five mechanisms the task
lists, (i)–(v), do NOT break coherence (§1.1). So: `mixDeep`'s own run is
coherent (its declarations print differently), but coherence is not an
unconditional invariant of `synthesizeChild`, and step (b) of the ruling
cannot be shown for the compiler as it is without a side condition that the
compiler does not establish. The pure part is written
(`Tools/ShippingCacheCoherent.lean`): the invariant, `Agree` for any
declaration list, (a), the pure insert lemma of (b), (c) modulo (b).
**Step (b) at run level is NOT shown; no endpoint changes; no test for
`mixDeep` is written.** A candidate that makes (b) a short theorem — a
CHECKED insert — is written beside the compiler's entry, not into it (§4).

## 1. Step 1: is the coherence clause true in every reachable world?

### 1.1 The five listed mechanisms — none breaks it

| | question | verdict | lines |
|---|---|---|---|
| (i) | the key; a width-generic child at two widths | CANNOT HAPPEN. The key is the declaration name ONLY (`synthesizeChild`, 8845–8849; doc 6248–6254: "the cache key is the declaration name only"). A child is compiled from its DECLARATION, never per call site: no argument or width enters `synthesizeCombinational n` (8837, 5515–5517: `declName [] false`). One name ↦ one entry, so a width-generic child cannot be held twice; a call whose widths disagree with that one module is the link check's business (`instLinkCheck`, 1200; called 8563, 8625), not the cache's. The module NAME does not encode parameters either: it is `declName.toString` (`CircuitM.init declName.toString`, 2940, 2965, 5357). | 8845–8849, 5357 |
| (ii) | rollback / fallback | CANNOT HAPPEN. `sparkleChildCache` has three occurrences besides its declaration (1029): the depth-0 clear 5471, the read 8846, the insert 8848. The wire-cache rollback excludes it by design (`WireCaches`, 5578–5590: "Not included: `sparkleSubModuleCache` / `sparkleChildCache`"; `restoreWireCaches` 5612–5623). No entry is ever removed or replaced except by the clear, which runs only when the depth reads 0 (5466), and the depth is written only at 5489 / 5505 (bump, `finally`), so it is positive throughout a run. A child synthesised inside a nested entry that later THROWS stays cached (the insert 8848 of the inner child has happened); the failed parent is not inserted (8847 threw). A parent can therefore not hold a module of an entry that was rolled back. The insert CAN overwrite (`m.insert`) only if `n` was inserted during its own run, i.e. `n` reaches itself; a kernel-checked definition's value does not mention itself, and a cyclic `unsafe` one runs into the depth limit (5431). NOT a theorem: see §3 (b), H3. |
| (iii) | legacy route vs machine route | CANNOT HAPPEN. Both read the child through ONE function: the machine closing through `sparkleChildSynth` (5192, 5209, set once to `synthesizeChild` at 8850), the translator through `childSynthEntry` (5543–5547; callers 6255–6257 → 6509, 6521; 8646, 8664). The route is chosen INSIDE the entry (`synthesizeFromConst`, 5264–5367), after the lookup; the entry is the same whoever asks. |
| (iv) | `sparkleSubModuleCache` vs `sparkleChildCache` | CANNOT HAPPEN. The sub-module cache holds the entry's RAW result (inserts 5273, 5280, 5299, 5364, before the post passes 5523–5529); the child cache holds the post-passed one. The sub-module cache has ONE reader, the legacy arm's memo 5311–5314, which returns to the same entry; no parent's design is assembled from it. Designs are assembled only from `synthesizeChild` results (6545–6551, 8540–8542, 8613–8615; `closeInstsG`'s `designWith`, `Sparkle/IR/MachineInstG.lean` 119) and built memory modules (5212–5213). |
| (v) | fresh names, `sparkleCallCounter` | CANNOT HAPPEN. `sparkleCallCounter` (949) is a run-length limit (6855–6868), not a name source; it is never reset, which changes when a run THROWS, not what it returns. Wire names come from the builder state, fresh per module (`CircuitM.init`, `Sparkle/IR/Builder.lean` 59–64). Two syntheses of one declaration may well differ (finding G: a nested module depends on `sparkleSubInstanceOutputs`), but only one of them is ever in the cache (ii). |

### 1.2 What does break it: two declarations, one module name

READ:

* a module's name is `declName.toString` (2940, 2965, 5357), or, for a
  machine-route memory, `SparkleMem_{combo|sync}_{aw}_{dw}`
  (`Sparkle/Compiler/MachMemory.lean` 46–58), built not compiled (5212–5213)
  and NOT in the cache;
* every join of designs is by NAME, first come first kept: the translator's
  `instAddModules` (8456–8461) and `instRegisterChild` (8497–8504), the
  legacy handler 6545–6551, `designWith` (`Sparkle/IR/Machine.lean` 302–305);
* `finishSynth`'s `ModuleNameCheck.check` (2228; `Sparkle/IR/ModuleNameCheck.lean`
  14–24) rejects two DIFFERENT raw names that normalise alike; "repeated uses
  of the SAME raw name are allowed" — it cannot see that one raw name stands
  for two modules, because the second was already dropped;
* `Lean.Name.toString` escapes components with `«»` EXCEPT when the name's
  root component starts with `#` or `?` (`toStringWithToken`,
  `maybePseudoSyntax`, toolchain `Init/Data/ToString/Name.lean` 100–112), has
  macro scopes, or is inaccessible. So `«#ccp.k»` (one component) and
  `«#ccp».k` (two components) both print `#ccp.k`; the Verilog normalisation
  drops `#` (`Sparkle/Backend/Verilog.lean` 32–41) and the name is legal.

**Counterexample N (name printing).** Source (`Tests/Compiler/CacheCoherenceProbe.lean`):

```lean
@[hardware_module] def _root_.«#ccp.k» (x) := x + 1
@[hardware_module] def _root_.«#ccp».k (x) := x + 2
@[hardware_module] def nA (x) := «#ccp.k» x + x
@[hardware_module] def nB (x) := «#ccp».k x + x
def nTop (x) := nA x + nB x          -- one outermost entry call: nTop
```

PREDICTED after the one entry call from an empty cache: four entries; `nA`'s
design holds the `x + 1` module named `#ccp.k`, `nB`'s the `x + 2` module of
the same name: `Agree [nA, nB]` is false. `nTop`'s design holds ONE module
`#ccp.k` (the first), `nB`'s instance is bound to it: emitted
`nB x = (x + 1) + x`, source `(x + 2) + x` — a wrong design with no error.

**Counterexample Mc (the same under a machine parent).** `«#ccp.c»` /
`«#ccp».c` are `cnt` counting by 1 / by 2, `mA` / `mB` are `mid2`'s shape
over each, `mTop` is `mixDeep`'s shape over `mA`, `mB`. The callees print
differently (`hsep`), no callee prints as one of its descendants (`hselfD`),
the parent prints as none (`hparent`, `hparentD`): every NAME hypothesis of
`closes_of_agree` holds. PREDICTED: the pure closing returns `none`
(`Sparkle/IR/MachineInstG.lean` 140–141: two visited modules of one name,
unequal), so **`MachineClosesAt mTop` is false although the hypotheses of
`machineClosesAtS_of_kids` hold**; the entry then takes the legacy arm and
ships the design with one `#ccp.c`. The probe runs the machine arm alone at
depth 1 from an empty cache (`MACHINE ARM` line) — exactly the run
`MachineClosesAt` is about.

**Counterexample M (memory name).** `@[hardware_module] def
_root_.SparkleMem_combo_4_8 (wa wd) := wd + 1`; `memKid` is `memCounter`
with the tag (its machine-route design holds the built memory module of
that name); `mmTop = memKid we wa wd + SparkleMem_combo_4_8 wa wd`.
PREDICTED: the cache holds two modules named `SparkleMem_combo_4_8`; the
design holds one, with the ports of whichever came first.

What the counterexamples do and do not say:

* They do NOT refute coherence of `mixDeep`'s outermost run: its
  declarations (`mixDeep`, `mid2`, `midH`, `rcH`, `cnt`) print pairwise
  differently and have no memory.
* They DO refute coherence as an unconditional invariant of the cache, and
  they refute `MachineClosesAt` from the hypotheses of
  `machineClosesAtS_of_kids` alone: a general theorem needs a hypothesis
  that separates the DECLARATIONS of the descendants (the present
  hypotheses separate callees, and descendants only as strings).
* The legacy join-by-name is a compiler finding of its own (candidate "H":
  two modules of one name, the second silently dropped), independent of the
  machine route. Not fixed here.

Per the task ("if a counterexample exists, STOP after writing it and the
probe"): the probe is written. Because the task's step 2 anticipates
exactly this kind (a per-declaration name condition), the PURE part of
steps 2–3 is also written; nothing run-level is claimed.

## 2. The invariant (`Tools/ShippingCacheCoherent.lean`, WRITTEN, NOT BUILT)

```lean
abbrev mods (y : Res) : List Sparkle.IR.AST.Module := y.1 :: y.2.modules

def Coherent (m : Std.HashMap Name Res) : Prop :=
  ∀ (c : Name) (y : Res) (c' : Name) (y' : Res), m.get? c = some y → m.get? c' = some y' →
    ∀ a ∈ mods y, ∀ b ∈ mods y', a.name = b.name → a = b

theorem agree_of_coherent (decls : List Name) (h : Coherent m) : Agree decls m
```

It is a statement about the cache CONTENT only (no declaration list), and
`Agree decls m` follows for every `decls`.

Why not the proposed shape ("every module of a cached design is the top
module of a cached entry" + "names determine the declaration"):

* design closure to cached TOPS is false of real caches: a machine-route
  memory module is in a design and is no entry's top (5212–5213);
* "names determine the declaration" is what counterexample N refutes, and
  it is not established by anything the compiler does at an insert.

`Coherent` asks directly what the closing consumes; where a module comes
from is a premise of the insert lemma (`fits_of_prov`), not a field.

## 3. The three steps

### (a) INITIAL — proved (pure) / stated (boundary)

* `coherent_empty : Coherent {}` — PROVED (written).
* `coherent_after_clear`: the world after `sparkleChildCache.set {}` is
  coherent — PROVED (written). The child cache IS among the refs the
  depth-0 entry clears (5471, READ).
* The existing start condition does NOT imply coherence: `StartV`
  (`Tools/ShippingChildInv.lean` 508–509) is
  `sval = synthesizeChild ∧ (dval = 0 ∨ CacheInv val)`, and its nested
  alternative admits any cache of `RealChild`s. The start condition with
  the clause is

  ```lean
  def StartVC (L) (w) := L.sval w = some synthesizeChild ∧
    (L.dval w = 0 ∨ (CacheInv mref cref (L.val w) ∧ Coherent (L.val w)))
  def ChildBndC mref cref w := ∃ L : RefLaws mref cref, StartVC L w ∧ L.quiet w
  ```

  `ChildBndC.bnd : ChildBndC w → ChildBnd w` (it is the STRONGER premise);
  `childBndC_of_zero`: at depth 0 the two ask the same
  (`sval`, `dval = 0`, `quiet`). So for an endpoint stated at an OUTERMOST
  start world the premise keeps its strength (the depth-0 disjunct is
  unchanged, and coherence after the clear is derived); for a start world
  of positive depth it becomes STRONGER, and that part is an assumption
  about the world, not derived. Where the endpoints' `ChildBnd` premise is
  discharged today (`ChildBnd.of_invW`, 729–732: any invariant world) the
  analogue is `ChildBndC.of_inv`, which needs coherence of that world —
  i.e. step (b).

### (b) PRESERVATION — the pure insert lemma PROVED; the run level NOT shown

Written and proved (pure):

```lean
def Fits (m) (y : Res) : Prop :=
  (∀ a ∈ mods y, ∀ b ∈ mods y, a.name = b.name → a = b) ∧
  (∀ c' y', m.get? c' = some y' → ∀ a ∈ mods y, ∀ b ∈ mods y', a.name = b.name → a = b)

theorem coherent_insert (h : Coherent m) (hf : Fits m y) : Coherent (m.insert c y)
theorem fits_of_prov (h : Coherent m) (hnd : ((mods y).map (·.name)).Nodup)
    (hprov : ∀ a ∈ mods y, (∃ c' y', m.get? c' = some y' ∧ a ∈ mods y') ∨
      (∀ c' y', m.get? c' = some y' → ∀ b ∈ mods y', b.name ≠ a.name)) : Fits m y
def fitsB (m) (y : Res) : Bool            -- Fits, decided
theorem fits_of_fitsB : fitsB m y = true → Fits m y
```

Written and proved (run level, the memoised entry only):

```lean
theorem synthesizeChild_coherent (L : RefLaws mref cref) (hc : Coherent (L.val w))
    (hE : ∀ w1 r w2, L.val w1 = L.val w →
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w1 r w2 →
      Coherent (L.val w2) ∧ Fits (L.val w2) r)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') : Coherent (L.val w')
```

hit → no change (`L.get`); miss → the entry's run (`hE`), then
`L.cacheModify` and `coherent_insert`. Re-used: `RunsTo.bind`, `RefLaws.get`,
`RefLaws.cacheModify`, `RunsTo.pure_world` — the decomposition of
`synthesizeChild_inv` (`Tools/ShippingChildRun.lean` 199–227).

**NOT shown — the premise `hE`.** It is the missing statement of step (b):

    EntryFits: a returning run of `synthesizeCombinational c` from a world
    whose cache is coherent (and `InvV`) ends in a world whose cache is
    coherent, and its result `Fits` that cache.

It splits into three facts, none of which exists:

* **H1 (provenance)**: every module of the result's design is held by an
  entry of the end cache, or is a built memory module. True by reading
  (designs are assembled only from `synthesizeChild` results and
  `memChild?`, §1.1 (iv)); as a theorem it is a statement about the RESULT
  of every arm of the entry — the translator's builder state
  (`cs.design.modules`) through every handler, `designWith` in the machine
  arm, the post passes' `top` (5520–5529, which rewrites design modules
  named like the top). The existing `Keeps` theorems (`bodyRel`,
  `legacyRel`, `translateRel`, `harnessRel`) speak of WORLDS, not of
  results or builder states: none of them can carry it. This is a
  development of the size of `legacyRel`.
* **H2 (the new top's name is new)**: no module the cache holds, and no
  module of the result's own design, has the name of the result's module
  unless it IS that module; likewise for a built memory module. FALSE in
  general (counterexamples N, M). It holds under a condition that
  separates the DECLARATIONS a run can cache — which the compiler does not
  check at an insert and which is not decidable from one parent's reader
  data (the cache of a nested start world holds entries of unrelated
  declarations).
* **H3 (no overwrite)**: `c` is not in the cache when its own run ends.
  True of kernel-checked declarations by acyclicity of the environment;
  no theorem.

And beyond the memoised entry, `MachineKeepsCoherent` (the machine
synthesis ends coherent when it starts coherent — what (c) consumes) needs
`synthesizeChild_coherent` threaded through the harness (the translator's
instance arms call `childSynthEntry`), i.e. a `Keeps`-style pass with the
clause. With the compiler as it is, `RefLaws.aux` cannot carry it
(`auxInsert` is for every inserted value, `Tools/ShippingChildInv.lean`
342–343) — as the predecessor found.

**By the ruling: (b) is NOT shown. An endpoint whose premise is
`ChildBndC` / `MachineClosesAtC` would only have the stronger invariant as
a premise; none is written.**

### (c) CONSUMPTION — proved modulo (b)

```lean
def MachineClosesAtC … declName shape : Prop :=   -- MachineClosesAt + `CoherentAt mref cref w`
def MachineKeepsCoherent … declName shape : Prop := -- a STATEMENT: the run ends coherent
theorem machineClosesAtC_of_S (decls) (hS : MachineClosesAtS … declName shape decls)
    (hK : MachineKeepsCoherent … declName shape) : MachineClosesAtC … declName shape
theorem MachineClosesAtC.of_closes : MachineClosesAt … → MachineClosesAtC …
```

`machineClosesAtC_of_S` is `closes_of_agree`'s consumer: the end world is
coherent (`hK`), hence `CacheAgrees decls w'` for the callees
(`cacheAgrees_of_coherentAt`), hence `MachineClosesAtS` fires. With
`machineClosesAtS_of_kids` (BUILT) it gives `MachineClosesAtC mixDeep` from
`MachineKeepsCoherent mixDeep` — the latter NOT derived.

`MachineClosesAtC` is NOT `MachineClosesAt`: it asks coherence of the
START world. `MachineClosesAt mixDeep` itself (every `InvW` world) is not
derivable by this route at all — the predecessor's world
(`mid2 ↦ y_a`, `midH ↦ y_b` with another `midH` module) satisfies `InvW`;
it is excluded only by the clause.

## 4. A candidate that makes (b) short: a CHECKED insert (decision for the user/integrator)

Written BESIDE the compiler's entry (`synthesizeChildC`, in the Tools
file; nothing uses it; `Sparkle/` untouched):

```lean
def synthesizeChildC (n : Name) : MetaM Res := do
  if let some r := (← sparkleChildCache.get).get? n then return r
  let r ← synthesizeCombinational n
  let m ← sparkleChildCache.get
  if fitsB m r then
    sparkleChildCache.modify (·.insert n r)
    return r
  else
    throwError "child cache: a module of {n} has the name of a different cached module"

theorem synthesizeChildC_coherent (L) (hc : Coherent (L.val w))
    (hE : ∀ w1 r w2, L.val w1 = L.val w → RunsTo (synthesizeCombinational c) … w1 r w2 →
      Coherent (L.val w2))
    (h : RunsTo (synthesizeChildC c) … w y w') : Coherent (L.val w')
```

With the check, H1–H3 are DECIDED at the insert instead of proved, the
clause holds in every world reachable from an outermost start, and the
counterexamples N / Mc / M become a thrown error instead of a wrong design
(for N today PREDICTED silent). What landing it would cost (NOT done — a
compiler change, the user's decision; "no unverified replacements"):

* `Sparkle/Compiler/Elab.lean` 8845–8849 (`synthesizeChild`), `fitsB` in a
  new small file under `Sparkle/`;
* re-prove (they unfold `synthesizeChild`): `child_keeps`
  (`Tools/ShippingChildKeeps.lean` 282), `synthesizeChild_inv`
  (`Tools/ShippingChildRun.lean` 199), `synthesizeChild_post`
  (`Tools/ShippingCallsSame.lean` 34);
* `RefLaws.auxInsert` (`Tools/ShippingChildInv.lean` 342–343) gets the
  premise `fitsB m1 r = true` (a WEAKER law: no witness is lost); adapt
  `RefLaws.withAux` / `plain` (517–524), `pin_insert`
  (`Tools/ShippingCallsSame.lean` 106), `Tests/Compiler/ShippingCallsCloseTest.lean`.
  Then `Coherent` rides as `aux` (`coherent_insert_of_fitsB` is exactly the
  new `auxInsert`), and `childKeeps_all` / `entry_keeps_all` /
  `harness_inv` carry it through the whole compiler with NO new translator
  proof: `bodyRel`, `legacyRel`, `translateRel`, `harnessRel` are generic in
  the witness and stay as built;
* (a) then needs nothing but `aux {}` at depth 0 (`coherent_empty`; the
  `hA0` argument of `core_keeps`), so the endpoints' `ChildBnd` premise
  stays AS IT IS at depth 0;
* (c): `MachineClosesAt` still quantifies over all `InvW` worlds. Either
  `InvW` gets the clause (then every statement mentioning `InvW` /
  `CacheInv` / `StartV` / `ChildBnd` changes meaning — 21 Tools files
  mention `InvW`, 79 `ChildBnd`; the PROOFS that only pass the invariant
  along do not change, the ones that BUILD it do: `invW_of_invV`,
  `invV_of_invW`, `ChildBnd.of_invW`, `RealChild.of_inv` / `.inv`,
  `cacheInv_insert`, `Triple.clear`, `child_keeps`), or the four consumers
  of `MachineClosesAt` on `mixDeep`'s path get a `…C` variant
  (`Tools.ShippingKidFacts.kids_runFacts` 128, `kids_outsCheck` 157,
  `kids_maskedN` 188, `kids_designCheck` 222) and the generator.
* Cost not measured: `fitsB` compares, per insert, every module of the new
  entry with every cached module of the same name by `DecidableEq`
  (structural). For the Keccak sponge that is one large module compared
  once per ancestor entry.

Without the compiler change there is a second route, larger: keep the
entry, prove H1 as a result-level development, and add to the endpoint a
DECIDABLE hypothesis that the declarations of all descendants print
pairwise differently and differ from every memory name — and restrict the
closing to worlds whose cache holds only those declarations (a nested
start world with foreign entries is not covered). That restriction is a
premise about the world again.

## 5. Endpoint — premise — state

| endpoint | premise | state |
|---|---|---|
| `mixDeep.machine_design_noPortsNR2` (OPEN, BUILT) | `MachineClosesAt mixDeep` | STAYS |
| `mixDeep.machine_design_noPortsNR2_closed` | — | does not exist; not created |
| every other endpoint | — | unchanged |

`Tests/Compiler/NoPortsMixDeepClosedTest.lean` is NOT written (step 4: not
all three steps are shown).

## 6. Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingCacheCoherent» where
      roots := #[`Tools.ShippingCacheCoherent]

(The probe is under the `Tests` library; no line, target-only, NOT in
`Tests/AllTests.lean`.)

Order: (1) `Tests.Compiler.CacheCoherenceProbe` — the counterexample; read
the `CACHECOH` lines before anything else; (2) `Tools.ShippingCacheCoherent`
— independent of (1).

## 7. UNVERIFIED, in risk order

1. The probe's declarations: whether `def _root_.«#ccp.k»` /
   `_root_.«#ccp».k` elaborate with the tag and whether the entry accepts
   them (a throw is logged as `threw=T`, and then N / Nd / Mc show
   nothing); whether `memKid` (a tagged `Signal.loop` with a memory) takes
   the machine route as a child; `circuit do` over the `#` children.
2. The PREDICTIONS of §1.2 (nothing was run): `toString` equality, the
   incoherent cache, one module in the design, `MACHINE ARM … some=F`.
3. `synthesizeChildC_coherent`: the `by_cases` on `fitsB m2 r = true` with
   `simp only [hf, ↓reduceIte] at h` (copied from `core_keeps`' depth
   test), `throwError_not_runs _ h` on the interpolated message,
   `rw [hv4, hv2]` under the unreduced `fun x => x.insert c r`.
4. `fits_of_fitsB`: `Std.HashMap.mem_toList_iff_getElem?_eq_some` (needs
   `LawfulBEq Name`), `get?` against `[·]?` (definitional).
5. `crossB_sound`: the final `simpa [hn] using h2`.
6. `coherent_insert`: `rw [Std.HashMap.get?_insert] at h1 h2`, the two
   `split`s (the text of `cacheInv_insert`).
7. `synthesizeChild_coherent`, `ChildBndC.bnd`, the world lemmas: text of
   BUILT proofs (`synthesizeChild_inv`, `invV_of_invW`).
