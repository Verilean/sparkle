# PARAM_INV_ESTIMATE: the translator-wide invariant for F-kids, its statement, and a size estimate

Status: study and statement only. No Lean source in the tree is edited; no theorem of F-kids is proved. Base 27417c9f
(par/param-inv). Ledger: FG 92 / T1 57 (this unit: FG -0 +0 / T1 -0 +0). Accepted counts unchanged.
"Counted" = produced by `grep`/`wc`/`awk` in this unit. "Read" = my reading of code, not checked by Lean.

## 0. Result in short

* The invariant is **state-level plus world-level**: `StatePF cs := ∀ x ∈ cs.design.modules, x.parameters = []`, and a
  predicate on the two caches that can hand back a `(Module × Design)` (`WorldPF`, §1). The state part alone is not
  enough (§2.3): a cache hit returns a pair that no `CircuitState` mentions.
* The statements of §1 elaborate (scratch build, exit 0, no `sorry`, §1 end). Proved in the scratch: `Design.empty`,
  `Design.addModule`, `CircuitM.init`, `CircuitM.addModuleToDesign`, `CircuitM.addParameter` leaves `design` unchanged
  (`rfl`), and the `CompilerM.addModuleToDesign` wrapper at the run level. The recursive part is **not** proved.
* Size (§3): the translator reaches about 100 definitions (counted: 17 in the `Rec` block, 82 in the step/instance
  block, plus the entry blocks); each needs a preservation lemma or a combinator application. An existing walk of this
  shape (`ShippingGateDesignWalk`, 1203 lines) covers only four node kinds. My estimate is several thousand lines;
  see §3.4 for the basis and the uncertainty.
* **One point needs a decision before any proof starts (§4):** the invariant must talk about the contents of
  `sparkleSubModuleCache` (the memo, "G-MEMO") and of `sparkleChildCache`. The tree has `RefLawsM`
  (`Tools/ShippingMemoLaws.lean`) whose header says it **extends the trust base**. This study did not find a way
  to state the invariant without it. Whether the F-kids route may use `RefLawsM` is a boundary/law question, so it is
  not decided here.

## 1. The statement, as a complete Lean text (elaborated in scratch)

`CompilerM := ReaderT CompilerState (StateT CircuitState MetaM)` (Elab.lean:94). A step is run in a fixed
Meta/Core context and a world; the world is indexed because cache contents are read from the world
(`RefLawsM.val` for `sparkleChildCache`, `RefLawsM.mval` for `sparkleSubModuleCache`).

* `StepPF L m`: every returning run of the CompilerM action `m` from a world with `WorldPF` and a state with
  `StatePF` ends in a world with `WorldPF` and a state with `StatePF`.
* `TranslatePF L T`: `StepPF` for every call of the translator `T`.
* `EntryPFAt L r`: the depth-bounded entry statement for a non-symbolic child (`synthesizeCombinational`): with
  remaining depth budget `r`, a returning run yields `PairPF (M, D)` and keeps `WorldPF`.
* `TranslateFuelPF L r`: `EntryPFAt L r → TranslatePF L (translateFuelFix (translateStep env) k)` for every `k`
  (the translator is a fuel fixpoint, Elab.lean:8247-8873, so induction on `k` is available; this is the step form).

The depth recursion (the induction the F-kids route needs): `EntryPFAt L r` for the child is proved from
`TranslateFuelPF L (r-1)` for its body, since a child runs at depth `dval + 1`; `EntryPFAt L 0` is vacuous because the
entry throws at `depth ≥ sparkleSynthDepthLimit` (Elab.lean:5465, read; `sparkleSynthDepthLimit = 1024`, Elab.lean:970).
The top call then needs only the symbolic top (F-kids §4 step 3): `finishSynth_symbolic`
(Tools/ShippingGen4ParamEntry.lean:112, exists) gives `D = fcs.design`, so `StatePF fcs` gives the design half.

Scratch text (file `Tests/Gen4/ParamInvScratch.lean`, built once with `kjob lake build Tests.Gen4.ParamInvScratch`,
exit 0, 704 jobs, no `sorry`; lakefile entry and file removed afterwards, not committed):

```lean
import Tools.ShippingGen4ParamIface
import Tools.ShippingTranslateSoundness
import Tools.ShippingMemoLaws
set_option autoImplicit false

namespace ParamInvScratch
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingMemo
open Tools.ShippingGen4ParamEntry (Tsyn)

/-! ## 1. predicates -/
def ParamFree (m : Sparkle.IR.AST.Module) : Prop := m.parameters = []
def DesignPF (D : Design) : Prop := ∀ x ∈ D.modules, ParamFree x
def StatePF (cs : CircuitState) : Prop := DesignPF cs.design
def PairPF (r : Sparkle.IR.AST.Module × Design) : Prop := ParamFree r.1 ∧ DesignPF r.2

section
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- the two caches that can hand a (module, design) back: contents are PairPF -/
def WorldPF (L : RefLawsM mref cref) (w : Void IO.RealWorld) : Prop :=
  (∀ n r, (L.val w).get? n = some r → PairPF r) ∧
  (∀ n r, (L.mval w).get? n = some r → PairPF r)

/-- one run of a CompilerM action, world-indexed -/
def CRun {α : Type} (m : CompilerM α) (ctx : CompilerState) (s : CircuitState)
    (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (a : α) (s' : CircuitState) (w' : Void IO.RealWorld) : Prop :=
  (m ctx s) mctx mref cctx cref w = EST.Out.ok (a, s') w'

/-- the preservation form for one CompilerM action -/
def StepPF (L : RefLawsM mref cref) {α : Type} (m : CompilerM α) : Prop :=
  ∀ (ctx : CompilerState) (s : CircuitState) (mctx : Meta.Context) (cctx : Core.Context)
    (w : Void IO.RealWorld) (a : α) (s' : CircuitState) (w' : Void IO.RealWorld),
    CRun m ctx s mctx mref cctx cref w a s' w' → WorldPF L w → StatePF s →
    WorldPF L w' ∧ StatePF s'

def TranslatePF (L : RefLawsM mref cref) (T : TranslateFn) : Prop :=
  ∀ e hint top named, StepPF L (T e hint top named)

/-- the depth-bounded entry statement for non-symbolic children -/
def EntryPFAt (L : RefLawsM mref cref) (r : Nat) : Prop :=
  ∀ (declName : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
    (M : Sparkle.IR.AST.Module) (D : Design),
    sparkleSynthDepthLimit ≤ L.dval w + r →
    RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M, D) w' →
    WorldPF L w → WorldPF L w' ∧ PairPF (M, D)

/-- the translator-wide preservation, given the child entry at one less budget -/
def TranslateFuelPF (L : RefLawsM mref cref) (r : Nat) : Prop :=
  EntryPFAt L r → ∀ (env : Environment) (k : Nat),
    TranslatePF L (translateFuelFix (translateStep env) k)
end

/-! ## 2. proved small pieces -/
theorem designPF_empty (n : String) : DesignPF (Design.empty n) := by
  intro x hx; simp [Design.empty] at hx

theorem designPF_addModule {D : Design} {m : Sparkle.IR.AST.Module} (hD : DesignPF D) (hm : ParamFree m) :
    DesignPF (D.addModule m) := by
  intro x hx
  simp only [Design.addModule, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hD x hx
  · exact hm

theorem statePF_init (n : String) : StatePF (CircuitM.init n) := designPF_empty n

theorem statePF_addModuleToDesign {cs : CircuitState} {m : Sparkle.IR.AST.Module}
    (hs : StatePF cs) (hm : ParamFree m) :
    StatePF ((CircuitM.addModuleToDesign m cs).2) := by
  unfold StatePF at *
  exact designPF_addModule hs hm

theorem addParameter_design (n : String) (v : Nat) (cs : CircuitState) :
    ((CircuitM.addParameter n v cs).2).design = cs.design := rfl

theorem statePF_addParameter {cs : CircuitState} (n : String) (v : Nat) (hs : StatePF cs) :
    StatePF ((CircuitM.addParameter n v cs).2) := by
  unfold StatePF; rw [addParameter_design]; exact hs

/-- the CompilerM wrapper of addModuleToDesign, world-indexed, at the state level -/
theorem compiler_addModuleToDesign_state {m : Sparkle.IR.AST.Module} {ctx : CompilerState}
    {s s' : CircuitState} {u : PUnit} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (h : CRun (CompilerM.addModuleToDesign m) ctx s mctx mref cctx cref w u s' w') :
    s' = (CircuitM.addModuleToDesign m s).2 := by
  unfold CRun at h
  change EST.Out.ok (PUnit.unit, (CircuitM.addModuleToDesign m s).2) w = _ at h
  cases h
  rfl

theorem compiler_addModuleToDesign_pf {m : Sparkle.IR.AST.Module} {ctx : CompilerState}
    {s s' : CircuitState} {u : PUnit} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (h : CRun (CompilerM.addModuleToDesign m) ctx s mctx mref cctx cref w u s' w')
    (hs : StatePF s) (hm : ParamFree m) : StatePF s' := by
  rw [compiler_addModuleToDesign_state h]
  exact statePF_addModuleToDesign hs hm

end ParamInvScratch
```

What the scratch proves (and nothing more): `designPF_empty`, `designPF_addModule`, `statePF_init`,
`statePF_addModuleToDesign`, `addParameter_design` (`rfl`), `statePF_addParameter`, and the run-level wrapper
`compiler_addModuleToDesign_pf`. `StepPF`, `TranslatePF`, `EntryPFAt`, `TranslateFuelPF` are definitions (Props); no
theorem uses them. The names are ones I chose; none exists in the tree.

## 2. What the invariant has to cover (read)

### 2.1 Where `design` can change (counted/read)
* `grep` for `addModuleToDesign` in Elab.lean: the definition (294) and the call sites 6624, 6628 (legacy instance arm),
  8519 (`instAddModules`), 8561 (`instRegisterChild`). Every added module is a `subDesign.modules` element or the
  `subModule` of a child entry's result (`synthesizeCombinational`/`childSynthEntry`/`sparkleChildSynth`).
* Whole-state writes in the translator: `withLocalDecl`/`withLetDecl` (`set newS`, 141/150: state of a sub-run, so the
  invariant holds by the sub-run's own step lemma), `set s0` (8647: restores an earlier state of the same run),
  6773 (`{ cs with module := … }`: design untouched). `modify` of `translateRecord` (6698, 8053): design untouched.
  `try … catch` in a StateT-over-MetaM program restores the state at the `try` (read from the `StateT` instance, not
  checked in Lean here).
* `CircuitM` primitives in Builder.lean (counted: 27 `def`s; the ones used by the translator are `freshName`,
  `makeWire`, `emitAssign`, `emitRegister`, `emitMemory`, `emitInstance`, `addInput/Output`, `addParameter`,
  `bindSourceVariable`): none but `addModuleToDesign` mentions `design` (counted by `grep design Builder.lean`: lines
  24, 62, 76-78, 82, 411-420).

### 2.2 Where children come from
`synthesizeCombinational n` (legacy arm, 6586/6598), `childSynthEntry`/`synthesizeChild` (8929-8934, through the
`sparkleChildSynth` ref), and `closeInstsM`/`closeInstsGM` (5206-5250, `sparkleChildSynth` again, plus memory modules
`o.child?`). Each result is handed on by `Sparkle.IR.Machine.closeInsts/closeInstsG` (Machine.lean:396 ff.) into a
design. So a Machine-side lemma "`closeInsts`/`closeInstsG` keep `DesignPF` when the children are `PairPF` and the memory
module has `parameters = []`" is needed (not read to the end; `designWith` at Machine.lean:399).

The child's *own* output goes through the full entry: `synthesizeCombinationalCoreWith … [] false` then
`dropZeroWidthModule` and `mergeChecked` (Elab.lean:5594-5605). By reading, `dropZeroWidthModule` is
`{ m with body, wires }` (ZeroWidth.lean:113-118), `mergeDuplicates` is `{ m with body, assertions }` or `m`
(RegDedup.lean:297-311), `finalize` reverses `parameters` (AST.lean:405), and `addClockResetIfSequential` uses
`addInput`: so `parameters` is preserved. `mergeChecked` has `mergeChecked_cases` (RefineCheck.lean:280, a disjunction
`mergeDuplicates m ∨ m`); the first alternative's field-preservation lemma is new. Counted: a `parameters` keep lemma
for each of 4 functions.

### 2.3 Why the state predicate is not closed on its own
The route that returns a ready-made pair without running the translator body is the memo hit at Elab.lean:5334-5338
(`if !symbolicMode … return cached`) and `synthesizeChild`'s cache read (8930). The pair comes from the ref's content,
which no `CircuitState` records. Writers: `sparkleSubModuleCache.modify (·.insert declName result)` at 5297, 5304,
5323, 5388, and `sparkleChildCache.modify` at 8932; both are `.set {}` at depth 0 (5540-5541).
The key is the declaration name only (as `Tools/ShippingMemoInv.lean` says, header). For `PairPF` that does not hurt:
every writer stores the result of a run with `parameters = []` and `symbolicMode = false` (caller grep in F-kids §1:
only 5594 and 8943 call the core; 8943 is the symbolic top, which does not store, 5388 is guarded by
`!symbolicMode` and the three certified arms need `!symbolicMode`, read in `certifiedShape?`/`mixedCertifiedShape?`).
So the memo/cache invariant is "every entry is `PairPF`", which a write of a `PairPF` result keeps. Stating it needs
the ref laws.

## 3. Size estimate

### 3.1 What I counted
* Elab.lean: 9513 lines (`wc -l`).
* `Rec` block (translator handlers, parameterised by the recursive call): lines 5702-8030, **17 `def`s, about 2330
  lines**. Largest: `translateExprToWireImpl` (6930-7992 incl. neighbours, ≈1030), `handleDefinitionUnfold`
  (6401-6804, ≈400), `translateExprToWireApp` (6804-6921), `handleLoop` (6125-6240), `handleMemory`, `handleCircuitMonad`.
* Step/instance block 8030-8960: **82 definitions, ≈830 lines up to `translateFallback` (8860)**; the largest are
  `translateInstanceOrFallback` (66), `translateProjInstanceUncachedWith` (50), `fallbackKind` (46, pure),
  `translateFallback` (43), `translateBoolUncachedWith` (41), `translateInstanceUncachedWith` (36).
* Control-flow forms inside 5702-8860 (counted by `grep`): `for` 8, `try` 19, `catch` 16, `with*` scope combinators 24,
  `let rec`/`where` 7, `liftMetaM` 110, `addModuleToDesign` 4. `forM/mapM`: 0 in this range.
* Entry side: `bindInputsLegacy` (2115), `emitLeaves` (2157), `finishSynth` (2218), `synthesizeCertified`/
  `synthesizeMixedCertified` (2934/2959), `closeInstsM/GM` (5206/5229), `synthesizeMachineCertified` (5252),
  `synthesizeFromConst` (≈5290-5400), `synthesizeCombinationalCoreWith` (5423-5590), the three post-processing passes.
* The machine route uses `partial def`s (`mach*`, Elab.lean:3888-4968, counted 8): they are opaque to the kernel. They
  run on pure data and do not touch `CircuitState.design`, so the invariant would need *no* lemma about them, only that
  the routes calling them are covered by the child-pair argument (read; not checked).

### 3.2 What already exists and what it gives (read)
* `RunsTo.bind/ite/try_finally`, `peel_bind`, `peel_ite`, `peel_lift` (Tools/ShippingEntrySoundness.lean:937-1030):
  the peel infrastructure on `MetaM` runs; I3b `core_symbolic_reads` (Tools/ShippingGen4ParamEntry.lean:216) peels the
  symbolic core down to `synthesizeFromConst`; `finishSynth_symbolic` (112) handles the last step. These cover the top
  prologue, not the legacy body.
* `Returns.bind/pure/get/set/liftMetaM` (Tools/ShippingTranslateSoundness.lean:59-113): `CompilerM`-level run
  combinators over `CircuitState` (existential world). `StepPF` needs the same combinators with the world kept, i.e. a
  world-indexed copy (new, small: five or six lemmas; the existing proofs are about 50 lines).
* `fuelFix_correct` (same file, header item 3): the generic fuel induction.
* `ShippingGateDesignWalk.lean` (1203 lines, counted): a design-level state invariant `DOk`/`DesW` proved "world by
  world" along the translator's fuel walk, but only for gate-route cones (`desW_fvar`, `desW_binary`, `desW_compare`,
  `desW_inst`). It is the closest model; it is not reusable as is, since its `DOk` has 8 conjuncts about shapes
  that a general run does not satisfy.
* `RefLaws` / `RefLawsM` (Tools/ShippingChildInv.lean:333, Tools/ShippingMemoLaws.lean:90) and the memo statements
  of `Tools/ShippingMemoInv.lean` (215 lines; generic `memoInv_of_empty/_reset/_frame/_read/_write/_hit` PROVED, per
  its header; the writing arms' obligations `ArmObligations`/`MemoSound` are statements only).
* `Kids*` (`ShippingKidsChildIface.lean`, 394 lines, `synthesizeCombinational_designL`, `map_other`): results for
  fixed declaration shapes; `map_other` is already used by I4-struct. Not a design-wide invariant.
* `RefLaws` tracks three values only (child cache, synthesis ref, depth); "the seven side maps' contents" have no lemma
  (PARAMETRIC_FREEZE.md:353). `RefLaws.aux` is a proof-side predicate of the child cache map with a closure condition
  `auxInsert`; whether `PairPF` can ride in it is **not checked**: `auxInsert` is stated for an arbitrary inserted `r`.

### 3.3 What is new
1. World-indexed run combinators for `CompilerM` (bind/pure/get/set/liftMetaM/ite/match/for-in/try-catch/tryFinally/
   withReader/withLocalDecl). ~300-500 lines (guess from the sizes of the existing `Returns.*` block).
2. A `StepPF` lemma for each `CompilerM` primitive wrapper (Elab.lean:170-305, ≈20) — all by "design field unchanged"
   (`rfl`-class), one generic lemma over a field-preserving state map plus ≈20 one-line instances; `addModuleToDesign`
   as scratch.
3. A `StepPF` lemma for each of the ≈100 translator definitions (17 `Rec` + ≈82 step/instance). The 82 are small
   (median ≈8 lines, counted); the preservation proof follows the code with combinators. The 17 `Rec` defs are large
   and mostly `liftMetaM`/`makeWire`/`emitAssign` sequences with `try/catch`; the heavy ones are
   `translateExprToWireImpl`, `handleDefinitionUnfold`, `handleLoop`, `handleCircuitMonad`.
4. The instance arms (`instAddModules`, `instRegisterChild`, legacy arm 6620-6628): where `design` actually changes;
   each needs `PairPF` of the child pair as the input fact. Small (4 sites).
5. The child-entry side: `EntryPFAt` for the legacy, certified (`synthesizeCertified`), mixed, and machine routes
   (`closeInsts`/`closeInstsG` + memory modules) and the 3 post-processing passes' `parameters` keep.
6. The memo/cache world invariant and its preservation across every `MetaM` step (needs §4).
7. The top call (small, given `finishSynth_symbolic`) and the name-collision link of F-kids §4 step 1.

### 3.4 Estimate (not a measurement)
Counting 1: ~400 lines; 2: ~100; 3: the 82 small defs at ~15 lines of proof each ≈ 1200, the 17 `Rec` defs at ≈ 1/3 of
their source length ≈ 800 plus the four heavy ones with extra case analysis; 4: ~150; 5: ~500-800 (four routes);
6: ~300-500 plus the §4 question; 7: ~150. **Total roughly 3500-5000 lines of Lean, i.e. larger than anything in
the M4 parametric bridge so far** (the unit-6 bridge file set is hundreds of lines; `ShippingGateDesignWalk` is 1203
lines for four node kinds). The per-line rate is a guess from existing files, not from timing. Build cost: the
translator-facing files elaborate slowly; the `core_symbolic_reads` theorem needs `maxHeartbeats 1600000`
(ParamEntry:215), so I expect several files with raised heartbeats and splitting by `Rec` handler.
The size is driven by *coverage of every handler*, not by the depth of the argument; each step is "design is not
touched". I did not find a way to avoid walking the handlers (a program-wide frame principle would need an edit of the
production monad, which is out of scope for this unit).

## 4. The point that needs a decision first: the memo/cache world invariant

* The invariant needs facts about `readOf sparkleSubModuleCache w` and `readOf sparkleChildCache w`. The tree's
  vocabulary for these is `RefLaws` (child cache, synthesis ref, depth) and `RefLawsM` (adds the memo). `RefLawsM`'s
  header: "This file EXTENDS the trust base … A theorem under `RefLawsM` is a theorem under MORE assumptions than one
  under `RefLaws`" and `distinct` is "NOT provable in the logic".
* I did not determine (a) whether the parametric chain's existing premises (I3b/I3c, `RefLaws`) already include
  `RefLawsM`'s memo fields, (b) whether `ChildBnd`/`RefLaws` is a ledger item for M4 and which. The files I read for
  the parametric side (`PARAMETRIC_FREEZE.md:33, 353`) say the symbolic top neither reads nor writes the memo and
  that the memo contents have no lemma; they do not say what a *child* run needs, which is what F-kids needs.
* Options (no choice made here):
  | option | what it needs | ledger/trust effect | note |
  |---|---|---|---|
  | A. use `RefLawsM` as it is | the memo laws as parameters of the F-kids theorem | adds the `RefLawsM` fields to the theorem's premises; whether they are ledger rows is not checked | a new law use → reviewer/user |
  | B. carry `PairPF` in `RefLaws.aux` for the child cache and show memo hits never occur for the parametric top's descendants | a proof that no child reads the memo, or a memo-free argument | no new law if it works | not checked; the memo is read for any non-symbolic child (5334) so a miss proof needs the reset at depth 0 and a "first writer" argument — G-MEMO is open for M3 as well (GENERAL_SPEC.md:255) |
  | C. guard in the production entry (F-kids §5 (c)) | production edit | out of scope | not allowed in this unit |
  Reversibility: all three are reversible before a proof exists. If not decided, the F-kids invariant stays a
  statement and B.P-8/B.P-1 are not reduced.

## 5. The other items, in the same frame (one line each)

* **F-θ** (parameter names are Nat binders, no duplicates): not part of this invariant. It is a fact about the top
  prologue (`dupParams`, `core_symbolic_prologue` exists) and `synthesizeFromConst`'s `foundNatBinder` loop; separate
  work, small, and independent of the translator walk.
* **F-top** (the top module's name/shape vs. the `D.addModule b` assembly): a different statement
  (`M.name`, collision refusal `ModuleNameCheck.check`); it shares one link with F-kids (the `x.name ≠ M'.name`
  guard is vacuous when the name check holds), which needs a Lean statement of `ModuleNameCheck.check` (new, small).
  Otherwise separate.
* **F-post** (post-processing keeps `parameters`/names): the same kind of field-preservation lemmas as §2.2
  (4 functions); it can share the `ParamFree`-keeps lemmas written for the child side, so it is *in* this frame at
  low cost, but its own premises (zero-width, merge) are not exercised here.
* **shape** (`D` vs `D.addModule b`, `SrcAt`): another job. It is about which design `specializeDesign` sees; it does not
  use `StatePF`.
* **assembly** (`LegalBinding D θ` from F-θ + F-top + F-kids + F-post): glue over `legalBinding_covers`
  (approved); depends on all four above; no new invariant.

Net: only F-kids (and the F-kids half of F-post) need the translator walk. The rest are separate, smaller proofs.

## 6. Ledger prospect

Nothing is accepted by this study. Conditional on F-θ, F-top, F-kids, F-post, shape and assembly all being proved with
no new premise: B.P-8 -1, B.P-1 -1 (reviewer's instruction). F-kids alone: 0. If Option A of §4 is the only route,
the premise count may go up by the `RefLawsM` memo fields (not counted; whether they are already in the ledger is the
open question in §4), which could cancel the reduction.

`台帳: FG 92 / T1 57（今回 FG -0 +0 / T1 -0 +0）`
`条件付き台帳: B.P-8 -1 / B.P-1 -1（全項目の証明が揃った場合のみ。F-kids 単独は 0。§4 の memo 法則の扱い次第で相殺の可能性あり）`

## 7. Limits

* Statements elaborate; only the small pieces of §1 are proved. Counts are from `grep`/`wc`/`awk` over the base tree;
  the line estimate of §3.4 is a guess.
* §2/§3.2 are reading. I did not read `translateExprToWireImpl`, `handleDefinitionUnfold`, or the `Machine.closeInsts*`
  bodies to the end, and did not search `Tools/` copies of the compiler (as in the F-kids study).
* No counterexample to F-kids was looked for here; "no reason found to doubt it" is the status from the previous study.
