# The outermost form (option 3): what is written, and why the endpoint is not

Round par/a-43, base poc `258d59cc`. **WRITTEN, NOT BUILT**: nothing here was
compiled or run by its author. No built file, endpoint, premise, generator
or count changes. Option 1 is not touched.

## 0. Result, plainly

* **`mixDeep.machine_design_noPortsNR2_outermost` is NOT written.** The
  design-level consumers do not factor through "the machine synthesis of
  THIS run returned a module"; the endpoint needs their proofs restated,
  which is either an edit of built files or a copy of about 1 800 lines.
  Neither was done without a ruling.
* What IS written: the statement every consumer actually takes of the
  closing (`MachineRan`), proved once from the all-worlds premise AND at
  outermost starts; one consumer carried over as a worked example; `mixDeep`
  at outermost starts in that form, and one design-level fact of it with no
  `MachineClosesAt`.

## 1. The consumers, read line by line

`kids_runFacts`, `kids_outsCheck`, `kids_maskedN`, `kids_designCheck`
(`Tools/ShippingKidFacts.lean`) only THREAD `closes : MachineClosesAt …`
into general theorems (`core_runFacts`, `core_outsCheck_all_gate`,
`core_kidsMaskedN_top`, `core_portsMatch_raw`, `core_clk`, `core_hierGate`,
`core_kidsPass_deep`, `core_designCheck_run`), which thread it further. It
is USED in thirteen base lemmas, always by the same three lines:

    obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ := machine_run_of_core hcore entry hB
    have hne := closes bb _ _ _ hw9 hd9 hrun9
    cases r with | none => exact absurd rfl hne | some res => …

| file (`Tools/`) | base lemma | line of the use | proof lines (about) |
|---|---|---|---|
| `ShippingChecksCore` | `core_kids_facts` | 97 | 160 |
| `ShippingChecksCore` | `core_kids_factsM` | 474 | 155 |
| `ShippingChecksRaw` | `core_raw_factsM` | 178 | 110 |
| `ShippingChecksWidths` | `core_hierGateM` | 134 | 55 |
| `ShippingChecksWidths` | `core_callPortsM` | 218 | 165 |
| `ShippingClosedTyped` | `core_closed_typedIn` | 134 | 240 |
| `ShippingChecksOuts` | `core_outsExtracted` | 132 | 170 |
| `ShippingChecksRun2` | `kidsDesign_real` | 73 | 90 |
| `ShippingCoreClk` | `core_clk` | 89 | 120 |
| `ShippingKidsSelf` | `core_kids_self` | 98 | 60 |
| `ShippingHierGateAny` | `core_hierGate_any` | 74 | 60 |
| `ShippingCallsChildPorts` | `core_calls_ports₁` | 192 | 190 |
| `ShippingCallsPortsG` | `core_calls_portsG` | 107 | 205 |

After the three lines the proof (its TAIL) works from the machine
synthesis's run with result `some (M, D)` and `InvW w9`; in the two tails
read in full (`core_kids_self`, `seqChild_iface`) `closes`, `hcore`, `entry`
and `hB` do not occur again. The other eleven tails were NOT read in full.

**They do not factor.** The tails are inline; no built lemma has the form
"from the machine run of this core run, …". The world `w9` is obtained by an
existential inversion inside each proof, and all that is known of it there
is `InvW` and `DepthPos` — so a premise about `Prov` worlds cannot be used
at it, and nothing weaker than the all-worlds `MachineClosesAt` fits the
built statements.

Also read: the HEAD `Tools.ShippingNoPorts.machine_design_noPorts` IS
parametric — in the closing predicate `C` and in the boundary `Bnd` — and
needs no sibling. Its arguments are what would: the four run facts above,
and the per-declaration `soundL` / `composed` (the machine-trace and
composition theorems), which take `C` and were generated at
`C := MachineClosesAt`. Where those two use the closing I did NOT trace.

## 2. What is written — `Tools/ShippingMachineRan.lean`

```lean
def Start0 mref cref (w : Void IO.RealWorld) : Prop :=
  ∃ L : RefLaws mref cref, L.sval w = some synthesizeChild ∧ L.dval w = 0 ∧ L.quiet w
theorem Start0.childBnd (h : Start0 mref cref w) : ChildBnd mref cref w
def MachineRan mctx mref cctx cref (c : Name) (shape : MachineShape) (M) (D) : Prop :=
  ∃ (b : Bool) (w9 w10 : Void IO.RealWorld),
    RunsTo (synthesizeMachineCertified … (profLogIO b) c shape) mctx mref cctx cref w9 (some (M, D)) w10 ∧
    InvW mref cref w9 ∧ DepthPos mref cref w9
theorem machineRan_of_closes (hcore) (entry) (hB : ChildBnd mref cref w)
    (closes : MachineClosesAt mctx mref cctx cref c shape) : MachineRan mctx mref cctx cref c shape M D
theorem machineRan_outermost (hcore) (entry) (h0 : Start0 mref cref w)
    (hclose : ∀ L b w9 r w10, InvV L w9 → L.dval w9 ≠ 0 → Prov (L.val w9) →
      RunsTo (synthesizeMachineCertified … c shape) mctx mref cctx cref w9 r w10 → r ≠ none) :
    MachineRan mctx mref cctx cref c shape M D
theorem core_kids_self_ran … (ran : MachineRan mctx mref cctx cref c d.shape M D) : (the conclusion of core_kids_self)
theorem core_kids_self_of_closes … : (the BUILT statement of core_kids_self)
```

`machineRan_of_closes` is the three lines, once: the built forms are that
instance. `machineRan_outermost` is `coreVia0_of` (BUILT) with the world
facts turned into the read-based ones. `core_kids_self_ran` is the tail of
the built proof, verbatim; `core_kids_self_of_closes` shows the built
statement is its instance.

`Tests/Compiler/MixDeepOutermostRanTest.lean` (target-only):

```lean
theorem mixDeep_machineRan_outermost
    (hr : RunsTo (synthesizeCombinational ``mixDeep) mctx mref cctx cref w (b, design) w')
    (hRg hR2 hRm hRr hRc : the five reflections) (h0 : Start0 mref cref w) :
    ∃ M D w1, RunsTo (synthesizeCombinationalCore ``mixDeep [] false) mctx mref cctx cref w (M, D) w1 ∧
      (b = dropZeroWidthModule M ∨ b = mergeChecked (dropZeroWidthModule M)) ∧
      MachineRan mctx mref cctx cref ``mixDeep mixDeep.machineData.shape M D
theorem mixDeep_kids_self_outermost (same premises) :
    ∃ M D, (b = … ∨ b = …) ∧ ∀ g ∈ D.modules, ∃ k hk y, RealChild mref cref (insts[k]).1 y ∧ …
```

Neither is a design-level endpoint: the conclusions are `MachineRan` and one
structural fact of the design, not `DesignSV`.

## 3. The start premise, and the classifier

`Start0 mref cref w` is the depth-0 disjunct of `ChildBnd` named:
`ChildBnd w` is `∃ L, (L.sval w = some synthesizeChild ∧ (L.dval w = 0 ∨
CacheInv (L.val w))) ∧ L.quiet w`; `Start0 w` is the same with the left
disjunct chosen, for the same witness (`Start0.childBnd`). It cannot be
stated as "`ChildBnd w` and depth 0" with two separate witnesses: the depth
must be read by the witness whose laws are used.

The existing classifier `Tools.ShippingFinalGoalCommand.allowed` accepts
`RunsTo`, `MachineDefines`, `EntryDefines`, `ChildBnd` and conjunctions of
them, by head constant. **`Start0` is NOT ALLOWED by it** (PREDICTED by
reading; the test prints the label it computes). It was not added to the
list. An endpoint built on it would carry one premise the present
classification rejects — that is part of what a ruling on option 3 decides.

## 4. Scope, against the existing endpoints

* The existing endpoints hold from every world satisfying `ChildBnd`: a
  depth-0 start OR a nested start with an invariant cache.
* A form on `Start0` holds from depth-0 starts only.
* "A user's command starts at depth 0": by READING, not a theorem.
  `sparkleSynthDepth` is created as 0 (`Sparkle/Compiler/Elab.lean` 961),
  written only by the entry (`set (depth + 1)` at 5517, `modify (· - 1)` in
  the `finally` at 5533), and the commands call the entry directly (8906,
  8953, 9011, 9065). So between commands it reads 0. That the law witness's
  `dval` is that reading in the start world is a statement about the
  runtime, of the same kind as `ChildBnd` itself: a premise, never proved.

NOT claimed: that `mixDeep` is covered; anything at nested starts; anything
about the SV text or `#sim`.

## 5. What the endpoint needs, and the decision

To write `mixDeep.machine_design_noPortsNR2_outermost` (the head at
`Bnd := Start0`-based, `C :=` the closing at `Prov` worlds):

1. the thirteen tails over `MachineRan` (as `core_kids_self_ran`), and
   `…_ran` forms of the theorems that thread `closes` between them and
   `kids_*` (about 35 call sites in 20 files);
2. `soundL` and `composed` of `mixDeep` at that `C` — not traced.

Two ways, both mechanical:

| | how | cost |
|---|---|---|
| (i) split in place | in each built base lemma, make the tail a lemma over `MachineRan` and keep the present statement as a two-line corollary (`machineRan_of_closes`); statements unchanged | edits 11 built files (the 13 lemmas); nothing duplicated; my recommendation, as an ISOLATED branch verified like `fix/singleout-nested` |
| (ii) copy | the tails restated in new files | about 1 800 lines of copied proof that do not follow the originals when they change |

I did not do (ii) at scale because the task asked to avoid duplication, and
(i) is forbidden to me without a ruling.

## 6. Build queue (integrator)

`lakefile.lean` (not edited):

    lean_lib «Tools.ShippingMachineRan» where
      roots := #[`Tools.ShippingMachineRan]

`Tests/AllTests.lean`: nothing. Order: `Tools.ShippingMachineRan` (imports
`Tools.ShippingCacheCoherentOuter`, `Tools.ShippingKidsSelf`), then
`Tests.Compiler.MixDeepOutermostRanTest` (imports
`Tests.Compiler.MixDeepOutermostTest`, `Tools.ShippingFinalGoalCommand`);
read the `OUTERMOST` lines and the three axiom listings.

## 7. UNVERIFIED, in risk order

1. `core_kids_self_ran`: a verbatim tail under an open list copied from
   `Tools/ShippingKidsSelf.lean` minus two unused lines.
2. `machineRan_outermost`: the argument order of `coreVia0_of`.
3. The test: `mixDeep_noMem` (kernel `decide` of `memChild?` on three
   names), the three `decide`s copied from `mixDeep_closes_prov`, the
   existential statement of `mixDeep_kids_self_outermost` (`insts[k]` with
   the bound `hk`).
4. The classifier's label for `Start0` is a prediction until the test runs.

## Integrator's build record (2026-10-13) — MEASURED

BUILT on poc 258d59cc + these files, cgrun 3 GiB swap 0, runs `a43` / `a43b`. `Tools.ShippingMachineRan`:
first attempt, as written. `MixDeepOutermostRanTest`: one integrator fix — `moduleByName` lives in
`Sparkle.IR.Machine`, not `Sparkle.IR.AST` (two places in a statement). Standard axioms for
`mixDeep_machineRan_outermost`, `mixDeep_kids_self_outermost`, `core_kids_self_of_closes`.

Classifier, measured on `mixDeep_machineRan_outermost` (7 proposition binders): the run ALLOWED, the five
reflections ALLOWED, **`Start0` NOT ALLOWED**. It was not added to the allow list.

STATE: the outermost endpoint `mixDeep.machine_design_noPortsNR2_outermost` is NOT written. What exists:
the common statement `MachineRan` (both the all-worlds closing and the outermost start give it), one
consumer restated over it (`core_kids_self_ran`, with the built statement recovered as an instance), and
`mixDeep` at outermost starts in that form — not `DesignSV` conclusions, not endpoints. Completing the
form needs the tails of 13 built base lemmas over `MachineRan` (a statement-preserving split in 11 built
files, or ~1,800 copied lines) and its start premise is NOT ALLOWED by the present classifier: both are
for the reviewer (open-rulings item 1). `mixDeep` stays OPEN.
