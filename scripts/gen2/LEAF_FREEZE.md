# M2-a2 LeafStmt: freeze rev1

Issue `sparkle-gen2-leaf`.
- **Branch:** `par/gen2-spec`; base ac91f8e3.
- **Scope:** new proof and test files plus their lakefile registrations only. No production or compiler change.

## 1. Why the memory-parent route does not apply
- **Consumer 1 needs an instance.** Consumer 1 (`machine_ships_hierC_noHstR`, Srm33Core.lean:24) and its relatives (`_at_free`, `_at_nw`) need `RunFacts.gate : hierGate b = true`. They then use `hasInst_of_hierGate`.
- **A leaf has none.** `hierGate m := m.body.any isInst && …` (RefineCheck.lean:196). For `insts = []`, `MachineWired` gives `body.all seqStmtOk` (MachineEntry.lean:706). Then `hierGate_false_of_seqOk` (ChecksDerived.lean:158) shows the gate is false.
- **Existing leaf theorems are all on the OLD boundary.** These are `machine_ships`/`_checked`/`_wired`, `seqChildRun_full`, `leaf_entry_ships`, `leaf_sat` and `LeafSeqRunN`. Each takes `sound … → MachineCloses → MachineTraceL`. No A-boundary leaf ships theorem exists.
- **Their bodies are pure.** The old boundary is used once, at `sound hr entry closes`.

## 2. Route
The A-boundary input is `(Pkg.trace L.O L.T hA p ran).toLB : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc`, from `ran : MachineTaken … (dv w + 1)`. This is the same as in M2-a.

That trace feeds pure copies of the old-boundary bodies, as below. None of these steps uses `JQC (dv w) w`, `MachineDefines` or `hcore`; they stay as unused binders of the frozen statement.

### Step 1: `leaf_topShips_of_LB` (new, pure)
```
theorem leaf_topShips_of_LB (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hok : p.d.ok = true) (hSlen : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) :
    ∀ n, TopShips p n p.decl b raw D
```
The proof copies `machine_ships_wired` (ShipsW.lean:72-109) and `machine_ships` (MachineShipping.lean:105-178), with the SV parts dropped:
- **Cleanup facts** (from `MachineWired`): cleanup identity, `rstIn`, `hregs`, `hevery`, `seqStmtOk`.
- **Merge step:** `hmerge` by `mergeChecked_nonAssign`. A register exists because of `hsl`.
- **Optimizer step:** `hopt` by `checkedOptimize_seqOk`, with `simpleBody b = false` from `simpleBody_false_of` and `mergeChecked_keeps_nonAssign`.
- **Seeding:** `seedIn_of_inputs`, `declWidth_mergeChecked`.
- **Register fits:** for r0 from `hevery`/`hinitW_of_ok`; for `b` from `refineCheck_regWidth`.
- **Transfer:** `refineCheck_transfer` twice.
- **Depth:** `runModuleTG_instFree` with `instFree_of_seqOk (checkedOptimize_seqOk_all …)`. It holds for every `n`, 0 included.
- **Inputs `take kD`:** handled by `htake`.

`ResetNk`, `kids` and the `openIns` antecedent are unused.

### Step 2: `seqStream_of_LB` and `seqChildRun_of_LB` (new, pure)
- **What they copy:** `seqStream_full` (SeqChild.lean:266-469) and `seqChildRun_full` (SeqInst.lean:350-404).
- **Inputs replaced:** `hL` + `hpost` + `hext`/`hextB` (= `ExtInS p`) take the place of `sound`/`hr`/`entry`/`closes`.
- **Extra step:** one `sourceInputs_congr` (MachineEntry.lean:181), from `extBS (boolsOf vals)` to the decoded `vals`.
- **Conclusion:** `SeqChildRun b (p.d.bsIn.take p.kD) p.d.shape.layout.outs (p.S i)`.

`ChildShips p n b D` then follows from `seqChildRunN_of_flat` (MachineDepth.lean:83) for every `dsn` and `n`. The `dsn` premises are unused, because `b` is instance-free (G-TRANSPORT is trivial for leaves).

### Step 3: assembly
`leaf_ships : LeafStmt' L`, from Step 1 and Step 2 on the trace above.

## 3. Premise amendment (FOR REVIEW before use)
The frozen `LeafStmt L DataOk` takes `DataOk` as a parameter. The proof needs a concrete `DataOk` and two more premises. Following the M2-a precedent (`MemParentStmt'`), the proposal is:

```
def LeafDataOkB (p : Pkg ι dom) : Bool :=
  p.d.ok && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
def LeafDataOk (p : Pkg ι dom) : Prop := LeafDataOkB p = true

def LeafStmt' {mref cref} (L : Laws mref cref) : Prop :=
  ∀ p mctx cctx w w1 raw b D,
    LeafDataOk p → ExtInS p → p.d.shape.insts = [] → p.d.shape.layout.slots ≠ [] →
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → RunsTo … (raw, D) w1 → hpost →
    MachineDefines … → MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    ∀ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D
```

| added premise | kind | why it is needed | supplier / open gap |
|---|---|---|---|
| `LeafDataOk p` | D (decidable) | `htake`: with `insts = []`, `callsOk_nIn` + `data_hIlen` give `bsIn.drop kD = []`. Also `hSlen`, `houtTy` and `ok` | generator `decide` per declaration; generic coverage is G-DATA (M5) |
| `ExtInS p` | semantic, as in `MemParentStmt'` | ChildShips only: `p.S` decodes `vals` directly, while the trace speaks about `extBS`/`extS`. TopShips does not need it | per declaration `rfl`/unfold (generator: "without instances the extension is the inputs themselves", MachineCommand.lean:2680); generic supply is the existing open gap "ExtInS generic supply" (M5 G3-GEN) |
| `slots ≠ []` | case split, NOT a scope cut | for `slots = []`, `closeMachine` adds no clk/rst port (Machine.lean:107-109), so `seedIn b ins t st "rst" = st "rst"`. The trace's rst hypothesis then fails for an arbitrary `st0` | the `slots = []` case goes to **G-SLOTLESS** (already in `sparkle-gen2-step`); see §4 |

## 4. Counterexample-type finding for G-SLOTLESS (recorded; FG unchanged)
- **The finding.** `ChildShips` as defined is unsatisfiable for a slotless (comb) leaf. `SeqChildRun` needs `"clk"`/`"rst"` ∈ inputs, and a comb module has neither.
- **What it does not affect.** FG and T1 conclude `TopShips` only, so FG is not narrowed. `TopShips` for a comb leaf is plausible: its body never reads `"rst"`, and the comb optimizer branch is covered by `checkedOptimize_sound`, `runModule_assigns` and `mergeDuplicates_sound`.
- **What it blocks.** The child interface that a parent of a comb child consumes. That is G-SLOTLESS / G-ONEOUT work: a comb child interface, as the gate-route children (`GateRun`) in the old composition.
- **What the M2-step freeze must decide.** It must propose a `ChildShips` amendment (a disjunction with a comb child run) or a separate comb consumer. Neither is done here.
- **Why `slots = []` is not covered here.** This unit proves `LeafStmt'` for `slots ≠ []` only. The `slots = []` leaf is NOT dropped from FG; it is an obligation of G-SLOTLESS.

## 5. Non-vacuity instance
A test `Tests/Gen2/LeafInstance.lean`: one generated register leaf from the existing corpus tests. The candidate is a `.machine_*` leaf already used by `leaf_entry_ships` tests; the build picks one with `insts = []` and `slots ≠ []`. Its parts:
- the `Pkg.gen` package with `kD = bsIn.length`;
- `LeafDataOk` by `decide`;
- `ExtInS` by unfold;
- `leaf_ships L` applied, with `#print axioms`.

As in M2-a, this is a conditional instance; it does not prove that a successful run exists.

## 6. Builds and acceptance
- **Builds:** focused, issue-linked, exact-head: `kjob -N sparkle-dev run --issue sparkle-gen2-leaf -- kjob lake build sparkle_barrier sparkle_jit Tools.ShippingGen2Leaf Tests.Gen2.LeafInstance`.
- **Regression set:** the M2-a/loop-pkg regression tests (MemParentInstance, QuantInstance, PkgCompat).
- **Axioms:** only `propext`, `Classical.choice`, `Quot.sound`.
- **Not claimed:** no `slots = []` leaf, no generic `ExtInS`/`LeafDataOk` supply, no run existence.
