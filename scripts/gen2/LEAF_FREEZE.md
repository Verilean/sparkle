# M2-a2 LeafStmt: freeze rev2 (rev1 1ddb25c6 reviewed: §3 approved, R1/R2 fixed)

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

## 3. Premise amendment (APPROVED 1ddb25c6; full type fixed in rev2)
`LeafStmt'` is the REGISTER-leaf lemma. It does not discharge the old all-leaf `LeafStmt`: the slotless case stays a
mandatory obligation (G-SLOTLESS in `sparkle-gen2-step`).

```
def LeafDataOkB (p : Pkg ι dom) : Bool :=
  p.d.ok && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
def LeafDataOk (p : Pkg ι dom) : Prop := LeafDataOkB p = true

def LeafStmt' {mref cref} (L : Laws mref cref) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    LeafDataOk p → ExtInS p → p.d.shape.insts = [] → p.d.shape.layout.slots ≠ [] →
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    ∀ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D
```

**Diff against the frozen `LeafStmt L DataOk`** (Defs.lean:299). Everything else is identical, binder order included:
1. the parameter `DataOk` is instantiated to `LeafDataOk` (decidable);
2. the premise `ExtInS p` is inserted after `LeafDataOk p` (the same definition as in `MemParentStmt'`);
3. the premise `p.d.shape.layout.slots ≠ []` is inserted after `p.d.shape.insts = []` (a case split; the slotless case is G-SLOTLESS).

| added premise | kind | why it is needed | supplier / open gap |
|---|---|---|---|
| `LeafDataOk p` | D (decidable) | `htake`: with `insts = []`, `callsOk_nIn` + `data_hIlen` give `bsIn.drop kD = []`. Also `hSlen`, `houtTy` and `ok` | generator `decide` per declaration; generic coverage is G-DATA (M5) |
| `ExtInS p` | semantic, as in `MemParentStmt'` | ChildShips only: `p.S` decodes `vals` directly, while the trace speaks about `extBS`/`extS`. TopShips does not need it | per declaration (generated `hextB`/`hext`); generic supply is the existing open gap "ExtInS generic supply" (M5 G3-GEN) |
| `slots ≠ []` | case split, NOT a scope cut | the trace's rst hypothesis is about `seedIn b ins t st "rst"`; with `"rst"` not an input it reads `st "rst"` (§4) | the `slots = []` case is **G-SLOTLESS** (mandatory, `sparkle-gen2-step`) |

## 4. Observation for G-SLOTLESS (read-only; NOT a kernel-proved counterexample; FG unchanged)
- **The fact.** `SeqChildRunN` (MachineDepth.lean:64-69) contains the conjuncts `"clk" ∈ mc.inputs.map (·.name)` and `"rst" ∈ …`. So it is false for any module without them.
- **What is NOT established.**
  - For `slots = []`, `closeMachine` does not add clk/rst (Machine.lean:107-109). That alone does not show the generated module lacks those names. A name guarantee that the original `t.inputs` contains no `"clk"`/`"rst"` would also be needed, and it is not proved.
  - `ChildShips` quantifies over extending designs `dsn` and over `i : ι`. It can therefore be vacuously true, for empty `ι` or when no such `dsn` exists. A claim that `ChildShips` itself is unsatisfiable would need a stated existence condition (some `i`, and some `dsn` containing `Dc` and `mc`, e.g. `dsn := ⟨mc :: Dc.modules, …⟩`).
- **What is recorded.** The existing sequential child interface cannot be applied to a generated comb module with no clock or reset input.
- **What M2-step has to decide** (recorded on `sparkle-gen2-step` by the reviewer):
  - a comb child interface and consumer, or a `ChildShips` revision;
  - compatibility with the existing sequential case;
  - the connection to ShipsRes/CacheShips/ServedP/StepStmt/T1.

  Proving slotless `TopShips` alone does not close parent use.

## 5. Non-vacuity instance (fixed)
- **The leaf.** `Tests.Compiler.SharedLeafGenTest.leaf16`, from the existing generated corpus test (SharedLeafGenTest.lean:35). It is one 16-bit register `a` (init 0, `a <~ a + x`), one bits input `x`, two outputs `s`, `odd`, and no calls.
- **Package.** `leaf16Pkg : Pkg Unit U := .gen leaf16Src`, with `ι = Unit`, `dom = fun _ => defaultDomain`, `decl := ``leaf16`, `d := leaf16.machineData` and `kD := leaf16.machineData.bsIn.length`.
- **Fields:**
  - `inits`/`body`/`obsR`/`ext`/`extB`/`src` are `leaf16.machine{Inits,Body,Result,Ext,ExtB,Source} defaultDomain`;
  - `gen` is assembled from `leaf16.machine_ok`, `machine_body`, `machine_inits`, `machine_writes`, `machine_result`, `machine_source` and `machine_ext_causal`, in the `b_wrapQ_gen` pattern (QuadCallsTest.lean:297). It is restricted to `Unit` by `genFacts_restrict`.
- **Data.** `LeafDataOk leaf16Pkg` by `decide`.
- **ExtInS.** By unfolding `leaf16.machineExt`/`machineExtB`, in the `b_wrapQ_hextB` pattern (QuadCallsTest.lean:313). With no calls, the extension at `j < kD` is the input itself.
- **Case.** `insts = []` and `slots ≠ []`, by `decide`/`rfl` on `leaf16.machineData`.
- **Result.** `leaf16_ships`, which is `leaf_ships L` applied to these, with `#print axioms`.

If a named generated theorem above does not exist for `leaf16`, the mechanical fallback is the same theorem from the generator's per-declaration output. A NAME change is recorded. If supplying any of these needs a new semantic premise, the work stops and goes back to review.

This remains a conditional instance (run hypotheses universally quantified); it does not prove that a successful run exists.

## 6. Builds and acceptance
- **Builds:** focused, issue-linked, exact-head: `kjob -N sparkle-dev run --issue sparkle-gen2-leaf -- kjob lake build sparkle_barrier sparkle_jit Tools.ShippingGen2Leaf Tests.Gen2.LeafInstance`.
- **Regression set:** the M2-a/loop-pkg regression tests (MemParentInstance, QuantInstance, PkgCompat).
- **Axioms:** only `propext`, `Classical.choice`, `Quot.sound`.
- **Not claimed:** no `slots = []` leaf, no generic `ExtInS`/`LeafDataOk` supply, no run existence.
