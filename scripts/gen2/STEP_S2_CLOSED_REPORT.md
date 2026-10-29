# S2 stop-and-report: the read-closedness of a slotless package module (STEP_IFACE_FREEZE rev3 §4 S2)

Issue `sparkle-gen2-step`.
- **Branch:** `par/gen2-spec`; base 2af2a29e. Read-only; no Lean change.
- **Why this report:** rev3 §4 S2 says "`readsClosedB` over the inputs: to be derived from the generated body; if it is not derivable from `MachineWired`, stop and report."

## Finding
1. **`MachineWired` does not give it.** `MachineWired` (MachineEntry.lean:655-706) has no conjunct about the body's reads. `linkedOk` (Machine.lean:337) is about instance outputs, not reads. Without a reads fact, a slotless module's run under `seedIn` may depend on `st "rst"` (`"rst"` is not an input), so neither S1 nor any seed change applies. The fact is needed for slotless `TopShips` and for `CombChildRunN`; it is not an artefact of the proof route.
2. **A supplier exists in the RUN, on the A boundary.**
   - `transition_closed` (TransitionClosed.lean:35-56) gives `readsClosedB (m.inputs.map (·.name)) m.body` for the TRANSITION module of the translator run. It also gives `∀ stmt ∈ m.body, ∃ l r, stmt = .assign l r`.
   - The A-boundary access to that run already exists and is built: `seqChild_ifaceA` (SeqChildIfaceA.lean:38-93, unit CPX, ba13bb58) uses `machine_run_of_coreA O hA hcore entry hw hc`, `synthesizeMachineCertified_leaf_runs hno`, `synthesizeMixedCertified_returns` and then `transition_closed`.
   - Its inputs (`AdmCtx`, `JQ`/cache start, the core run, `MachineDefines`, `ok`, `hbody`) are binders already present in `LeafStmt'`/`StepStmt` (`JQC (dv w) w`, `MachineDefines`, `GenFacts.body_eq`).
   - **One premise to check:** `seqChild_ifaceA` also takes the old `MachineCloses` (`closesM`), only to exclude the `none` result. On the A boundary that exclusion comes from `MachineTaken` (the run returned `some`). The adaptation is mechanical but must be checked in the build.
3. **Missing: carrying closedness from the transition module `t` to the shipped module `b`.**
   - **The path:** `closeLets K t = some t'` (lets become internal), then `closeMachine lay t'` with `lay.slots = []` (`body.dropLast ++ nextAssigns … ++ out assigns`, Machine.lean:98-112), then cleanup (identity, `MachineWired`), then `mergeChecked` (`mergeChecked_closed` exists, MergeClosed).
   - **The existing propagation is narrow:** `slotless_childComb` (MachineChildComb.lean:121-140) covers only `lay.outs = [o]` with `o.name = "out"` and `K ≠ 0`.
   - **The general case needs a new pure lemma:** any `lay.outs`, any `K` (with `K = 0`: `closeLets 0`).

## Proposed sub-unit S2-c (for review)
```lean
theorem slotless_closed_full {t t' b : Module} {lay : Layout} {K : Nat}
    (hcl : closeLets K t = some t') (hclosed : readsClosedB (t.inputs.map (·.name)) t.body = true)
    (hassign : ∀ stmt ∈ t.body, ∃ l r, stmt = Stmt.assign l r) (hslots : lay.slots = [])
    (hpost : b = dropZeroWidthModule (closeMachine lay t') ∨ b = mergeChecked (dropZeroWidthModule (closeMachine lay t')))
    -- plus the name facts closeLets/closeMachine need (from transition_closed / transition_facts), fixed in the S2-c freeze
    : readsClosedB (b.inputs.map (·.name)) b.body = true ∧ b.body.all isAssign = true
```
- **Its run-level supplier:** `slotless_closed_ofRun`, which gives it for `p`'s package module from `hA`, `JQC (dv w) w`, the core run, `MachineDefines`, `MachineTaken` and `p.gen.body_eq`. It ports `seqChild_ifaceA`'s first half.
- **No new premise for `LeafStmt'`/`StepStmt`:** every input is an existing binder, and S2's slotless statement uses the same binders as `LeafStmt'`.
- **If the build shows a needed fact that the run does not give, I stop again.** One example would be a name freshness of the `out` assigns that `closeMachine` adds for general `lay.outs`.

## Effect on the plan
- **S2 waits** for S2-c (freeze, then implement).
- **S4 proceeds now** (pure lemmas `evalAssigns_mems_irrel`, `childFn_of_combRun`, `combS_pointwise`, `Pkg.src_get`). S4's assign-only and closedness facts come from the PARENT's `closeInsts` (`kidsCombB`), not from S2-c.
- **S3 and S5** keep their own freezes. S5's slotless top needs S2-c's closedness too.
- **Unchanged:** FG/T1/M2 acceptance. No new residual is added.
