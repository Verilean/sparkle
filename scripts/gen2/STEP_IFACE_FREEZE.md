# M2-step part 1: the child interface for combinational children (G-SLOTLESS) — freeze rev1, FOR REVIEW

Issue `sparkle-gen2-step`.
- **Branch:** `par/gen2-spec`; base 5b93aa2f.
- **What this is:** a semantic amendment of `ChildShips`. Under the spec rules it needs review before any Lean use.
- **What it is not:** FG, T1Stmt and the M2 acceptance conditions are unchanged. No production or compiler change.

All file:line references are at 5b93aa2f, from a read-only survey that I spot-checked.

## 1. The obstruction
- **The current child interface is sequential only.** `ChildShips q n mc Dc` (Defs.lean:61-64) is `SeqChildRunN … (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i)` for every extending `dsn` and every `i`. `SeqChildRunN` (MachineDepth.lean:64-79) requires `"clk" ∈ inputs` and `"rst" ∈ inputs`.
- **A combinational module has neither port.** A slotless machine module gets no clk/rst port from `closeMachine` (Machine.lean:107-109). Its other ports are allocated names, and `nAlloc_clk`/`nAlloc_rst` (FirstGateChild.lean:517, 523) show no allocated name is `"clk"`/`"rst"`. This closes the name question left open in LEAF_FREEZE §4: the module's inputs contain neither name, once this is connected through `MachineWired`'s `Allocated` conjunct (MachineEntry.lean:660).
- **The consequence.** No `ChildShips` value exists for a combinational child at an extending design and an index. So no parent of a combinational child can obtain its child facts from `ShipsRes`.
- **No existing A-boundary consumer has a combinational branch at depth n:**
  - group parents: `calls_hchildRN` (CallsLinkedTNR.lean:46), `machine_linkedT_callsRNA` (DepthRunRA.lean:142) and the gen2 copy `machine_linkedT_callsServed` (Gen2Consumer) all take `MemFacts ∨ SeqFactsRN`;
  - the three-way `calls_hchildRG` (CallsLinkedTG.lean:257) is depth 0, on the old boundary;
  - one-output parents: `machine_linked_callsRA` (ComposeRA.lean:72) takes `hfn : ChildFn` for every run of the callee, not served results.

## 2. Proposed amendment (A-COMB)
```lean
/-- A combinational child run at depth `n`: `SeqChildRunN` without its clock/reset part. -/
def CombChildRunN (children) (dsn : Design) (n : Nat) (mc : Module)
    (bsC : List (Name × MixedGateBinder)) (outsC : List OutField) (S : (Nat → List Nat) → List (Nat → Nat)) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧
  "clk" ∉ mc.inputs.map (·.name) ∧ "rst" ∉ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (argPorts mc).length = (bsC.filter fun b => b.2 != .domain).length ∧
  ∀ (T : Nat) (ins : Nat → String → Nat) (s : KT n) (vals : Nat → List Nat),
    (∀ τ, τ < T → InRange (vals τ) (bsC.filter fun b => b.2 != .domain)) →
    (∀ t, t < T → (argPorts mc).map (fun p => ins t p.name) = vals (T - 1 - t)) →
    ResetN dsn n mc s →
    ∃ envs, RunOn children n mc (seedIn mc ins) T s = some envs ∧ envs.length = T ∧
      ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
        outsC[k]? = some o → (S vals)[k]? = some f → (envs[j]'hj) o.name = f j

def ChildRunN (children) (dsn) (n) (mc) (bsC) (outsC) (S) : Prop :=
  SeqChildRunN children dsn n mc bsC outsC S ∨ CombChildRunN children dsn n mc bsC outsC S

-- ChildShips: SeqChildRunN replaced by ChildRunN; nothing else changes
def ChildShips (q : Pkg ι dom) (n : Nat) (mc : Module) (Dc : Design) : Prop :=
  ∀ dsn, (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
    moduleByName dsn.modules mc.name = some mc →
    ∀ i, ChildRunN (childMap dsn.modules) dsn n mc (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i)
```

**Why this form:**
- **The two disjuncts exclude each other.** One has `"clk" ∈ inputs`, the other `∉`. A consumer selects the branch from the module (`isSeqChild`, InstStmtG.lean:20), as the depth-0 three-way consumer does (CallsLinkedTG.lean:29-30).
- **The same interface data.** `bsC`, `outsC` and `S = q.S i` are kept, so `CallDec`, `MemDec`, `ServedP` and the call decoding are untouched.
- **`ResetN` is kept.** Consumers already supply it for every instance (CallsLinkedTNR.lean:57; `ComposedNWRegs`). For an assignment-only module it carries only the memory/kid parts.
- **Not weaker for sequential children.** The left disjunct is exactly the old predicate.

**The alternative, rejected:** a single predicate with `isSeqChild mc → clk ∧ rst ∈ inputs`. It would change the sequential runner `seq_inst_runN` (MachineDepth.lean:98) and every `SeqChildRunN` producer. The disjunction makes compatibility a single `Or.inl`.

## 3. Reach of the change and compatibility
- **Where `ChildShips` is used.** `ShipsRes`/`ShipsAt` (Defs:101, 114); through them `CacheShips`, `InvAt`, `IHAt` (in both premise and conclusion), `BodyKeepsInv`/`ChildKeepsInv`/`KeepBody`/`KeepChild`, `ServedP`/`ServedPC` and `ServedShipsStmt`; and the conclusions of `StepStmt`, `MemParentStmt(')`, `LeafStmt(')`. It is not used in `T1Hyp` or `T1Stmt`.
- **Proved theorems.** `memParent_childShips` (Gen2MemShips.lean:49) and `leaf_childShips_of_LB` (Gen2Leaf.lean) each change by one `Or.inl` at their final `exact`. Their statements and the instance tests are unchanged as text.
- **`Tests/Gen2/PkgCompat.lean`.** `Old.ChildShips` is the frozen pre-Pkg text.
  - The `rfl`/`_eq` checks for `ChildShips` and everything built on it stop being equalities.
  - The NEW→OLD `*_compat` implications stop being valid, because `ChildShips` occurs in premise position (`IHAt`, `ServedP` in `StepStmt`).
  - **Proposal:** record A-COMB in GENERAL_SPEC §0 as a semantic amendment, and re-baseline PkgCompat's `Old.*` at the A-COMB text. The Pkg-refactor `rfl` checks are kept, now against a copy that already contains `ChildRunN`.
  - **Added test:** `SeqChildRunN → ChildRunN`, plus a mutual-exclusion lemma (`¬ (SeqChildRunN ∧ CombChildRunN)` for a module with distinct inputs).
  - **Under review:** whether the reviewer prefers instead to keep `Old.*` and state one-directional `Old.ChildShips → ChildShips` facts only where the position is positive.

## 4. Units this amendment opens (all inside `sparkle-gen2-step`, G-SLOTLESS; each frozen before Lean)
| unit | content | existing pieces | missing (to be proved) |
|---|---|---|---|
| S1 `runModule_seed_local` | reset irrelevance: an assignment-only, memory-free body closed over its reads gives the same run under seeds that agree on its inputs | `evalAssigns_local` (HierOptRunH:36), `regNexts_assigns`/`applyNexts_nil` (ShipsComb:38-57), `readsClosedB_eq` (DepthHR:25) | the lemma itself |
| S2 slotless leaf `TopShips` + `CombChildRunN` | from the A-boundary trace, `ExtInS`, `insts = []`, `slots = []`, `hpost`: `TopShips` and `ChildShips` (right disjunct) at every `n` | `traceL_of_LB`, `seedR` (ShipsComb:30), `runModule_assigns`, `mergeDuplicates_sound` (PostSoundness:411), `checkedOptimize_sound` (OptSoundness:301), `RunOn_instFree`, `runModuleTG_instFree` | `combChildRunN_of_LB`, slotless `leaf_topShips`; the `ChildComb`-style closedness of the package's module from `MachineWired` (the existing `slotless_childComb_full` covers one output with lets ≠ 0 only) |
| S3 group-parent consumer | the three-way per-instance premise at depth n on the A boundary: `MemFacts ∨ SeqFactsRN ∨ CombFactsRN`; `comb_inst_runN` via `runKS_RunOn` + `RunOn_instFree` | `seq_inst_runN` (Depth:98), `gate_inst_run` (CallsLinkedTG:126, depth 0) | `CombFactsRN`, `comb_inst_runN`, `calls_hchildRNC`, a `machine_linkedT_callsServedC` (`ChildRunN` in place of `SeqChildRunN`) |
| S4 one-output parents | `childFn_of_combChildRunN` (T = 1); a served version of `machine_linked_callsRA` (`hfn` from `ServedP (ShipsRes …)`); `composedNWn_of_H` (DepthHR:208) to depth n | `machine_linked_callsRA`, `composedNWn_of_H`, `closeInsts_kidsComb` | the two lemmas; this is G-ONEOUT |
| S5 slotless parents/top | a slotless module's own `TopShips`: `RunFacts.rst` (GuardsSound:321) requires `"rst"`, so consumer 1 needs a no-rst variant; slotless parent `ChildShips` through `CombChildRunN` (C6's `hsl` is the blocker, Gen2C6:28) | `hierRefineCheck_linkedH_noRst` (HierOptRunHNoRst:56), `refineCheck_transfer_noReg` (RefineNoRst:224) | a no-rst consumer 1 and `combChildRunN_of_composedH` |
| S6 connection | `ShipsRes`/`CacheShips`/`ServedP`/`StepStmt`/T1 restated with A-COMB; PkgCompat re-baseline; the memParent/leaf `Or.inl` updates | — | the edits and the rebuild |

**Not in scope here (recorded for gen4 routes).** Gate-route children have no `Pkg`: `T1Hyp.defines` needs `MachineDefines` (Defs:177). A machine-route parent that calls a gate-route child therefore depends on a route that T1's package assignment does not cover. This is not new; it belongs to gen4 route coverage. A future gate package could reuse `CombChildRunN` through a `GateKidRun → CombChildRunN` lemma. Nothing is dropped from FG.

## 5. Order, and the rest of M2-step
1. Review of A-COMB (this document).
2. S6 definition edit plus the compatibility updates, built together.
3. S1, then S2. These close the slotless leaf, both `TopShips` and the child interface.
4. S3 and S4 (G-SLOTLESS parents, G-ONEOUT).
5. S5.
6. Then the StepStmt route: G-LIFT, G-TRANSPORT, mixed G-BD/G-RUNFACTS and `seqFactsRN_of_callDec`/U-ADAPT. It consumes `ChildRunN` via S3/S4, in its own freeze.

## 6. Not claimed
No Lean is changed by this document. Nothing here is proved; the existing pieces listed above are used only as read.
