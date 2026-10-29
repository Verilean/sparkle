# M2-step part 1: the child interface for combinational children (G-SLOTLESS) — freeze rev3, FOR RE-REVIEW (rev1 b60e3980: A-COMB approved; rev2 b7f85204: plan approved, R1 source-output supplier and R2 .gen-restricted compat fixed here)

Issue `sparkle-gen2-step`.
- **Branch:** `par/gen2-spec`; base 5b93aa2f.
- **What this is:** a semantic amendment of `ChildShips`. Under the spec rules it needs review before any Lean use.
- **What it is not:** FG, T1Stmt and the M2 acceptance conditions are unchanged. No production or compiler change.

All file:line references are at 5b93aa2f, from a read-only survey that I spot-checked.

## 1. The obstruction
- **The current child interface is sequential only.** `ChildShips q n mc Dc` (Defs.lean:61-64) is `SeqChildRunN … (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i)` for every extending `dsn` and every `i`. `SeqChildRunN` (MachineDepth.lean:64-79) requires `"clk" ∈ inputs` and `"rst" ∈ inputs`.
- **A combinational module has neither port.** A slotless machine module gets no clk/rst port from `closeMachine` (Machine.lean:107-109). Its other ports are allocated names, and `nAlloc_clk`/`nAlloc_rst` (FirstGateChild.lean:517, 523) show no allocated name is `"clk"`/`"rst"`. This closes the name question left open in LEAF_FREEZE §4: the module's inputs contain neither name, once this is connected through `MachineWired`'s `Allocated` conjunct (MachineEntry.lean:661).
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
- **The same interface data.** `bsC`, `outsC` and `S = q.S i` are kept, so `CallDec`, `MemDec`, `ServedP` and the call decoding are untouched.
- **`ResetN` is kept.** Consumers already supply it for every instance (CallsLinkedTNR.lean:57; `ComposedNWRegs`).
- **The alternative, rejected:** a single predicate with `isSeqChild mc → clk ∧ rst ∈ inputs`. It would change `seq_inst_runN` (MachineDepth.lean:98) and every `SeqChildRunN` producer.

**Checks frozen with A-COMB** (built as the definition-edit unit, S6; each must be a kernel-checked lemma):
- (C1) the embedding `SeqChildRunN … → ChildRunN …` (`Or.inl`);
- (C2) for `"clk" ∈ mc.inputs.map (·.name)`: `ChildRunN … ↔ SeqChildRunN …`;
- (C3) exclusivity `¬ (SeqChildRunN … ∧ CombChildRunN …)`, from `"clk" ∈` against `"clk" ∉`; no `Nodup` premise.

**What A-COMB costs (recorded).** It WEAKENS the general child guarantee: a `ChildShips` value no longer says the child is sequential. The final guarantee is preserved only after every parent consumer proves the unchanged `TopShips` from BOTH branches (S3, S4, S5). Until then, the preservation is open, and it is listed as such in M2's acceptance. The T1/FG goals are unchanged.

## 3. Reach of the change and compatibility
**Where `ChildShips` is used.**
- `ShipsRes`/`ShipsAt` (Defs:101, 114), and through them:
  - `CacheShips`, `InvAt`;
  - `IHAt`: `InvAt` in its premise, `ShipsRes` in its conclusion;
  - `BodyKeepsInv`/`ChildKeepsInv`/`KeepBodyStmt`/`KeepChildStmt`;
  - `ServedP`/`ServedPC` (with `Q := ShipsRes`), `ServedShipsStmt`;
  - `StepStmt`'s trace premise.
- The conclusions of `StepStmt`, `MemParentStmt(')` and `LeafStmt(')`.
- Not used in `T1Hyp` (Defs:161-183: `pkg`, `defines`, `closes`, `dec`, `closed`) or `T1Stmt` (conclusion `TopShips`).

**Proved theorems.** `memParent_childShips` (Gen2MemShips.lean:49) and `leaf_childShips_of_LB` (Gen2Leaf.lean) each change by one `Or.inl` at their final `exact`. Their statements and the instance tests are unchanged as text.

**`Tests/Gen2/PkgCompat.lean`.** The frozen `Old.*` baseline STAYS as it is; it is the historical pre-A-COMB text. The loss of equalities is shown, not hidden by a re-baseline. Each existing check is classified as follows:

| check (PkgCompat line) | position of `ChildShips` | after A-COMB |
|---|---|---|
| `CallDec`/`MemDec`/`TopShips`/`MemParentDataOk`/`ExtInS`/`MemOrigin` `rfl` (249-255) | none | unchanged `rfl` |
| `t1Hyp_iff` (327) | none | unchanged |
| `t1Stmt_compat` (388) | none (`T1Hyp`, `TopShips` only) | unchanged |
| `ChildShips` `rfl` (247) | — | replaced by `Old.ChildShips q n mc Dc → ChildShips (.gen q) n mc Dc` |
| `shipsRes_eq`/`shipsAt_eq` (265/276) | positive | replaced by `Old → new` implications |
| `cacheShips_eq` (287) | positive (through `ShipsRes`) | `Old → new` |
| `invAt_eq` (293) | positive (`JQC ∧ CacheShips`) | `Old → new` |
| `iHAt_eq` (299) | mixed: negative in `InvAt`, positive in `ShipsRes` | no implication in either direction; recorded as "changed, mixed", with a comment naming both positions |
| `bodyKeepsInv_eq`/`childKeepsInv_eq` (305/311) | mixed: `Keeps` has `InvAt` as pre- and post-condition | "changed, mixed" |
| `keepBody_eq`/`keepChild_eq` (317/322) | mixed (`ChildKeepsInv → BodyKeepsInv`; `IHAt` premise) | "changed, mixed" |
| `memParentStmt'_compat`/`memParentStmt_compat`/`leafStmt_compat` (366/370/374) | positive only (conclusion) | NOT a simple flip: `Old.*` quantifies over every `SrcPkg`, the new statement over every `Pkg` (`.loop` included), so `Old` gives nothing for `.loop`. Replaced by the `.gen`-restricted forms below (R2 on b7f85204) |
| `stepStmt_compat` (378) | mixed: `ServedP (ShipsRes …)` in premise, `ChildShips` in conclusion | "changed, mixed" |
| `servedShips_compat` (396) | mixed | "changed, mixed" |

**The `.gen`-restricted compat forms, exact types** (in `Tests/Gen2/PkgCompat.lean`):
```lean
theorem memParentStmt'_gen (L : Laws mref cref) : Old.MemParentStmt' (ι := ι) (dom := dom) L →
    ∀ (q : SrcPkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
      (raw b : Sparkle.IR.AST.Module) (D : Design),
      MemParentDataOk (.gen q) → ExtInS (.gen q) → MemOrigin (.gen q) →
      q.d.shape.insts ≠ [] → q.d.shape.instFields ≠ [] → q.d.shape.layout.slots ≠ [] →
      AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
      RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      MachineDefines mctx mref cctx cref q.decl q.d.shape →
      MachineTaken L mctx cctx (dv w + 1) q.decl q.d.shape raw D →
      (∀ k (hk : k < q.d.shape.insts.length), MemDec (.gen q) k (q.d.shape.insts[k]).1) →
      ∀ n, TopShips (.gen q) (n + 1) q.decl b raw D ∧ ChildShips (.gen q) (n + 1) b D
```
- **`memParentStmt_gen` and `leafStmt_gen`:** the same pattern. Each is the body of the new statement at `p := .gen q`, with `DataOk := DataOkLiftCompat DataOk` as in the existing tests, obtained from the corresponding `Old.*`.
- **How each is proved:** apply `Old.* q`, then the pointwise `Old.ChildShips q … → ChildShips (.gen q) …` on the conclusion. `Old.TopShips` and `TopShips (.gen q)` are `rfl` (PkgCompat:251).
- **What they are kept separate from:**
  - the pointwise `ChildShips` embedding;
  - the positive transports `Old.ShipsRes L P c r → ShipsRes L (Pkgs.lift P) c r` and `Old.CacheShips … → CacheShips L (Pkgs.lift P) …` over the lift, which are statements about `Pkgs.lift P`, not about `.gen q`.
- **What stays as planned:** `t1Hyp_iff` and `t1Stmt_compat`.

For every "changed, mixed" row, the test keeps the old statement text under `Old` and adds a comment. No theorem claims a relation the proof does not give.

**Optional, as reviewed:** a separate namespace `ACombBase` holding the A-COMB text of the `SrcPkg` definitions, with the Pkg-lift `rfl`/`_eq` checks against it. It checks the Pkg lift itself and does not replace `Old`. Existing acceptance evidence at earlier SHAs stays valid as history.

## 4. Units this amendment opens (inside `sparkle-gen2-step`; each frozen before Lean)
`RunOn_instFree` is used ONLY where the module is instance-free by a fact of the run: a leaf (`insts = []`), or a child of a one-output parent (`kidsCombB`, see S4). General comb children with instances go through `runKS_RunOn` (MachineDepth.lean:34), which has no `instFree` premise.

### S1 reset irrelevance (pure)
```lean
theorem runModule_seed_local {we : WEnv} {body : List Stmt} {X : List String}
    (hA : body.all isAssign = true) (hR : readsClosedB X body = true)
    {seed₁ seed₂ : Nat → (String → Nat) → Env}
    (hagree : ∀ t st, ∀ x ∈ X, seed₁ t st x = seed₂ t st x) :
    ∀ T st mems envs₁, runModule we body seed₁ T st mems = some envs₁ →
      ∃ envs₂, runModule we body seed₂ T st mems = some envs₂ ∧ envs₂.length = envs₁.length ∧
        ∀ j (h₁ : j < envs₁.length) (h₂ : j < envs₂.length) x, x ∈ X ++ writesOf body →
          (envs₂[j]'h₂) x = (envs₁[j]'h₁) x
```
Pieces: `evalAssigns_local` (HierOptRunH:36), `regNexts_assigns`/`applyNexts_nil` (ShipsComb:38-57), `readsClosedB_eq` (DepthHR:25).

### S2 slotless leaf (pure)
- `combChildRunN_of_LB`, from the A-boundary trace + `ExtInS p` + `LeafDataOk p` + `insts = []` + `slots = []` + `hpost`:

  `∀ n dsn i, CombChildRunN (childMap dsn.modules) dsn n b (p.d.bsIn.take p.kD) p.d.shape.layout.outs (p.S i)`.

  Route: `traceL_of_LB` (Gen2Leaf.lean), the trace at a seed with rst = 0, then S1 (rst ∉ inputs), the merge, `RunOn_instFree`.
- **Its input facts, from `MachineWired`:**
  - `"clk"`/`"rst"` ∉ inputs, from `Allocated` (MachineEntry.lean:661) + `nAlloc_clk`/`nAlloc_rst`;
  - assign-only, from the `insts = [] → slots = [] → body.all isAssign` conjunct (MachineEntry.lean:678);
  - `readsClosedB` over the inputs: to be derived from the generated body; if it is not derivable from `MachineWired`, stop and report.
- The slotless leaf `TopShips` via `seedR`-style seeding + S1 + `runModule_assigns` + `mergeDuplicates_sound` + `checkedOptimize_sound`.

### S3 group parents (`instFields ≠ []`, `closeInstsG`): the general comb child
- **Children here may have instances** (a hierarchical comb child), so no `instFree` is assumed.
- **`CombFactsRN`:** `SeqFactsRN` (CallsLinkedTNR.lean:23) with `CombChildRunN` in place of `SeqChildRunN`.
- **`comb_inst_runN`:** the depth-n runner of an instance whose module satisfies `CombChildRunN`. It goes via `runKS_RunOn` and `connsG` without clk/rst (MachineLinkedT.lean:28), as `seq_inst_runN` (Depth:98) does, minus the clk/rst connections.
- **Exact types are frozen in S3's own freeze.** They are the `seq_inst_runN`/`calls_hchildRN` types with that one predicate replaced.
- **The consumer:** `calls_hchildRNC` and `machine_linkedT_callsServedC` with a three-way per-instance premise `MemFacts ∨ SeqFactsRN ∨ CombFactsRN`, chosen per instance by `isSeqChild`.
- **Hierarchical comb children are an explicit obligation of S3** (the `runKS_RunOn` route), not excluded.
- **`hseq` obligation (from S6, 1fdbc18d).** `seqFactsRN_of_callDec` is sequential-only (`hseq : ∀ mc, ServedPC … c mc → "clk" ∈ …`). S3 branches per actual served `mc`, or uses a `PC` restricted by the branch, e.g. `ServedPC … ∧ "clk" ∈ …` for the sequential part. It does not obtain the universal `hseq` from a case split on one `mc`. `hseq` never becomes a T1/FG premise.

### S4 one-output parents (`instFields = []`, `closeInsts`; G-ONEOUT)
**Facts of the PARENT's run, not restrictions of the child.** A successful `closeInsts` (Machine.lean:396-426) makes every instance module `mc`:
- (a) satisfy `kidsCombB` (Machine.lean:371-382; `closeInsts_kidsComb`, ChildServe.lean:248): `mc.body.all isAssign`, `readsClosedB (mc.inputs.map (·.name)) mc.body`, outputs written, outputs not inputs, inputs connected by `ref`;
- (b) satisfy `instStmt`'s checks (Machine.lean:272-287): `mc.outputs = [outP]`, no input named `"clk"`/`"rst"`, distinct argument ports, `outP.name ∉` argument names.

So every child of a one-output parent is assignment-only (hence instance-free), single-output and has no clk/rst. These are consequences of the parent's accepted run, read off the closing; FG is not narrowed. The child's `ChildShips` value is then necessarily the `CombChildRunN` branch (by C3 and (b)).

**Missing lemmas (pure), exact types:**
```lean
-- (S4-a) assignment-only bodies do not read memories
theorem evalAssigns_mems_irrel {we : WEnv} {body : List Stmt} (hA : body.all isAssign = true) :
    ∀ (mems mems' : MEnv) (env : Env), evalAssigns we mems body env = evalAssigns we mems' body env

-- (S4-b) a flat combinational child run is a per-cycle function of its argument values
theorem childFn_of_combRun {dsn : Design} {n : Nat} {mc : Module} {bsC} {o : OutField} {outP : Port}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : CombChildRunN (childMap dsn.modules) dsn n mc bsC [o] S)
    (hA : mc.body.all isAssign = true) (hout : mc.outputs = [outP])
    (hS : ∀ v, InRange v (bsC.filter fun b => b.2 != .domain) → ∃ f, (S (fun _ => v))[0]? = some f) :
    ChildFn mc (fun v => InRange v (bsC.filter fun b => b.2 != .domain))
      (fun v => ((S (fun _ => v))[0]?.map (· 0)).getD 0)

-- (S4-c) the source stream is pointwise in the argument stream (for the parent's per-cycle `hcalls`)
theorem combS_pointwise {dsn : Design} {n : Nat} {mc : Module} {bsC} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : CombChildRunN (childMap dsn.modules) dsn n mc bsC outsC S) (hA : mc.body.all isAssign = true) :
    ∀ (vals : Nat → List Nat) (τ : Nat) (k : Nat) (o : OutField) (f g : Nat → Nat),
      (∀ τ', τ' ≤ τ → InRange (vals τ') (bsC.filter fun b => b.2 != .domain)) →
      outsC[k]? = some o → (S vals)[k]? = some f → (S (fun _ => vals τ))[k]? = some g → f τ = g 0
```
- **The source-output existence (review R1 on b7f85204).** `CombChildRunN` only constrains outputs `f` with `(S vals)[k]? = some f`, so a `S` with too few entries satisfies it vacuously. Example: `S := fun _ => []` with a constant-1 module; without `hS`, S4-b's `getD 0` function would be 0. Hence the explicit premise `hS` in S4-b; S4-c takes `f` and `g` as given witnesses.
- **The supplier of `hS` and of S4-c's `g`, for `S := q.S i` of the callee's actual package `q`:**
  ```lean
  theorem Pkg.src_get (q : Pkg ι dom) : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k : Nat) (o : OutField),
      q.d.shape.layout.outs[k]? = some o → ∃ f, (q.src i bools bits)[k]? = some f
  ```
  It is proved by cases on `q`:
  - `.gen`: `GenFacts.source` + `GenFacts.result` (QuadComposed.lean:135-150) give `(q.src i bools bits).length = q.d.outs.length`, by the length of the mapped equation. `outsFitB` in `q.d.ok` (MachineAuto.lean:136-143) gives `layout.outs.length ≤ q.d.outs.length`.
  - `.loop`: the same from `SrcPkgL`'s `hres`/`hsrc` (Gen2Loop.lean:161-170).

  `q.S i v = q.src i (boolsOf …) (bitsOf …)` (Pkg.lean:75), so `hS` and `g` follow from `Pkg.src_get` at `k = 0`, with `q.d.shape.layout.outs = [o]` (the `outsC` of `ChildShips`). This supplier is a lemma of the package facts the parent's `ShipsRes`/`P` already carries, not a new premise. **If either case cannot be proved from those facts, the work stops there and is reported; no new residual is added silently.**
- **Proof ingredients.**
  - `RunOn_instFree`, from (a) via `instFree_of_seqOk`-style lemmas.
  - S4-a, to pass from the zero memories of `ResetN` to `ChildFn`'s arbitrary `mems`.
  - An explicit `KT n` state with `stOf n s = env`; `ResetN` is satisfiable since an assign-only body has no registers or memories (a construction lemma, part of S4-b).
  - `seedIn mc ins 0 env = env` for `ins 0 := env` on the inputs.
  - S1/`evalAssigns_local` for the cycle-locality used by S4-c.
- **The consumer.** A served version of `machine_linked_callsRA` (ComposeRA.lean:72): `hfn` is supplied per call from `Served1P (ShipsRes L P)` (Defs) at the parent's actual instance module. `P k`/`F k` are the S4-b functions of the callee package's `S`. The parent's `hcalls` comes from `CallDec` + S4-c. Then `composedNWn_of_H` (DepthHR:208) with `kidsComb` from (a), to depth n.
- **Not claimed:** S4-b/S4-c are NOT derived from a general `CombChildRunN`. They use (a)'s `isAssign` fact (from the parent's closing) and `[o]`/`[outP]` from (b).

### S5 slotless parents and slotless tops
- **A slotless parent's own `ChildShips`.** It is the `CombChildRunN` branch from its composed run at depth n: `combChildRunN_of_composedNW_run`, mirroring `seqChildRunN_of_composedNW_run` (Gen2C6:28), whose `hsl` is the blocker. It goes through `RunOn` directly (the parent has instances), so it is consistent with S3's `runKS_RunOn` route.
- **A slotless module's `TopShips`.** `RunFacts.rst` (GuardsSound:321) requires `"rst"`, so consumer 1 needs a no-rst variant, from `hierRefineCheck_linkedH_noRst` (HierOptRunHNoRst:56) and `refineCheck_transfer_noReg` (RefineNoRst:224).
- **Exact types are in S5's freeze.**

### S6 definition edit and connection
- A-COMB in Defs, the C1-C3 lemmas, and the PkgCompat classification (§3).
- The memParent/leaf `Or.inl` updates and the instance rebuilds.

**Not in scope here (recorded for gen4 routes).** Gate-route children have no `Pkg`: `T1Hyp.defines` needs `MachineDefines` (Defs:177). A machine-route parent that calls a gate-route child therefore depends on gen4 route coverage. A later gate package can reuse `CombChildRunN` (a `GateKidRun → CombChildRunN [out]` lemma). Nothing is dropped from FG.

## 5. Order, and the rest of M2-step
1. Re-review of this rev2.
2. S1 and S2 research and lemma preparation may proceed now: pure lemmas that do not depend on the `ChildShips` edit.
3. S6, after rev2 is confirmed: the A-COMB definition edit, C1-C3, the PkgCompat classification and the `Or.inl` updates.
4. S2 assembly, S3, S4 (G-ONEOUT), S5.
5. Then the StepStmt route: G-LIFT, G-TRANSPORT, mixed G-BD/G-RUNFACTS and `seqFactsRN_of_callDec`/U-ADAPT, consuming `ChildRunN` through S3/S4, in its own freeze.

**M2 acceptance unchanged:** G-SLOTLESS covers slotless leaves AND their use by parents; G-ONEOUT is required; and the final-guarantee preservation over A-COMB is open until S3-S5 are done.

## 6. Not claimed
No Lean is changed by this document. Nothing here is proved; the existing pieces listed above are used only as read.
