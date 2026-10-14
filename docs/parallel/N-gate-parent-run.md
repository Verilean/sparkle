# N — `gate_parent_run` for the instance-root parents (round 1)

Branch `par/n-1` from poc `c3176ef1` (the single capturing entry). **WRITTEN, NOT
BUILT. Nothing was compiled or run** (worker N never starts Lean). "READ" = read in
the tree; "PREDICTED" = expected from reading.

## 0. Where the chain stands

| task | status |
|---|---|
| 1. the mixed harness shell, world by world | written: `Tools/ShippingGateParentRuns.lean` (`mixedHarness_runs`, `instanceArm_run`, the binder walk, the leaf) |
| 2. the S6 shape tail over `armCont` | written: `Tools/ShippingGateParentTail.lean` (`InstanceNShape`, `armCont_instanceN_tail`) |
| 3. the two full-entry facts on instance bodies | written: `Tools/ShippingGateParentPost.lean` (pure) |
| 4. `gate_parent_run` for the root shapes + `parentUse` | written: `Tools/ShippingGateParentRun.lean`, `Tests/Compiler/GateParentRunTest.lean` (target-only, axioms printed) — **with two premises outside the classifier's ALLOWED list (§2)** |
| 5. the cone (`parentMix`) | **NOT started.** Exact next statement in §5 |

## 1. Files, statements

### `Tools/ShippingGateParentRuns.lean` (task 1)

Small rules (namespace `Tools.ShippingGateParentRun`):

    runs_keep  (hk : Keeps … (J L.plain D) m) (hw : InvV L w) (hd : L.dval w = D)
               (r : RunsTo m … w a w') : InvV L w' ∧ L.dval w' = D
    op_runs    (hp : Op p) … : the same for a frame / diagnostic operation (`Triple.op`)
    runsToReturns (h : RunsTo (c ctx s) … w (a, s') w') : Returns c ctx s a s'
    RunsTo.bindC (h : RunsTo ((c >>= f) ctx s) … w r w') :
      ∃ a s1 w1, RunsTo (c ctx s) … w (a, s1) w1 ∧ RunsTo (f a ctx s1) … w1 r w'
    RunsTo.bindR  — the same, the rest as `Returns (f a) ctx s1 r.1 r.2`
    lift_runs (h : RunsTo (CompilerM.liftMetaM x ctx s) … w (a, s') w') :
      s' = s ∧ RunsTo x … w a w'

The walk:

    bindInputPort_runs (hw : InvV L w) (hd : L.dval w = D)
        (h : RunsTo (bindInputPort id nm ty k ctx s) … w p w') :
      ∃ w1, InvV L w1 ∧ L.dval w1 = D ∧
        RunsTo (k {ctx with varMap := (id, (makeWire nm ty true s).1) :: ctx.varMap}
                  (addInput (makeWire nm ty true s).1 ty (makeWire nm ty true s).2).2) … w1 p w'
    bindMixed_runs L k bools bits : ∀ l a w p w', InvV L w → L.dval w = D →
        RunsTo (bindMixedCertifiedInputs k l a.context a.state) … w p w' →
        ∃ w1, InvV L w1 ∧ L.dval w1 = D ∧
          RunsTo (k (prepare bools bits l a).context (prepare bools bits l a).state) … w1 p w'
    emitLeaves_single_runs (hw) (hd)
        (h : RunsTo (emitLeaves (translateExprToWire tenv) cacheRef (profLogIO b) [(port, e)] none 0 ctx s) … w r w') :
      ∃ w1 w2 wire s1 ty, InvV L w1 ∧ L.dval w1 = D ∧
        RunsTo (translateExprToWire tenv e port false true ctx s) … w1 (wire, s1) w2 ∧
        s1.usedNames.contains port = false ∧
        r.2 = (emitAssign port (.ref wire) (addOutput port ty s1).2).2 ∧ ty = leafOutputType s1 wire

**The harness shell:**

    theorem mixedHarness_runs (L : RefLaws mref cref) {D : Nat} … (hw : InvV L w) (hd : L.dval w = D)
        (hr : RunsTo (synthesizeMixedCertified (fun e hint top named => translateExprToWire tenv e hint top named)
          (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
      ∃ ids cache wT wT' wire sm0 ty st,
        ids.Nodup ∧ ids.length = bs.length ∧ InvV L wT ∧ L.dval wT = D ∧
        RunsTo (translateExprToWire tenv (instFVars (ids.map .fvar).toArray 0 body) "out" false true
          (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids) (start (entryCompilerState false cache) (ofDecl declName))).context
          (prepare … ).state) mctx mref cctx cref wT (wire, sm0) wT' ∧
        sm0.usedNames.contains "out" = false ∧
        st = (emitAssign "out" (.ref wire) (addOutput "out" ty sm0).2).2 ∧ ty = leafOutputType sm0 wire ∧
        m = (addClockResetIfSequential st.module).finalize ∧ d = st.design

**The arm, with its states** (the built `instanceArm_grow` gives the `armCont` run as `∃ st s'`, which the
shape proof cannot use):

    theorem instanceArm_run (L) (hfn : e.getAppFn = .const mn us) (htag : isHardwareModule env mn = true)
        (hw : InvV L w) (hd : L.dval w ≠ 0)
        (hr : RunsTo (translateInstanceOrFallback env rec e hint top named ctx st) … w (wire, s') w') :
      ∃ y : Res, RealChild mref cref mn y ∧ Returns (armCont rec mn y e hint top named) ctx st wire s'

Note on depth: the shell keeps `InvV` and the depth up to the translator's start only. For ONE call
nothing after the arm is needed (the `RealChild` comes from `childSynthEntry_post` at the arm). The
growing cache (`WG`, `WG.child_hit`) is not used by the root shapes; it is what the cone with repeated
callees needs (§5).

### `Tools/ShippingGateParentTail.lean` (task 2)

    def InstanceNShape (declName) (bs) (ids) (cache) (argIds : List FVarId) (y : Module × Design)
        (m : Module) (d : Design) : Prop :=
      ∀ wOut ports, y.2.modules = [] → y.1.inputs = ports → y.1.outputs = [⟨"out", .bitVector wOut⟩] →
        (no clk / rst in ports) → ports.length = argIds.length →
        ∃ instName outW conns, ∀ bools bits env0 ws vals, (let a, p as InstanceNPreserves)
          Admissible … → (∀ i h, p.bits (argIds[i]) = some ⟨ws i, vals i⟩) →
          m.body = [.inst y.1.name instName (conns.reverse ++ [("out", .ref outW)]), .assign "out" (.ref outW)] ∧
          d.modules = [y.1] ∧ outW ≠ "out" ∧ ∃ aWs, (InstanceNPreserves' connection facts)

    theorem armCont_instanceN_tail
        (tr : Returns (armCont (translateFuelFix (translateStep tenv) 1048575) mn y
            (instEN mn lvls dF (argIds.map .fvar)) "out" false true) (prepared ctx) (prepared state) w sm0)
        (ht : st = (emitAssign "out" (.ref w) (addOutput "out" ty sm0).2).2)
        (hm : m = (addClockResetIfSequential st.module).finalize) (hd : d = st.design) :
      InstanceNShape declName bs ids cache argIds y m d

The proof is the text of `synthesizeMixedCertified_instanceN_sound` from the line after its
`rw [hsub sub hSubM] at tr` to the end, `mc := y.1`, `dc := y.2`, the domain argument any `dF`.

### `Tools/ShippingGateParentPost.lean` (task 3, pure)

    dropZeroWidth_instBody (hb : M.body = [.inst cn iname conns, .assign l (.ref r)])
        (hconns : ∀ c ∈ conns, ∃ x, c.2 = .ref x)
        (hl : (buildWidthMap M).get? l = some k) (hk : k ≠ 0) :
      (dropZeroWidthModule M).body = M.body ∧ .inputs = M.inputs ∧ .outputs = M.outputs ∧ .name = M.name
    mergeChecked_instBody (hb : M.body = [.inst …, .assign l rhs]) :
      refineCheck M (mergeChecked M) = true ∨ mergeChecked M = M
    hierGate_instBody (hb : …) : hierGate M = true
    post_instBody (hpost : b = dz M ∨ b = mergeChecked (dz M)) (hb) (hconns) (hl) (hk) :
      (dz M).body = M.body ∧ hierGate (dz M) = true ∧ b.inputs = M.inputs ∧ b.outputs = M.outputs ∧
      (b = dz M ∨ refineCheck (dz M) b = true)

`hierBinds` (the MEASURED branch of `checkedOptimize`) is not proved: it is `refineCheck` of the
extracted interface, a computation on the module's content.

### `Tools/ShippingGateParentRun.lean` (task 4)

    runsTo_det (h1 : RunsTo m … w a1 w1) (h2 : RunsTo m … w a2 w2) : a1 = a2 ∧ w1 = w2
    sfc_mixed_run (old) (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body)) (hw : InvV L w)
        (hr : RunsTo (synthesizeFromConst (translateExprToWire tenv) (profLogIO b) declName [] false true ci isInst) … w (m, d) w') :
      ∃ wa wb, InvV L wa ∧ L.dval wa = L.dval w ∧ RunsTo (synthesizeMixedCertified …) … wa (m, d) wb
    parent_core_instanceN (hD : D ≠ 0) (hposs) (htag : isHardwareModule tenv mn = true) (hpure) (hbin) (hkind)
        (hw : InvV L w) (hd : L.dval w = D)
        (hr : RunsTo (synthesizeMixedCertified … declName bs (instEN mn lvls dE (poss.map (inputExpr bs.length)))) … w (m, d) w') :
      ∃ y ids cache, RealChild mref cref mn y ∧ ids.Nodup ∧ ids.length = bs.length ∧
        InstanceNShape declName bs ids cache (poss.map fun q => ids[q]!) y m d
    instanceNH_term_gate (peel : mixedGatePeel d.value = some (bs, body))
        (hroot : hierInstRoot isInst (bs.map (·.2)).toArray body = true) (hscalar) :
      mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, body)

**The theorem:**

    theorem gate_parent_run {f value bs mn lvls dE poss} {mctx mref cctx cref w w' b design}
        (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
        (entry : EntryDefines mctx mref cctx cref f value)
        (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Lean.Environment) mctx mref cctx cref wE e wE' →
          isHardwareModule e mn = true)
        (hscalar : ∀ dv : DefinitionVal, dv.value = value → mixedGateResultScalar dv.type = true)
        (old : ∀ dv, dv.value = value → certifiedShape? false [] (.defnInfo dv) = none)
        (accept : ∀ dv, dv.value = value → mixedGateResultScalar dv.type = true → ∀ isInst,
          isInst (instEN mn lvls dE (poss.map (inputExpr bs.length))) = true →
          mixedCertifiedShape? false [] (.defnInfo dv) isInst = some (bs, instEN mn lvls dE (poss.map (inputExpr bs.length))))
        (hposs : ∀ q ∈ poss, q < bs.length)
        (hpure : (mn == ``Signal.pure) = false) (hbin : signalBinOpOf mn = none)
        (hkind : ∀ ids, ids.length = bs.length →
          fallbackKind (instEN mn lvls (instFVars (ids.map .fvar).toArray 0 dE) ((poss.map fun q => ids[q]!).map .fvar)) = .other)
        (bnd : ChildBnd mref cref w) :
      ∃ (M : Module) (D : Design) (y : Res) (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
        (b = dropZeroWidthModule M ∨ b = mergeChecked (dropZeroWidthModule M)) ∧
        b.name = M.name ∧
        ((∀ x ∈ D.modules, x.name ≠ M.name) → design.modules = D.modules) ∧
        RealChild mref cref mn y ∧ ids.Nodup ∧ ids.length = bs.length ∧
        InstanceNShape f bs ids cache (poss.map fun q => ids[q]!) y M D

Proof: `ChildBnd` gives one law witness `L`; `synthesizeCombinational_checked` and `full_split` decompose
the full entry, `runsTo_det` identifies their two core runs; `core_reads_val0` (outermost) or
`core_reads_val` (nested, `CacheInv` from `StartV`) give the entry's reads `ci`, `envR` and the body's
start world (invariant, positive depth); `EntryDefines` names the entry constant; `tag` at the entry's
read and `hscalar` give the gate's acceptance (`accept`) under `instancePredicate envR`; the run of
`synthesizeFromConst` is the harness (`sfc_mixed_run`); `parent_core_instanceN` at `tenv := envR` —
the SAME value the translator was built from (the capture): the arm's tag is `tag` at that read.

Coverage of the three root declarations: `accept` is discharged by the built `instanceN_term_gate` for a
binder domain (`parentUse`, done in the test) and by `instanceNH_term_gate` for a closed-constant domain
(`wrapAdd`, `wrapPick`: the canonical spine refuses a constant argument; the pipeline disjunct
`hierInstRoot` accepts — PREDICTED from `hierInstSpine`'s second case; the probe logs which disjunct
accepts, I did not see its output). `wrapAdd` / `wrapPick` are NOT instantiated (their value / peel
reflections do not exist in the tree; `#def_decl_value` + a `rfl` peel per declaration, as for
`parentUse`).

### `Tests/Compiler/GateParentRunTest.lean` (target-only)

`parentUse_peelN` (`rfl`), `parentUse_pure`, `parentUse_binOp`, `parentUse_kind` (`rfl` / `decide`, the
tactics of `LegacySemInstanceTest`'s `dbl_kind`), `parentUse_gate_parent_run` (binders: the run,
`EntryDefines`, `tag`, `hscalar`, `ChildBnd` — the same `tag` / `hscalar` binders as the BUILT
`parentUse_instance_entry`), `#print axioms` of it and of `gate_parent_run`. PREDICTED: `propext`,
`Classical.choice`, `Quot.sound` only.

## 2. The premises — FINDING: two environment facts outside the ALLOWED list

`gate_parent_run` has, besides the ALLOWED `RunsTo`, `EntryDefines`, `ChildBnd` and pure facts of the
reflected value, two premises of the form the built S6 entry endpoints carry:

* **`tag`** (the callee is designated in every `getEnv` read of these contexts). It CANNOT be derived
  from `EntryDefines`: `EntryDefines` pins only the VALUE of the entry constant. If the callee were not
  designated, the mixed gate would refuse the parent, and `entryConst` returns the declaration as read
  whenever its unfolding passes no gate — with the same value; the run then takes the machine or legacy
  route. Nothing in `EntryDefines` or in the run's result distinguishes the two. (With the capture, the
  arm's tag IS the gate's tag: one read. But the gate's acceptance itself needs the tag, and for an
  instance root the acceptance is equivalent to it.)
* **`hscalar`** (the entry constant's TYPE is one scalar Signal): the instance disjuncts of
  `mixedCertifiedShape?` test `mixedGateResultScalar d.type`; `EntryDefines` says nothing of the type.

Neither is in `Tools.ShippingFinalGoalCommand.allowed`. I did not add a reflection form; I record the
choice for the reviewer:

1. admit the S6 forms (`tag` as a `RunsTo getEnv`-universal reflection, `hscalar` as an `EntryDefines`-
   style reflection of the type) in the classifier; or
2. ONE gate reflection, the analogue of `MachineDefines` (which already reads `mixedCertifiedShape? …
   (instancePredicate envR) = none` per world):

       def GateDefines mctx mref cctx cref f bs body : Prop :=
         ∀ w1 ci w2 w5 envR w6, RunsTo (getConstInfo f) … w1 ci w2 → RunsTo getEnv … w5 envR w6 →
           ∃ dv, entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) = .defnInfo dv ∧
             certifiedShape? false [] (.defnInfo dv) = none ∧
             mixedCertifiedShape? false [] (.defnInfo dv) (instancePredicate envR) = some (bs, body)

   With it `tag` / `hscalar` / `old` / `accept` / `entry` collapse into one premise, and the arm's tag
   follows from the acceptance by the built `spineRoot_tag` (canonical spine) or
   `Tools.ShippingInstanceTag.root_tag` (pipeline root; its projection disjunct is excluded by the last
   argument being a binder — `spine_tag`'s argument). Not done: it is a new reflection form (ruled out
   once as "strengthen `EntryDefines`", B-slotless-parents-2 §11.5).

The proof of `gate_parent_run` does not depend on which: `parent_core_instanceN` takes only the tag at
the translator's own environment.

## 3. Build order, lean_lib lines

`lakefile.lean` (NOT edited by me):

    lean_lib «Tools.ShippingGateParentRuns» where
      roots := #[`Tools.ShippingGateParentRuns]

    lean_lib «Tools.ShippingGateParentTail» where
      roots := #[`Tools.ShippingGateParentTail]

    lean_lib «Tools.ShippingGateParentRun» where
      roots := #[`Tools.ShippingGateParentRun]

    lean_lib «Tools.ShippingGateParentPost» where
      roots := #[`Tools.ShippingGateParentPost]

Order (each builds on poc as is; Runs and Tail are independent of each other):
1. `Tools.ShippingGateParentPost` (imports `ShippingPostSoundness`, `ShippingRegisterSoundness`) — independent.
2. `Tools.ShippingGateParentRuns` (imports `ShippingInstArmGrow`, `ShippingChildBody`, `ShippingCacheCoherentVia`, `ShippingMixedEntrySoundness`).
3. `Tools.ShippingGateParentTail` (imports `ShippingInstArmGrow`, `ShippingInstanceEntrySoundness`).
4. `Tools.ShippingGateParentRun` (imports 2, 3, `ShippingCacheCoherentOuter`, `ShippingMachineShipping`, `ShippingInlineSoundness`).
5. `lake build Tests.Compiler.GateParentRunTest` (target-only; nothing to add to `Tests/AllTests.lean`).

## 4. Risks, in the order I expect them

1. **`emitLeaves_single_runs` / `bindInputPort_runs`** — the `RunsTo.bindC` unification against the
   unfolded do-blocks (the same shapes the built `Returns.bind` matches), and the `obtain ⟨rfl, …⟩`
   substitutions of the circuit state (which variable `subst` keeps does not matter: the goal follows).
   In `bindInputPort_runs`: the `have hrd' : RunsTo (Pure.pure (ctx, sB) …) := hrd` (the built
   `bindInputPort_S` proves `getCompilerState ctx st = pure (ctx, st)` by `rfl`), and `subst e1` replacing
   `ctx` by `old` before `rw [← hwn, ← hsA, ← hsB]`.
2. **`armCont_instanceN_tail`** — `unfold armCont at tr; rw [houts] at tr; simp only [] at tr` in the
   place of S6's `rw [show ((mc, dc).1.outputs) = mc.outputs from rfl, houts] at tr; simp only [] at tr`;
   if `simp only []` makes no progress: `dsimp only at tr`. The rest is S6's text verbatim.
3. **`parent_core_instanceN`** — `hinst` (`rw [instFVars_instEN]; simp only [List.map_map]; congr 1;
   apply List.map_congr_left`); `rw [stepEq] at htr` rewriting a prefix of the applied action
   `translateExprToWire … ctx s` (kabstract sees the partial application; if not, `have` the run in
   the translator's arm form and `exact` by `stepEq ▸`).
4. **`lift_runs`** — `cases h` on `EST.Out.ok (b, s) w1 = EST.Out.ok (a, s') w'` with `a s' w'` the
   lemma's own variables (the built `Returns.liftMetaM` does `cases hrun` the same way).
5. **`mixedHarness_runs`** — `keeps_iff.mpr (Triple.mapM _ (fun _ => Triple.frame L.plain Framed.freshFVar D) bs)`
   (the `JE` / `fun e w => J … ∧ OkExc e` match, as in `harnessRel_of`).
6. **`gate_parent_run`** — named arguments `(tenv := envR) (D := L.dval wa)` to `parent_core_instanceN`.
7. **`GateParentRunTest.parentUse_kind`** — `fallbackKind` on `.fvar ids[q]!` arguments by `rfl`
   (`dbl_kind` did it on `.fvar xid`); `instanceNH_term_gate`'s `simp only` list (unused by the test).
8. **`ShippingGateParentPost`** — `split` on the `if !allConcrete` under the projections;
   `hierGate_instBody`'s `rfl` after `rw [hb]` under the `let isInst`.

## 5. Where it stops: the cone (task 5), the exact next statement

The cone (`parentMix = childAdd a b + a`, `hierGateRoot`) is NOT started. What the root proof does
not give:

* the S6 cone result `HierConePreserves` is built from `LeafContract`s, and the instance leaf's
  contract `inst_leaf_contract` (`Tools/ShippingInstanceLeaf.lean` 441) is a `Contract` — a statement
  about EVERY `Returns` run of the leaf's translation — with the child pinned by
  `hsub : ∀ r, MReturns (childSynthEntry mn) r → r = (mc, dc)`. A world-aware cone needs the leaf
  contract restated for runs FROM AN INVARIANT WORLD OF POSITIVE DEPTH, with the run's child.
* the operands' translations before a leaf run change the world; the leaf's start world is invariant
  by `TranslateRel` (`translateRel`, built) applied to the earlier operands — so the decomposition of
  the cone's `translateCanonicalSignalBinary` (and the other cone nodes) must be done at `RunsTo` level.

Exact next statement (the leaf, the world-aware twin of `inst_leaf_contract`'s first half):

    theorem inst_leaf_runs (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {rec : TranslateFn}
        {mn : Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
        (hstep : ∀ hint top named, translateStepWith (translateFallback tenv) rec (instEN mn lvls dom argsE) hint top named =
          translateInstanceOrFallback tenv rec (instEN mn lvls dom argsE) hint top named)
        (htag : isHardwareModule tenv mn = true)
        {hint top named ctx s w wire s' w'} (hw : InvV L w) (hd : L.dval w = D)
        (hr : RunsTo (translateStepWith (translateFallback tenv) rec (instEN mn lvls dom argsE) hint top named ctx s)
          mctx mref cctx cref w (wire, s') w') :
      ∃ y : Res, RealChild mref cref mn y ∧ (L.val w').get? mn = some y ∧ InvV L w' ∧ L.dval w' = D ∧
        SubMap (L.val w) (L.val w') ∧ Returns (armCont rec mn y (instEN mn lvls dom argsE) hint top named) ctx s wire s'

(from `instanceArm_run` plus `armCont_keepsC` / `WG.ofKeeps` for the world after the arm — the cache
entry is what a REPEATED callee needs: `WG.keepEntry` + `WG.child_hit` make the second call's pair the
first's), then `inst_leaf_contract`'s second half over `armCont … y` (the tail of its proof after its
`hsub` rewrite, like task 2), then a `RunsTo`-level fuel induction over `hierGateBoolBody` /
`hierGateBitsBody` collecting the leaves' pairs (`kids : List (Name × Res)`, each a `RealChild`, equal
pairs for equal callees by the cache), then `HierConePreserves` with `SubSynthDefinesAll` replaced by
`kids`.

## 6. Could not be determined by reading

* Every risk of §4 (nothing was elaborated).
* Which root disjunct accepts `wrapAdd` / `wrapPick` (the probe logs it; I did not see the log).
* Whether `fallbackKind` reduces by `rfl` on arguments `.fvar ids[q]!` (stuck `getElem!` inside the
  constructor) as it does on `.fvar xid`.
* Whether a child of a gate-route parent can have the parent's module name (the `(∀ x ∈ D.modules,
  x.name ≠ M.name) →` antecedent of the design equation is left to the consumer; `ofDecl_ne` and the
  child's own name fact would discharge it).

---

# Round 2: `GateDefines`, `gate_parent_runG`, and the cone's leaf (WRITTEN, NOT BUILT)

Same rules; nothing compiled or run. The round-1 files are unchanged.

## 7. `GateDefines` — ONE reflection premise, NOT ALLOWED until ruled

`Tools/ShippingGateDefines.lean` (a PROOF-SIDE definition; nothing was added to
`Tools.ShippingFinalGoalCommand.allowed`):

    def GateDefines mctx mref cctx cref (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr) : Prop :=
      ∀ w1 ci w2 w5 envR w6,
        RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
        RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
        ∃ dv : DefinitionVal,
          entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) = .defnInfo dv ∧
          certifiedShape? false [] (.defnInfo dv) = none ∧
          mixedCertifiedShape? false [] (.defnInfo dv) (instancePredicate envR) = some (bs, body)

**Until the classifier admits it, `gate_parent_runG` carries one NOT ALLOWED reflection premise.**

| | `EntryDefines f v` | `MachineDefines f shape` | `GateDefines f bs body` |
|---|---|---|---|
| per world or global | per world: every `getConstInfo` / `getEnv` run in the run's contexts and refs | per world, plus a SECOND `getEnv` run (the machine arm reads again) | per world, ONE `getEnv` run (the entry reads once since the capture) |
| entry constant | `= .defnInfo d ∧ d.value = v` | not named | `= .defnInfo dv` |
| first gate | — | refuses | refuses |
| mixed gate, under `instancePredicate envR` | — | refuses | ACCEPTS as `(bs, body)` |
| further reading | — | `machineShape? … (structEnv envR') = some shape` | — |
| contexts | independent (`EntryDefines.ctx`) | independent (`MachineDefines.ctx`) | independent (`GateDefines.ctx`, written) |

What it states that `EntryDefines` does not: the gate's VERDICT on the entry constant, which reads the
value, the TYPE (`mixedGateResultScalar`) and the run's `@[hardware_module]` tags (the predicate). It is
`MachineDefines` with the mixed gate's verdict flipped to "accepts as (bs, body)" and no machine
reading. `gateDefines_of_entry` (in `ShippingGateParentRunG`): the round-1 premises (`EntryDefines` +
`tag` + `hscalar` + `old` + pure acceptance) imply `GateDefines` — it is no stronger an assumption.

What a generator must decide to produce it per declaration (as for `MachineDefines`: a BINDER of the
generated endpoint over reflected constants, never a proved fact): evaluate, in the elaboration
environment, `entryConst true false [] ci (instancePredicate env) …`, check `certifiedShape? … = none` and
`mixedCertifiedShape? … (instancePredicate env) = some (bs, body)`, and reflect `bs` / `body` as
constants (`f.gateBinders`, `f.gateBody`). The pure side facts are kernel `rfl` / `decide` per
declaration: `MixedGateSel kinds body`, `poss ≠ []`, the positions, `hpure`, `hbin`, `hkind`.

Also in the file: `mixedGateCond` (the text of the gate's condition), `mixedShape_cond` (an acceptance
is the peel and the condition), `MixedGateSel kinds body := ∀ isInst sc, isInst body = false →
mixedGateCond isInst kinds body sc = false` (only an instance disjunct accepts the body; per
declaration `unfold mixedGateCond unifiedInstanceRoot hierInstRoot; rw [hI]; rfl`), `gate_pred`
(acceptance + `MixedGateSel` ⇒ `instancePredicate envR body = true`), `list_snoc_of_ne`,
`lastBVar_tag` (the text of the built `spine_tag`'s case), `instEN_pred_tag`.

## 8. `gate_parent_runG` (`Tools/ShippingGateParentRunG.lean`)

    theorem gate_parent_runG {f bs mn lvls dE poss} {mctx mref cctx cref w w' b design}
        (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
        (gdef : GateDefines mctx mref cctx cref f bs (instEN mn lvls dE (poss.map (inputExpr bs.length))))
        (hsel : MixedGateSel (bs.map (·.2)).toArray (instEN mn lvls dE (poss.map (inputExpr bs.length))))
        (hne : poss ≠ []) (hposs : ∀ q ∈ poss, q < bs.length)
        (hpure : (mn == ``Signal.pure) = false) (hbin : signalBinOpOf mn = none)
        (hkind : ∀ ids, ids.length = bs.length →
          fallbackKind (instEN mn lvls (instFVars (ids.map .fvar).toArray 0 dE) ((poss.map fun q => ids[q]!).map .fvar)) = .other)
        (bnd : ChildBnd mref cref w) :
      (the conclusion of gate_parent_run, unchanged)

`EntryDefines`, `tag`, `hscalar`, `old`, `accept` are gone: `old` and the acceptance are `GateDefines`
at the run's own reads; the TAG is derived (`gate_pred hshape hsel`, then `instEN_pred_tag hne`) at the
entry's read `envR`, the value the translator was built from; `hscalar` is inside the acceptance.
`Tests/Compiler/GateParentRunGTest.lean` (target-only): `parentUse_sel`, `parentUse_gate_parent_runG`
(binders: the run, `GateDefines`, `ChildBnd`), axioms printed. Round-1 `gate_parent_run` kept as it was.

## 9. The cone (task 5): how far it got

Written:

* `Tools/ShippingGateConeLeafRuns.lean` — `fuelRec_keepsC`, `instanceArm_runW`, **`inst_leaf_runs`**
  as stated in §5 (the run's child `y` is a `RealChild`, THE end-cache entry of the callee,
  invariant / depth / every start entry kept, the rest `Returns (armCont … y …) ctx s wire s'`).
* `Tools/ShippingGateConeLeafContract.lean` — **`armCont_leaf_contract`**: `inst_leaf_contract`'s
  second half over `armCont rec mn y` for ANY pair `y`, with the child's facts about `y` and NO
  `hsub` / `htag`:

      Contract (armCont rec mn y) ctx inputs we mems initial (instEN mn lvls dom argsE) v

NOT written: the `RunsTo`-level fuel induction over the cone and `HierConePreserves` with `kids`. Why:
`HierConePreserves` is built by `fuel_contract_leaves` from leaf `Contract`s, and a `Contract` speaks
of EVERY `Returns` run, in any world — so the instance leaf's contract needs every run's child pinned
(the global `SubSynthDefinesAll`); in a world whose cache holds another pair the run returns that
pair. The composition must be redone at world level. Design: a cone run's leaves are pinned by the
FINAL cache `mF` of the parent's translation (`inst_leaf_runs` puts each child in the cache; entries
are kept; a repeated callee is a hit of the same pair); the linked semantics' children are read off `mF`.

Exact next statement:

    structure ContractW (L : RefLaws mref cref) (D : Nat) (mF : Std.HashMap Name Res)
        (rec : TranslateFn) (ctx : CompilerState) (inputs : FVarId → Option Value) (we : WEnv)
        (mems : MEnv) (initial : Env) (e : Lean.Expr) (v : Value) : Prop where
      keeps : ∀ hint top named s w0 r w1, InvV L w0 → L.dval w0 = D →
        RunsTo (rec e hint top named ctx s) mctx mref cctx cref w0 r w1 →
        InvV L w1 ∧ L.dval w1 = D ∧ SubMap (L.val w0) (L.val w1)
      frame : ∀ hint top named s t w w0 w1, Lookup ctx inputs s → InvV L w0 → L.dval w0 = D →
        SubMap (L.val w1) mF → RunsTo (rec e hint top named ctx s) … w0 (w, t) w1 → Frame s t
      sem : ∀ hint top named s t w prior w0 w1, Inv ctx inputs we mems initial s prior →
        ScalarWidthsAgree we t → InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
        RunsTo (rec e hint top named ctx s) … w0 (w, t) w1 → Outcome ctx inputs we mems initial prior s t w v

    theorem inst_leaf_contractW (hD : D ≠ 0) (fuel) (hpure) (hbin) (hkind)
        (htag : isHardwareModule tenv mn = true)
        (hkid : ∀ y, mF.get? mn = some y → (the child facts of armCont_leaf_contract for y))
        (hargs : ∀ k …, ContractW L D mF (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial argsE[k] vs[k])
        (meaning) (hsem) (hwidth) :
      ContractW L D mF (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
        (instEN mn lvls dom argsE) v

Its proof needs `armCont`'s operand runs (`instArgs`) at `RunsTo` level (like `bindInputPort_runs`) so
that `hargs` applies to them; then the twin of `fuel_contract_leaves` for `ContractW` (every cone node
re-walked at `RunsTo` level, the operands keeping the invariant by `translateRel`, the `SubMap` chain to
`mF`); then `HierConePreserves` with `mF`'s entries as the children.

## 10. Build order (round 2) and lean_lib lines

    lean_lib «Tools.ShippingGateDefines» where
      roots := #[`Tools.ShippingGateDefines]
    lean_lib «Tools.ShippingGateParentRunG» where
      roots := #[`Tools.ShippingGateParentRunG]
    lean_lib «Tools.ShippingGateConeLeafRuns» where
      roots := #[`Tools.ShippingGateConeLeafRuns]
    lean_lib «Tools.ShippingGateConeLeafContract» where
      roots := #[`Tools.ShippingGateConeLeafContract]

Order: `ShippingGateDefines` (independent of round 1) → `ShippingGateParentRunG` (needs round-1
`ShippingGateParentRun`) → `Tests.Compiler.GateParentRunGTest` (target-only; imports
`GateParentRunTest`). `ShippingGateConeLeafRuns` (needs round-1 `ShippingGateParentRuns`) and
`ShippingGateConeLeafContract` (imports `ShippingInstanceLeaf`, `ShippingInstArmGrow`) are independent.

## 11. Risks (round 2), in order

1. `mixedShape_cond`: the `simp only` reducing the outer `match` and the `if false || !…`; two
   `split at h`; `cases h` on `some (bs', body') = some (bs, body)`.
2. `parentUse_sel`: `rfl` evaluating the five predicate-free disjuncts and `hierGateRoot` without
   reaching the predicate (read: `hierGateBoolBody` falls to `false`; `gateTopWidth?` is `none` since
   the instance slot of the arguments is a binder).
3. `armCont_leaf_contract`: `unfold armCont at tr; rw [houts] at tr; exact tr`.
4. `instanceArm_runW`: the argument order of `armCont_keepsC`, the `legacyRel` projection, `childKeeps`.
5. `instEN_pred_tag`: `rw [List.map_append, List.foldl_append]; try rfl`.

---

# Round 3: the cone at world level (WRITTEN, NOT BUILT)

Branch `par/n-3` (from poc `9365dacb`). Nothing compiled or run. Round 1–2 files unchanged; compiler
files untouched; the classifier's ALLOWED list untouched.

## 12. Files, statements

### `Tools/ShippingGateConeW.lean`

* `RunsC c ctx s mctx mref cctx cref w p w'` := `RunsTo (c ctx s) …` (the action is an argument, so
  `split` sees the step's `if` / `match` exactly as the built `Returns` proofs do); `RunsC.bind`,
  `RunsC.pure`, `runsCReturns`.
* `keepsW` (a run of an action that keeps `J L' D` for every witness keeps `InvV`, the depth, and
  every cache entry — `WG.ofKeeps`), `fuel_runsW` (the translator at any fuel, `D ≠ 0`).
* **`ContractW L mF D rec ctx inputs we mems initial e v`** (structure, fields `frame`, `sem`): every
  returning `RunsC (rec e hint top named) ctx s … w0 (w, t) w1` with `InvV L w0`, `L.dval w0 = D`,
  `SubMap (L.val w1) mF` has the `Frame` / the `Outcome`. `ContractW.ofContract` (world-free →
  world-indexed), `ContractW.zero`, `ContractW.atRun` (one run's facts, `ChildAt`).
* `KidFacts children C mn n v y`: the premises of the built `armCont_leaf_contract` about the pair `y`
  (port shape, `children y.1.name = some (y.1, cwe)`, the text of `ChildCorrect`).
* the binary node: `core_binary_eq`, `binary_returnsW` (`binary_returns` with worlds),
  `binary_frameAt` / `binary_outcomeAt` (texts of `binary_frame` / `binary_outcome` over `ChildAt`),
  `binary_coreW`, **`binary_contractW`**.
* `cfrag` (leaves, `boolLit`, `bitsLit`, `bitsNum`, `binary`) and **`fuel_contractW`** (the text of
  `fuel_contract_leaves` on `cfrag`, leaves bring `ContractW` at every fuel).
* **`inst_leaf_contractW`** ([HierCtx] [ChildSem]):

      (hD : D ≠ 0) (hpure) (hbin) (hkind) (htag : isHardwareModule tenv mn = true)
      (hlenV) (hargs : ∀ k …, Contract (translateFuelFix (translateStep tenv) fuel) … argsE[k] vs[k])
      (meaning) (hsem : ChildSem.childSem mn vs = some v)
      (hkid : ∀ y, mF.get? mn = some y → KidFacts HierCtx.children inferInstance mn argsE.length v y) :
      ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) … (instEN mn lvls dom argsE) v

  Proof: `inst_leaf_runs` gives the run's child `y` as the END cache's entry; `SubMap (L.val w1) mF`
  makes it `mF`'s entry; `hkid` gives its facts; `armCont_leaf_contract` closes. No pinned child,
  no `HardwareTagged`.
* `InstLeafK` / `LeafK` (a leaf is a world-free `LeafContract` OR an instance leaf whose arguments
  have world-free leaf contracts and whose `mF` entry has `KidFacts`), **`leafK_contractW`** (every
  fuel, in `hierLink children`).

### `Tools/ShippingGateConeRun.lean`

* `prepare_cs` (the prepared context / state do not depend on the valuation), `outStructure`,
  `outRuns` (texts of `emitLeaves_structure_link` / `emitLeaves_runs_link` over one run's facts).
* **`HierConePreservesK tenv mF declName bs body m`**: `HierConePreserves` on `cfrag` with
  `LeafK … mF …` leaves in the place of `LeafContract` (and `tenv` a parameter).
* **`cone_harness_runK`**: `(L) (hD : D ≠ 0) (hw : InvV L w) (hd : L.dval w = D)
  (hr : RunsTo (synthesizeMixedCertified (translateExprToWire tenv) (profLogIO b) declName bs body) … (m, d) w')
  ⊢ ∃ wT', CacheInv mref cref (L.val wT') ∧ HierConePreservesK tenv (L.val wT') declName bs body m`
  — `mF` is the child cache at the END of the parent's translation (`wT'` from `mixedHarness_runs`).
* **`gate_cone_runG`** (the full entry):

      (hr : RunsTo (synthesizeCombinational f) … w (b, design) w')
      (gdef : GateDefines mctx mref cctx cref f bs body) (bnd : ChildBnd mref cref w) :
      ∃ M Dd envR a5 a6 mF, (b = dz M ∨ b = mergeChecked (dz M)) ∧ b.name = M.name ∧
        ((∀ x ∈ Dd.modules, x.name ≠ M.name) → design.modules = Dd.modules) ∧
        RunsTo getEnv … a5 envR a6 ∧ (∃ dv, mixedCertifiedShape? … (instancePredicate envR) = some (bs, body)) ∧
        CacheInv mref cref mF ∧ HierConePreservesK envR mF f bs body M

  Premises: `hr` (ALLOWED), `bnd` (ALLOWED), **`gdef` — `GateDefines`, NOT ALLOWED** (the round-2
  ruling is still pending). No `tag`, no pinned child. The per-leaf tag `isHardwareModule envR mn`
  is a consumer obligation inside `InstLeafK`, a fact of the value `envR` the conclusion exposes
  together with the gate's acceptance at it (deriving it from that acceptance for a cone body —
  inverting `hierGateBitsBody` at an instance leaf — is NOT done).

### `Tests/Compiler/GateConeRunTest.lean` (target-only)

`parentMix_coneK` (from `HierConePreservesK` + `tagR` + facts of `mF`'s `childAdd` entry `y`:
`y.1 = childModule`, `y.2.modules = []` → the S6 observation `ParentMixObserves M`, the conclusion of
the built `parentMix_entry_observes`), `parentMix_gate_cone_runG` (binders: the run, `GateDefines`,
`ChildBnd`; the three facts of the run's own values are antecedents of the conclusion), axioms
printed. PREDICTED axioms: `propext`, `Classical.choice`, `Quot.sound`.

## 13. Build order, lean_lib lines (added next to `Tools.ShippingGateConeLeafContract`)

    lean_lib «Tools.ShippingGateConeW» where
      roots := #[`Tools.ShippingGateConeW]
    lean_lib «Tools.ShippingGateConeRun» where
      roots := #[`Tools.ShippingGateConeRun]

1. `Tools.ShippingGateConeW` (imports `ShippingGateConeLeafRuns`, `ShippingGateConeLeafContract`,
   `ShippingChildTranslate`, `ShippingWalkGrow`, `ShippingHierTermSoundness`);
2. `Tools.ShippingGateConeRun` (imports 1 and `ShippingGateParentRunG`);
3. `lake build Tests.Compiler.GateConeRunTest`.

## 14. Risks, in the order I expect them

1. `leafK_contractW`: `letI` in the statement and `intro instH instC` (the let-bound instances must be
   local instances for `inst_leaf_contractW`'s synthesis). Fallback: state the conclusion as
   `@ContractW _ _ (hierLink children).toLinkCtx C L …` and `letI` in the proof.
2. `binary_contractW`: `unfold translateStepWith at hr; dsimp only at hr; split at hr` on `RunsC`
   (mirrors `binary_contract`); the `subst` directions in the hit branch (`hs : sh = s` eliminates `s`).
3. `core_binary_eq`: whether `simp only […]` closes the equation (a `try rfl` follows).
4. `binary_returnsW`: `simp only [width] at hr`, the beta-redex continuations under `RunsC.bind`,
   `cases u` (Unit).
5. `keepsW`: the named arguments of `WG.ofKeeps`.
6. `ContractW.zero`: `Returns.throw` unifying `throw ?e` with `translateFuelFix … 0 e …` (as in the
   built `fuel_contract_leaves`).
7. `prepare_cs`: `show` through `extend`'s `let`/`match`; `cone_harness_runK`: `rw [← hpc, ← hps] at htr`
   needs the `fun _ => false` / `fun _ _ => 0` of `mixedHarness_runs` to match syntactically.
8. Test: `by decide` on `(childModule, y2).1` port facts, `rfl` for `hkind`, `cases hy'`.

## 15. Not covered (the exact next pieces)

* the other cone nodes at world level (`compare`, `boolBinary`, `boolNot`, `boolEq`, `mux`, `setw`,
  slices, concatenations, applicative forms): each is `binary_contractW`'s pattern — a `RunsC`
  decomposition of the node's lowering (`…_returnsW`), the built `…_outcome` text over `ChildAt`,
  and a `cfrag` constructor;
* instance leaves with instance ARGUMENTS (`parentNested`): `instArgs` at world level, `hargs` as
  `ContractW` (the §9 statement);
* deriving the leaf tag from `GateDefines`' acceptance of a cone body.

---

# Round 4: the leaf tag from the gate's acceptance (WRITTEN, NOT BUILT)

Branch `par/n-4` (from poc `2fb68bc7`). Nothing compiled or run. Rounds 1–3 files unchanged;
compiler files untouched; the classifier's ALLOWED list untouched.

## 16. What was asked, what is done

`parentMix_gate_cone_runG` (round 3) concludes `ParentMixObserves M` under three antecedents about the
run's own values: (a) `isHardwareModule envR ``childAdd = true`, (b) `mF`'s `childAdd` entry `y` has
`y.1 = childModule`, (c) `y.2.modules = []`.

**(a) DISCHARGED, generally.** `Tools/ShippingGateConeTag.lean`:

* `GateLeafSel kinds body leaf := ∀ isInst sc, isInst leaf = false → mixedGateCond isInst kinds body sc = false`
  — pure, per declaration; the leaf twin of the built `MixedGateSel`.
* `gate_leaf_pred` (acceptance under `instancePredicate env` + `GateLeafSel` ⟹ the predicate designates
  the leaf), `gate_leaf_tag` / `gate_leaf_tag'` (for `instEN mn lvls dE (poss.map (inputExpr n))`,
  `poss ≠ []`: `isHardwareModule env mn = true`, via the built `instEN_pred_tag`; `'` takes the
  `∃ dv, mixedCertifiedShape? … (instancePredicate envR) = some (bs, body)` that `gate_cone_runG` exposes).
  Any cone body, any leaf position, any callee.
* Discharging `GateLeafSel` by evaluation without `DecidableEq Expr`: `bvarCallE mn is` (the call
  `.const mn []` on bound variables), `bvarCall` (a kernel-reducible recogniser), `bvarCall_sound`, and
  `gateLeafSel_of`: it suffices that `mixedGateCond (fun e => !bvarCall mn is e && isInst e) kinds body sc
  = false` for every `isInst` (funext: that predicate IS `isInst` once `isInst leaf = false`). Per
  declaration this is `unfold mixedGateCond unifiedInstanceRoot hierInstRoot`, the two body spines
  rewritten to `false` (closed `rfl` facts — `hierInstSpine` reaches the leaf, which the predicate
  refuses), then kernel `rfl`.

`Tests/Compiler/GateConeTagTest.lean` (target-only): `parentMix_leaf_eq` (rfl), `parentMix_leafSel`,
`parentMix_tag`, and **`parentMix_gate_cone_runG'`** — binders the run, `GateDefines`, `ChildBnd`;
conclusion `∃ M envR mF, post ∧ CacheInv mF ∧ isHardwareModule envR ``childAdd = true ∧
(∀ y, mF.get? ``childAdd = some y → y.1 = childModule → y.2.modules = [] → ParentMixObserves M)`.
The old theorem is kept.

**(b) NOT dischargeable; (c) not discharged.** Why:

1. `childAdd x y := x + y` (uniform 8-bit `+` under `{dom}`) is accepted by the FIRST gate
   (`certifiedShape?`: `gateTopWidth? = some 8`, `gateBody` accepts), so its full entry goes through
   `synthesizeCertified`, not `synthesizeMixedCertified`. The built child facts from a `RealChild` —
   `childFull_of_real` (design `= []`), `gate_real_ports`, `gate_child_full` — are for MIXED-gate
   children (`old : certifiedShape? … = none` is one of their premises) and do not apply.
2. (b) asks for TEXT equality with the hand-written `childModule`. No theorem pins a full-entry module's
   text (the first gate's `Preserves`/`fragmentDecl_*` give semantics and ports only; the wire names come
   from the run's allocator). A `RunsTo` cannot be evaluated in the kernel, so "by computation per
   declaration" is not available either. (b) should be REMOVED, not proved: restate the observation over
   the run's own child, i.e. `children := fun n => if n = y.1.name then some (y.1, weOf y.1) else none`,
   and prove `KidFacts children addSem ``childAdd 2 v y` from `RealChild ``childAdd y`.
3. What that needs (a "first-gate child" unit, all outside the compiler):
   * `fragmentDecl_of_entry`: `fragmentDecl_of_env` with `EnvDefines` replaced by
     **`EntryDefines … ``childAdd (quoteDecl `dom [`x, `y] 8 (.bin .add (.inp 0) (.inp 1)))`** (ALLOWED):
     `synthesizeCombinationalCore_reads`, `EntryDefines` at the reads, `synthesizeFromConst_sound` on the
     entry constant, `outcome_quote`; then the full-entry form via `synthesizeCombinational_reads` +
     `postprocess_sound` (evaluation for EVERY initial environment — KidFacts' evaluation has no `rst`
     premise, and the fragment facts have none either; `weOf y.1` as `cwe`); ports: `PostReady` gives
     `outputs = [out : bitVector 8]` and input-name `Nodup`;
   * input names are not `clk` / `rst` / `out`: an allocation fact for `bindCertifiedInputs`' port names
     (new; the mixed route's is `pb.wireNames`);
   * **(c)** `y.2.modules = []`: `synthesizeCertified` returns `st.design` (`finishSynth_returns`) and the
     full entry only maps the design's modules; what is missing is that the first-gate translation of an
     instance-free body leaves `st.design.modules = []` (a design frame for `bindCertifiedInputs` /
     `emitLeaves` / the `FExpr` arms; the mixed route has it as `hdes`).
   The new theorem would then carry one more ALLOWED binder (`EntryDefines` of `childAdd`) and NO
   antecedent; its conclusion would observe `M` linked against the run's child rather than `childModule`.

Optional `compare` node at world level: NOT written this round.

## 17. Build order, lean_lib lines

    lean_lib «Tools.ShippingGateConeTag» where
      roots := #[`Tools.ShippingGateConeTag]

(added to `lakefile.lean` after `Tools.ShippingGateConeRun`).

1. `Tools.ShippingGateConeTag` (imports `Tools.ShippingGateDefines` only; independent of rounds 3);
2. `lake build Tests.Compiler.GateConeTagTest` (imports `Tests.Compiler.GateConeRunTest` and 1).

Premises of `parentMix_gate_cone_runG'`: `hr` (RunsTo, ALLOWED), `gdef` (`GateDefines`, NOT ALLOWED —
ruling pending, unchanged), `bnd` (ChildBnd, ALLOWED). Antecedents left in the conclusion: (b), (c).
PREDICTED axioms: `propext`, `Classical.choice`, `Quot.sound` (`parentMix_tag` may print only `propext`
or fewer).

## 18. Risks, in the order I expect them

1. `parentMix_leafSel`: that `simp only [hs1, hs2, Bool.and_false, Bool.false_and]` finds the two spine
   disjunctions after `unfold` (beta-redexes `(fun e => …) parentMixBody`; `parentMixBody` is an
   `abbrev`); then the final kernel `rfl` (evaluates `mixedGateBoolBody`, `mixedGateVectorRoot`,
   `unifiedGateRoot`, the register / memory roots and `hierGateRoot` on the body — the last reaches the
   leaf through `hierGateBitsBody`'s operator arm and the predicate's `bvarCall` → `false`).
   Fallback: `show` the condition with the two instance disjuncts already `false`, or `decide`-free
   `Bool` case split `cases isInst parentMixBody` after `simp only [mixedGateCond, …]`.
2. `hs1` / `hs2` by `rfl` (the leaf is `if 0 = 0 then instEN … else …` inside the abbrev: whnf).
3. `bvarCall_sound`: `simp only [bvarCall, …] at h` on the two matching arms; the impossible
   constructor cases by `cases h` (whnf of `bvarCall` to `false`) else `simp [bvarCall] at h`;
   `rw [h1, h2]; try rfl` in the `const` arm (no `subst` of the theorem's parameter `mn`); `subst h1`
   (`k = i`, two pattern variables) in the `app` arm.
4. `gateLeafSel_of`: `rw [← heq]` abstracting the free `isInst` in the goal.
5. `parentMix_tag`: `rw [parentMix_leaf_eq] at h0` and the implicit arguments of `gate_leaf_tag'`
   (given explicitly).

---

# Round 5: the cone theorem with no antecedent (WRITTEN, NOT BUILT)

Branch `par/n-5` (from poc `83010ed1`). Nothing compiled or run. Rounds 1–4 files unchanged;
compiler files untouched; the classifier's ALLOWED list untouched.

## 19. What was asked, what is done

`parentMix_gate_cone_runG'` (round 4) still had two antecedents about `mF`'s entry `y` of
`childAdd`: (b) `y.1 = childModule`, (c) `y.2.modules = []`. Both are gone from the new theorem
`parentMix_gate_cone_runK` (`Tests/Compiler/GateConeKidTest.lean`); the old theorems are kept.

* **(b) replaced** (as recommended in §16): the observation is stated against the run's OWN child,
  `ownChild y := fun s => if s = y.1.name then some (y.1, declWidth y.1) else none`
  (`ParentMixObservesC (ownChild y) M`; `ParentMixObserves M = ParentMixObservesC (childrenOf
  childModule.name) M` by `rfl`, `parentMixObserves_pinned`).
* **The first-gate child unit** (`Tools/ShippingFirstGateChild.lean`, general — any first-gate
  declaration `quoteDecl dn names n fe`, `fe.WF`, `0 < n`):
  * **the bridge** `bindCertified_mixed`: `bindCertifiedInputs k (bs.zip ids) =
    bindMixedCertifiedInputs k ((bs.map mixB).zip ids)` (by the two definitions; `mixB` sends
    `.signal n ↦ .bits n`). `synthesizeCertified` is otherwise the mixed harness verbatim, so
    `synthesizeCertified_returnsM` gives `synthesizeMixedCertified_returns`' conclusion at
    `firstBs dn names n := (quoteBinders dn names n).map mixB`, and `first_body` shows the body is
    `quote` of the unified term `ofF n fe` at positions `0` (domain) / `j+1` (inputs). Every built
    harness theorem then applies to a first-gate run: `first_core_run` (core run + `EntryDefines`
    ⇒ mixed-harness run, existential over the run's `envR`);
  * `fragmentDecl_of_entry` (= `fragmentDecl_of_env` with `EnvDefines` → `EntryDefines`),
    `synthesizeCombinational_fragment_entry` (full entry, via `synthesizeCombinational_reads` +
    `postprocess_sound`), `first_core_postReady`, `first_full_outputs` (`outputs = [out :
    bitVector n]`), `first_full_inputs` (input names `Nodup`, `length = names.length`, every input
    `Allocated`, ≠ `clk` / `rst` / `out`);
  * **(c) the design frame**: `first_core_design` (core `D.modules = []`, from
    `transition_closed`'s `st.design = init.design`, i.e. the spine's `Ext` over the bridged run)
    and `ChildFull.design` (full entry) — no new frame proof was needed;
  * `first_child_fullFacts`: `ChildFull c (firstBs …) b design` (the text of
    `gate_child_comb` + `gate_child_fullFacts` with the core run replaced by the bridge);
  * `ChildFnR` (= `ChildFn` without its `env "rst" = 0` premise, which `gate_childFn` never used),
    `gate_childFnR`, `childFnR_dropZW`, `childFnR_merge`, `childFnR_post` (the built proofs with that
    binder dropped), `first_child_fnR`: the full-entry module computes `firstFn` of its argument
    ports on EVERY environment; `firstFn_eval`: `firstFn … vals = evalFE n (ofNat ∘ vals.getD) fe`
    (`portIdx_first`, `evalFE_congr`).
* **`KidFacts` from `RealChild`** (`Tools/ShippingFirstGateKid.lean`): `kidFacts_of_first` /
  `kidFacts_of_first'`: `EntryDefines c (quoteDecl dn names n fe)` (moved to the child's own
  contexts by `EntryDefines.ctx`) + `RealChild c y` + a spec `hC` of the consumer's `C` on `c`
  (argument count, in-range values, result `= evalFE`) ⇒ `KidFacts (ownChild y) C c names.length v y`.
  `hC` is a property of `C` alone; for `addSem` it is `addSem_spec`, by evaluation.
* Test: `childAddEntry = childAddValue` (`#def_entry_value`, `rfl`) pins the `EntryDefines` value to
  the real `childAdd`'s entry constant; `parentMix_coneKC` is `parentMix_coneK` over any linked
  context whose `childAdd` entry has `KidFacts`.

## 20. Build order, lean_lib lines

    lean_lib «Tools.ShippingFirstGateChild» where
      roots := #[`Tools.ShippingFirstGateChild]
    lean_lib «Tools.ShippingFirstGateKid» where
      roots := #[`Tools.ShippingFirstGateKid]

(added after `Tools.ShippingGateConeTag`).

1. `Tools.ShippingFirstGateChild` (imports `ShippingGateChildComb`, `ShippingPostSoundness`);
2. `Tools.ShippingFirstGateKid` (imports 1, `ShippingGateConeW`, `ShippingReflectCtx`);
3. `lake build Tests.Compiler.GateConeKidTest` (imports `Tests.Compiler.GateConeTagTest` and 2).

Premises of `parentMix_gate_cone_runK`: `hr` (RunsTo, ALLOWED), `gdef` (`GateDefines`, NOT ALLOWED —
ruling pending, unchanged), `bnd` (ChildBnd, ALLOWED), **`centry : EntryDefines … ``childAdd
childAddValue` (ALLOWED, the one new binder)**. No antecedent in the conclusion except the cache
lookup `mF.get? ``childAdd = some y` (as before: the existence of the entry is not concluded).
PREDICTED axioms: `propext`, `Classical.choice`, `Quot.sound`.

## 21. Risks, in the order I expect them

1. `bindCertified_mixed`: `simp only [List.zip_cons_cons, List.map_cons, mixB, bindCertifiedInputs,
   bindMixedCertifiedInputs]` (the equation lemmas of the two structural walks and of `mixB`), and
   the `rfl` nil cases (`List.zip [] _` / `zip (_ :: _) []` by whnf). Fallback: `show` the unfolded
   `bindInputPort …` forms.
2. `firstBs_filter` / `portIdx_first`: the head `(dn, .domain)` dropped by `filter` — `exact` by
   defeq, else the `simp only [List.filter_cons, bne_self_eq_false, …]` alternative; `List.take_succ_cons`
   name.
3. `first_child_fullFacts` / `first_core_design` / `first_child_fnR`: elaboration of
   `transition_closed` / `transition_facts` with the named `(dom := …) (bpos := fun _ => 0)
   (vpos := fun j => j + 1)` and `first_body` (beta-redexes `(fun _ => 0) j`, defeq only);
   `hcomb`'s `rcases hpost with rfl | rfl` inside a `have … := by`.
4. `synthesizeCertified_returnsM`: `rw [bindCertified_mixed] at run'` (the term under `Returns`
   after `MReturns.run`), `split at hr` on the `if hids`.
5. `kidFacts_of_first`: the anonymous constructor for `KidFacts` (a `def`; same form as the built
   `parentMix_coneK`), `List.cons.inj` / `subst` of the output port, `List.getElem_map` rewrites in
   `hvals`, `rw [← hfe]` matching the `evalFE` term of `hC`.
6. Test: `childAddEntry = childAddValue := rfl` (binder names `dom`, `x`, `y` of the real `childAdd`;
   if it fails, the premise value is wrong, not the proofs); `addSem_spec`'s `show` of the
   evaluated `evalFE`/`List.sum` and the `BitVec.toNat_*` rewrites (a `simp` alternative follows);
   `childAdd_fe_wf`'s `⟨(by decide : 0 < 2), (by decide : 1 < 2)⟩` against `FExpr.WF`.
7. `gate_childFnR`: a verbatim copy of `gate_childFn`'s proof under a superset of its opens (name
   ambiguity from the extra `open`s is the only new risk).
