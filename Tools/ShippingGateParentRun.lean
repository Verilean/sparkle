import Tools.ShippingGateParentRuns
import Tools.ShippingGateParentTail
import Tools.ShippingCacheCoherentOuter
import Tools.ShippingMachineShipping
import Tools.ShippingInlineSoundness

variable {tenv : Lean.Environment}

/-! # `gate_parent_run` for the instance-root parents (worker N, round 1)

WRITTEN, NOT BUILT.

A gate-route PARENT whose body is one call of a `@[hardware_module]` child on
its binders (`parentUse`, `wrapAdd`, `wrapPick`: the canonical n-ary call
`instEN mn lvls dom args`, the domain a binder or a closed constant): a
returning run of the FULL entry `synthesizeCombinational f`, from a world
satisfying `ChildBnd`, returns the cleaned (and possibly merged) module of a
core module whose shape is the S6 n-ary instance shape over THE CHILD PAIR
THE RUN'S OWN NESTED SYNTHESIS RETURNED — a `RealChild` of the callee (a run
of the real full entry on it, over these state references) — with no
`HardwareTagged` / `SubSynthDefines` premise.

* `runsTo_det` — two returning runs of one action from one world in one
  context agree (`RunsTo` is an equation of the run function);
* `sfc_mixed_run` — the mixed arm of `synthesizeFromConst`, with worlds: the
  harness run, from an invariant world of the start depth, returns the arm's
  result (the text of the built `sfc_mixed_val`, keeping the run);
* `parent_core_instanceN` — the harness shell (`mixedHarness_runs`), the
  dispatch step (`instanceN_step`), the instance arm with its states
  (`instanceArm_run`) and the shape tail (`armCont_instanceN_tail`);
* `gate_parent_run`.

## The premises of `gate_parent_run`, and the two that are NOT reflections in the classifier's list

The run (`RunsTo`), the reflection `EntryDefines f value`, `ChildBnd` — the
classifier's ALLOWED forms — and pure facts of the gate's reading of the
value (`old`, `accept`, `hposs`, `hpure`, `hbin`, `hkind`: functions of
expressions, no world). Two more, both of the form the BUILT S6 entry
endpoints (`instanceN_entry_of_env`) already carry:

* `tag` — every `getEnv` read in these contexts designates the callee. It is
  NOT derivable from `EntryDefines`: `EntryDefines` pins the entry
  constant's VALUE, and when the callee is not designated the mixed gate
  refuses the parent and `entryConst` may return the declaration as read —
  with the same value — so the run would take another route; nothing in the
  run's value distinguishes the two.
* `hscalar` — the entry constant's TYPE is one scalar Signal (the mixed
  gate's instance disjuncts test the declaration's type,
  `mixedGateResultScalar d.type`). `EntryDefines` says nothing of the type.

Both are facts about the run's environment, of the kind `EntryDefines` is,
but not in `Tools.ShippingFinalGoalCommand.allowed`. The alternative is ONE
reflection of the gate's acceptance at the run's read (the gate analogue of
`MachineDefines`, which already reads `mixedCertifiedShape? … (instancePredicate
envR)`): docs/parallel/N-gate-parent-run.md §4. -/
namespace Tools.ShippingGateParentRun
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv
open Tools.ShippingMixedEntrySoundness (Setup start prepare)
open Tools.ShippingMixedSourceBridge (inputExpr instantiated_input)
open Tools.ShippingInstanceEntrySoundness (instEN instEN_getAppFn instFVars_instEN
  instanceN_step instancePredicate_instEN)
open Tools.ShippingInlineSoundness (EntryDefines)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- Two returning runs of one action from one world agree. -/
theorem runsTo_det {α : Type} {m : MetaM α} {w : Void IO.RealWorld} {a1 a2 : α}
    {w1 w2 : Void IO.RealWorld}
    (h1 : RunsTo m mctx mref cctx cref w a1 w1) (h2 : RunsTo m mctx mref cctx cref w a2 w2) :
    a1 = a2 ∧ w1 = w2 := by
  unfold RunsTo at h1 h2
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

/-- **The mixed arm of `synthesizeFromConst`, with the run**: the log line,
the harness, the memo insert, `return`. The harness starts in an invariant
world of the arm's start depth and returns the arm's result. -/
theorem sfc_mixed_run (L : RefLaws mref cref) {b : Bool} {declName : Lean.Name}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hw : InvV L w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n)
      (profLogIO b) declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ wa wb : Void IO.RealWorld, InvV L wa ∧ L.dval wa = L.dval w ∧
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named)
        (profLogIO b) declName bs body) mctx mref cctx cref wa (m, d) wb := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  obtain ⟨_, wa, hlog, hr⟩ := RunsTo.bind hr
  obtain ⟨⟨hva, hsa, hda⟩, hqa⟩ := L.sameD (.profLog _ _) hlog hw.2.2
  have hwa : InvV L wa := ⟨by rw [hva]; exact hw.1, by rw [hsa]; exact hw.2.1, hqa⟩
  obtain ⟨res, wb, hharn, hr⟩ := RunsTo.bind hr
  obtain ⟨_, wc, hmod, hr⟩ := RunsTo.bind hr
  obtain ⟨hres, -⟩ := RunsTo.pure_world hr
  subst hres
  exact ⟨wa, wb, hwa, hda, hharn⟩

/-- **The core of a gate-route instance parent.** A returning run of the
harness on the canonical n-ary call body, from an invariant world of positive
depth, with the callee designated in the translator's environment: the
child pair of the run's own nested synthesis is a `RealChild`, and the
returned pair has the S6 n-ary shape over it. -/
theorem parent_core_instanceN (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {mn : Lean.Name} {lvls : List Level} {dE : Lean.Expr} {poss : List Nat}
    (hposs : ∀ q ∈ poss, q < bs.length)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : ∀ ids : List FVarId, ids.length = bs.length →
      fallbackKind (instEN mn lvls (instFVars (ids.map Lean.Expr.fvar).toArray 0 dE)
        ((poss.map fun q => ids[q]!).map Lean.Expr.fvar)) = .other)
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs (instEN mn lvls dE (poss.map (inputExpr bs.length))))
      mctx mref cctx cref w (m, d) w') :
    ∃ (y : Res) (ids : List FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
      RealChild mref cref mn y ∧ ids.Nodup ∧ ids.length = bs.length ∧
      InstanceNShape declName bs ids cache (poss.map fun q => ids[q]!) y m d := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, -, hm, hdd⟩ :=
    mixedHarness_runs L hw hd hr
  -- the instantiated body: the call on the fresh ids
  have hinst : instFVars (ids.map Lean.Expr.fvar).toArray 0
      (instEN mn lvls dE (poss.map (inputExpr bs.length))) =
      instEN mn lvls (instFVars (ids.map Lean.Expr.fvar).toArray 0 dE)
        ((poss.map fun q => ids[q]!).map Lean.Expr.fvar) := by
    rw [instFVars_instEN]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    exact instantiated_input len (hposs q hq)
  rw [hinst] at htr
  -- the dispatch step lands in the instance arm
  have stepEq : translateExprToWire tenv
      (instEN mn lvls (instFVars (ids.map Lean.Expr.fvar).toArray 0 dE)
        ((poss.map fun q => ids[q]!).map Lean.Expr.fvar)) "out" false true =
      translateInstanceOrFallback tenv (translateFuelFix (translateStep tenv) 1048575)
        (instEN mn lvls (instFVars (ids.map Lean.Expr.fvar).toArray 0 dE)
          ((poss.map fun q => ids[q]!).map Lean.Expr.fvar)) "out" false true := by
    show translateStepWith (translateFallback tenv) (translateFuelFix (translateStep tenv) 1048575)
      (instEN mn lvls (instFVars (ids.map Lean.Expr.fvar).toArray 0 dE)
        ((poss.map fun q => ids[q]!).map Lean.Expr.fvar)) "out" false true = _
    exact instanceN_step _ mn lvls _ _ _ _ _ hpure hbin (hkind ids len)
  rw [stepEq] at htr
  -- the arm: the run's own child, and the rest of the run on it
  obtain ⟨y, hreal, harm⟩ := instanceArm_run L (instEN_getAppFn mn lvls _ _) htag hwT
    (by rw [hdT]; exact hD) htr
  exact ⟨y, ids, cache, hreal, nd, len, armCont_instanceN_tail harm hst hm hdd⟩

/-- Gate acceptance by the PIPELINE root disjunct (`hierInstRoot`, the last
disjunct of `mixedCertifiedShape?`): the form a parent written at a concrete
domain takes (`wrapAdd`, `wrapPick`: the domain argument is a closed
constant, so the canonical spine `unifiedInstanceSpine` refuses it). For
`gate_parent_run`'s `accept` premise: `hroot` is computed per declaration
(`unfold hierInstRoot; rw [hI]; rfl`). -/
theorem instanceNH_term_gate {d : DefinitionVal} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {isInst : Lean.Expr → Bool}
    (peel : mixedGatePeel d.value = some (bs, body))
    (hroot : hierInstRoot isInst (bs.map (·.2)).toArray body = true)
    (hscalar : mixedGateResultScalar d.type = true) :
    mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, body) := by
  simp only [mixedCertifiedShape?, List.isEmpty_nil, Bool.not_true, peel, hroot, hscalar,
    Bool.and_true, Bool.true_and, Bool.or_true, if_true, ↓reduceIte]
  try rfl

/-- **`gate_parent_run` for the instance-root parents.** From a returning run
of the full entry on `f` from a `ChildBnd` world, the entry reflection, the
two environment facts of the S6 entry endpoints (`tag`, `hscalar`; file
header) and the pure gate reading: the returned module is the cleaned (and
possibly merged) module of a core module `M` (same name); the returned
design is the core design `D` when no module of `D` is named like `M`; the
callee's pair `y` is a `RealChild` (a run of the real full entry on `mn`
over these state references); and `(M, D)` has the S6 n-ary instance shape
over `y` — the instance statement of `y.1`, the design `[y.1]`, the
connections reading the parent's prepared input wires — under the child's
port shape. -/
theorem gate_parent_run {f : Lean.Name} {value : Lean.Expr}
    {bs : List (Lean.Name × MixedGateBinder)} {mn : Lean.Name} {lvls : List Level}
    {dE : Lean.Expr} {poss : List Nat}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref f value)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Lean.Environment) mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e mn = true)
    (hscalar : ∀ dv : DefinitionVal, dv.value = value → mixedGateResultScalar dv.type = true)
    (old : ∀ dv : DefinitionVal, dv.value = value → certifiedShape? false [] (.defnInfo dv) = none)
    (accept : ∀ dv : DefinitionVal, dv.value = value → mixedGateResultScalar dv.type = true →
      ∀ isInst : Lean.Expr → Bool,
        isInst (instEN mn lvls dE (poss.map (inputExpr bs.length))) = true →
        mixedCertifiedShape? false [] (.defnInfo dv) isInst =
          some (bs, instEN mn lvls dE (poss.map (inputExpr bs.length))))
    (hposs : ∀ q ∈ poss, q < bs.length)
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : ∀ ids : List FVarId, ids.length = bs.length →
      fallbackKind (instEN mn lvls (instFVars (ids.map Lean.Expr.fvar).toArray 0 dE)
        ((poss.map fun q => ids[q]!).map Lean.Expr.fvar)) = .other)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (y : Res) (ids : List FVarId)
      (cache : IO.Ref (Lean.ExprStructMap String)),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      b.name = M.name ∧
      ((∀ x ∈ D.modules, x.name ≠ M.name) → design.modules = D.modules) ∧
      RealChild mref cref mn y ∧ ids.Nodup ∧ ids.length = bs.length ∧
      InstanceNShape f bs ids cache (poss.map fun q => ids[q]!) y M D := by
  obtain ⟨L, ⟨hsv, hdep⟩, hq⟩ := bnd
  -- the full entry: the core run and the post passes
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨M2, D2, w2, hcore2, -, hname, hmods⟩ := Tools.ShippingCacheCoherentRun.full_split L hr
  obtain ⟨hMD, -⟩ := runsTo_det hcore2 hcore
  obtain ⟨hM, hD⟩ := Prod.mk.inj hMD
  rw [hM] at hname
  rw [hM, hD] at hmods
  -- the entry's reads and the body's start world (outermost or nested)
  have hreads : ∃ (bb : Bool) (envR : Lean.Environment) (ci : ConstantInfo)
      (a1 a2 a3 a4 a5 a6 : Void IO.RealWorld),
      RunsTo (getConstInfo f) mctx mref cctx cref a1 ci a2 ∧
      RunsTo (Lean.getEnv : MetaM Lean.Environment) mctx mref cctx cref a5 envR a6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n)
        (profLogIO bb) f [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref a3 (M, D) a4 ∧ InvV L a3 ∧ L.dval a3 ≠ 0 := by
    by_cases h0 : L.dval w = 0
    · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
        Tools.ShippingCacheCoherentOuter.core_reads_val0 L (fun L' => bodyRel L') hsv hq h0 hcore
      exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
    · rcases hdep with hz | hci
      · exact absurd hz h0
      · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
          Tools.ShippingCacheCoherentVia.core_reads_val L (fun L' => bodyRel L')
            ⟨hci, hsv, hq⟩ h0 hcore
        exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
  obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩ := hreads
  -- the reflection: the entry constant; the gate at the entry's predicate
  obtain ⟨dv, hdv, hval⟩ := entry a1 ci a2 a5 envR a6 hget henv
  rw [hdv] at run
  have htag : Sparkle.Compiler.isHardwareModule envR mn = true := tag a5 envR a6 henv
  have shape := accept dv hval (hscalar dv hval) (Sparkle.Compiler.Elab.instancePredicate envR)
    (instancePredicate_instEN envR mn lvls _ _ htag)
  -- the mixed arm, the harness, the instance arm and the shape
  obtain ⟨wa, wb, hwa, hda, hharn⟩ := sfc_mixed_run L (old dv hval) shape hw3 run
  obtain ⟨y, ids, cache, hreal, nd, len, hshape⟩ :=
    parent_core_instanceN (tenv := envR) L (D := L.dval wa) (by rw [hda]; exact hd3)
      hposs htag hpure hbin hkind hwa rfl hharn
  exact ⟨M, D, y, ids, cache, hpost, hname, hmods, hreal, nd, len, hshape⟩

end Tools.ShippingGateParentRun
