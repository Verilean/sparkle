import Tools.ShippingGateParentRun
import Tools.ShippingGateDefines

/-! # `gate_parent_run` on the gate reflection `GateDefines` (worker N, round 2)

WRITTEN, NOT BUILT.

`gate_parent_runG`: the round-1 `gate_parent_run` with ONE reflection premise,
`GateDefines f bs body` (`Tools/ShippingGateDefines.lean`), in the place of
`EntryDefines` + `tag` + `hscalar` + `old` + `accept`:

* the entry constant, the first gate's refusal and the mixed gate's
  acceptance under `instancePredicate envR` are what `GateDefines` states at
  the run's own reads;
* the callee's TAG at the translator's environment is DERIVED: the
  acceptance plus the pure selection fact `MixedGateSel` (only an instance
  disjunct accepts the body) give `instancePredicate envR body = true`
  (`gate_pred`), and the last argument being a binder excludes the
  predicate's projection disjunct (`instEN_pred_tag`, the argument of the
  built `spine_tag`) — the environment is the ONE value the entry read and
  built the translator from;
* `hscalar` is not needed: the scalar test is inside the acceptance.

`GateDefines` is NOT in the classifier's ALLOWED list (a ruling is asked):
until then `gate_parent_runG` carries one NOT ALLOWED reflection premise.
`gateDefines_of_entry`: the round-1 premises imply `GateDefines`, so the
round-1 theorem (kept as is) is no weaker in what it assumes. -/
namespace Tools.ShippingGateParentRun
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingInstanceEntrySoundness (instEN instancePredicate_instEN)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingGateDefines

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **The round-1 premises give `GateDefines`.** -/
theorem gateDefines_of_entry {f : Lean.Name} {value : Lean.Expr}
    {bs : List (Lean.Name × MixedGateBinder)} {mn : Lean.Name} {lvls : List Level}
    {dE : Lean.Expr} {poss : List Nat}
    (entry : EntryDefines mctx mref cctx cref f value)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Lean.Environment) mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e mn = true)
    (hscalar : ∀ dv : DefinitionVal, dv.value = value → mixedGateResultScalar dv.type = true)
    (old : ∀ dv : DefinitionVal, dv.value = value → certifiedShape? false [] (.defnInfo dv) = none)
    (accept : ∀ dv : DefinitionVal, dv.value = value → mixedGateResultScalar dv.type = true →
      ∀ isInst : Lean.Expr → Bool,
        isInst (instEN mn lvls dE (poss.map (inputExpr bs.length))) = true →
        mixedCertifiedShape? false [] (.defnInfo dv) isInst =
          some (bs, instEN mn lvls dE (poss.map (inputExpr bs.length)))) :
    GateDefines mctx mref cctx cref f bs (instEN mn lvls dE (poss.map (inputExpr bs.length))) := by
  intro w1 ci w2 w5 envR w6 hget henv
  obtain ⟨dv, hdv, hval⟩ := entry w1 ci w2 w5 envR w6 hget henv
  exact ⟨dv, hdv, old dv hval, accept dv hval (hscalar dv hval) _
    (instancePredicate_instEN envR mn lvls _ _ (tag w5 envR w6 henv))⟩

/-- **`gate_parent_run` on the gate reflection.** The conclusion of
`gate_parent_run`; the premises: the run, `GateDefines` (NOT ALLOWED until
ruled), `ChildBnd`, and pure facts of the reflected body. -/
theorem gate_parent_runG {f : Lean.Name}
    {bs : List (Lean.Name × MixedGateBinder)} {mn : Lean.Name} {lvls : List Level}
    {dE : Lean.Expr} {poss : List Nat}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs (instEN mn lvls dE (poss.map (inputExpr bs.length))))
    (hsel : MixedGateSel (bs.map (·.2)).toArray (instEN mn lvls dE (poss.map (inputExpr bs.length))))
    (hne : poss ≠ [])
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
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨M2, D2, w2, hcore2, -, hname, hmods⟩ := Tools.ShippingCacheCoherentRun.full_split L hr
  obtain ⟨hMD, -⟩ := runsTo_det hcore2 hcore
  obtain ⟨hM, hD⟩ := Prod.mk.inj hMD
  rw [hM] at hname
  rw [hM, hD] at hmods
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
  -- the reflection at the run's own reads
  obtain ⟨dv, hdv, hold, hshape⟩ := gdef a1 ci a2 a5 envR a6 hget henv
  rw [hdv] at run
  -- the tag at the entry's read, from the acceptance
  have htag : Sparkle.Compiler.isHardwareModule envR mn = true :=
    instEN_pred_tag hne (gate_pred hshape hsel)
  obtain ⟨wa, wb, hwa, hda, hharn⟩ := sfc_mixed_run L hold hshape hw3 run
  obtain ⟨y, ids, cache, hreal, nd, len, hshapeN⟩ :=
    parent_core_instanceN (tenv := envR) L (D := L.dval wa) (by rw [hda]; exact hd3)
      hposs htag hpure hbin hkind hwa rfl hharn
  exact ⟨M, D, y, ids, cache, hpost, hname, hmods, hreal, nd, len, hshapeN⟩

end Tools.ShippingGateParentRun
