import Tools.ShippingGateTypedFinal

variable {tenv : Lean.Environment}

/-! # Gate-route parents: the typed walk under a typing chosen per instantiation (worker N, round 16)

WRITTEN, NOT BUILT.

`cone_harness_typed` / `gate_cone_runTyped` / `gate_typedFacts`
(`Tools/ShippingGateTypedFinal.lean`, round 14) fix the typing
`τ : Lean.Expr → Nat` of the cone's sub-expressions BEFORE the fresh ids the
body is instantiated with. That is enough when `τ` does not depend on WHICH
input a free variable is (the seven parents: every input 8 bits wide; parentCmp
types by the application's arity). For a parent whose inputs have DIFFERENT
widths (`wrapPick sel x`: 2 and 8 bits), no fixed `τ` can give
`τ (.fvar i0) = 2` and `τ (.fvar i1) = 8` for EVERY pair of distinct ids
(swap them) — the round-14 form cannot be instantiated (obstacle, recorded).

Here the three statements with the typing chosen AFTER the instantiation
(`∃ τ`, per cache and ids); `TFin G m` does not mention `τ`, so the
conclusions are unchanged. Copies of the round-14 proofs (`typedFinal_of_run`
reused); the old theorems are kept and are the case of a constant choice. -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

section harnessTI
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingChildInv (RefLaws InvV Res CacheInv ChildBnd bodyRel profLogIO RealChild)
open Tools.ShippingCacheCoherentRun (SubMap sub_refl)
open Tools.ShippingGateDefines (GateDefines)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **The harness with three walks, the typing chosen per instantiation**
(`cone_harness_typed` with `∃ τ` under the cache and ids; a copy of its proof). -/
theorem cone_harness_typedI (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      ∀ (G : Sparkle.IR.AST.Module → Prop),
        (∀ (cache' : IO.Ref (Lean.ExprStructMap String)) (ids' : List FVarId), ids'.Nodup →
          ids'.length = bs.length →
          DesW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (Sparkle.IR.ModuleName.ofDecl declName)
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) true ∧
          NamW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (prepInsN bs ids' cache' (Sparkle.IR.ModuleName.ofDecl declName))
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) ∧
          ∃ τ : Lean.Expr → Nat,
          TypW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (prepPortsT bs ids' cache' (Sparkle.IR.ModuleName.ofDecl declName)) τ
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body)) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl declName) m d ∧ NFin G m ∧ TFin G m := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, hty, hm,
    hdd⟩ :=
    mixedHarness_runs L hw hd hr
  obtain ⟨⟨hcT, -, -⟩, -, -⟩ := fuel_runsW (tenv := tenv) L hD translateFuelLimit hwT hdT htr
  refine ⟨wT', hcT, fun G hE hpos => ?_⟩
  obtain ⟨hE1, hE2, τ, hE3⟩ := hE cache ids nd len
  exact ⟨desFinal_of_run hE1 hpos hwT hdT (sub_refl _) htr hst hty hm hdd,
    namesFinal_of_run hE2 hwT hdT (sub_refl _) htr hst hm,
    typedFinal_of_run (τ := τ) hE2 hE3 hwT hdT (sub_refl _) htr hst hty hm⟩

/-- **The full entry with three walks, the typing chosen per instantiation**
(`gate_cone_runTyped` with `∃ τ`; a copy of its proof). -/
theorem gate_cone_runTypedI {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs body)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (Dd : Sparkle.IR.AST.Design) (envR : Lean.Environment)
      (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      ((∀ x ∈ Dd.modules, x.name ≠ M.name) → design.modules = Dd.modules) ∧
      (∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body)) ∧
      CacheInv mref cref mF ∧
      (∀ (G : Sparkle.IR.AST.Module → Prop),
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 →
          ∀ (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId), ids.Nodup →
          ids.length = bs.length →
          DesW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
              (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
            G (Sparkle.IR.ModuleName.ofDecl f)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) true ∧
          NamW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
              (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
            G (prepInsN bs ids cache (Sparkle.IR.ModuleName.ofDecl f))
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) ∧
          ∃ τ : Lean.Expr → Nat,
          TypW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
              (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
            G (prepPortsT bs ids cache (Sparkle.IR.ModuleName.ofDecl f)) τ
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body)) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl f) M Dd ∧ NFin G M ∧ TFin G M) := by
  obtain ⟨L, ⟨hsv, hdep⟩, hq⟩ := bnd
  obtain ⟨M, Dd, w1, hcore, hpost⟩ :=
    Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨M2, D2, w2, hcore2, -, hname, hmods⟩ := Tools.ShippingCacheCoherentRun.full_split L hr
  obtain ⟨hMD, -⟩ := runsTo_det hcore2 hcore
  obtain ⟨hM, hD⟩ := Prod.mk.inj hMD
  rw [hM] at hname
  rw [hM, hD] at hmods
  have hreads : ∃ (bb : Bool) (envR : Lean.Environment) (ci : Lean.ConstantInfo)
      (a1 a2 a3 a4 a5 a6 : Void IO.RealWorld),
      RunsTo (Lean.getConstInfo f) mctx mref cctx cref a1 ci a2 ∧
      RunsTo (Lean.getEnv : Lean.Meta.MetaM Lean.Environment) mctx mref cctx cref a5 envR a6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n)
        (profLogIO bb) f [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref a3 (M, Dd) a4 ∧ InvV L a3 ∧ L.dval a3 ≠ 0 := by
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
  obtain ⟨dv, hdv, hold, hshape⟩ := gdef a1 ci a2 a5 envR a6 hget henv
  rw [hdv] at run
  obtain ⟨wa, wb, hwa, hda, hharn⟩ := sfc_mixed_run L hold hshape hw3 run
  have hDa : L.dval wa ≠ 0 := by rw [hda]; exact hd3
  obtain ⟨wT', hcache, hdes⟩ :=
    cone_harness_typedI (tenv := envR) L (D := L.dval wa) hDa hwa rfl hharn
  exact ⟨M, Dd, envR, L.val wT', hpost, hmods, ⟨dv, hshape⟩, hcache,
    fun G hE hpos => hdes G (fun cache ids nd len => hE L (L.dval wa) hDa cache ids nd len)
      hpos⟩

end harnessTI

section factsTI
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingChildInv (RefLaws Res CacheInv ChildBnd RealChild)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingMixedEntrySoundness (prepare start)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **`hierTyped` and `designSideB3` derived** for a gate parent whose
instance leaves call one gate child `c` (file header). Premises: the run,
`GateDefines` (NOT ALLOWED), `ChildBnd`; the child facts of every `c` entry
of a `CacheInv` cache (incl. `GateChildPorts`); the body's three walks, the
typing `τ` chosen per instantiation (`gate_typedFacts` with `∃ τ`). -/
theorem gate_typedFactsI {f c : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {n : Nat} {bsc : List (Lean.Name × MixedGateBinder)} {nc : Nat}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs body)
    (bnd : ChildBnd mref cref w)
    (hkid : ∀ mF : Std.HashMap Lean.Name Res, CacheInv mref cref mF → ∀ y : Res,
      mF.get? c = some y →
      InstLeafOk (ChildGN c mF) n y ∧ Tools.ShippingGateChildComb.ChildComb y.1 ∧
        y.1.name ≠ Sparkle.IR.ModuleName.ofDecl f ∧
        Tools.ShippingGatePorts.GateChildPorts c bsc nc y.1)
    (hwalk : ∀ envR : Lean.Environment,
      (∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body)) →
      ∀ mF : Std.HashMap Lean.Name Res,
      (∀ y : Res, mF.get? c = some y →
        InstLeafOk2 (ChildGN c mF) n y ∧ Tools.ShippingGatePorts.GateChildPorts c bsc nc y.1) →
      ∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 →
      ∀ (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId), ids.Nodup →
      ids.length = bs.length →
      DesW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
        (ChildGN c mF) (Sparkle.IR.ModuleName.ofDecl f)
        (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) true ∧
      NamW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
        (ChildGN c mF) (prepInsN bs ids cache (Sparkle.IR.ModuleName.ofDecl f))
        (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) ∧
      ∃ τ : Lean.Expr → Nat,
      TypW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
        (ChildGN c mF) (prepPortsT bs ids cache (Sparkle.IR.ModuleName.ofDecl f)) τ
        (instFVars (ids.map Lean.Expr.fvar).toArray 0 body))
    (hpos : ∀ x ∈ bs, ∀ k, x.2 = MixedGateBinder.bits k → 0 < k) :
    Tools.ShippingHierTyped.hierTyped (childMap design.modules) b = true ∧
      designSideB3 design.modules b = true := by
  obtain ⟨M, Dd, envR, mF, hpost, hmods, hacc, hcache, hdes⟩ := gate_cone_runTypedI hr gdef bnd
  have hleaf2 : ∀ y : Res, mF.get? c = some y →
      InstLeafOk2 (ChildGN c mF) n y ∧ Tools.ShippingGatePorts.GateChildPorts c bsc nc y.1 :=
    fun y hy => ⟨⟨(hkid mF hcache y hy).1, leaf_extra_of_combN (hkid mF hcache y hy).2.1⟩,
      (hkid mF hcache y hy).2.2.2⟩
  obtain ⟨fin, -, hT⟩ := hdes (ChildGN c mF)
    (fun L' D hD cache ids nd len => hwalk envR hacc mF hleaf2 L' D hD cache ids nd len) hpos
  have hms : ∀ x, ChildGN c mF x →
      Sparkle.IR.Machine.moduleByName design.modules x.name = some x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [hxy]
    exact designHasChild_of_final fin (childGN_eq hy) (hkid mF hcache y hy).2.2.1 hmods
  have hGF : ∀ x, ChildGN c mF x → GFactsT design.modules x := by
    intro x hx
    have hm := hms x hx
    obtain ⟨y, hy, hxy⟩ := hx
    subst hxy
    exact gFacts_of_ports hm (hkid mF hcache y hy).2.2.2
  obtain ⟨hb, hw, hi⟩ := post_fieldsN fin.mod hpost
  have ho := Tools.ShippingGateOutPort.post_outputs hpost
  obtain ⟨h1, h2, h3, h4⟩ := hT b hb hw hi ho design.modules hGF
  have hg := Tools.ShippingGateCombSide.hierGate_of_modOk fin.mod hpost
  refine ⟨h1, ?_⟩
  simp only [designSideB3, Bool.and_eq_true]
  exact ⟨⟨h2, h3⟩, Tools.ShippingPortsMatchShipped.portsMatchB_shipped hg h4⟩

end factsTI

end Tools.ShippingGateParentRun

#print axioms Tools.ShippingGateParentRun.cone_harness_typedI
#print axioms Tools.ShippingGateParentRun.gate_cone_runTypedI
#print axioms Tools.ShippingGateParentRun.gate_typedFactsI
