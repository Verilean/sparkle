import Tools.ShippingGateConeCompare

variable {tenv : Lean.Environment}

/-! # Instance leaves whose ARGUMENTS have world-indexed contracts (worker N, round 9)

WRITTEN, NOT BUILT.

`inst_leaf_contractW` (round 3) gives the world-indexed contract `ContractW`
of a canonical instance call whose arguments have WORLD-FREE contracts
(`Contract`: every `Returns` run of the argument, in any world). An argument
that is itself an instance call (`childAdd (childAdd a b) b`, `parentNested`)
has no world-free contract — the child its run synthesises is the run's own —
only a `ContractW`. Here the instance leaf at world level with `ContractW`
arguments:

* `instanceArm_runWW` — the text of the built `instanceArm_runW`, with the
  continuation kept as a RUN of `armCont` from the world after the child's
  synthesis (invariant, depth `D`), instead of a world-free `Returns`;
  `inst_leaf_runsW` — the same on a canonical call at fuel `fuel + 1`;
* `runsC_get` — `get`, with its world (the world is unchanged);
* `instArgs_W` — the operand walk `instArgs` world by world: each operand's
  run starts in an invariant world at depth `D` and ends in a world whose
  cache is in the end cache (so in `mF`); the text of the built
  `instArgs_frame` / `instArgs_sem` over `ContractW.atRun`;
* `instUncached_shapeW` — the text of the built `instUncached_shape` with the
  worlds: the operand walk is a RUN from an invariant world, and its end
  cache is contained in the lowering's end cache (the suffix's invariant by
  `vc`);
* `armCont_leaf_runW` — the text of the built `armCont_leaf_contract` on ONE
  run, with `ContractW` operands (the wrapper by the built
  `controlCached_runsW`);
* **`inst_leaf_contractWA`** — the instance leaf's `ContractW` from the
  `ContractW`s of its arguments (no world-free argument contract).

The cache: a callee's entry in the run's child cache is ONE pair per callee
NAME (`mF : HashMap Name Res`). `inst_leaf_runs` makes the child of EVERY
call of `mn` in the run THE end cache's entry of `mn` (entries are kept), so
an inner and an outer call of the same callee instantiate the same pair `y`;
the child facts are asked of `y` at each call's own value (`KidFacts … v y`,
one per call). -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

/-! ## The instance arm, with the continuation's run -/

section arm
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInv
open Tools.ShippingWalkGrow
open Tools.ShippingCacheCoherentRun (SubMap sub_trans)
open Tools.ShippingInstanceEntrySoundness (instEN instEN_getAppFn instanceN_step)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **The instance arm, world by world, with the continuation's RUN** (the
text of the built `instanceArm_runW`; the continuation is a run of `armCont`
on the run's child from the world after the child's synthesis). -/
theorem instanceArm_runWW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (k : Nat)
    {e : Lean.Expr} {mn : Lean.Name} {us : List Level}
    (hfn : e.getAppFn = .const mn us)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    {hint : String} {top named : Bool} {ctx : CompilerState} {st : CircuitState}
    {w : Void IO.RealWorld} {wire : String} {s' : CircuitState} {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (translateInstanceOrFallback tenv (translateFuelFix (translateStep tenv) k)
      e hint top named ctx st) mctx mref cctx cref w (wire, s') w') :
    ∃ (y : Res) (wm : Void IO.RealWorld), RealChild mref cref mn y ∧
      (L.val w').get? mn = some y ∧ InvV L wm ∧ L.dval wm = D ∧
      RunsTo (armCont (translateFuelFix (translateStep tenv) k) mn y e hint top named ctx st)
        mctx mref cctx cref wm (wire, s') w' := by
  have hC : ∀ L' : RefLaws mref cref, ChildKeeps L' D :=
    fun L' => childKeeps L' D (fun h => absurd h hD)
  have hrec : ∀ (L' : RefLaws mref cref) (mctx : Meta.Context) (cctx : Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D)
        (translateFuelFix (translateStep tenv) k e hint top named) :=
    fun L' => fuelRec_keepsC L' D (hC L') k
  have hlegC : ∀ (L' : RefLaws mref cref) (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D)
        (Rec.translateExprToWireCached
          (fun e h t n => translateFuelFix (translateStep tenv) k e h t n) e hint top named) :=
    fun L' e hint top named =>
      (legacyRel L' D (hC L') (translateFuelFix (translateStep tenv) k) (hrec L')
        mctx cctx).1 e hint top named
  unfold translateInstanceOrFallback at hr
  rw [hfn] at hr
  try dsimp only at hr
  rw [htag] at hr
  simp only [if_true] at hr
  obtain ⟨⟨sub, s1⟩, w1, r1, r2⟩ := RunsTo.bind hr
  obtain ⟨hs1, rc⟩ := lift_runs r1
  obtain ⟨hreal, hw1, hdep1, hsub1, hget1, -⟩ :=
    childSynthEntry_post L (fun L' => bodyRel L') hw (by rw [hd]; exact hD) rc
  have r2' : RunsTo (armCont (translateFuelFix (translateStep tenv) k) mn sub e hint top named
      ctx s1) mctx mref cctx cref w1 (wire, s') w' := r2
  rw [hs1] at r2'
  have hk : WG mctx cctx L D ctx (fun m => m.get? mn = some sub)
      (armCont (translateFuelFix (translateStep tenv) k) mn sub e hint top named)
      (fun _ _ => True) :=
    WG.ofKeeps (fun L' st0 =>
      armCont_keepsC L' D (translateFuelFix (translateStep tenv) k) (hrec L') (hC L') (hlegC L')
        mn sub e hint top named ctx st0)
  obtain ⟨-, -, hs2, -⟩ := hk st w1 (wire, s') w' hw1 (hdep1.trans hd) hget1 r2'
  exact ⟨sub, w1, hreal, hs2 mn sub hget1, hw1, hdep1.trans hd, r2'⟩

/-- **`inst_leaf_runs`, with the continuation's run.** -/
theorem inst_leaf_runsW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom argsE) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    {hint : String} {top named : Bool} {ctx : CompilerState} {s : CircuitState}
    {w : Void IO.RealWorld} {wire : String} {s' : CircuitState} {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (translateFuelFix (translateStep tenv) (fuel + 1) (instEN mn lvls dom argsE)
      hint top named ctx s) mctx mref cctx cref w (wire, s') w') :
    ∃ (y : Res) (wm : Void IO.RealWorld), RealChild mref cref mn y ∧
      (L.val w').get? mn = some y ∧ InvV L wm ∧ L.dval wm = D ∧
      RunsTo (armCont (translateFuelFix (translateStep tenv) fuel) mn y
        (instEN mn lvls dom argsE) hint top named ctx s) mctx mref cctx cref wm (wire, s') w' := by
  have hstep : translateFuelFix (translateStep tenv) (fuel + 1) (instEN mn lvls dom argsE)
      hint top named =
      translateInstanceOrFallback tenv (translateFuelFix (translateStep tenv) fuel)
        (instEN mn lvls dom argsE) hint top named := by
    show translateStepWith (translateFallback tenv) (translateFuelFix (translateStep tenv) fuel)
      (instEN mn lvls dom argsE) hint top named = _
    exact instanceN_step _ mn lvls _ _ _ _ _ hpure hbin hkind
  rw [hstep] at hr
  exact instanceArm_runWW L hD fuel (instEN_getAppFn mn lvls dom argsE) htag hw hd hr

end arm

/-! ## The operand walk and the uncached lowering, world by world -/

section walk
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedLiteralSoundness (DeclGrows)
open Tools.ShippingBoolSourceSoundness (translateControlCachedWith_returns)
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingInstanceEntrySoundness
open Tools.ShippingInstanceLeaf
open Tools.ShippingChildInv (armCont RefLaws InvV J KeepsC Res childKeeps
  recordTranslation_keepsC instArgs_keepsC instClkRst_keepsC)
open Tools.ShippingCacheCoherentRun (SubMap sub_trans sub_refl)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- `get`, with its world: the value and the state are the start state, the
world is unchanged (the text of the built `Returns.get`). -/
theorem runsC_get {ctx : CompilerState} {s s' a : CircuitState} {w w' : Void IO.RealWorld}
    (h : RunsC (MonadState.get : CompilerM CircuitState) ctx s mctx mref cctx cref w (a, s') w') :
    a = s ∧ s' = s ∧ w' = w := by
  change EST.Out.ok (s, s) w = _ at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- **The uncached instance lowering, with its worlds** (the text of the
built `instUncached_shape`): the operand walk is a RUN from an invariant
world at depth `D`, whose end cache is contained in the lowering's end cache;
the lowering ends in an invariant world at depth `D`. `hrec`: the recursive
translator keeps the invariant (for the real translator: `fuelRec_keepsC`). -/
theorem instUncached_shapeW (L : RefLaws mref cref) {D : Nat} {rec : TranslateFn}
    (hrec : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D) (rec e hint top named))
    {ctx : CompilerState} {mn : Name}
    {mc : Sparkle.IR.AST.Module} {dc : Design} {so : Port}
    {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {hint : String} {top named : Bool} {s t : CircuitState} {w : String}
    {w0 w1 : Void IO.RealWorld}
    (hdc : dc.modules = [])
    (hnoclk : ∀ p ∈ mc.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hlen : mc.inputs.length = argsE.length)
    (hw0 : InvV L w0) (hd0 : L.dval w0 = D)
    (run : RunsC (translateInstanceUncachedWith rec mn mc dc so
      (instEN mn lvls dom argsE) hint top named) ctx s mctx mref cctx cref w0 (w, t) w1) :
    ∃ (d' : Design) (conns : List (String × Sparkle.IR.AST.Expr)) (sA : CircuitState)
      (wa wb : Void IO.RealWorld),
      InvV L wa ∧ L.dval wa = D ∧ InvV L w1 ∧ L.dval w1 = D ∧ SubMap (L.val wb) (L.val w1) ∧
      RunsC (instArgs rec [] (mc.inputs.zip argsE) 0) ctx { s with design := d' }
        mctx mref cctx cref wa (conns, sA) wb ∧
      ((instHitValid s.translateRecord (instEN mn lvls dom argsE) w = true ∧ t = sA) ∨
       (∃ iname : String, w = (CircuitM.makeWire hint so.ty named sA).1 ∧
         t = { (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2 with
           module := (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module.addStmt
             (.inst mc.name iname (conns.reverse ++ [(so.name, .ref w)])) } ∧
         instLinked (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module mc
           (conns.reverse ++ [(so.name, .ref w)]) = true)) := by
  rw [instanceUncached_run] at run
  -- the prefix: `get`, the (empty) design modules, the child's registration,
  -- the clk/rst plumbing (none), the arity guard
  obtain ⟨cs0, sG, wg, hget0, k1⟩ := RunsC.bind (c := (get : CompilerM CircuitState)) run
  obtain ⟨hcs0, hsG, hwg⟩ := runsC_get hget0
  rw [hcs0, hsG, hwg] at k1
  rw [hdc] at k1
  obtain ⟨u0, sA0, wA0, hAdd0, k2⟩ := RunsC.bind (c := instAddModules _ []) k1
  have hAdd0' : RunsC (Pure.pure () : CompilerM Unit) ctx s mctx mref cctx cref w0 (u0, sA0)
      wA0 := hAdd0
  obtain ⟨hp0, hwA0⟩ := RunsC.pure hAdd0'
  rw [(Prod.mk.inj hp0).2, hwA0] at k2
  obtain ⟨uR, sB, wR, hReg, k3⟩ := RunsC.bind (c := instRegisterChild _ mc) k2
  obtain ⟨hwR, hdR, -⟩ := keepsW L (fun L' => by vc) hw0 hd0 hReg
  have hsB : ∃ d', sB = { s with design := d' } := by
    have hRegR := runsCReturns hReg
    unfold instRegisterChild at hRegR
    obtain ⟨cs, s1, hget, k⟩ := Returns.bind (m := (get : CompilerM CircuitState)) hRegR
    obtain ⟨hcs, hs1⟩ := Returns.get hget
    rw [hcs, hs1] at k
    split at k
    · exact ⟨_, addModuleToDesignC_returns k⟩
    · obtain ⟨-, hs⟩ := Returns.pure k
      exact ⟨s.design, hs⟩
  obtain ⟨d', hsB⟩ := hsB
  obtain ⟨conns0, sC, wC, hClk, k4⟩ := RunsC.bind (c := instClkRst [] mc.inputs) k3
  obtain ⟨hwC, hdC, -⟩ :=
    keepsW L (fun L' => instClkRst_keepsC L' D mc.inputs []) hwR hdR hClk
  obtain ⟨hconns0, hsC⟩ := instClkRst_skip hnoclk (runsCReturns hClk)
  -- `filter_noclk` is stated under `[HierCtx] [ChildSem]` it does not use; its text here
  have hfl : mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst") = mc.inputs := by
    rw [List.filter_eq_self]
    intro p hp
    obtain ⟨h1, h2⟩ := hnoclk p hp
    simp [bne, h1, h2]
  rw [hfl, instEN_spineArgs] at k4
  obtain ⟨uG, sH, wH, hGuard, k5⟩ := RunsC.bind (c := instArityCheck mn _ _) k4
  unfold instArityCheck at hGuard
  rw [if_neg (by simp [hlen])] at hGuard
  obtain ⟨hpG, hwH⟩ := RunsC.pure hGuard
  have hsH : sH = sC := (Prod.mk.inj hpG).2
  have hdrop : (dom :: argsE).drop ((dom :: argsE).length - mc.inputs.length) = argsE := by
    simp [hlen]
  rw [hdrop, hconns0] at k5
  -- the operand walk, from an invariant world
  obtain ⟨conns, sF, wb, hArgs, k6⟩ := RunsC.bind (c := instArgs _ _ _ 0) k5
  rw [hsH, hsC, hsB, hwH] at hArgs
  obtain ⟨hwb, hdb, -⟩ :=
    keepsW L (fun L' => instArgs_keepsC L' D rec (hrec L') _ _ _) hwC hdC hArgs
  -- the suffix keeps the invariant: the walk's end cache is in the end cache
  obtain ⟨hw1, hd1, hsub6⟩ := keepsW L (fun L' => by vc) hwb hdb k6
  refine ⟨d', conns, sF, wC, wb, hwC, hdC, hw1, hd1, hsub6, hArgs, ?_⟩
  -- the suffix's shape: the text of the built `instUncached_shape`
  have k6R := runsCReturns k6
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6R
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  have hsQ := Returns.liftMetaM hCacheRead
  cases hhit : (cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
      (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}").filter
      (instHitValid s.translateRecord (instEN mn lvls dom argsE)) with
  | some cw =>
    rw [hhit] at k8
    obtain ⟨hw, ht⟩ := Returns.pure k8
    left
    refine ⟨?_, by rw [ht, hsQ, hsP2]⟩
    rw [hw]
    cases hget : cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
        (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}" with
    | none => rw [hget] at hhit; cases hhit
    | some c0 =>
      rw [hget] at hhit
      by_cases hv : instHitValid s.translateRecord (instEN mn lvls dom argsE) c0 = true
      · have : (some c0 : Option String) = some cw := by
          simpa [Option.filter, hv] using hhit
        cases this
        exact hv
      · simp [Option.filter, hv] at hhit
  | none =>
    rw [hhit] at k8
    simp only [] at k8
    obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire hint _ named) k8
    obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
    obtain ⟨uP, sV, hPut, k10⟩ :=
      Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
    have hsV := Returns.liftMetaM hPut
    obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
    obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
    obtain ⟨uL, sL, hLink, k11⟩ := Returns.bind (m := instLinkCheck _ _ _) k11
    obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
    rw [hsL] at k11
    obtain ⟨uE, sI, hEmit, k12⟩ :=
      Returns.bind (m := CompilerM.emitInstance mc.name _ _) k11
    have hsI := emitInstanceC_returns hEmit
    obtain ⟨hwEq, ht⟩ := Returns.pure k12
    right
    refine ⟨instName, ?_, ?_, ?_⟩
    · rw [hwEq, houtW, hsQ, hsP2]
    · rw [ht, hsI, hsN, hsV, hsW, hsQ, hsP2, hwEq]
      simp
    · rw [hsN, hsV, hsW, hsQ, hsP2, List.reverse_cons] at hlinked
      rw [hwEq]
      exact hlinked

section inst
variable [HierCtx] [ChildSem]

/-- **The operand walk, world by world**: every operand's run starts in an
invariant world at depth `D` and ends in a world whose cache is in the walk's
end cache; with the end cache in `mF`, each operand's `ContractW` applies
(`atRun`). The text of the built `instArgs_frame` / `instArgs_sem`. -/
theorem instArgs_W (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env} :
    ∀ (pairs : List (Port × Lean.Expr)) (vs : List Value)
      (acc : List (String × Sparkle.IR.AST.Expr)) (i : Nat)
      (r : List (String × Sparkle.IR.AST.Expr)) (s t : CircuitState)
      (w0 w1 : Void IO.RealWorld),
    pairs.length = vs.length →
    (∀ k (hk : k < pairs.length) (hk' : k < vs.length),
      ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
        (pairs[k]'hk).2 (vs[k]'hk')) →
    InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
    RunsC (instArgs (translateFuelFix (translateStep tenv) fuel) acc pairs i) ctx s
      mctx mref cctx cref w0 (r, t) w1 →
    SubMap (L.val w0) (L.val w1) ∧
    (Lookup ctx inputs s → Frame s t) ∧
    (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
      ∃ (ws : List String) (result : Env), ws.length = pairs.length ∧
        r = ((pairs.zip ws).map
          (fun pw => (pw.1.1.name, Sparkle.IR.AST.Expr.ref pw.2))).reverse ++ acc ∧
        Inv ctx inputs we mems initial t result ∧
        (∀ z, s.usedNames.contains z = true → result z = prior z) ∧
        (∀ z, s.usedNames.contains z = true → t.usedNames.contains z = true) ∧
        ∀ k (hk : k < ws.length) (hk' : k < vs.length),
          result (ws[k]'hk) = (vs[k]'hk').toNat ∧ t.usedNames.contains (ws[k]'hk) = true)
  | [], _, acc, i, r, s, t, w0, w1, _, _, _, _, _, hr => by
    unfold instArgs at hr
    obtain ⟨hp, hw⟩ := RunsC.pure hr
    obtain ⟨hr', hs⟩ := Prod.mk.inj hp
    refine ⟨by rw [hw]; exact sub_refl _, fun _ => by rw [hs]; exact Frame.refl _, ?_⟩
    intro prior h _
    rw [hs]
    exact ⟨[], prior, rfl, by rw [hr']; rfl, h, fun _ _ => rfl, fun _ hz => hz,
      fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | (p, e) :: rest, [], acc, i, r, s, t, w0, w1, hlen, _, _, _, _, _ => by
    simp at hlen
  | (p, e) :: rest, v :: vs, acc, i, r, s, t, w0, w1, hlen, hc, hw, hd, hsub, hr => by
    unfold instArgs at hr
    obtain ⟨aw, s1, wa, hread, hrest⟩ := RunsC.bind hr
    obtain ⟨hwa, hda, hsa⟩ := fuel_runsW (tenv := tenv) L hD fuel hw hd hread
    have hcRest : ∀ k (hk : k < rest.length) (hk' : k < vs.length),
        ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
          (rest[k]'hk).2 (vs[k]'hk') := by
      intro k hk hk'
      have := hc (k + 1) (by simpa using hk) (by simpa using hk')
      simpa using this
    obtain ⟨subT, frT, semT⟩ := instArgs_W L hD fuel rest vs _ (i + 1) r s1 t wa w1
      (by simpa using hlen) hcRest hwa hda hsub hrest
    have c0 := (hc 0 (by simp) (by simp)).atRun hw hd (sub_trans subT hsub) hread
    refine ⟨sub_trans hsa subT, fun lookup => ?_, fun prior h widths => ?_⟩
    · have f1 := c0.frame lookup
      exact f1.trans (frT (lookup.transfer f1))
    · have lookup := Lookup.ofInputs h.inputs
      have f1 := c0.frame lookup
      have f2 := frT (lookup.transfer f1)
      have w1' : ScalarWidthsAgree we s1 := f2.decls.widths widths
      have step := c0.sem prior h w1'
      obtain ⟨res1, inv1, val1, fr1⟩ := step.execution
      obtain ⟨ws, result, hlenW, hrEq, invT, frT', grT, vals⟩ := semT res1 inv1 widths
      refine ⟨aw :: ws, result, by simp [hlenW], ?_, invT, ?_, ?_, ?_⟩
      · rw [hrEq]
        simp
      · intro z hz
        rw [frT' z (step.grows z hz)]
        exact fr1 z hz
      · intro z hz
        exact grT z (step.grows z hz)
      · intro k hk hk'
        cases k with
        | zero =>
          refine ⟨?_, grT aw step.used⟩
          show result aw = v.toNat
          rw [frT' aw step.used]
          exact val1
        | succ k => exact vals k (by simpa using hk) (by simpa using hk')

set_option maxHeartbeats 1000000 in
/-- **The arm's continuation on ONE run, with `ContractW` operands** (the text
of the built `armCont_leaf_contract`, the wrapper decomposed by the built
`controlCached_runsW`, the lowering by `instUncached_shapeW`, the operand walk
by `instArgs_W`). -/
theorem armCont_leaf_runW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {mn : Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {vs : List Value} {v : Value} {y : Sparkle.IR.AST.Module × Design} {cwe : WEnv}
    {outName : String} {wOut : Nat}
    (hdc : y.2.modules = [])
    (hnoclk : ∀ p ∈ y.1.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hnodup : (y.1.inputs.map (·.name)).Nodup)
    (houts : y.1.outputs = [⟨outName, .bitVector wOut⟩])
    (houtFresh : ∀ p ∈ y.1.inputs, (outName == p.name) = false)
    (hlen : y.1.inputs.length = argsE.length) (hlenV : argsE.length = vs.length)
    (hargs : ∀ k (hk : k < argsE.length) (hk' : k < vs.length),
      ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
        (argsE[k]'hk) (vs[k]'hk'))
    (meaning : Meaning inputs (instEN mn lvls dom argsE) v)
    (hsem : ChildSem.childSem mn vs = some v)
    (hwidth : v.kind.width = wOut)
    (hchild : HierCtx.children y.1.name = some (y.1, cwe))
    (hcorrect : ChildCorrect mn y.1 cwe outName)
    {hint : String} {top named : Bool} {s t : CircuitState} {w : String}
    {w0 w1 : Void IO.RealWorld}
    (hwI : InvV L w0) (hdI : L.dval w0 = D) (hsubF : SubMap (L.val w1) mF)
    (hrun : RunsC (armCont (translateFuelFix (translateStep tenv) fuel) mn y
      (instEN mn lvls dom argsE) hint top named) ctx s mctx mref cctx cref w0 (w, t) w1) :
    ChildAt ctx inputs we mems initial s t w v := by
  have hrecK : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D)
        (translateFuelFix (translateStep tenv) fuel e hint top named) :=
    fun L' => fuelRec_keepsC (tenv := tenv) L' D (childKeeps L' D (fun h => absurd h hD)) fuel
  -- the continuation at a one-output child is the validated wrapper
  have hr' : RunsC (translateControlCachedWith
      (translateInstanceUncachedWith (translateFuelFix (translateStep tenv) fuel) mn y.1 y.2
        ⟨outName, .bitVector wOut⟩) (instEN mn lvls dom argsE) hint top named) ctx s
      mctx mref cctx cref w0 (w, t) w1 := by
    unfold armCont at hrun
    rw [houts] at hrun
    exact hrun
  have pairsLen : (y.1.inputs.zip argsE).length = vs.length := by
    simp [hlen, hlenV]
  have pairContracts : ∀ k (hk : k < (y.1.inputs.zip argsE).length) (hk' : k < vs.length),
      ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
        ((y.1.inputs.zip argsE)[k]'hk).2 (vs[k]'hk') := by
    intro k hk hk'
    have hkA : k < argsE.length := by rw [hlenV]; exact hk'
    have : ((y.1.inputs.zip argsE)[k]'hk).2 = argsE[k]'hkA := by simp
    rw [this]
    exact hargs k hkA hk'
  rcases controlCached_runsW L hwI hdI hr' with hit | ⟨sm, wa, wb, hwa, hda, lowerRun, recordRun⟩
  · -- a validated hit of the expression cache
    refine ⟨fun _ => ?_, fun prior h _ => hit_outcome h meaning hit⟩
    have ht := (cacheLookupValidated_returns hit).1
    rw [ht]
    exact Frame.refl s
  · -- a miss: the uncached lowering, then the record
    obtain ⟨d', conns, sA, wc, wd, hwc, hdc', hwb, hdb, subD, hArgs, hcase⟩ :=
      instUncached_shapeW L hrecK hdc hnoclk hlen hwa hda lowerRun
    obtain ⟨-, -, subR⟩ := keepsW L (fun L' => recordTranslation_keepsC L' D
      (instEN mn lvls dom argsE) w (!named && !(instEN mn lvls dom argsE).isFVar && !top))
      hwb hdb recordRun
    obtain ⟨-, argsFrame, argsSem⟩ := instArgs_W L hD fuel (y.1.inputs.zip argsE) vs [] 0 conns
      { s with design := d' } sA wc wd pairsLen pairContracts hwc hdc'
      (sub_trans subD (sub_trans subR hsubF)) hArgs
    have recordR := runsCReturns recordRun
    refine ⟨fun lookup => ?_, fun prior h widths => ?_⟩
    · -- the structural frame (the built `lowerFrame`, then the record)
      have fD : Frame s { s with design := d' } := frame_design s d'
      have fA := argsFrame (lookup.transfer fD)
      have fl : Frame s sm ∧ (s.usedNames.contains w = false ∨
          s.translateRecord.get? w = some (instEN mn lvls dom argsE)) := by
        rcases hcase with ⟨hvalid, ht⟩ | ⟨iname, hw, ht, -⟩
        · rw [ht]
          exact ⟨fD.trans fA, Or.inr (instHitValid_record hvalid)⟩
        · have fW := Tools.ShippingMixedBinarySoundness.Frame.makeWire sA hint wOut named
          have fN := frame_freshName (CircuitM.makeWire hint (.bitVector wOut) named sA).2
            s!"inst_{y.1.name}" false
          have fI := frame_emitInst (CircuitM.freshName s!"inst_{y.1.name}" false
              (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2
            (.inst y.1.name iname (conns.reverse ++ [(outName, .ref w)]))
          refine ⟨?_, Or.inl ?_⟩
          · rw [ht]
            exact (((fD.trans fA).trans fW).trans fN).trans fI
          · have freshA := (CircuitM.makeWire_spec hint (.bitVector wOut) named sA).1
            rw [← hw] at freshA
            cases hu : s.usedNames.contains w with
            | false => rfl
            | true =>
              have := (fD.trans fA).used w hu
              rw [freshA] at this
              cases this
      exact frame_record_valid fl.1 fl.2 recordR
    · -- the semantic outcome (the built body, at the run's own operand walk)
      have hs := recordTranslation_returns recordR
      have wm : ScalarWidthsAgree we sm := by
        intro p hp; apply widths p; rw [hs]; exact hp
      have step : Outcome ctx inputs we mems initial prior s sm w v := by
        -- only the design changed before the operand walk
        have invD : Inv ctx inputs we mems initial { s with design := d' } prior :=
          h.transfer (LinkCtx.runs_body (s := s) rfl h.runs)
            (LinkCtx.typed_body (s := s) rfl (fun _ hq => hq) (fun _ hq => hq) h.typed) rfl rfl
            (fun _ hu => hu) (fun _ _ => rfl)
        rcases hcase with ⟨hvalid, ht⟩ | ⟨iname, hw, ht, hlk⟩
        · -- a validated single-out cache hit: the wire is recorded for this expression
          have wA : ScalarWidthsAgree we sA := by rw [← ht]; exact wm
          obtain ⟨ws, resA, hlenW, hconns, invA, frA, grA, vals⟩ := argsSem prior invD wA
          obtain ⟨used, value, width⟩ :=
            h.records w _ (instHitValid_record hvalid) v meaning
          rw [ht]
          exact ⟨grA w used, width, grA, resA, invA, (frA w used).trans value, frA⟩
        · -- a fresh wire and one instance statement
          have hdeclT : ({ name := w, ty := .bitVector wOut } : Port) ∈ sm.module.wires := by
            rw [ht]
            show _ ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
              (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.module.wires
            rw [(CircuitM.freshName_spec _ _ _).2.2,
              (CircuitM.makeWire_spec hint (.bitVector wOut) named sA).2.2.2, hw]
            exact List.mem_cons_self
          have wA : ScalarWidthsAgree we sA := by
            intro p hp
            apply wm p
            rw [ht]
            show p ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
              (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.module.wires
            rw [(CircuitM.freshName_spec _ _ _).2.2,
              (CircuitM.makeWire_spec hint (.bitVector wOut) named sA).2.2.2]
            exact List.mem_cons_of_mem _ hp
          obtain ⟨ws, resA, hlenW, hconns, invA, frA, grA, vals⟩ := argsSem prior invD wA
          have specW := CircuitM.makeWire_spec hint (.bitVector wOut) named sA
          have freshA : sA.usedNames.contains w = false := by rw [hw]; exact specW.1
          -- the state just before the instance statement
          have invW : Inv ctx inputs we mems initial
              (CircuitM.makeWire hint (.bitVector wOut) named sA).2 resA :=
            invA.allocate hint (.bitVector wOut) named
          have specN := CircuitM.freshName_spec s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (.bitVector wOut) named sA).2
          have invN : Inv ctx inputs we mems initial
              (CircuitM.freshName s!"inst_{y.1.name}" false
                (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2 resA :=
            invW.transfer (LinkCtx.runs_body (by rw [specN.2.2]) invW.runs)
              (LinkCtx.typed_body (by rw [specN.2.2])
                (fun q hq => by rw [specN.2.2]; exact hq)
                (fun q hq => by rw [specN.2.2]; exact hq) invW.typed)
              (CircuitM.freshName_sourceBindings _ _ _) (CircuitM.freshName_translateRecord _ _ _)
              (fun z hz => by rw [specN.2.1]; simp [Std.HashSet.contains_insert, hz])
              (fun _ _ => rfl)
          -- the connection list and the child's evaluation
          have hconnsRev : conns.reverse = (y.1.inputs.zip ws).map
              (fun pw => (pw.1.name, Sparkle.IR.AST.Expr.ref pw.2)) := by
            rw [hconns, List.append_nil, List.reverse_reverse]
            exact zip3_map (fun (p : Port) (w : String) => (p.name, Sparkle.IR.AST.Expr.ref w))
              y.1.inputs argsE ws hlen
          have hwsLen : ws.length = y.1.inputs.length := by
            rw [hlenW]
            simp [hlen]
          have hports : ∀ k (hk : k < y.1.inputs.length) (hk' : k < vs.length),
              connEnv (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref w)]) resA
                (y.1.inputs[k]'hk).name = (vs[k]'hk').toNat := by
            intro k hk hk'
            have hkW : k < ws.length := by rw [hwsLen]; exact hk
            have hl : (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref w)]).lookup
                (y.1.inputs[k]'hk).name = some (.ref (ws[k]'hkW)) := by
              apply lookup_append_left
              rw [hconnsRev]
              exact lookup_zip_ports y.1.inputs ws k hk hkW hnodup
            rw [connEnv_at hl]
            exact (vals k hkW hk').1
          obtain ⟨cres, hrunC, houtV⟩ := hcorrect mems
            (connEnv (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref w)]) resA) vs v hsem
            hports
          have hlookOut : (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref w)]).lookup
              outName = some (.ref w) := by
            have hne : ∀ p ∈ conns.reverse, (outName == p.1) = false := by
              intro p hp
              rw [hconnsRev] at hp
              obtain ⟨pw, hpw, rfl⟩ := List.mem_map.mp hp
              exact houtFresh pw.1 (List.of_mem_zip hpw).1
            rw [lookup_append_right hne]
            simp [List.lookup]
          have hbind : bindOuts y.1.outputs
              (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref w)]) cres resA =
              write resA w v.toNat := by
            rw [houts]
            show (match (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref w)]).lookup
                outName with
              | some (.ref w) => fun n => if n = w then cres outName else resA n
              | _ => resA) = _
            rw [hlookOut, houtV]
            rfl
          have runsI := runs_inst (iname := iname)
            (conns := conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref w)])
            invN.runs hchild hrunC
          rw [hbind] at runsI
          have inputSafe : ∀ id u, inputs id = some u →
              visible ctx (CircuitM.freshName s!"inst_{y.1.name}" false
                (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.sourceBindings id ≠
                some w := by
            intro id u hi bound
            rw [CircuitM.freshName_sourceBindings, CircuitM.makeWire_sourceBindings] at bound
            obtain ⟨z, hz, hu, _, _⟩ := invA.inputs.lookup id u hi
            have eq : z = w := Option.some.inj (hz.symm.trans bound)
            rw [eq, freshA] at hu
            cases hu
          have recordSafe : ∀ e u, (CircuitM.freshName s!"inst_{y.1.name}" false
                (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.translateRecord.get? w =
                some e → ¬ Meaning inputs e u := by
            intro e u record
            rw [CircuitM.freshName_translateRecord, CircuitM.makeWire_translateRecord] at record
            exact fun meaning => fresh_not_recorded invA.records freshA meaning record
          have invT : Inv ctx inputs we mems initial sm (write resA w v.toNat) := by
            rw [ht]
            exact inv_write_reserved invN inputSafe recordSafe rfl rfl (fun _ hz => hz) runsI
              (HierCtx.typed_inst hchild (instLinked_sound hlk) invN.typed)
          have usedN : ∀ z, sA.usedNames.contains z = true → sm.usedNames.contains z = true := by
            intro z hz
            rw [ht]
            show (CircuitM.freshName s!"inst_{y.1.name}" false
              (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.usedNames.contains z = true
            rw [specN.2.1, specW.2.1]
            simp [Std.HashSet.contains_insert, hz]
          refine ⟨?_, ?_, fun z hz => usedN z (grA z hz), write resA w v.toNat, invT,
            by simp [write], ?_⟩
          · rw [ht]
            show (CircuitM.freshName s!"inst_{y.1.name}" false
              (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.usedNames.contains w = true
            rw [specN.2.1, specW.2.1, ← hw]
            simp [Std.HashSet.contains_insert]
          · rw [wm _ hdeclT, ← hwidth]
            rfl
          · intro z hz
            have hzA := grA z hz
            have ne : z ≠ w := by
              intro eq
              rw [eq, freshA] at hzA
              cases hzA
            simp only [write, ne, if_false]
            exact frA z hz
      obtain ⟨result, inv, val, frame⟩ := step.execution
      refine ⟨?_, step.width, ?_, result,
        inv.record meaning step.used val step.width recordR, val, frame⟩
      · rw [hs]; exact step.used
      · rw [hs]; exact step.grows

/-- **`inst_leaf_contractWA`**: the world-indexed contract of a canonical call
of a callee designated in the translator's environment, from the
WORLD-INDEXED contracts of its arguments (an argument may itself be an
instance call). The run's child is `mF`'s entry of the callee
(`inst_leaf_runsW`); the child facts are asked of that entry only. -/
theorem inst_leaf_contractWA (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env}
    {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {vs : List Value} {v : Value}
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom argsE) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    (hlenV : argsE.length = vs.length)
    (hargs : ∀ k (hk : k < argsE.length) (hk' : k < vs.length),
      ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
        (argsE[k]'hk) (vs[k]'hk'))
    (meaning : Meaning inputs (instEN mn lvls dom argsE) v)
    (hsem : ChildSem.childSem mn vs = some v)
    (hkid : ∀ y : Res, mF.get? mn = some y →
      Tools.ShippingGateParentRun.KidFacts HierCtx.children (inferInstance : ChildSem) mn
        argsE.length v y) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
      (instEN mn lvls dom argsE) v := by
  have run : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String)
      (top named : Bool) (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
      InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
      RunsC (translateFuelFix (translateStep tenv) (fuel + 1) (instEN mn lvls dom argsE)
        hint top named) ctx s mctx mref cctx cref w0 (w, t) w1 →
      ChildAt ctx inputs we mems initial s t w v := by
    intro mctx cctx hint top named s t w w0 w1 hw hd hsub hr
    obtain ⟨y, wm, -, hget, hwm, hdm, hrA⟩ :=
      inst_leaf_runsW (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
    obtain ⟨cwe, outName, wOut, hdc, hnoclk, hnodup, houts, houtFresh, hlen, hwidth, hchild,
      hcorrect⟩ := hkid y (hsub mn y hget)
    exact armCont_leaf_runW L hD fuel hdc hnoclk hnodup houts houtFresh hlen hlenV hargs meaning
      hsem hwidth hchild hcorrect hwm hdm hsub hrA
  exact ⟨fun mctx cctx hint top named s t w w0 w1 lookup hw hd hsub hr =>
      (run mctx cctx hint top named s t w w0 w1 hw hd hsub hr).frame lookup,
    fun mctx cctx hint top named s t w prior w0 w1 h widths hw hd hsub hr =>
      (run mctx cctx hint top named s t w w0 w1 hw hd hsub hr).sem prior h widths⟩

end inst

end walk

end Tools.ShippingGateParentRun
