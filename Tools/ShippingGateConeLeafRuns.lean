import Tools.ShippingGateParentRuns

variable {tenv : Lean.Environment}

/-! # The cone's instance leaf, world by world (worker N, round 2)

WRITTEN, NOT BUILT.

The first half of a world-aware instance-leaf contract: a returning run of
the real translator (fuel `fuel + 1`) on a canonical call of a callee
designated in the translator's environment, from an invariant world of
positive depth `D`:

* the child pair `y` the arm synthesised is a `RealChild` of the callee;
* `y` is THE entry of the callee in the END cache of the run (so every later
  call of the same callee in the same run is a hit of `y`: `WG.keepEntry`,
  `WG.child_hit`);
* the invariant and the depth hold at the end, and every entry of the start
  cache is kept;
* the rest of the run is a run of `armCont` on `y` from the run's own
  circuit state to its end state (the door to `armCont_leaf_contract`).

`fuelRec_keepsC`: the recursive translator at any fuel keeps the child
invariant (the fuel induction of the built `translateRel_of_fallback`, at a
fuel other than the entry's). -/
namespace Tools.ShippingGateParentRun
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

/-- The recursive translator at any fuel keeps the invariant. -/
theorem fuelRec_keepsC (L : RefLaws mref cref) (D : Nat) (hC : ChildKeeps L D) (k : Nat) :
    ∀ (mctx : Meta.Context) (cctx : Core.Context) (e : Lean.Expr) (hint : String)
      (top named : Bool),
      KeepsC mctx mref cctx cref (J L D)
        (translateFuelFix (translateStep tenv) k e hint top named) :=
  fuelFix_keepsC (translateStep tenv) (fun rec hrec mctx cctx e hint top named => by
    unfold translateStep
    exact translateStepWith_keepsC L D (translateFallback tenv) rec hrec
      (fallbackRel_of_legacy L (legacyRel L) D hC rec hrec mctx cctx) e hint top named) k

/-- **The instance arm, world by world, with its states and the end cache.** -/
theorem instanceArm_runW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (k : Nat)
    {e : Lean.Expr} {mn : Lean.Name} {us : List Level}
    (hfn : e.getAppFn = .const mn us)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    {hint : String} {top named : Bool} {ctx : CompilerState} {st : CircuitState}
    {w : Void IO.RealWorld} {wire : String} {s' : CircuitState} {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (translateInstanceOrFallback tenv (translateFuelFix (translateStep tenv) k)
      e hint top named ctx st) mctx mref cctx cref w (wire, s') w') :
    ∃ y : Res, RealChild mref cref mn y ∧ (L.val w').get? mn = some y ∧
      InvV L w' ∧ L.dval w' = D ∧ SubMap (L.val w) (L.val w') ∧
      Returns (armCont (translateFuelFix (translateStep tenv) k) mn y e hint top named)
        ctx st wire s' := by
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
  obtain ⟨hw2, hd2, hs2, -⟩ := hk st w1 (wire, s') w' hw1 (hdep1.trans hd) hget1 r2'
  exact ⟨sub, hreal, hs2 mn sub hget1, hw2, hd2, sub_trans hsub1 hs2,
    ⟨mctx, mref, cctx, cref, w1, w', r2'⟩⟩

/-- **`inst_leaf_runs`**: a returning run of the real translator at fuel
`fuel + 1` on a canonical call (none of the core / fallback shapes) of a
designated callee, from an invariant world of positive depth `D`: the run's
child is a `RealChild` and the end cache's entry; invariant, depth and every
start entry kept; the rest is a run of `armCont` on that child. -/
theorem inst_leaf_runs (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
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
    ∃ y : Res, RealChild mref cref mn y ∧ (L.val w').get? mn = some y ∧
      InvV L w' ∧ L.dval w' = D ∧ SubMap (L.val w) (L.val w') ∧
      Returns (armCont (translateFuelFix (translateStep tenv) fuel) mn y
        (instEN mn lvls dom argsE) hint top named) ctx s wire s' := by
  have hstep : translateFuelFix (translateStep tenv) (fuel + 1) (instEN mn lvls dom argsE)
      hint top named =
      translateInstanceOrFallback tenv (translateFuelFix (translateStep tenv) fuel)
        (instEN mn lvls dom argsE) hint top named := by
    show translateStepWith (translateFallback tenv) (translateFuelFix (translateStep tenv) fuel)
      (instEN mn lvls dom argsE) hint top named = _
    exact instanceN_step _ mn lvls _ _ _ _ _ hpure hbin hkind
  rw [hstep] at hr
  exact instanceArm_runW L hD fuel (instEN_getAppFn mn lvls dom argsE) htag hw hd hr

end Tools.ShippingGateParentRun
