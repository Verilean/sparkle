import Tools.ShippingFGCircuitS3f2Final
set_option autoImplicit false
-- FG circuit pilot S3j, unit 1: the checked pilot wrapper `pilotEntry3` (the entry `synthesizeCombinationalOffR pilotReaderOk2` behind TWO start checks made INSIDE MetaM: the run's own Meta context has no `canUnfold?` callback, and `sparkleSynthDepth` reads 0), and what a successful run of it gives: `AdmCtx quiet mctx cctx` for every `quiet` and `dv w = 0`, and a run of the existing OffR entry from the SAME world `w` (the depth cell is `ReadWorld`).  An `Environment → Name → Bool` reader check cannot see the Meta context or the depth ref (it is a pure function of the environment), so the checks are in the wrapper, not in `pilotReaderOk2`.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §60.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3jStart
open Lean Meta Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (readOf)
open Tools.ShippingStRefCorrespondence (ReadWorld getW)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA (AdmCtx admCtx_none)
open Tools.ShippingFGCircuitS3f2Final (pilotReaderOk2)

/-- the S3j pilot entry: the S3f2 entry `synthesizeCombinationalOffR pilotReaderOk2` behind two start checks (an explicit error, no fallback): (1) the Meta context of THIS run has no `canUnfold?` callback; (2) `sparkleSynthDepth` is 0 -/
def pilotEntry3 (declName : Name) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let ctx ← readThe Meta.Context
  unless ctx.canUnfold?.isNone do
    throwError "pilot entry: the Meta context has a canUnfold? callback; refusing to synthesize"
  let depth ← sparkleSynthDepth.get
  unless depth == 0 do
    throwError "pilot entry: the synthesis depth is not 0; refusing to synthesize"
  synthesizeCombinationalOffR pilotReaderOk2 declName

section Runs
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the Meta-context read returns THE context of the run and keeps the world -/
theorem runsTo_readThe {w w' : Void IO.RealWorld} {a : Meta.Context}
    (h : RunsTo (readThe Meta.Context : MetaM Meta.Context) mctx mref cctx cref w a w') : a = mctx ∧ w' = w := by
  unfold RunsTo at h
  change EST.Out.ok mctx w = _ at h
  cases h; exact ⟨rfl, rfl⟩

/-- reading the Meta context and continuing is the continuation at THE context of the run -/
theorem runsTo_readThe_bind {β : Type} {f : Meta.Context → MetaM β} {w w' : Void IO.RealWorld} {r : β}
    (h : RunsTo ((readThe Meta.Context : MetaM Meta.Context) >>= f) mctx mref cctx cref w r w') :
    RunsTo (f mctx) mctx mref cctx cref w r w' := h

/-- a `get` returns the cell's contents and moves the world to `getW` -/
theorem runsTo_get {σ : Type} (r : IO.Ref σ) {w w' : Void IO.RealWorld} {a : σ}
    (h : RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w a w') : a = readOf r w ∧ w' = getW r w := by
  unfold RunsTo at h
  change (match (ST.Ref.get r : ST IO.RealWorld σ) w with | .mk a s => EST.Out.ok a s) = _ at h
  cases hg : (ST.Ref.get r : ST IO.RealWorld σ) w with
  | mk b s =>
    have h1 : readOf r w = b := by unfold readOf; rw [hg]
    have h2 : getW r w = s := by unfold getW; rw [hg]
    rw [hg] at h
    change EST.Out.ok b s = EST.Out.ok a w' at h
    injection h with h3 h4
    exact ⟨by rw [← h3, h1], by rw [← h4, h2]⟩

/-- **the two start checks and the run behind them**: a successful run of `pilotEntry3` from `w` gives (1) no `canUnfold?` callback in the run's own Meta context, (2) the depth cell reads 0 at `w`, and (3) a successful run of `synthesizeCombinationalOffR pilotReaderOk2` with the same result and end world from the world after the depth read, `getW sparkleSynthDepth w` -/
theorem pilotEntry3_run {X : Name} {w w' : Void IO.RealWorld} {r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (hr : RunsTo (pilotEntry3 X) mctx mref cctx cref w r w') :
    mctx.canUnfold? = none ∧ readOf sparkleSynthDepth w = 0 ∧
      RunsTo (synthesizeCombinationalOffR pilotReaderOk2 X) mctx mref cctx cref (getW sparkleSynthDepth w) r w' := by
  unfold pilotEntry3 at hr
  replace hr := runsTo_readThe_bind hr
  dsimp only at hr
  by_cases hc : mctx.canUnfold?.isNone = true
  · rw [if_pos hc] at hr
    obtain ⟨depth, w2, h2, hr⟩ := Tools.ShippingEntrySoundness.RunsTo.bind hr
    obtain ⟨hdv, rfl⟩ := runsTo_get sparkleSynthDepth h2
    by_cases hd : (depth == 0) = true
    · rw [if_pos hd] at hr
      refine ⟨by simpa using hc, ?_, hr⟩
      rw [← hdv]; simpa using hd
    · rw [if_neg hd] at hr
      obtain ⟨u3, w3, h3, -⟩ := Tools.ShippingEntrySoundness.RunsTo.bind hr
      exact (Tools.ShippingEntrySoundness.RunsTo.throwError_false h3).elim
  · rw [if_neg hc] at hr
    obtain ⟨u3, w3, h3, -⟩ := Tools.ShippingEntrySoundness.RunsTo.bind hr
    exact (Tools.ShippingEntrySoundness.RunsTo.throwError_false h3).elim

end Runs

end Tools.ShippingFGCircuitS3jStart
