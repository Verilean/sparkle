import Tools.ShippingFGCircuitS1iHead
set_option autoImplicit false
-- FG circuit pilot S1o: `HeadAt` on the profile-DISABLED run form, from a run-local premise on the getEnv result plus `CellPrem`; the log branch is not entered.  No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1o: the profile-disabled path of `coreHead`

`coreHead X` decides profiling by its FIRST action: `profile := (← IO.getEnv "SPARKLE_PROFILE").isSome`; the log action `logProf` runs `IO.eprintln`, `flushStderr`, `IO.FS.Handle.mk`, `putStrLn`, `flush` only if `profile`.
Reviewer ruling (S1o, 所見C): `profLogIO true` can run an arbitrary `IO` callback (`FS.Stream.putStr`, `setStderr`), so "∀ world, the log preserves `envAt cref`" is not adopted as a runtime law.  The guaranteed path is therefore the run in which the log branch is not taken.
* `GetEnvProfileAt` is the minimal run-local premise at the run's start world `w`: any run of `IO.getEnv "SPARKLE_PROFILE"` from `w` returns `none` and keeps the Core environment.  It is a named hypothesis about the run, NOT obtained from a Meta observation of the process environment.
* `headAt_of_profileOff` proves `HeadAt X w` from `CellPrem` and `GetEnvProfileAt` using only the existing `EnvFrame` lemmas (`bind`, `pure`, `ite`, get/set cells, `throwError`); `HeadIO` is not used and no law is added.
* `LogBranchDraft` (UNAPPROVED, not counted, not absorbed into C.EN-4/Laws, never used by a theorem here) records the exact obligation if the log branch were kept in scope: stderr callback separated from the fixed Handle operations. -/
namespace Tools.ShippingFGCircuitS1oHead
open Lean Tools.ShippingEntryReadsLinked Tools.ShippingEnvSnapshot Sparkle.Compiler.Elab
open Tools.ShippingGen5EnvFrame3 (CellPrem CellOK)
open Tools.ShippingChildInv (SideRef)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingFGCircuitS1iHead
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the first action of `coreHead`, as a `MetaM` action -/
abbrev profileAct : MetaM (Option String) := liftM (IO.getEnv "SPARKLE_PROFILE")

/-- **minimal getEnvProfile frame (run-local)**: from the start world `w`, a run of the profile lookup returns `none` and keeps the Core environment -/
structure GetEnvProfileAt (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop where
  unset : ∀ (o : Option String) (w1 : Void IO.RealWorld), RunsTo profileAct mctx mref cctx cref w o w1 → o = none
  env : ∀ (o : Option String) (w1 : Void IO.RealWorld), RunsTo profileAct mctx mref cctx cref w o w1 → envAt cref w1 = envAt cref w

set_option maxHeartbeats 1000000 in
/-- **`HeadAt` on the profile-disabled run** from `CellPrem` and the run-local `GetEnvProfileAt` -/
theorem headAt_of_profileOff (X : Name) {w : Void IO.RealWorld} (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hg : GetEnvProfileAt mctx mref cctx cref w) : HeadAt X mctx mref cctx cref w := by
  intro s w1 hh
  obtain ⟨hC, hS, hD, hSide, -, hm, -, -, hc, -⟩ := hcell
  unfold coreHead at hh
  obtain ⟨o, w0, h0, h1⟩ := Tools.ShippingEntrySoundness.RunsTo.bind hh
  have ho := hg.unset o w0 h0
  have he := hg.env o w0 h0
  subst ho
  refine Eq.trans ((?_ : EnvFrame _ mctx mref cctx cref) w0 s w1 h1) he
  sorry

end Tools.ShippingFGCircuitS1oHead
