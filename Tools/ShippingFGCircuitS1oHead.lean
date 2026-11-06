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
  repeat' ((try dsimp -zeta only); ef_step)
  rw [if_neg (by simp)]
  exact EnvFrame.pure ()

section Finals
open Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingStRefCorrespondence (ReadWorld)

/-- **`counterLoop_final9P`**: `counterLoop_final9` with the head fact supplied on the profile-disabled run form: `CellPrem` + `GetEnvProfileAt` at the start world (instead of `HeadIO`; no log obligation) -/
theorem counterLoop_final9P {ι : Type} (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (hg : GetEnvProfileAt mctx mref cctx cref w)
    (hread : ReadsAt env₀ cref w)
    (hgatesB : entryGatesB env₀ ``counterLoop = true)
    (hquote : QuoteAt env₀ ``counterLoop counterLoopType counterLoopValue)
    (hreader : ReaderAt lvl env₀ ``counterLoop counterLoop.machineData) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p :=
  counterLoop_final9 L lvl env₀ hstart hr (headAt_of_profileOff _ hcell hg) hcell.2.2.2.2.2.2.2.2.1 hread hgatesB hquote hreader

end Finals

/-! ## FREEZE DRAFT — UNAPPROVED, NOT COUNTED, NOT ABSORBED INTO C.EN-4 / Laws, USED BY NO THEOREM ABOVE

The log branch (`profile = true`) obligation, if the log is kept in scope, with the stderr callback separated from the fixed Handle operations.
`StderrPreserves`: `IO.eprintln msg; flushStderr` write to the CURRENT stderr stream (`setStderr` may have installed an arbitrary `putStr`/`flush` callback), so the env-preservation is an explicit condition about that callback, never a general runtime law.
`FixedHandlePreserves`: `IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append; putStrLn; flush` (fixed path, fixed `Handle` primitives). -/
def logTailAct (msg : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
  h.putStrLn msg
  h.flush

def logStderrAct (msg : String) : IO Unit := do
  IO.eprintln msg
  Sparkle.Compiler.flushStderr

structure LogBranchDraft (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop where
  stderrPreserves : ∀ msg, EnvFrame (liftM (logStderrAct msg) : MetaM Unit) mctx mref cctx cref
  fixedHandlePreserves : ∀ msg, EnvFrame (liftM (logTailAct msg) : MetaM Unit) mctx mref cctx cref

end Tools.ShippingFGCircuitS1oHead

#print axioms Tools.ShippingFGCircuitS1oHead.headAt_of_profileOff
#print axioms Tools.ShippingFGCircuitS1oHead.counterLoop_final9P
