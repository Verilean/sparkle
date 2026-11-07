import Tools.ShippingFGCircuitS2mReach
import Tools.ShippingFGCircuitS2sAdmLawsX
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2sAdmS2hHist2
import Tools.ShippingFGCircuitS2sAdmChildCacheA
import Tools.ShippingFGCircuitS2sAdmChildCanonKeyA
import Tools.ShippingFGCircuitS2sAdmChildComposeA
import Tools.ShippingFGCircuitS2sAdmChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildCoreC
import Tools.ShippingFGCircuitS2sAdmChildDepthA
import Tools.ShippingFGCircuitS2sAdmChildDepthC
import Tools.ShippingFGCircuitS2sAdmChildFallbackA
import Tools.ShippingFGCircuitS2sAdmChildFrontA
import Tools.ShippingFGCircuitS2sAdmChildFrontCP
import Tools.ShippingFGCircuitS2sAdmChildInvA
import Tools.ShippingFGCircuitS2sAdmChildLegacyCachedA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHandlersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyHelpersA
import Tools.ShippingFGCircuitS2sAdmChildLegacyImplA
import Tools.ShippingFGCircuitS2sAdmChildLegacyTailA
import Tools.ShippingFGCircuitS2sAdmChildMainA
import Tools.ShippingFGCircuitS2sAdmChildPathA
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildRunAMain
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTeleMainA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
import Tools.ShippingFGCircuitS2sAdmChildPinC
import Tools.ShippingFGCircuitS2sAdmCallsGatePinned
import Tools.ShippingFGCircuitS2sAdmRunLocal
import Tools.ShippingFGCircuitS2sAdmLinked
import Tools.ShippingFGCircuitS2sAdmRunReads
import Tools.ShippingFGCircuitS2sAdmServedRealA
import Tools.ShippingFGCircuitS2sAdmParentRanA
import Tools.ShippingFGCircuitS2sAdmParentTailsA
import Tools.ShippingFGCircuitS2sAdmParentDesignA
import Tools.ShippingFGCircuitS2sAdmS1qLinked
import Tools.ShippingFGCircuitS2sAdmS1tFinal
import Tools.ShippingFGCircuitS2sAdmS1uSrc
import Tools.ShippingFGCircuitS2sAdmS1zClose
import Tools.ShippingFGCircuitS2sAdmS2dKids
import Tools.ShippingFGCircuitS2sAdmS2hHist3
-- FG circuit pilot S2s5: HAND port of ShippingFGCircuitS2mReach.lean onto the context-predicate bundle `RefLawsAOpsX`: `LeafStepX/ReachedX/quietRX` carry the context predicate `adm`, `ropsRX` keeps `O.adm` (no `AdmDownR`/`hdown`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- FG circuit pilot S2m (part 1): a REACHABILITY / ENVIRONMENT invariant from the target root run's start world `w₀`, replacing the universal miss premise `MissE` (S2h, FG D.T-4h). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §39.
-- Design (reviewer ruling on S2h): `MissE` was universal over every `JQH` world where a miss occurs; for an empty cache the `JQH` cache condition is trivial, so `ReadsAt` to the fixed root environment did not follow from the history condition. Here the invariant carries, in the QUIET predicate itself, (i) `O.quiet`, (ii) `ReadsAt e cref w` with `e = envAt cref w₀`, (iii) `Reached w₀ w` (generated from the root start world by the leaf steps of the laws). `JQH` over this strengthened `RefLawsAOps` (`ropsR`) is the invariant `JQHR`; all the S2h theorems (core chain, `synthesizeChild` miss/hit, `closeInstsM/GM`, the body steps) apply to it unchanged. What the strengthened quiet predicate needs beyond what is proved from `CellPrem` is stated as NAMED run-local hypotheses (`DRowEnvR`, `DiagEnvR`, `TeleR`, `ProfStepR`, `ProfOffW` at the root, `AdmDownR`, `AdmRootR`), each over reached worlds only.

namespace Tools.ShippingFGCircuitS2mReach
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (endW endW_of_runs Throws Op)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingGen5Env (ReadsAt readsAt_self)
open Tools.ShippingGen5EnvFrame (readsAt_endW)
open Tools.ShippingGen5EnvFrame3 (CellPrem DRow envFrameEnd_framedA envFrameEnd_throws)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2hHist
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt)
open Sparkle.Compiler.Elab (sparkleChildCache sparkleSynthDepth)

section Defs
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **One leaf step of the laws**: the world after a run of an operation of one of the classes the laws speak of (a `FramedA` row, a diagnostic, a `throwError`, a write of the child cache or of the depth), in an admissible context. Arbitrary `MetaM` code is NOT a leaf step. -/
inductive LeafStepX (quiet : Void IO.RealWorld → Prop) (adm : CtxPred) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : Void IO.RealWorld → Void IO.RealWorld → Prop
  | frame {α : Type} (mctx : Meta.Context) (cctx : Core.Context) (p : MetaM α) (w : Void IO.RealWorld) :
      adm mctx cctx → FramedA MkRefd p → LeafStepX quiet adm mref cref w (endW mctx mref cctx cref p w)
  | diag {α : Type} (mctx : Meta.Context) (cctx : Core.Context) (p : MetaM α) (w : Void IO.RealWorld) :
      adm mctx cctx → Tools.ShippingChildInv.Diag p → LeafStepX quiet adm mref cref w (endW mctx mref cctx cref p w)
  | throws {α : Type} (mctx : Meta.Context) (cctx : Core.Context) (p : MetaM α) (w : Void IO.RealWorld) :
      adm mctx cctx → Throws p → LeafStepX quiet adm mref cref w (endW mctx mref cctx cref p w)
  | cacheSet (mctx : Meta.Context) (cctx : Core.Context) (v : Std.HashMap Name Tools.ShippingChildInv.Res)
      (w : Void IO.RealWorld) (u : Unit) (w' : Void IO.RealWorld) :
      adm mctx cctx →
      RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → LeafStepX quiet adm mref cref w w'
  | depthSet (mctx : Meta.Context) (cctx : Core.Context) (v : Nat)
      (w : Void IO.RealWorld) (u : Unit) (w' : Void IO.RealWorld) :
      adm mctx cctx →
      RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → LeafStepX quiet adm mref cref w w'

/-- **Reached from the root start world `w₀`** by leaf steps. -/
inductive ReachedX (quiet : Void IO.RealWorld → Prop) (adm : CtxPred) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) (w₀ : Void IO.RealWorld) : Void IO.RealWorld → Prop
  | start : ReachedX quiet adm mref cref w₀ w₀
  | step {w w' : Void IO.RealWorld} : ReachedX quiet adm mref cref w₀ w → LeafStepX quiet adm mref cref w w' →
      ReachedX quiet adm mref cref w₀ w'

/-- **The strengthened quiet predicate**: quiet, the Core environment reads as `e` (`ReadsAt`), and the world is reached from `w₀` -/
abbrev quietRX (quiet : Void IO.RealWorld → Prop) (adm : CtxPred) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) (e : Environment) (w₀ : Void IO.RealWorld) :
    Void IO.RealWorld → Prop :=
  fun w => quiet w ∧ ReadsAt e cref w ∧ ReachedX quiet adm mref cref w₀ w

/-! ## the named run-local hypotheses (complete types first) -/

/-- NAMED HYPOTHESIS (FG D.T-4m1, class-D rows `whnf`/`inferType`/`isClass?`/`whnfUntil`/`instantiateForall`/`mkLambdaFVars`/`mkAppM`/`unfoldDefinition?`/`reduce`/`ioEnv`/`monoMs`/`mkExprCache`/`localMk`): from a quiet world reached from `w₀` whose Core environment reads as `e`, in an admissible context, a run of a class-D operation leaves a world whose Core environment reads as `e`. (`DRow` rows are exactly the `FramedA` rows that `CellPrem` does not frame.) -/
def DRowEnvRX (O : RefLawsAOpsX MkRefd mref cref) (e : Environment) (w₀ : Void IO.RealWorld) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) {α : Type} (p : MetaM α), O.adm mctx cctx → DRow p →
    ∀ w : Void IO.RealWorld, O.quiet w → ReadsAt e cref w → ReachedX O.quiet O.adm mref cref w₀ w →
      ReadsAt e cref (endW mctx mref cctx cref p w)

/-- NAMED HYPOTHESIS (FG D.T-4m2, diagnostic rows `profLog`/`ppExpr`/`ioEprintln`/`msgToString`/`ioGetStderr`/`stderrFlush`/`ioHandleMk`/`ioHandlePutStrLn`/`ioHandleFlush`): the same for a diagnostic operation -/
def DiagEnvRX (O : RefLawsAOpsX MkRefd mref cref) (e : Environment) (w₀ : Void IO.RealWorld) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) {α : Type} (p : MetaM α), O.adm mctx cctx →
    Tools.ShippingChildInv.Diag p →
    ∀ w : Void IO.RealWorld, O.quiet w → ReadsAt e cref w → ReachedX O.quiet O.adm mref cref w₀ w →
      ReadsAt e cref (endW mctx mref cctx cref p w)

/-- NAMED HYPOTHESIS (FG D.T-4m3, the four telescope rows `forallTelescopeReducing`/`lambdaTelescope`/`withLocalDeclD`/`withLetDecl`): the continuation law of `RefLawsATele`, at the strengthened quiet predicate (so only for invariants whose worlds are quiet, read `e`, and are reached from `w₀`) -/
abbrev TeleRX (O : RefLawsAOpsX MkRefd mref cref) (e : Environment) (w₀ : Void IO.RealWorld) : Prop :=
  RefLawsATeleX (quietRX O.quiet O.adm mref cref e w₀) O.adm mref cref

/-- NAMED HYPOTHESIS (FG D.T-4m4): a leaf step from a reached world keeps the profile lookup unset (the process environment variable is not written by any leaf operation) -/
def ProfStepRX (O : RefLawsAOpsX MkRefd mref cref) (w₀ : Void IO.RealWorld) : Prop :=
  ∀ w w' : Void IO.RealWorld, ReachedX O.quiet O.adm mref cref w₀ w → LeafStepX O.quiet O.adm mref cref w w' →
    ProfOffW mref cref w → ProfOffW mref cref w'

end Defs

section Build
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem ReachedX.leafFrame {O : RefLawsAOpsX MkRefd mref cref} {w₀ w : Void IO.RealWorld}
    (h : ReachedX O.quiet O.adm mref cref w₀ w) {mctx : Meta.Context} {cctx : Core.Context} {α : Type} {p : MetaM α}
    (hA : O.adm mctx cctx) (hp : FramedA MkRefd p) :
    ReachedX O.quiet O.adm mref cref w₀ (endW mctx mref cctx cref p w) :=
  .step h (.frame mctx cctx p w hA hp)

/-- **The strengthened operations bundle** `ropsR`: the plain operations laws `O`, with `quiet` strengthened by `ReadsAt e` and reachability from `w₀`. The non-class-D framed rows, the throws, the cache/depth writes keep `ReadsAt` from `CellPrem` (`envFrameEnd_*`); the class-D rows and the diagnostics from the named hypotheses `hD`, `hG`; the contexts from `hdown`. -/
def ropsRX (O : RefLawsAOpsX MkRefd mref cref) (hcell : CellPrem MkRefd mref cref) (e : Environment)
    (w₀ : Void IO.RealWorld) (hD : DRowEnvRX O e w₀) (hG : DiagEnvRX O e w₀) :
    RefLawsAOpsX MkRefd mref cref where
  quiet := quietRX O.quiet O.adm mref cref e w₀
  adm := O.adm
  adm_closed := O.adm_closed
  diag := by
    intro mctx cctx α adm p hp w hw
    obtain ⟨hq, hR, hr⟩ := hw
    have a := adm
    have H := O.diag a p hp w hq
    exact ⟨H.1, H.2, hG mctx cctx p a hp w hq hR hr, .step hr (.diag mctx cctx p w a hp)⟩
  frameT := by
    intro mctx cctx α adm p hp w hw
    obtain ⟨hq, hR, hr⟩ := hw
    obtain ⟨hC, hS, hD', hSide, hFresh, hm, hmf, hmne, hc, hsg⟩ := hcell
    have a := adm
    have H := O.frameT a p hp w hq
    exact ⟨H.1, H.2, readsAt_endW (envFrameEnd_throws hp hc hm) hR, .step hr (.throws mctx cctx p w a hp)⟩
  excOk := by
    intro mctx cctx α adm p hp w e' w' hw h
    exact O.excOk adm p hp w e' w' hw.1 h
  frameQ := by
    intro mctx cctx α adm p hp w hw
    obtain ⟨hq, hR, hr⟩ := hw
    have a := adm
    refine ⟨O.frameQ a p hp w hq, ?_, hr.leafFrame a hp⟩
    by_cases hnd : DRow p
    · exact hD mctx cctx p a hnd w hq hR hr
    · exact readsAt_endW (envFrameEnd_framedA hcell hp hnd) hR
  cacheSetQ := by
    intro mctx cctx adm v w u w' h hw
    obtain ⟨hq, hR, hr⟩ := hw
    have a := adm
    have he := endW_of_runs h
    have hf : Tools.ShippingGen5EnvFrame.EnvFrameEnd (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref :=
      Tools.ShippingGen5EnvFrame.envFrameEnd_set v hcell.1.2.1 hcell.1.2.2
    refine ⟨O.cacheSetQ a v w u w' h hq, ?_, .step hr (.cacheSet mctx cctx v w u w' a h)⟩
    rw [← he]
    exact readsAt_endW hf hR
  depthSetQ := by
    intro mctx cctx adm v w u w' h hw
    obtain ⟨hq, hR, hr⟩ := hw
    have a := adm
    have he := endW_of_runs h
    have hf : Tools.ShippingGen5EnvFrame.EnvFrameEnd (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref :=
      Tools.ShippingGen5EnvFrame.envFrameEnd_set v hcell.2.2.1.2.1 hcell.2.2.1.2.2
    refine ⟨O.depthSetQ a v w u w' h hq, ?_, .step hr (.depthSet mctx cctx v w u w' a h)⟩
    rw [← he]
    exact readsAt_endW hf hR
  frame := by
    intro mctx cctx α adm p hp w hw
    exact O.frame adm p hp w hw.1
  cacheSet := by
    intro mctx cctx adm v w u w' h hw
    exact O.cacheSet adm v w u w' h hw.1
  depthSet := by
    intro mctx cctx adm v w u w' h hw
    exact O.depthSet adm v w u w' h hw.1

end Build

end Tools.ShippingFGCircuitS2mReach
