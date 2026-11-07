import Tools.ShippingFGCircuitS3nModel
import Tools.ShippingFGCircuitS3mField
import Tools.ShippingFGCircuitS3jStart
set_option autoImplicit false
-- FG circuit pilot S3n (E1, step 3): the connection between the explicit-state model (`Tools.ShippingFGCircuitS3nModel`) and the REAL world / refs / context.  `Rel`, the leaf correspondences (`GetCorr`, `SetCorr`, `StderrCorr`, `EnvCorr`) and the initial correspondence are written out as named HYPOTHESES (Props); none is adopted, none is a TRUSTED item, none is supplied for the runtime.  Direction: a REAL run succeeds → the model run succeeds with the related return value and a related end state.  The bridge lemmas (pure, bind, get/set, a small composition) are proved UNDER those hypotheses; no hypothesis states a final conclusion.  docs/FG-CIRCUIT-PILOT.md §64.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3nBridge
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (readOf Res)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingStRefCorrespondence (ReadWorld SetGet SetFrame getW setW)
open Tools.ShippingHeapModel (Sig Heap Ref M Out getM setM bindM pureM hget hset)
open Tools.ShippingFGCircuitS3n

open Sparkle.Compiler.Elab

/-- the model signature whose tracked contents are the REAL types of the three compiler refs -/
abbrev realSig : Sig := sigOf (Std.HashMap Name Res) (Option (Name → MetaM Res))

/-- the MODEL's successful run (`ShippingHeapModel.RunsTo`); the unqualified `RunsTo` below is the REAL one -/
abbrev MRunsTo {α : Type} (p : M realSig α) (h : Heap realSig) (a : α) (h' : Heap realSig) : Prop :=
  Tools.ShippingHeapModel.RunsTo p h a h'
open Tools.ShippingFGCircuitS3m (stderrW StderrKeeps)

/-- the correspondence of a model heap and a real world: the three tracked refs hold EXACTLY the model's contents.  Nothing is said about `mref`, `cref`, the side refs, the diagnostic output or the environment (their real counterparts are not Lean terms of the world). -/
def Rel (h : Heap realSig) (w : Void IO.RealWorld) : Prop :=
  cv w = h.cache ∧ sv w = h.synth ∧ dv w = h.depth

/-- **correspondence of a leaf (HYPOTHESIS shape)**: if the REAL action `m` runs successfully from a world related to the model heap `h`, then the model action `p` runs successfully from `h` with a return value related by `RA`, and the end states are related.  Direction: real success → model success. -/
def Corr (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) {α β : Type} (RA : α → β → Prop) (m : MetaM α) (p : M realSig β) : Prop :=
  ∀ (w w' : Void IO.RealWorld) (h : Heap realSig) (a : α),
    Rel h w → RunsTo m mctx mref cctx cref w a w' → ∃ (b : β) (h' : Heap realSig), MRunsTo p h b h' ∧ RA a b ∧ Rel h' w'

section Hyps
variable (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
  (cref : ST.Ref IO.RealWorld Core.State)

/-- HYPOTHESIS: the real `get` of `r` corresponds to the model's `get` of `rm`, same value -/
def GetCorr {σ : Type} (r : IO.Ref σ) (rm : Ref realSig σ) : Prop :=
  Corr mctx mref cctx cref (· = ·) (ST.Ref.get r : MetaM σ) (getM rm)
/-- HYPOTHESIS: the real `set` of `r` corresponds to the model's `set` of `rm` -/
def SetCorr {σ : Type} (r : IO.Ref σ) (rm : Ref realSig σ) : Prop :=
  ∀ v : σ, Corr mctx mref cctx cref (· = ·) (ST.Ref.set r v : MetaM Unit) (setM rm v)
/-- HYPOTHESIS: the real `IO.getStderr` corresponds to the model's `getStderr`; the stream value is NOT compared -/
def StderrCorr : Prop :=
  Corr mctx mref cctx cref (fun _ _ => True) (liftM IO.getStderr : MetaM IO.FS.Stream) (getStderrM (C := Std.HashMap Name Res) (S := Option (Name → MetaM Res)))
/-- REFUTED in S3o (`Tools.ShippingFGCircuitS3oFix.envCorr_inconsistent`): `Rel` does not bind the environment, so this is incompatible with any successful real `getEnv`.  Superseded by `EnvCorrE`.
HYPOTHESIS: the real `IO.getEnv k` corresponds to the model's lookup in its environment component (this includes the claim that the model's environment component is the process environment) -/
def EnvCorr (k : String) : Prop :=
  Corr mctx mref cctx cref (· = ·) (liftM (IO.getEnv k) : MetaM (Option String)) (getEnvM (C := Std.HashMap Name Res) (S := Option (Name → MetaM Res)) k)
end Hyps

/-- REFUTED as a restriction in S3o (`oldInit_any_world`): holds at every world.  Superseded by `InitCorrE`.
HYPOTHESIS (initial correspondence): the start world `w0` of the run is related to a model heap in which the concrete quiet holds -/
def InitCorr (w0 : Void IO.RealWorld) : Prop := ∃ h0 : Heap realSig, Rel h0 w0 ∧ quietM h0

/-- REFUTED as a restriction in S3o (`oldQuietR_eq_true`: it equals `fun _ => True`).  Superseded by `quietRE`.
the quiet induced on worlds by `Rel` and the model's quiet -/
def quietR (w : Void IO.RealWorld) : Prop := ∃ h : Heap realSig, Rel h w ∧ quietM h

section Bridge
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
  {cref : ST.Ref IO.RealWorld Core.State}

/-- a real `set` run ends in `setW` and returns `()` -/
theorem runsTo_set {σ : Type} (r : IO.Ref σ) (v : σ) {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref w u w') : w' = setW r v w := by
  unfold RunsTo at h
  change (match (ST.Ref.set r v : ST IO.RealWorld Unit) w with | .mk a s => EST.Out.ok a s) = _ at h
  cases hg : (ST.Ref.set r v : ST IO.RealWorld Unit) w with
  | mk b s =>
    have h2 : setW r v w = s := by unfold setW; rw [hg]
    rw [hg] at h
    change EST.Out.ok b s = EST.Out.ok u w' at h
    injection h with _ h4
    rw [← h4, h2]

/-- the lifted `IO.getStderr` always runs, and ends in `stderrW w` -/
theorem runsTo_getStderr (w : Void IO.RealWorld) :
    ∃ a, RunsTo (liftM IO.getStderr : MetaM IO.FS.Stream) mctx mref cctx cref w a (stderrW w) := by
  unfold RunsTo stderrW
  cases hg : (IO.getStderr : BaseIO IO.FS.Stream) w with
  | mk a s =>
    refine ⟨a, ?_⟩
    change (match (IO.getStderr : BaseIO IO.FS.Stream) w with | .mk a s => EST.Out.ok a s) = _
    rw [hg]

/-- `pure` corresponds to `pure` -/
theorem corr_pure {α β : Type} (RA : α → β → Prop) (a : α) (b : β) (hab : RA a b) :
    Corr mctx mref cctx cref RA (pure a : MetaM α) (pureM b) := by
  intro w w' h a' hrel hr
  unfold RunsTo at hr
  cases hr
  exact ⟨b, h, rfl, hab, hrel⟩

/-- **bind composition**: correspondences of the parts compose (the continuation's correspondence is needed for every related pair of intermediate values) -/
theorem corr_bind {α β γ δ : Type} {RA : α → β → Prop} {RB : γ → δ → Prop} {m : MetaM α} {p : M realSig β}
    {f : α → MetaM γ} {g : β → M realSig δ}
    (hm : Corr mctx mref cctx cref RA m p) (hf : ∀ a b, RA a b → Corr mctx mref cctx cref RB (f a) (g b)) :
    Corr mctx mref cctx cref RB (m >>= f) (bindM p g) := by
  intro w w'' h c hrel hr
  obtain ⟨a, w1, hm1, hf1⟩ := Tools.ShippingEntrySoundness.RunsTo.bind hr
  obtain ⟨b, h1, hp1, hab, hrel1⟩ := hm w w1 h a hrel hm1
  obtain ⟨d, h2, hp2, hcd, hrel2⟩ := hf a b hab w1 w'' h1 c hrel1 hf1
  refine ⟨d, h2, ?_, hcd, hrel2⟩
  unfold MRunsTo Tools.ShippingHeapModel.RunsTo at hp1 hp2 ⊢
  simp only [bindM, hp1]
  exact hp2

/-! ### what the CellPrem fields give for the hypotheses (the hypotheses are WEAKER than those fields) -/

/-- `ReadWorld r` (a `CellPrem` field) plus the value agreement of `r` with `rm` on related states gives `GetCorr r rm` -/
theorem getCorr_of_readWorld {σ : Type} (r : IO.Ref σ) (rm : Ref realSig σ) (hRW : ReadWorld r)
    (hv : ∀ w h, Rel h w → readOf r w = hget rm h) : GetCorr mctx mref cctx cref r rm := by
  intro w w' h a hrel hr
  have hg := Tools.ShippingFGCircuitS3jStart.runsTo_get r hr
  obtain ⟨ha, hw⟩ := hg
  have hw' : w' = w := by rw [hw]; exact hRW w
  subst hw'
  exact ⟨a, h, by rw [ha, hv _ _ hrel]; rfl, by rw [ha, hv _ _ hrel], hrel⟩

theorem getCorr_depth (hRW : ReadWorld sparkleSynthDepth) : GetCorr mctx mref cctx cref sparkleSynthDepth rDepth :=
  getCorr_of_readWorld _ _ hRW (fun _ _ hrel => hrel.2.2)

/-- `SetGet` and `SetFrame` of the depth ref (with the two pointer inequalities) give `SetCorr` of the depth ref -/
theorem setCorr_depth (hSG : SetGet sparkleSynthDepth) (hF1 : SetFrame sparkleSynthDepth sparkleChildCache)
    (hF2 : SetFrame sparkleSynthDepth sparkleChildSynth) (hne1 : sparkleSynthDepth.ref ≠ sparkleChildCache.ref)
    (hne2 : sparkleSynthDepth.ref ≠ sparkleChildSynth.ref) :
    SetCorr mctx mref cctx cref sparkleSynthDepth rDepth := by
  intro v w w' h u hrel hr
  have hw := runsTo_set _ _ hr
  subst hw
  refine ⟨(), hset rDepth v h, rfl, rfl, ?_, ?_, ?_⟩
  · exact (hF1 hne1 v w).trans hrel.1
  · exact (hF2 hne2 v w).trans hrel.2.1
  · exact hSG v w

/-! ### the small composition: get depth; set depth (d+1); getStderr; return d -/

def realProg : MetaM Nat :=
  (ST.Ref.get sparkleSynthDepth : MetaM Nat) >>= fun d =>
  (ST.Ref.set sparkleSynthDepth (d + 1) : MetaM Unit) >>= fun _ =>
  (liftM IO.getStderr : MetaM IO.FS.Stream) >>= fun _ =>
  pure d

def modelProg : M realSig Nat :=
  bindM (getM rDepth) fun d =>
  bindM (setM rDepth (d + 1)) fun _ =>
  bindM getStderrM fun _ =>
  pureM d

/-- **the bridge for the small composition**, under the three leaf hypotheses only: a real run of `realProg` that succeeds gives a model run of `modelProg` that succeeds, with the SAME return value and a related end state -/
theorem bridge_small (hG : GetCorr mctx mref cctx cref sparkleSynthDepth rDepth)
    (hS : SetCorr mctx mref cctx cref sparkleSynthDepth rDepth) (hE : StderrCorr mctx mref cctx cref) :
    Corr mctx mref cctx cref (· = ·) realProg modelProg := by
  unfold realProg modelProg
  refine corr_bind hG fun d b hdb => ?_
  subst hdb
  refine corr_bind (hS (d + 1)) fun _ _ _ => ?_
  refine corr_bind hE fun _ _ _ => ?_
  exact corr_pure _ d d rfl

/-- the model run of `modelProg` returns the depth and writes depth+1, nothing else tracked changes -/
theorem modelProg_spec {h h' : Heap realSig} {a : Nat} (hr : MRunsTo modelProg h a h') :
    a = h.depth ∧ h'.depth = h.depth + 1 ∧ h'.cache = h.cache ∧ h'.synth = h.synth ∧ (quietM h' ↔ quietM h) := by
  change Out.ok h.depth (hset rDepth (h.depth + 1) h) = Out.ok a h' at hr
  injection hr with h1 h2
  subst h1; subst h2
  exact ⟨rfl, rfl, rfl, rfl, Iff.rfl⟩

/-- **a consequence about the REAL run, obtained through the model** (under the three hypotheses and `Rel`): a successful real run of `realProg` returns the depth the model state had, and ends with depth+1, the same cache and the same synthesis ref -/
theorem real_small_consequence (hG : GetCorr mctx mref cctx cref sparkleSynthDepth rDepth)
    (hS : SetCorr mctx mref cctx cref sparkleSynthDepth rDepth) (hE : StderrCorr mctx mref cctx cref)
    {w w' : Void IO.RealWorld} {h : Heap realSig} {a : Nat} (hrel : Rel h w)
    (hr : RunsTo realProg mctx mref cctx cref w a w') :
    a = dv w ∧ dv w' = dv w + 1 ∧ cv w' = cv w ∧ sv w' = sv w := by
  obtain ⟨b, h', hp, hab, hrel'⟩ := bridge_small hG hS hE w w' h a hrel hr
  obtain ⟨e1, e2, e3, e4, -⟩ := modelProg_spec hp
  subst hab
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrel.2.2]; exact e1
  · rw [hrel'.2.2, hrel.2.2]; exact e2
  · rw [hrel'.1, hrel.1]; exact e3
  · rw [hrel'.2.1, hrel.2.1]; exact e4

/-! ### what the correspondence can feed: `StderrKeeps` for the induced quiet -/

/-- **`StderrCorr` (+ the model's `getStderr`) gives `StderrKeeps quietR`** — the `diag`-at-`ioGetStderr` instance of `Laws`, for the quiet induced by `Rel`.  It is NOT `Laws.O.diag` (all `Diag` constructors, all admissible contexts), and it says nothing for the quiet of an arbitrary `Laws`. -/
theorem stderrKeeps_of_corr (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (hE : StderrCorr mctx mref cctx cref) : StderrKeeps quietR := by
  intro w ⟨h, hrel, hq⟩
  obtain ⟨a, hr⟩ := runsTo_getStderr (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) w
  obtain ⟨b, h', hp, -, hrel'⟩ := hE w (stderrW w) h a hrel hr
  obtain ⟨e1, -, -, -, hqiff⟩ := getStderr_keeps (C := Std.HashMap Name Res) (S := Option (Name → MetaM Res)) hp
  subst e1
  exact ⟨⟨by rw [hrel'.1, hrel.1], by rw [hrel'.2.1, hrel.2.1], by rw [hrel'.2.2, hrel.2.2]⟩, h', hrel', hq⟩

end Bridge
end Tools.ShippingFGCircuitS3nBridge
