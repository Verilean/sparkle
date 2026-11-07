import Tools.ShippingFGCircuitS3nBridge
set_option autoImplicit false
-- FG circuit pilot S3o: (1) KERNEL REFUTATIONS of two S3n bridge definitions (`EnvCorr` is incompatible with a successful real `getEnv`; the old `InitCorr` / `quietR` hold at EVERY world), (2) the corrected relation `RelE env` (the environment is an explicit ORACLE `env`, fixed for the whole execution and preserved through bind), the leaf hypotheses restated against it, `corrE_bind` / `bridge_smallE` re-proved, (3) what the corrected `InitCorrE` / `quietRE` constrain (only the oracle) and what they do not, (4) a MODEL-INTERNAL consistency fact (a toy semantics in which all the corrected hypotheses and a successful `getEnv` hold together).  Nothing here is adopted, nothing is TRUSTED, no hypothesis is supplied for the runtime, and the toy model says NOTHING about the real pilot.  No sorry/axiom/native_decide/law.  docs/FG-CIRCUIT-PILOT.md §65.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3oFix
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (readOf Res)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingStRefCorrespondence (ReadWorld SetGet SetFrame getW setW)
open Tools.ShippingHeapModel (Sig Heap Ref M Out getM setM bindM pureM hget hset)
open Tools.ShippingFGCircuitS3n
open Tools.ShippingFGCircuitS3nBridge (realSig MRunsTo Rel EnvCorr InitCorr quietR runsTo_set runsTo_getStderr)
open Tools.ShippingFGCircuitS3m (stderrW StderrKeeps)
open Sparkle.Compiler.Elab

/-! ## 1. refutations of the S3n definitions -/

/-- the lifted `IO.getEnv k` always runs (it is a `BaseIO`): from every world there is a successful real run -/
theorem runsTo_getEnv (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (k : String) (w : Void IO.RealWorld) :
    ∃ (a : Option String) (w' : Void IO.RealWorld), RunsTo (liftM (IO.getEnv k) : MetaM (Option String)) mctx mref cctx cref w a w' := by
  unfold RunsTo
  cases hg : (IO.getEnv k : BaseIO (Option String)) w with
  | mk a s =>
    refine ⟨a, s, ?_⟩
    change (match (IO.getEnv k : BaseIO (Option String)) w with | .mk a s => EST.Out.ok a s) = _
    rw [hg]

/-- a model heap related (in the OLD sense `Rel`) to `w`, with an arbitrary environment list -/
def heapOf (w : Void IO.RealWorld) (env : List (String × String)) : Heap realSig :=
  { cache := cv w, synth := sv w, depth := dv w, other := fun _ => 0, next := 0, reg := { stderr := [], env := env } }

theorem rel_heapOf (w : Void IO.RealWorld) (env : List (String × String)) : Rel (heapOf w env) w := ⟨rfl, rfl, rfl⟩

/-- **refutation of the old `EnvCorr`, with a given successful run**: `EnvCorr k` plus one successful real `getEnv k` run from `w` gives `False`.  The two heaps `hEmpty` (env = `[]`) and `hSome` (env = `[(k,"v")]`) are BOTH `Rel`-related to the same `w` (the old `Rel` ignores the environment); the old `Corr` quantifies over every related heap, so the same real return value `a` would equal both `none` and `some "v"`. -/
theorem envCorr_inconsistent_of_run (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (k : String) (w w' : Void IO.RealWorld) (a : Option String)
    (hr : RunsTo (liftM (IO.getEnv k) : MetaM (Option String)) mctx mref cctx cref w a w')
    (hC : EnvCorr mctx mref cctx cref k) : False := by
  obtain ⟨b1, h1, hp1, hab1, -⟩ := hC w w' (heapOf w []) a (rel_heapOf w []) hr
  obtain ⟨b2, h2, hp2, hab2, -⟩ := hC w w' (heapOf w [(k, "v")]) a (rel_heapOf w [(k, "v")]) hr
  obtain ⟨e1, -⟩ := getEnv_keeps (C := Std.HashMap Name Res) (S := Option (Name → MetaM Res)) k hp1
  obtain ⟨e2, -⟩ := getEnv_keeps (C := Std.HashMap Name Res) (S := Option (Name → MetaM Res)) k hp2
  have h1' : a = none := hab1.trans e1
  have h2' : a = some "v" := by
    refine hab2.trans (e2.trans ?_)
    simp [heapOf, DiagEnv.getEnv]
  rw [h1'] at h2'
  exact Option.noConfusion h2'

/-- **refutation of the old `EnvCorr`** (no run assumed: the run exists from every world, `runsTo_getEnv`): the old `EnvCorr k` is false for every Meta/Core context and every key, as soon as there is any world. -/
theorem envCorr_inconsistent (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (k : String) (w : Void IO.RealWorld)
    (hC : EnvCorr mctx mref cctx cref k) : False := by
  obtain ⟨a, w', hr⟩ := runsTo_getEnv mctx mref cctx cref k w
  exact envCorr_inconsistent_of_run mctx mref cctx cref k w w' a hr hC

/-- **the old `InitCorr` and `quietR` hold at EVERY world** (the heap with the cache/synth/depth read off `w` and an empty environment is related and quiet): `quietR` does not restrict the real process. -/
theorem oldInit_any_world (w : Void IO.RealWorld) : InitCorr w ∧ quietR w :=
  ⟨⟨heapOf w [], rel_heapOf w [], rfl⟩, ⟨heapOf w [], rel_heapOf w [], rfl⟩⟩

theorem oldQuietR_eq_true : quietR = fun _ => True := by
  funext w
  exact propext ⟨fun _ => trivial, fun _ => (oldInit_any_world w).2⟩

/-! ## 2. the corrected relation: an explicit environment ORACLE, fixed for the whole execution

A generic correspondence over an arbitrary "real run" relation `Run` on an arbitrary world type `W`: the oracle is a parameter of the RELATION `Rel`, hence of every leaf hypothesis AND of the end state of every leaf, so a bind composition cannot re-choose it. -/

section Generic
variable {C S W : Type}

/-- generic correspondence: if the real run `Run` succeeds from a world related to `h`, the model action `p` runs successfully from `h` with a `RA`-related value and a `Rel`-related end state -/
def GCorr {α β : Type} (Rel : Heap (sigOf C S) → W → Prop) (Run : W → α → W → Prop) (RA : α → β → Prop)
    (p : M (sigOf C S) β) : Prop :=
  ∀ (w w' : W) (h : Heap (sigOf C S)) (a : α), Rel h w → Run w a w' →
    ∃ (b : β) (h' : Heap (sigOf C S)), Tools.ShippingHeapModel.RunsTo p h b h' ∧ RA a b ∧ Rel h' w'

theorem gcorr_pure {α β : Type} {Rel : Heap (sigOf C S) → W → Prop} {Run : W → α → W → Prop} (RA : α → β → Prop)
    (a : α) (b : β) (hab : RA a b) (hdec : ∀ w c w', Run w c w' → c = a ∧ w' = w) :
    GCorr Rel Run RA (pureM b : M (sigOf C S) β) := by
  intro w w' h c hrel hr
  obtain ⟨hc, hw⟩ := hdec w c w' hr
  subst hc; subst hw
  exact ⟨b, h, rfl, hab, hrel⟩

theorem gcorr_bind {α β γ δ : Type} {Rel : Heap (sigOf C S) → W → Prop} {RA : α → β → Prop} {RB : γ → δ → Prop}
    {Rm : W → α → W → Prop} {Rf : α → W → γ → W → Prop} {Rb : W → γ → W → Prop}
    {p : M (sigOf C S) β} {g : β → M (sigOf C S) δ}
    (hdec : ∀ w c w'', Rb w c w'' → ∃ a w1, Rm w a w1 ∧ Rf a w1 c w'')
    (hm : GCorr Rel Rm RA p) (hf : ∀ a b, RA a b → GCorr Rel (Rf a) RB (g b)) :
    GCorr Rel Rb RB (bindM p g) := by
  intro w w'' h c hrel hr
  obtain ⟨a, w1, hm1, hf1⟩ := hdec w c w'' hr
  obtain ⟨b, h1, hp1, hab, hrel1⟩ := hm w w1 h a hrel hm1
  obtain ⟨d, h2, hp2, hcd, hrel2⟩ := hf a b hab w1 w'' h1 c hrel1 hf1
  refine ⟨d, h2, ?_, hcd, hrel2⟩
  unfold Tools.ShippingHeapModel.RunsTo at hp1 hp2 ⊢
  simp only [bindM, hp1]
  exact hp2
end Generic

/-- `lookup` of the oracle -/
def lookupEnv (env : List (String × String)) (k : String) : Option String :=
  (env.find? (fun p => p.1 == k)).map (fun p => p.2)

theorem getEnv_eq_lookup (d : DiagEnv) (k : String) : d.getEnv k = lookupEnv d.env k := rfl

/-- **the corrected relation**: the three tracked refs hold exactly the model's contents AND the model's environment component IS the oracle `env`.  The diagnostic output list and `mref` / `cref` / side refs are still unconstrained. -/
def RelE (env : List (String × String)) (h : Heap realSig) (w : Void IO.RealWorld) : Prop :=
  cv w = h.cache ∧ sv w = h.synth ∧ dv w = h.depth ∧ h.reg.env = env

/-- the corrected correspondence of a leaf, for the oracle `env` -/
def CorrE (env : List (String × String)) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) {α β : Type} (RA : α → β → Prop) (m : MetaM α) (p : M realSig β) : Prop :=
  ∀ (w w' : Void IO.RealWorld) (h : Heap realSig) (a : α),
    RelE env h w → RunsTo m mctx mref cctx cref w a w' → ∃ (b : β) (h' : Heap realSig), MRunsTo p h b h' ∧ RA a b ∧ RelE env h' w'

theorem corrE_eq_gcorr (env : List (String × String)) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) {α β : Type} (RA : α → β → Prop) (m : MetaM α)
    (p : M realSig β) :
    CorrE env mctx mref cctx cref RA m p = GCorr (RelE env) (fun w a w' => RunsTo m mctx mref cctx cref w a w') RA p := rfl

section HypsE
variable (env : List (String × String)) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
  (cref : ST.Ref IO.RealWorld Core.State)

/-- HYPOTHESIS: real `get` of `r` ~ model `get` of `rm`, same value (against the oracle `env`) -/
def GetCorrE {σ : Type} (r : IO.Ref σ) (rm : Ref realSig σ) : Prop :=
  CorrE env mctx mref cctx cref (· = ·) (ST.Ref.get r : MetaM σ) (getM rm)
/-- HYPOTHESIS: real `set` of `r` ~ model `set` of `rm` -/
def SetCorrE {σ : Type} (r : IO.Ref σ) (rm : Ref realSig σ) : Prop :=
  ∀ v : σ, CorrE env mctx mref cctx cref (· = ·) (ST.Ref.set r v : MetaM Unit) (setM rm v)
/-- HYPOTHESIS: real `IO.getStderr` ~ model `getStderr` (the stream value is not compared) -/
def StderrCorrE : Prop :=
  CorrE env mctx mref cctx cref (fun _ _ => True) (liftM IO.getStderr : MetaM IO.FS.Stream)
    (getStderrM (C := Std.HashMap Name Res) (S := Option (Name → MetaM Res)))
/-- HYPOTHESIS: the real `IO.getEnv k`, run from a world related to the oracle `env`, returns exactly the lookup of `k` in `env` (this is the ONLY place where the oracle is tied to the real process) -/
def EnvCorrE (k : String) : Prop :=
  CorrE env mctx mref cctx cref (· = ·) (liftM (IO.getEnv k) : MetaM (Option String))
    (getEnvM (C := Std.HashMap Name Res) (S := Option (Name → MetaM Res)) k)
end HypsE

/-- corrected initial correspondence: the start world is related to a model heap carrying the oracle, in which the concrete quiet holds -/
def InitCorrE (env : List (String × String)) (w0 : Void IO.RealWorld) : Prop := ∃ h0 : Heap realSig, RelE env h0 w0 ∧ quietM h0

/-- the quiet induced on worlds by `RelE env` and the model's quiet -/
def quietRE (env : List (String × String)) (w : Void IO.RealWorld) : Prop := ∃ h : Heap realSig, RelE env h w ∧ quietM h

section BridgeE
variable {env : List (String × String)} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
  {cref : ST.Ref IO.RealWorld Core.State}

theorem runsTo_pure {α : Type} (a : α) {w w' : Void IO.RealWorld} {c : α}
    (hr : RunsTo (pure a : MetaM α) mctx mref cctx cref w c w') : c = a ∧ w' = w := by
  unfold RunsTo at hr
  cases hr
  exact ⟨rfl, rfl⟩

theorem corrE_pure {α β : Type} (RA : α → β → Prop) (a : α) (b : β) (hab : RA a b) :
    CorrE env mctx mref cctx cref RA (pure a : MetaM α) (pureM b) :=
  gcorr_pure (Rel := RelE env) RA a b hab (fun _ _ _ hr => runsTo_pure a hr)

/-- **bind composition for the corrected relation**: the SAME oracle `env` is a fixed parameter of the hypothesis, of the continuation's hypothesis and of the conclusion; it is not re-chosen at the leaves. -/
theorem corrE_bind {α β γ δ : Type} {RA : α → β → Prop} {RB : γ → δ → Prop} {m : MetaM α} {p : M realSig β}
    {f : α → MetaM γ} {g : β → M realSig δ}
    (hm : CorrE env mctx mref cctx cref RA m p) (hf : ∀ a b, RA a b → CorrE env mctx mref cctx cref RB (f a) (g b)) :
    CorrE env mctx mref cctx cref RB (m >>= f) (bindM p g) :=
  gcorr_bind (Rel := RelE env) (Rm := fun w a w' => RunsTo m mctx mref cctx cref w a w')
    (Rf := fun a w c w'' => RunsTo (f a) mctx mref cctx cref w c w'')
    (Rb := fun w c w'' => RunsTo (m >>= f) mctx mref cctx cref w c w'')
    (fun _ _ _ hr => Tools.ShippingEntrySoundness.RunsTo.bind hr) hm hf

theorem getCorrE_of_readWorld {σ : Type} (r : IO.Ref σ) (rm : Ref realSig σ) (hRW : ReadWorld r)
    (hv : ∀ w h, RelE env h w → readOf r w = hget rm h) : GetCorrE env mctx mref cctx cref r rm := by
  intro w w' h a hrel hr
  have hg := Tools.ShippingFGCircuitS3jStart.runsTo_get r hr
  obtain ⟨ha, hw⟩ := hg
  have hw' : w' = w := by rw [hw]; exact hRW w
  subst hw'
  exact ⟨a, h, by rw [ha, hv _ _ hrel]; rfl, by rw [ha, hv _ _ hrel], hrel⟩

theorem getCorrE_depth (hRW : ReadWorld sparkleSynthDepth) : GetCorrE env mctx mref cctx cref sparkleSynthDepth rDepth :=
  getCorrE_of_readWorld _ _ hRW (fun _ _ hrel => hrel.2.2.1)

theorem setCorrE_depth (hSG : SetGet sparkleSynthDepth) (hF1 : SetFrame sparkleSynthDepth sparkleChildCache)
    (hF2 : SetFrame sparkleSynthDepth sparkleChildSynth) (hne1 : sparkleSynthDepth.ref ≠ sparkleChildCache.ref)
    (hne2 : sparkleSynthDepth.ref ≠ sparkleChildSynth.ref) :
    SetCorrE env mctx mref cctx cref sparkleSynthDepth rDepth := by
  intro v w w' h u hrel hr
  have hw := runsTo_set _ _ hr
  subst hw
  refine ⟨(), hset rDepth v h, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact (hF1 hne1 v w).trans hrel.1
  · exact (hF2 hne2 v w).trans hrel.2.1
  · exact hSG v w
  · exact hrel.2.2.2

/-- a corrected `getEnv` hypothesis pins the real return value to the oracle's lookup -/
theorem envCorrE_returns {k : String} (hE : EnvCorrE env mctx mref cctx cref k) {w w' : Void IO.RealWorld} {h : Heap realSig}
    {a : Option String} (hrel : RelE env h w)
    (hr : RunsTo (liftM (IO.getEnv k) : MetaM (Option String)) mctx mref cctx cref w a w') : a = lookupEnv env k := by
  obtain ⟨b, h', hp, hab, -⟩ := hE w w' h a hrel hr
  obtain ⟨e1, -⟩ := getEnv_keeps (C := Std.HashMap Name Res) (S := Option (Name → MetaM Res)) k hp
  rw [hab, e1, getEnv_eq_lookup, hrel.2.2.2]

/-! ### the small composition, restated against the oracle -/

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

theorem bridge_smallE (hG : GetCorrE env mctx mref cctx cref sparkleSynthDepth rDepth)
    (hS : SetCorrE env mctx mref cctx cref sparkleSynthDepth rDepth) (hE : StderrCorrE env mctx mref cctx cref) :
    CorrE env mctx mref cctx cref (· = ·) realProg modelProg := by
  unfold realProg modelProg
  refine corrE_bind hG fun d b hdb => ?_
  subst hdb
  refine corrE_bind (hS (d + 1)) fun _ _ _ => ?_
  refine corrE_bind hE fun _ _ _ => ?_
  exact corrE_pure _ d d rfl

theorem modelProg_specE {h h' : Heap realSig} {a : Nat} (hr : MRunsTo modelProg h a h') :
    a = h.depth ∧ h'.depth = h.depth + 1 ∧ h'.cache = h.cache ∧ h'.synth = h.synth ∧ h'.reg.env = h.reg.env := by
  change Out.ok h.depth (hset rDepth (h.depth + 1) h) = Out.ok a h' at hr
  injection hr with h1 h2
  subst h1; subst h2
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem real_small_consequenceE (hG : GetCorrE env mctx mref cctx cref sparkleSynthDepth rDepth)
    (hS : SetCorrE env mctx mref cctx cref sparkleSynthDepth rDepth) (hE : StderrCorrE env mctx mref cctx cref)
    {w w' : Void IO.RealWorld} {h : Heap realSig} {a : Nat} (hrel : RelE env h w)
    (hr : RunsTo realProg mctx mref cctx cref w a w') :
    a = dv w ∧ dv w' = dv w + 1 ∧ cv w' = cv w ∧ sv w' = sv w := by
  obtain ⟨b, h', hp, hab, hrel'⟩ := bridge_smallE hG hS hE w w' h a hrel hr
  obtain ⟨e1, e2, e3, e4, -⟩ := modelProg_specE hp
  subst hab
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrel.2.2.1]; exact e1
  · rw [hrel'.2.2.1, hrel.2.2.1]; exact e2
  · rw [hrel'.1, hrel.1]; exact e3
  · rw [hrel'.2.1, hrel.2.1]; exact e4

/-! ### the SAME oracle through a bind: two reads of one key cannot disagree -/

def realEnvProg (k : String) : MetaM (Option String × Option String) :=
  (liftM (IO.getEnv k) : MetaM (Option String)) >>= fun a =>
  (liftM (IO.getEnv k) : MetaM (Option String)) >>= fun b =>
  pure (a, b)

def modelEnvProg (k : String) : M realSig (Option String × Option String) :=
  bindM (getEnvM k) fun a =>
  bindM (getEnvM k) fun b =>
  pureM (a, b)

theorem bridge_env_twice (k : String) (hE : EnvCorrE env mctx mref cctx cref k) :
    CorrE env mctx mref cctx cref (· = ·) (realEnvProg k) (modelEnvProg k) := by
  unfold realEnvProg modelEnvProg
  refine corrE_bind hE fun a b hab => ?_
  subst hab
  refine corrE_bind hE fun b b' hbb => ?_
  subst hbb
  exact corrE_pure _ (a, b) (a, b) rfl

/-- a successful real run of the two-read program returns the oracle's lookup twice -/
theorem real_env_twice (k : String) (hE : EnvCorrE env mctx mref cctx cref k)
    {w w' : Void IO.RealWorld} {h : Heap realSig} {a b : Option String} (hrel : RelE env h w)
    (hr : RunsTo (realEnvProg k) mctx mref cctx cref w (a, b) w') : a = lookupEnv env k ∧ b = lookupEnv env k := by
  obtain ⟨c, h', hp, hab, -⟩ := bridge_env_twice k hE w w' h (a, b) hrel hr
  change Out.ok (h.reg.getEnv k, h.reg.getEnv k) h = Out.ok c h' at hp
  injection hp with h1 _
  subst h1
  injection hab with ha hb
  rw [getEnv_eq_lookup, hrel.2.2.2] at ha hb
  exact ⟨ha, hb⟩

/-- **control**: under the corrected relation the oracle is determined by the world's relation — two heaps with different environment components are NOT both `RelE`-related to the same world for the same oracle -/
theorem relE_env_unique {env : List (String × String)} {h h' : Heap realSig} {w : Void IO.RealWorld}
    (hr : RelE env h w) (hr' : RelE env h' w) : h.reg.env = h'.reg.env := hr.2.2.2.trans hr'.2.2.2.symm

theorem relE_not_both (k : String) (env : List (String × String)) (w : Void IO.RealWorld) :
    ¬ (RelE env (heapOf w []) w ∧ RelE env (heapOf w [(k, "v")]) w) := by
  rintro ⟨h1, h2⟩
  have := relE_env_unique h1 h2
  exact List.noConfusion this

/-- **control at the observation level**: a corrected `EnvCorrE env k` whose oracle has `k` unset cannot coexist with a real run observing `some v` from a world related to the oracle — the oracle commits to ONE value -/
theorem envCorrE_observation_committed {k : String} (hE : EnvCorrE env mctx mref cctx cref k)
    (hnone : lookupEnv env k = none) {w w' : Void IO.RealWorld} {h : Heap realSig} {v : String}
    (hrel : RelE env h w) (hr : RunsTo (liftM (IO.getEnv k) : MetaM (Option String)) mctx mref cctx cref w (some v) w') : False := by
  have := envCorrE_returns hE hrel hr
  rw [hnone] at this
  exact Option.noConfusion this

/-! ### what the corrected `InitCorrE` / `quietRE` constrain: ONLY the oracle -/

theorem initCorrE_iff (env : List (String × String)) (w0 : Void IO.RealWorld) :
    InitCorrE env w0 ↔ lookupEnv env "SPARKLE_DEBUG" = none := by
  constructor
  · rintro ⟨h0, hrel, hq⟩
    have hq' : lookupEnv h0.reg.env "SPARKLE_DEBUG" = none := hq
    rw [hrel.2.2.2] at hq'
    exact hq'
  · intro h
    exact ⟨{ cache := cv w0, synth := sv w0, depth := dv w0, other := fun _ => 0, next := 0, reg := { stderr := [], env := env } },
      ⟨rfl, rfl, rfl, rfl⟩, h⟩

theorem quietRE_iff (env : List (String × String)) (w : Void IO.RealWorld) :
    quietRE env w ↔ lookupEnv env "SPARKLE_DEBUG" = none := initCorrE_iff env w

/-- the corrected quiet does not depend on the world at all: any two worlds satisfy it together or not at all -/
theorem quietRE_world_independent (env : List (String × String)) (w w' : Void IO.RealWorld) : quietRE env w ↔ quietRE env w' :=
  (quietRE_iff env w).trans (quietRE_iff env w').symm

/-- the corrected quiet is a genuine, non-constant restriction on the ORACLE: it fails for an oracle that sets `SPARKLE_DEBUG` -/
theorem quietRE_oracle_nonconst (w : Void IO.RealWorld) :
    quietRE [] w ∧ ¬ quietRE [("SPARKLE_DEBUG", "1")] w := by
  refine ⟨(quietRE_iff [] w).2 rfl, fun h => ?_⟩
  have := (quietRE_iff [("SPARKLE_DEBUG", "1")] w).1 h
  have h2 : lookupEnv [("SPARKLE_DEBUG", "1")] "SPARKLE_DEBUG" = some "1" := by decide
  rw [h2] at this
  exact Option.noConfusion this

/-- the corrected `StderrCorrE` feeds `StderrKeeps (quietRE env)` (the `diag`-at-`ioGetStderr` instance only; NOT `Laws.O.diag`) -/
theorem stderrKeeps_of_corrE (hE : StderrCorrE env mctx mref cctx cref) : StderrKeeps (quietRE env) := by
  intro w ⟨h, hrel, hq⟩
  obtain ⟨a, hr⟩ := runsTo_getStderr (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) w
  obtain ⟨b, h', hp, -, hrel'⟩ := hE w (stderrW w) h a hrel hr
  obtain ⟨e1, -, -, -, hqiff⟩ := getStderr_keeps (C := Std.HashMap Name Res) (S := Option (Name → MetaM Res)) hp
  subst e1
  exact ⟨⟨by rw [hrel'.1, hrel.1], by rw [hrel'.2.1, hrel.2.1], by rw [hrel'.2.2.1, hrel.2.2.1]⟩, h', hrel', hq⟩

end BridgeE

/-! ## 4. a MODEL-INTERNAL consistency fact

A toy "real" semantics (NOT Lean's runtime): a world record, hand-written run relations for the four leaves, and the corrected `GCorr` over it.  All the corrected leaf hypotheses, the initial correspondence and a SUCCESSFUL `getEnv` hold together in it, and the bind composition goes through the generic `gcorr_bind`.  This shows the SHAPE of the corrected hypotheses is satisfiable; it says nothing about the real pilot. -/

namespace Toy

structure TW where
  cache : List Nat
  synth : Option Nat
  depth : Nat
  penv : List (String × String)

def RelT (env : List (String × String)) (h : Heap exSig) (w : TW) : Prop :=
  h.cache = w.cache ∧ h.synth = w.synth ∧ h.depth = w.depth ∧ h.reg.env = env ∧ w.penv = env

def tGetDepth : TW → Nat → TW → Prop := fun w a w' => a = w.depth ∧ w' = w
def tSetDepth (v : Nat) : TW → Unit → TW → Prop := fun w _ w' => w' = { w with depth := v }
def tStderr : TW → Unit → TW → Prop := fun w _ w' => w' = w
def tGetEnv (k : String) : TW → Option String → TW → Prop := fun w a w' => a = lookupEnv w.penv k ∧ w' = w
def tPure {α : Type} (a : α) : TW → α → TW → Prop := fun w c w' => c = a ∧ w' = w
def tBind {α γ : Type} (R1 : TW → α → TW → Prop) (R2 : α → TW → γ → TW → Prop) : TW → γ → TW → Prop :=
  fun w c w'' => ∃ a w1, R1 w a w1 ∧ R2 a w1 c w''

abbrev dRef : Ref exSig Nat := Ref.depth

theorem gc_get (env : List (String × String)) : GCorr (RelT env) tGetDepth (· = ·) (getM dRef) := by
  intro w w' h a hrel ⟨ha, hw⟩
  subst hw
  exact ⟨h.depth, h, rfl, ha.trans hrel.2.2.1.symm, hrel⟩

theorem gc_set (env : List (String × String)) (v : Nat) : GCorr (RelT env) (tSetDepth v) (· = ·) (setM dRef v) := by
  intro w w' h a hrel hw
  subst hw
  exact ⟨(), hset dRef v h, rfl, rfl, hrel.1, hrel.2.1, rfl, hrel.2.2.2.1, hrel.2.2.2.2⟩

theorem gc_stderr (env : List (String × String)) : GCorr (RelT env) tStderr (fun _ _ => True) (getStderrM (C := List Nat) (S := Option Nat)) := by
  intro w w' h a hrel hw
  subst hw
  exact ⟨(), h, rfl, trivial, hrel⟩

theorem gc_env (env : List (String × String)) (k : String) :
    GCorr (RelT env) (tGetEnv k) (· = ·) (getEnvM (C := List Nat) (S := Option Nat) k) := by
  intro w w' h a hrel ⟨ha, hw⟩
  subst hw
  refine ⟨h.reg.getEnv k, h, rfl, ?_, hrel⟩
  rw [ha, hrel.2.2.2.2, ← hrel.2.2.2.1]
  rfl

/-- the toy program: get depth; set depth+1; getStderr; getEnv "HOME"; return (depth, env value) -/
def toyModel : M exSig (Nat × Option String) :=
  bindM (getM dRef) fun d =>
  bindM (setM dRef (d + 1)) fun _ =>
  bindM (getStderrM (C := List Nat) (S := Option Nat)) fun _ =>
  bindM (getEnvM (C := List Nat) (S := Option Nat) "HOME") fun e =>
  pureM (d, e)

def toyRun : TW → (Nat × Option String) → TW → Prop :=
  tBind tGetDepth fun d => tBind (tSetDepth (d + 1)) fun _ => tBind tStderr fun _ => tBind (tGetEnv "HOME") fun e => tPure (d, e)

/-- the same oracle goes through the composed toy program (bind) -/
theorem gc_prog (env : List (String × String)) : GCorr (RelT env) toyRun (· = ·) toyModel := by
  unfold toyRun toyModel
  refine gcorr_bind (fun _ _ _ h => h) (gc_get env) fun d b hdb => ?_
  subst hdb
  refine gcorr_bind (fun _ _ _ h => h) (gc_set env (d + 1)) fun _ _ _ => ?_
  refine gcorr_bind (fun _ _ _ h => h) (gc_stderr env) fun _ _ _ => ?_
  refine gcorr_bind (fun _ _ _ h => h) (gc_env env "HOME") fun e e' hee => ?_
  subst hee
  exact gcorr_pure _ (d, e) (d, e) rfl (fun _ _ _ h => h)

def w0 : TW := { cache := [10], synth := some 7, depth := 0, penv := [("HOME", "/root")] }

/-- **simultaneous satisfaction in the model**: one oracle, one start world, one model heap with the concrete quiet; the four corrected leaf correspondences (for every key / every written value), the corrected correspondence of the composed program, the initial correspondence, AND a successful `getEnv "HOME"` run returning `some "/root"` — all together. -/
theorem simultaneous_sat :
    ∃ (env : List (String × String)) (w : TW) (h0 : Heap exSig),
      RelT env h0 w ∧ quietM h0 ∧
      GCorr (RelT env) tGetDepth (· = ·) (getM dRef) ∧
      (∀ v, GCorr (RelT env) (tSetDepth v) (· = ·) (setM dRef v)) ∧
      GCorr (RelT env) tStderr (fun _ _ => True) (getStderrM (C := List Nat) (S := Option Nat)) ∧
      (∀ k, GCorr (RelT env) (tGetEnv k) (· = ·) (getEnvM (C := List Nat) (S := Option Nat) k)) ∧
      GCorr (RelT env) toyRun (· = ·) toyModel ∧
      (∃ (a : Option String) (w' : TW), tGetEnv "HOME" w a w' ∧ a = some "/root") :=
  ⟨[("HOME", "/root")], w0, s0, ⟨rfl, rfl, rfl, rfl, rfl⟩, quiet_s0,
    gc_get _, gc_set _, gc_stderr _, gc_env _, gc_prog _,
    some "/root", w0, ⟨by decide, rfl⟩, rfl⟩

end Toy
end Tools.ShippingFGCircuitS3oFix
