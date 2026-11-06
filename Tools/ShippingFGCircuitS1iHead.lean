import Tools.ShippingFGCircuitS1hQuote
set_option autoImplicit false
-- FG circuit pilot S1i, unit 1: `hhead` (`EnvFrame (coreHead X)`) from `CellPrem` plus two named IO facts; and the run-local form `HeadAt X w`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # S1i-1: what derives `hhead`, and what stays

`coreHead X` (the prefix of `synthesizeCombinationalCore`) is a straight-line `MetaM` program over: `IO.getEnv "SPARKLE_PROFILE"`, the profile logging `IO` action (stderr and `/tmp/sparkle-profile.log`, only when the variable is set),
`ST.Ref.get/set` of the synthesis side caches (`SideRef`) and of `sparkleSynthDepth`/`sparkleChildCache`, and a `throwError` (depth limit).
* `envFrame_coreHead` proves `EnvFrame (coreHead X)` from `CellPrem MkRefd mref cref` (the existing C.EN-4 premise bundle: `CellOK` of every ref touched, `ReadWorld mref`/`cref`) and the IO obligation `HeadIO` (`IO.getEnv "SPARKLE_PROFILE"`, and the profile logging action `profLogIO true`, itself a composition of several IO actions, not "two primitives").
* `HeadIO` is what the existing laws do not give: `Laws` (`frame`, `frameQ`, `same` for `FramedA.ioEnv`) speak of `cv`/`sv`/`dv`/quiet, not of `envAt cref`; `QuietStrength` adds `ReadsAt` only as a conjunct of the strengthened `L'`, and `frameQ_plus` excludes the class-D rows (`DRow.ioEnv`)
  by hypothesis (`¬ DRow p`).  So no supply path for the environment frame of `IO.getEnv n` and of the logging action has been found from `Laws`/`CellPrem`/`QuietStrength`/`ReadWorld` (no underivability is proved; docs §14, §16.3).  The log obligation as a universal law is NOT adopted (reviewer ruling, S1o): `FS.Stream.putStr` is an arbitrary `IO` callback (`setStderr`), so see `S1oHead` for the profile-disabled run form.
* `HeadAt X w` is the smallest form the endpoint theorem uses: only the run's own start world `w` (not all worlds): any `coreHead` run from `w` ends in a world with the same Core environment.  `headAt_of_frame` gives it from `EnvFrame (coreHead X)`.
Nothing here adds a law; `HeadIO` is a premise, not an axiom. -/
namespace Tools.ShippingFGCircuitS1iHead
open Lean Tools.ShippingEntryReadsLinked Tools.ShippingEnvSnapshot Sparkle.Compiler.Elab
open Tools.ShippingGen5EnvFrame3 (CellPrem CellOK)
open Tools.ShippingChildInv (SideRef)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingFGCircuitS1hFrame (envFrame_of_envFrameEnd getEnvFrame_of_readWorld)
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem ef_get_side (hc : ∀ {σ : Type} (r : IO.Ref σ), SideRef r → CellOK cref r) {σ : Type} {r : IO.Ref σ} (h : SideRef r) :
    EnvFrame (ST.Ref.get r : MetaM σ) mctx mref cctx cref :=
  envFrame_of_envFrameEnd (Tools.ShippingGen5EnvFrame.envFrameEnd_get (hc r h).1)

theorem ef_set_side (hc : ∀ {σ : Type} (r : IO.Ref σ), SideRef r → CellOK cref r) {σ : Type} {r : IO.Ref σ} (h : SideRef r) (v : σ) :
    EnvFrame (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref :=
  envFrame_of_envFrameEnd (Tools.ShippingGen5EnvFrame.envFrameEnd_set v (hc r h).2.1 (hc r h).2.2)

theorem ef_letFun {α β : Type} (v : β → MetaM α) (b : (β → MetaM α) → MetaM α)
    (hv : ∀ x, EnvFrame (v x) mctx mref cctx cref)
    (hb : ∀ jp : β → MetaM α, (∀ x, EnvFrame (jp x) mctx mref cctx cref) → EnvFrame (b jp) mctx mref cctx cref) :
    EnvFrame (letFun v b) mctx mref cctx cref := hb v hv

theorem ef_ite {α : Type} {c : Prop} [Decidable c] {a b : MetaM α} (ha : EnvFrame a mctx mref cctx cref) (hb : EnvFrame b mctx mref cctx cref) :
    EnvFrame (if c then a else b) mctx mref cctx cref := by
  split <;> assumption

theorem ef_let {α β : Type} (v : β) (b : β → MetaM α) (h : EnvFrame (b v) mctx mref cctx cref) :
    EnvFrame (letFun v b) mctx mref cctx cref := h

theorem ef_get_cell {σ : Type} {r : IO.Ref σ} (h : CellOK cref r) : EnvFrame (ST.Ref.get r : MetaM σ) mctx mref cctx cref :=
  envFrame_of_envFrameEnd (Tools.ShippingGen5EnvFrame.envFrameEnd_get h.1)

theorem ef_set_cell {σ : Type} {r : IO.Ref σ} (h : CellOK cref r) (v : σ) : EnvFrame (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref :=
  envFrame_of_envFrameEnd (Tools.ShippingGen5EnvFrame.envFrameEnd_set v h.2.1 h.2.2)

theorem ef_throw {α : Type} (msg : MessageData) (hc : Tools.ShippingStRefCorrespondence.ReadWorld cref)
    (hm : Tools.ShippingStRefCorrespondence.ReadWorld mref) : EnvFrame (throwError msg : MetaM α) mctx mref cctx cref :=
  envFrame_of_envFrameEnd (Tools.ShippingGen5EnvFrame3.envFrameEnd_throws (.err msg) hc hm)

/-- the profile logging action of `coreHead` (copied from the source) -/
def profLogIO (profile : Bool) (msg : String) : IO Unit :=
  if profile = true then do
    IO.eprintln msg
    Sparkle.Compiler.flushStderr
    let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
    h.putStrLn msg
    h.flush
  else pure ()

theorem ef_prof_false (msg : String) : EnvFrame (liftM (profLogIO false msg : IO Unit) : MetaM Unit) mctx mref cctx cref := by
  have : (profLogIO false msg : IO Unit) = pure () := by simp [profLogIO]
  rw [this]
  exact EnvFrame.pure ()

open Lean.Elab Lean.Elab.Tactic in
set_option hygiene false in
/-- dispatch on the head symbol of the monadic action (syntactic, no unfolding) -/
elab "ef_step" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let x := t.getAppArgs[1]!
  let fn := x.getAppFn
  if let .letE n ty v b _ := x then
    let vS ← Term.exprToSyntax v
    let bS ← Term.exprToSyntax (.lam n ty b .default)
    if ty.isArrow && ty.bindingBody!.getAppFn.constName? == some ``Lean.Meta.MetaM then
      evalTactic (← `(tactic| refine ef_letFun $vS $bS (fun _ => ?_) (fun _ _ => ?_)))
    else
      evalTactic (← `(tactic| refine ef_let $vS $bS ?_))
    return
  match fn.constName? with
  | some ``ite => evalTactic (← `(tactic| refine ef_ite ?_ ?_))
  | some ``Bind.bind => evalTactic (← `(tactic| refine EnvFrame.bind ?_ (fun _ => ?_)))
  | some ``Pure.pure => evalTactic (← `(tactic| exact EnvFrame.pure _))
  | some ``ST.Ref.get => evalTactic (← `(tactic| first | exact ef_get_side hSide (by constructor) | exact ef_get_cell hD | exact ef_get_cell hC | exact ef_get_cell hS))
  | some ``ST.Ref.set => evalTactic (← `(tactic| first | exact ef_set_side hSide (by constructor) _ | exact ef_set_cell hD _ | exact ef_set_cell hC _ | exact ef_set_cell hS _))
  | some ``Lean.throwError => evalTactic (← `(tactic| exact ef_throw _ hc hm))
  | _ => evalTactic (← `(tactic| apply_assumption))


/-- the two IO facts `coreHead` needs beyond `CellPrem`: neither `IO.getEnv "SPARKLE_PROFILE"` nor the profile logging action (`profLogIO true`) changes the Core environment (the `cref` cell) -/
structure HeadIO (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop where
  getEnv : EnvFrame (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref
  log : ∀ msg, EnvFrame (liftM (profLogIO true msg : IO Unit) : MetaM Unit) mctx mref cctx cref

set_option maxHeartbeats 1000000 in
/-- **`hhead` from `CellPrem` and `HeadIO`** -/
theorem envFrame_coreHead (X : Name) (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hio : HeadIO mctx mref cctx cref) : EnvFrame (coreHead X) mctx mref cctx cref := by
  obtain ⟨hC, hS, hD, hSide, -, hm, -, -, hc, -⟩ := hcell
  unfold coreHead
  refine EnvFrame.bind hio.getEnv (fun profile => ?_)
  repeat' ((try dsimp -zeta only); ef_step)
  cases hb : profile.isSome
  · exact ef_prof_false _
  · exact hio.log _

/-- the run-local form: any `coreHead` run from the start world `w` keeps the Core environment -/
def HeadAt (X : Name) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop :=
  ∀ (s : CoreSaved) (w1 : Void IO.RealWorld), RunsTo (coreHead X) mctx mref cctx cref w s w1 → envAt cref w1 = envAt cref w

theorem headAt_of_frame {X : Name} {w : Void IO.RealWorld} (h : EnvFrame (coreHead X) mctx mref cctx cref) :
    HeadAt X mctx mref cctx cref w := fun s w1 hh => h w s w1 hh

theorem headAt_of_cellPrem {X : Name} {w : Void IO.RealWorld} (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hio : HeadIO mctx mref cctx cref) : HeadAt X mctx mref cctx cref w :=
  headAt_of_frame (envFrame_coreHead X hcell hio)

theorem readsAt_after_headAt {X : Name} {w w1 : Void IO.RealWorld} {s : CoreSaved}
    (hhead : HeadAt X mctx mref cctx cref w) (hh : RunsTo (coreHead X) mctx mref cctx cref w s w1) :
    Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref w1 :=
  Tools.ShippingGen5Env.ReadsAt.of_envEq (hhead s w1 hh) (Tools.ShippingGen5Env.readsAt_self cref w)

/-- the root is a constant of the start environment, from `HeadAt` -/
theorem root_find_of_headAt {X : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hhead : HeadAt X mctx mref cctx cref w)
    (hc : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w') :
    ∃ ci : ConstantInfo, (envAt cref w).find? X = some ci := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, -, -, -⟩ := Tools.ShippingEntryReadsLinked.core_chain hc
  exact ⟨ci, Tools.ShippingGen5Env.ci_of_readsAt hget (readsAt_after_headAt hhead hh)⟩

/-- `machineDefinesLinked_of_head` with `HeadAt` -/
theorem machineDefinesLinked_of_headAt {X : Name} {shape : MachineShape} {ci₀ : ConstantInfo}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hhead : HeadAt X mctx mref cctx cref w)
    (hg : GetEnvFrame mctx mref cctx cref)
    (hc : (envAt cref w).find? X = some ci₀)
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (envAt cref w)) (userInliner (envAt cref w)) (structEnv (envAt cref w))) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate (envAt cref w)) (userInliner (envAt cref w)) (structEnv (envAt cref w))) (instancePredicate (envAt cref w)) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate (envAt cref w)) (userInliner (envAt cref w)) (structEnv (envAt cref w))) (structEnv (envAt cref w)) = some shape) :
    Tools.ShippingFGCircuitLinked.MachineDefinesLinked mctx mref cctx cref X shape w M D w' := by
  intro _ s w1 w2 w3 w4 envR ci h0 h1 h2 _
  have r1 := readsAt_after_headAt hhead h0
  have r2 : Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref w2 :=
    Tools.ShippingGen5Env.ReadsAt.of_frame (envFrame_getConstInfo X hg) h1 r1
  have r3 : Tools.ShippingGen5Env.ReadsAt (envAt cref w) cref w3 := Tools.ShippingGen5Env.ReadsAt.of_frame hg h2 r2
  have hci : ci = ci₀ := Option.some.inj ((Tools.ShippingGen5Env.ci_of_readsAt h1 r1).symm.trans hc)
  obtain ⟨-, hi, hu, hs⟩ := Tools.ShippingGen5Env.envR_of_readsAt h2 r2
  subst hci
  rw [hi, hu, hs]
  refine ⟨hg1, hg2, ?_⟩
  intro envR' w8 h3
  obtain ⟨-, -, -, hs'⟩ := Tools.ShippingGen5Env.envR_of_readsAt h3 r3
  rw [hs']
  exact hsh

section Finals
open Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote
open Tools.ShippingGen5Env (ReadsAt)

/-- `machineDefinesLinked_of_reader_head` with `HeadAt` -/
theorem machineDefinesLinked_of_reader_headAt {lvl : Lean.Expr → Nat} {X : Name} {ty val : Lean.Expr}
    {dd : Tools.ShippingMachineAuto.MachineData} {d : DefinitionVal}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hhead : HeadAt X mctx mref cctx cref w) (hg : GetEnvFrame mctx mref cctx cref)
    (hE : RootInEnv (envAt cref w) X ty val d) (hRead : RootReader lvl (envAt cref w) X dd)
    (hgates : EntryGates (envAt cref w) X) :
    MachineDefinesLinked mctx mref cctx cref X dd.shape w M D w' := by
  obtain ⟨hf, -, -, -⟩ := hE
  obtain ⟨E, hent, hsh, -⟩ := hRead
  have hgE := hgates E hent
  unfold Tools.ShippingGen5Acc.entry₀ at hent
  rw [hf] at hent
  simp only [Option.map_some, Option.some.injEq] at hent
  subst hent
  exact machineDefinesLinked_of_headAt hhead hg hf hgE.1 hgE.2 hsh

/-- **`counterLoop_final9`**: `counterLoop_final8` with `hhead : EnvFrame (coreHead X)` (all worlds) replaced by the run-local `HeadAt X w` (only the run's start world) -/
theorem counterLoop_final9 {ι : Type} (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAt ``counterLoop mctx mref cctx cref w)
    (hcell : ReadWorld cref)
    (hread : ReadsAt env₀ cref w)
    (hgatesB : entryGatesB env₀ ``counterLoop = true)
    (hquote : QuoteAt env₀ ``counterLoop counterLoopType counterLoopValue)
    (hreader : ReaderAt lvl env₀ ``counterLoop counterLoop.machineData) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p := by
  obtain ⟨raw, D₀, w1, hc, -⟩ := Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry hr
  obtain ⟨⟨d, hE⟩, hRead⟩ := rootEnv_of_lookup (quoteAt_of_readsAt hread hquote) (readerAt_of_readsAt hread hreader) (root_find_of_headAt hhead hc)
  exact counterLoop_final4D L lvl hstart hr
    (fun _ _ _ => machineDefinesLinked_of_reader_headAt (lvl := lvl) hhead (getEnvFrame_of_readWorld hcell) hE hRead
      (entryGatesB_sound (entryGatesB_of_readsAt hread hgatesB))) hRead hE

/-- **`counterLoop_final9C`**: the run-local head fact itself from `CellPrem` (which contains `ReadWorld cref`) and the two IO facts `HeadIO` -/
theorem counterLoop_final9C {ι : Type} (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (hio : HeadIO mctx mref cctx cref)
    (hread : ReadsAt env₀ cref w)
    (hgatesB : entryGatesB env₀ ``counterLoop = true)
    (hquote : QuoteAt env₀ ``counterLoop counterLoopType counterLoopValue)
    (hreader : ReaderAt lvl env₀ ``counterLoop counterLoop.machineData) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p :=
  counterLoop_final9 L lvl env₀ hstart hr (headAt_of_cellPrem hcell hio) hcell.2.2.2.2.2.2.2.2.1 hread hgatesB hquote hreader

end Finals

end Tools.ShippingFGCircuitS1iHead

#print axioms Tools.ShippingFGCircuitS1iHead.envFrame_coreHead
#print axioms Tools.ShippingFGCircuitS1iHead.headAt_of_cellPrem
#print axioms Tools.ShippingFGCircuitS1iHead.root_find_of_headAt
#print axioms Tools.ShippingFGCircuitS1iHead.machineDefinesLinked_of_headAt
#print axioms Tools.ShippingFGCircuitS1iHead.counterLoop_final9
#print axioms Tools.ShippingFGCircuitS1iHead.counterLoop_final9C
