import Tools.ShippingFGCircuitS1hFrame
set_option autoImplicit false
-- FG circuit pilot S1h, unit 2: `EntryGates` (h_A_P06, env level) as a small pure checker `entryGatesB : Bool` with soundness (and completeness). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # S1h-2: `hgates` as a checker

`entryGatesB env X` is a Bool function of the environment: it looks up the entry constant `entry₀ env X` and tests the two refusal facts the machine boundary needs (`certifiedShape? = none`, `mixedCertifiedShape? = none`).
`entryGatesB_sound`: `entryGatesB env X = true → EntryGates env X`; `entryGatesB_iff` shows it is exactly `EntryGates` (no strengthening, no weakening).
Nothing semantic is renamed into the Bool: it is the very two `Option.isNone` tests of `EntryGates`.  An `Environment` is a runtime object, not a closed kernel term, so `decide` cannot evaluate it; the evaluation `entryGatesB env X = true` for the four roots
is done by running the (compiled) function on this build's environment (`Tests/Gen5/FGCircuitPilotCheck7.lean`, a value of ONE environment, not a kernel fact about an arbitrary run's start environment).  The step from the checker to the premise of the final theorem is the kernel-checked `entryGatesB_sound`. -/
namespace Tools.ShippingFGCircuitS1hGates
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1hFrame
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt coreHead core_chain)
open Tools.ShippingStRefCorrespondence (ReadWorld)


/-- the two refusal facts of the entry constant, as a Bool; a missing constant passes (as in `EntryGates`) -/
def entryGatesB (env : Environment) (X : Name) : Bool :=
  match Tools.ShippingGen5Acc.entry₀ env X with
  | none => true
  | some E => (certifiedShape? false [] E).isNone && (mixedCertifiedShape? false [] E (instancePredicate env)).isNone

/-- **soundness**: the checker returning `true` gives `EntryGates` -/
theorem entryGatesB_sound {env : Environment} {X : Name} (h : entryGatesB env X = true) : EntryGates env X := by
  intro E hE
  unfold entryGatesB at h
  rw [hE] at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact h

/-- the converse: the checker is exactly `EntryGates` -/
theorem entryGatesB_complete {env : Environment} {X : Name} (h : EntryGates env X) : entryGatesB env X = true := by
  unfold entryGatesB
  cases hE : Tools.ShippingGen5Acc.entry₀ env X with
  | none => rfl
  | some E =>
    obtain ⟨h1, h2⟩ := h E hE
    simp [h1, h2]

theorem entryGatesB_iff {env : Environment} {X : Name} : entryGatesB env X = true ↔ EntryGates env X :=
  ⟨entryGatesB_sound, entryGatesB_complete⟩

/-- a failing checker is a witness against the premise: if `entryGatesB` is `false` then `EntryGates` fails -/
theorem not_entryGates_of_false {env : Environment} {X : Name} (h : entryGatesB env X = false) : ¬ EntryGates env X :=
  fun hg => by have := entryGatesB_complete hg; rw [h] at this; exact Bool.false_ne_true this

/-- **`counterLoop_final7`**: `counterLoop_final6` with `hgates` replaced by the checker's result `entryGatesB (envAt cref w) counterLoop = true` -/
theorem counterLoop_final7 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    {d : DefinitionVal}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hhead : Tools.ShippingEnvSnapshot.EnvFrame (coreHead ``counterLoop) mctx mref cctx cref)
    (hcell : Tools.ShippingStRefCorrespondence.ReadWorld cref)
    (hgatesB : entryGatesB (envAt cref w) ``counterLoop = true)
    (hRead : RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData)
    (hE : RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p :=
  counterLoop_final6 L lvl hstart hr hhead hcell (entryGatesB_sound hgatesB) hRead hE

end Tools.ShippingFGCircuitS1hGates

#print axioms Tools.ShippingFGCircuitS1hGates.entryGatesB_sound
#print axioms Tools.ShippingFGCircuitS1hGates.entryGatesB_iff
#print axioms Tools.ShippingFGCircuitS1hGates.counterLoop_final7
