import Tools.ShippingFGCircuitS1hGates
set_option autoImplicit false
-- FG circuit pilot S1h, unit 3: `QuoteAt` / `ReaderAt` / gates of the start environment from the same facts of ONE checked environment `env₀` and `ReadsAt env₀ cref w`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # S1h-3: reducing the start-environment facts to a checked environment

The reader outputs (`dataOfAt`, `machineShape?`) call `partial` helpers: the kernel cannot evaluate them, and an `Environment` is not a closed term.  What the kernel CAN do is show that these facts depend on the environment only through
`find? X`, `instancePredicate`, `userInliner` and `structEnv` (the entry constant `entry₀` is a function of those, and `machineShape?` / `dataOfAt` of the entry constant and `structEnv`).
`ReadsAt env₀ cref w` (the start world reads the environment `env₀`: its constants are `env₀`'s and its three derived arguments are equal) therefore transfers `entryGatesB`, `QuoteAt` and `ReaderAt` from `env₀` to the start environment,
provided the start environment has the root (`find? X = some _`, supplied by the run: `root_find_of_head`), or has no root (then the gates hold trivially, `QuoteAt` and `ReaderAt` are vacuous).
The evaluation facts (`QuoteAt env₀`, `ReaderAt env₀`, `entryGatesB env₀`) are about ONE environment and are checked by running the functions in `MetaM` on this build's environment (`Tests/Gen5/FGCircuitPilotCheck7.lean`); they stay premises of the kernel theorem.
What is reduced: three statements about an arbitrary run's start environment become (1) the same three statements about `env₀` and (2) the environment identification `ReadsAt env₀ cref w` (DG-ENV C0). -/
namespace Tools.ShippingFGCircuitS1hQuote
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1hFrame Tools.ShippingFGCircuitS1hGates
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt coreHead core_chain)
open Tools.ShippingStRefCorrespondence (ReadWorld)



open Tools.ShippingGen5Env (ReadsAt)

/-- the entry constant of the start environment is `env₀`'s, when the start environment has the root -/
theorem entry₀_of_readsAt {e env₀ : Environment} {X : Name} {ci : ConstantInfo}
    (h : ∀ X ci, e.find? X = some ci → env₀.find? X = some ci) (hi : instancePredicate e = instancePredicate env₀)
    (hu : userInliner e = userInliner env₀) (hs : structEnv e = structEnv env₀) (hf : e.find? X = some ci) :
    Tools.ShippingGen5Acc.entry₀ e X = Tools.ShippingGen5Acc.entry₀ env₀ X := by
  unfold Tools.ShippingGen5Acc.entry₀
  rw [hf, h X ci hf, hi, hu, hs]

theorem entryGatesB_of_readsAt {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {env₀ : Environment} {X : Name}
    (hr : ReadsAt env₀ cref w) (hg : entryGatesB env₀ X = true) : entryGatesB (envAt cref w) X = true := by
  obtain ⟨h, hi, hu, hs⟩ := hr
  cases hf : (envAt cref w).find? X with
  | none =>
    unfold entryGatesB Tools.ShippingGen5Acc.entry₀
    rw [hf]; rfl
  | some ci =>
    have he := entry₀_of_readsAt (X := X) h hi hu hs hf
    unfold entryGatesB at hg ⊢
    rw [he, hi]; exact hg

theorem quoteAt_of_readsAt {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {env₀ : Environment} {X : Name} {ty val : Lean.Expr}
    (hr : ReadsAt env₀ cref w) (hq : QuoteAt env₀ X ty val) : QuoteAt (envAt cref w) X ty val :=
  fun ci hci => hq ci (hr.1 X ci hci)

theorem readerAt_of_readsAt {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {env₀ : Environment} {X : Name}
    {lvl : Lean.Expr → Nat} {dd : Tools.ShippingMachineAuto.MachineData}
    (hr : ReadsAt env₀ cref w) (hrd : ReaderAt lvl env₀ X dd) : ReaderAt lvl (envAt cref w) X dd := by
  intro E hE
  obtain ⟨h, hi, hu, hs⟩ := hr
  have hf : ∃ ci, (envAt cref w).find? X = some ci := by
    unfold Tools.ShippingGen5Acc.entry₀ at hE
    cases hf : (envAt cref w).find? X with
    | none => rw [hf] at hE; simp at hE
    | some ci => exact ⟨ci, rfl⟩
  obtain ⟨ci, hf⟩ := hf
  have he := entry₀_of_readsAt (X := X) h hi hu hs hf
  rw [he] at hE
  rw [hs]
  exact hrd E hE

/-- **`counterLoop_final8`**: `QuoteAt` / `ReaderAt` / gates are premises about a checked environment `env₀`, tied to the start world by `ReadsAt env₀ cref w` -/
theorem counterLoop_final8 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hhead : Tools.ShippingEnvSnapshot.EnvFrame (coreHead ``counterLoop) mctx mref cctx cref)
    (hcell : Tools.ShippingStRefCorrespondence.ReadWorld cref)
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
  obtain ⟨⟨d, hE⟩, hRead⟩ := rootEnv_of_lookup (quoteAt_of_readsAt hread hquote) (readerAt_of_readsAt hread hreader) (root_find_of_head hhead hc)
  exact counterLoop_final7 L lvl hstart hr hhead hcell (entryGatesB_of_readsAt hread hgatesB) hRead hE

end Tools.ShippingFGCircuitS1hQuote

#print axioms Tools.ShippingFGCircuitS1hQuote.entryGatesB_of_readsAt
#print axioms Tools.ShippingFGCircuitS1hQuote.quoteAt_of_readsAt
#print axioms Tools.ShippingFGCircuitS1hQuote.readerAt_of_readsAt
#print axioms Tools.ShippingFGCircuitS1hQuote.counterLoop_final8
