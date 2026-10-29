import Tools.ShippingMachineOutcomeA
import Tools.ShippingEntryReadsLinked
set_option autoImplicit false
-- NOT BUILT: written without running Lean. No sorry / axiom / native_decide.

/-! # DG-RUNREADS (scripts/gen5/DG_RUNREADS_FREEZE.md, par/gen5-t2 b8f9cd7a, scoped approved; notes ce3f7e2c)

`RunReadsAt`: the reads of ONE core run on the run's own linked world chain (`core_chain`), with the machine run's
worlds `w5 w6` and the translator environment `envR` exposed. RR1 `coreHead_jqcA`: the head establishes
`JQC (D+1)`. RR2 `fromConst_machine_linkA`: the machine branch of the body split on linked worlds WITHOUT `htr` /
`hchild` (no `JQC` after the machine run). RR3 `runReads_of_run`: the producer, from `O`, `hA`, `JQ`/cache at `w`,
the core run, `MachineDefines` and `MachineClosesAtA` only; `closes` excludes `none` at `w5`.

Not claimed: `ClosingRun`, `GeneratedAt`, `InvAt` at `w5`, `envR = envR'`, `ci ∈ envR`, the FG-run peel, fallback
runs. Not M5 or FG completion. -/
namespace Tools.ShippingGen5RunReads
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Sparkle.IR.Builder
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC
open Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA
open Tools.ShippingChildRunAMain
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids (MachineClosesAtA)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The reads of ONE core run `w → w'`, on the run's own linked world chain (DGEN §3). -/
structure RunReadsAt (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (X : Name) (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module)
    (D : Sparkle.IR.AST.Design) (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (shape : MachineShape)
    (w5 w6 : Void IO.RealWorld) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  chain : ∃ (s : Tools.ShippingEntryReadsLinked.CoreSaved) (w1 w2 w3 w4 wl : Void IO.RealWorld),
    s.profile = b ∧
    RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1 ∧
    RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 ∧
    RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire envR e h t n) (profLogIO b) X shape)
      mctx mref cctx cref w5 (some (raw, D)) w6 ∧
    RunsTo (show MetaM Unit from profLogIO b
      s!"[profile] synthesizeCombinational {X} machine certified front end") mctx mref cctx cref w6 () wl ∧
    RunsTo (sparkleSubModuleCache.modify (·.insert X (raw, D)) : MetaM Unit) mctx mref cctx cref wl () w4 ∧
    RunsTo (Tools.ShippingMachineOutcomeA3.coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg)
      mctx mref cctx cref w4 () w'
  gates : certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (instancePredicate envR) = none
  shapeEq : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape

/-- **(RR1)** The core head establishes `JQC (D+1)` at its end world (the peel of `core_reads_linkA`,
ShippingMachineOutcomeA.lean, on `coreHead`). -/
theorem coreHead_jqcA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {X : Name} {D : Nat}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1) :
    JQC O (D + 1) w1 := by
  have h := hh
  unfold Tools.ShippingEntryReadsLinked.coreHead at h
  by_cases h0 : D = 0
  · subst h0
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ 0) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag O hA (stableA_JQ _ 0)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet O hA (stableA_JQ _ 0)) hw s3
    have hdD : d = 0 := hd.2.trans hd.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    simp only [↓reduceIte, beq_self_eq_true] at h
    peelP h; peelP h; peelP h; peelP h; peelP h; peelP h; peelP h
    peelF O hA (stableA_JQ _ 0) h hw; peelF O hA (stableA_JQ _ 0) h hw
    peelF O hA (stableA_JQ _ 0) h hw; peelF O hA (stableA_JQ _ 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleC_clear O hA 0 (R := fun _ _ => False)) hw step
    clear step
    peelF O hA (stableA_JQC O 0) h hw; peelF O hA (stableA_JQC O 0) h hw
    peelF O hA (stableA_JQC O 0) h hw; peelF O hA (stableA_JQC O 0) h hw
    peelF O hA (stableA_JQC O 0) h hw; peelF O hA (stableA_JQC O 0) h hw
    peelF O hA (stableA_JQC O 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleC_depthSet O hA 0 (0 + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw
  · replace hw : JQC O D w := ⟨hw, hc.resolve_left h0⟩
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O D) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag O hA (stableA_JQC O D)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet O hA (stableA_JQC O D)) hw s3
    have hdD : d = D := hd.2.trans hd.1.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    have h0' : ¬ ((d == 0) = true) := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleC_depthSet O hA d (d + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw

/-- **(RR2)** The machine branch of the body, split on linked worlds, without `htr`/`hchild` (the proof of
`synthesizeFromConst_machine_split2A` without its `JQC` after the machine run). -/
theorem fromConst_machine_linkA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {tenv : Environment} {b : Bool} {X : Name} {n : Nat} {ci : ConstantInfo} {isInst : Lean.Expr → Bool}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none) (miss : mixedCertifiedShape? false [] ci isInst = none)
    (hw : JQC O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false true
      ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR' : Environment) (w₁ : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR' w₁ ∧ JQC O n w₁ ∧
      ∀ shape, machineShape? false [] ci (structEnv envR') = some shape →
        ∃ (r : Option Res) (w₂ : Void IO.RealWorld),
          RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X shape)
            mctx mref cctx cref w₁ r w₂ ∧
          ((∃ res, r = some res ∧ res = (m, d) ∧ ∃ wl : Void IO.RealWorld,
              RunsTo (show MetaM Unit from profLogIO b
                s!"[profile] synthesizeCombinational {X} machine certified front end") mctx mref cctx cref w₂ () wl ∧
              RunsTo (sparkleSubModuleCache.modify (·.insert X res) : MetaM Unit) mctx mref cctx cref wl () w') ∨
           (r = none ∧ RunsTo (legacyTail (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false ci)
              mctx mref cctx cref w₂ (m, d) w')) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O n) FramedA.env)) hw henv
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  refine ⟨envR, _, henv, hw1, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  refine ⟨r, w3, hmach, ?_⟩
  cases r with
  | none => exact Or.inr ⟨rfl, hr⟩
  | some res =>
    dsimp only at hr
    obtain ⟨_, wl, hlog, hr⟩ := RunsTo.bind hr
    obtain ⟨_, wm, hmod, hr⟩ := RunsTo.bind hr
    obtain ⟨he, rfl⟩ := RunsTo.pure_world hr
    exact Or.inl ⟨res, rfl, he.symm, wl, hlog, hmod⟩

/-- **(RR3) DG-RUNREADS.** -/
theorem runReads_of_run (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {X : Name}
    {shape : MachineShape} {D₀ : Nat} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape) :
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6 ∧ JQC O (D₀ + 1) w5 := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, hfin⟩ :=
    Tools.ShippingEntryReadsLinked.core_chain hr
  have hw1 := coreHead_jqcA O hA hw hc hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (D₀ + 1))
    (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (D₀ + 1)) FramedA.env)) hw2 henv
  obtain ⟨old, miss, -⟩ := entry _ _ _ _ _ _ _ _ _ hget henv henv
  obtain ⟨envR', w5, henv', hw5, hmach⟩ := fromConst_machine_linkA O hA old miss hw3 hbody
  obtain ⟨-, -, hshape⟩ := entry _ _ _ _ _ _ _ _ _ hget henv henv'
  obtain ⟨r, w6, hrun, hout⟩ := hmach shape hshape
  have hne := closes s.profile (D₀ + 1) w5 r w6 hw5 (by omega) hrun
  rcases hout with ⟨res, hres, hrd, wl, hlog, hmod⟩ | ⟨hnone, -⟩
  · subst hres
    subst hrd
    exact ⟨s.profile, ci, envR, envR', w5, w6,
      ⟨hr, ⟨s, w1, w2, w3, w4, wl, rfl, hh, hget, henv, henv', hrun, hlog, hmod, hfin⟩, ⟨old, miss⟩, hshape⟩, hw5⟩
  · exact absurd hnone hne

end Tools.ShippingGen5RunReads
