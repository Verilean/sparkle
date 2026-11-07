import Tools.ShippingGen5RunReads
import Tools.ShippingFGCircuitS2sAdmLawsX
import Tools.ShippingFGCircuitS2sAdmS2hHist
import Tools.ShippingFGCircuitS2sAdmS2hHist2
import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
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
import Tools.ShippingFGCircuitS2sAdmChildProjFieldA
import Tools.ShippingFGCircuitS2sAdmChildRunA
import Tools.ShippingFGCircuitS2sAdmChildRunAKids
import Tools.ShippingFGCircuitS2sAdmChildTeleCP
import Tools.ShippingFGCircuitS2sAdmChildTeleLocalA
import Tools.ShippingFGCircuitS2sAdmChildTranslateA
import Tools.ShippingFGCircuitS2sAdmChildTranslatePathA
import Tools.ShippingFGCircuitS2sAdmChildVCA
import Tools.ShippingFGCircuitS2sAdmChildVertA
import Tools.ShippingFGCircuitS2sAdmChildWalkA
import Tools.ShippingFGCircuitS2sAdmKWalk
-- FG circuit pilot S2s4: SELECTIVE port of ShippingGen5RunReads.lean onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.
set_option autoImplicit false
-- Built in g5rr3-88771739 (clean, exit 0, 745 jobs). No sorry / axiom / native_decide.

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
open Tools.ShippingMachineOutcomeA (legacyTail)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **(RR1)** The core head establishes `JQCX (D+1)` at its end world (the peel of `core_reads_linkA`,
ShippingMachineOutcomeA.lean, on `coreHead`). -/
theorem coreHead_jqcAX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx) {X : Name} {D : Nat}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvAX O (cv w))
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1) :
    JQCX O (D + 1) w1 := by
  have h := hh
  unfold Tools.ShippingEntryReadsLinked.coreHead at h
  by_cases h0 : D = 0
  · subst h0
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runsX (keeps_iff.mp (keepsA_framedX O hA (stableA_JQ _ 0) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runsX (keeps_iff.mp (keepsA_diagX O hA (stableA_JQ _ 0)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runsX (tripleA_depthGetX O hA (stableA_JQ _ 0)) hw s3
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
    have hw := triple_runsX (tripleC_clearX O hA 0 (R := fun _ _ => False)) hw step
    clear step
    peelF O hA (stableA_JQCX O 0) h hw; peelF O hA (stableA_JQCX O 0) h hw
    peelF O hA (stableA_JQCX O 0) h hw; peelF O hA (stableA_JQCX O 0) h hw
    peelF O hA (stableA_JQCX O 0) h hw; peelF O hA (stableA_JQCX O 0) h hw
    peelF O hA (stableA_JQCX O 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runsX (tripleC_depthSetX O hA 0 (0 + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw
  · replace hw : JQCX O D w := ⟨hw, hc.resolve_left h0⟩
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runsX (keeps_iff.mp (keepsA_framedX O hA (stableA_JQCX O D) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runsX (keeps_iff.mp (keepsA_diagX O hA (stableA_JQCX O D)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runsX (tripleA_depthGetX O hA (stableA_JQCX O D)) hw s3
    have hdD : d = D := hd.2.trans hd.1.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    have h0' : ¬ ((d == 0) = true) := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    peelF O hA (stableA_JQCX O d) h hw; peelF O hA (stableA_JQCX O d) h hw
    peelF O hA (stableA_JQCX O d) h hw; peelF O hA (stableA_JQCX O d) h hw
    peelF O hA (stableA_JQCX O d) h hw; peelF O hA (stableA_JQCX O d) h hw
    peelF O hA (stableA_JQCX O d) h hw
    peelF O hA (stableA_JQCX O d) h hw; peelF O hA (stableA_JQCX O d) h hw
    peelF O hA (stableA_JQCX O d) h hw; peelF O hA (stableA_JQCX O d) h hw
    peelF O hA (stableA_JQCX O d) h hw; peelF O hA (stableA_JQCX O d) h hw
    peelF O hA (stableA_JQCX O d) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runsX (tripleC_depthSetX O hA d (d + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw


/-- **(RR2)** The machine branch of the body, split on linked worlds, without `htr`/`hchild` (the proof of
`synthesizeFromConst_machine_split2A` without its `JQCX` after the machine run). -/
theorem fromConst_machine_linkAX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx)
    {tenv : Environment} {b : Bool} {X : Name} {n : Nat} {ci : ConstantInfo} {isInst : Lean.Expr → Bool}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none) (miss : mixedCertifiedShape? false [] ci isInst = none)
    (hw : JQCX O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false true
      ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR' : Environment) (w₁ : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR' w₁ ∧ JQCX O n w₁ ∧
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
  have hw1 := triple_runsX (keeps_iff.mp (keepsA_framedX O hA (stableA_JQCX O n) FramedA.env)) hw henv
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
theorem runReads_of_runX (O : RefLawsAOpsX MkRefd mref cref) (hA : O.adm mctx cctx) {X : Name}
    {shape : MachineShape} {D₀ : Nat} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvAX O (cv w))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtAX O mctx cctx X shape) :
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6 ∧ JQCX O (D₀ + 1) w5 := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, hfin⟩ :=
    Tools.ShippingEntryReadsLinked.core_chain hr
  have hw1 := coreHead_jqcAX O hA hw hc hh
  have hw2 := triple_runsX (keeps_iff.mp (keepsA_framedX O hA (stableA_JQCX O (D₀ + 1))
    (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runsX (keeps_iff.mp (keepsA_framedX O hA (stableA_JQCX O (D₀ + 1)) FramedA.env)) hw2 henv
  obtain ⟨old, miss, -⟩ := entry _ _ _ _ _ _ _ _ _ hget henv henv
  obtain ⟨envR', w5, henv', hw5, hmach⟩ := fromConst_machine_linkAX O hA old miss hw3 hbody
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

