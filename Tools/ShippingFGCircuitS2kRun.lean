import Tools.ShippingFGCircuitS2hHist3
import Tools.ShippingFGCircuitS1qLinked
import Tools.ShippingFGCircuitRunLocal
import Tools.ShippingGen2Served
set_option autoImplicit false
-- FG circuit pilot S2k (part 1): the root's machine run and its SERVED instances from a HISTORY world (`JQH`), with the children `RealChildE` (they carry the reads of their own run). Copies of `machine_run_of_coreCOff`, `synthesizeFromConst_machine_invR`, `synthesizeMachineCertified_runsA`, `synthesizeCombinationalCore_machine_soundRA_ranA` with `JQC`/`RealChildA` ↦ `JQH`/`RealChildE`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §37.

namespace Tools.ShippingFGCircuitS2kRun
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingMachineTraceX Tools.ShippingServedRealA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge Tools.ShippingMachineAuto
open Tools.ShippingMachineRef Tools.ShippingMachineSource Tools.ShippingUnifiedSource
open Tools.ShippingFGCircuitS2hHist Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitRunLocal Tools.ShippingGen2

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `MachineRunJQC` at a history world: the machine synthesis a core run performs returned the run's result from a `JQH O E n` world -/
def MachineRunJQH (O : RefLawsAOps MkRefd mref cref) (E : StartEv) (mctx : Meta.Context) (cctx : Core.Context)
    (n : Nat) (c : Name) (shape : MachineShape) (M : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (tenv : Lean.Environment), ∃ (b : Bool) (w9 w10 : Void IO.RealWorld),
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
      mctx mref cctx cref w9 (some (M, D)) w10 ∧ JQH O E n w9

theorem MachineRunJQH.toC {O : RefLawsAOps MkRefd mref cref} {E : StartEv} {n : Nat} {c : Name} {shape : MachineShape}
    {M : Sparkle.IR.AST.Module} {D : Design} (h : MachineRunJQH O E mctx cctx n c shape M D) :
    MachineRunJQC O mctx cctx n c shape M D := by
  obtain ⟨tenv, b, w9, w10, hrun, hw⟩ := h
  exact ⟨tenv, b, w9, w10, hrun, hw.toC⟩

/-- `synthesizeFromConst_machine_invR` at `JQH` -/
theorem synthesizeFromConst_machine_invH (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {E : StartEv} {tenv : Lean.Environment}
    {logProf : String → IO Unit} {declName : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : JQH O E n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) logProf
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w7 w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
            shape) mctx mref cctx cref w7 r w8 ∧ JQH O E n w7 ∧
          ∀ res, r = some res → res = (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQH O E n) FramedA.env)) hw henv
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  refine ⟨envR, _, henv, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  refine ⟨r, _, _, hmach, hw1, ?_⟩
  intro res hres
  subst hres
  dsimp only at hr
  have hr := hr.mreturns
  peel_bind hr
  peel_bind hr
  exact (MReturns.pure hr).symm

/-- `machine_run_of_coreCOff` at a history world, for the root run (depth 0: the head clears the cache, so the history is empty) -/
theorem machine_run_of_coreHOff (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (hw : JQ O.quiet 0 w) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
        mctx mref cctx cref w9 r w10 ∧ JQH O E (0 + 1) w9 ∧
      ∀ res, r = some res → res = (m, d) := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, -⟩ := core_chainOff hr
  have hw1 := Tools.ShippingFGCircuitS2hHist.coreHeadOff_jqhA (E := E) O hA hw hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQH O E (0 + 1)) (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQH O E (0 + 1)) FramedA.env)) hw2 henv
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hget henv hbody
  obtain ⟨envR', w8, henv', hmach⟩ := synthesizeFromConst_machine_invH O hA old miss hw3 hbody
  obtain ⟨r, w9, w10, hrun, hw9, hres⟩ := hmach shape (hshape _ _ henv')
  exact ⟨_, false, r, w9, w10, hrun, hw9, hres⟩

theorem machineRunJQH_of_closesHOff (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (closes : MachineClosesAtH (mref := mref) (cref := cref) O E mctx cctx declName shape)
    (hw : JQ O.quiet 0 w) :
    MachineRunJQH O E mctx cctx (0 + 1) declName shape m d := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machine_run_of_coreHOff O hA hr entry hw
  have hne := closes b (0 + 1) w9 r w10 hw9 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact ⟨tenv, b, w9, w10, hrun, hw9⟩

/-- `synthesizeMachineCertified_runsA` at `JQH`: the closing's children are `ChildrenRealE` -/
theorem synthesizeMachineCertified_runsH (O : RefLawsAOps MkRefd mref cref) {E : StartEv} (hB : BodyStepH O E)
    (hmiss : MissE O E) (hA : AdmCtx O.quiet mctx cctx) {n : Nat} (hn : 1 ≤ n) {tenv : Lean.Environment}
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref (JQH O E n)
      (translateExprToWire tenv e hint top named))
    {b : Bool} {declName shape m d} {w w'} (hw : JQH O E n w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
          ChildrenRealE O E shape children)) := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (mixed_keepsAP O hA (stableA_JQH O E n) _ b declName
    shape.binders shape.body htr)) hw run
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    split at hr
    · rename_i hi
      have eq := RunsTo.pure_eq hr
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨hm, hd⟩ := eq
      exact ⟨t, t', d', run.mreturns, hcl, Or.inl ⟨hi, hm, hd⟩⟩
    · rename_i hi
      have hne : shape.insts ≠ [] := by rw [hi]; exact List.cons_ne_nil _ _
      split at hr
      · rename_i hf
        obtain ⟨children, hc, hreal, _⟩ := closeInstsM_runH O hB hmiss hA hn hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inl ⟨List.isEmpty_iff.mp hf, hc.symm⟩, hreal⟩⟩
      · rename_i hf
        obtain ⟨children, hc, hmc, hreal, _⟩ := closeInstsGM_runH O hB hmiss hA hn hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inr ⟨fun h => hf (List.isEmpty_iff.mpr h), hc.symm, hmc⟩, hreal⟩⟩
  · have eq := RunsTo.pure_eq hr
    cases eq

/-- the served instances of a root run from a history world are `RealChildE`: `synthesizeCombinationalCore_machine_soundRA_ranA` at `JQH`, in the `SoundXAt` form of `Pkg.traceX` -/
theorem soundX_served_E (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) {E : StartEv}
    (hmiss : MissE O E) (hA : AdmCtx O.quiet mctx cctx) {n : Nat} (hn : 1 ≤ n)
    {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    (ran : MachineRunJQH O E mctx cctx n declName shape m d) :
    SoundXAt (ServedP (RealChildE O E) declName shape m d) declName shape m d := by
  intro bsIn slotBs letBs hbs hlets positive slotKinds letKinds layW outsOk outsNodup
  obtain ⟨tenv, prof, w9, w10, hrun, hw9⟩ := ran
  obtain ⟨t, t', d₀, hmix, hcl, hmt⟩ :=
    synthesizeMachineCertified_runsH O (bodyStepH_of_tele O T) hmiss hA hn
      (by obtain ⟨D, rfl⟩ : ∃ D, n = D + 1 := ⟨n - 1, by omega⟩; exact htrH_of_tele O hA T hmiss D tenv) hw9 hrun
  have hmt0 : (shape.insts = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
      (shape.insts ≠ [] ∧ ∃ children,
        CloseCalls shape t (closeMachine shape.layout t') d₀ children m d) := by
    rcases hmt with h0 | ⟨hi, children, hcc, _⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hi, children, hcc⟩
  refine synthesizeMachineCertified_soundX _ hmix hcl hmt0 ?_ hbs hlets positive slotKinds
    letKinds layW outsOk outsNodup
  intro ids cache regs lets wired hmp notInst
  have h0 : ∀ st ∈ (closeMachine shape.layout t').body, isInst st = false := fun st hs => by
    cases hi : isInst st
    · rfl
    · exact absurd (notInst st hs hi) id
  refine ⟨?g, ?o⟩
  case o =>
    intro hfe1 k hk args mc st hargs hst hcs hmod
    rcases hmt with ⟨h0', _, _⟩ | ⟨_, children, hcc, hreal⟩
    · rw [h0'] at hk; exact absurd hk (Nat.not_lt_zero _)
    rcases hcc with ⟨_, hC⟩ | ⟨hfe0, _, _⟩
    case inr => exact absurd hfe1 hfe0
    rw [hmp] at hcs
    obtain ⟨y, hy, hmcy⟩ := Tools.ShippingChildServe.closeInsts_serves hC h0 hst hcs hmod
    have hyc := (Tools.ShippingChildServe.closeInsts_acyclic hC).2.2.2 y (List.mem_of_getElem? hy)
    obtain ⟨_, hkr⟩ := hreal
    obtain ⟨y', hy', hor⟩ := hkr k hk
    rw [hy] at hy'; cases hy'
    subst hmcy
    rcases hor with hmem | hrc
    · exact Or.inl ⟨y, hmem, rfl⟩
    · exact Or.inr ⟨y.2, hrc, hyc⟩
  case g =>
  intro hfe k hk mc iname argWs outs outWs hst hout hke hmod
  rcases hmt with ⟨h0, _, _⟩ | ⟨_, children, hcc, hreal⟩
  · rw [h0] at hk; exact absurd hk (Nat.not_lt_zero _)
  rcases hcc with ⟨hfe0, _⟩ | ⟨_, hG, _⟩
  · exact absurd hfe0 hfe
  have hall := wired.2.1
  rw [hmp] at hall hout
  have hcr : "clk" ∉ t.inputs.map (·.name) ∧ "rst" ∉ t.inputs.map (·.name) :=
    ⟨fun h => (allocated_ne (hall _ h)).1 rfl, fun h => (allocated_ne (hall _ h)).2 rfl⟩
  obtain ⟨y, hy, hmcy⟩ := Tools.ShippingChildServe.closeInstsG_serves hG
    (fun st hs => by
      cases hi : isInst st
      · rfl
      · exact absurd (notInst st hs hi) id)
    hcr hk hst hout hke hmod
  have hyc := ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y (List.mem_of_getElem? hy)).2
  obtain ⟨_, hkr⟩ := hreal
  obtain ⟨y', hy', hor⟩ := hkr k hk
  rw [hy] at hy'; cases hy'
  subst hmcy
  rcases hor with hmem | hrc
  · exact Or.inl ⟨y, hmem, rfl⟩
  · exact Or.inr ⟨y.2, hrc, hyc⟩

end Tools.ShippingFGCircuitS2kRun

#print axioms Tools.ShippingFGCircuitS2kRun.machineRunJQH_of_closesHOff
#print axioms Tools.ShippingFGCircuitS2kRun.synthesizeMachineCertified_runsH
#print axioms Tools.ShippingFGCircuitS2kRun.soundX_served_E
