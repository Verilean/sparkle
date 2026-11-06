import Tools.ShippingFGCircuitFinal3
import Tools.ShippingGen5Env
import Tools.ShippingGen5RunReads
import Tools.ShippingEnvSnapshot
set_option autoImplicit false
-- FG circuit pilot S1g, unit 1: `MachineDefinesLinked`, the machine boundary on the LINKED world chain of the core run, and its supply from start-environment facts. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `MachineDefinesLinked`

`MachineDefinesRun` (S1f) quantifies the read worlds `w1 w5 w3` of the core run freely (only the VALUES `ci` / `envR` are tied to a run). `MachineDefinesLinked` asks the three machine-boundary facts only of the worlds of the run's own chain
(`core_chain`): `w --coreHead--> w1 --getConstInfo--> w2 --getEnv--> w3 --synthesizeFromConst(its first getEnv at w3)-->`. The chain worlds are linked, so `ReadsAt e` at the start propagates along it.

SUPPLY (`machineDefinesLinked_of_env`): from `Start`, `hquiet : ∀ u, L.O.quiet u → ReadsAt e cref u` (the quiet-strengthening of DG-ENV, C.EN-4 / ENV), `GetEnvFrame` (the one primitive law of `EnvSnapshot`, C.EN-4) and the three gate/shape facts of ONE environment `e`
(`find? X`, `certifiedShape? = none`, `mixedCertifiedShape? = none`, `machineShape? = some shape`). The world-quantified `MachineDefinesRun` is replaced by premises about one environment plus the two named laws.
The consumers `…C` are copies of the `…R` consumers with `core_chain` (linked) in place of `synthesizeCombinationalCore_reads` (unlinked). -/
namespace Tools.ShippingFGCircuitLinked
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildVertA Tools.ShippingChildCoreC Tools.ShippingChildRunA
open Tools.ShippingServedRealA Tools.ShippingChildRunAKids Tools.ShippingMachineClose Tools.ShippingMixedEntrySoundness Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingEntryReadsLinked (CoreSaved coreHead core_chain envAt)
open Tools.ShippingFGCircuitRunLocal

/-- the machine boundary of the core run, on the linked chain `coreHead → getConstInfo → getEnv → synthesizeFromConst` -/
def MachineDefinesLinked (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) (w : Void IO.RealWorld) (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w' : Void IO.RealWorld) : Prop :=
  RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w' →
  ∀ (s : CoreSaved) (w1 w2 w3 w4 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo),
    RunsTo (coreHead declName) mctx mref cctx cref w s w1 →
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
    RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO s.profile) declName [] false true
      (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (instancePredicate envR))
      mctx mref cctx cref w3 (M, D) w4 →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (instancePredicate envR) = none ∧
    ∀ (envR' : Environment) (w8 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w8 →
      machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (structEnv envR') = some shape

section Supply
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **supply of the linked boundary** from the start admissibility, the quiet-strengthening `hquiet`, `GetEnvFrame`, and the gate / shape facts of one environment `e`. -/
theorem machineDefinesLinked_of_env (L : Tools.ShippingGen2.Laws mref cref) {X : Name} {shape : MachineShape} {e : Environment} {ci₀ : ConstantInfo}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hA : AdmCtx L.O.quiet mctx cctx) (hw : JQ L.O.quiet 0 w)
    (hquiet : ∀ u, L.O.quiet u → Tools.ShippingGen5Env.ReadsAt e cref u)
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    (hc : e.find? X = some ci₀)
    (hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate e) (userInliner e) (structEnv e)) = none)
    (hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate e) (userInliner e) (structEnv e)) (instancePredicate e) = none)
    (hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate e) (userInliner e) (structEnv e)) (structEnv e) = some shape) :
    MachineDefinesLinked mctx mref cctx cref X shape w M D w' := by
  intro _ s w1 w2 w3 w4 envR ci h0 h1 h2 _
  have hj1 : JQC L.O (0 + 1) w1 := Tools.ShippingGen5RunReads.coreHead_jqcA L.O hA hw (Or.inl rfl) h0
  have r1 : Tools.ShippingGen5Env.ReadsAt e cref w1 := hquiet _ hj1.1.1
  have r2 : Tools.ShippingGen5Env.ReadsAt e cref w2 :=
    Tools.ShippingGen5Env.ReadsAt.of_frame (Tools.ShippingEnvSnapshot.envFrame_getConstInfo X hg) h1 r1
  have r3 : Tools.ShippingGen5Env.ReadsAt e cref w3 := Tools.ShippingGen5Env.ReadsAt.of_frame hg h2 r2
  have hci : ci = ci₀ := Option.some.inj ((Tools.ShippingGen5Env.ci_of_readsAt h1 r1).symm.trans hc)
  obtain ⟨-, hi, hu, hs⟩ := Tools.ShippingGen5Env.envR_of_readsAt h2 r2
  subst hci
  rw [hi, hu, hs]
  refine ⟨hg1, hg2, ?_⟩
  intro envR' w8 h3
  obtain ⟨-, -, -, hs'⟩ := Tools.ShippingGen5Env.envR_of_readsAt h3 r3
  rw [hs']
  exact hsh

end Supply

section Consumers
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `machine_run_of_coreR` on the linked chain -/
theorem machine_run_of_coreC (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinked mctx mref cctx cref declName shape w m d w')
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
        mctx mref cctx cref w9 r w10 ∧ JQC O (D + 1) w9 ∧
      ∀ res, r = some res → res = (m, d) := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, -⟩ := core_chain hr
  have hw1 := Tools.ShippingGen5RunReads.coreHead_jqcA O hA hw hc hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (D + 1)) (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (D + 1)) FramedA.env)) hw2 henv
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hget henv hbody
  obtain ⟨envR', w8, henv', hmach⟩ := synthesizeFromConst_machine_invR O hA old miss hw3 hbody
  obtain ⟨r, w9, w10, hrun, hw9, hres⟩ := hmach shape (hshape _ _ henv')
  exact ⟨_, s.profile, r, w9, w10, hrun, hw9, hres⟩

theorem machineRunJQC_of_closesC (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinked mctx mref cctx cref declName shape w m d w')
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    MachineRunJQC O mctx cctx (D + 1) declName shape m d := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machine_run_of_coreC O hA hr entry hw hc
  have hne := closes b (D + 1) w9 r w10 hw9 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact ⟨tenv, b, w9, w10, hrun, hw9⟩

/-- `synthesizeCombinationalCore_machine_soundR` on the linked chain -/
theorem synthesizeCombinationalCore_machine_soundC {declName : Name}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinked mctx mref cctx cref declName shape w m d w')
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hbs : shape.binders = bsIn ++ slotBs ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outsOk : ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (shape.layout.outs.map (·.name)).Nodup) :
    MachinePreserves declName shape bsIn slotBs letBs m d := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, -⟩ := core_chain hr
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hget henv hbody
  obtain ⟨envR', w8, henv', hmach⟩ := synthesizeFromConst_machineR old miss hbody
  obtain ⟨r, w9, w10, hrun, hres⟩ := hmach shape (hshape _ _ henv')
  have hne := closes _ _ _ _ hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact synthesizeMachineCertified_sound hrun.mreturns hbs hlets positive slotKinds letKinds
      layW outsOk outsNodup

end Consumers

end Tools.ShippingFGCircuitLinked

#print axioms Tools.ShippingFGCircuitLinked.machineDefinesLinked_of_env
#print axioms Tools.ShippingFGCircuitLinked.machineRunJQC_of_closesC
#print axioms Tools.ShippingFGCircuitLinked.synthesizeCombinationalCore_machine_soundC
