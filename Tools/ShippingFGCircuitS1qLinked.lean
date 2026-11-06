import Tools.ShippingFGCircuitS1oHead
import Tools.ShippingFGCircuitFinal4
import Tools.ShippingFGCircuitRoots4
import Tools.ShippingGen5RunReads
set_option autoImplicit false
-- FG circuit pilot S1q, unit 1: the profile-free entry `synthesizeCombinationalCoreOff` split as `coreHeadOff` / `coreRestOff`, its linked chain, and the machine boundary on it.  No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1q-1: the chain of the profile-free entry

`synthesizeCombinationalCoreOff` (Sparkle/Compiler/Elab.lean) is `synthesizeCombinationalCoreWith … declName [] false true` with `profile := false` fixed by the definition: no `IO.getEnv "SPARKLE_PROFILE"`, no profile log.
`coreHeadOff` / `coreRestOff` are the mirror of `coreHead` / `coreRest` without those two (`CoreSaved.profile := false`).  The existing `coreHead`, `coreRest`, `core_*`, `MachineDefinesLinked`, … are NOT changed; the `…Off` theorems below are copies of the existing proofs under the renaming
`synthesizeCombinationalCore → synthesizeCombinationalCoreOff`, `coreHead → coreHeadOff`, `core_chain → core_chainOff`, `profLogIO s.profile → (fun _ => pure ())`. -/
namespace Tools.ShippingFGCircuitS1qLinked
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (CoreSaved envAt bind_assoc_fn ite_bind_fn)
open Tools.ShippingMachineOutcomeA3 (coreFinally RunsTo.try_finally')

/-- the prefix of `synthesizeCombinationalCoreOff` up to and including `depth + 1`; no `IO.getEnv`, no log -/
def coreHeadOff (declName : Name) : MetaM CoreSaved := do
  let depth ← sparkleSynthDepth.get
  if depth ≥ sparkleSynthDepthLimit then
    throwError "hardware modules nested deeper than the synthesis depth limit"
  let savedFvarMap ← if depth == 0 then pure ({} : Std.HashMap Lean.Name Lean.Expr)
                     else sparkleFvarValueMap.get
  let savedWireWidthCache ←
    if depth == 0 then pure ({} : Std.HashMap String Nat)
    else sparkleWireWidthCache.get
  let savedLetWireCache ←
    if depth == 0 then pure ({} : Std.HashMap String String)
    else sparkleLetWireCache.get
  let savedLoopWireCache ←
    if depth == 0 then pure ({} : Std.HashMap String String)
    else sparkleLoopWireCache.get
  let savedWireCanon ←
    if depth == 0 then pure ({} : Std.HashMap String String)
    else sparkleWireCanon.get
  let savedSubInstanceOutputs ←
    if depth == 0 then pure ({} : Std.HashMap (UInt64 × String) String)
    else sparkleSubInstanceOutputs.get
  let savedSingleOutInstanceCache ←
    if depth == 0 then pure ({} : Std.HashMap String String)
    else sparkleSingleOutInstanceCache.get
  if depth == 0 then
    sparkleTypeCache.set {}
    sparkleTypeCacheHits.set 0
    sparkleTypeCacheMiss.set 0
    sparkleSubModuleCache.set {}
    sparkleChildCache.set {}
    sparkleSubInstanceOutputs.set {}
    sparkleSingleOutInstanceCache.set {}
    sparkleFvarValueMap.set {}
    sparkleWireWidthCache.set {}
    sparkleLetWireCache.set {}
    sparkleLoopWireCache.set {}
    sparkleWireCanon.set {}
  else
    sparkleFvarValueMap.set {}
    sparkleWireWidthCache.set {}
    sparkleLetWireCache.set {}
    sparkleLoopWireCache.set {}
    sparkleWireCanon.set {}
    sparkleSubInstanceOutputs.set {}
    sparkleSingleOutInstanceCache.set {}
  sparkleSynthDepth.set (depth + 1)
  pure ⟨false, depth, savedFvarMap, savedWireWidthCache, savedLetWireCache, savedLoopWireCache,
    savedWireCanon, savedSubInstanceOutputs, savedSingleOutInstanceCache⟩

/-- `try doSynth finally …` of the profile-free entry -/
def coreRestOff (declName : Name) (s : CoreSaved) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let doSynth : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
    let constInfo ← getConstInfo declName
    let env ← getEnv
    if (entryInlinerError? env true false [] constInfo (instancePredicate env)).isSome then
      throwError (stringToMessageData s!"{declName}: {(entryInlinerError? env true false []
        constInfo (instancePredicate env)).getD ""}")
    else
    synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) (fun _ => pure ()) declName [] false true
      (entryConst true false [] constInfo
        (instancePredicate env) (userInliner env) (structEnv env))
      (instancePredicate env)
  tryFinally doSynth (coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg)

theorem core_eqOff (declName : Name) :
    synthesizeCombinationalCoreOff declName = (coreHeadOff declName >>= fun s => coreRestOff declName s) := by
  unfold synthesizeCombinationalCoreOff coreHeadOff coreRestOff
  simp only [bind_assoc_fn, ite_bind_fn]
  rfl

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem core_splitOff {declName : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (M, D) w') :
    ∃ (s : CoreSaved) (w1 : Void IO.RealWorld),
      RunsTo (coreHeadOff declName) mctx mref cctx cref w s w1 ∧
      RunsTo (coreRestOff declName s) mctx mref cctx cref w1 (M, D) w' := by
  rw [core_eqOff] at hr
  obtain ⟨s, w1, hh, hk⟩ := RunsTo.bind hr
  exact ⟨s, w1, hh, hk⟩

/-- the chain of the profile-free entry: `w —head→ w1 —getConstInfo→ w2 —getEnv→ w3 —body→ w4 —finally→ w'` -/
theorem core_chainOff {declName : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (M, D) w') :
    ∃ (s : CoreSaved) (w1 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo)
      (w2 w3 w4 : Void IO.RealWorld),
      RunsTo (coreHeadOff declName) mctx mref cctx cref w s w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (fun _ => pure ())
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 ∧
      RunsTo (coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg) mctx mref cctx cref w4 () w' := by
  obtain ⟨s, w1, hh, hk⟩ := core_splitOff hr
  unfold coreRestOff at hk
  obtain ⟨w4, u, hx, hfin⟩ := RunsTo.try_finally' hk
  cases u
  obtain ⟨ci, w2, hget, hx⟩ := RunsTo.bind hx
  obtain ⟨envR, w3, henv, hx⟩ := RunsTo.bind hx
  rcases RunsTo.ite hx with hx | hx
  · exact (Tools.ShippingEntrySoundness.RunsTo.throwError_false hx).elim
  exact ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hx, hfin⟩

section Consumers
open Tools.ShippingMachineEntry Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildVertA Tools.ShippingChildCoreC Tools.ShippingChildRunA
open Tools.ShippingServedRealA Tools.ShippingChildRunAKids Tools.ShippingMachineClose Tools.ShippingMixedEntrySoundness Sparkle.IR.Machine
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingFGCircuitRunLocal
open Sparkle.IR.Builder Tools.ShippingChildTranslateA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingMachineOutcomeA (legacyTail)

/-- **(RR1)** The core head establishes `JQC (D+1)` at its end world (the peel of `core_reads_linkA`,
ShippingMachineOutcomeA.lean, on `coreHead`). -/
theorem coreHeadOff_jqcA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {X : Name} {D : Nat}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hh : RunsTo (coreHeadOff X) mctx mref cctx cref w s w1) :
    JQC O (D + 1) w1 := by
  have h := hh
  unfold coreHeadOff at h
  by_cases h0 : D = 0
  · subst h0
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


/-- the machine boundary of the core run, on the linked chain `coreHead → getConstInfo → getEnv → synthesizeFromConst` -/
def MachineDefinesLinkedOff (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) (w : Void IO.RealWorld) (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w' : Void IO.RealWorld) : Prop :=
  RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (M, D) w' →
  ∀ (s : CoreSaved) (w1 w2 w3 w4 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo),
    RunsTo (coreHeadOff declName) mctx mref cctx cref w s w1 →
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
    RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO false) declName [] false true
      (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (instancePredicate envR))
      mctx mref cctx cref w3 (M, D) w4 →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (instancePredicate envR) = none ∧
    ∀ (envR' : Environment) (w8 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w8 →
      machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (structEnv envR') = some shape

/-- `machine_run_of_coreR` on the linked chain -/
theorem machine_run_of_coreCOff (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
        mctx mref cctx cref w9 r w10 ∧ JQC O (D + 1) w9 ∧
      ∀ res, r = some res → res = (m, d) := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, -⟩ := core_chainOff hr
  have hw1 := coreHeadOff_jqcA O hA hw hc hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (D + 1)) (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (D + 1)) FramedA.env)) hw2 henv
  obtain ⟨old, miss, hshape⟩ := entry hr s w1 w2 w3 w4 envR ci hh hget henv hbody
  obtain ⟨envR', w8, henv', hmach⟩ := synthesizeFromConst_machine_invR O hA old miss hw3 hbody
  obtain ⟨r, w9, w10, hrun, hw9, hres⟩ := hmach shape (hshape _ _ henv')
  exact ⟨_, false, r, w9, w10, hrun, hw9, hres⟩

theorem machineRunJQC_of_closesCOff (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    MachineRunJQC O mctx cctx (D + 1) declName shape m d := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machine_run_of_coreCOff O hA hr entry hw hc
  have hne := closes b (D + 1) w9 r w10 hw9 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact ⟨tenv, b, w9, w10, hrun, hw9⟩

/-- `synthesizeCombinationalCore_machine_soundR` on the linked chain of the profile-free entry -/
theorem synthesizeCombinationalCore_machine_soundCOff {declName : Name}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
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
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, hbody, -⟩ := core_chainOff hr
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

end Tools.ShippingFGCircuitS1qLinked

#print axioms Tools.ShippingFGCircuitS1qLinked.core_eqOff
#print axioms Tools.ShippingFGCircuitS1qLinked.core_chainOff
#print axioms Tools.ShippingFGCircuitS1qLinked.coreHeadOff_jqcA
#print axioms Tools.ShippingFGCircuitS1qLinked.machineRunJQC_of_closesCOff
#print axioms Tools.ShippingFGCircuitS1qLinked.synthesizeCombinationalCore_machine_soundCOff
