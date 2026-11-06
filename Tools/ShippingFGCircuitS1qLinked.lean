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

end Tools.ShippingFGCircuitS1qLinked

#print axioms Tools.ShippingFGCircuitS1qLinked.core_eqOff
#print axioms Tools.ShippingFGCircuitS1qLinked.core_chainOff
