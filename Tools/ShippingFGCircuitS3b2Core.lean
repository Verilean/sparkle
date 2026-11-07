import Tools.ShippingFGCircuitS1qEndpoint
import Tools.ShippingReflectCtx
set_option autoImplicit false
-- FG circuit pilot S3b2 (route B), unit 3: the chain of `synthesizeCombinationalCoreOffR readerOk` (the existing core plus ONE pure guard) and the BRIDGE to the existing core / `synthesizeCombinationalOff`: a successful run with a check is a successful run of the existing code with the same input, start/end world, Module and Design.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §53.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3b2Core
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (CoreSaved bind_assoc_fn ite_bind_fn)
open Tools.ShippingMachineOutcomeA3 (coreFinally RunsTo.try_finally')
open Tools.ShippingFGCircuitS1qLinked (coreHeadOff coreRestOff core_eqOff)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- two successful runs in sequence are a successful run of `tryFinally` -/
theorem RunsTo.try_finally_intro {α β : Type} {x : MetaM α} {fin : MetaM β} {w : Void IO.RealWorld} {a : α}
    {w1 w' : Void IO.RealWorld} {u : β}
    (hx : RunsTo x mctx mref cctx cref w a w1) (hf : RunsTo fin mctx mref cctx cref w1 u w') :
    RunsTo (_root_.tryFinally x fin) mctx mref cctx cref w a w' := by
  unfold RunsTo at hx hf ⊢
  change (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w = _
  unfold EST.bind
  simp only [MonadFinally.tryFinally']
  rw [hx]
  simp only [hf]
  rfl

/-- the second half of `synthesizeCombinationalCoreOffR` (after the shared head) -/
def coreRestOffR (readerOk : Environment → Name → Bool) (declName : Name) (s : CoreSaved) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let doSynth : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
    let constInfo ← getConstInfo declName
    let env ← getEnv
    if (entryInlinerError? env true false [] constInfo (instancePredicate env)).isSome then
      throwError (stringToMessageData s!"{declName}: {(entryInlinerError? env true false []
        constInfo (instancePredicate env)).getD ""}")
    else if !(Sparkle.Compiler.PilotEnvTables.startEnvOk declName env) then
      throwError (stringToMessageData s!"{declName}: the start environment does not match the environment tables of the guarantee (definition bodies, constructors, List.rec); refusing to synthesize")
    else if !(Sparkle.Compiler.PilotKidTables.startKidsOk declName env (userInliner env) (instancePredicate env) gatePeeledBody) then
      throwError (stringToMessageData s!"{declName}: the start environment does not satisfy the callee facts of the guarantee (callee definitions, inliner, instance predicate); refusing to synthesize")
    else if !(readerOk env declName) then
      throwError (stringToMessageData s!"{declName}: the start environment does not pass the reader check of this entry; refusing to synthesize")
    else
    synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) (fun _ => pure ()) declName [] false true
      (entryConst true false [] constInfo
        (instancePredicate env) (userInliner env) (structEnv env))
      (instancePredicate env)
  tryFinally doSynth (coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg)

theorem core_eqOffR (readerOk : Environment → Name → Bool) (declName : Name) :
    synthesizeCombinationalCoreOffR readerOk declName =
      (coreHeadOff declName >>= fun s => coreRestOffR readerOk declName s) := by
  unfold synthesizeCombinationalCoreOffR coreHeadOff coreRestOffR
  simp only [bind_assoc_fn, ite_bind_fn]
  rfl

/-- **the chain of the checked core**: head, `getConstInfo`, `getEnv` returning `envR`, the four guards at that `envR` (the inliner error absent, `startEnvOk`, `startKidsOk`, and the NEW `readerOk envR declName`), the body, the `finally` -/
theorem coreR_chain {readerOk : Environment → Name → Bool} {declName : Name} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCoreOffR readerOk declName) mctx mref cctx cref w (M, D) w') :
    ∃ (s : CoreSaved) (w1 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo)
      (w2 w3 w4 : Void IO.RealWorld),
      RunsTo (coreHeadOff declName) mctx mref cctx cref w s w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
      ¬ ((entryInlinerError? envR true false [] ci (instancePredicate envR)).isSome = true) ∧
      Sparkle.Compiler.PilotEnvTables.startEnvOk declName envR = true ∧
      Sparkle.Compiler.PilotKidTables.startKidsOk declName envR (userInliner envR) (instancePredicate envR) gatePeeledBody = true ∧
      readerOk envR declName = true ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (fun _ => pure ())
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 ∧
      RunsTo (coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg) mctx mref cctx cref w4 () w' := by
  rw [core_eqOffR] at hr
  obtain ⟨s, w1, hh, hk⟩ := RunsTo.bind hr
  unfold coreRestOffR at hk
  obtain ⟨w4, u, hx, hfin⟩ := RunsTo.try_finally' hk
  cases u
  obtain ⟨ci, w2, hget, hx⟩ := RunsTo.bind hx
  obtain ⟨envR, w3, henv, hx⟩ := RunsTo.bind hx
  by_cases c1 : (entryInlinerError? envR true false [] ci (instancePredicate envR)).isSome = true
  · rw [if_pos c1] at hx
    exact (Tools.ShippingEntrySoundness.RunsTo.throwError_false hx).elim
  rw [if_neg c1] at hx
  by_cases c2 : (!(Sparkle.Compiler.PilotEnvTables.startEnvOk declName envR)) = true
  · rw [if_pos c2] at hx
    exact (Tools.ShippingEntrySoundness.RunsTo.throwError_false hx).elim
  rw [if_neg c2] at hx
  by_cases c3 : (!(Sparkle.Compiler.PilotKidTables.startKidsOk declName envR (userInliner envR) (instancePredicate envR) gatePeeledBody)) = true
  · rw [if_pos c3] at hx
    exact (Tools.ShippingEntrySoundness.RunsTo.throwError_false hx).elim
  rw [if_neg c3] at hx
  by_cases c4 : (!(readerOk envR declName)) = true
  · rw [if_pos c4] at hx
    exact (Tools.ShippingEntrySoundness.RunsTo.throwError_false hx).elim
  rw [if_neg c4] at hx
  refine ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, c1, ?_, ?_, ?_, hx, hfin⟩
  · simpa using c2
  · simpa using c3
  · simpa using c4

/-- **the bridge (core)**: a successful run of the checked core is a successful run of the EXISTING core `synthesizeCombinationalCoreOff` with the same declaration, start world, end world, Module and Design.  (The check is a pure test of `envR`: it does not change what is run.) -/
theorem coreR_to_core {readerOk : Environment → Name → Bool} {declName : Name} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCoreOffR readerOk declName) mctx mref cctx cref w (M, D) w') :
    RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (M, D) w' := by
  obtain ⟨s, w1, envR, ci, w2, w3, w4, hh, hget, henv, c1, c2, c3, -, hbody, hfin⟩ := coreR_chain hr
  rw [core_eqOff]
  refine Tools.ShippingReflectCtx.RunsTo.bind_intro hh ?_
  unfold coreRestOff
  refine RunsTo.try_finally_intro (w1 := w4) (u := ()) ?_ hfin
  refine Tools.ShippingReflectCtx.RunsTo.bind_intro hget ?_
  refine Tools.ShippingReflectCtx.RunsTo.bind_intro henv ?_
  rw [if_neg c1, if_neg (by simpa using c2), if_neg (by simpa using c3)]
  exact hbody

/-- **the bridge (entry)**: a successful run of the checked `synthesizeCombinationalOffR` is a successful run of the EXISTING `synthesizeCombinationalOff` (same post-processing) with the same declaration, start/end world, Module and Design -/
theorem offR_to_off {readerOk : Environment → Name → Bool} {declName : Name} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {D' : Design}
    (hr : RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w') :
    RunsTo (synthesizeCombinationalOff declName) mctx mref cctx cref w (b, D') w' := by
  unfold synthesizeCombinationalOffR at hr
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind hr
  unfold synthesizeCombinationalOff
  exact Tools.ShippingReflectCtx.RunsTo.bind_intro (coreR_to_core hcore) h

end Tools.ShippingFGCircuitS3b2Core

#print axioms Tools.ShippingFGCircuitS3b2Core.coreR_chain
#print axioms Tools.ShippingFGCircuitS3b2Core.offR_to_off
