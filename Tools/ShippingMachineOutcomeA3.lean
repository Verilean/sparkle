import Tools.ShippingMachineOutcomeA
import Tools.ShippingChildComposeC
-- BUILT (unit MO3): mo3b exit 0 (mo3a exit 1: missing opens). Audit in Tests/Compiler/ChildVertAuditTest.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # MO3: the core's ORIGINAL end world (the entry's `finally`)

* `RunsTo.try_finally'`: a returning `try x finally fin` is a returning run of `x` (`w → w₁`) and a
  returning run of `fin` (`w₁ → w'`), `w'` the end of the whole.
* `coreFinally`: the `finally` block of `synthesizeCombinationalCoreWith` (copied from the source,
  with the saved maps as parameters).
* `core_reads_link3A`: `core_reads_linkA` plus the finally run from the body end `w4` to the core end `w'`
  (saved maps are existential: they are the values the entry read at its start; NOT linked to those reads here).
* `core_machine_outcomeA''`: `core_machine_outcomeA'` with the legacy tail / machine case ending at the
  body end world `w₅`, AND the finally run `w₅ → w'` explicit, AND `JQC O D w'` (invariant at the core's end
  world, from `core_tripleAC`). (a) machine and (b) legacy remain distinct; same meaning NOT shown. -/

namespace Tools.ShippingMachineOutcomeA3
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
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingMachineOutcomeA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem RunsTo.try_finally' {α β : Type} {x : MetaM α} {fin : MetaM β}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {a : α}
    {w' : Void IO.RealWorld}
    (h : RunsTo (_root_.tryFinally x fin) mctx mref cctx cref w a w') :
    ∃ (w1 : Void IO.RealWorld) (u : β),
      RunsTo x mctx mref cctx cref w a w1 ∧ RunsTo fin mctx mref cctx cref w1 u w' := by
  unfold RunsTo at h
  change (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w = _
    at h
  unfold EST.bind at h
  split at h
  · rename_i p w1 heq
    simp only [MonadFinally.tryFinally'] at heq
    split at heq
    · rename_i v w2 hx
      split at heq
      · rename_i u w3 hfin
        cases heq
        simp only [EST.pure] at h
        cases h
        exact ⟨w2, u, hx, hfin⟩
      · cases heq
    · split at heq <;> cases heq
  · cases h

/-- The `finally` block of `synthesizeCombinationalCoreWith`, at entry depth `D`, with the saved maps. -/
def coreFinally (D : Nat) (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
    (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
    (sg : Std.HashMap String String) : MetaM Unit := do
  sparkleSynthDepth.modify (· - 1)
  if D != 0 then
    sparkleFvarValueMap.set sf
    sparkleWireWidthCache.set sw
    sparkleLetWireCache.set sl
    sparkleLoopWireCache.set sp
    sparkleWireCanon.set sc
    sparkleSubInstanceOutputs.set ss
    sparkleSingleOutInstanceCache.set sg

theorem core_reads_link3A (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {D : Nat} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module}
    {Dg : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, Dg) w') :
    ∃ (b : Bool) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO b)
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, Dg) w4 ∧ JQC O (D + 1) w3 ∧
      ∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
        (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
        (sg : Std.HashMap String String),
        RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w4 () w' := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h  -- guess: G3
  by_cases h0 : D = 0
  · -- outermost: the clear establishes the cache half
    subst h0
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
    obtain ⟨_, u, h, hfin⟩ := RunsTo.try_finally' h
    cases u
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (0 + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (0 + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, hget, henv, h, hw, _, _, _, _, _, _, _, hfin⟩
  · -- nested: the cache half is inherited
    replace hw : JQC O D w := ⟨hw, hc.resolve_left h0⟩
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
    obtain ⟨_, u, h, hfin⟩ := RunsTo.try_finally' h
    cases u
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, hget, henv, h, hw, _, _, _, _, _, _, _, hfin⟩

theorem core_machine_outcomeA'' (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    ∃ (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
      (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld) (r : Option Res),
      RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
      JQC O (D + 1) w₃ ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
      machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
        (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b)
        declName shape) mctx mref cctx cref w₄ r w₆ ∧ JQC O (D + 1) w₄ ∧ JQC O (D + 1) w₆ ∧
      (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
        (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
        (sg : Std.HashMap String String),
        RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w') ∧ JQC O D w' ∧
      ((∃ res, r = some res ∧ res = (m, d) ∧ ∃ wl : Void IO.RealWorld,
          RunsTo (show MetaM Unit from profLogIO b
            s!"[profile] synthesizeCombinational {declName} machine certified front end")
            mctx mref cctx cref w₆ () wl ∧
          RunsTo (sparkleSubModuleCache.modify (·.insert declName res) : MetaM Unit)
            mctx mref cctx cref wl () w₅) ∨
       (r = none ∧
        RunsTo (legacyTail
          (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b)
          declName [] false
          (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
            (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
        ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
          RunsTo (synthesizeMixedCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b)
            declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
          JQC O (D + 1) w₇ ∧
          ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
           (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
             ((shape.instFields.isEmpty = true ∧
                RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
                  mctx mref cctx cref w₇ none w₆) ∨
              (shape.instFields.isEmpty = false ∧
                RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
                  mctx mref cctx cref w₇ none w₆)))))) := by
  obtain ⟨b, envR, ci, w1, w2, w3, w4, get, henv, run, hw3, sf, sw, sl, sp, sc, ss, sg, hfin⟩ :=
    core_reads_link3A O hA hw hc hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  have htrD := htr_of_tele O hA T D envR
  obtain ⟨envR', wA, henv', hwA, hsplit⟩ :=
    synthesizeFromConst_machine_split2A O hA htrD
      (fun c => childKeepsC_all_of_tele O T (D + 1) (by omega) mctx cctx hA c) old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w6, hrun, hw6, hout⟩ := hsplit shape hshape
  refine ⟨envR, b, ci, envR', w1, w2, w3, wA, w4, w6, r, get, henv, hw3, henv', hshape, hrun,
    hwA, hw6, ⟨sf, sw, sl, sp, sc, ss, sg, hfin⟩, ?_, ?_⟩
  · by_cases h0 : D = 0
    · subst h0
      exact triple_runs (Tools.ShippingChildComposeC.core_tripleAC_of_tele O hA T declName) hw hr
    · exact triple_runs (Tools.ShippingChildCoreC.core_tripleAC O hA D declName
        (Tools.ShippingChildDepthC.hbodyC_of_step O (Tools.ShippingChildComposeC.bodyStepC_of_tele O T)
          hA D declName)) ⟨hw, hc.resolve_left h0⟩ hr
  rcases hout with h | ⟨hn, htail⟩
  · exact Or.inl h
  · subst hn
    obtain ⟨t, d₀, wh, hh, hwh, hcase⟩ :=
      synthesizeMachineCertified_noneSplitA O hA htrD hwA hrun
    exact Or.inr ⟨rfl, htail, t, d₀, wh, hh, hwh, hcase⟩


end Tools.ShippingMachineOutcomeA3
