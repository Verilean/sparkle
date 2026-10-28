import Tools.ShippingMachineOutcomeA3
-- BUILT (unit MO4): mo4a exit 1 (implicit mctx/mref/cctx/cref of two defs), mo4b exit 0; audit mo4c exit 0 (ChildVertAuditTest).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # MO4: the entry's saved maps ARE the values its start reads returned

`core_machine_outcomeA''` (MO3) has the finally run `coreFinally D sf … sg` from the body end to the core's end
world `w'`, but `sf … sg` are existential.  Here:

* `StartReadsN` (entry depth `D ≠ 0`): the entry's initial reads FROM THE CORE'S START WORLD `w`, as runs:
  `IO.getEnv "SPARKLE_PROFILE"`, the profile log, the depth read (returning `D`), then the seven `get`s of the
  fvar-value / wire-width / let-wire / loop-wire / wire-canon / sub-instance-output / single-out maps, each returning
  the saved value, and each saved value EQUALS `readOf r` at the world the read ran from (`runsTo_get_readOf`,
  no law).  At `D = 0` the saved values are `{}` (the entry reads nothing; the finally restores nothing).
* `FinallyRestores`: the finally run split into the depth decrement and (for `D ≠ 0`) the seven `set` runs with
  exactly `sf … sg`.
* `core_machine_outcomeA'''`: `core_machine_outcomeA''` plus these links (successful runs only).

NOT shown (OPEN): that `readOf r` of a side map at the read world equals `readOf r w` (the laws of `RefLawsAOps`
track only `cv`/`sv`/`dv`; nothing says the IO steps / the other `get`s leave the side maps alone), and that after
a `set r v` the ref reads `v` (no set-then-read lemma: `ST.Ref.set` is opaque).  So "the restored components of
`w'` equal the start values" is exposed as RUN witnesses (the `set` runs carry the read values), not as
`readOf … w' = readOf … w`. -/

namespace Tools.ShippingMachineOutcomeA4
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
open Tools.ShippingMachineOutcomeA Tools.ShippingMachineOutcomeA3

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A get step that keeps its run (the value and the end world are named). -/
macro "peelK " O:term:max hA:term:max hS:term:max h:ident hw:ident v:ident x:ident g:ident :
    tactic => `(tactic|
  (obtain ⟨$v:ident, $x:ident, $g:ident, $h:ident⟩ := RunsTo.bind $h:ident
   have $hw:ident := framed_runs $O $hA $hS $hw $g
     (FramedA.sideGet (by constructor))))

/-- The entry's start reads at depth `D ≠ 0`, from the core's start world `w`. -/
def StartReadsN (declName : Name) (b : Bool) (D : Nat) (w : Void IO.RealWorld)
    (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
    (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
    (sg : Std.HashMap String String) : Prop :=
  ∃ (prof : Option String) (wa wb wc x1 x2 x3 x4 x5 x6 x7 : Void IO.RealWorld),
    prof.isSome = b ∧
    RunsTo (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref w prof wa ∧
    RunsTo (liftM (profLogIO b s!"[profile] synthesizeCombinational {declName} entering") : MetaM Unit)
      mctx mref cctx cref wa () wb ∧
    RunsTo (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref wb D wc ∧
    RunsTo (sparkleFvarValueMap.get : MetaM (Std.HashMap Name Expr)) mctx mref cctx cref wc sf x1 ∧
      sf = readOf sparkleFvarValueMap wc ∧
    RunsTo (sparkleWireWidthCache.get : MetaM (Std.HashMap String Nat)) mctx mref cctx cref x1 sw x2 ∧
      sw = readOf sparkleWireWidthCache x1 ∧
    RunsTo (sparkleLetWireCache.get : MetaM (Std.HashMap String String)) mctx mref cctx cref x2 sl x3 ∧
      sl = readOf sparkleLetWireCache x2 ∧
    RunsTo (sparkleLoopWireCache.get : MetaM (Std.HashMap String String)) mctx mref cctx cref x3 sp x4 ∧
      sp = readOf sparkleLoopWireCache x3 ∧
    RunsTo (sparkleWireCanon.get : MetaM (Std.HashMap String String)) mctx mref cctx cref x4 sc x5 ∧
      sc = readOf sparkleWireCanon x4 ∧
    RunsTo (sparkleSubInstanceOutputs.get : MetaM (Std.HashMap (UInt64 × String) String))
      mctx mref cctx cref x5 ss x6 ∧ ss = readOf sparkleSubInstanceOutputs x5 ∧
    RunsTo (sparkleSingleOutInstanceCache.get : MetaM (Std.HashMap String String))
      mctx mref cctx cref x6 sg x7 ∧ sg = readOf sparkleSingleOutInstanceCache x6

/-- The finally block as runs: the depth decrement, then (`D ≠ 0`) the seven restoring `set`s. -/
def FinallyRestores (D : Nat) (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
    (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
    (sg : Std.HashMap String String) (w5 w' : Void IO.RealWorld) : Prop :=
  ∃ y0 : Void IO.RealWorld,
    RunsTo (sparkleSynthDepth.modify (· - 1) : MetaM Unit) mctx mref cctx cref w5 () y0 ∧
    (D = 0 → w' = y0) ∧
    (D ≠ 0 → ∃ y1 y2 y3 y4 y5 y6 : Void IO.RealWorld,
      RunsTo (sparkleFvarValueMap.set sf : MetaM Unit) mctx mref cctx cref y0 () y1 ∧
      RunsTo (sparkleWireWidthCache.set sw : MetaM Unit) mctx mref cctx cref y1 () y2 ∧
      RunsTo (sparkleLetWireCache.set sl : MetaM Unit) mctx mref cctx cref y2 () y3 ∧
      RunsTo (sparkleLoopWireCache.set sp : MetaM Unit) mctx mref cctx cref y3 () y4 ∧
      RunsTo (sparkleWireCanon.set sc : MetaM Unit) mctx mref cctx cref y4 () y5 ∧
      RunsTo (sparkleSubInstanceOutputs.set ss : MetaM Unit) mctx mref cctx cref y5 () y6 ∧
      RunsTo (sparkleSingleOutInstanceCache.set sg : MetaM Unit) mctx mref cctx cref y6 () w')

theorem coreFinally_split {D : Nat} {sf : Std.HashMap Name Expr} {sw : Std.HashMap String Nat}
    {sl sp sc : Std.HashMap String String} {ss : Std.HashMap (UInt64 × String) String}
    {sg : Std.HashMap String String} {w5 w' : Void IO.RealWorld}
    (h : RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w5 () w') :
    FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w5 w' := by
  unfold coreFinally at h
  obtain ⟨u, y0, hm, h⟩ := RunsTo.bind h
  refine ⟨y0, hm, ?_, ?_⟩
  · intro h0
    subst h0
    rw [if_neg (by decide)] at h
    exact (RunsTo.pure_world h).2
  · intro h0
    rw [if_pos (by simpa using h0)] at h
    obtain ⟨_, y1, s1, h⟩ := RunsTo.bind h
    obtain ⟨_, y2, s2, h⟩ := RunsTo.bind h
    obtain ⟨_, y3, s3, h⟩ := RunsTo.bind h
    obtain ⟨_, y4, s4, h⟩ := RunsTo.bind h
    obtain ⟨_, y5, s5, h⟩ := RunsTo.bind h
    obtain ⟨_, y6, s6, h⟩ := RunsTo.bind h
    exact ⟨y1, y2, y3, y4, y5, y6, s1, s2, s3, s4, s5, s6, h⟩

theorem core_reads_link4A (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
        RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w4 () w' ∧
        (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
        (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) declName b D w sf sw sl sp sc ss sg) := by
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
    exact ⟨prof.isSome, env, ci, _, w2, _, _, hget, henv, h, hw, _, _, _, _, _, _, _, hfin, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun h0 => absurd rfl h0⟩
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
    peelK O hA (stableA_JQC O d) h hw sf x1 g1
    peelK O hA (stableA_JQC O d) h hw sw x2 g2
    peelK O hA (stableA_JQC O d) h hw sl x3 g3
    peelK O hA (stableA_JQC O d) h hw sp x4 g4
    peelK O hA (stableA_JQC O d) h hw sc x5 g5
    peelK O hA (stableA_JQC O d) h hw ss x6 g6
    peelK O hA (stableA_JQC O d) h hw sg x7 g7
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
    exact ⟨prof.isSome, env, ci, _, w2, _, _, hget, henv, h, hw, _, _, _, _, _, _, _, hfin, fun h0' => absurd h0' h0,
      fun _ => ⟨prof, wa, wb, wc, x1, x2, x3, x4, x5, x6, x7, rfl, s1, s2, s3, g1,
        runsTo_get_readOf _ g1, g2, runsTo_get_readOf _ g2, g3, runsTo_get_readOf _ g3, g4,
        runsTo_get_readOf _ g4, g5, runsTo_get_readOf _ g5, g6, runsTo_get_readOf _ g6, g7,
        runsTo_get_readOf _ g7⟩⟩


theorem core_machine_outcomeA''' (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
        RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
        FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
        (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
        (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) declName b D w sf sw sl sp sc ss sg)) ∧ JQC O D w' ∧
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
  obtain ⟨b, envR, ci, w1, w2, w3, w4, get, henv, run, hw3, sf, sw, sl, sp, sc, ss, sg, hfin, hz, hst⟩ :=
    core_reads_link4A O hA hw hc hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  have htrD := htr_of_tele O hA T D envR
  obtain ⟨envR', wA, henv', hwA, hsplit⟩ :=
    synthesizeFromConst_machine_split2A O hA htrD
      (fun c => childKeepsC_all_of_tele O T (D + 1) (by omega) mctx cctx hA c) old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w6, hrun, hw6, hout⟩ := hsplit shape hshape
  refine ⟨envR, b, ci, envR', w1, w2, w3, wA, w4, w6, r, get, henv, hw3, henv', hshape, hrun,
    hwA, hw6, ⟨sf, sw, sl, sp, sc, ss, sg, hfin, coreFinally_split hfin, hz, hst⟩, ?_, ?_⟩
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


end Tools.ShippingMachineOutcomeA4
