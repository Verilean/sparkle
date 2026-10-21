import Tools.ShippingChildRunAMain
-- BUILT (unit MO): mo2 exit 0 (mo1 exit 1: missing opens); audit mo3 exit 0 (axioms propext, Classical.choice, Quot.sound).
-- BUILT (unit MO2): section "MO2" at the end (core_reads_linkA, synthesizeMachineCertified_noneSplitA, synthesizeFromConst_machine_split2A, core_machine_outcomeA'): mo2a exit 0; audit in Tests/Compiler/ChildVertAuditTest.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Machine outcome split of a successful core run (ledger row "machine outcome split")

`MachineClosesAtA` (the machine synthesis never returns `none`) is NOT assumed. For a returning run
of `synthesizeCombinationalCore declName [] false` whose entry constant is the machine `shape`
(`MachineDefines`), `core_machine_outcomeA` proves a DISJUNCTION about the machine attempt, which
runs from a `JQC O (D+1)` world `w₁` to a world `w₂`:

* (a) it returned `some res` and `res` is the core's result;
* (b) it returned `none`, and the body then ran the legacy/memo tail FROM `w₂`, the ACTUAL post-attempt
  world. `synthesizeFromConst` does NOT roll the attempt's side effects back (the attempt is bound
  with `let machineResult? ← …` and nothing restores state), so they are kept.

In both cases `JQC O (D+1)` holds at `w₂` (the machine run keeps it: `machineCert_keepsAP`). Item 2
of the unit: in case (b) the legacy part starts in `JQC O (D+1)` and can be analysed separately.

Premises: `O`, `hA`, `T : RefLawsATele` (added, unproved telescope boundary; used only for the
`Keeps` of the machine run), the start world, `MachineDefines`. PROVED relative to those. NOT proved:
that case (a) or (b) occurs for a given input; that the machine result (a) and the legacy result (b)
have the same meaning (NOT shown; the two routes are kept distinct); semantic preservation of the legacy
route (OPEN); the evidence kept for (b) is the actual run of `legacyTail` from `w₂`;
runtime fit of the laws. `JQC` is a history/invariant, not freshness. -/

namespace Tools.ShippingMachineOutcomeA
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The legacy/memo tail of `synthesizeFromConst` (Elab.lean, after `machineResult?` is `none`):
a verbatim copy, so that the decomposition below is stated about a named program. The proof that
the body's remainder IS this program is by `exact` (definitional). -/
def legacyTail (translate : TranslateFn) (logProf : String → IO Unit)
    (declName : Name) (parameters : List (String × Nat)) (symbolicMode : Bool)
    (constInfo : ConstantInfo) : MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  if !symbolicMode then
    let memo ← sparkleSubModuleCache.get
    if let some cached := memo.get? declName then
      logProf s!"[profile] synthesizeCombinational {declName} MEMO HIT"
      return cached
  logProf s!"[profile] getConstInfo done"
  match constInfo with
  | .defnInfo defnInfo =>
    logProf s!"[profile] synthesizeCombinational {declName} starting (defnInfo)"
    let t0 ← IO.monoMsNow
    logProf s!"[profile] calling openRecordInputs"
    let body0 ← openRecordInputs defnInfo.value
    let body := stripMemoizeWrappers body0
    let t1 ← IO.monoMsNow
    logProf s!"[profile] openRecordInputs done ({t1 - t0} ms)"
    Lean.Meta.lambdaTelescope body fun xs innerBody => do
      logProf s!"[profile] calling splitReturnLeaves"
      if symbolicMode then
        for (parameterName, _) in parameters do
          let mut foundNatBinder := false
          for x in xs do
            let decl ← x.fvarId!.getDecl
            if decl.userName.toString == parameterName then
              let binderType ← whnf decl.type
              if binderType.isConstOf ``Nat then
                foundNatBinder := true
          if !foundNatBinder then
            throwError
              s!"Requested retained hardware parameter '{parameterName}' is not a top-level Nat binder of {declName}"

      let leaves ← splitReturnLeaves innerBody
      let t2 ← IO.monoMsNow
      logProf s!"[profile] splitReturnLeaves done ({t2 - t1} ms, leaves={leaves.size})"
      let cacheRef ← IO.mkRef ({} : Lean.ExprStructMap String)
      let compilerBody :=
        emitLeaves translate cacheRef logProf leaves.toList none 0
      let compiler := bindInputsLegacy parameters symbolicMode xs 0 compilerBody
      let circuitState := CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)
      let (_, finalCircuitState) ←
        (compiler.run (entryCompilerState symbolicMode cacheRef)).run circuitState
      let result ← finishSynth declName parameters symbolicMode finalCircuitState
      if !symbolicMode then
        sparkleSubModuleCache.modify (·.insert declName result)
      return result
  | _ =>
    throwError s!"Cannot synthesize {declName}: not a definition"

/-- **The body of a machine-route run, split on the machine attempt's outcome.** From a returning
run of `synthesizeFromConst … true ci isInst` (both gates miss) in a `JQC O n` world: for every shape
`machineShape?` yields at the run's second environment, the machine attempt ran from `w₇` (`JQC`) to
`w₈` (`JQC`: it keeps the invariant, from `htr` / `hchild`), and EITHER it returned `some res` with
`res` the body's result, OR it returned `none` and the legacy tail ran from `w₈` (the post-attempt
world, no rollback) to the body's result. -/
theorem synthesizeFromConst_machine_splitA (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {tenv : Lean.Environment} {b : Bool} {declName : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref (JQC O n)
      (translateExprToWire tenv e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref (JQC O n) (synthesizeChild c))
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : JQC O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n)
      (profLogIO b) declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ (r : Option Res) (w7 w8 : Void IO.RealWorld),
          RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b)
            declName shape) mctx mref cctx cref w7 r w8 ∧ JQC O n w7 ∧ JQC O n w8 ∧
          ((∃ res, r = some res ∧ res = (m, d)) ∨
           (r = none ∧ ∃ w9, RunsTo (legacyTail
              (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b)
              declName [] false ci) mctx mref cctx cref w8 (m, d) w9)) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O n) FramedA.env)) hw henv
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  refine ⟨envR, _, _, henv, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  have hw3 := triple_runs (keeps_iff.mp (machineCert_keepsAP O hA (stableA_JQC O n) _ b declName
    htr hchild (fun _ h => h.1.2.1) shape)) hw1 hmach
  refine ⟨r, _, w3, hmach, hw1, hw3, ?_⟩
  cases r with
  | none => exact Or.inr ⟨rfl, _, hr⟩
  | some res =>
    refine Or.inl ⟨res, rfl, ?_⟩
    dsimp only at hr
    have hr := hr.mreturns
    peel_bind hr
    peel_bind hr
    exact (MReturns.pure hr).symm

/-- **`core_machine_outcomeA`: the machine outcome split of a successful core run.** From a returning
run of `synthesizeCombinationalCore declName [] false` from a world with `JQ O.quiet D` (and the cache
half when `D ≠ 0`), whose entry constant is the machine `shape` (`MachineDefines`): the declaration was
read (`getConstInfo`, `getEnv`) and the machine attempt ran from a `JQC O (D+1)` world `w₁` to a
`JQC O (D+1)` world `w₂`, and EITHER (a) it returned `some res` and `res` is the core's result, OR
(b) it returned `none` and the legacy/memo tail ran from `w₂` (the actual post-attempt world; the
attempt's effects are not rolled back) to the core's result. No `MachineClosesAtA`. -/
theorem core_machine_outcomeA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w₁ w₂ : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b)
        declName shape) mctx mref cctx cref w₁ r w₂ ∧ JQC O (D + 1) w₁ ∧ JQC O (D + 1) w₂ ∧
      ((∃ res, r = some res ∧ res = (m, d)) ∨
       (r = none ∧ ∃ (ci : ConstantInfo) (w₃ : Void IO.RealWorld),
          RunsTo (legacyTail
            (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b)
            declName [] false
            (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
              (structEnv tenv))) mctx mref cctx cref w₂ (m, d) w₃)) := by
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run, hw3⟩ :=
    core_reads_invA O hA hw hc hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hsplit⟩ :=
    synthesizeFromConst_machine_splitA O hA (htr_of_tele O hA T D envR)
      (fun c => childKeepsC_all_of_tele O T (D + 1) (by omega) mctx cctx hA c) old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hw9, hw10, hout⟩ := hsplit shape hshape
  refine ⟨envR, b, r, w9, w10, hrun, hw9, hw10, ?_⟩
  rcases hout with h | ⟨h0, w11, h1⟩
  · exact Or.inl h
  · exact Or.inr ⟨h0, _, w11, h1⟩

/-! ## MO2: the refined split (cause of `none`, the reads, the original end world)

Added AFTER the MO theorems above, which are kept unchanged (BUILT: mo2/mo3). -/

/-- `core_reads_invA` with the worlds LINKED (a copy of its proof; only the statement differs):
`getConstInfo` ends at `w2`, the `getEnv` read runs from that same `w2` and ends at `w3`, the body
`synthesizeFromConst …` runs from that same `w3` (`JQC O (D+1)`) and ends at `w4`. After `w4` the entry
runs its `finally` block (depth decrement, restores) up to the core's end world; that block is NOT
exposed (`RunsTo.try_finally` drops it), so `w4` is the body's end world, not the core's `w'`. -/
theorem core_reads_linkA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
        mctx mref cctx cref w3 (M, Dg) w4 ∧ JQC O (D + 1) w3 := by
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
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (0 + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (0 + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, hget, henv, h, hw⟩
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
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, hget, henv, h, hw⟩

/-- **Where `synthesizeMachineCertified` returned `none`.** From a `JQC O n` world, a run of the machine
synthesis that returned `none` ran the harness `synthesizeMixedCertified` (world `w` → `wh`, kept `JQC`),
and then EITHER `closeLets` returned `none` (pure; `w' = wh`), OR `closeLets` was `some t'`, there are
calls, and the closing returned `none`: `closeInstsM` (`instFields` empty) or `closeInstsGM`
(`instFields` non-empty), each as the actual run from `wh` to the end world `w'`. Nothing says WHICH
of these occurs for a given input; `closeInsts*` returning `none` is not analysed further (not
needed: no `ChildrenRealA` for a `none`). -/
theorem synthesizeMachineCertified_noneSplitA (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {n : Nat} {tenv : Lean.Environment}
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref (JQC O n)
      (translateExprToWire tenv e hint top named))
    {b : Bool} {declName : Name} {shape : MachineShape} {w w' : Void IO.RealWorld}
    (hw : JQC O n w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w none w') :
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (wh : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) mctx mref cctx cref w (t, d₀) wh ∧ JQC O n wh ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w' = wh) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref wh none w') ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref wh none w')))) := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (mixed_keepsAP O hA (stableA_JQC O n) _ b declName
    shape.binders shape.body htr)) hw run
  dsimp only at hr
  refine ⟨t, d', w1, run, hw1, ?_⟩
  split at hr
  · rename_i t' hcl
    right
    split at hr
    · have eq := RunsTo.pure_eq hr
      cases eq
    · rename_i hi
      have hne : shape.insts ≠ [] := by rw [hi]; exact List.cons_ne_nil _ _
      refine ⟨t', hcl, hne, ?_⟩
      split at hr
      · rename_i hf
        exact Or.inl ⟨hf, hr⟩
      · rename_i hf
        exact Or.inr ⟨by simpa using hf, hr⟩
  · rename_i hcl
    obtain ⟨_, rfl⟩ := RunsTo.pure_world hr
    exact Or.inl ⟨hcl, rfl⟩

/-- **The body of a machine-route run, refined.** As `synthesizeFromConst_machine_splitA`, with the
worlds linked: the first `getEnv` read runs from the start world `w` to `w₁`, the machine attempt runs
from THAT `w₁`, and the outcome carries the ORIGINAL run's end world `w'`:
(a) `some res`: after the attempt (world `w₂`) the body runs the profile log (`wl`) and then
`sparkleSubModuleCache.modify (·.insert declName res)` ending at `w'`, and returns `res = (m, d)`;
(b) `none`: the legacy tail itself runs from `w₂` to `(m, d)` and `w'`. -/
theorem synthesizeFromConst_machine_split2A (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {tenv : Lean.Environment} {b : Bool} {declName : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref (JQC O n)
      (translateExprToWire tenv e hint top named))
    (hchild : ∀ c, Keeps mctx mref cctx cref (JQC O n) (synthesizeChild c))
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : JQC O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n)
      (profLogIO b) declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w₁ : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR w₁ ∧ JQC O n w₁ ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ (r : Option Res) (w₂ : Void IO.RealWorld),
          RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b)
            declName shape) mctx mref cctx cref w₁ r w₂ ∧ JQC O n w₂ ∧
          ((∃ res, r = some res ∧ res = (m, d) ∧ ∃ wl : Void IO.RealWorld,
              RunsTo (show MetaM Unit from profLogIO b
                s!"[profile] synthesizeCombinational {declName} machine certified front end")
                mctx mref cctx cref w₂ () wl ∧
              RunsTo (sparkleSubModuleCache.modify (·.insert declName res) : MetaM Unit)
                mctx mref cctx cref wl () w') ∨
           (r = none ∧ RunsTo (legacyTail
              (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b)
              declName [] false ci) mctx mref cctx cref w₂ (m, d) w')) := by
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
  have hw3 := triple_runs (keeps_iff.mp (machineCert_keepsAP O hA (stableA_JQC O n) _ b declName
    htr hchild (fun _ h => h.1.2.1) shape)) hw1 hmach
  refine ⟨r, w3, hmach, hw3, ?_⟩
  cases r with
  | none => exact Or.inr ⟨rfl, hr⟩
  | some res =>
    dsimp only at hr
    obtain ⟨_, wl, hlog, hr⟩ := RunsTo.bind hr
    obtain ⟨_, wm, hmod, hr⟩ := RunsTo.bind hr
    obtain ⟨he, rfl⟩ := RunsTo.pure_world hr
    exact Or.inl ⟨res, rfl, he.symm, wl, hlog, hmod⟩

/-- **`core_machine_outcomeA'`: the refined machine outcome split.** As `core_machine_outcomeA`, with
(1) the actual reads kept and LINKED: `getConstInfo declName` returns `ci` (`w₁ → w₂`), the `getEnv`
read returning `tenv` (the translator's environment) runs from that `w₂` to `w₃`, the body runs from
that `w₃` (`JQC O (D+1)`), whose first step is a second `getEnv` read (`envR'`, `w₃ → w₄`), and the
machine attempt starts at that `w₄`; the attempted `shape` is the machine shape of `ci`'s entry constant
at `structEnv envR'`;
(2) the cause of a `none`: case (b) is split by where `synthesizeMachineCertified` returned `none`
(harness world `wh`; `closeLets` pure `none`; `closeInstsM`; `closeInstsGM`), the harness and closing
runs kept;
(3) the legacy tail's run ends at the BODY's end world `w₅` (case (b)), and in case (a) the steps
between the machine result and `w₅` are the profile log and the cache insert
`sparkleSubModuleCache.modify (·.insert declName res)`. `w₅` is the end world of the body
(`synthesizeFromConst`), NOT the core's `w'`: the entry's `finally` block runs after it (and is not
exposed — OPEN, would need `RunsTo.try_finally` strengthened).
Machine (a) and legacy (b) results are NOT shown to mean the same; not runtime fit; legacy semantic
preservation OPEN. No `MachineClosesAtA`, no input guard. -/
theorem core_machine_outcomeA' (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
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
  obtain ⟨b, envR, ci, w1, w2, w3, w4, get, henv, run, hw3⟩ :=
    core_reads_linkA O hA hw hc hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  have htrD := htr_of_tele O hA T D envR
  obtain ⟨envR', wA, henv', hwA, hsplit⟩ :=
    synthesizeFromConst_machine_split2A O hA htrD
      (fun c => childKeepsC_all_of_tele O T (D + 1) (by omega) mctx cctx hA c) old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w6, hrun, hw6, hout⟩ := hsplit shape hshape
  refine ⟨envR, b, ci, envR', w1, w2, w3, wA, w4, w6, r, get, henv, hw3, henv', hshape, hrun,
    hwA, hw6, ?_⟩
  rcases hout with h | ⟨hn, htail⟩
  · exact Or.inl h
  · subst hn
    obtain ⟨t, d₀, wh, hh, hwh, hcase⟩ :=
      synthesizeMachineCertified_noneSplitA O hA htrD hwA hrun
    exact Or.inr ⟨rfl, htail, t, d₀, wh, hh, hwh, hcase⟩

end Tools.ShippingMachineOutcomeA
