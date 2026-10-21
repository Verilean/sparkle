import Tools.ShippingChildRunAMain
-- BUILT (unit MO): mo2 exit 0 (mo1 exit 1: missing opens); audit mo3 exit 0 (axioms propext, Classical.choice, Quot.sound).
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

end Tools.ShippingMachineOutcomeA
