import Tools.ShippingCoreSoundness

/-! # Front-end normalisation: the entry constant

The synthesis entry does not hand `synthesizeFromConst` the declaration it
read but its ENTRY CONSTANT (`entryConst`): the declaration itself whenever a
certified gate accepts it, and the declaration with its user definitions
unfolded (`userInliner`, a pure function of the environment the run reads)
when the original misses both gates and the unfolding passes one.

Every family theorem is a statement about `synthesizeFromConst` on a constant,
so it applies to the entry constant verbatim.  This file states that:

* `synthesizeCombinationalCore_entry_sound` — the whole bundle (all family
  contracts and the fragment outcome) at the entry constant of the run;
* `EntryDefines` — the run boundary "the entry constant of this run has value
  `v`", with `EntryDefines.of_env` (a gate-accepted declaration: it is
  `EnvDefines`) and `EntryDefines.of_inline` (an unfolded one: `EnvDefines`
  plus what the run's environment unfolds the value to);
* entry-constant endpoints for the unified combinational family and the
  feedback register, with the same conclusions as their `_of_env` twins.

The unfolding itself is NOT reasoned about: the theorems speak about the
value the entry constant has.  That the unfolded value means what the source
declaration means is Lean's own delta/beta, checked per declaration by the
kernel (`rfl` between the declaration and the denotation of the quoted term). -/

namespace Tools.ShippingInlineSoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingEntrySoundness Tools.ShippingPostSoundness
open Tools.ShippingCoreSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedExecutionSoundness
open Tools.ShippingMixedSourceBridge
open Tools.ShippingMixedPrintSoundness (mixedShape_positive)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingVectorMuxSoundness
open Tools.ShippingRegisterSoundness
open Tools.ShippingMemoryEntrySoundness
open Tools.ShippingInstanceEntrySoundness

/-- **The entry-constant boundary.** In this run, the constant the entry
hands on — computed by `entryConst` from the declaration and the environment
the run reads — is a definition with value `v`. -/
def EntryDefines (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (v : Lean.Expr) : Prop :=
  ∀ w1 ci w2 w5 envR w6,
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    ∃ d : DefinitionVal,
      entryConst true false [] ci (instancePredicate envR) (userInliner envR) = .defnInfo d ∧
        d.value = v

/-- A declaration the mixed gate accepts as read: the entry-constant boundary
is `EnvDefines`. -/
theorem EntryDefines.of_env {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {declName : Name}
    {v : Lean.Expr}
    (env : EnvDefines mctx mref cctx cref declName v)
    (gate : ∀ d : DefinitionVal, d.value = v → ∀ isInst,
      (mixedCertifiedShape? false [] (.defnInfo d) isInst).isSome = true) :
    EntryDefines mctx mref cctx cref declName v := by
  intro w1 ci w2 w5 envR w6 get _
  obtain ⟨d, rfl, hv⟩ := env w1 ci w2 get
  refine ⟨d, ?_, hv⟩
  have h := gate d hv (instancePredicate envR)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
  exact entryConst_mixed hr

/-- An unfolded declaration: `EnvDefines` for the declaration as written,
plus what every environment the run reads does with that value — it unfolds
it to `v'`, its gates miss the original and one accepts the unfolding. -/
theorem EntryDefines.of_inline {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {declName : Name}
    {v v' : Lean.Expr}
    (env : EnvDefines mctx mref cctx cref declName v)
    (inline : ∀ w5 envR w6,
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
      ∀ d : DefinitionVal, d.value = v →
        userInliner envR v = v' ∧
        certifiedShape? false [] (.defnInfo d) = none ∧
        mixedCertifiedShape? false [] (.defnInfo d) (instancePredicate envR) = none ∧
        ((certifiedShape? false [] (.defnInfo { d with value := v' })).isSome = true ∨
          (mixedCertifiedShape? false [] (.defnInfo { d with value := v' })
            (instancePredicate envR)).isSome = true)) :
    EntryDefines mctx mref cctx cref declName v' := by
  intro w1 ci w2 w5 envR w6 get henv
  obtain ⟨d, rfl, hv⟩ := env w1 ci w2 get
  obtain ⟨hinl, old, miss, hit⟩ := inline w5 envR w6 henv d hv
  have hc : inlinedConst (userInliner envR) (.defnInfo d) =
      .defnInfo { d with value := v' } := by
    simp only [inlinedConst, hv, hinl]
  refine ⟨{ d with value := v' }, ?_, rfl⟩
  rw [entryConst_inlined old miss (by rw [hc]; exact hit), hc]

/-- **The bundle at the entry constant.** One successful run of the real
entry satisfies the fragment outcome and every family contract for the
constant the entry handed on — the declaration as read, or its unfolding. -/
theorem synthesizeCombinationalCore_entry_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w') :
    ∃ (ci : ConstantInfo) (envR : Environment) (w1 w2 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      (entryConst true false [] ci (instancePredicate envR) (userInliner envR) = ci ∨
        entryConst true false [] ci (instancePredicate envR) (userInliner envR) =
          inlinedConst (userInliner envR) ci) ∧
      CertifiedOutcome
        (entryConst true false [] ci (instancePredicate envR) (userInliner envR)) m ∧
      ∀ bs body,
        certifiedShape? false []
          (entryConst true false [] ci (instancePredicate envR) (userInliner envR)) = none →
        mixedCertifiedShape? false []
          (entryConst true false [] ci (instancePredicate envR) (userInliner envR))
          (instancePredicate envR) = some (bs, body) →
        ShippingPreserves declName bs body m ∧
        InstancePreserves declName bs body m d ∧
        Instance1Preserves declName bs body m d ∧
        InstanceNPreserves declName bs body m d ∧
        InstanceGPreserves declName bs body m d ∧
        ProjInstancePreserves declName bs body m d ∧
        Tools.ShippingHierTermSoundness.HierConePreserves declName bs body m := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  refine ⟨ci, envR, w1, w2, w5, w6, get, henv, entryConst_cases _ _ _,
    synthesizeFromConst_sound run.mreturns, fun bs body old shape => ?_⟩
  exact ⟨⟨synthesizeFromConst_mixed_sound old shape run.mreturns,
      synthesizeFromConst_term_sound old shape run.mreturns,
      synthesizeFromConst_vector_sound old shape run.mreturns,
      synthesizeFromConst_register_sound old shape run.mreturns,
      synthesizeFromConst_registerEnable_sound old shape run.mreturns,
      synthesizeFromConst_loopRegister_sound old shape run.mreturns,
      synthesizeFromConst_register2_sound old shape run.mreturns,
      synthesizeFromConst_cdo_sound old shape run.mreturns,
      synthesizeFromConst_cdo2_sound old shape run.mreturns,
      synthesizeFromConst_memory_sound old shape run.mreturns,
      synthesizeFromConst_memoryCone_sound old shape run.mreturns⟩,
    synthesizeFromConst_instance_sound old shape run.mreturns,
    synthesizeFromConst_instance1_sound old shape run.mreturns,
    synthesizeFromConst_instanceN_sound old shape run.mreturns,
    synthesizeFromConst_instanceG_sound old shape run.mreturns,
    synthesizeFromConst_instanceProj_sound old shape run.mreturns,
    Tools.ShippingHierTermSoundness.synthesizeFromConst_hierCone_sound old shape
      run.mreturns⟩

/-! ## Entry-constant endpoints

The `_of_env` endpoints with `EnvDefines` replaced by `EntryDefines`: same
premises on the value, same conclusions. -/

/-- Source-to-RTL execution for the unified combinational domain at the real
synthesis entry, for the entry constant. -/
theorem execution_source_of_entry {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : Sparkle.Core.Domain.DomainConfig}
        (bools : Nat → Sparkle.Core.Signal.Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      Tools.ShippingMixedSourceBridge.SourceInputs declName bs ids cache (fun j => (bools j).val tick)
        (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        (pack srt ((Tools.ShippingUnifiedSource.denote (fun j => bools (bpos j))
          (fun j w => bits (vpos j) w) e).val tick)).toNat := by
  obtain ⟨raw, design', world, core, post⟩ := synthesizeCombinational_reads hr
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads core
  obtain ⟨d, hd, definition⟩ := entry w1 ci w2 w5 envR w6 get henv
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have mixedGate := term_gate (d := d)
    (by rw [definition]; exact peel) he hb hv
  exact source_signals
    (term_execution (synthesizeFromConst_term_sound oldGate (mixedGate _) run.mreturns)
      (mixedShape_positive (mixedGate (fun _ => false))) post) he hb hv

/-- Feedback-register step endpoint at the real core entry, for the entry
constant. -/
theorem loopRegister_step_of_entry {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value instE : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, loopRegisterE (inputExpr bs.length dpos)
      (inputExpr (bs.length + 1) dpos) instE w v
      (quote (inputExpr (bs.length + 1) dpos) (fun j => inputExpr (bs.length + 1) (bpos j))
        (fun j => if j = kv then .bvar 0 else inputExpr (bs.length + 1) (vpos j)) e)))
    (hdp : dpos < bs.length)
    (hself : vw kv = w) (he : e.WF kb (kv + 1) vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ w →
      weOf m r = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun j => bools (bpos j))
            (fun j n => if j = kv then BitVec.ofNat n (env0 r) else bits (vpos j) n)
            e).toNat)], mems) ∧
        envF "out" = env0 r := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  obtain ⟨d, hd, definition⟩ := entry w1 ci w2 w5 envR w6 get henv
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have hdom : ((inputExpr bs.length dpos).isFVar || (inputExpr bs.length dpos).isBVar) = true := by
    simp only [Tools.ShippingMixedSourceBridge.inputExpr]
    rfl
  have mixedGate := loopRegister_term_gate (d := d)
    (by rw [definition]; exact peel) hdom hself hvlt he hb hvp
  exact loopRegister_source
    (synthesizeFromConst_loopRegister_sound oldGate (mixedGate _) run.mreturns)
    rfl hdp hself he hvlt hb hvp

/-- Feedback-register whole-trace endpoint at the real core entry, for the
entry constant. -/
theorem loopRegister_run_of_entry {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value instE : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, loopRegisterE (inputExpr bs.length dpos)
      (inputExpr (bs.length + 1) dpos) instE w v
      (quote (inputExpr (bs.length + 1) dpos) (fun j => inputExpr (bs.length + 1) (bpos j))
        (fun j => if j = kv then .bvar 0 else inputExpr (bs.length + 1) (vpos j)) e)))
    (hdp : dpos < bs.length)
    (hself : vw kv = w) (he : e.WF kb (kv + 1) vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Nat → Bool) (bits : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat) (S : Nat → Nat),
      (∀ t stv, SourceInputs declName bs ids cache (bools (k - 1 - t)) (bits (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r < 2 ^ w →
      S 0 = st0 r →
      (∀ j, j + 1 ≤ k → S (j + 1) = (eval (fun i => bools j (bpos i))
        (fun i n => if i = kv then BitVec.ofNat n (S j) else bits j (vpos i) n) e).toNat) →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j := by
  obtain ⟨ids, nd, len, cache, r, H⟩ :=
    loopRegister_step_of_entry hr entry old peel hdp hself he hvlt hb hvp
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro bools bits mems k seed st0 S hseed hst0 hS0 hSs
  apply trace_of_cycles_inv (P := fun s => s < 2 ^ w)
    (F := fun t s => (eval (fun i => bools (k - 1 - t) (bpos i))
      (fun i n => if i = kv then BitVec.ofNat n s else bits (k - 1 - t) (vpos i) n) e).toNat)
    ?_ ?_ k st0 S hst0 hS0 ?_
  · intro t stv hP
    obtain ⟨hsrc, hrst, hread⟩ := hseed t stv
    obtain ⟨-, -, -, envF, hstep, hout⟩ :=
      H (bools (k - 1 - t)) (bits (k - 1 - t)) (seed t stv) mems hsrc hrst
        (by rw [hread]; exact hP)
    refine ⟨envF, ?_, by rw [hout, hread]⟩
    rw [hread] at hstep
    exact hstep
  · intro t s hP
    exact BitVec.isLt _
  · intro j hj
    rw [hSs j hj]
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    rw [hidx]


end Tools.ShippingInlineSoundness
