import Tools.ShippingRegisterSoundness
import Tests.Compiler.ShippingMixedExecutionTest
import Sparkle.Core.CircuitDo

/-! S4 register foundation tests: a real `Signal.register` declaration over
the unified combinational domain, its gate acceptance, cycle/trace regression
against the actual `stepModule` semantics, and the general endpoint
instantiated with a standard-axioms audit. -/
namespace Sparkle.Tests.Compiler.ShippingRegisterSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingUnifiedSource
open Tools.ShippingMixedSourceBridge Tools.ShippingRegisterSoundness
open Tools.ShippingMixedExecutionSoundness

/-- An 8-bit accumulator-style register whose next value is a mux/arithmetic
cone over the inputs. The only initialization is the t = 0 value. -/
def regAcc {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.register 3#8 (Signal.mux c a b + a)

def regAccTerm : Term (.bits 8) := .binary .add
  (.mux (.boolInput 0) (.bitsInput 8 0) (.bitsInput 8 1)) (.bitsInput 8 0)

theorem regAcc_wf : regAccTerm.WF 1 2 (fun _ => 8) := by simp [regAccTerm, Term.WF]

/-- The register source is the library register over the term's denotation. -/
theorem regAcc_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    Signal.register 3#8 (denote bi vi regAccTerm) = regAcc (bi 0) (vi 0 8) (vi 1 8) := rfl

#def_decl_value regAccValue of regAcc
def regAccBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
theorem regAcc_peel : mixedGatePeel regAccValue = some (regAccBinders,
    registerE (inputExpr regAccBinders.length 0) 8 3
      (quote (inputExpr regAccBinders.length 0)
        (fun _ => inputExpr regAccBinders.length 1)
        (fun j => inputExpr regAccBinders.length (j + 2)) regAccTerm)) := rfl

/-- The general register endpoint on the real declaration: each cycle of the
raw synthesized module observes the current register value on `out` and steps
the register by the source cone's value, with reset held low. -/
theorem regAcc_step {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``regAcc [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``regAcc regAccValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = regAccBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs ``regAcc regAccBinders ids cache bools bits env0 →
      env0 "rst" = 0 →
      weOf m r = 8 ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun _ => bools 1)
            (fun j n => bits (j + 2) n) regAccTerm).toNat)], mems) ∧
        envF "out" = env0 r := by
  apply register_step_of_env (kb := 1) (kv := 2) (vw := fun _ => 8)
    (bpos := fun _ => 1) (vpos := fun j => j + 2) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) regAcc_peel
    (by simp [regAccBinders]) regAcc_wf (by decide)
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-- An enabled register: capture the mux/arithmetic cone when `en` holds,
else hold the current value. Exercises the fixed hold semantics. -/
def regHold {dom : DomainConfig} (en c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.registerWithEnable 5#8 en (Signal.mux c a b + a)

def regHoldTerm : Term (.bits 8) := .binary .add
  (.mux (.boolInput 1) (.bitsInput 8 0) (.bitsInput 8 1)) (.bitsInput 8 0)

theorem regHoldTerm_wf : regHoldTerm.WF 2 2 (fun _ => 8) := by simp [regHoldTerm, Term.WF]
theorem regHoldEn_wf : (Term.boolInput 0).WF 2 2 (fun _ => 8) := by simp [Term.WF]

#def_decl_value regHoldValue of regHold
def regHoldBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`en, .bool), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
theorem regHold_peel : mixedGatePeel regHoldValue = some (regHoldBinders,
    registerEnableE (inputExpr regHoldBinders.length 0) 8 5
      (quote (inputExpr regHoldBinders.length 0)
        (fun j => inputExpr regHoldBinders.length (j + 1))
        (fun j => inputExpr regHoldBinders.length (j + 3)) (.boolInput 0))
      (quote (inputExpr regHoldBinders.length 0)
        (fun j => inputExpr regHoldBinders.length (j + 1))
        (fun j => inputExpr regHoldBinders.length (j + 3)) regHoldTerm)) := rfl

/-- The enabled-register endpoint on the real declaration. -/
theorem regHold_step {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``regHold [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``regHold regHoldValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = regHoldBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs ``regHold regHoldBinders ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ 8 →
      weOf m r = 8 ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, if bools 1 then (eval (fun j => bools (j + 1))
            (fun j n => bits (j + 3) n) regHoldTerm).toNat else env0 r)], mems) ∧
        envF "out" = env0 r := by
  apply Tools.ShippingRegisterSoundness.registerEnable_step_of_env (kb := 2) (kv := 2)
    (vw := fun _ => 8) (bpos := fun j => j + 1) (vpos := fun j => j + 3)
    (en := .boolInput 0) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) regHold_peel
    (by simp [regHoldBinders]) regHoldEn_wf regHoldTerm_wf (by decide)
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`en, rfl⟩
    · exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-- A feedback register: the next-state cone reads the register back through
the loop binder (`Signal.loop`), muxed against an input and accumulated. -/
def accLoop {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.loop (fun s => Signal.register 0#8 (Signal.mux c s a + b))

/-- The cone as a unified term: the loop binder is source input index 2. -/
def accLoopTerm : Term (.bits 8) := .binary .add
  (.mux (.boolInput 0) (.bitsInput 8 2) (.bitsInput 8 0)) (.bitsInput 8 1)

theorem accLoopTerm_wf : accLoopTerm.WF 1 3 (fun _ => 8) := by simp [accLoopTerm, Term.WF]

#def_decl_value accLoopValue of accLoop
def accLoopBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
def accLoopInst : Lean.Expr :=
  .app (.const ``BitVec.instInhabited []) (Tools.ShippingEntrySoundness.natE 8)
theorem accLoop_peel : mixedGatePeel accLoopValue = some (accLoopBinders,
    Tools.ShippingRegisterSoundness.loopRegisterE
      (inputExpr accLoopBinders.length 0) (inputExpr (accLoopBinders.length + 1) 0)
      accLoopInst 8 0
      (quote (inputExpr (accLoopBinders.length + 1) 0)
        (fun _ => inputExpr (accLoopBinders.length + 1) 1)
        (fun j => if j = 2 then .bvar 0 else inputExpr (accLoopBinders.length + 1) (j + 2))
        accLoopTerm)) := rfl

/-- The feedback endpoint on the real declaration: each cycle observes the
register on `out` and steps by the cone at the current state. -/
theorem accLoop_step {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``accLoop [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``accLoop accLoopValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = accLoopBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs ``accLoop accLoopBinders ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ 8 →
      weOf m r = 8 ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun _ => bools 1)
            (fun j n => if j = 2 then BitVec.ofNat n (env0 r) else bits (j + 2) n)
            accLoopTerm).toNat)], mems) ∧
        envF "out" = env0 r := by
  apply Tools.ShippingRegisterSoundness.loopRegister_step_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 8) (bpos := fun _ => 1) (vpos := fun j => j + 2) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) accLoop_peel
    (by simp [accLoopBinders]) rfl accLoopTerm_wf (by decide)
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-- The full trace endpoint on the real declaration: the compiled module's
`runModule` trace observes exactly the source `Signal.loop` register stream,
for every admissible seeding discipline, from state 0. -/
theorem accLoop_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``accLoop [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``accLoop accLoopValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = accLoopBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat),
      (∀ t stv, SourceInputs ``accLoop accLoopBinders ids cache
          (fun i => (bools i).val (k - 1 - t)) (fun i n => (bits i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r = 0 →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((accLoop (bools 1) (bits 2 8) (bits 3 8)).val j).toNat := by
  have packaged := Tools.ShippingRegisterSoundness.loopRegister_run_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 8) (bpos := fun _ => 1) (vpos := fun j => j + 2) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) accLoop_peel
    (by simp [accLoopBinders]) rfl accLoopTerm_wf (by decide)
    (by
      intro j hj
      have h : j = 0 := by omega
      subst h
      exact ⟨`c, rfl⟩)
    (by
      intro j hj
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl
      · exact ⟨`a, rfl⟩
      · exact ⟨`b, rfl⟩)
  obtain ⟨ids, nd, len, cache, r, H⟩ := packaged
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro D bools bits mems k seed st0 hseed hst0
  -- The source stream: loop_register_val gives the recurrence pointwise.
  have hcone : ∀ (s₁ s₂ : Signal D (BitVec 8)) (t : Nat), s₁.val t = s₂.val t →
      (Signal.mux (bools 1) s₁ (bits 2 8) + bits 3 8).val t =
      (Signal.mux (bools 1) s₂ (bits 2 8) + bits 3 8).val t := by
    intro s1 s2 t h
    show (if (bools 1).val t then s1.val t else (bits 2 8).val t) + (bits 3 8).val t = _
    rw [h]
    rfl
  have hv := Tools.ShippingRegisterSoundness.loop_register_val (0#8)
    (fun s => Signal.mux (bools 1) s (bits 2 8) + bits 3 8) hcone
  have hacc : accLoop (bools 1) (bits 2 8) (bits 3 8) =
      Signal.loop (fun s => Signal.register 0#8
        (Signal.mux (bools 1) s (bits 2 8) + bits 3 8)) := rfl
  apply H (fun wall i => (bools i).val wall) (fun wall i n => (bits i n).val wall)
    mems k seed st0
    (fun j => ((accLoop (bools 1) (bits 2 8) (bits 3 8)).val j).toNat)
    hseed (by rw [hst0]; decide)
  · rw [hst0, hacc]
    rw [show (Signal.loop (fun s => Signal.register 0#8
      (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))).val 0 = 0#8 from hv.1]
    rfl
  · intro j hj
    rw [hacc]
    rw [show (Signal.loop (fun s => Signal.register 0#8
      (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))).val (j + 1) =
      (Signal.mux (bools 1) (Signal.loop (fun s => Signal.register 0#8
        (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))) (bits 2 8) + bits 3 8).val j
      from hv.2 j]
    show ((if (bools 1).val j then _ else (bits 2 8).val j) + (bits 3 8).val j).toNat = _
    cases hc : (bools 1).val j <;>
      simp [eval, accLoopTerm, Tools.ShippingScalarSoundness.Binary.apply, hc,
        BitVec.ofNat_toNat]

/-- The full trace endpoint for the plain register: the compiled module's
`runModule` trace observes exactly the source `Signal.register` stream. -/
theorem regAcc_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``regAcc [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``regAcc regAccValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = regAccBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat),
      (∀ t stv, SourceInputs ``regAcc regAccBinders ids cache
          (fun i => (bools i).val (k - 1 - t)) (fun i n => (bits i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r = 3 →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((regAcc (bools 1) (bits 2 8) (bits 3 8)).val j).toNat := by
  have packaged := Tools.ShippingRegisterSoundness.register_run_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 8) (bpos := fun _ => 1) (vpos := fun j => j + 2) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) regAcc_peel
    (by simp [regAccBinders]) regAcc_wf (by decide)
    (by
      intro j hj
      have h : j = 0 := by omega
      subst h
      exact ⟨`c, rfl⟩)
    (by
      intro j hj
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl
      · exact ⟨`a, rfl⟩
      · exact ⟨`b, rfl⟩)
  obtain ⟨ids, nd, len, cache, r, H⟩ := packaged
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro D bools bits mems k seed st0 hseed hst0
  apply H (fun wall i => (bools i).val wall) (fun wall i n => (bits i n).val wall)
    mems k seed st0
    (fun j => ((regAcc (bools 1) (bits 2 8) (bits 3 8)).val j).toNat)
    hseed
  · rw [hst0]
    rfl
  · intro j hj
    show ((Signal.mux (bools 1) (bits 2 8) (bits 3 8) + bits 2 8).val j).toNat = _
    show ((if (bools 1).val j then (bits 2 8).val j else (bits 3 8).val j)
      + (bits 2 8).val j).toNat = _
    cases hc : (bools 1).val j <;>
      simp [eval, regAccTerm, Tools.ShippingScalarSoundness.Binary.apply, hc]

/-- The full trace endpoint for the enabled register: the compiled module's
`runModule` trace observes exactly the source capture/hold stream. -/
theorem regHold_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``regHold [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``regHold regHoldValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = regHoldBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat),
      (∀ t stv, SourceInputs ``regHold regHoldBinders ids cache
          (fun i => (bools i).val (k - 1 - t)) (fun i n => (bits i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r = 5 →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((regHold (bools 1) (bools 2) (bits 3 8) (bits 4 8)).val j).toNat := by
  have packaged := Tools.ShippingRegisterSoundness.registerEnable_run_of_env (kb := 2)
    (kv := 2) (vw := fun _ => 8) (bpos := fun j => j + 1) (vpos := fun j => j + 3)
    (en := .boolInput 0) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) regHold_peel
    (by simp [regHoldBinders]) regHoldEn_wf regHoldTerm_wf (by decide)
    (by
      intro j hj
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl
      · exact ⟨`en, rfl⟩
      · exact ⟨`c, rfl⟩)
    (by
      intro j hj
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl
      · exact ⟨`a, rfl⟩
      · exact ⟨`b, rfl⟩)
  obtain ⟨ids, nd, len, cache, r, H⟩ := packaged
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro D bools bits mems k seed st0 hseed hst0
  apply H (fun wall i => (bools i).val wall) (fun wall i n => (bits i n).val wall)
    mems k seed st0
    (fun j => ((regHold (bools 1) (bools 2) (bits 3 8) (bits 4 8)).val j).toNat)
    hseed (by rw [hst0]; decide)
  · rw [hst0]
    rfl
  · intro j hj
    change (if (bools 1).val j = true then
        (Signal.mux (bools 2) (bits 3 8) (bits 4 8) + bits 3 8).val j
      else (regHold (bools 1) (bools 2) (bits 3 8) (bits 4 8)).val j).toNat =
      if (bools 1).val j = true then _ else _
    cases hc : (bools 1).val j
    · simp [hc]
    · simp only [hc, if_pos rfl]
      show ((if (bools 2).val j then (bits 3 8).val j else (bits 4 8).val j)
        + (bits 3 8).val j).toNat = _
      cases hc2 : (bools 2).val j <;>
        simp [eval, regHoldTerm, Tools.ShippingScalarSoundness.Binary.apply, hc2]

/-- A two-stage shift chain: the mux/arithmetic cone feeds the inner
register, whose output feeds the outer register. -/
def regChain {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.register 1#8 (Signal.register 2#8 (Signal.mux c a b + a))

#def_decl_value regChainValue of regChain
def regChainBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
theorem regChain_peel : mixedGatePeel regChainValue = some (regChainBinders,
    registerE (inputExpr regChainBinders.length 0) 8 1
      (registerE (inputExpr regChainBinders.length 0) 8 2
        (quote (inputExpr regChainBinders.length 0)
          (fun _ => inputExpr regChainBinders.length 1)
          (fun j => inputExpr regChainBinders.length (j + 2)) regAccTerm))) := rfl

/-- The two-stage chain endpoint on the real declaration: each cycle
observes the outer register, shifts the inner value outward, and steps the
inner register by the source cone. -/
theorem regChain_step {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``regChain [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``regChain regChainValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = regChainBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r1 r2 : String), r1 ≠ r2 ∧
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs ``regChain regChainBinders ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r2 < 2 ^ 8 →
      weOf m r1 = 8 ∧ weOf m r2 = 8 ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r2, (eval (fun _ => bools 1)
            (fun j n => bits (j + 2) n) regAccTerm).toNat), (r1, env0 r2)], mems) ∧
        envF "out" = env0 r1 := by
  apply Tools.ShippingRegisterSoundness.register2_step_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 8) (bpos := fun _ => 1) (vpos := fun j => j + 2) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) regChain_peel
    (by simp [regChainBinders]) regAcc_wf (by decide) (by decide)
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-- The full trace endpoint for the chain: the compiled module's `runModule`
trace observes exactly the nested source `Signal.register` streams. -/
theorem regChain_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``regChain [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``regChain regChainValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = regChainBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r1 r2 : String), r1 ≠ r2 ∧
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat),
      (∀ t stv, SourceInputs ``regChain regChainBinders ids cache
          (fun i => (bools i).val (k - 1 - t)) (fun i n => (bits i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧
          seed t stv r1 = stv r1 ∧ seed t stv r2 = stv r2) →
      st0 r1 = 1 → st0 r2 = 2 →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((regChain (bools 1) (bits 2 8) (bits 3 8)).val j).toNat := by
  have packaged := Tools.ShippingRegisterSoundness.register2_run_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 8) (bpos := fun _ => 1) (vpos := fun j => j + 2) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) regChain_peel
    (by simp [regChainBinders]) regAcc_wf (by decide) (by decide)
    (by
      intro j hj
      have h : j = 0 := by omega
      subst h
      exact ⟨`c, rfl⟩)
    (by
      intro j hj
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl
      · exact ⟨`a, rfl⟩
      · exact ⟨`b, rfl⟩)
  obtain ⟨ids, nd, len, cache, r1, r2, hne, H⟩ := packaged
  refine ⟨ids, nd, len, cache, r1, r2, hne, ?_⟩
  intro D bools bits mems k seed st0 hseed hst01 hst02
  apply H (fun wall i => (bools i).val wall) (fun wall i n => (bits i n).val wall)
    mems k seed st0
    (fun j => ((regChain (bools 1) (bits 2 8) (bits 3 8)).val j).toNat)
    (fun j => ((Signal.register 2#8
      (Signal.mux (bools 1) (bits 2 8) (bits 3 8) + bits 2 8)).val j).toNat)
    hseed (by rw [hst02]; decide)
  · rw [hst01]
    rfl
  · rw [hst02]
    rfl
  · intro j hj
    show ((Signal.mux (bools 1) (bits 2 8) (bits 3 8) + bits 2 8).val j).toNat = _
    show ((if (bools 1).val j then (bits 2 8).val j else (bits 3 8).val j)
      + (bits 2 8).val j).toNat = _
    cases hc : (bools 1).val j <;>
      simp [eval, regAccTerm, Tools.ShippingScalarSoundness.Binary.apply, hc]
  · intro j hj
    rfl

/-- Two cross-coupled registers as a two-slot `circuit do`: a swap/accumulate
pair whose cones each read both registers. -/
def cdo2X {dom : DomainConfig} (c : Signal dom Bool) (a : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) :=
  circuit do
    let x ← Signal.reg (1#8)
    let y ← Signal.reg (2#8)
    x <~ Signal.mux c (y : Signal dom (BitVec 8)) a
    y <~ Signal.mux c (x : Signal dom (BitVec 8)) (y : Signal dom (BitVec 8)) + a
    return x

/-- The feedback accumulator written as a single-slot `circuit do`. -/
def cdoAcc {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) :=
  circuit do
    let r ← Signal.reg (3#8)
    r <~ Signal.mux c r a + b
    return r

/-- The same design as an explicit feedback register. -/
def cdoLoopAcc {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.loop (fun s => Signal.register 3#8 (Signal.mux c s a + b))

/-- Source identification: the `circuit do` output stream IS the explicit
feedback-register stream (definitional unfolding of the reduced single-slot
`runCircuitH` state plus the `map_fst_loop_register` anchor). -/
theorem cdoAcc_val {D : DomainConfig} (c : Signal D Bool) (a b : Signal D (BitVec 8))
    (t : Nat) : (cdoAcc c a b).val t = (cdoLoopAcc c a b).val t := by
  have hcone : ∀ (s₁ s₂ : Signal D (BitVec 8)) (j : Nat), s₁.val j = s₂.val j →
      (Signal.mux c s₁ a + b).val j = (Signal.mux c s₂ a + b).val j := by
    intro s1 s2 j h
    show (if c.val j then s1.val j else a.val j) + b.val j = _
    rw [h]
    rfl
  have hb : cdoAcc c a b = Signal.map Prod.fst (Signal.loop (fun live =>
      Sparkle.Core.Signal.bundle2
        (Signal.register 3#8 (Signal.mux c (Signal.map Prod.fst live) a + b))
        (Signal.pure ()))) := rfl
  rw [hb]
  exact Tools.ShippingRegisterSoundness.map_fst_loop_register 3#8
    (fun s => Signal.mux c s a + b) hcone t

#def_decl_value cdoAccValue of cdoAcc
def cdoAccBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
theorem cdoAcc_peel : mixedGatePeel cdoAccValue = some (cdoAccBinders,
    Tools.ShippingRegisterSoundness.cdoE `r
      (inputExpr cdoAccBinders.length 0) (inputExpr (cdoAccBinders.length + 1) 0)
      (inputExpr (cdoAccBinders.length + 2) 0) (inputExpr (cdoAccBinders.length + 3) 0) 8 3
      (quote (inputExpr (cdoAccBinders.length + 2) 0)
        (fun _ => inputExpr (cdoAccBinders.length + 2) 1)
        (fun j => if j = 2 then Tools.ShippingRegisterSoundness.readE
            (inputExpr (cdoAccBinders.length + 2) 0) 8 (.bvar 0)
          else inputExpr (cdoAccBinders.length + 2) (j + 2))
        accLoopTerm)) := rfl

/-- The general circuit-do endpoint on the real declaration: each cycle
observes the register on `out` and steps by the cone at the current state. -/
theorem cdoAcc_step {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``cdoAcc [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``cdoAcc cdoAccValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = cdoAccBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs ``cdoAcc cdoAccBinders ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ 8 →
      weOf m r = 8 ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun _ => bools 1)
            (fun j n => if j = 2 then BitVec.ofNat n (env0 r) else bits (j + 2) n)
            accLoopTerm).toNat)], mems) ∧
        envF "out" = env0 r := by
  apply Tools.ShippingRegisterSoundness.cdo_step_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 8) (bpos := fun _ => 1) (vpos := fun j => j + 2) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) cdoAcc_peel
    (by simp [cdoAccBinders]) rfl accLoopTerm_wf (by decide)
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-- The full trace endpoint for the circuit-do declaration: the compiled
`runModule` trace observes exactly the `circuit do` output stream. -/
theorem cdoAcc_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``cdoAcc [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``cdoAcc cdoAccValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = cdoAccBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat),
      (∀ t stv, SourceInputs ``cdoAcc cdoAccBinders ids cache
          (fun i => (bools i).val (k - 1 - t)) (fun i n => (bits i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r = 3 →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((cdoAcc (bools 1) (bits 2 8) (bits 3 8)).val j).toNat := by
  have packaged := Tools.ShippingRegisterSoundness.cdo_run_of_env (kb := 1) (kv := 2)
    (vw := fun _ => 8) (bpos := fun _ => 1) (vpos := fun j => j + 2) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) cdoAcc_peel
    (by simp [cdoAccBinders]) rfl accLoopTerm_wf (by decide)
    (by
      intro j hj
      have h : j = 0 := by omega
      subst h
      exact ⟨`c, rfl⟩)
    (by
      intro j hj
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl
      · exact ⟨`a, rfl⟩
      · exact ⟨`b, rfl⟩)
  obtain ⟨ids, nd, len, cache, r, H⟩ := packaged
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro D bools bits mems k seed st0 hseed hst0
  have hcone : ∀ (s₁ s₂ : Signal D (BitVec 8)) (t : Nat), s₁.val t = s₂.val t →
      (Signal.mux (bools 1) s₁ (bits 2 8) + bits 3 8).val t =
      (Signal.mux (bools 1) s₂ (bits 2 8) + bits 3 8).val t := by
    intro s1 s2 t h
    show (if (bools 1).val t then s1.val t else (bits 2 8).val t) + (bits 3 8).val t = _
    rw [h]
    rfl
  have hv := Tools.ShippingRegisterSoundness.loop_register_val (3#8)
    (fun s => Signal.mux (bools 1) s (bits 2 8) + bits 3 8) hcone
  have hacc : ∀ j, (cdoAcc (bools 1) (bits 2 8) (bits 3 8)).val j =
      (Signal.loop (fun s => Signal.register 3#8
        (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))).val j := fun j =>
    cdoAcc_val (bools 1) (bits 2 8) (bits 3 8) j
  apply H (fun wall i => (bools i).val wall) (fun wall i n => (bits i n).val wall)
    mems k seed st0
    (fun j => ((cdoAcc (bools 1) (bits 2 8) (bits 3 8)).val j).toNat)
    hseed (by rw [hst0]; decide)
  · rw [hst0, hacc 0]
    rw [show (Signal.loop (fun s => Signal.register 3#8
      (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))).val 0 = 3#8 from hv.1]
    rfl
  · intro j hj
    rw [hacc (j + 1), hacc j]
    rw [show (Signal.loop (fun s => Signal.register 3#8
      (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))).val (j + 1) =
      (Signal.mux (bools 1) (Signal.loop (fun s => Signal.register 3#8
        (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))) (bits 2 8) + bits 3 8).val j
      from hv.2 j]
    show ((if (bools 1).val j then _ else (bits 2 8).val j) + (bits 3 8).val j).toNat = _
    cases hc : (bools 1).val j <;>
      simp [eval, accLoopTerm, Tools.ShippingScalarSoundness.Binary.apply, hc,
        BitVec.ofNat_toNat]

open Sparkle.IR.AST in
run_cmd liftTermElabM do
  -- Gate acceptance and multi-cycle numeric regression on the raw module.
  let ci ← getConstInfo ``regAcc
  unless (mixedCertifiedShape? false [] ci).isSome do
    throwError "register source missed the extended gate"
  let (m, _) ← synthesizeCombinationalCore ``regAcc [] false
  -- Locate the emitted register statement.
  let regs := m.body.filterMap fun st => match st with
    | .register o _ (rstName, _) _ init => some (o, rstName, init)
    | _ => none
  let [(r, rstName, init)] := regs | throwError "expected exactly one register, got {regs.length}"
  unless rstName == "rst" && init == 3 do throwError "unexpected register fields"
  unless m.inputs.any (·.name == "clk") && m.inputs.any (·.name == "rst") do
    throwError "clock/reset ports missing"
  -- The zero-width pass is the identity on this sequential shape.
  let m' := Sparkle.IR.ZeroWidth.dropZeroWidthModule m
  unless m'.body == m.body do throwError "dropZeroWidth changed the sequential body"
  unless m'.wires == m.wires do throwError "dropZeroWidth changed the sequential wires"
  let we := Tools.ShippingEntrySoundness.weOf m
  -- Input traces: cycle t feeds (c, a, b); expected is the register recurrence.
  let ctrace := fun (t : Nat) => t % 2 == 1
  let atrace := fun (t : Nat) => (7 * t + 1) % 256
  let btrace := fun (t : Nat) => (13 * t + 5) % 256
  let mut state : Nat := 3  -- encodeInit 3 8
  let mut count : Nat := 0
  for t in List.range 12 do
    let env0 := fun (n : String) =>
      if n == "_gen_c" then (if ctrace t then 1 else 0)
      else if n == "_gen_a" then atrace t
      else if n == "_gen_b" then btrace t
      else if n == r then state
      else 0
    let some (envF, nexts, _) := stepModule we m.body env0 | throwError "stepModule failed at {t}"
    unless envF "out" == state do
      throwError "cycle {t}: out={envF "out"} expected register {state}"
    let expected := ((if ctrace t then BitVec.ofNat 8 (atrace t) else BitVec.ofNat 8 (btrace t))
      + BitVec.ofNat 8 (atrace t)).toNat
    let some (_, next) := nexts.find? (fun p => p.1 == r) | throwError "register next missing"
    unless next == expected do
      throwError "cycle {t}: next={next} expected {expected}"
    state := next
    count := count + 1
  unless count == 12 do throwError "register cycle count mismatch: {count}"
  -- Default-configuration evidence: the sequential (unvalidated) duplicate
  -- merge also preserves the 12-cycle trace here. Its PROOF remains open.
  let mm := Sparkle.IR.RegDedup.mergeDuplicates m'
  let regs2 := mm.body.filterMap fun st => match st with
    | .register o _ _ _ _ => some o
    | _ => none
  let [r2] := regs2 | throwError "merged module register count changed: {regs2.length}"
  let we2 := Tools.ShippingEntrySoundness.weOf mm
  let mut state2 : Nat := 3
  let mut count2 : Nat := 0
  for t in List.range 12 do
    let env0 := fun (n : String) =>
      if n == "_gen_c" then (if ctrace t then 1 else 0)
      else if n == "_gen_a" then atrace t
      else if n == "_gen_b" then btrace t
      else if n == r2 then state2
      else 0
    let some (envF, nexts, _) := stepModule we2 mm.body env0 |
      throwError "merged stepModule failed at {t}"
    unless envF "out" == state2 do
      throwError "merged cycle {t}: out={envF "out"} expected {state2}"
    let expected := ((if ctrace t then BitVec.ofNat 8 (atrace t) else BitVec.ofNat 8 (btrace t))
      + BitVec.ofNat 8 (atrace t)).toNat
    let some (_, next) := nexts.find? (fun p => p.1 == r2) |
      throwError "merged register next missing"
    unless next == expected do
      throwError "merged cycle {t}: next={next} expected {expected}"
    state2 := next
    count2 := count2 + 1
  unless count2 == 12 do throwError "merged register cycle count mismatch: {count2}"
  -- Enabled register: capture on en, hold across disabled stretches.
  let ciH ← getConstInfo ``regHold
  unless (mixedCertifiedShape? false [] ciH).isSome do
    throwError "enabled register missed the gate"
  let (mh, _) ← synthesizeCombinationalCore ``regHold [] false
  let regsH := mh.body.filterMap fun st => match st with
    | .register o _ _ _ init => some (o, init)
    | _ => none
  let [(rH, initH)] := regsH | throwError "expected one enabled register"
  let mh' := Sparkle.IR.ZeroWidth.dropZeroWidthModule mh
  unless mh'.body == mh.body && mh'.wires == mh.wires do
    throwError "dropZeroWidth changed the enabled-register module"
  unless initH == 5 do throwError "unexpected enable-register init"
  let weH := Tools.ShippingEntrySoundness.weOf mh
  let entrace := fun (t : Nat) => t % 3 == 0
  let mut stateH : Nat := 5
  let mut countH : Nat := 0
  for t in List.range 12 do
    let env0 := fun (n : String) =>
      if n == "_gen_en" then (if entrace t then 1 else 0)
      else if n == "_gen_c" then (if ctrace t then 1 else 0)
      else if n == "_gen_a" then atrace t
      else if n == "_gen_b" then btrace t
      else if n == rH then stateH
      else 0
    let some (envF, nexts, _) := stepModule weH mh.body env0 |
      throwError "enabled stepModule failed at {t}"
    unless envF "out" == stateH do
      throwError "enabled cycle {t}: out={envF "out"} expected {stateH}"
    let captured := ((if ctrace t then BitVec.ofNat 8 (atrace t) else BitVec.ofNat 8 (btrace t))
      + BitVec.ofNat 8 (atrace t)).toNat
    let expected := if entrace t then captured else stateH
    let some (_, next) := nexts.find? (fun p => p.1 == rH) |
      throwError "enabled register next missing"
    unless next == expected do
      throwError "enabled cycle {t}: next={next} expected {expected}"
    stateH := next
    countH := countH + 1
  unless countH == 12 do throwError "enabled register cycle count mismatch: {countH}"
  -- Feedback register: the cone reads the register back each cycle.
  let ciL ← getConstInfo ``accLoop
  unless (mixedCertifiedShape? false [] ciL).isSome do
    throwError "feedback register missed the gate"
  let (ml, _) ← synthesizeCombinationalCore ``accLoop [] false
  let regsL := ml.body.filterMap fun st => match st with
    | .register o _ _ _ init => some (o, init)
    | _ => none
  let [(rL, initL)] := regsL | throwError "expected one feedback register"
  let ml' := Sparkle.IR.ZeroWidth.dropZeroWidthModule ml
  unless ml'.body == ml.body && ml'.wires == ml.wires do
    throwError "dropZeroWidth changed the feedback-register module"
  unless initL == 0 do throwError "unexpected feedback-register init"
  let weL := Tools.ShippingEntrySoundness.weOf ml
  let mut stateL : Nat := 0
  let mut countL : Nat := 0
  for t in List.range 12 do
    let env0 := fun (n : String) =>
      if n == "_gen_c" then (if ctrace t then 1 else 0)
      else if n == "_gen_a" then atrace t
      else if n == "_gen_b" then btrace t
      else if n == rL then stateL
      else 0
    let some (envF, nexts, _) := stepModule weL ml.body env0 |
      throwError "feedback stepModule failed at {t}"
    unless envF "out" == stateL do
      throwError "feedback cycle {t}: out={envF "out"} expected {stateL}"
    let expected := ((if ctrace t then BitVec.ofNat 8 stateL else BitVec.ofNat 8 (atrace t))
      + BitVec.ofNat 8 (btrace t)).toNat
    let some (_, next) := nexts.find? (fun p => p.1 == rL) |
      throwError "feedback register next missing"
    unless next == expected do
      throwError "feedback cycle {t}: next={next} expected {expected}"
    stateL := next
    countL := countL + 1
  unless countL == 12 do throwError "feedback register cycle count mismatch: {countL}"
  -- Two-stage chain: the module carries two registers; `out` observes the
  -- outer one, which shifts from the inner one each cycle.
  let ciC ← getConstInfo ``regChain
  unless (mixedCertifiedShape? false [] ciC).isSome do
    throwError "register chain missed the gate"
  let (mc, _) ← synthesizeCombinationalCore ``regChain [] false
  let regsC := mc.body.filterMap fun st => match st with
    | .register o _ _ _ init => some (o, init)
    | _ => none
  let [(rInner, initInner), (rOuter, initOuter)] := regsC
    | throwError "expected two chain registers"
  unless initInner == 2 && initOuter == 1 do throwError "unexpected chain inits"
  let mc' := Sparkle.IR.ZeroWidth.dropZeroWidthModule mc
  unless mc'.body == mc.body && mc'.wires == mc.wires do
    throwError "dropZeroWidth changed the chain module"
  let weC := Tools.ShippingEntrySoundness.weOf mc
  let mut s1 : Nat := 1
  let mut s2 : Nat := 2
  let mut countC : Nat := 0
  for t in List.range 12 do
    let env0 := fun (n : String) =>
      if n == "_gen_c" then (if ctrace t then 1 else 0)
      else if n == "_gen_a" then atrace t
      else if n == "_gen_b" then btrace t
      else if n == rOuter then s1
      else if n == rInner then s2
      else 0
    let some (envF, nexts, _) := stepModule weC mc.body env0 |
      throwError "chain stepModule failed at {t}"
    unless envF "out" == s1 do
      throwError "chain cycle {t}: out={envF "out"} expected {s1}"
    let cone := ((if ctrace t then BitVec.ofNat 8 (atrace t) else BitVec.ofNat 8 (btrace t))
      + BitVec.ofNat 8 (atrace t)).toNat
    let some (_, nextI) := nexts.find? (fun p => p.1 == rInner) |
      throwError "chain inner next missing"
    let some (_, nextO) := nexts.find? (fun p => p.1 == rOuter) |
      throwError "chain outer next missing"
    unless nextI == cone && nextO == s2 do
      throwError "chain cycle {t}: nexts=({nextI},{nextO}) expected ({cone},{s2})"
    s1 := nextO
    s2 := nextI
    countC := countC + 1
  unless countC == 12 do throwError "chain cycle count mismatch: {countC}"
  -- Single-slot circuit do: gate-accepted and synthesized to the SAME
  -- module as the explicit Signal.loop feedback form (whose cycle/trace
  -- theorems therefore apply verbatim); source streams identified by
  -- `cdoAcc_val`.
  let ciD ← getConstInfo ``cdoAcc
  unless (mixedCertifiedShape? false [] ciD).isSome do
    throwError "circuit-do missed the gate"
  let (md, _) ← synthesizeCombinationalCore ``cdoAcc [] false
  let (mLoopTwin, _) ← synthesizeCombinationalCore ``cdoLoopAcc [] false
  unless md.body == mLoopTwin.body && md.wires == mLoopTwin.wires &&
      md.outputs == mLoopTwin.outputs do
    throwError "circuit-do module differs from the explicit loop form"
  -- The raw sequential merge is empirically the IDENTITY on every
  -- certified register shape (the translator's expression cache leaves no
  -- duplicate nodes, so the partition refinement ends discrete). This is
  -- the evidence base for the planned structural merge-identity proof
  -- that would carry the register theorems to the default (merged)
  -- configuration; a change here means the default configuration departs
  -- from the certified raw module.
  for decl in [``regAcc, ``regHold, ``accLoop, ``regChain, ``cdoAcc] do
    let (mr, _) ← synthesizeCombinationalCore decl [] false
    let mrz := Sparkle.IR.ZeroWidth.dropZeroWidthModule mr
    let mrm := Sparkle.IR.RegDedup.mergeDuplicatesRaw mrz
    unless mrm.body == mrz.body && mrm.wires == mrz.wires &&
        mrm.outputs == mrz.outputs do
      throwError "sequential merge changed the certified module of {decl}"
  -- Two-slot circuit do: gate acceptance and a 12-cycle two-register
  -- regression against the cross-coupled source recurrences (out = x;
  -- x' = mux c y a; y' = (mux c x y) + a). The proof chain for this shape
  -- is the next unit; this regression pins the compiled semantics.
  let ci2 ← getConstInfo ``cdo2X
  unless (mixedCertifiedShape? false [] ci2).isSome do
    throwError "two-slot circuit-do missed the gate"
  let (m2, _) ← synthesizeCombinationalCore ``cdo2X [] false
  let regs2 := m2.body.filterMap fun st => match st with
    | .register o _ _ _ init => some (o, init)
    | _ => none
  let [(rX, initX), (rY, initY)] := regs2
    | throwError "expected two circuit-do registers"
  unless initX == 1 && initY == 2 do throwError "unexpected two-slot inits"
  let m2' := Sparkle.IR.ZeroWidth.dropZeroWidthModule m2
  unless m2'.body == m2.body && m2'.wires == m2.wires do
    throwError "dropZeroWidth changed the two-slot module"
  let we2 := Tools.ShippingEntrySoundness.weOf m2
  let mut sx : Nat := 1
  let mut sy : Nat := 2
  let mut count2s : Nat := 0
  for t in List.range 12 do
    let env0 := fun (n : String) =>
      if n == "_gen_c" then (if ctrace t then 1 else 0)
      else if n == "_gen_a" then atrace t
      else if n == rX then sx
      else if n == rY then sy
      else 0
    let some (envF, nexts, _) := stepModule we2 m2.body env0 |
      throwError "two-slot stepModule failed at {t}"
    unless envF "out" == sx do
      throwError "two-slot cycle {t}: out={envF "out"} expected {sx}"
    let expX := if ctrace t then sy else atrace t
    let expY := ((if ctrace t then BitVec.ofNat 8 sx else BitVec.ofNat 8 sy)
      + BitVec.ofNat 8 (atrace t)).toNat
    let some (_, nX) := nexts.find? (fun p => p.1 == rX) |
      throwError "two-slot x next missing"
    let some (_, nY) := nexts.find? (fun p => p.1 == rY) |
      throwError "two-slot y next missing"
    unless nX == expX && nY == expY do
      throwError "two-slot cycle {t}: nexts=({nX},{nY}) expected ({expX},{expY})"
    sx := nX
    sy := nY
    count2s := count2s + 1
  unless count2s == 12 do throwError "two-slot cycle count mismatch: {count2s}"
  logInfo m!"REGISTER REGRESSION: {count} cycles of the raw synthesized module (and {count2} of the merged default configuration) match the source register recurrence (init 3, reset low); {countH} enabled-register cycles match the capture/hold recurrence (init 5); {countL} feedback cycles match the loop recurrence (init 0); {countC} two-stage chain cycles match the nested register recurrence (inits 1/2); the single-slot circuit-do synthesizes to the identical loop-form module; the raw sequential merge is the identity on all five certified register modules; {count2s} two-slot circuit-do cycles match the cross-coupled recurrences (inits 1/2)"

run_cmd do
  if (← get).messages.hasErrors then throwError "register regression failed"
  for name in [``Tools.ShippingRegisterSoundness.synthesizeMixedCertified_register_sound,
      ``Tools.ShippingRegisterSoundness.register_step_of_env,
      ``Tools.ShippingRegisterSoundness.trace_of_cycles,
      ``Tools.ShippingRegisterSoundness.register_term_gate,
      ``Tools.ShippingRegisterSoundness.synthesizeMixedCertified_registerEnable_sound,
      ``Tools.ShippingRegisterSoundness.registerEnable_step_of_env,
      ``Tools.ShippingRegisterSoundness.synthesizeMixedCertified_loopRegister_sound,
      ``Tools.ShippingRegisterSoundness.loopRegister_step_of_env,
      ``Tools.ShippingRegisterSoundness.trace_of_cycles_inv,
      ``Tools.ShippingRegisterSoundness.loop_register_val,
      ``Tools.ShippingRegisterSoundness.loopRegister_run_of_env,
      ``Tools.ShippingRegisterSoundness.synthesizeMixedCertified_register2_sound,
      ``Tools.ShippingRegisterSoundness.register2_step_of_env,
      ``Tools.ShippingRegisterSoundness.trace_of_cycles2,
      ``Tools.ShippingRegisterSoundness.register2_run_of_env,
      ``Tools.ShippingRegisterSoundness.synthesizeMixedCertified_cdo_sound,
      ``Tools.ShippingRegisterSoundness.cdoConeToLoop_quote,
      ``Tools.ShippingRegisterSoundness.cdo_step_of_env,
      ``Tools.ShippingRegisterSoundness.cdo_run_of_env,
      ``regAcc_step, ``regHold_step, ``accLoop_step, ``regChain_step,
      ``regAcc_run, ``regHold_run, ``accLoop_run, ``regChain_run, ``cdoAcc_step, ``cdoAcc_run,
      ``Tools.ShippingRegisterSoundness.map_fst_loop_register, ``cdoAcc_val] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected register soundness axiom: {name}: {ax}"
  logInfo "REGISTER ENDPOINT: standard axioms only; register cycle theorem connected to the real core entry"

end Sparkle.Tests.Compiler.ShippingRegisterSoundnessTest
