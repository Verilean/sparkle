import Tools.ShippingRegisterSoundness
import Tests.Compiler.ShippingMixedExecutionTest

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
  logInfo m!"REGISTER REGRESSION: {count} cycles of the raw synthesized module match the source register recurrence (init 3, reset low)"

run_cmd do
  if (← get).messages.hasErrors then throwError "register regression failed"
  for name in [``Tools.ShippingRegisterSoundness.synthesizeMixedCertified_register_sound,
      ``Tools.ShippingRegisterSoundness.register_step_of_env,
      ``Tools.ShippingRegisterSoundness.trace_of_cycles,
      ``Tools.ShippingRegisterSoundness.register_term_gate,
      ``regAcc_step] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected register soundness axiom: {name}: {ax}"
  logInfo "REGISTER ENDPOINT: standard axioms only; register cycle theorem connected to the real core entry"

end Sparkle.Tests.Compiler.ShippingRegisterSoundnessTest
