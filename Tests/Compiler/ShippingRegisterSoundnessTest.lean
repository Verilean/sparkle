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
  logInfo m!"REGISTER REGRESSION: {count} cycles of the raw synthesized module (and {count2} of the merged default configuration) match the source register recurrence (init 3, reset low); {countH} enabled-register cycles match the capture/hold recurrence (init 5); {countL} feedback cycles match the loop recurrence (init 0)"

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
      ``regAcc_step, ``regHold_step, ``accLoop_step] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected register soundness axiom: {name}: {ax}"
  logInfo "REGISTER ENDPOINT: standard axioms only; register cycle theorem connected to the real core entry"

end Sparkle.Tests.Compiler.ShippingRegisterSoundnessTest
