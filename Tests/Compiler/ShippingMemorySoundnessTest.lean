import Tools.ShippingMemoryEntrySoundness
import Tests.Compiler.ShippingMixedExecutionTest

/-! S5-1 memory foundation tests: a real `Signal.memory` declaration, the
compiled module pinned byte-for-byte to the canonical body the semantics
layer proves about, a 12-cycle numeric regression against the actual
`stepModule`/`memNexts` semantics, and the trace endpoint instantiated on
the pinned shape with a standard-axioms audit. -/
namespace Sparkle.Tests.Compiler.ShippingMemorySoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMemorySoundness Tools.ShippingMemoryEntrySoundness
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMixedExecutionSoundness

/-- A single-port sync-read memory over direct input operands: the
canonical S5 shape. -/
def memAcc {dom : DomainConfig} (wa : Signal dom (BitVec 2))
    (wd : Signal dom (BitVec 8)) (wen : Signal dom Bool)
    (ra : Signal dom (BitVec 2)) : Signal dom (BitVec 8) :=
  Signal.memory wa wd wen ra

#def_decl_value memAccValue of memAcc
def memAccBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`wa, .bits 2), (`wd, .bits 8), (`wen, .bool), (`ra, .bits 2)]
theorem memAcc_peel : mixedGatePeel memAccValue = some (memAccBinders,
    memoryE (inputExpr memAccBinders.length 0) 2 8
      (inputExpr memAccBinders.length 1) (inputExpr memAccBinders.length 2)
      (inputExpr memAccBinders.length 3) (inputExpr memAccBinders.length 4)) := rfl

/-- **The memory trace endpoint on the real declaration**: the compiled
module's whole `runModule` trace observes the source `Signal.memory`
stream — premises are the entry facts alone (no byte-level module gate). -/
theorem memAcc_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``memAcc [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``memAcc memAccValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = memAccBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
      ∀ {D : DomainConfig} (boolsS : Nat → Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (we : WEnv) (mems0 : MEnv) (k : Nat)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ t stv, SourceInputs ``memAcc memAccBinders ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv rdW = stv rdW) →
      st0 rdW = 0 →
      (∀ n i, mems0 n i = 0) →
      ∃ envs, runModule we m.body seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((memAcc (bitsS 1 2) (bitsS 2 8) (boolsS 3) (bitsS 4 2)).val j).toNat :=
  memory_run_of_env (dpos := 0) (wapos := 1) (wdpos := 2) (wenpos := 3) (rapos := 4)
    hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl)
    memAcc_peel (by decide) (by decide) (by decide)
    ⟨`wa, rfl⟩ ⟨`wd, rfl⟩ ⟨`wen, rfl⟩ ⟨`ra, rfl⟩

/-- The compiled module's body IS the canonical body of the semantics
layer; the trace endpoint below is therefore about the real compiler
output, premise-pinned by the gate in the command block. -/
theorem memAcc_run_val {we : WEnv} {D : DomainConfig}
    (waS : Signal D (BitVec 2)) (wdS : Signal D (BitVec 8))
    (weS : Signal D Bool) (raS : Signal D (BitVec 2)) :
    ∀ (k : Nat) (seed : Nat → (String → Nat) → Env)
      (st0 : String → Nat) (mems0 : MEnv),
      (∀ t stv, seed t stv "_gen_out_rdata" = stv "_gen_out_rdata" ∧
        seed t stv "_gen_wa" = ((waS.val (k - 1 - t)).toNat) ∧
        seed t stv "_gen_wd" = ((wdS.val (k - 1 - t)).toNat) ∧
        seed t stv "_gen_wen" = (if weS.val (k - 1 - t) then 1 else 0) ∧
        seed t stv "_gen_ra" = ((raS.val (k - 1 - t)).toNat)) →
      st0 "_gen_out_rdata" = 0 →
      (∀ n i, mems0 n i = 0) →
      ∃ envs, runModule we
          (memBody "_gen_out" "clk" "_gen_wa" "_gen_wd" "_gen_wen" "_gen_ra"
            "_gen_out_rdata" 2 8) seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((Signal.memory waS wdS weS raS).val j).toNat :=
  memory_run_val (by decide) (by decide) (by decide) (by decide) (by decide)
    waS wdS weS raS

-- Deterministic 12-cycle stimulus.
private def watr (t : Nat) : Nat := t % 4
private def wdtr (t : Nat) : Nat := (17 * t + 3) % 256
private def wetr (t : Nat) : Bool := t % 3 ≠ 1
private def ratr (t : Nat) : Nat := (t + 1) % 4

open Sparkle.IR.AST in
run_cmd liftTermElabM do
  -- The compiled module is EXACTLY the canonical shape.
  let (mr, _) ← synthesizeCombinationalCore ``memAcc [] false
  let expected := memBody "_gen_out" "clk" "_gen_wa" "_gen_wd" "_gen_wen"
    "_gen_ra" "_gen_out_rdata" 2 8
  unless mr.body == expected do
    throwError "memory module body departed from the canonical shape"
  unless mr.outputs.map (·.name) == ["out"] do
    throwError "memory module outputs departed from [out]"
  unless (mr.inputs.map (·.name)).contains "_gen_wa" &&
      (mr.inputs.map (·.name)).contains "_gen_ra" do
    throwError "memory module inputs departed from the operand wires"
  -- 12-cycle regression: run the ACTUAL stepModule semantics and compare
  -- both the observed output and the latch/array evolution against the
  -- source recurrence (Signal.memory's memState).
  let weE : WEnv := fun n =>
    if n == "_gen_wd" || n == "_gen_out_rdata" || n == "out" then 8
    else if n == "_gen_wa" || n == "_gen_ra" then 2
    else 1
  let mut st : Nat := 0        -- latch state (_gen_out_rdata)
  let mut arr : List Nat := [0, 0, 0, 0]
  let mut mems : MEnv := fun _ _ => 0
  let mut count : Nat := 0
  for t in List.range 12 do
    let env0 : Env := fun n =>
      if n == "_gen_wa" then watr t
      else if n == "_gen_wd" then wdtr t
      else if n == "_gen_wen" then (if wetr t then 1 else 0)
      else if n == "_gen_ra" then ratr t
      else if n == "_gen_out_rdata" then st
      else 0
    let some (envF, nexts, mems') := stepModule weE mr.body env0 mems |
      throwError "memory stepModule failed at {t}"
    unless envF "out" == st do
      throwError "memory cycle {t}: out={envF "out"} expected {st}"
    let some (_, latch) := nexts.find? (fun p => p.1 == "_gen_out_rdata") |
      throwError "memory latch missing at {t}"
    let expectedLatch := arr[ratr t]!
    unless latch == expectedLatch do
      throwError "memory cycle {t}: latch={latch} expected {expectedLatch}"
    unless (List.range 4).all (fun i => mems' "_gen_out" i ==
        (if wetr t && i == watr t then wdtr t else arr[i]!)) do
      throwError "memory cycle {t}: array mismatch"
    st := latch
    arr := (List.range 4).map (fun i =>
      if wetr t && i == watr t then wdtr t else arr[i]!)
    mems := mems'
    count := count + 1
  unless count == 12 do throwError "memory cycle count mismatch: {count}"
  -- Axiom audit: the endpoint and the general layer carry only the
  -- standard axioms.
  for name in [``Tools.ShippingMemorySoundness.memStep,
      ``Tools.ShippingMemorySoundness.trace_of_cycles_memArr,
      ``Tools.ShippingMemorySoundness.memory_run,
      ``Tools.ShippingMemorySoundness.memory_run_val,
      ``Tools.ShippingMemoryEntrySoundness.synthesizeMixedCertified_memory_sound,
      ``Tools.ShippingMemoryEntrySoundness.memory_body_of_env,
      ``Tools.ShippingMemoryEntrySoundness.memory_run_of_env,
      ``memAcc_run_val, ``memAcc_peel, ``memAcc_run] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected memory soundness axiom: {name}: {ax}"
  logInfo "MEMORY FOUNDATION: canonical shape pinned; 12-cycle trace matches; standard axioms only"

end Sparkle.Tests.Compiler.ShippingMemorySoundnessTest
