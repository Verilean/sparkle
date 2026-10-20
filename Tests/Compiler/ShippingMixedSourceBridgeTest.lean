import Tools.ShippingMixedSourceBridge
import Tests.Compiler.ShippingMixedRecursionTest

namespace Sparkle.Tests.Compiler.ShippingMixedSourceBridgeTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMuxLoweringSoundness

#def_decl_value sourceValue of ShippingMixedRecursionTest.source

def binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]

theorem source_peel : mixedGatePeel sourceValue = some (binders,
    quoteB (.bvar 3) 8 (fun _ => inputExpr binders.length 1)
      (fun j => inputExpr binders.length (j + 2)) ShippingMixedRecursionTest.term) := rfl

theorem bool_position : ∀ j, j < 1 → ∃ name, binders[1]? = some (name, .bool) :=
  fun _ _ => ⟨`c, rfl⟩
theorem bits_position : ∀ j, j < 2 → ∃ name, binders[j + 2]? = some (name, .bits 8) := by
  intro j hj
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with rfl | rfl
  · exact ⟨`a, rfl⟩
  · exact ⟨`b, rfl⟩

/-- A real declaration, all source Signals and all observation times, through
actual synthesis and checked optimization. No intermediate valuation lookup,
quotation-substitution, readiness or optimizer-success premises. -/
theorem nested_source {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``ShippingMixedRecursionTest.source)
      mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``ShippingMixedRecursionTest.source sourceValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = binders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``ShippingMixedRecursionTest.source binders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ∃ result, evalAssigns (weOf (Sparkle.IR.OptCheck.checkedOptimize m)) mems
          (Sparkle.IR.OptCheck.checkedOptimize m).body initial = some result ∧
        result "out" = encodeBool
          ((ShippingMixedRecursionTest.source (bools 1) (bits 2 8) (bits 3 8)).val tick) ∧
        "out" ∈ (Sparkle.IR.OptCheck.checkedOptimize m).outputs.map (·.name) := by
  exact shipping_source_of_env hr env (by rfl) source_peel (by decide)
    ShippingMixedRecursionTest.term_wf bool_position bits_position

def reordered {dom : DomainConfig} (a : Signal dom (BitVec 8)) (c : Signal dom Bool)
    (_unused : Signal dom (BitVec 17)) (b : Signal dom (BitVec 8)) :=
  Signal.mux c (Signal.ult a b) (Signal.pure true)
#def_decl_value reorderedValue of reordered

def reorderedBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`c, .bool), (`_unused, .bits 17), (`b, .bits 8)]
def reorderedTerm : BExpr := .mux (.inp 0) (.compare false (.inp 0) (.inp 1)) (.lit true)
def reorderedBits (j : Nat) := if j = 0 then 1 else 4

theorem reordered_peel : mixedGatePeel reorderedValue = some (reorderedBinders,
    quoteB (.bvar 4) 8 (fun _ => inputExpr reorderedBinders.length 2)
      (fun j => inputExpr reorderedBinders.length (reorderedBits j)) reorderedTerm) := rfl

theorem reordered_wf : reorderedTerm.WF 1 2 8 := by
  simp [reorderedTerm, BExpr.WF, FExpr.WF]
theorem reordered_bool_position : ∀ j, j < 1 → ∃ name, reorderedBinders[2]? = some (name, .bool) :=
  fun _ _ => ⟨`c, rfl⟩
theorem reordered_bits_position : ∀ j, j < 2 → ∃ name, reorderedBinders[reorderedBits j]? = some (name, .bits 8) := by
  intro j hj
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with rfl | rfl
  · exact ⟨`a, rfl⟩
  · exact ⟨`b, rfl⟩

theorem reordered_source {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``reordered)
      mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref ``reordered reorderedValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = reorderedBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``reordered reorderedBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ∃ result, evalAssigns (weOf (Sparkle.IR.OptCheck.checkedOptimize m)) mems
          (Sparkle.IR.OptCheck.checkedOptimize m).body initial = some result ∧
        result "out" = encodeBool
          ((reordered (bits 1 8) (bools 2) (bits 3 17) (bits 4 8)).val tick) ∧
        "out" ∈ (Sparkle.IR.OptCheck.checkedOptimize m).outputs.map (·.name) := by
  exact shipping_source_of_env hr env (by rfl) reordered_peel (by decide)
    reordered_wf reordered_bool_position reordered_bits_position

run_cmd liftTermElabM do
  for name in [``ShippingMixedRecursionTest.source, ``reordered] do
    let ci ← getConstInfo name
    unless (mixedCertifiedShape? false [] ci).isSome do throwError "source missed mixed gate"
    let (m, _) ← synthesizeCombinational name
    unless m.inputs.length == (if name == ``reordered then 4 else 3) do
      throwError "source bridge input count mismatch"

run_cmd do
  if (← get).messages.hasErrors then throwError "mixed source bridge regression failed"
  for name in [``prepare_bool_absent, ``prepare_bits_absent, ``prepare_bool_lookup,
      ``prepare_bits_lookup, ``instantiated_input, ``zip_ids, ``zip_member, ``source_inputs,
      ``index_fresh, ``source_positions, ``source_signals, ``mixed_kind_at, ``mixed_bits_at,
      ``source_gate, ``shipping_source_signals, ``shipping_source_of_env,
      ``source_peel, ``bool_position, ``bits_position, ``nested_source, ``reordered_peel, ``reordered_wf,
      ``reordered_bool_position, ``reordered_bits_position, ``reordered_source] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mixed source bridge axiom: {name}: {ax}"
  logInfo "MIXED SOURCE BRIDGE: arbitrary argument positions; real nested source Signal theorem through checked optimization; EnvDefines retained; text/settling remains open"

end Sparkle.Tests.Compiler.ShippingMixedSourceBridgeTest
