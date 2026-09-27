import Tools.ShippingMixedExecutionSoundness
import Tests.Compiler.ShippingMixedEntryTest
import Tests.Compiler.ShippingMixedSourceBridgeTest

namespace Sparkle.Tests.Compiler.ShippingMixedExecutionTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.ShippingEntrySoundness Tools.ShippingMixedEntrySoundness
open Tools.ShippingMixedPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingMixedExecutionSoundness Tools.ShippingTypedPostSoundness
open Tools.SVParser.AST Tools.SVParser.EmitSem
open Tools.ShippingSettledSoundness
open Tools.ShippingTypedExprSoundness Tools.ShippingSVBridge
open Tools.SVParser.EmitAst
open Tools.ShippingMixedDeclSoundness Tools.ShippingDeclWidths Tools.ShippingPrintSoundness

/-- The public endpoint asks for no printable-declaration certificate. -/
theorem shipping_execution {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) →
        MixedSourcePreserves declName bs body (ExecutionValue m) :=
  synthesizeCombinational_mixed_execution hr

open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMixedSourceBridge Tools.ShippingMuxLoweringSoundness
open Sparkle.Tests.Compiler.ShippingMixedSourceBridgeTest

theorem nested_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
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
      ExecutionValue m initial mems (encodeBool
        ((ShippingMixedRecursionTest.source (bools 1) (bits 2 8) (bits 3 8)).val tick)) :=
  execution_source_of_env hr env (by rfl) source_peel (by decide)
    ShippingMixedRecursionTest.term_wf bool_position bits_position

theorem reordered_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
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
      ExecutionValue m initial mems (encodeBool
          ((reordered (bits 1 8) (bools 2) (bits 3 17) (bits 4 8)).val tick)) := by
  exact execution_source_of_env hr env (by rfl) reordered_peel (by decide)
    reordered_wf reordered_bool_position reordered_bits_position

/-- Every RHS reads the old round; writes become visible together. -/
def parallelRound (widths : String → Option Nat) (pairs : List CombStep) (old : Env) : Option Env :=
  pairs.foldlM (fun next step => match step with
    | .assign lhs rhs => do
      let n ← widths lhs
      let v ← Tools.SVParser.SVSemantics.evalSV widths old n rhs
      pure (fun x => if x = lhs then mask n v else next x)
    | _ => none) old

def shared {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux c (Signal.ult (a + b) b) (Signal.ult (a + b) b)

run_cmd liftTermElabM do
  let mut cases := 0
  let mut accepted := 0
  let mut retained := 0
  for name in [``ShippingMixedRecursionTest.source, ``ShippingMixedEntryTest.passthrough,
      ``ShippingMixedEntryTest.constant, ``ShippingMixedEntryTest.oneBit,
      ``ShippingMixedSourceBridgeTest.reordered, ``shared] do
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (actual, _) ← synthesizeCombinational name
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      if optCheck post (Sparkle.IR.Optimize.optimizeModule post) &&
          assignmentOrderCheck (Sparkle.IR.Optimize.optimizeModule post).body then
        accepted := accepted + 1
      else retained := retained + 1
      let m := checkedOptimize post
      unless Tools.ShippingSVBridge.forwardCheck m && assignmentOrderCheck m.body do
        throwError "mixed execution checks failed: {name}"
      let some sv := emitAstModule m | throwError "mixed AST emission failed"
      let some pairs := combItems sv.items | throwError "mixed body extraction failed"
      let widths := astWidths sv
      let names := (declarationTable sv).map Prod.fst
      for c in [false, true] do
        for a in [0, 1, 127, 128, 255] do
          for b in [0, 1, 127, 128, 255] do
            let values := if name == ``ShippingMixedEntryTest.passthrough then [encodeBool c]
              else if name == ``ShippingMixedEntryTest.constant then []
              else if name == ``ShippingMixedEntryTest.oneBit then [encodeBool c, a % 2]
              else if name == ``ShippingMixedSourceBridgeTest.reordered then [a, encodeBool c, 131071, b]
              else [encodeBool c, a, b]
            let av := BitVec.ofNat 8 a
            let bv := BitVec.ofNat 8 b
            let expected := encodeBool <| if name == ``ShippingMixedEntryTest.passthrough then c
              else if name == ``ShippingMixedEntryTest.constant then false
              else if name == ``ShippingMixedEntryTest.oneBit then c && (a % 2 < 1)
              else if name == ``ShippingMixedSourceBridgeTest.reordered then if c then av < bv else true
              else if name == ``shared then av + bv < bv
              else if av + bv < bv then c || (av - bv ≤ bv) else av * bv < av
            for seed in [0, 1, 65535] do
              let initial := fun w =>
                match (((raw.inputs.map (·.name)).zip values).find? (fun p => p.1 == w)) with
                | some (_, v) => v
                | none => mask ((widths w).getD 0) seed
              let some stable := evalAssignsSV widths (fun _ _ => 0) pairs initial |
                throwError "mixed SV evaluation failed"
              let mut current := initial
              for _ in [:pairs.length] do
                let some next := parallelRound widths pairs current | throwError "mixed delta failed"
                current := next
              let some extra := parallelRound widths pairs current | throwError "mixed stable round failed"
              unless observeUnsignedOutput sv current "out" == some expected &&
                  names.all (fun x => current x == stable x && extra x == stable x) do
                throwError "mixed source/delta mismatch: {name}, {c}, {a}, {b}, seed {seed}"
              cases := cases + 1
  unless cases == 2700 && accepted > 0 && retained > 0 do throwError "mixed execution coverage failed"
  logInfo m!"MIXED EXECUTION: {cases} source/SV/parallel-delta cases, {accepted} accepted and {retained} retained paths"

run_cmd do
  if (← get).messages.hasErrors then throwError "mixed execution regression failed"
  for name in [``Tools.ShippingMixedOrderSoundness.fuel_orders,
      ``Tools.ShippingMixedOrderSoundness.bool_fuel_orders,
      ``Tools.ShippingMixedForwardSoundness.checked_forwardCheck,
      ``checked_order, ``execution_of_entry, ``synthesizeCombinational_mixed_execution,
      ``execution_source_of_env, ``shipping_execution, ``nested_execution, ``reordered_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mixed execution axiom: {name}: {ax}"
  logInfo "MIXED EXECUTION ENDPOINT: shipping source, syntax, unique bounded solution and finite parallel settling; standard axioms only"

end Sparkle.Tests.Compiler.ShippingMixedExecutionTest
