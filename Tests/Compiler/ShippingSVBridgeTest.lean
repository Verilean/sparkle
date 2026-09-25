import Tools.ShippingSVBridge
import Tests.Compiler.ShippingEntrySoundnessTest

namespace Sparkle.Tests.Compiler.ShippingSVBridgeTest

open Lean Elab Command
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab Sparkle.IR.OptCheck
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.ShippingPrintSoundness Tools.ShippingSVBridge
open Sparkle.Tests.Compiler.ShippingEntrySoundnessTest
open Tools.ShippingEntrySoundness Tools.ShippingTranslateSoundness

/-- Apply the general width derivation to a real declaration and the actual
core entry. Only the explicitly separate name-stability condition remains. -/
theorem fragA_core_forward {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (h : RunsTo (synthesizeCombinationalCore ``fragA [] false) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref ``fragA fragAValue)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    forwardCheck m = true := by
  rw [fragAValue_eq] at henv
  exact core_forwardCheck h henv feA_wf (by decide) hs

example : ¬ SizedExpr (fun _ => 8) (.op .add [.const 1 8, .const 2 8]) 16 := by
  intro h
  have hw := h.width
  simp [widthOf] at hw

def hashBinder {dom : Sparkle.Core.Domain.DomainConfig}
    («a#» : Sparkle.Core.Signal.Signal dom (BitVec 8)) : Sparkle.Core.Signal.Signal dom (BitVec 8) :=
  «a#»

-- The wrapper is tied to the printed tree, and does not silently discard
-- unsupported semantics when reading its items.
example : combItems [.regDecl "r" none none] = none := rfl
example : combItems [.instantiation "sub" "u" []] = none := rfl
example : combItems [.wireDecl "w" none (some (.lit (.decimal (some 8) 0)))] = none := rfl

run_cmd liftTermElabM do
  for name in [``fragA, ``fragB, ``fragC, ``fragD] do
    let (core, _) ← synthesizeCombinationalCore name [] false
    unless forwardCheck core do
      throwError "forward check rejected the core entry result: {name}"
    let (m, _) ← synthesizeCombinational name
    for o in [m, checkedOptimize m] do
      let wof := printWidths (o.wires ++ o.inputs ++ o.outputs)
      unless Sparkle.IR.RegDedup.declWidth o "out" == 0 && wof "out" != some 0 do
        throwError "expected the wire-only / output-port width boundary"
      unless !(assignsCheck wof (Sparkle.IR.RegDedup.declWidth o) o.body) do
        throwError "wire-only width lookup unexpectedly passed the output assignment"
      unless forwardCheck o do
        throwError "forward check rejected actual unoptimized/optimized fragment: {name}"
      let some sv := emitAstModule o | throwError "AST emission failed"
      let some pairs := combItems sv.items | throwError "AST item extraction failed"
      -- A smoke check of the actual tree, not the general proof's substitute.
      let initial : Env := fun _ => 0
      let some ir := evalAssigns (Sparkle.IR.RegDedup.declWidth o) (fun _ _ => 0) o.body initial
        | throwError "IR execution failed"
      let some rtl := evalAssignsSV wof (fun _ _ => 0) pairs initial
        | throwError "SV assignment-fold execution failed"
      unless ir "out" == rtl "out" do
        throwError "IR and emitted-tree smoke check disagree"

  -- Changing only an unused assignment's target width preserves the old
  -- optimizer output check but invalidates the all-assignments forward rule.
  let (m, _) ← synthesizeCombinational ``fragA
  let o := checkedOptimize m
  let bad := {o with wires := o.wires ++ [{name := "unused_bad_width", ty := .bitVector 8}], body := o.body ++ [.assign "unused_bad_width" (.const 300 16)]}
  unless optCheck m bad do
    throwError "negative control must pass the output-only optimizer check"
  unless !(forwardCheck bad) do
    throwError "forward check accepted mismatched assignment width"
  let (named, _) ← synthesizeCombinationalCore ``hashBinder [] false
  unless named.wires.any (fun p => Sparkle.Backend.Verilog.sanitizeName p.name != p.name) do
    throwError "name-stability negative control unexpectedly has stable names"
  unless !(forwardCheck named) do
    throwError "forward check unexpectedly accepted the unstable-name core module"

run_cmd do
  if (← get).messages.hasErrors then throwError "SV bridge regression failed"
  for name in [``evalAssigns_widths, ``forwardCheck_sound, ``combItems_append,
      ``combItems_wires, ``body_combItems, ``module_combItems, ``module_forward,
      ``compiledFragment_forward] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected SV bridge axiom: {name}: {ax}"
  for name in [``fragA_core_forward, ``core_forwardCheck, ``postReady_forwardCheck,
      ``dropZeroWidth_sized, ``Tools.ShippingTranslateSoundness.SizedExpr.width,
      ``Tools.ShippingSVBridge.SizedExpr.forward] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected core-width axiom: {name}: {ax}"
  logInfo "SHIPPING CORE WIDTH OK: core forwardCheck derived under name stability; standard axioms only; final optimized check still open"
  logInfo "SHIPPING SV BRIDGE OK: actual AST assignments, width transport, conditional source/SV fold theorem; final forwardCheck and initialization obligations still open"

end Sparkle.Tests.Compiler.ShippingSVBridgeTest
