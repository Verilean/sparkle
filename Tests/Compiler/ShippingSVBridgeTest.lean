import Tools.ShippingSVBridge
import Tests.Compiler.ShippingEntrySoundnessTest

namespace Sparkle.Tests.Compiler.ShippingSVBridgeTest

open Lean Elab Command
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab Sparkle.IR.OptCheck
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.ShippingPrintSoundness Tools.ShippingSVBridge
open Tools.ShippingModulePrintSoundness
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

/-- The same real declaration, now at the full synthesis entry after cleanup
and validated merging. The forward check is a conclusion, not a premise. -/
theorem fragA_synthesized_forward {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (h : RunsTo (synthesizeCombinational ``fragA) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref ``fragA fragAValue)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    forwardCheck m = true := by
  rw [fragAValue_eq] at henv
  exact synthesized_forwardCheck h henv feA_wf (by decide) hs

/-- No hypothesis about the optimized module: the real optimizer selection
now preserves the source-derived check on either returned branch. -/
theorem fragA_compiled_forward {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (h : RunsTo (synthesizeCombinational ``fragA) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref ``fragA fragAValue)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    forwardCheck (checkedOptimize m) = true := by
  rw [fragAValue_eq] at henv
  exact compiled_forwardCheck h henv feA_wf (by decide) hs

/-- Apply the initialized source-to-SV theorem to the actual declaration. -/
theorem fragA_initialized_sv {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (h : RunsTo (synthesizeCombinational ``fragA) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref ``fragA fragAValue)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    ∃ sv port pairs, emitAstModule (checkedOptimize m) = some sv ∧
      combItems sv.items = some pairs ∧
      (∀ j x, j < 2 → port j = some x →
        ∃ sp ∈ sv.ports, sp.dir = .input ∧ sp.name = x ∧
          declaredPortWidth sp = some 8 ∧ sp.isSigned = false) ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec 8)) (t : Nat),
        let initial := inputEnv 2 port (fun j => (sigs j).val t)
        Bounded (forwardWidths (checkedOptimize m)) initial ∧
        ∃ env, evalAssignsSV (Sparkle.IR.PrintCheck.widths (checkedOptimize m))
          (fun _ _ => 0) pairs initial = some env ∧
          env "out" = ((fragA (sigs 0) (sigs 1)).val t).toNat := by
  rw [fragAValue_eq] at henv
  obtain ⟨sv, port, pairs, ht, _, hi, _, _, hdecl, hsem⟩ :=
    compiledFragment_forward h henv feA_wf (by decide) hs
  refine ⟨sv, port, pairs, ht, hi, hdecl, ?_⟩
  intro dom sigs t
  exact hsem sigs t (fun _ _ => 0)

-- Interpret the actual range, including scalar and ascending declarations.
example : declaredPortWidth {dir := .input, name := "scalar", width := none} = some 1 := rfl
example : declaredPortWidth {dir := .input, name := "descending", width := some (7, 0)} = some 8 := rfl
example : declaredPortWidth {dir := .input, name := "ascending", width := some (0, 7)} = some 8 := rfl
example : declaredPortWidth {dir := .input, name := "symbolic", width := none, widthExpr := some (.ident "N", .ident "L")} = none := rfl

private def unusedInput : Sparkle.IR.AST.Module :=
  { name := "unused", inputs := [{name := "x", ty := .bitVector 8}], outputs := [{name := "out", ty := .bitVector 8}], wires := [{name := "x", ty := .bitVector 8}], body := [.assign "out" (.const 0 8)] }

private def narrowedUnused : Sparkle.IR.AST.Module :=
  { unusedInput with wires := [{name := "x", ty := .bitVector 1}] }

-- No RHS reads x: both output preservation and the old printing guard pass.
-- Yet 255 at x would not fit the candidate's printer lookup. The new guard
-- rejects it even though its output is the same constant zero.
example : optCheckCore unusedInput narrowedUnused = true := by decide
run_cmd do
  unless Sparkle.IR.PrintCheck.moduleCheck narrowedUnused do
    throwError "unused-input negative must pass the old expression guard"
  unless !(optCheck unusedInput narrowedUnused) do
    throwError "optimizer accepted a narrowed unused input"
example : ¬ Bounded (forwardWidths narrowedUnused)
    (inputEnv 1 (fun _ => some "x") (fun _ => (255#8))) := by
  intro h
  have hx := h "x"
  have hw : forwardWidths narrowedUnused "x" = 1 := by
    simp [forwardWidths, printWidths, narrowedUnused, unusedInput,
      Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
  rw [hw] at hx
  change 255 < 2 ^ 1 at hx
  omega

example : inputEnv 2 (fun j => if j = 0 then some "a" else some "b")
    (fun j => if j = 0 then (255#8) else 17#8) "b" = 17 := by decide
example : inputEnv 0 (fun _ => none) (fun _ => (255#8)) "other" = 0 := rfl

private def mergeOld : List Stmt :=
  [.assign "x" (.const 7 8), .assign "y" (.const 7 8), .assign "out" (.ref "y")]
private def mergeNew : List Stmt :=
  [.assign "x" (.const 7 8), .assign "y" (.ref "x"), .assign "out" (.ref "x")]
private def mergeWidths (x : String) : Nat := if x = "out" then 0 else 8

example : Sparkle.IR.RegDedup.validateMerge mergeWidths mergeOld mergeNew = true := by decide
example : Sparkle.IR.RegDedup.validateMerge
    (fun x => if x = "y" then 16 else mergeWidths x) mergeOld mergeNew = false := by decide

theorem merged_uniform : Tools.ShippingPostSoundness.UniformStmts mergeWidths 8 mergeNew := by
  apply Tools.ShippingPostSoundness.validateMerge_sized (old := mergeOld) (by decide)
  intro s hs
  simp only [mergeOld, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact ⟨_, _, rfl, .const 7 8, Or.inl (by decide)⟩
  · exact ⟨_, _, rfl, .const 7 8, Or.inl (by decide)⟩
  · exact ⟨_, _, rfl, SizedExpr.ref "y", Or.inr rfl⟩

example : ¬ SizedExpr (fun _ => 8) (.op .add [.const 1 8, .const 2 8]) 16 := by
  intro h
  have hw := h.width
  simp [widthOf] at hw

def hashBinder {dom : Sparkle.Core.Domain.DomainConfig}
    («a#» : Sparkle.Core.Signal.Signal dom (BitVec 8)) : Sparkle.Core.Signal.Signal dom (BitVec 8) :=
  «a#»

-- Known shipping defect, not a passing correctness example. Keep the real
-- successful source-to-text reproduction until naming is repaired. The
-- forward theorem excludes it through its explicit name-stability premise.
def hashCollision {dom : Sparkle.Core.Domain.DomainConfig}
    («a#» «a##» : Sparkle.Core.Signal.Signal dom (BitVec 8)) :
    Sparkle.Core.Signal.Signal dom (BitVec 8) := «a#» + «a##»

def unusedSignalInput {dom : Sparkle.Core.Domain.DomainConfig}
    (_a : Sparkle.Core.Signal.Signal dom (BitVec 8)) : Sparkle.Core.Signal.Signal dom (BitVec 8) :=
  Sparkle.Core.Signal.Signal.pure 0

-- The wrapper is tied to the printed tree, and does not silently discard
-- unsupported semantics when reading its items.
example : combItems [.regDecl "r" none none] = none := rfl
example : combItems [.instantiation "sub" "u" []] = none := rfl
example : combItems [.wireDecl "w" none (some (.lit (.decimal (some 8) 0)))] = none := rfl

run_cmd liftTermElabM do
  for name in [``fragA, ``fragB, ``fragC, ``fragD, ``dupLit, ``unusedSignalInput] do
    let (core, _) ← synthesizeCombinationalCore name [] false
    unless forwardCheck core do
      throwError "forward check rejected the core entry result: {name}"
    let (m, _) ← synthesizeCombinational name
    unless Sparkle.IR.PrintCheck.inputWidthsAgree m (checkedOptimize m) do
      throwError "optimized input widths changed: {name}"
    unless Sparkle.IR.PrintCheck.moduleCheck m &&
        optCheck m (Sparkle.IR.Optimize.optimizeModule m) do
      throwError "expected the guarded optimizer to accept the real candidate: {name}"
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
  unless optCheckCore m bad do
    throwError "negative control must pass the output-only optimizer check"
  unless !(optCheck m bad) do
    throwError "guarded optimizer accepted the mismatched-width candidate"
  unless !(forwardCheck bad) do
    throwError "forward check accepted mismatched assignment width"
  let (named, _) ← synthesizeCombinationalCore ``hashBinder [] false
  unless named.wires.any (fun p => Sparkle.Backend.Verilog.sanitizeName p.name != p.name) do
    throwError "name-stability negative control unexpectedly has stable names"
  unless !(forwardCheck named) do
    throwError "forward check unexpectedly accepted the unstable-name core module"
  let (collision, _) ← synthesizeCombinational ``hashCollision
  unless collision.inputs.length == 2 && (collision.inputs.map (·.name)).Nodup do
    throwError "collision probe must start with two distinct IR input names"
  let some sv := emitAstModule (checkedOptimize collision)
    | throwError "collision reproduction unexpectedly failed AST emission"
  let inputNames := (sv.ports.filter (fun p => p.dir == .input)).map (·.name)
  unless inputNames.length == 2 && !(decide inputNames.Nodup) do
    throwError "known printed-name collision changed: update the ledger and this reproduction"
  unless !(forwardCheck (checkedOptimize collision)) do
    throwError "forward check must exclude the known printed-name collision"
  logInfo "KNOWN NAME BUG: successful synthesis of hashCollision emits duplicate AST input names; excluded by the theorem's name premise, not fixed"

run_cmd do
  if (← get).messages.hasErrors then throwError "SV bridge regression failed"
  for name in [``evalAssigns_widths, ``forwardCheck_sound, ``combItems_append,
      ``combItems_wires, ``body_combItems, ``module_combItems, ``module_forward,
      ``compiledFragment_forward, ``compiledFragment_forward_with_initial,
      ``compiled_inputWidths, ``checkedOptimize_inputWidths,
      ``compiled_inputTypes, ``compiled_inputDecls, ``emitAstModule_input,
      ``emitAstModule_ports, ``astPort_bits,
      ``inputEnv_input, ``inputEnv_bounded, ``fragA_initialized_sv] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected SV bridge axiom: {name}: {ax}"
  for name in [``fragA_core_forward, ``core_forwardCheck, ``postReady_forwardCheck,
      ``dropZeroWidth_sized, ``Tools.ShippingTranslateSoundness.SizedExpr.width,
      ``Tools.ShippingSVBridge.SizedExpr.forward] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected core-width axiom: {name}: {ax}"
  for name in [``fragA_synthesized_forward, ``synthesized_forwardCheck, ``uniform_forwardCheck,
      ``merged_uniform, ``Tools.ShippingPostSoundness.validateStep_sized,
      ``Tools.ShippingPostSoundness.validateMerge_sized,
      ``Tools.ShippingPostSoundness.mergeDuplicates_sized,
      ``Tools.ShippingPostSoundness.postprocess_sized,
      ``Tools.ShippingPostSoundness.synthesizeCombinational_sized,
      ``printExpr_sound, ``printCheck_forward, ``synthesized_printCheck,
      ``checkedOptimize_printCheck, ``compiled_forwardCheck, ``fragA_compiled_forward] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected postprocessing-width axiom: {name}: {ax}"
  logInfo "SHIPPING SYNTHESIZED WIDTH OK: cleanup, merge and guarded optimizer preserve the source-derived check; standard axioms only"
  logInfo "SHIPPING CORE WIDTH OK: core forwardCheck derived under name stability; standard axioms only"
  logInfo "SHIPPING SV BRIDGE OK: forwardCheck and bounded-initialization premises discharged; source inputs reach actual unsigned SV port declarations at the proved width; names and text interpretation remain explicit"

end Sparkle.Tests.Compiler.ShippingSVBridgeTest
