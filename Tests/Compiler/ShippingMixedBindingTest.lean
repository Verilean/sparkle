import Tools.ShippingMixedBindingSoundness
import Tests.Compiler.ShippingMixedEntryTest
import Tests.Compiler.ShippingMixedSourceBridgeTest

namespace Sparkle.Tests.Compiler.ShippingMixedBindingTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.ShippingEntrySoundness Tools.ShippingMixedEntrySoundness
open Tools.ShippingMixedPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingMixedBindingSoundness Tools.ShippingTypedPostSoundness
open Tools.SVParser.AST Tools.SVParser.EmitSem
open Tools.ShippingTypedExprSoundness Tools.ShippingSVBridge
open Tools.SVParser.EmitAst
open Tools.ShippingMixedDeclSoundness Tools.ShippingDeclWidths Tools.ShippingPrintSoundness

/-- The public endpoint asks for no printable-declaration certificate. -/
theorem shipping_syntax {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        MixedSourcePreserves declName bs body (SyntaxValue m) :=
  synthesizeCombinational_mixed_syntax hr

open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMixedSourceBridge Tools.ShippingMuxLoweringSoundness
open Sparkle.Tests.Compiler.ShippingMixedSourceBridgeTest

theorem nested_syntax {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
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
      SyntaxValue m initial mems (encodeBool
        ((ShippingMixedRecursionTest.source (bools 1) (bits 2 8) (bits 3 8)).val tick)) :=
  syntax_source_of_env hr env (by rfl) source_peel (by decide)
    ShippingMixedRecursionTest.term_wf bool_position bits_position


def refsDeclared (names : List String) : SVExpr → Bool
  | .lit _ => true
  | .ident x => names.contains x
  | .binary _ a b => refsDeclared names a && refsDeclared names b
  | .ternary c t f => refsDeclared names c && refsDeclared names t && refsDeclared names f
  | _ => false

run_cmd liftTermElabM do
  let mut count := 0
  let mut accepted := 0
  let mut retained := 0
  for name in [``ShippingMixedRecursionTest.source, ``ShippingMixedEntryTest.passthrough,
      ``ShippingMixedEntryTest.constant, ``ShippingMixedEntryTest.oneBit,
      ``ShippingMixedSourceBridgeTest.reordered] do
    let (raw, _) ← synthesizeCombinationalCore name [] false
    let (actual, _) ← synthesizeCombinational name
    for post in [dropZeroWidthModule raw, mergeDuplicates (dropZeroWidthModule raw), actual] do
      if optCheck post (Sparkle.IR.Optimize.optimizeModule post) &&
          assignmentOrderCheck (Sparkle.IR.Optimize.optimizeModule post).body then
        accepted := accepted + 1
      else
        retained := retained + 1
      let m := checkedOptimize post
      let some sv := emitAstModule m | throwError "mixed syntax AST emission failed"
      let some pairs := combItems sv.items | throwError "mixed syntax body extraction failed"
      let names := (declarationTable sv).map Prod.fst
      unless Sparkle.IR.ModuleNames.legal sv.name do throwError "invalid mixed module name"
      for name in names do
        unless Sparkle.IR.ModuleNames.legal name do throwError "invalid mixed data name"
      for pair in pairs do
        match pair with
        | .assign lhs rhs =>
          unless names.contains lhs && refsDeclared names rhs do
            throwError "unbound mixed assignment: {name}: {lhs}"
        | _ => throwError "unexpected mixed memory read"
      let countWires := (m.wires.filter fun p => !((m.inputs ++ m.outputs).map (·.name)).contains p.name).length
      unless renderModule m.name countWires sv == some (verilogOf post) do
        throwError "mixed syntax shipping text mismatch"
      count := count + 1
  unless count == 15 && accepted > 0 && retained > 0 do
    throwError "mixed syntax branches not exercised"
  logInfo m!"MIXED SYNTAX: {count} real entry/postprocessing paths; {accepted} accepted, {retained} retained; all targets/references bound"

run_cmd do
  if (← get).messages.hasErrors then throwError "mixed syntax regression failed"
  for name in [``TypedExpr.refs_positive, ``body_combItems_names, ``module_combItems_names,
      ``validateMerge_go_output, ``mergeDuplicates_output, ``emitLeaves_postReady,
      ``synthesizeMixedCertified_sound, ``positive_declared, ``typed_bindings, ``sized_of_flat,
      ``printWidths_decl, ``post_printCheck, ``post_syntax, ``post_control_syntax,
      ``checked_syntax, ``rendered_of_entry, ``mixed_syntax, ``synthesizeCombinational_mixed_syntax,
      ``syntax_source_of_env, ``shipping_syntax, ``nested_syntax] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mixed syntax axiom: {name}: {ax}"
  logInfo "MIXED SYNTAX ENDPOINT: actual source to complete shipping grammar and binding; SV value transfer/settling remain open"

end Sparkle.Tests.Compiler.ShippingMixedBindingTest
