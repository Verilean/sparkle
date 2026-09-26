import Tools.ShippingModuleNames
import Tools.SVParser.Parser

open Lean Elab Command Sparkle.Compiler.Elab
open Sparkle.IR.AST Sparkle.Backend.Verilog Sparkle.IR.ModuleNameCheck
open Sparkle.Core.Signal Sparkle.Core.Domain

-- These deliberately have no namespace: a namespace prefix would turn the
-- emitted name into a non-keyword, and fail to exercise the rejection branch.
def «module» {dom : DomainConfig} (a : Signal dom (BitVec 8)) := a
def «1bad» {dom : DomainConfig} (a : Signal dom (BitVec 8)) := a

namespace Sparkle.Tests.Compiler.ShippingModuleNamesTest

#guard !Sparkle.IR.ModuleNames.legal ""
#guard !Sparkle.IR.ModuleNames.legal "module"
#guard !Sparkle.IR.ModuleNames.legal "always_ff"
#guard !Sparkle.IR.ModuleNames.legal "1bad"
#guard !Sparkle.IR.ModuleNames.legal "$system"
#guard !Sparkle.IR.ModuleNames.legal "日本語"
#guard Sparkle.IR.ModuleNames.legal "_gen_module"
#guard Sparkle.IR.ModuleNames.legal "Module"
#guard Sparkle.IR.ModuleNames.legal "alu_v2"
#guard !checkNames ["a.b", "a_b"]
#guard !checkNames ["a#", "a"]
#guard checkNames ["a.b", "a.b", "other"]
#guard !checkNames ["bad\nname"]

private def child : Sparkle.IR.AST.Module :=
  {name := "a.b", inputs := [⟨"i", .bitVector 8⟩], outputs := [⟨"out", .bitVector 8⟩],
    wires := [], body := [.assign "out" (.ref "i")]}
private def parent : Sparkle.IR.AST.Module :=
  {name := "module_name_probe", inputs := child.inputs, outputs := child.outputs,
    wires := [], body := [.inst child.name "u_child" [("i", .ref "i"), ("out", .ref "out")]]}
private def good : Design := {topModule := parent.name, modules := [child, parent]}
private def aliasDefinition : Design := {topModule := child.name, modules := [child, {child with name := "a_b"}]}
private def aliasReference : Design :=
  {topModule := parent.name, modules := [child, {parent with body := [.inst "a_b" "u_child" []]}]}

#guard checkDesign good
#guard !checkDesign {good with topModule := "missing"}
#guard !checkDesign aliasDefinition
#guard !checkDesign aliasReference
#guard !checkDesign {topModule := child.name, modules := [child, child]}

namespace ModuleAlias
namespace a
@[hardware_module] def b (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := x + Signal.pure (dom := defaultDomain) (1#8)
end a
@[hardware_module] def a_b (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := x + Signal.pure (dom := defaultDomain) (2#8)
def top (x : Signal defaultDomain (BitVec 8)) := a.b x + a_b x
end ModuleAlias

run_cmd liftTermElabM do
  for decl in [``«module», ``«1bad», ``ModuleAlias.top] do
    let refused ← try
      let _ ← synthesizeCombinational decl
      pure false
    catch e =>
      let message ← e.toMessageData.toString
      unless (message.splitOn "Invalid or colliding Verilog module names").length > 1 do
        throwError "unexpected synthesis failure for {decl}: {message}"
      pure true
    unless refused do throwError "invalid module name accepted: {decl}"
  for d in [aliasDefinition, aliasReference, {topModule := child.name, modules := [child, child]}] do
    let refused ← try
      let _ ← validateDesignNames d
      pure false
    catch _ => pure true
    unless refused do throwError "invalid design names accepted"
  let accepted ← validateDesignNames good
  unless accepted.modules.map (·.name) == good.modules.map (·.name) do
    throwError "name validation changed an accepted design"

run_cmd do
  let text := toVerilogDesign good
  let .ok parsed := Tools.SVParser.Parser.parse text
    | throwError "accepted hierarchical design does not parse"
  unless parsed.modules.map (·.name) == ["a_b", "module_name_probe"] do
    throwError "ordinary name normalization changed"
  for m in good.modules do
    let some ast := Tools.SVParser.EmitAst.emitAstModule m
      | throwError "AST emission failed"
    unless ast.name == Sparkle.Backend.Verilog.sanitizeName m.name do throwError "AST module name differs"
  -- Concrete fixture for the external elaboration/simulation regression.
  IO.FS.writeFile "/tmp/sparkle_module_names.sv" (text ++ "\nmodule tb;\n" ++
    "reg [7:0] i; wire [7:0] out; module_name_probe dut(.i(i), .out(out));\n" ++
    "initial begin i = 8'd37; #1; if (out !== 8'd37) $fatal(1); $finish; end\nendmodule\n")

run_cmd do
  if (← get).messages.hasErrors then throwError "module-name regression failed"
  for name in [``Sparkle.IR.ModuleNames.legal_spec, ``checkNames_sound,
      ``check_sound, ``checkDesign_top, ``checkDesign_nodup, ``linkage_iff,
      ``Tools.ShippingEntrySoundness.finishSynth_returns,
      ``Tools.ShippingModuleNames.validateDesignNames_returns,
      ``Tools.ShippingModuleNames.hierarchical_names,
      ``Tools.ShippingModuleNames.hierarchical_parameters_names,
      ``Tools.ShippingModuleNames.hierarchical_linkage,
      ``Tools.ShippingModuleNames.emitted_name,
      ``Tools.ShippingModuleNames.emitted_instance_target,
      ``Tools.ShippingModuleNames.hierarchical_instance_linkage,
      ``Tools.ShippingModuleNames.compiled_moduleName] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected module-name axiom: {name}: {ax}"
  logInfo "SHIPPING MODULE NAMES OK: successful synthesis derives lexical validity; successful hierarchy derives unique emitted definitions and no definition/reference aliases; standard axioms only"
end Sparkle.Tests.Compiler.ShippingModuleNamesTest
