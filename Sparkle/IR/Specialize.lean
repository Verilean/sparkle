/-
  Concrete specialization for retained-parameter IR.

  Backends with a fixed data layout (CSim, CUDA, SMT, and similar consumers)
  cannot preserve a SystemVerilog-style module parameter in their ABI. This
  pass evaluates one explicit parameter configuration and removes every
  symbolic width before those backends run.
-/

import Sparkle.IR.AST

namespace Sparkle.IR.Specialize

open Sparkle.IR.AST
open Sparkle.IR.Type

/-- One explicit retained-parameter configuration. -/
abbrev Bindings := List (String × Nat)

private def duplicateName? (names : List String) : Option String :=
  names.find? fun name => (names.filter (· == name)).length > 1

private def validateParameterDeclarations (modules : List Module) : Except String Unit := do
  for hardwareModule in modules do
    let names := hardwareModule.parameters.map (·.name)
    if let some name := duplicateName? names then
      throw s!"module '{hardwareModule.name}' declares duplicate retained parameter '{name}'"

/-- Validate that an explicit configuration names every retained parameter
    exactly once and does not contain misspelled/irrelevant names. Parameter
    names are design-global because the current `Stmt.inst` IR has no
    per-instance parameter override map. -/
private def validateBindings (modules : List Module) (bindings : Bindings) : Except String Unit := do
  validateParameterDeclarations modules
  let bindingNames := bindings.map (·.1)
  if let some name := duplicateName? bindingNames then
    throw s!"duplicate specialization binding for parameter '{name}'"
  let parameterNames := modules.flatMap fun hardwareModule =>
    hardwareModule.parameters.map (·.name)
  for (name, value) in bindings do
    if !parameterNames.contains name then
      throw s!"unknown specialization binding '{name}'"
    if value == 0 then
      throw s!"specialization binding for parameter '{name}' has zero width; values must be positive"
  for name in parameterNames do
    if bindings.lookup name |>.isNone then
      throw s!"missing specialization binding for parameter '{name}'"

private def requirePositive (context : String) (value : Nat) : Except String Nat := do
  if value == 0 then throw s!"{context} specializes to zero width"
  return value

/-- Replace a symbolic hardware width with one concrete positive width.
    Existing concrete zero-bit bookkeeping is preserved so the standard
    optimizer can remove it after specialization. -/
partial def specializeType (bindings : Bindings) (context : String) :
    HWType → Except String HWType
  | .bit => return .bit
  | .bitVector width => return .bitVector width
  | .bitVectorDim dimension => do
    let width ← dimension.evaluate bindings
    return hwTypeFromWidth (← requirePositive context width)
  | .array size elementType => do
    return .array size (← specializeType bindings s!"{context} element" elementType)

private def specializePort (bindings : Bindings) (moduleName : String)
    (port : Port) : Except String Port := do
  return {
    port with
    ty := ← specializeType bindings s!"module '{moduleName}' port '{port.name}'" port.ty
  }

/-- Evaluate symbolic slice bounds and recursively specialize every expression
    constructor. -/
partial def specializeExpr (bindings : Bindings) : Expr → Except String Expr
  | .const value width => return .const value width
  | .ref name => return .ref name
  | .op operator arguments =>
    return .op operator (← arguments.mapM (specializeExpr bindings))
  | .concat arguments =>
    return .concat (← arguments.mapM (specializeExpr bindings))
  | .slice expression hi lo =>
    return .slice (← specializeExpr bindings expression) hi lo
  | .sliceDim expression hi lo => do
    let concreteHi ← hi.evaluate bindings
    let concreteLo ← lo.evaluate bindings
    if concreteHi < concreteLo then
      throw s!"invalid specialized slice [{concreteHi}:{concreteLo}]: high bound is below low bound"
    return .slice (← specializeExpr bindings expression) concreteHi concreteLo
  | .index array index =>
    return .index (← specializeExpr bindings array) (← specializeExpr bindings index)

/-- Recursively specialize all expression-bearing statement constructors. -/
def specializeStmt (bindings : Bindings) : Stmt → Except String Stmt
  | .assign lhs rhs => return .assign lhs (← specializeExpr bindings rhs)
  | .register output clock reset input initValue =>
    return .register output clock reset (← specializeExpr bindings input) initValue
  | .memory name addrWidth dataWidth clock writeAddr writeData writeEnable
      readAddr readData comboRead => do
    return .memory name addrWidth dataWidth clock
      (← specializeExpr bindings writeAddr)
      (← specializeExpr bindings writeData)
      (← specializeExpr bindings writeEnable)
      (← specializeExpr bindings readAddr)
      readData comboRead
  | .inst moduleName instName connections => do
    let connections ← connections.mapM fun (portName, expression) => do
      return (portName, ← specializeExpr bindings expression)
    return .inst moduleName instName connections

private def specializeModuleUnchecked (hardwareModule : Module)
    (bindings : Bindings) : Except String Module := do
  let inputs ← hardwareModule.inputs.mapM
    (specializePort bindings hardwareModule.name)
  let outputs ← hardwareModule.outputs.mapM
    (specializePort bindings hardwareModule.name)
  let wires ← hardwareModule.wires.mapM
    (specializePort bindings hardwareModule.name)
  let body ← hardwareModule.body.mapM (specializeStmt bindings)
  let assertions ← hardwareModule.assertions.mapM fun (name, expression) => do
    return (name, ← specializeExpr bindings expression)
  return {
    hardwareModule with
    parameters := []
    inputs := inputs
    outputs := outputs
    wires := wires
    body := body
    assertions := assertions
  }

/-- Specialize one module. The supplied bindings must match that module's
    retained parameter declarations exactly. -/
def specializeModule (hardwareModule : Module) (bindings : Bindings) :
    Except String Module := do
  validateBindings [hardwareModule] bindings
  specializeModuleUnchecked hardwareModule bindings

/-- Specialize every module in a design with one explicit configuration.

    The current IR does not encode per-instance parameter overrides, so a name
    shared by multiple modules receives the same value. All declarations must
    be bound explicitly; `Parameter.defaultValue` is metadata for native
    parameter backends and is deliberately not an implicit CSim choice. -/
def specializeDesign (design : Design) (bindings : Bindings) : Except String Design := do
  if (design.findModule design.topModule).isNone then
    throw s!"top module '{design.topModule}' is missing from design"
  validateBindings design.modules bindings
  let modules ← design.modules.mapM (specializeModuleUnchecked · bindings)
  return { design with modules := modules }

end Sparkle.IR.Specialize
