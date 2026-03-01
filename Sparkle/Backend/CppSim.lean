/-
  C++ Simulation Backend

  Generates C++ simulation code from the IR.
  Produces a C++ class with eval()/tick()/reset() methods.
-/

import Sparkle.IR.AST
import Sparkle.IR.Type

namespace Sparkle.Backend.CppSim

open Sparkle.IR.AST
open Sparkle.IR.Type

-- Helper to embed literal braces in string interpolation
private def ob : String := "{"
private def cb : String := "}"

/-- Build a name-to-type map from a module's ports and wires -/
def buildTypeMap (m : Module) : List (String × HWType) :=
  let inputMap := m.inputs.map fun (p : Port) => (p.name, p.ty)
  let outputMap := m.outputs.map fun (p : Port) => (p.name, p.ty)
  let wireMap := m.wires.map fun (p : Port) => (p.name, p.ty)
  inputMap ++ outputMap ++ wireMap

/-- Look up bit-width for a name in the type map -/
def lookupWidth (typeMap : List (String × HWType)) (name : String) : Nat :=
  match typeMap.find? (fun (n, _) => n == name) with
  | some (_, ty) => ty.bitWidth
  | none => 32

/-- Sanitize a name to be a valid C++ identifier -/
def sanitizeName (name : String) : String :=
  name.replace "." "_"
    |>.replace "-" "_"
    |>.replace " " "_"
    |>.replace "'" "_prime"
    |>.replace "#" ""

/-- Convert HWType to C++ type string -/
def emitCppType : HWType → String
  | .bit => "uint8_t"
  | .bitVector w =>
    if w ≤ 8 then "uint8_t"
    else if w ≤ 16 then "uint16_t"
    else if w ≤ 32 then "uint32_t"
    else "uint64_t"
  | .array size elemType =>
    "std::array<" ++ emitCppType elemType ++ ", " ++ toString size ++ ">"

/-- Check if a width needs masking (not a native C++ integer width) -/
def needsMask (w : Nat) : Bool :=
  w != 8 && w != 16 && w != 32 && w != 64

/-- Emit a bit mask expression for the given width -/
def emitMask (w : Nat) : String :=
  if !needsMask w then ""
  else if w == 1 then "1"
  else s!"((1ULL << {w}) - 1)"

/-- Wrap an expression with a mask if the width requires it -/
def applyMask (expr : String) (w : Nat) : String :=
  let mask := emitMask w
  if mask.isEmpty then expr
  else s!"(({expr}) & {mask})"

/-- Convert Operator to C++ operator symbol -/
def emitCppOperator (op : Operator) : String :=
  match op with
  | .and => "&"
  | .or  => "|"
  | .xor => "^"
  | .not => "~"
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .eq  => "=="
  | .lt_u => "<"
  | .lt_s => "<"
  | .le_u => "<="
  | .le_s => "<="
  | .gt_u => ">"
  | .gt_s => ">"
  | .ge_u => ">="
  | .ge_s => ">="
  | .shl => "<<"
  | .shr => ">>"
  | .asr => ">>"
  | .neg => "-"
  | .mux => "?"

/-- Get signed cast type for a given width -/
def signedCastType (w : Nat) : String :=
  if w ≤ 8 then "int8_t"
  else if w ≤ 16 then "int16_t"
  else if w ≤ 32 then "int32_t"
  else "int64_t"

/-- Best-effort width inference for an expression -/
partial def inferExprWidth (typeMap : List (String × HWType)) : Expr → Nat
  | .const _ w => w
  | .ref name => lookupWidth typeMap name
  | .slice _ hi lo => hi - lo + 1
  | .concat args =>
    args.foldl (fun acc arg => acc + inferExprWidth typeMap arg) 0
  | .index arr _ =>
    match arr with
    | .ref name =>
      match typeMap.find? (fun (n, _) => n == name) with
      | some (_, .array _ elemType) => elemType.bitWidth
      | _ => 32
    | _ => 32
  | .op .eq _ | .op .lt_u _ | .op .lt_s _ | .op .le_u _
  | .op .le_s _ | .op .gt_u _ | .op .gt_s _ | .op .ge_u _
  | .op .ge_s _ => 1
  | .op .mux args =>
    match args with
    | [_, thenVal, _] => inferExprWidth typeMap thenVal
    | _ => 32
  | .op _ args =>
    match args with
    | [arg1, _] => inferExprWidth typeMap arg1
    | [arg1] => inferExprWidth typeMap arg1
    | _ => 32

/-- Convert IR expression to C++ expression -/
partial def emitExpr (typeMap : List (String × HWType)) (e : Expr) : String :=
  match e with
  | .const value width =>
    let cppType := emitCppType (.bitVector width)
    if value < 0 then
      let modulus : Int := (2 : Int) ^ width
      let unsigned := ((value % modulus) + modulus) % modulus
      s!"({cppType})0x{Nat.toDigits 16 unsigned.toNat |> String.ofList}ULL"
    else
      s!"({cppType}){value}ULL"

  | .ref name =>
    sanitizeName name

  | .concat args =>
    -- Concat: shift+OR chain
    match args with
    | [] => "(uint8_t)0ULL"
    | [single] => emitExpr typeMap single
    | _ =>
      let widths := args.map (inferExprWidth typeMap ·)
      let totalWidth := widths.foldl (· + ·) 0
      let resultType := emitCppType (.bitVector totalWidth)
      let pairs := args.zip widths
      -- foldr: process right-to-left, accumulating shift from LSB
      let (terms, _) := pairs.foldr (fun (arg, w) (acc, shift) =>
        let expr := emitExpr typeMap arg
        let term := if shift > 0 then
          "((" ++ resultType ++ ")" ++ expr ++ " << " ++ toString shift ++ ")"
        else
          "(" ++ resultType ++ ")" ++ expr
        (term :: acc, shift + w)
      ) ([], 0)
      "(" ++ String.intercalate " | " terms ++ ")"

  | .slice e hi lo =>
    let sliceWidth := hi - lo + 1
    let mask := emitMask sliceWidth
    if lo == 0 then
      if mask.isEmpty then emitExpr typeMap e
      else s!"({emitExpr typeMap e} & {mask})"
    else
      let shifted := s!"({emitExpr typeMap e} >> {lo})"
      if mask.isEmpty then shifted
      else s!"({shifted} & {mask})"

  | .index arr idx =>
    s!"{emitExpr typeMap arr}[{emitExpr typeMap idx}]"

  | .op .mux args =>
    match args with
    | [cond, thenVal, elseVal] =>
      s!"({emitExpr typeMap cond} ? {emitExpr typeMap thenVal} : {emitExpr typeMap elseVal})"
    | _ => "/* ERROR: mux requires 3 arguments */"

  | .op .not args =>
    match args with
    | [arg] => s!"(~{emitExpr typeMap arg})"
    | _ => "/* ERROR: not requires 1 argument */"

  | .op .neg args =>
    match args with
    | [arg] => s!"(-{emitExpr typeMap arg})"
    | _ => "/* ERROR: neg requires 1 argument */"

  | .op operator args =>
    match args with
    | [arg1, arg2] =>
      match operator with
      | .lt_s | .le_s | .gt_s | .ge_s =>
        let w := inferExprWidth typeMap arg1
        let stype := signedCastType w
        s!"(({stype}){emitExpr typeMap arg1} {emitCppOperator operator} ({stype}){emitExpr typeMap arg2} ? 1 : 0)"
      | .asr =>
        let w := inferExprWidth typeMap arg1
        let stype := signedCastType w
        let utype := emitCppType (.bitVector w)
        s!"(({utype})(({stype}){emitExpr typeMap arg1} >> {emitExpr typeMap arg2}))"
      | .eq | .lt_u | .le_u | .gt_u | .ge_u =>
        s!"({emitExpr typeMap arg1} {emitCppOperator operator} {emitExpr typeMap arg2} ? 1 : 0)"
      | _ =>
        s!"({emitExpr typeMap arg1} {emitCppOperator operator} {emitExpr typeMap arg2})"
    | _ => s!"/* ERROR: operator with wrong arity */"

/-- Parts of a C++ class generated from a single statement -/
structure StmtParts where
  declarations : List String
  evalBody     : List String
  tickBody     : List String
  resetBody    : List String

instance : Append StmtParts where
  append a b :=
    { declarations := a.declarations ++ b.declarations
    , evalBody := a.evalBody ++ b.evalBody
    , tickBody := a.tickBody ++ b.tickBody
    , resetBody := a.resetBody ++ b.resetBody }

def StmtParts.empty : StmtParts :=
  { declarations := [], evalBody := [], tickBody := [], resetBody := [] }

/-- Emit a C++ constant expression for an init value with given width -/
def emitInitValue (initValue : Int) (width : Nat) : String :=
  let cppType := emitCppType (.bitVector width)
  if initValue < 0 then
    let modulus : Int := (2 : Int) ^ width
    let unsigned := ((initValue % modulus) + modulus) % modulus
    s!"({cppType})0x{Nat.toDigits 16 unsigned.toNat |> String.ofList}ULL"
  else
    s!"({cppType}){initValue}ULL"

/-- Split a statement into declaration/eval/tick/reset parts -/
def emitStmt (stmt : Stmt) (typeMap : List (String × HWType))
    (design : Option Design := none) : StmtParts :=
  match stmt with
  | .assign lhs rhs =>
    let width := lookupWidth typeMap lhs
    let expr := emitExpr typeMap rhs
    let masked := applyMask expr width
    { declarations := []
    , evalBody := [s!"        {sanitizeName lhs} = {masked};"]
    , tickBody := []
    , resetBody := [] }

  | .register output _clock _reset input initValue =>
    let width := lookupWidth typeMap output
    let cppType := emitCppType (.bitVector width)
    let outName := sanitizeName output
    let nextName := s!"{outName}_next"
    let inputExpr := applyMask (emitExpr typeMap input) width
    let initExpr := emitInitValue initValue width
    { declarations := [s!"    {cppType} {outName};", s!"    {cppType} {nextName};"]
    , evalBody := [s!"        {nextName} = {inputExpr};"]
    , tickBody := [s!"        {outName} = {nextName};"]
    , resetBody := [s!"        {outName} = {initExpr};"] }

  | .memory name addrWidth dataWidth _clock writeAddr writeData writeEnable readAddr readData comboRead =>
    let memSize := 2 ^ addrWidth
    let elemType := emitCppType (.bitVector dataWidth)
    let memName := sanitizeName name
    let rdName := sanitizeName readData
    let memDecl := "    std::array<" ++ elemType ++ ", " ++ toString memSize ++ "> " ++ memName ++ ";"
    if comboRead then
      { declarations := [memDecl]
      , evalBody := [s!"        {rdName} = {memName}[{emitExpr typeMap readAddr}];"]
      , tickBody := [s!"        if ({emitExpr typeMap writeEnable}) {memName}[{emitExpr typeMap writeAddr}] = {emitExpr typeMap writeData};"]
      , resetBody := [s!"        {memName}.fill(0);"] }
    else
      let addrLatch := s!"{memName}_raddr"
      let addrType := emitCppType (.bitVector addrWidth)
      { declarations := [memDecl, s!"    {addrType} {addrLatch};"]
      , evalBody := [s!"        {addrLatch} = {emitExpr typeMap readAddr};"]
      , tickBody :=
          [ s!"        if ({emitExpr typeMap writeEnable}) {memName}[{emitExpr typeMap writeAddr}] = {emitExpr typeMap writeData};"
          , s!"        {rdName} = {memName}[{addrLatch}];" ]
      , resetBody := [s!"        {memName}.fill(0);"] }

  | .inst moduleName instName connections =>
    let className := sanitizeName moduleName
    let iName := sanitizeName instName
    -- Look up sub-module in design to determine input/output ports
    let subModule := design.bind fun (d : Design) => d.findModule moduleName
    let outputPortNames : List String := match subModule with
      | some sm => sm.outputs.map fun (p : Port) => p.name
      | none => []
    let inputConns := connections.filterMap fun (portName, expr) =>
      if !outputPortNames.contains portName then
        some s!"        {iName}.{sanitizeName portName} = {emitExpr typeMap expr};"
      else none
    let outputConns := connections.filterMap fun (portName, expr) =>
      if outputPortNames.contains portName then
        match expr with
        | .ref wireName => some s!"        {sanitizeName wireName} = {iName}.{sanitizeName portName};"
        | _ => none
      else none
    { declarations := [s!"    {className} {iName};"]
    , evalBody := inputConns ++ [s!"        {iName}.eval();"] ++ outputConns
    , tickBody := [s!"        {iName}.tick();"]
    , resetBody := [s!"        {iName}.reset();"] }

/-- Emit a complete C++ class for a module -/
def emitModule (m : Module) (design : Option Design := none) : String :=
  if m.isPrimitive then
    s!"// Primitive module: {m.name}\n// (blackbox - not generated)\n\n"
  else
    let typeMap := buildTypeMap m
    let className := sanitizeName m.name

    -- Collect all StmtParts
    let allParts := m.body.map (emitStmt · typeMap design)

    -- Input port declarations
    let inputDecls := m.inputs.map fun (p : Port) =>
      s!"    {emitCppType p.ty} {sanitizeName p.name};"

    -- Output port declarations
    let outputDecls := m.outputs.map fun (p : Port) =>
      s!"    {emitCppType p.ty} {sanitizeName p.name};"

    -- Internal wire declarations (excluding ports and register outputs)
    let portNames := (m.inputs ++ m.outputs).map fun (p : Port) => p.name
    let registerNames := m.body.filterMap fun s => match s with
      | .register output .. => some output
      | _ => none
    let internalWires := m.wires.filter fun (w : Port) =>
      !portNames.contains w.name && !registerNames.contains w.name
    let wireDecls := internalWires.map fun (p : Port) =>
      s!"    {emitCppType p.ty} {sanitizeName p.name};"

    -- Extra declarations from statements (registers, memories, sub-instances)
    let stmtDecls := allParts.foldl (fun acc p => acc ++ p.declarations) []

    -- Eval/tick/reset bodies
    let evalBody := allParts.foldl (fun acc p => acc ++ p.evalBody) []
    let tickBody := allParts.foldl (fun acc p => acc ++ p.tickBody) []
    let resetBody := allParts.foldl (fun acc p => acc ++ p.resetBody) []

    -- Assemble the class
    let header := s!"// Generated by Sparkle HDL - C++ Simulation Model\n// Module: {m.name}\n\n"
    let classOpen := "class " ++ className ++ " {\npublic:\n"

    let inputSection := if inputDecls.isEmpty then "" else
      "    // Input ports\n" ++ String.intercalate "\n" inputDecls ++ "\n\n"

    let outputSection := if outputDecls.isEmpty then "" else
      "    // Output ports\n" ++ String.intercalate "\n" outputDecls ++ "\n\n"

    let wireSection := if wireDecls.isEmpty then "" else
      "    // Internal wires\n" ++ String.intercalate "\n" wireDecls ++ "\n\n"

    let stmtDeclSection := if stmtDecls.isEmpty then "" else
      "    // Registers and memories\n" ++ String.intercalate "\n" stmtDecls ++ "\n\n"

    let constructor := "    " ++ className ++ "() { reset(); }\n\n"

    let resetMethod :=
      "    void reset() {\n" ++
      (if resetBody.isEmpty then "" else String.intercalate "\n" resetBody ++ "\n") ++
      "    }\n\n"

    let evalMethod :=
      "    void eval() {\n" ++
      (if evalBody.isEmpty then "" else String.intercalate "\n" evalBody ++ "\n") ++
      "    }\n\n"

    let tickMethod :=
      "    void tick() {\n" ++
      (if tickBody.isEmpty then "" else String.intercalate "\n" tickBody ++ "\n") ++
      "    }\n"

    let classClose := "};\n"

    header ++ classOpen ++ inputSection ++ outputSection ++ wireSection ++
    stmtDeclSection ++ constructor ++ resetMethod ++ evalMethod ++ tickMethod ++ classClose

/-- Convert a single module to C++ simulation code with includes -/
def toCppSim (m : Module) : String :=
  let includes := "#include <cstdint>\n#include <array>\n#include <cstring>\n\n"
  includes ++ emitModule m

/-- Convert a full design to C++ simulation code -/
def toCppSimDesign (d : Design) : String :=
  let header := "#include <cstdint>\n#include <array>\n#include <cstring>\n\n"
  -- Emit sub-modules before top module (dependency order)
  let topName := d.topModule
  let subModules := d.modules.filter fun (m : Module) => m.name != topName
  let topModule := d.modules.find? fun (m : Module) => m.name == topName
  let subCode := subModules.map (emitModule · (some d))
  let topCode := match topModule with
    | some m => [emitModule m (some d)]
    | none => []
  header ++ String.intercalate "\n" (subCode ++ topCode)

end Sparkle.Backend.CppSim
