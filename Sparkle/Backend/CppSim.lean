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
    else if w ≤ 64 then "uint64_t"
    else  -- Wide type: use array of uint32_t words
      let nWords := (w + 31) / 32
      "std::array<uint32_t, " ++ toString nWords ++ ">"
  | .array size elemType =>
    "std::array<" ++ emitCppType elemType ++ ", " ++ toString size ++ ">"

/-- Check if a width needs masking (not a native C++ integer width).
    1-bit values are stored in uint8_t and comparisons return 0/1, so no mask needed. -/
def needsMask (w : Nat) : Bool :=
  w != 8 && w != 16 && w != 32 && w != 64

/-- Emit a bit mask expression for the given width -/
def emitMask (w : Nat) : String :=
  if !needsMask w then ""
  else if w == 1 then "1"
  else
    -- Use hex constant for readability and to help compiler optimization
    let mask := (2 ^ w - 1 : Nat)
    s!"0x{Nat.toDigits 16 mask |> String.ofList}ULL"

/-- Wrap an expression with a mask if the width requires it -/
def applyMask (expr : String) (w : Nat) : String :=
  let mask := emitMask w
  if mask.isEmpty then expr
  else s!"(({expr}) & {mask})"

/-- Check if an IR expression produces a result that is already correctly masked.
    Invariant: every assignment applies a mask, so .ref reads yield masked values. -/
partial def exprIsMasked (w : Nat) : Expr → Bool
  | .const _ _ => true  -- constants are always exact
  | .ref _ => true  -- all wires are masked at their assignment site
  | .op .eq _ | .op .lt_u _ | .op .lt_s _ | .op .le_u _
  | .op .le_s _ | .op .gt_u _ | .op .gt_s _ | .op .ge_u _
  | .op .ge_s _ => w == 1  -- comparisons produce 0 or 1
  | .slice _ hi lo => (hi - lo + 1) == w  -- slice is already exact width
  | .op .mux [_, t, e] => exprIsMasked w t && exprIsMasked w e
  | .op .and [a, b] => exprIsMasked w a || exprIsMasked w b  -- AND is masked if either operand is
  | .op .or [a, b] => exprIsMasked w a && exprIsMasked w b  -- OR of masked stays in width
  | .op .xor [a, b] => exprIsMasked w a && exprIsMasked w b  -- XOR of masked stays in width
  | .op .shr _ => true  -- right-shift moves bits toward LSB, no new upper bits
  | .op .asr _ => true  -- cast to unsigned in emitExpr handles width
  | _ => !needsMask w  -- native widths don't need masking

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
    -- Use appropriate literal suffix: U for ≤32bit, ULL for >32bit
    let suffix := if width > 32 then "ULL" else "U"
    if value < 0 then
      let modulus : Int := (2 : Int) ^ width
      let unsigned := ((value % modulus) + modulus) % modulus
      s!"({cppType})0x{Nat.toDigits 16 unsigned.toNat |> String.ofList}{suffix}"
    else
      s!"({cppType}){value}{suffix}"

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
      if totalWidth > 64 then
        -- Wide concat: build std::array<uint32_t, N> initializer
        let nWords := (totalWidth + 31) / 32
        -- For now, if total ≤ 96 bits (3 words), build word-by-word
        -- Each word = bits [i*32+31 : i*32] of the concatenated result
        -- Simplified: delegate to narrow concat for the lower 64 bits,
        -- and handle upper bits separately
        let lowerArgs := args  -- all args contribute to the result
        let lowerWidths := widths
        -- Build as: {word0, word1, word2}
        -- word0 = lower 32 bits, word1 = bits [63:32], word2 = bits [95:64]
        -- This is complex in general; for the signExtend pattern specifically
        -- (concat of sign-extension bits and original value), generate inline
        let pairs := lowerArgs.zip lowerWidths
        let (terms, _) := pairs.foldr (fun (arg, w) (acc, shift) =>
          let expr := emitExpr typeMap arg
          let term := if shift > 0 then
            s!"(({emitCppType (.bitVector 64)}){expr} << {shift})"
          else
            s!"({emitCppType (.bitVector 64)}){expr}"
          (term :: acc, shift + w)
        ) ([], 0)
        -- Build std::array initializer from terms
        let combined := "(" ++ String.intercalate " | " terms ++ ")"
        -- Pack into array: {low32, mid32, high32}
        let w0 := s!"(uint32_t)({combined} & 0xffffffffULL)"
        let w1 := s!"(uint32_t)(({combined} >> 32) & 0xffffffffULL)"
        let w2 := if nWords > 2 then s!"(uint32_t)(({combined} >> 64) & 0xffffffffULL)" else "0U"
        "std::array<uint32_t, " ++ toString nWords ++ ">{" ++ "{" ++ w0 ++ ", " ++ w1 ++ (if nWords > 2 then ", " ++ w2 else "") ++ "}" ++ "}"
      else
        let resultType := emitCppType (.bitVector totalWidth)
        let pairs := args.zip widths
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
    -- Check if the source expression is wider than 64 bits (std::array type)
    let srcWidth := inferExprWidth typeMap e
    if srcWidth > 64 then
      -- Wide integer: extract from std::array<uint32_t, N>
      -- Access the correct word(s) and shift/mask
      let wordIdx := lo / 32
      let bitOffset := lo % 32
      let srcExpr := emitExpr typeMap e
      if sliceWidth <= 32 then
        let mask := (2 ^ sliceWidth - 1 : Nat)
        let maskStr := s!"0x{Nat.toDigits 16 mask |> String.ofList}ULL"
        if bitOffset == 0 then
          s!"((uint64_t){srcExpr}[{wordIdx}] & {maskStr})"
        else if bitOffset + sliceWidth <= 32 then
          s!"(((uint64_t){srcExpr}[{wordIdx}] >> {bitOffset}) & {maskStr})"
        else
          -- Spans two words
          let bitsFromLow := 32 - bitOffset
          let bitsFromHigh := sliceWidth - bitsFromLow
          let maskHigh := (2 ^ bitsFromHigh - 1 : Nat)
          s!"((((uint64_t){srcExpr}[{wordIdx}] >> {bitOffset}) | ((uint64_t){srcExpr}[{wordIdx + 1}] << {bitsFromLow})) & {maskStr})"
      else if sliceWidth <= 64 then
        -- Result fits in uint64_t, may span multiple words
        let mask := (2 ^ sliceWidth - 1 : Nat)
        let maskStr := s!"0x{Nat.toDigits 16 mask |> String.ofList}ULL"
        if bitOffset == 0 then
          s!"(((uint64_t){srcExpr}[{wordIdx + 1}] << 32) | (uint64_t){srcExpr}[{wordIdx}]) & {maskStr})"
        else
          s!"((((uint64_t){srcExpr}[{wordIdx + 1}] << {32 - bitOffset}) | ((uint64_t){srcExpr}[{wordIdx}] >> {bitOffset})) & {maskStr})"
      else
        -- Result > 64 bits: return as-is (rare case)
        emitExpr typeMap e
    else
      -- Normal (≤ 64 bit) path
      let mask := (2 ^ sliceWidth - 1 : Nat)
      let maskStr := s!"0x{Nat.toDigits 16 mask |> String.ofList}ULL"
      if sliceWidth >= 64 then
        if lo == 0 then emitExpr typeMap e
        else s!"({emitExpr typeMap e} >> {lo})"
      else
        if lo == 0 then
          s!"({emitExpr typeMap e} & {maskStr})"
        else
          s!"(({emitExpr typeMap e} >> {lo}) & {maskStr})"

  | .index arr idx =>
    s!"{emitExpr typeMap arr}[{emitExpr typeMap idx}]"

  | .op .mux args =>
    match args with
    | [cond, thenVal, elseVal] =>
      s!"({emitExpr typeMap cond} ? {emitExpr typeMap thenVal} : {emitExpr typeMap elseVal})"
    | _ => "/* ERROR: mux requires 3 arguments */"

  | .op .not args =>
    match args with
    -- .not in IR is always boolean negation (logical NOT).
    -- Verilog bitwise NOT (~) is lowered as XOR with -1 in Lower.lean.
    | [arg] => s!"(!{emitExpr typeMap arg})"
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
        -- Always use at least 32-bit types for ASR to avoid overflow in
        -- sign-extension patterns like (val << N) >> N where N can be large
        let w := max (inferExprWidth typeMap arg1) 32
        let stype := signedCastType w
        let utype := emitCppType (.bitVector w)
        s!"(({utype})(({stype}){emitExpr typeMap arg1} >> {emitExpr typeMap arg2}))"
      | .eq =>
        -- eq(x, 0) → !x, eq(0, x) → !x (common boolean idiom)
        match arg1, arg2 with
        | _, .const 0 _ => s!"(!({emitExpr typeMap arg1}) ? 1 : 0)"
        | .const 0 _, _ => s!"(!({emitExpr typeMap arg2}) ? 1 : 0)"
        | _, _ => s!"({emitExpr typeMap arg1} == {emitExpr typeMap arg2} ? 1 : 0)"
      | .lt_u | .le_u | .gt_u | .ge_u =>
        s!"({emitExpr typeMap arg1} {emitCppOperator operator} {emitExpr typeMap arg2} ? 1 : 0)"
      | _ =>
        s!"({emitExpr typeMap arg1} {emitCppOperator operator} {emitExpr typeMap arg2})"
    | _ => s!"/* ERROR: operator with wrong arity */"

/-- Parts of a C++ class generated from a single statement -/
structure StmtParts where
  declarations    : List String
  evalBody        : List String
  tickBody        : List String
  resetBody       : List String
  evalTickLocals  : List String   -- _next local decls for evalTick()

instance : Append StmtParts where
  append a b :=
    { declarations := a.declarations ++ b.declarations
    , evalBody := a.evalBody ++ b.evalBody
    , tickBody := a.tickBody ++ b.tickBody
    , resetBody := a.resetBody ++ b.resetBody
    , evalTickLocals := a.evalTickLocals ++ b.evalTickLocals }

def StmtParts.empty : StmtParts :=
  { declarations := [], evalBody := [], tickBody := [], resetBody := [], evalTickLocals := [] }

/-- Emit a C++ constant expression for an init value with given width -/
def emitInitValue (initValue : Int) (width : Nat) : String :=
  let cppType := emitCppType (.bitVector width)
  if initValue < 0 then
    let modulus : Int := (2 : Int) ^ width
    let unsigned := ((initValue % modulus) + modulus) % modulus
    s!"({cppType})0x{Nat.toDigits 16 unsigned.toNat |> String.ofList}ULL"
  else
    s!"({cppType}){initValue}ULL"

/-- Flatten a MUX chain into (condition, value) pairs + default.
    mux(c1, v1, mux(c2, v2, default)) → [(c1, v1), (c2, v2)], default -/
private partial def flattenMuxChain (e : Expr) : List (Expr × Expr) × Expr :=
  match e with
  | .op .mux [cond, thenVal, elseVal] =>
    let (rest, default_) := flattenMuxChain elseVal
    ((cond, thenVal) :: rest, default_)
  | _ => ([], e)

/-- Count the depth of a MUX chain (number of nested ternary operators) -/
private partial def muxChainDepth : Expr → Nat
  | .op .mux [_, _, elseVal] => 1 + muxChainDepth elseVal
  | _ => 0

/-- Emit a MUX chain as if-else block for better branch prediction.
    Returns empty list if the expression is not a suitable MUX chain (< minArms). -/
def emitMuxAsIfElse (typeMap : List (String × HWType))
    (lhsName : String) (width : Nat) (rhs : Expr)
    (minArms : Nat := 4) : List String :=
  let (arms, default_) := flattenMuxChain rhs
  if arms.length < minArms then []  -- too shallow to benefit from if-else
  else
    let maskFn := fun (e : Expr) =>
      let s := emitExpr typeMap e
      if exprIsMasked width e then s else applyMask s width
    -- Emit: lhs = default; if (c1) lhs = v1; else if (c2) lhs = v2; ...
    let defaultLine := s!"        {lhsName} = {maskFn default_};"
    let ifLines := (arms.zip (List.range arms.length)).map fun ((cond, val), idx) =>
      let condStr := emitExpr typeMap cond
      let valStr := maskFn val
      if idx == 0 then s!"        if ({condStr}) {lhsName} = {valStr};"
      else s!"        else if ({condStr}) {lhsName} = {valStr};"
    [defaultLine] ++ ifLines

/-- Split a statement into declaration/eval/tick/reset parts -/
def emitStmt (stmt : Stmt) (typeMap : List (String × HWType))
    (design : Option Design := none) : StmtParts :=
  match stmt with
  | .assign lhs rhs =>
    let width := lookupWidth typeMap lhs
    if width > 64 then
      -- Skip wide assigns (handled via memory/array paths elsewhere)
      StmtParts.empty
    else
      -- For deep MUX chains (≥16 arms), emit if-else for branch prediction
      let sn := sanitizeName lhs
      let ifElseLines := if muxChainDepth rhs >= 16 then
          emitMuxAsIfElse typeMap sn width rhs 16
        else []
      if !ifElseLines.isEmpty then
        { declarations := []
        , evalBody := ifElseLines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      else
        let expr := emitExpr typeMap rhs
        let masked := if exprIsMasked width rhs then expr else applyMask expr width
        { declarations := []
        , evalBody := [s!"        {sanitizeName lhs} = {masked};"]
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }

  | .register output _clock _reset input initValue =>
    let width := lookupWidth typeMap output
    let cppType := emitCppType (.bitVector width)
    let outName := sanitizeName output
    let nextName := s!"{outName}_next"
    let rawExpr := emitExpr typeMap input
    let inputExpr := if exprIsMasked width input then rawExpr else applyMask rawExpr width
    let initExpr := emitInitValue initValue width
    -- Expand deep MUX chains (≥16 arms) into if/else-if cascades for better
    -- branch prediction and I-cache locality. Shorter chains stay as a single
    -- ternary expression. We no longer special-case "self-referencing"
    -- registers (default-else → reg itself) — since every evalTick-local
    -- `_next` is now initialized to the current register value, Clang -O2
    -- elides any redundant `reg_next = reg;` store in either code shape.
    let ifElseLines := if muxChainDepth input >= 16 then
        emitMuxAsIfElse typeMap nextName width input 16
      else []
    -- Initialize the evalTick-local `_next` to the current register value.
    -- This preserves Verilog `<=` non-blocking semantics: downstream
    -- conditions in the same evalTick read the OLD value. Clang -O2 elides
    -- the store when it's immediately overwritten.
    let nextLocalDecl := s!"        {cppType} {nextName} = {outName};"
    let body : List String :=
      if ifElseLines.isEmpty then [s!"        {nextName} = {inputExpr};"]
      else ifElseLines
    { declarations := [s!"    {cppType} {outName};", s!"    {cppType} {nextName};"]
    , evalBody := body
    , tickBody := [s!"        {outName} = {nextName};"]
    , resetBody := [s!"        {outName} = {initExpr};"]
    , evalTickLocals := [nextLocalDecl] }

  | .memory name addrWidth dataWidth _clock writeAddr writeData writeEnable readAddr readData comboRead =>
    let memSize := 2 ^ addrWidth
    let elemType := emitCppType (.bitVector dataWidth)
    let memName := sanitizeName name
    let rdName := sanitizeName readData
    let memDecl := "    std::array<" ++ elemType ++ ", " ++ toString memSize ++ "> " ++ memName ++ ";"
    -- Declare rdName if not already in typeMap (e.g. unused memory read port)
    let rdType := emitCppType (.bitVector dataWidth)
    let rdInTypeMap := typeMap.any fun (n, _) => sanitizeName n == rdName
    let rdDecl := if rdInTypeMap then [] else [s!"    {rdType} {rdName};"]
    -- Skip dead memory writes when writeEnable is constant 0
    let isDeadWrite := match writeEnable with
      | .const 0 _ => true | _ => false
    let writeTickLine := if isDeadWrite then []
      else [s!"        if ({emitExpr typeMap writeEnable}) {memName}[{emitExpr typeMap writeAddr}] = {emitExpr typeMap writeData};"]
    if comboRead then
      { declarations := [memDecl] ++ rdDecl
      , evalBody := [s!"        {rdName} = {memName}[{emitExpr typeMap readAddr}];"]
      , tickBody := writeTickLine
      , resetBody := [s!"        {memName}.fill(0);"]
      , evalTickLocals := [] }
    else
      let addrLatch := s!"{memName}_raddr"
      let addrType := emitCppType (.bitVector addrWidth)
      { declarations := [memDecl, s!"    {addrType} {addrLatch};"] ++ rdDecl
      , evalBody := [s!"        {addrLatch} = {emitExpr typeMap readAddr};"]
      , tickBody :=
          writeTickLine ++
          [ s!"        {rdName} = {memName}[{addrLatch}];" ]
      , resetBody := [s!"        {memName}.fill(0);"]
      , evalTickLocals := [] }

  | .inst moduleName instName connections =>
    let className := sanitizeName moduleName
    let rawIName := sanitizeName instName
    -- Avoid name collision when module name == instance name (e.g., picorv32)
    let iName := if rawIName == className then rawIName ++ "_inst" else rawIName
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
    , resetBody := [s!"        {iName}.reset();"]
    , evalTickLocals := [] }

/-- Collect all wire name references from an IR expression -/
partial def collectExprRefs : Expr → List String
  | .ref name => [name]
  | .const _ _ => []
  | .slice inner _ _ => collectExprRefs inner
  | .concat args => args.foldl (fun acc a => acc ++ collectExprRefs a) []
  | .op _ args => args.foldl (fun acc a => acc ++ collectExprRefs a) []
  | .index arr idx => collectExprRefs arr ++ collectExprRefs idx

/-- Collect all wire names referenced in tick() bodies (memory write exprs, read data for
    non-combo-read memories). These must remain class members even when not in observableWires. -/
def collectTickRefWires (body : List Stmt) : List String :=
  body.foldl (fun acc stmt =>
    match stmt with
    | .register _ _ _ input _ =>
      -- Register input expr is evaluated in tick (or evalTick's register section).
      -- Wires referenced here must NOT be localized away.
      acc ++ (collectExprRefs input).map sanitizeName
    | .memory _ _ _ _ wa wd we ra rd cr =>
      let refs := collectExprRefs wa ++ collectExprRefs wd ++ collectExprRefs we
      -- Non-combo-read: tick() assigns rd and references readAddr exprs
      let refs := if !cr then refs ++ collectExprRefs ra ++ [rd] else refs
      acc ++ refs.map sanitizeName
    | _ => acc
  ) []

/-- Emit a complete C++ class for a module -/
def emitModule (m : Module) (design : Option Design := none)
    (observableWires : Option (List String) := none) : String :=
  if m.isPrimitive then
    s!"// Primitive module: {m.name}\n// (blackbox - not generated)\n\n"
  else
    let typeMap := buildTypeMap m
    let className := sanitizeName m.name

    -- Filter identity assigns (x = ref x) before code generation.
    -- These are generated by SSA lowering for `output reg` declarations
    -- and would produce useless `x = x;` lines that shadow real assignments.
    let filteredBody := m.body.filter fun s => match s with
      | .assign lhs (.ref name) => lhs != name
      | _ => true
    -- Collect all StmtParts
    let allParts := filteredBody.map (emitStmt · typeMap design)

    -- Collect register output names (used for dedup below)
    let registerNames := m.body.filterMap fun s => match s with
      | .register output .. => some output
      | _ => none

    -- Input port declarations
    let inputDecls := m.inputs.map fun (p : Port) =>
      s!"    {emitCppType p.ty} {sanitizeName p.name};"

    -- Output port declarations (skip if also a register output — register emits its own decl)
    let outputDecls := m.outputs.filterMap fun (p : Port) =>
      if registerNames.contains p.name then none
      else some s!"    {emitCppType p.ty} {sanitizeName p.name};"

    -- Internal wire declarations (excluding ports and register outputs)
    let portNames := (m.inputs ++ m.outputs).map fun (p : Port) => p.name
    let internalWires := Id.run do
      let mut seen : List String := []
      let mut result : List Port := []
      for w in m.wires do
        if !portNames.contains w.name && !registerNames.contains w.name &&
           !seen.contains w.name then
          result := result ++ [w]
          seen := seen ++ [w.name]
      result

    -- Partition into member wires (observable/JIT) and local wires
    -- Wires referenced in tick() bodies must always be class members
    let tickRefs := collectTickRefWires m.body
    let memberWires := match observableWires with
      | some ws => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          ws.contains sn || tickRefs.contains sn
      | none => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          sn.startsWith "_gen_" || tickRefs.contains sn
    -- Collect memory names to avoid declaring them as local scalars
    let memoryNames := m.body.filterMap fun s => match s with
      | .memory name _ _ _ _ _ _ _ _ _ => some (sanitizeName name) | _ => none
    let localWires := match observableWires with
      | some ws => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          !ws.contains sn && !tickRefs.contains sn && !memoryNames.contains sn
      | none => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          !sn.startsWith "_gen_" && !tickRefs.contains sn && !memoryNames.contains sn

    let wireDecls := memberWires.map fun (p : Port) =>
      s!"    {emitCppType p.ty} {sanitizeName p.name};"

    -- Local variable declarations (emitted inside eval())
    let localDecls := localWires.map fun (p : Port) =>
      s!"        {emitCppType p.ty} {sanitizeName p.name};"

    -- Extra declarations from statements (registers, memories, sub-instances).
    -- Deduplicate by C++ identifier: some Verilog patterns (e.g. LiteX's
    -- `reg [N:0] foo; always @(posedge clk) foo <= mem[addr];`) surface in the
    -- IR as both a `.memory` read-data port and a standalone `.register`
    -- statement bound to the same name. Without dedup the class would have two
    -- conflicting declarations of `foo` (different widths) and fail to compile.
    -- Keep the first declaration — memory read ports are emitted before
    -- register decls and carry the correct dataWidth from the memory.
    let extractDeclName (line : String) : Option String := Id.run do
      -- Match "    <type> <name>;" — take the token before the trailing ';'
      let trimmed := line.trimLeft
      if trimmed.isEmpty then return none
      let withoutSemi := if trimmed.endsWith ";" then trimmed.dropRight 1 else trimmed
      let toks := (withoutSemi.splitOn " ").filter (· != "")
      toks.getLast?
    let rawStmtDecls := allParts.foldl (fun acc p => acc ++ p.declarations) []
    let stmtDecls := Id.run do
      let mut seen : List String := []
      let mut result : List String := []
      for decl in rawStmtDecls do
        match extractDeclName decl with
        | some n =>
          if seen.contains n then pure ()
          else
            seen := seen ++ [n]
            result := result ++ [decl]
        | none => result := result ++ [decl]
      result

    -- Eval/tick/reset bodies
    let evalBody := allParts.foldl (fun acc p => acc ++ p.evalBody) []
    let tickBody := allParts.foldl (fun acc p => acc ++ p.tickBody) []
    let resetBody := allParts.foldl (fun acc p => acc ++ p.resetBody) []
    let evalTickLocals := allParts.foldl (fun acc p => acc ++ p.evalTickLocals) []

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

    -- Function splitting: partition evalBody into chunks for better I-cache behavior.
    -- Additionally, lines containing "pcpi" are separated into a dedicated chunk
    -- that can be conditionally skipped when PCPI is inactive.
    let chunkSize := 500  -- lines per eval_partN function (larger = fewer splits)
    let evalChunks := Id.run do
      let mut chunks : List (List String) := []
      let mut current : List String := []
      let mut inIfBlock : Bool := false  -- track if we're inside an if-else chain
      for line in evalBody do
        let trimmed := line.trimLeft
        -- Track if-else block state
        if trimmed.startsWith "if (" || trimmed.startsWith "if(" then
          inIfBlock := true
        -- End of if-else block: a line that doesn't start with else/}
        if inIfBlock && !trimmed.startsWith "else " && !trimmed.startsWith "}" &&
           !trimmed.startsWith "if (" && !trimmed.startsWith "if(" then
          inIfBlock := false
        current := current ++ [line]
        if current.length >= chunkSize && !inIfBlock then
          chunks := chunks ++ [current]
          current := []
      if !current.isEmpty then chunks := chunks ++ [current]
      chunks

    let needsSplit := evalChunks.length > 1

    -- Determine which local wires can stay local to each part vs need member promotion.
    -- A wire that is only referenced within a single chunk can be a local of that chunk.
    let (evalLocalDecls, extraMemberDecls, chunkLocalDecls) := if needsSplit then Id.run do
      -- For each local wire, find which chunks reference it (by name in the string)
      let mut crossChunk : List String := []  -- wires used across multiple chunks → member
      let mut perChunk : List (List String) := evalChunks.map (fun _ => [])
      for decl in localDecls do
        -- Extract wire name from declaration: "        uint32_t foo_bar;"
        let parts := decl.trim.splitOn " "
        let wireName := if parts.length >= 2 then (parts[parts.length - 1]!).dropRight 1 else ""
        if wireName.isEmpty then
          crossChunk := crossChunk ++ [decl]
        else
          let mut usedIn : List Nat := []
          let mut cidx : Nat := 0
          for chunk in evalChunks do
            let chunkStr := String.intercalate "\n" chunk
            if (chunkStr.splitOn wireName).length > 1 then
              usedIn := usedIn ++ [cidx]
            cidx := cidx + 1
          if usedIn.length == 1 then
            -- Wire used in only one chunk → local of that chunk
            let ci := usedIn.head!
            perChunk := perChunk.set ci ((perChunk[ci]!) ++ [decl])
          else
            -- Wire used across chunks → promote to member
            crossChunk := crossChunk ++ [decl]
      ([], crossChunk, perChunk)
    else
      (localDecls, [], evalChunks.map (fun _ => []))

    -- eval_part / evalTick are emitted WITHOUT any conditional guards. An
    -- earlier `wrapConditionalGuards` heuristic tried to gate large groups of
    -- lines sharing a prefix (e.g. `cpu_*`) under a detected enable signal
    -- (`_valid` / `_trigger` / `_enable`) to improve I-cache locality, but it
    -- was unsound: the prefix inevitably swept up unrelated subsystems (memory
    -- interface, top-level output wires), which stopped updating when the
    -- enable was 0 and broke Verilog semantics. See Issue 6. We rely on
    -- Clang -O2 dead-store elimination for the same speedup.
    let evalPartMethods := if needsSplit then Id.run do
      let mut result : List String := []
      let mut idx : Nat := 0
      for chunk in evalChunks do
        let locals := chunkLocalDecls[idx]!
        let localSection := if locals.isEmpty then "" else
          String.intercalate "\n" locals ++ "\n"
        result := result ++ [
          s!"    void eval_part{idx}() \{\n" ++
          localSection ++
          String.intercalate "\n" chunk ++ "\n" ++
          "    }\n"]
        idx := idx + 1
      result
    else []

    -- For parts beyond the first, add dirty tracking:
    -- tick() sets _dirty_partN = true when any register that feeds partN changes.
    -- eval() skips partN if not dirty.
    -- For now, generate unconditional calls (dirty tracking = future optimization).
    let evalCallParts := if needsSplit then Id.run do
      let mut result : List String := []
      for idx in List.range evalChunks.length do
        result := result ++ [s!"        eval_part{idx}();"]
      result
    else []

    let evalMethod := if needsSplit then
      "    void eval() {\n" ++
      String.intercalate "\n" evalCallParts ++ "\n" ++
      "    }\n\n"
    else
      "    void eval() {\n" ++
      (if evalLocalDecls.isEmpty then "" else String.intercalate "\n" evalLocalDecls ++ "\n") ++
      (if evalBody.isEmpty then "" else String.intercalate "\n" evalBody ++ "\n") ++
      "    }\n\n"

    let tickMethod :=
      "    void tick() {\n" ++
      (if tickBody.isEmpty then "" else String.intercalate "\n" tickBody ++ "\n") ++
      "    }\n\n"

    -- evalTick: inline all eval code + tick, with ALL non-tick wires as locals.
    -- This avoids member access overhead and improves cache locality.
    -- Wires that are NOT referenced in tick() can be local to evalTick.
    let evalTickWireLocals := internalWires.filterMap fun (w : Port) =>
      let sn := sanitizeName w.name
      -- Only localize scalar wires (≤ 64 bit) as stack variables.
      -- Wide integers (> 64 bit) stay as class members to avoid
      -- per-cycle std::array zero-init overhead (~20% perf hit).
      let isScalar := w.ty.bitWidth ≤ 64
      if isScalar && !tickRefs.contains sn && !memoryNames.contains sn then
        some s!"        {emitCppType w.ty} {sn} = 0;"
      else none
    let allWireLocalDecls := evalTickWireLocals
    let guardedEvalBody := evalBody
    -- IMPORTANT: The previous "self-ref register optimization" that collapsed
    -- `reg_next` into in-place `reg` writes has been removed entirely. It broke
    -- Verilog `<=` (non-blocking) semantics whenever one register's condition
    -- read another self-ref register that had already been in-place written
    -- earlier in the same evalTick (cf. Issue 1: pcpi_mul, mul_waiting corrupted
    -- mul_finish's condition). Performance is recovered instead by initializing
    -- `_next` locals to the current register value so that `else reg_next = reg;`
    -- becomes a dead store that Clang -O2 elides.
    let evalTickLocalsFiltered := evalTickLocals
    -- Sub-module hierarchical call rewrite (eval → evalTick, drop sub.tick())
    let instNames := m.body.filterMap fun s => match s with
      | .inst _ instName _ => some (sanitizeName instName)
      | _ => none
    let evalTickEvalBody := guardedEvalBody.map fun line =>
      instNames.foldl (fun l inst =>
        l.replace s!"{inst}.eval();" s!"{inst}.evalTick();"
      ) line
    let evalTickTickBody := tickBody.filter fun line =>
      !instNames.any (fun inst => (line.splitOn s!"{inst}.tick()").length > 1)
    let evalTickMethod :=
      "    void evalTick() {\n" ++
      (if evalTickLocalsFiltered.isEmpty then "" else
        "        // Register next-state (local for register promotion)\n" ++
        String.intercalate "\n" evalTickLocalsFiltered ++ "\n") ++
      (if allWireLocalDecls.isEmpty then "" else
        "        // Wire locals (stack-allocated for cache locality)\n" ++
        String.intercalate "\n" allWireLocalDecls ++ "\n") ++
      (if evalTickEvalBody.isEmpty then "" else String.intercalate "\n" evalTickEvalBody ++ "\n") ++
      (if evalTickTickBody.isEmpty then "" else String.intercalate "\n" evalTickTickBody ++ "\n") ++
      "    }\n"

    -- Promoted local wires (when function splitting is active)
    let promotedSection := if extraMemberDecls.isEmpty then "" else
      "    // Promoted local wires (for function splitting)\n" ++
      String.intercalate "\n" extraMemberDecls ++ "\n\n"

    -- Eval part methods (only when splitting)
    let evalPartSection := if evalPartMethods.isEmpty then "" else
      "    // Split eval() into parts for I-cache optimization\n" ++
      String.intercalate "\n" evalPartMethods ++ "\n"

    let classClose := "};\n"

    header ++ classOpen ++ inputSection ++ outputSection ++ wireSection ++
    promotedSection ++ stmtDeclSection ++ constructor ++ resetMethod ++
    evalPartSection ++ evalMethod ++ tickMethod ++ evalTickMethod ++ classClose

/-- Convert a single module to C++ simulation code with includes -/
def toCppSim (m : Module) : String :=
  let includes := "#include <cstdint>\n#include <array>\n#include <cstring>\n\n"
  includes ++ emitModule m

/-- Convert a full design to C++ simulation code -/
def toCppSimDesign (d : Design)
    (observableWires : Option (List String) := none) : String :=
  let header := "#include <cstdint>\n#include <array>\n#include <cstring>\n\n"
  -- Emit modules in dependency order (bottom-up: leaf modules first, top last)
  let topName := d.topModule
  -- Topological sort: modules that don't instantiate others go first
  let getInstModules (m : Module) : List String :=
    m.body.filterMap fun s => match s with | .inst modName _ _ => some modName | _ => none
  let sorted := Id.run do
    let mut emitted : List String := []
    let mut result : List Module := []
    let mut remaining := d.modules
    let mut changed := true
    while changed && !remaining.isEmpty do
      changed := false
      let mut next : List Module := []
      for m in remaining do
        let deps := getInstModules m
        if deps.all (fun dep => emitted.any (· == dep)) then
          result := result ++ [m]
          emitted := emitted ++ [m.name]
          changed := true
        else
          next := next ++ [m]
      remaining := next
    result ++ remaining  -- append any remaining (circular deps)
  let code := sorted.map fun m =>
    if m.name == topName then emitModule m (some d) observableWires
    else emitModule m (some d)
  header ++ String.intercalate "\n" code

/-- Collect memory entries from a module's body (name, addrWidth, dataWidth) -/
private def collectMemories (body : List Stmt) : List (String × Nat × Nat) :=
  body.filterMap fun stmt =>
    match stmt with
    | .memory name addrWidth dataWidth .. => some (name, addrWidth, dataWidth)
    | _ => none

/-- Collect (sanitizedName, width) for all registers ≤64 bits -/
private def collectRegisters (body : List Stmt) (typeMap : List (String × HWType))
    : List (String × Nat) :=
  body.filterMap fun stmt =>
    match stmt with
    | .register output .. =>
      let width := lookupWidth typeMap output
      if width ≤ 64 then some (sanitizeName output, width) else none
    | _ => none

/-- Generate jit_set_reg switch cases -/
private def emitSetRegSwitch (regs : List (String × Nat)) : String :=
  let indexed := (List.range regs.length).zip regs
  let cases := indexed.map fun (i, sName, width) =>
    let cppType := emitCppType (.bitVector width)
    s!"            case {i}: s->{sName} = ({cppType})val; break;"
  String.intercalate "\n" cases

/-- Generate jit_get_reg switch cases -/
private def emitGetRegSwitch (regs : List (String × Nat)) : String :=
  let indexed := (List.range regs.length).zip regs
  let cases := indexed.map fun (i, sName, _width) =>
    s!"            case {i}: return (uint64_t)s->{sName};"
  String.intercalate "\n" cases

/-- Generate jit_reg_name switch cases -/
private def emitRegNameSwitch (regs : List (String × Nat)) : String :=
  let indexed := (List.range regs.length).zip regs
  let cases := indexed.map fun (i, sName, _width) =>
    s!"            case {i}: return \"{sName}\";"
  String.intercalate "\n" cases

/-- Generate set_input switch cases from Module.inputs (skip clk only) -/
private def emitSetInputSwitch (inputs : List Port) : String :=
  let userInputs := inputs.filter fun (p : Port) =>
    p.name != "clk"
  let indexed := (List.range userInputs.length).zip userInputs
  let cases := indexed.map fun (i, p) =>
    let sName := sanitizeName p.name
    let cppType := emitCppType p.ty
    s!"            case {i}: s->{sName} = ({cppType})val; break;"
  String.intercalate "\n" cases

/-- Generate get_output switch cases from Module.outputs -/
private def emitGetOutputSwitch (outputs : List Port) : String :=
  -- For wide packed outputs (array), expose each 32-bit element
  -- For scalar outputs, return directly
  let cases := outputs.foldl (fun (acc : List String × Nat) (p : Port) =>
    let sName := sanitizeName p.name
    let w := p.ty.bitWidth
    if w > 64 then
      -- Wide array output: expose each 32-bit element
      let nWords := (w + 31) / 32
      let wordCases := List.range nWords |>.map fun j =>
        s!"            case {acc.2 + j}: return (uint64_t)s->{sName}[{j}];"
      (acc.1 ++ wordCases, acc.2 + nWords)
    else
      let cast := s!"(uint64_t)s->{sName}"
      (acc.1 ++ [s!"            case {acc.2}: return {cast};"], acc.2 + 1)
  ) ([], 0)
  String.intercalate "\n" cases.1

/-- Count total output slots (wide outputs expand to multiple slots) -/
private def countOutputSlots (outputs : List Port) : Nat :=
  outputs.foldl (fun acc p =>
    let w := p.ty.bitWidth
    if w > 64 then acc + (w + 31) / 32 else acc + 1
  ) 0

/-- Get the filtered list of named wires (observable or _gen_ prefix, ≤64 bits) -/
private def getNamedWires (wires : List Port)
    (observableWires : Option (List String) := none) : List Port :=
  match observableWires with
  | some ws => wires.filter fun (w : Port) =>
      ws.contains (sanitizeName w.name) && w.ty.bitWidth ≤ 64
  | none => wires.filter fun (w : Port) =>
      (sanitizeName w.name).startsWith "_gen_" && w.ty.bitWidth ≤ 64

/-- Generate get_wire switch for named internal wires (observable or _gen_ prefix, ≤64 bits) -/
private def emitGetWireSwitch (wires : List Port)
    (observableWires : Option (List String) := none) : String × Nat :=
  let namedWires := getNamedWires wires observableWires
  let indexed := (List.range namedWires.length).zip namedWires
  let cases := indexed.map fun (i, p) =>
    let sName := sanitizeName p.name
    s!"            case {i}: return (uint64_t)s->{sName};"
  (String.intercalate "\n" cases, namedWires.length)

/-- Generate wire_name switch (returns wire name by index for discovery) -/
private def emitWireNameSwitch (wires : List Port)
    (observableWires : Option (List String) := none) : String :=
  let namedWires := getNamedWires wires observableWires
  let indexed := (List.range namedWires.length).zip namedWires
  let cases := indexed.map fun (i, p) =>
    let sName := sanitizeName p.name
    s!"            case {i}: return \"{sName}\";"
  String.intercalate "\n" cases

/-- Generate memory access switch cases from Module.body -/
private def emitMemoryAccessSwitches (body : List Stmt) :
    String × String × Nat :=
  let mems := collectMemories body
  let indexed := (List.range mems.length).zip mems
  let setCases := indexed.map fun (i, name, _addrWidth, _dataWidth) =>
    let sName := sanitizeName name
    s!"            case {i}: s->{sName}[addr] = data; break;"
  let getCases := indexed.map fun (i, name, _addrWidth, _dataWidth) =>
    let sName := sanitizeName name
    s!"            case {i}: return (uint32_t)s->{sName}[addr];"
  ( String.intercalate "\n" setCases
  , String.intercalate "\n" getCases
  , mems.length )

/-- Generate jit_memset_word switch cases from Module.body -/
private def emitMemsetWordSwitch (body : List Stmt) : String :=
  let mems := collectMemories body
  let indexed := (List.range mems.length).zip mems
  let cases := indexed.map fun (i, name, addrWidth, _dataWidth) =>
    let sName := sanitizeName name
    let memSize := 2 ^ addrWidth
    s!"            case {i}: for (uint32_t k = 0; k < count && (addr + k) < {memSize}; k++) s->{sName}[addr + k] = val; break;"
  String.intercalate "\n" cases

/-- Generate self-contained JIT wrapper .cpp from a Design -/
def toCppSimJIT (d : Design)
    (observableWires : Option (List String) := none) : String :=
  -- Generate the CppSim class code (reuse existing, with observableWires for member/local partitioning)
  let classCode := toCppSimDesign d observableWires
  -- Find top module for port/wire introspection
  let topModule := d.modules.find? fun (m : Module) => m.name == d.topModule
  match topModule with
  | none => classCode ++ "\n// ERROR: top module not found\n"
  | some m =>
    let className := sanitizeName m.name
    let userInputs := m.inputs.filter fun (p : Port) =>
      p.name != "clk"
    let numInputs := userInputs.length
    let numOutputs := countOutputSlots m.outputs
    let setInputCases := emitSetInputSwitch m.inputs
    let getOutputCases := emitGetOutputSwitch m.outputs
    let (wireSwitch, numWires) := emitGetWireSwitch m.wires observableWires
    let wireNameSwitch := emitWireNameSwitch m.wires observableWires
    let (memSetCases, memGetCases, numMems) :=
      emitMemoryAccessSwitches m.body
    let memsetWordCases := emitMemsetWordSwitch m.body
    let typeMap := buildTypeMap m
    let regs := collectRegisters m.body typeMap
    let numRegs := regs.length
    let setRegCases := emitSetRegSwitch regs
    let getRegCases := emitGetRegSwitch regs
    let regNameCases := emitRegNameSwitch regs
    -- Assemble extern "C" wrapper
    classCode ++
    "\n// ============================================================\n" ++
    "// Auto-generated JIT FFI wrapper\n" ++
    "// ============================================================\n\n" ++
    s!"extern \"C\" {ob}\n\n" ++
    s!"void* jit_create() {ob} return new {className}(); {cb}\n" ++
    s!"void  jit_destroy(void* ctx) {ob} delete static_cast<{className}*>(ctx); {cb}\n" ++
    s!"void  jit_reset(void* ctx) {ob} static_cast<{className}*>(ctx)->reset(); {cb}\n" ++
    s!"void  jit_eval(void* ctx)  {ob} static_cast<{className}*>(ctx)->eval(); {cb}\n" ++
    s!"void  jit_tick(void* ctx)  {ob} static_cast<{className}*>(ctx)->tick(); {cb}\n" ++
    s!"void  jit_eval_tick(void* ctx) {ob} static_cast<{className}*>(ctx)->evalTick(); {cb}\n\n" ++
    s!"void jit_set_input(void* ctx, uint32_t idx, uint64_t val) {ob}\n" ++
    s!"    auto* s = static_cast<{className}*>(ctx);\n" ++
    s!"    switch (idx) {ob}\n" ++
    setInputCases ++ "\n" ++
    s!"    {cb}\n" ++
    s!"{cb}\n\n" ++
    s!"uint64_t jit_get_output(void* ctx, uint32_t idx) {ob}\n" ++
    s!"    auto* s = static_cast<{className}*>(ctx);\n" ++
    s!"    switch (idx) {ob}\n" ++
    getOutputCases ++ "\n" ++
    s!"    {cb}\n" ++
    s!"    return 0;\n" ++
    s!"{cb}\n\n" ++
    s!"uint64_t jit_get_wire(void* ctx, uint32_t idx) {ob}\n" ++
    s!"    auto* s = static_cast<{className}*>(ctx);\n" ++
    s!"    switch (idx) {ob}\n" ++
    wireSwitch ++ "\n" ++
    s!"    {cb}\n" ++
    s!"    return 0;\n" ++
    s!"{cb}\n\n" ++
    s!"void jit_set_mem(void* ctx, uint32_t mem_idx, uint32_t addr, uint32_t data) {ob}\n" ++
    s!"    auto* s = static_cast<{className}*>(ctx);\n" ++
    s!"    switch (mem_idx) {ob}\n" ++
    memSetCases ++ "\n" ++
    s!"    {cb}\n" ++
    s!"{cb}\n\n" ++
    s!"uint32_t jit_get_mem(void* ctx, uint32_t mem_idx, uint32_t addr) {ob}\n" ++
    s!"    auto* s = static_cast<{className}*>(ctx);\n" ++
    s!"    switch (mem_idx) {ob}\n" ++
    memGetCases ++ "\n" ++
    s!"    {cb}\n" ++
    s!"    return 0;\n" ++
    s!"{cb}\n\n" ++
    s!"void jit_memset_word(void* ctx, uint32_t mem_idx, uint32_t addr, uint32_t val, uint32_t count) {ob}\n" ++
    s!"    auto* s = static_cast<{className}*>(ctx);\n" ++
    s!"    switch (mem_idx) {ob}\n" ++
    memsetWordCases ++ "\n" ++
    s!"    {cb}\n" ++
    s!"{cb}\n\n" ++
    s!"const char* jit_wire_name(uint32_t idx) {ob}\n" ++
    s!"    switch (idx) {ob}\n" ++
    wireNameSwitch ++ "\n" ++
    s!"    {cb}\n" ++
    s!"    return \"\";\n" ++
    s!"{cb}\n\n" ++
    s!"uint32_t jit_num_inputs()   {ob} return {numInputs}; {cb}\n" ++
    s!"uint32_t jit_num_outputs()  {ob} return {numOutputs}; {cb}\n" ++
    s!"uint32_t jit_num_wires()    {ob} return {numWires}; {cb}\n" ++
    s!"uint32_t jit_num_memories() {ob} return {numMems}; {cb}\n\n" ++
    s!"void jit_set_reg(void* ctx, uint32_t reg_idx, uint64_t val) {ob}\n" ++
    s!"    auto* s = static_cast<{className}*>(ctx);\n" ++
    s!"    switch (reg_idx) {ob}\n" ++
    setRegCases ++ "\n" ++
    s!"    {cb}\n" ++
    s!"{cb}\n\n" ++
    s!"uint64_t jit_get_reg(void* ctx, uint32_t reg_idx) {ob}\n" ++
    s!"    auto* s = static_cast<{className}*>(ctx);\n" ++
    s!"    switch (reg_idx) {ob}\n" ++
    getRegCases ++ "\n" ++
    s!"    {cb}\n" ++
    s!"    return 0;\n" ++
    s!"{cb}\n\n" ++
    s!"const char* jit_reg_name(uint32_t idx) {ob}\n" ++
    s!"    switch (idx) {ob}\n" ++
    regNameCases ++ "\n" ++
    s!"    {cb}\n" ++
    s!"    return \"\";\n" ++
    s!"{cb}\n\n" ++
    s!"uint32_t jit_num_regs() {ob} return {numRegs}; {cb}\n\n" ++
    s!"void* jit_snapshot(void* ctx) {ob}\n" ++
    s!"    return new {className}(*static_cast<{className}*>(ctx));\n" ++
    s!"{cb}\n\n" ++
    s!"void jit_restore(void* ctx, void* snap) {ob}\n" ++
    s!"    *static_cast<{className}*>(ctx) = *static_cast<{className}*>(snap);\n" ++
    s!"{cb}\n\n" ++
    s!"void jit_free_snapshot(void* snap) {ob}\n" ++
    s!"    delete static_cast<{className}*>(snap);\n" ++
    s!"{cb}\n\n" ++
    s!"{cb} // extern \"C\"\n"

end Sparkle.Backend.CppSim
