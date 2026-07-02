/-
  C Simulation Backend

  Generates C simulation code from the IR.
  Produces a C `struct` plus `static` helper functions for
  reset()/eval()/tick(), and a single externally-visible
  `jit_vtable()` that the loader can dlsym to obtain function
  pointers for every operation.

  This is the C-language replacement for the deleted `CppSim`
  backend.  See `docs/known-issues/KnownIssues.md` Issue #70 for
  the reason for the rewrite: linking the JIT `.so` against
  libstdc++ caused per-handle dlopen state to silently collapse
  onto a single handle when the build-environment glibc and the
  host-binary glibc disagreed on `GLIBC_ABI_*` symbol versions.
  Emitting C lets us link against libc only, dodging the bug,
  and the C surface fits every construct CppSim used (no
  templates / smart-pointers / RAII were ever in play here).

  Per-module externally-visible symbol:
    `const JitVTable* jit_vtable(void);`
  All other helpers are `static` — there is no `jit_eval` /
  `jit_tick` symbol left that two .so handles could share.
-/

import Sparkle.IR.AST
import Sparkle.IR.Type
import Std.Data.HashSet

namespace Sparkle.Backend.CSim

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

/-- Sanitize a name to be a valid C identifier -/
def sanitizeName (name : String) : String :=
  name.replace "." "_"
    |>.replace "-" "_"
    |>.replace " " "_"
    |>.replace "'" "_prime"
    |>.replace "#" ""

/-- Number of 32-bit words a wide bit-vector occupies. -/
private def wordsOf (w : Nat) : Nat := (w + 31) / 32

/-- Convert HWType to a C scalar type string.  For wide
    integers (> 64 bits) and arrays we return a base scalar
    type; the surrounding declaration adds the array
    dimensions (see `emitFieldDecl`). -/
def emitScalarBase : HWType → String
  | .bit => "uint8_t"
  | .bitVector w =>
    if w ≤ 8 then "uint8_t"
    else if w ≤ 16 then "uint16_t"
    else if w ≤ 32 then "uint32_t"
    else if w ≤ 64 then "uint64_t"
    else "uint32_t"  -- wide: array of 32-bit words
  | .array _ elemType => emitScalarBase elemType

/-- Total array length suffix for a HWType, e.g. `[3]` for a
    96-bit wide type, `[8][3]` for `array 8 (bitVector 96)`,
    or empty for a single ≤ 64-bit scalar. -/
partial def emitArraySuffix : HWType → String
  | .bit => ""
  | .bitVector w =>
    if w ≤ 64 then "" else s!"[{wordsOf w}]"
  | .array size elemType => s!"[{size}]" ++ emitArraySuffix elemType

/-- Emit a C field/local declaration like `uint32_t foo[3]` —
    the type goes on the left, the array dimensions on the
    right of the name (C array syntax). -/
def emitFieldDecl (ty : HWType) (name : String) : String :=
  let base := emitScalarBase ty
  let suff := emitArraySuffix ty
  s!"{base} {name}{suff}"

/-- For situations where a *parameter* or *declaration* needs
    just the type and dimensions but no identifier, used by
    casts. -/
def emitTypeName (ty : HWType) : String :=
  let base := emitScalarBase ty
  let suff := emitArraySuffix ty
  if suff.isEmpty then base else base ++ suff

/-- True for widths that are not native C integer widths. -/
def needsMask (w : Nat) : Bool :=
  w != 8 && w != 16 && w != 32 && w != 64

/-- Emit a bit mask expression for the given width -/
def emitMask (w : Nat) : String :=
  if !needsMask w then ""
  else if w == 1 then "1"
  else
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
  | .const _ _ => true
  | .ref _ => true
  | .op .eq _ | .op .lt_u _ | .op .lt_s _ | .op .le_u _
  | .op .le_s _ | .op .gt_u _ | .op .gt_s _ | .op .ge_u _
  | .op .ge_s _ => w == 1
  | .slice _ hi lo => (hi - lo + 1) == w
  | .op .mux [_, t, e] => exprIsMasked w t && exprIsMasked w e
  | .op .and [a, b] => exprIsMasked w a || exprIsMasked w b
  | .op .or [a, b] => exprIsMasked w a && exprIsMasked w b
  | .op .xor [a, b] => exprIsMasked w a && exprIsMasked w b
  | .op .shr _ => true
  | .op .asr _ => true
  | _ => !needsMask w

/-- Convert Operator to C operator symbol -/
def emitCOperator (op : Operator) : String :=
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

/-- Convert IR expression to C expression.

    Wide (> 64 bit) values are represented as `uint32_t[N]`
    arrays in declarations.  In expression contexts an "rvalue
    array" doesn't really exist in C, so the only ways we
    produce wide expressions are:

      * `.ref` to a wide variable — emits the bare identifier,
        which C decays to a pointer in most contexts; the
        wide-assign code below indexes it slot-by-slot rather
        than copying.
      * `.const` with width > 64 — emits a C99 compound literal
        `(uint32_t[N]){w0, w1, …}`, which is a valid rvalue
        only at statement scope.
      * `.concat` over wide totals — same compound-literal
        shape.

    All wide assignments (see `emitStmt`) must therefore
    either:
      (a) be element-wise slot writes (`lhs[j] = …`), or
      (b) wrap the RHS in `memcpy(lhs, RHS, sizeof(lhs))`
          when RHS is a compound literal — `lhs = RHS` on a
          C array is rejected by the compiler. -/
partial def emitExpr (typeMap : List (String × HWType)) (e : Expr) : String :=
  match e with
  | .const value width =>
    let modulus : Int := (2 : Int) ^ width
    let unsigned : Nat :=
      if value < 0 then (((value % modulus) + modulus) % modulus).toNat
      else value.toNat
    if width > 64 then
      -- Wide const: C99 compound literal `(uint32_t[N]){w0, …}`.
      let nWords := wordsOf width
      let slot (j : Nat) : String :=
        let w := (unsigned >>> (j * 32)) &&& 0xFFFFFFFF
        s!"0x{Nat.toDigits 16 w |> String.ofList}u"
      let body := String.intercalate ", " ((List.range nWords).map slot)
      s!"(uint32_t[{nWords}])\{{body}}"
    else
      let cType := emitScalarBase (.bitVector width)
      let suffix := if width > 32 then "ULL" else "U"
      s!"({cType})0x{Nat.toDigits 16 unsigned |> String.ofList}{suffix}"

  | .ref name =>
    sanitizeName name

  | .concat args =>
    match args with
    | [] => "(uint8_t)0ULL"
    | [single] => emitExpr typeMap single
    | _ =>
      let widths := args.map (inferExprWidth typeMap ·)
      let totalWidth := widths.foldl (· + ·) 0
      if totalWidth > 64 then
        -- Wide concat: build `(uint32_t[N]){…}` compound literal.
        -- Same algorithm as CppSim: per-slot, mask each
        -- contributing arg into place.
        let nWords := wordsOf totalWidth
        let argsWithBits : List (Expr × Nat × Nat) := Id.run do
          let mut acc : List (Expr × Nat × Nat) := []
          let mut shift : Nat := 0
          for (arg, w) in (args.zip widths).reverse do
            acc := (arg, shift, w) :: acc
            shift := shift + w
          return acc.reverse
        let slotExpr (j : Nat) : String := Id.run do
          let slotLo : Nat := j * 32
          let slotHi : Nat := slotLo + 31
          let mut parts : List String := []
          for (arg, argLo, w) in argsWithBits do
            let argHi := argLo + w - 1
            let lo := if argLo > slotLo then argLo else slotLo
            let hi := if argHi < slotHi then argHi else slotHi
            if lo ≤ hi then
              let bitInArgLo := lo - argLo
              let bitInArgHi := hi - argLo
              let bitInResultLo := lo - slotLo
              let argExpr := emitExpr typeMap arg
              let bitCount := bitInArgHi - bitInArgLo + 1
              let maskNat : Nat := (2 ^ bitCount) - 1
              let mask := s!"0x{Nat.toDigits 16 maskNat |> String.ofList}ULL"
              let shifted :=
                if w > 64 then
                  let argSlot := bitInArgLo / 32
                  let argBitInSlot := bitInArgLo % 32
                  let bitsFromThisSlot :=
                    let available := 32 - argBitInSlot
                    if bitCount < available then bitCount else available
                  let m2 : Nat := (2 ^ bitsFromThisSlot) - 1
                  let m2str := s!"0x{Nat.toDigits 16 m2 |> String.ofList}ULL"
                  match arg with
                  | .const value _ =>
                    let modulus : Int := (2 : Int) ^ w
                    let unsigned : Nat :=
                      if value < 0 then (((value % modulus) + modulus) % modulus).toNat
                      else value.toNat
                    let slotVal := (unsigned >>> (argSlot * 32)) &&& 0xFFFFFFFF
                    let slotHex := s!"0x{Nat.toDigits 16 slotVal |> String.ofList}ULL"
                    if argBitInSlot == 0 then
                      s!"({slotHex} & {m2str})"
                    else
                      s!"(({slotHex} >> {argBitInSlot}) & {m2str})"
                  | _ =>
                    if argBitInSlot == 0 then
                      s!"((uint64_t){argExpr}[{argSlot}] & {m2str})"
                    else
                      s!"(((uint64_t){argExpr}[{argSlot}] >> {argBitInSlot}) & {m2str})"
                else
                  if bitInArgLo == 0 then
                    s!"((uint64_t){argExpr} & {mask})"
                  else
                    s!"(((uint64_t){argExpr} >> {bitInArgLo}) & {mask})"
              let placed :=
                if bitInResultLo == 0 then shifted
                else s!"({shifted} << {bitInResultLo})"
              parts := parts ++ [placed]
          let combined :=
            if parts.isEmpty then "0ULL"
            else "(" ++ String.intercalate " | " parts ++ ")"
          return s!"(uint32_t)({combined} & 0xffffffffULL)"
        let slots := (List.range nWords).map slotExpr
        s!"(uint32_t[{nWords}])\{" ++ String.intercalate ", " slots ++ "}"
      else
        let resultType := emitScalarBase (.bitVector totalWidth)
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
    let srcWidth := inferExprWidth typeMap e
    if srcWidth > 64 then
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
          let bitsFromLow := 32 - bitOffset
          s!"((((uint64_t){srcExpr}[{wordIdx}] >> {bitOffset}) | ((uint64_t){srcExpr}[{wordIdx + 1}] << {bitsFromLow})) & {maskStr})"
      else if sliceWidth <= 64 then
        let mask := (2 ^ sliceWidth - 1 : Nat)
        let maskStr := s!"0x{Nat.toDigits 16 mask |> String.ofList}ULL"
        if bitOffset == 0 then
          s!"((((uint64_t){srcExpr}[{wordIdx + 1}] << 32) | (uint64_t){srcExpr}[{wordIdx}]) & {maskStr})"
        else
          s!"((((uint64_t){srcExpr}[{wordIdx + 1}] << {32 - bitOffset}) | ((uint64_t){srcExpr}[{wordIdx}] >> {bitOffset})) & {maskStr})"
      else
        emitExpr typeMap e
    else
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
    -- IR `.not` is logical negation; bitwise NOT is lowered as XOR with -1.
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
        s!"(({stype}){emitExpr typeMap arg1} {emitCOperator operator} ({stype}){emitExpr typeMap arg2} ? 1 : 0)"
      | .asr =>
        let w := max (inferExprWidth typeMap arg1) 32
        let stype := signedCastType w
        let utype := emitScalarBase (.bitVector w)
        s!"(({utype})(({stype}){emitExpr typeMap arg1} >> {emitExpr typeMap arg2}))"
      | .eq =>
        match arg1, arg2 with
        | _, .const 0 _ => s!"(!({emitExpr typeMap arg1}) ? 1 : 0)"
        | .const 0 _, _ => s!"(!({emitExpr typeMap arg2}) ? 1 : 0)"
        | _, _ => s!"({emitExpr typeMap arg1} == {emitExpr typeMap arg2} ? 1 : 0)"
      | .lt_u | .le_u | .gt_u | .ge_u =>
        s!"({emitExpr typeMap arg1} {emitCOperator operator} {emitExpr typeMap arg2} ? 1 : 0)"
      | .mul =>
        -- Wide-multiply codegen.  Same algorithm as CppSim's
        -- C++ port: project both wide operands to int64_t (low
        -- 64 bits, sign-extended), multiply via __int128,
        -- pack the 96-bit result into 3 slots.  In C we don't
        -- have lambdas, so we use a GCC/Clang statement
        -- expression `({ … })` which is supported by both
        -- compilers and serves the same purpose.  The result
        -- is a compound literal of a 3-element array.
        let w1 := inferExprWidth typeMap arg1
        let w2 := inferExprWidth typeMap arg2
        if w1 > 64 || w2 > 64 then
          let lhsExpr := emitExpr typeMap arg1
          let rhsExpr := emitExpr typeMap arg2
          let lhsLo64 :=
            if w1 > 64 then s!"((uint64_t)({lhsExpr})[0] | ((uint64_t)({lhsExpr})[1] << 32))"
            else s!"((uint64_t)({lhsExpr}))"
          let rhsLo64 :=
            if w2 > 64 then s!"((uint64_t)({rhsExpr})[0] | ((uint64_t)({rhsExpr})[1] << 32))"
            else s!"((uint64_t)({rhsExpr}))"
          -- The wide-mul value is consumed by `emitStmt`'s
          -- `.op .mul` arm which generates a slot-by-slot
          -- assign, so we expose the three slot expressions
          -- as a marker the assign-side recognises.  Here we
          -- emit a statement-expression that returns a
          -- compound-literal array; this is only used by
          -- `memcpy`-style wide assigns.
          let body :=
            s!"\{ __int128 __p = (__int128)(int64_t){lhsLo64} * (__int128)(int64_t){rhsLo64};" ++
            " (uint32_t[3]){(uint32_t)((unsigned __int128)__p & 0xffffffffULL), " ++
            "(uint32_t)(((unsigned __int128)__p >> 32) & 0xffffffffULL), " ++
            "(uint32_t)(((unsigned __int128)__p >> 64) & 0xffffffffULL)}; }"
          -- Wrap in `(__extension__ ({ … }))` so GCC accepts
          -- it as an expression at any nesting depth.
          s!"(__extension__ ({body}))"
        else
          s!"({emitExpr typeMap arg1} {emitCOperator operator} {emitExpr typeMap arg2})"
      | _ =>
        s!"({emitExpr typeMap arg1} {emitCOperator operator} {emitExpr typeMap arg2})"
    | _ => s!"/* ERROR: operator with wrong arity */"

/-- Parts of a C struct + helper-set generated from a single statement -/
structure StmtParts where
  declarations    : List String
  evalBody        : List String
  tickBody        : List String
  resetBody       : List String
  evalTickLocals  : List String
  deriving Inhabited

instance : Append StmtParts where
  append a b :=
    { declarations := a.declarations ++ b.declarations
    , evalBody := a.evalBody ++ b.evalBody
    , tickBody := a.tickBody ++ b.tickBody
    , resetBody := a.resetBody ++ b.resetBody
    , evalTickLocals := a.evalTickLocals ++ b.evalTickLocals }

def StmtParts.empty : StmtParts :=
  { declarations := [], evalBody := [], tickBody := [], resetBody := [], evalTickLocals := [] }

/-- Emit a C reset value for a register init.

    For ≤ 64-bit widths returns a scalar cast.

    For wide (> 64-bit) widths returns a list of slot
    assignments like `lhs[0] = 0x…u; lhs[1] = 0x…u;` since
    C does not let you assign a compound literal to an
    array-typed lvalue.  The caller (register reset path)
    threads these through `resetBody`. -/
def emitInitScalar (initValue : Int) (width : Nat) : String :=
  let cType := emitScalarBase (.bitVector width)
  let modulus : Int := (2 : Int) ^ width
  let unsigned : Nat :=
    if initValue < 0 then (((initValue % modulus) + modulus) % modulus).toNat
    else initValue.toNat
  s!"({cType})0x{Nat.toDigits 16 unsigned |> String.ofList}ULL"

/-- Per-slot reset lines for a wide register `name`. -/
def emitInitWideLines (name : String) (initValue : Int) (width : Nat) : List String :=
  let modulus : Int := (2 : Int) ^ width
  let unsigned : Nat :=
    if initValue < 0 then (((initValue % modulus) + modulus) % modulus).toNat
    else initValue.toNat
  let nWords := wordsOf width
  (List.range nWords).map fun i =>
    let w := (unsigned >>> (i * 32)) &&& 0xFFFFFFFF
    s!"        {name}[{i}] = 0x{Nat.toDigits 16 w |> String.ofList}u;"

/-- Flatten a MUX chain into (condition, value) pairs + default. -/
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

/-- Emit a MUX chain as if-else block for better branch prediction. -/
def emitMuxAsIfElse (typeMap : List (String × HWType))
    (lhsName : String) (width : Nat) (rhs : Expr)
    (minArms : Nat := 4) : List String :=
  let (arms, default_) := flattenMuxChain rhs
  if arms.length < minArms then []
  else
    let maskFn := fun (e : Expr) =>
      let s := emitExpr typeMap e
      if exprIsMasked width e then s else applyMask s width
    let defaultLine := s!"        {lhsName} = {maskFn default_};"
    let ifLines := (arms.zip (List.range arms.length)).map fun ((cond, val), idx) =>
      let condStr := emitExpr typeMap cond
      let valStr := maskFn val
      if idx == 0 then s!"        if ({condStr}) {lhsName} = {valStr};"
      else s!"        else if ({condStr}) {lhsName} = {valStr};"
    [defaultLine] ++ ifLines

/-- Split a statement into declaration/eval/tick/reset parts -/
partial def emitStmt (stmt : Stmt) (typeMap : List (String × HWType))
    (design : Option Design := none) : StmtParts :=
  match stmt with
  | .assign lhs rhs =>
    let width := lookupWidth typeMap lhs
    if width > 64 then
      let sn := sanitizeName lhs
      let nWords := wordsOf width
      match rhs with
      | .op .mul _ =>
        -- The wide-mul __int128 IIFE returns a `(uint32_t[3])`
        -- compound literal. C will not let us assign that to a
        -- `uint32_t[3]` lvalue, so memcpy slot-by-slot.
        let expr := emitExpr typeMap rhs
        let mulSlots := 3
        let body : List String :=
          [s!"        \{ uint32_t __mul_tmp[{mulSlots}]; uint32_t (*__src)[{mulSlots}] = (uint32_t(*)[{mulSlots}]){expr}; memcpy(__mul_tmp, __src, sizeof(__mul_tmp));"]
          ++
          (List.range nWords).map (fun j =>
            if j < mulSlots then s!"          {sn}[{j}] = __mul_tmp[{j}];"
            else s!"          {sn}[{j}] = 0;")
          ++ ["        }"]
        { declarations := []
        , evalBody := body
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .concat _ =>
        -- Wide concat returns `(uint32_t[N]){…}` compound
        -- literal. memcpy into the lvalue.
        let expr := emitExpr typeMap rhs
        { declarations := []
        , evalBody :=
            [s!"        memcpy({sn}, {expr}, sizeof({sn}));"]
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .mux [cond, thenVal, elseVal] =>
        -- Wide mux: pick a side per slot via ternary on the
        -- shared scalar condition.  Both branches are wide
        -- and identifier-shaped (a `.ref` or a `.const`); if
        -- a branch is a `.const` we materialise it to a
        -- temporary first (compound literal slot indexing
        -- isn't valid in C without parens).
        let condS := emitExpr typeMap cond
        let materialise (label : String) (br : Expr)
            : List String × String :=
          match br with
          | .ref _ => ([], emitExpr typeMap br)
          | _ =>
            let tmp := s!"__mux_{label}_{sn}"
            let init := emitExpr typeMap br
            ([s!"        uint32_t {tmp}[{nWords}]; memcpy({tmp}, {init}, sizeof({tmp}));"], tmp)
        let (thenDecl, thenSym) := materialise "t" thenVal
        let (elseDecl, elseSym) := materialise "e" elseVal
        let lines := (List.range nWords).map fun j =>
          s!"        {sn}[{j}] = ({condS}) ? {thenSym}[{j}] : {elseSym}[{j}];"
        { declarations := []
        , evalBody := thenDecl ++ elseDecl ++ lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .or [a, b] =>
        let aS := emitExpr typeMap a
        let bS := emitExpr typeMap b
        let lines := (List.range nWords).map fun j =>
          s!"        {sn}[{j}] = {aS}[{j}] | {bS}[{j}];"
        { declarations := []
        , evalBody := lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .and [a, b] =>
        let aS := emitExpr typeMap a
        let bS := emitExpr typeMap b
        let lines := (List.range nWords).map fun j =>
          s!"        {sn}[{j}] = {aS}[{j}] & {bS}[{j}];"
        { declarations := []
        , evalBody := lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .xor [a, b] =>
        let aS := emitExpr typeMap a
        let bS := emitExpr typeMap b
        let lines := (List.range nWords).map fun j =>
          s!"        {sn}[{j}] = {aS}[{j}] ^ {bS}[{j}];"
        { declarations := []
        , evalBody := lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .shl [a, b] =>
        let shiftAmount : Nat := match b with
          | .const v _ => v.toNat
          | _ => 0
        let aS := emitExpr typeMap a
        let k := shiftAmount / 32
        let r := shiftAmount % 32
        let slot (j : Nat) : String :=
          if j < k then "0u"
          else if j == k then
            if r == 0 then s!"{aS}[0]" else s!"({aS}[0] << {r})"
          else
            let lower := j - k
            let upperShift := if r == 0 then "0u" else s!"({aS}[{lower - 1}] >> {32 - r})"
            if r == 0 then s!"{aS}[{lower}]"
            else s!"(({aS}[{lower}] << {r}) | {upperShift})"
        let lines := (List.range nWords).map fun j =>
          s!"        {sn}[{j}] = {slot j};"
        { declarations := []
        , evalBody := lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .ref _ =>
        -- Wide identifier copy: memcpy from src array to dest.
        let expr := emitExpr typeMap rhs
        { declarations := []
        , evalBody := [s!"        memcpy({sn}, {expr}, sizeof({sn}));"]
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | _ =>
        StmtParts.empty
    else
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
    let outName := sanitizeName output
    let nextName := s!"{outName}_next"
    if width > 64 then
      -- Wide register.  Storage is `uint32_t out[N]`.  We
      -- maintain a parallel `out_next[N]` and on tick() we
      -- memcpy next -> current.  Register input must be one
      -- of the wide-assign-supported shapes (ref/mux/concat/
      -- and/or/xor/shl/mul).  We synthesise an `assign
      -- out_next := input` Stmt and reuse the wide-assign
      -- arms above to emit the per-slot eval body.
      let nWords := wordsOf width
      let assignToNext := Stmt.assign nextName input
      -- Build a typeMap entry for `out_next` so the wide
      -- assign code finds its width.  We can splice it onto
      -- the local typeMap.
      let nextTypeMap := (nextName, HWType.bitVector width) :: typeMap
      let nextParts := emitStmt assignToNext nextTypeMap design
      let declStr := emitFieldDecl (.bitVector width) outName ++ ";"
      let nextDeclStr := emitFieldDecl (.bitVector width) nextName ++ ";"
      let tickLines := (List.range nWords).map fun j =>
        s!"        {outName}[{j}] = {nextName}[{j}];"
      let resetLines := emitInitWideLines outName initValue width
      -- evalTickLocals: declare a fresh `_next[N]` on the
      -- stack, pre-initialised from `out`.  Per-slot memcpy
      -- of the current register value preserves Verilog
      -- non-blocking semantics for downstream conditions in
      -- the same evalTick.
      let nextLocalDecl :=
        s!"        uint32_t {nextName}[{nWords}]; memcpy({nextName}, {outName}, sizeof({nextName}));"
      { declarations := [s!"    {declStr}", s!"    {nextDeclStr}"]
      , evalBody := nextParts.evalBody
      , tickBody := tickLines
      , resetBody := resetLines
      , evalTickLocals := [nextLocalDecl] }
    else
      let cType := emitScalarBase (.bitVector width)
      let rawExpr := emitExpr typeMap input
      let inputExpr := if exprIsMasked width input then rawExpr else applyMask rawExpr width
      let initExpr := emitInitScalar initValue width
      let ifElseLines := if muxChainDepth input >= 16 then
          emitMuxAsIfElse typeMap nextName width input 16
        else []
      let nextLocalDecl := s!"        {cType} {nextName} = {outName};"
      let body : List String :=
        if ifElseLines.isEmpty then [s!"        {nextName} = {inputExpr};"]
        else ifElseLines
      { declarations := [s!"    {cType} {outName};", s!"    {cType} {nextName};"]
      , evalBody := body
      , tickBody := [s!"        {outName} = {nextName};"]
      , resetBody := [s!"        {outName} = {initExpr};"]
      , evalTickLocals := [nextLocalDecl] }

  | .memory name addrWidth dataWidth _clock writeAddr writeData writeEnable readAddr readData comboRead =>
    let memSize := 2 ^ addrWidth
    let memName := sanitizeName name
    let rdName := sanitizeName readData
    let elemTy : HWType := .bitVector dataWidth
    -- Array of array (e.g. `uint32_t mem[1024][3]` for a 96-bit-wide BRAM).
    let elemSuffix := emitArraySuffix elemTy
    let memDecl := s!"    {emitScalarBase elemTy} {memName}[{memSize}]{elemSuffix};"
    let rdInTypeMap := typeMap.any fun (n, _) => sanitizeName n == rdName
    let rdDecl := if rdInTypeMap then [] else [s!"    {emitFieldDecl elemTy rdName};"]
    let isDeadWrite := match writeEnable with
      | .const 0 _ => true | _ => false
    let writeTickLine := if isDeadWrite then []
      else
        if dataWidth > 64 then
          -- Wide write: memcpy into the BRAM slot.
          [s!"        if ({emitExpr typeMap writeEnable}) memcpy({memName}[{emitExpr typeMap writeAddr}], {emitExpr typeMap writeData}, sizeof({memName}[0]));"]
        else
          [s!"        if ({emitExpr typeMap writeEnable}) {memName}[{emitExpr typeMap writeAddr}] = {emitExpr typeMap writeData};"]
    let zeroLine := s!"        memset({memName}, 0, sizeof({memName}));"
    if comboRead then
      let readLine :=
        if dataWidth > 64 then
          s!"        memcpy({rdName}, {memName}[{emitExpr typeMap readAddr}], sizeof({rdName}));"
        else
          s!"        {rdName} = {memName}[{emitExpr typeMap readAddr}];"
      { declarations := [memDecl] ++ rdDecl
      , evalBody := [readLine]
      , tickBody := writeTickLine
      , resetBody := [zeroLine]
      , evalTickLocals := [] }
    else
      let addrLatch := s!"{memName}_raddr"
      let addrType := emitScalarBase (.bitVector addrWidth)
      let readTickLine :=
        if dataWidth > 64 then
          s!"        memcpy({rdName}, {memName}[{addrLatch}], sizeof({rdName}));"
        else
          s!"        {rdName} = {memName}[{addrLatch}];"
      { declarations := [memDecl, s!"    {addrType} {addrLatch};"] ++ rdDecl
      , evalBody := [s!"        {addrLatch} = {emitExpr typeMap readAddr};"]
      , tickBody := writeTickLine ++ [readTickLine]
      , resetBody := [zeroLine]
      , evalTickLocals := [] }

  | .inst moduleName instName connections =>
    -- Sub-module instances become an embedded struct field plus
    -- calls to the sub-module's static helpers via the same naming
    -- scheme.  The C functions are file-static, so we depend on
    -- their being emitted earlier in the same translation unit
    -- (`toCDesign` emits in dependency order).
    let className := sanitizeName moduleName
    let rawIName := sanitizeName instName
    let iName := if rawIName == className then rawIName ++ "_inst" else rawIName
    let subModule := design.bind fun (d : Design) => d.findModule moduleName
    let outputPortNames : List String := match subModule with
      | some sm => sm.outputs.map fun (p : Port) => p.name
      | none => []
    let inputConns := connections.filterMap fun (portName, expr) =>
      if !outputPortNames.contains portName then
        let portWidth := match subModule with
          | some sm =>
            match (sm.inputs ++ sm.outputs ++ sm.wires).find? (·.name == portName) with
            | some p => p.ty.bitWidth
            | none => 32
          | none => 32
        if portWidth > 64 then
          some s!"        memcpy({iName}.{sanitizeName portName}, {emitExpr typeMap expr}, sizeof({iName}.{sanitizeName portName}));"
        else
          some s!"        {iName}.{sanitizeName portName} = {emitExpr typeMap expr};"
      else none
    let outputConns := connections.filterMap fun (portName, expr) =>
      if outputPortNames.contains portName then
        let portWidth := match subModule with
          | some sm =>
            match (sm.outputs ++ sm.wires).find? (·.name == portName) with
            | some p => p.ty.bitWidth
            | none => 32
          | none => 32
        match expr with
        | .ref wireName =>
          if portWidth > 64 then
            some s!"        memcpy({sanitizeName wireName}, {iName}.{sanitizeName portName}, sizeof({sanitizeName wireName}));"
          else
            some s!"        {sanitizeName wireName} = {iName}.{sanitizeName portName};"
        | _ => none
      else none
    { declarations := [s!"    struct {className} {iName};"]
    , evalBody := inputConns ++ [s!"        sparkle_{className}_eval(&{iName});"] ++ outputConns
    , tickBody := [s!"        sparkle_{className}_tick(&{iName});"]
    , resetBody := [s!"        sparkle_{className}_reset(&{iName});"]
    , evalTickLocals := [] }

/-- Collect all wire name references from an IR expression -/
partial def collectExprRefs : Expr → List String
  | .ref name => [name]
  | .const _ _ => []
  | .slice inner _ _ => collectExprRefs inner
  | .concat args => args.foldl (fun acc a => acc ++ collectExprRefs a) []
  | .op _ args => args.foldl (fun acc a => acc ++ collectExprRefs a) []
  | .index arr idx => collectExprRefs arr ++ collectExprRefs idx

/-- Collect all wire names referenced in tick() bodies. -/
def collectTickRefWires (body : List Stmt) : List String :=
  body.foldl (fun acc stmt =>
    match stmt with
    | .register _ _ _ input _ =>
      acc ++ (collectExprRefs input).map sanitizeName
    | .memory _ _ _ _ wa wd we ra rd cr =>
      let refs := collectExprRefs wa ++ collectExprRefs wd ++ collectExprRefs we
      let refs := if !cr then refs ++ collectExprRefs ra ++ [rd] else refs
      acc ++ refs.map sanitizeName
    | _ => acc
  ) []

/-- Emit a complete C struct + static helpers for a module.
    Returns the full C source fragment (no includes; callers
    add those at design level). -/
def emitModule (m : Module) (design : Option Design := none)
    (observableWires : Option (List String) := none) : String :=
  if m.isPrimitive then
    s!"/* Primitive module: {m.name} */\n/* (blackbox - not generated) */\n\n"
  else
    let typeMap := buildTypeMap m
    let className := sanitizeName m.name

    let filteredBody := m.body.filter fun s => match s with
      | .assign lhs (.ref name) => lhs != name
      | _ => true
    let allParts := filteredBody.map (emitStmt · typeMap design)

    let registerNames := m.body.filterMap fun s => match s with
      | .register output .. => some output
      | _ => none

    let inputDecls := m.inputs.map fun (p : Port) =>
      s!"    {emitFieldDecl p.ty (sanitizeName p.name)};"

    let outputDecls := m.outputs.filterMap fun (p : Port) =>
      if registerNames.contains p.name then none
      else some s!"    {emitFieldDecl p.ty (sanitizeName p.name)};"

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

    let tickRefs := collectTickRefWires m.body
    let memberWires := match observableWires with
      | some ws => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          ws.contains sn || tickRefs.contains sn
      | none => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          sn.startsWith "_gen_" || tickRefs.contains sn
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
      s!"    {emitFieldDecl p.ty (sanitizeName p.name)};"

    let extractDeclName (line : String) : Option String := Id.run do
      let trimmed := line.trimLeft
      if trimmed.isEmpty then return none
      let withoutSemi := if trimmed.endsWith ";" then trimmed.dropRight 1 else trimmed
      -- Strip array dimensions after the identifier
      let beforeBracket := (withoutSemi.splitOn "[").head!
      let toks := (beforeBracket.splitOn " ").filter (· != "")
      toks.getLast?
    let rawStmtDecls := allParts.foldl (fun acc (p : StmtParts) => acc ++ p.declarations) []
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

    let evalBody := allParts.foldl (fun acc (p : StmtParts) => acc ++ p.evalBody) []
    let tickBody := allParts.foldl (fun acc (p : StmtParts) => acc ++ p.tickBody) []
    let resetBody := allParts.foldl (fun acc (p : StmtParts) => acc ++ p.resetBody) []
    let evalTickLocals := allParts.foldl (fun acc (p : StmtParts) => acc ++ p.evalTickLocals) []

    let structName := s!"struct {className}"

    let inputSection := if inputDecls.isEmpty then "" else
      "    /* Input ports */\n" ++ String.intercalate "\n" inputDecls ++ "\n\n"
    let outputSection := if outputDecls.isEmpty then "" else
      "    /* Output ports */\n" ++ String.intercalate "\n" outputDecls ++ "\n\n"
    let wireSection := if wireDecls.isEmpty then "" else
      "    /* Internal wires */\n" ++ String.intercalate "\n" wireDecls ++ "\n\n"
    let stmtDeclSection := if stmtDecls.isEmpty then "" else
      "    /* Registers, memories, sub-instances */\n" ++ String.intercalate "\n" stmtDecls ++ "\n\n"

    let structDecl :=
      structName ++ " {\n" ++
      inputSection ++ outputSection ++ wireSection ++ stmtDeclSection ++
      "};\n\n"

    let localWireDecls := localWires.map fun (p : Port) =>
      s!"    {emitFieldDecl p.ty (sanitizeName p.name)};"

    -- ----------------------------------------------------------------
    -- Self-qualification strategy.
    --
    -- The StmtParts emitted above write to bare identifiers like
    --   `        foo = (bar | baz);`
    -- which only typecheck inside a method on a CppSim class.  In C
    -- we have an explicit `self` pointer, so every reference to a
    -- struct field needs to become `self->foo`.
    --
    -- We compute the full set of member names (inputs, outputs,
    -- wires, register / memory / instance fields) and do a
    -- token-level substitution on each body string.  Tokens are
    -- defined as maximal runs of `[A-Za-z0-9_]`.
    -- ----------------------------------------------------------------

    let memberNames : List String := Id.run do
      let mut s : List String := []
      for p in m.inputs do s := s ++ [sanitizeName p.name]
      for p in m.outputs do s := s ++ [sanitizeName p.name]
      for p in memberWires do s := s ++ [sanitizeName p.name]
      -- Register / memory / inst names from stmtDecls
      for decl in stmtDecls do
        match extractDeclName decl with
        | some n => s := s ++ [n]
        | none => pure ()
      s

    -- Token-level substitution: walk the string, accumulating
    -- alnum/underscore tokens, and emit `self->TOK` when TOK is
    -- in `memberSet`.
    let memberSet : Std.HashSet String := memberNames.foldl (fun s n => s.insert n) ({} : Std.HashSet String)

    let isTokChar (c : Char) : Bool :=
      c.isAlphanum || c == '_'

    let qualify (input : String) : String := Id.run do
      -- A token is a maximal alnum/underscore run.  Two contexts
      -- where we MUST NOT add `self->`:
      --
      --   (a) Field access: any token preceded by `.` or `->`
      --       is a field name of some other object (sub-instance
      --       member access, struct member access).
      --   (b) After a `->`: same reason — that's pointer-field
      --       access, not a top-level identifier.
      --
      -- Easy: while scanning, track whether the LAST emitted
      -- non-alnum character was `.` or whether the previous two
      -- non-alnum chars formed `->`.  If so, skip qualification
      -- for this token.
      let mut out : String := ""
      let mut buf : String := ""
      let mut prevC : Char := ' '
      let mut prevPrevC : Char := ' '
      let mut skipNext : Bool := false
      for c in input.toList do
        if isTokChar c then
          buf := buf.push c
        else
          if !buf.isEmpty then
            if skipNext then
              out := out ++ buf
            else if memberSet.contains buf then
              out := out ++ "self->" ++ buf
            else
              out := out ++ buf
            buf := ""
          out := out.push c
          -- Update next-token skip state: skip if this delimiter is `.`
          -- or if the last two chars formed `->`.
          skipNext :=
            c == '.' || (c == '>' && prevC == '-')
          prevPrevC := prevC
          prevC := c
      let _ := prevPrevC
      if !buf.isEmpty then
        if skipNext then
          out := out ++ buf
        else if memberSet.contains buf then
          out := out ++ "self->" ++ buf
        else
          out := out ++ buf
      return out

    let evalBodyQ := evalBody.map qualify
    let tickBodyQ := tickBody.map qualify
    let resetBodyQ := resetBody.map qualify

    let resetFn :=
      s!"static void sparkle_{className}_reset({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if resetBodyQ.isEmpty then "" else
        String.intercalate "\n" resetBodyQ ++ "\n") ++
      "}\n\n"

    let evalFn :=
      s!"static void sparkle_{className}_eval({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if localWireDecls.isEmpty then "" else
        String.intercalate "\n" localWireDecls ++ "\n") ++
      (if evalBodyQ.isEmpty then "" else
        String.intercalate "\n" evalBodyQ ++ "\n") ++
      "}\n\n"

    let tickFn :=
      s!"static void sparkle_{className}_tick({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if tickBodyQ.isEmpty then "" else
        String.intercalate "\n" tickBodyQ ++ "\n") ++
      "}\n\n"

    -- For evalTick we splice in stack-locals for register-next
    -- values (so the compiler can register-allocate them) and
    -- rewrite sub-instance `eval` calls to `evalTick`.
    let instNames := m.body.filterMap fun s => match s with
      | .inst _ instName _ => some (sanitizeName instName)
      | _ => none
    let rewriteSubEval (line : String) : String :=
      instNames.foldl (fun l inst =>
        l.replace s!"sparkle_{sanitizeName m.name}_{inst}.evalTick"
          s!"sparkle_evalTick_placeholder"
      ) line
    let _ := rewriteSubEval

    -- Build a map: register name → would-be self->reg_next.  We
    -- inject locals on the stack to elide the member-store
    -- overhead.
    let regNames := m.body.filterMap fun s => match s with
      | .register output .. => some (sanitizeName output)
      | _ => none

    -- For evalTick: replace `self->reg_next` with `reg_next` (local)
    -- and `self->reg` reads stay as-is (still member).  At end of
    -- evalTick we copy locals into self->reg via the tick body.
    -- Simpler: keep eval body as `self->reg_next = …;`, and at
    -- the end have `self->reg = self->reg_next;` (tick).  The
    -- CppSim "_next as stack local" optimisation is a perf-only
    -- tweak; for correctness we don't need it in v1.

    -- Filter tick body to drop sub-instance .tick() — already
    -- folded into evalTick of sub-instance via .eval() → .evalTick.
    let evalTickTickBody := tickBodyQ.filter fun line =>
      !instNames.any (fun inst => (line.splitOn s!"sparkle_evalTick_placeholder_TICK_{inst}").length > 1)

    -- Sub-eval → sub-evalTick textual rewrite on eval body.
    let evalTickEvalBody := evalBodyQ.map fun line =>
      instNames.foldl (fun l inst =>
        -- We emit `sparkle_<modName>_eval(&self->iName)` — find
        -- the inst name and switch `_eval` → `_eval_tick`.  This
        -- is a heuristic: look for `&self->inst)` as a marker.
        let marker := s!"&self->{inst})"
        if (l.splitOn marker).length > 1 then
          l.replace "_eval(" "_eval_tick("
        else l) line
    -- Also strip tick calls that match instance names from the
    -- tick body when present.
    let evalTickTickBody := evalTickTickBody.filter fun line =>
      !instNames.any (fun inst =>
        (line.splitOn s!"_tick(&self->{inst})").length > 1)

    let evalTickFn :=
      s!"static void sparkle_{className}_eval_tick({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if localWireDecls.isEmpty then "" else
        String.intercalate "\n" localWireDecls ++ "\n") ++
      (if evalTickEvalBody.isEmpty then "" else
        String.intercalate "\n" evalTickEvalBody ++ "\n") ++
      (if evalTickTickBody.isEmpty then "" else
        String.intercalate "\n" evalTickTickBody ++ "\n") ++
      "}\n\n"
    let _ := evalTickLocals  -- evalTick-specific stack locals: future opt
    let _ := regNames

    structDecl ++ resetFn ++ evalFn ++ tickFn ++ evalTickFn

/-- Convert a full design to C simulation code (no JIT wrapper) -/
def toCDesign (d : Design)
    (observableWires : Option (List String) := none) : String :=
  let header :=
    "/* Generated by Sparkle HDL — C Simulation Model */\n" ++
    "#include <stdint.h>\n" ++
    "#include <stdlib.h>\n" ++
    "#include <string.h>\n\n"
  let topName := d.topModule
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
    result ++ remaining
  let code := sorted.map fun m =>
    if m.name == topName then emitModule m (some d) observableWires
    else emitModule m (some d)
  header ++ String.intercalate "\n" code

/-- Convert a single module to C simulation code with includes -/
def toC (m : Module) : String :=
  let includes :=
    "#include <stdint.h>\n" ++
    "#include <stdlib.h>\n" ++
    "#include <string.h>\n\n"
  includes ++ emitModule m

/-! ## JIT FFI wrapper

Each `.so` exports exactly ONE symbol — `jit_vtable` — which
returns a pointer to a `JitVTable` containing function
pointers for every operation.  Everything else is `static`,
so dlsym cannot reach it.  This sidesteps the collision-on-
shared-symbol problem from Issue #70: two .so files with the
same internal `jit_eval` cannot conflict because neither
publishes that name.
-/

/-- Collect memory entries from a module's body -/
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

private def emitSetRegSwitch (regs : List (String × Nat)) : String :=
  let indexed := (List.range regs.length).zip regs
  let cases := indexed.map fun (i, sName, width) =>
    let cType := emitScalarBase (.bitVector width)
    s!"        case {i}: s->{sName} = ({cType})val; break;"
  String.intercalate "\n" cases

private def emitGetRegSwitch (regs : List (String × Nat)) : String :=
  let indexed := (List.range regs.length).zip regs
  let cases := indexed.map fun (i, sName, _width) =>
    s!"        case {i}: return (uint64_t)s->{sName};"
  String.intercalate "\n" cases

private def emitRegNameSwitch (regs : List (String × Nat)) : String :=
  let indexed := (List.range regs.length).zip regs
  let cases := indexed.map fun (i, sName, _width) =>
    s!"        case {i}: return \"{sName}\";"
  String.intercalate "\n" cases

private def emitSetInputSwitch (inputs : List Port) : String :=
  let userInputs := inputs.filter fun (p : Port) =>
    p.name != "clk"
  let indexed := (List.range userInputs.length).zip userInputs
  let cases := indexed.map fun (i, p) =>
    let sName := sanitizeName p.name
    let cType := emitScalarBase p.ty
    s!"        case {i}: s->{sName} = ({cType})val; break;"
  String.intercalate "\n" cases

private def emitGetOutputSwitch (outputs : List Port) : String :=
  let cases := outputs.foldl (fun (acc : List String × Nat) (p : Port) =>
    let sName := sanitizeName p.name
    let w := p.ty.bitWidth
    if w > 64 then
      let nWords := wordsOf w
      let wordCases := List.range nWords |>.map fun j =>
        s!"        case {acc.2 + j}: return (uint64_t)s->{sName}[{j}];"
      (acc.1 ++ wordCases, acc.2 + nWords)
    else
      let cast := s!"(uint64_t)s->{sName}"
      (acc.1 ++ [s!"        case {acc.2}: return {cast};"], acc.2 + 1)
  ) ([], 0)
  String.intercalate "\n" cases.1

private def countOutputSlots (outputs : List Port) : Nat :=
  outputs.foldl (fun acc p =>
    let w := p.ty.bitWidth
    if w > 64 then acc + wordsOf w else acc + 1
  ) 0

private def getNamedWires (wires : List Port)
    (observableWires : Option (List String) := none) : List Port :=
  match observableWires with
  | some ws => wires.filter fun (w : Port) =>
      ws.contains (sanitizeName w.name) && w.ty.bitWidth ≤ 64
  | none => wires.filter fun (w : Port) =>
      (sanitizeName w.name).startsWith "_gen_" && w.ty.bitWidth ≤ 64

private def emitGetWireSwitch (wires : List Port)
    (observableWires : Option (List String) := none) : String × Nat :=
  let namedWires := getNamedWires wires observableWires
  let indexed := (List.range namedWires.length).zip namedWires
  let cases := indexed.map fun (i, p) =>
    let sName := sanitizeName p.name
    s!"        case {i}: return (uint64_t)s->{sName};"
  (String.intercalate "\n" cases, namedWires.length)

private def emitWireNameSwitch (wires : List Port)
    (observableWires : Option (List String) := none) : String :=
  let namedWires := getNamedWires wires observableWires
  let indexed := (List.range namedWires.length).zip namedWires
  let cases := indexed.map fun (i, p) =>
    let sName := sanitizeName p.name
    s!"        case {i}: return \"{sName}\";"
  String.intercalate "\n" cases

private def emitMemoryAccessSwitches (body : List Stmt) :
    String × String × Nat :=
  let mems := collectMemories body
  let indexed := (List.range mems.length).zip mems
  let setCases := indexed.map fun (i, name, _addrWidth, dataWidth) =>
    let sName := sanitizeName name
    if dataWidth > 64 then
      s!"        case {i}: s->{sName}[addr][0] = data; break;"
    else
      s!"        case {i}: s->{sName}[addr] = data; break;"
  let getCases := indexed.map fun (i, name, _addrWidth, dataWidth) =>
    let sName := sanitizeName name
    if dataWidth > 64 then
      s!"        case {i}: return (uint32_t)s->{sName}[addr][0];"
    else
      s!"        case {i}: return (uint32_t)s->{sName}[addr];"
  ( String.intercalate "\n" setCases
  , String.intercalate "\n" getCases
  , mems.length )

private def emitMemsetWordSwitch (body : List Stmt) : String :=
  let mems := collectMemories body
  let indexed := (List.range mems.length).zip mems
  let cases := indexed.map fun (i, name, addrWidth, dataWidth) =>
    let sName := sanitizeName name
    let memSize := 2 ^ addrWidth
    if dataWidth > 64 then
      s!"        case {i}: for (uint32_t k = 0; k < count && (addr + k) < {memSize}; k++) s->{sName}[addr + k][0] = val; break;"
    else
      s!"        case {i}: for (uint32_t k = 0; k < count && (addr + k) < {memSize}; k++) s->{sName}[addr + k] = val; break;"
  String.intercalate "\n" cases

/-- Generate the self-contained JIT wrapper `.c` for a Design.

    The output is a single translation unit containing:
      * Per-module struct + static helpers from `toCDesign`.
      * The `JitVTable` struct definition.
      * Static trampolines that adapt `void*` ctx to the
        top-module's typed `struct Top*` and call the
        appropriate `sparkle_<top>_*` helper.
      * The `JitVTable` instance pre-populated with those
        trampolines.
      * The single externally-visible `jit_vtable()`
        accessor function.

    The top-level `.so` therefore exports `jit_vtable` and
    nothing else (other than the unavoidable glibc init/fini
    stubs). -/
def toCJIT (d : Design)
    (observableWires0 : Option (List String) := none) : String :=
  -- Determine which internal wires must be struct MEMBERS (persist
  -- across ticks): those feeding a register/memory input.  All other
  -- combinational wires can be eval-local stack values (register-
  -- allocated, no per-tick struct store — a measured instruction-count
  -- win on large flat SoCs like LiteX).  We express this by handing
  -- the member set to everything downstream as `observableWires`, so
  -- the struct layout, the eval bodies, and the JIT wire switches all
  -- agree on the same partition.  Any caller-requested observables are
  -- unioned in so debug pokes still work.
  let observableWires : Option (List String) :=
    match d.modules.find? fun (m : Module) => m.name == d.topModule with
    | none => observableWires0
    | some m =>
      let tickRefs := collectTickRefWires m.body
      let extra := observableWires0.getD []
      some (tickRefs ++ extra)
  let classCode := toCDesign d observableWires
  let topModule := d.modules.find? fun (m : Module) => m.name == d.topModule
  match topModule with
  | none => classCode ++ "\n/* ERROR: top module not found */\n"
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
    let _ := numInputs  -- exposed via vtable's num_wires/num_regs but kept for reference
    let _ := numMems
    let _ := numOutputs

    let vtableType :=
      "/* ---- JIT vtable schema (must match c_src/sparkle_jit.c) ---- */\n" ++
      "typedef struct JitVTable {\n" ++
      "    void* (*create)(void);\n" ++
      "    void  (*destroy)(void* ctx);\n" ++
      "    void  (*reset)(void* ctx);\n" ++
      "    void  (*eval)(void* ctx);\n" ++
      "    void  (*tick)(void* ctx);\n" ++
      "    void  (*eval_tick)(void* ctx);\n" ++
      "    void  (*set_input)(void* ctx, uint32_t idx, uint64_t val);\n" ++
      "    uint64_t (*get_output)(void* ctx, uint32_t idx);\n" ++
      "    uint64_t (*get_wire)(void* ctx, uint32_t idx);\n" ++
      "    void  (*set_mem)(void* ctx, uint32_t mem_idx, uint32_t addr, uint32_t data);\n" ++
      "    uint32_t (*get_mem)(void* ctx, uint32_t mem_idx, uint32_t addr);\n" ++
      "    void  (*memset_word)(void* ctx, uint32_t mem_idx, uint32_t addr, uint32_t val, uint32_t count);\n" ++
      "    const char* (*wire_name)(uint32_t idx);\n" ++
      "    uint32_t (*num_wires)(void);\n" ++
      "    void  (*set_reg)(void* ctx, uint32_t reg_idx, uint64_t val);\n" ++
      "    uint64_t (*get_reg)(void* ctx, uint32_t reg_idx);\n" ++
      "    const char* (*reg_name)(uint32_t idx);\n" ++
      "    uint32_t (*num_regs)(void);\n" ++
      "    void* (*snapshot)(void* ctx);\n" ++
      "    void  (*restore)(void* ctx, void* snap);\n" ++
      "    void  (*free_snapshot)(void* snap);\n" ++
      "} JitVTable;\n\n"

    let trampolines :=
      s!"/* ---- Trampolines: void*-typed adapters for the vtable ---- */\n\n" ++
      s!"static void* sparkle_jit_create(void) \{\n" ++
      s!"    struct {className}* p = (struct {className}*)calloc(1, sizeof(struct {className}));\n" ++
      s!"    if (p) sparkle_{className}_reset(p);\n" ++
      s!"    return (void*)p;\n" ++
      s!"}\n\n" ++
      s!"static void sparkle_jit_destroy(void* ctx) \{ free(ctx); }\n" ++
      s!"static void sparkle_jit_reset(void* ctx) \{ sparkle_{className}_reset((struct {className}*)ctx); }\n" ++
      s!"static void sparkle_jit_eval(void* ctx) \{ sparkle_{className}_eval((struct {className}*)ctx); }\n" ++
      s!"static void sparkle_jit_tick(void* ctx) \{ sparkle_{className}_tick((struct {className}*)ctx); }\n" ++
      s!"static void sparkle_jit_eval_tick(void* ctx) \{ sparkle_{className}_eval_tick((struct {className}*)ctx); }\n\n" ++
      s!"static void sparkle_jit_set_input(void* ctx, uint32_t idx, uint64_t val) \{\n" ++
      s!"    struct {className}* s = (struct {className}*)ctx;\n" ++
      s!"    switch (idx) \{\n" ++
      setInputCases ++ "\n" ++
      s!"    }\n" ++
      s!"}\n\n" ++
      s!"static uint64_t sparkle_jit_get_output(void* ctx, uint32_t idx) \{\n" ++
      s!"    struct {className}* s = (struct {className}*)ctx;\n" ++
      s!"    switch (idx) \{\n" ++
      getOutputCases ++ "\n" ++
      s!"    }\n" ++
      s!"    return 0;\n" ++
      s!"}\n\n" ++
      s!"static uint64_t sparkle_jit_get_wire(void* ctx, uint32_t idx) \{\n" ++
      s!"    struct {className}* s = (struct {className}*)ctx; (void)s;\n" ++
      s!"    switch (idx) \{\n" ++
      wireSwitch ++ "\n" ++
      s!"    }\n" ++
      s!"    return 0;\n" ++
      s!"}\n\n" ++
      s!"static void sparkle_jit_set_mem(void* ctx, uint32_t mem_idx, uint32_t addr, uint32_t data) \{\n" ++
      s!"    struct {className}* s = (struct {className}*)ctx; (void)s; (void)addr; (void)data;\n" ++
      s!"    switch (mem_idx) \{\n" ++
      memSetCases ++ "\n" ++
      s!"    }\n" ++
      s!"}\n\n" ++
      s!"static uint32_t sparkle_jit_get_mem(void* ctx, uint32_t mem_idx, uint32_t addr) \{\n" ++
      s!"    struct {className}* s = (struct {className}*)ctx; (void)s; (void)addr;\n" ++
      s!"    switch (mem_idx) \{\n" ++
      memGetCases ++ "\n" ++
      s!"    }\n" ++
      s!"    return 0;\n" ++
      s!"}\n\n" ++
      s!"static void sparkle_jit_memset_word(void* ctx, uint32_t mem_idx, uint32_t addr, uint32_t val, uint32_t count) \{\n" ++
      s!"    struct {className}* s = (struct {className}*)ctx; (void)s; (void)addr; (void)val; (void)count;\n" ++
      s!"    switch (mem_idx) \{\n" ++
      memsetWordCases ++ "\n" ++
      s!"    }\n" ++
      s!"}\n\n" ++
      s!"static const char* sparkle_jit_wire_name(uint32_t idx) \{\n" ++
      s!"    switch (idx) \{\n" ++
      wireNameSwitch ++ "\n" ++
      s!"    }\n" ++
      s!"    return \"\";\n" ++
      s!"}\n\n" ++
      s!"static uint32_t sparkle_jit_num_wires(void) \{ return {numWires}; }\n\n" ++
      s!"static void sparkle_jit_set_reg(void* ctx, uint32_t reg_idx, uint64_t val) \{\n" ++
      s!"    struct {className}* s = (struct {className}*)ctx; (void)s; (void)val;\n" ++
      s!"    switch (reg_idx) \{\n" ++
      setRegCases ++ "\n" ++
      s!"    }\n" ++
      s!"}\n\n" ++
      s!"static uint64_t sparkle_jit_get_reg(void* ctx, uint32_t reg_idx) \{\n" ++
      s!"    struct {className}* s = (struct {className}*)ctx; (void)s;\n" ++
      s!"    switch (reg_idx) \{\n" ++
      getRegCases ++ "\n" ++
      s!"    }\n" ++
      s!"    return 0;\n" ++
      s!"}\n\n" ++
      s!"static const char* sparkle_jit_reg_name(uint32_t idx) \{\n" ++
      s!"    switch (idx) \{\n" ++
      regNameCases ++ "\n" ++
      s!"    }\n" ++
      s!"    return \"\";\n" ++
      s!"}\n\n" ++
      s!"static uint32_t sparkle_jit_num_regs(void) \{ return {numRegs}; }\n\n" ++
      s!"static void* sparkle_jit_snapshot(void* ctx) \{\n" ++
      s!"    struct {className}* p = (struct {className}*)calloc(1, sizeof(struct {className}));\n" ++
      s!"    if (p) memcpy(p, ctx, sizeof(struct {className}));\n" ++
      s!"    return (void*)p;\n" ++
      s!"}\n\n" ++
      s!"static void sparkle_jit_restore(void* ctx, void* snap) \{\n" ++
      s!"    memcpy(ctx, snap, sizeof(struct {className}));\n" ++
      s!"}\n\n" ++
      s!"static void sparkle_jit_free_snapshot(void* snap) \{ free(snap); }\n\n"

    let vtableInst :=
      "/* ---- The single externally-visible symbol ---- */\n\n" ++
      "static const JitVTable g_sparkle_jit_vtable = {\n" ++
      "    .create = sparkle_jit_create,\n" ++
      "    .destroy = sparkle_jit_destroy,\n" ++
      "    .reset = sparkle_jit_reset,\n" ++
      "    .eval = sparkle_jit_eval,\n" ++
      "    .tick = sparkle_jit_tick,\n" ++
      "    .eval_tick = sparkle_jit_eval_tick,\n" ++
      "    .set_input = sparkle_jit_set_input,\n" ++
      "    .get_output = sparkle_jit_get_output,\n" ++
      "    .get_wire = sparkle_jit_get_wire,\n" ++
      "    .set_mem = sparkle_jit_set_mem,\n" ++
      "    .get_mem = sparkle_jit_get_mem,\n" ++
      "    .memset_word = sparkle_jit_memset_word,\n" ++
      "    .wire_name = sparkle_jit_wire_name,\n" ++
      "    .num_wires = sparkle_jit_num_wires,\n" ++
      "    .set_reg = sparkle_jit_set_reg,\n" ++
      "    .get_reg = sparkle_jit_get_reg,\n" ++
      "    .reg_name = sparkle_jit_reg_name,\n" ++
      "    .num_regs = sparkle_jit_num_regs,\n" ++
      "    .snapshot = sparkle_jit_snapshot,\n" ++
      "    .restore = sparkle_jit_restore,\n" ++
      "    .free_snapshot = sparkle_jit_free_snapshot,\n" ++
      "};\n\n" ++
      "/* The ONLY externally-visible symbol from this .so. */\n" ++
      "__attribute__((visibility(\"default\")))\n" ++
      "const JitVTable* jit_vtable(void) {\n" ++
      "    return &g_sparkle_jit_vtable;\n" ++
      "}\n"

    classCode ++ "\n" ++ vtableType ++ trampolines ++ vtableInst

end Sparkle.Backend.CSim
