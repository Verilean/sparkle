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
import Sparkle.IR.Specialize
import Std.Data.HashSet
import Std.Data.HashMap

namespace Sparkle.Backend.CSim

open Sparkle.IR.AST
open Sparkle.IR.Type

/-- Name→type lookup used by the emitters.  Backed by a `Std.HashMap`
    so `lookupWidth` is O(1): `emitExpr`/`inferExprWidth` probe it once
    per expression node.  The old linear-scan `List` made emit O(N·M)
    over a module's N nodes and M wires — quadratic on large designs
    like Keccak's ~1600-wire round. -/
abbrev TypeMap := Std.HashMap String HWType

-- Helper to embed literal braces in string interpolation
private def ob : String := "{"
private def cb : String := "}"

/-- Build a name-to-type map from a module's ports and wires.
    `insertIfNew` preserves the first binding on a name clash, matching
    the old `List.find?` (inputs, then outputs, then wires) semantics. -/
def buildTypeMap (m : Module) : TypeMap :=
  let entries := (m.inputs ++ m.outputs ++ m.wires).map fun (p : Port) => (p.name, p.ty)
  entries.foldl (fun acc (n, t) => acc.insertIfNew n t) {}

/-- Look up bit-width for a name in the type map -/
def lookupWidth (typeMap : TypeMap) (name : String) : Nat :=
  match typeMap.get? name with
  | some ty => ty.bitWidth
  | none => 32

/-- Sanitize a name to be a valid C identifier.
    Fast path: called per name occurrence during emission (millions of
    times on XiangShan-scale modules); almost every name is clean. -/
def sanitizeName (name : String) : String :=
  if name.all (fun c =>
      c.isAlphanum || c == '_' || c == '$') then
    name
  else
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
  | .bitVectorDim _ => "SPARKLE_UNSUPPORTED_SYMBOLIC_WIDTH"

/-- Total array length suffix for a HWType, e.g. `[3]` for a
    96-bit wide type, `[8][3]` for `array 8 (bitVector 96)`,
    or empty for a single ≤ 64-bit scalar. -/
partial def emitArraySuffix : HWType → String
  | .bit => ""
  | .bitVector w =>
    if w ≤ 64 then "" else s!"[{wordsOf w}]"
  | .array size elemType => s!"[{size}]" ++ emitArraySuffix elemType
  | .bitVectorDim _ => "[SPARKLE_UNSUPPORTED_SYMBOLIC_WIDTH]"

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
  -- A constant is only "already masked" if its DECLARED width fits the
  -- target width.  `.const (-1) 32` (the SVParser's bitwise-NOT mask)
  -- feeding a 1-bit wire used to pass here unconditionally, so the xor
  -- arm below skipped the store mask and a `~x` landed as 0xff in a
  -- 1-bit uint8 field (XiangShan ICacheMshr.io_wfi_wfiSafe, 14 modules).
  | .const _ cw => cw ≤ w
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
partial def inferExprWidth (typeMap : TypeMap) : Expr → Nat
  | .const _ w => w
  | .ref name => lookupWidth typeMap name
  | .slice _ hi lo => hi - lo + 1
  | .sliceDim _ _ _ => 0
  | .concat args =>
    args.foldl (fun acc arg => acc + inferExprWidth typeMap arg) 0
  | .index arr _ =>
    match arr with
    | .ref name =>
      match typeMap.get? name with
      | some (.array _ elemType) => elemType.bitWidth
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

/-- Wide (>64-bit) add/sub as a multi-word ripple-carry/borrow GCC
    statement-expression returning a compound-literal array (the same
    shape the wide-`.mul` arm and `emitStmt`'s memcpy assign expect).
    Operands `a`/`b` are the already-emitted C strings for two `nWords`
    32-bit-slot arrays; they are indexed directly (`(a)[i]`), so they
    must be side-effect-free lvalues/literals (refs, consts) — which is
    what add/sub operands always are.  Without this, wide `+`/`-` fell
    through to the scalar arm and emitted `arrayA - arrayB`, i.e. C
    pointer subtraction — a hard compile error (breaks every >64-bit
    datapath, e.g. the secp256k1 mul's 258-bit accumulator reduce). -/
private def wideAddSubExpr (isAdd : Bool) (a b : String) (nWords : Nat) : String :=
  let words := (List.range nWords).map (fun i =>
    let ai := "(uint64_t)(" ++ a ++ ")[" ++ toString i ++ "]"
    let bi := "(uint64_t)(" ++ b ++ ")[" ++ toString i ++ "]"
    if isAdd then
      "uint64_t __s" ++ toString i ++ " = " ++ ai ++ " + " ++ bi ++
        " + __c; __c = __s" ++ toString i ++ " >> 32;"
    else
      "int64_t __s" ++ toString i ++ " = (int64_t)" ++ ai ++ " - (int64_t)" ++ bi ++
        " - (int64_t)__c; __c = (__s" ++ toString i ++ " < 0) ? 1 : 0;")
  let elems := String.intercalate ", "
    ((List.range nWords).map (fun i => "(uint32_t)__s" ++ toString i))
  let body := "uint64_t __c = 0; " ++ String.intercalate " " words ++
    " (uint32_t[" ++ toString nWords ++ "]){" ++ elems ++ "};"
  "(__extension__ ({ " ++ body ++ " }))"

/-- Emit the C lines that ripple-add/sub two `nWords`-slot arrays `aS`,
    `bS` DIRECTLY into `dst` (no compound-literal statement-expression,
    whose block-scoped storage dangles before a `memcpy` reads it). -/
private def wideAddSubInto (isAdd : Bool) (dst aS bS : String) (nWords : Nat) : List String :=
  if isAdd then
    ["        { uint64_t __c = 0;"]
    ++ (List.range nWords).map (fun j =>
        s!"          __c += (uint64_t){aS}[{j}] + (uint64_t){bS}[{j}]; {dst}[{j}] = (uint32_t)__c; __c >>= 32;")
    ++ ["        }"]
  else
    ["        { uint64_t __brw = 0;"]
    ++ (List.range nWords).map (fun j =>
        s!"          \{ uint64_t __bi = (uint64_t){bS}[{j}] + __brw; {dst}[{j}] = (uint32_t)((uint64_t){aS}[{j}] - __bi); __brw = ((uint64_t){aS}[{j}] < __bi) ? 1 : 0; }")
    ++ ["        }"]

/-- Wide (>64-bit) unsigned compare as a most-significant-word-first
    nested ternary.  Returns `a < b` when `strict`, else `a <= b`.
    Without this, wide `<`/`<=`/… fell through to the scalar arm and
    compared the operand ARRAYS as pointers (silently wrong), which
    breaks e.g. the modular reduction's `if (2·acc ≥ p)` gate. -/
private def wideCmpExpr (strict : Bool) (a b : String) (nWords : Nat) : String :=
  let base := if strict then "0" else "1"
  let expr := (List.range nWords).foldl (fun rest i =>
    let ai := "(uint32_t)(" ++ a ++ ")[" ++ toString i ++ "]"
    let bi := "(uint32_t)(" ++ b ++ ")[" ++ toString i ++ "]"
    "(" ++ ai ++ " < " ++ bi ++ " ? 1 : (" ++ ai ++ " > " ++ bi ++ " ? 0 : " ++ rest ++ "))")
    base
  "(" ++ expr ++ ")"

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
partial def emitExpr (typeMap : TypeMap) (e : Expr) : String :=
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
                  -- Extract `bitCount` (≤ 32) bits of the WIDE operand starting
                  -- at bit `bitInArgLo`.  These bits can straddle two of the
                  -- operand's own 32-bit words — combine both (the old code took
                  -- only the low word and dropped the overflow, corrupting any
                  -- non-word-aligned wide operand, e.g. HMAC's `dLo8‖zmodn‖…`).
                  let argSlot := bitInArgLo / 32
                  let argBitInSlot := bitInArgLo % 32
                  let fullMask : Nat := (2 ^ bitCount) - 1
                  let fmStr := s!"0x{Nat.toDigits 16 fullMask |> String.ofList}ULL"
                  match arg with
                  | .const value _ =>
                    let modulus : Int := (2 : Int) ^ w
                    let unsigned : Nat :=
                      if value < 0 then (((value % modulus) + modulus) % modulus).toNat
                      else value.toNat
                    let bits := (unsigned >>> bitInArgLo) &&& fullMask
                    s!"0x{Nat.toDigits 16 bits |> String.ofList}ULL"
                  | _ =>
                    if argBitInSlot == 0 then
                      s!"((uint64_t){argExpr}[{argSlot}] & {fmStr})"
                    else
                      let spans := argBitInSlot + bitCount > 32
                      let hiP := if spans then s!" | ((uint64_t){argExpr}[{argSlot + 1}] << {32 - argBitInSlot})" else ""
                      s!"((((uint64_t){argExpr}[{argSlot}] >> {argBitInSlot}){hiP}) & {fmStr})"
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
        -- A 33..64-bit slice at a non-zero offset spans up to THREE
        -- source words (e.g. `ram[88:25]`: bits 25-31 of word 0, all of
        -- word 1, bits 0-24 of word 2).  The old two-word form silently
        -- zeroed everything above bit 32+(32-offset) — XiangShan's
        -- Queue1_RegMapperInput lost the top half of its 64-bit payload.
        -- Build the general OR over words lo/32 .. hi/32.  Shift bounds:
        -- for k ≥ 1, 32k - bitOffset ≤ 64 - bitOffset ≤ 63 when a third
        -- word exists (bitOffset ≥ 1), so no UB-range shifts.
        let hiWord := hi / 32
        let terms := (List.range (hiWord - wordIdx + 1)).map fun k =>
          let j := wordIdx + k
          if k == 0 then
            if bitOffset == 0 then s!"(uint64_t){srcExpr}[{j}]"
            else s!"((uint64_t){srcExpr}[{j}] >> {bitOffset})"
          else
            s!"((uint64_t){srcExpr}[{j}] << {32 * k - bitOffset})"
        s!"((({String.intercalate " | " terms})) & {maskStr})"
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

  | .sliceDim _ _ _ =>
    "SPARKLE_UNSUPPORTED_SYMBOLIC_SLICE"
  | .index arr idx =>
    s!"{emitExpr typeMap arr}[{emitExpr typeMap idx}]"

  | .op .mux args =>
    match args with
    | [cond, thenVal, elseVal] =>
      s!"({emitExpr typeMap cond} ? {emitExpr typeMap thenVal} : {emitExpr typeMap elseVal})"
    | _ => "/* ERROR: mux requires 3 arguments */"

  | .op .not args =>
    match args with
    -- `.op .not` is a hardware complement: LOGICAL `!` for a 1-bit Bool, but
    -- BITWISE `~` (masked to the operand width) for a multi-bit bus.  Emitting
    -- `!` for a wide bus collapses it to 0/1 (e.g. the 32-bit `~e` in SHA-256's
    -- Ch became `!e`, silently corrupting every hash).
    | [arg] =>
      let w := inferExprWidth typeMap arg
      if w ≤ 1 then s!"(!{emitExpr typeMap arg})"
      else s!"((~{emitExpr typeMap arg}) & {(1 <<< w) - 1}ULL)"
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
        -- Signed compare at the INFERRED value width w.  A plain signed
        -- C cast only works when w is exactly the cast's width: for
        -- w = 6 the value's sign bit (bit 5) is not int8_t's bit 7, so
        -- `(int8_t)x` reads padding as sign (XiangShan FIFOReg's wrap
        -- flag).  Compare with the sign bit flipped instead — unsigned,
        -- container-independent, and `& mask` shields against any
        -- unmasked upper bits.
        let w := max (inferExprWidth typeMap arg1) (inferExprWidth typeMap arg2)
        if w == 8 || w == 16 || w == 32 || w == 64 then
          let stype := signedCastType w
          s!"(({stype}){emitExpr typeMap arg1} {emitCOperator operator} ({stype}){emitExpr typeMap arg2} ? 1 : 0)"
        else
          let w := min w 64
          let m := s!"0x{String.ofList (Nat.toDigits 16 (2 ^ w - 1))}ULL"
          let sb := s!"0x{String.ofList (Nat.toDigits 16 (2 ^ (w - 1)))}ULL"
          s!"(((({emitExpr typeMap arg1} & {m}) ^ {sb}) {emitCOperator operator} (({emitExpr typeMap arg2} & {m}) ^ {sb})) ? 1 : 0)"
      | .shr | .shl =>
        -- Verilog: a shift amount ≥ the value width yields 0.  C: a
        -- shift ≥ the CONTAINER width is UB — x86 wraps the count mod
        -- 32/64, so `table_0 >> req` with a random 8-bit req (BusyTable
        -- read ports) produced phantom bits whenever req ≥ 32.  Promote
        -- to uint64 and guard dynamic amounts; constant amounts fold.
        -- ONLY for ≤64-bit operands: a >64-bit operand here is a uint32
        -- ARRAY, and casting it to uint64 shifts the POINTER (the wide
        -- paths in matWide / the top-level assign arms own that case).
        let w1 := inferExprWidth typeMap arg1
        if w1 > 64 then
          -- A >64-bit operand is a uint32 ARRAY here.  A wide SHR whose
          -- result is consumed in a ≤64-bit context (firtool's packed-
          -- array dynamic select `(_GEN >> (addr*8)) & 0xff`) extracts a
          -- 64-bit window via the emitted helper; wide SHL nested in a
          -- scalar context has no meaningful ≤64-bit reading — leave the
          -- (non-compiling) raw form so it fails loudly.
          if operator == .shr then
            s!"sparkle_wide_shr64({emitExpr typeMap arg1}, {wordsOf w1}u, (unsigned)({emitExpr typeMap arg2}))"
          else
            s!"({emitExpr typeMap arg1} {emitCOperator operator} {emitExpr typeMap arg2})"
        else
          let cop := if operator == .shr then ">>" else "<<"
          match arg2 with
          | .const v _ =>
            if v ≥ 64 then "0ULL"
            else s!"((uint64_t){emitExpr typeMap arg1} {cop} {v})"
          | _ =>
            let aS := emitExpr typeMap arg1
            let bS := emitExpr typeMap arg2
            s!"((uint64_t)({bS}) >= 64 ? 0ULL : ((uint64_t){aS} {cop} ({bS})))"
      | .asr =>
        let w := max (inferExprWidth typeMap arg1) 32
        let stype := signedCastType w
        let utype := emitScalarBase (.bitVector w)
        s!"(({utype})(({stype}){emitExpr typeMap arg1} >> {emitExpr typeMap arg2}))"
      | .eq =>
        let w := max (inferExprWidth typeMap arg1) (inferExprWidth typeMap arg2)
        if w > 64 then
          -- Wide equality: AND per-word compares.  A `const 0` operand
          -- becomes a per-word zero-check.  Without this, `!(x)` / `x==y`
          -- on the 32-bit-slot ARRAYS were pointer ops (always false /
          -- address compare) — e.g. the bit-serial multiplier's
          -- "is this bit zero?" test was stuck true, so it added the
          -- multiplicand every cycle.
          let n := wordsOf w
          let mkTerms (x y : Expr) : String :=
            let xs := emitExpr typeMap x
            match y with
            | .const 0 _ =>
              String.intercalate " && " ((List.range n).map (fun j => s!"({xs}[{j}] == 0)"))
            | _ =>
              let ys := emitExpr typeMap y
              String.intercalate " && " ((List.range n).map (fun j => s!"({xs}[{j}] == {ys}[{j}])"))
          match arg1, arg2 with
          | _, .const 0 _ => s!"(({mkTerms arg1 arg2}) ? 1 : 0)"
          | .const 0 _, _ => s!"(({mkTerms arg2 arg1}) ? 1 : 0)"
          | _, _          => s!"(({mkTerms arg1 arg2}) ? 1 : 0)"
        else
        match arg1, arg2 with
        | _, .const 0 _ => s!"(!({emitExpr typeMap arg1}) ? 1 : 0)"
        | .const 0 _, _ => s!"(!({emitExpr typeMap arg2}) ? 1 : 0)"
        | _, _ => s!"({emitExpr typeMap arg1} == {emitExpr typeMap arg2} ? 1 : 0)"
      | .lt_u | .le_u | .gt_u | .ge_u =>
        let w := max (inferExprWidth typeMap arg1) (inferExprWidth typeMap arg2)
        if w > 64 then
          let a := emitExpr typeMap arg1
          let b := emitExpr typeMap arg2
          let n := wordsOf w
          -- a≥b ⟺ b≤a ; a>b ⟺ b<a — reuse the (strict) le/lt form by
          -- swapping operands for the ≥/> cases.
          match operator with
          | .lt_u => wideCmpExpr true  a b n
          | .le_u => wideCmpExpr false a b n
          | .gt_u => wideCmpExpr true  b a n
          | _     => wideCmpExpr false b a n   -- .ge_u
        else
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
      | .add =>
        let w := max (inferExprWidth typeMap arg1) (inferExprWidth typeMap arg2)
        if w > 64 then wideAddSubExpr true (emitExpr typeMap arg1) (emitExpr typeMap arg2) (wordsOf w)
        else s!"({emitExpr typeMap arg1} + {emitExpr typeMap arg2})"
      | .sub =>
        let w := max (inferExprWidth typeMap arg1) (inferExprWidth typeMap arg2)
        if w > 64 then wideAddSubExpr false (emitExpr typeMap arg1) (emitExpr typeMap arg2) (wordsOf w)
        else s!"({emitExpr typeMap arg1} - {emitExpr typeMap arg2})"
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
def emitMuxAsIfElse (typeMap : TypeMap)
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
partial def emitStmt (stmt : Stmt) (typeMap : TypeMap)
    (design : Option Design := none) : StmtParts :=
  match stmt with
  | .assign lhs rhs =>
    let width := lookupWidth typeMap lhs
    if width > 64 then
      let sn := sanitizeName lhs
      let nWords := wordsOf width
      -- Per-word slot expressions for wide logical shifts (shared by the
      -- direct `.op .shl`/`.op .shr` arms and `matWide` below).
      let constAmt : Expr → Nat := fun b => match b with | .const v _ => v.toNat | _ => 0
      let shlSlot (aS : String) (sa j : Nat) : String :=
        let k := sa / 32; let r := sa % 32
        if j < k then "0u"
        else if j == k then (if r == 0 then s!"{aS}[0]" else s!"({aS}[0] << {r})")
        else
          let lower := j - k
          let upperShift := if r == 0 then "0u" else s!"({aS}[{lower - 1}] >> {32 - r})"
          if r == 0 then s!"{aS}[{lower}]" else s!"(({aS}[{lower}] << {r}) | {upperShift})"
      let shrSlot (aS : String) (sa srcWords j : Nat) : String :=
        let k := sa / 32; let r := sa % 32
        let idx := j + k
        if idx ≥ srcWords then "0u"
        else if r == 0 then s!"{aS}[{idx}]"
        else
          let hiPart := if idx + 1 < srcWords then s!" | ({aS}[{idx + 1}] << {32 - r})" else ""
          s!"(({aS}[{idx}] >> {r}){hiPart})"
      -- Materialise a single operand into an indexable array: a `.ref` renders
      -- directly; anything else (concat/const compound literal, …) is memcpy'd
      -- into a temp so it can be read per-word.
      let matOp (label : String) (e : Expr) : List String × String :=
        match e with
        | .ref _ => ([], emitExpr typeMap e)
        | _ =>
          let tmp := s!"__{label}_{sn}"
          ([s!"        uint32_t {tmp}[{nWords}]; memcpy({tmp}, {emitExpr typeMap e}, sizeof({tmp}));"], tmp)
      -- Materialise a wide sub-expression into an indexable temp array so it
      -- can be read per-word (needed when a shift/bitwise op is NESTED inside
      -- another op — `emitExpr` of a wide op is not a valid C expression, e.g.
      -- HMAC's `(key ⊕ c36) ++ c36` produced an invalid `array ^ array`).
      let rec matWide (label : String) (e : Expr) : List String × String :=
        -- A NARROW (≤64-bit) operand inside a wide op is a C scalar —
        -- indexing it `[j]` is invalid (FMA's borrow chain fed
        -- `(x >> 26) & 1` straight into the wide subtract).  Box it into
        -- a zero-extended word array first.
        let wE := inferExprWidth typeMap e
        if wE ≤ 64 && (match e with | .ref _ => wE ≤ 64 && false | _ => true) then
          let tmp := s!"__{label}_{sn}"
          ([ s!"        uint32_t {tmp}[{nWords}]; memset({tmp}, 0, sizeof({tmp}));"
           , s!"        \{ uint64_t {tmp}_v = (uint64_t){emitExpr typeMap e}; {tmp}[0] = (uint32_t){tmp}_v;" ++
             (if nWords > 1 then s!" {tmp}[1] = (uint32_t)({tmp}_v >> 32);" else "") ++ " }"
           ], tmp)
        else
        match e with
        | .ref name =>
          if (lookupWidth typeMap name) ≤ 64 then
            -- narrow REF: same boxing (a scalar struct field can't be
            -- indexed per word either)
            let tmp := s!"__{label}_{sn}"
            ([ s!"        uint32_t {tmp}[{nWords}]; memset({tmp}, 0, sizeof({tmp}));"
             , s!"        \{ uint64_t {tmp}_v = (uint64_t){emitExpr typeMap e}; {tmp}[0] = (uint32_t){tmp}_v;" ++
               (if nWords > 1 then s!" {tmp}[1] = (uint32_t)({tmp}_v >> 32);" else "") ++ " }"
             ], tmp)
          else
            ([], emitExpr typeMap e)
        | .op .shl [a, b] =>
          -- Materialise the shifted operand too: it can itself be a compound
          -- (concat / nested op / another wide op), and `aS[j]` indexing needs
          -- an array lvalue.
          let (da, aS) := matWide s!"{label}s" a
          let tmp := s!"__{label}_{sn}"
          match b with
          | .const v _ =>
            let sa := v.toNat
            (da ++ (s!"        uint32_t {tmp}[{nWords}];"
              :: (List.range nWords).map (fun j => s!"        {tmp}[{j}] = {shlSlot aS sa j};")), tmp)
          | _ =>
            -- DYNAMIC shift amount.  The old `constAmt` fallback treated any
            -- non-constant amount as 0 — XiangShan's Phr rotates a doubled
            -- 52-bit history vector with `{phr, phr} >> ptr` (104-bit), and
            -- every folded-history output silently used the UNSHIFTED value.
            -- Emit a runtime word loop instead.
            let bS := emitExpr typeMap b
            (da ++
              [ s!"        uint32_t {tmp}[{nWords}];"
              , s!"        \{ unsigned {tmp}_sa = (unsigned)({bS}); unsigned {tmp}_k = {tmp}_sa >> 5, {tmp}_r = {tmp}_sa & 31;"
              , s!"          for (unsigned {tmp}_j = 0; {tmp}_j < {nWords}u; {tmp}_j++) \{"
              , s!"            uint32_t {tmp}_lo = ({tmp}_j >= {tmp}_k) ? {aS}[{tmp}_j - {tmp}_k] : 0u;"
              , s!"            uint32_t {tmp}_hi = ({tmp}_j >= {tmp}_k + 1) ? {aS}[{tmp}_j - {tmp}_k - 1] : 0u;"
              , s!"            {tmp}[{tmp}_j] = {tmp}_r ? (({tmp}_lo << {tmp}_r) | ({tmp}_hi >> (32 - {tmp}_r))) : {tmp}_lo;"
              , s!"          }"
              , s!"        }" ], tmp)
        | .op .shr [a, b] =>
          let (da, aS) := matWide s!"{label}s" a
          let tmp := s!"__{label}_{sn}"
          let srcWords := wordsOf (inferExprWidth typeMap a)
          match b with
          | .const v _ =>
            let sa := v.toNat
            (da ++ (s!"        uint32_t {tmp}[{nWords}];"
              :: (List.range nWords).map (fun j => s!"        {tmp}[{j}] = {shrSlot aS sa srcWords j};")), tmp)
          | _ =>
            -- Dynamic amount: same word loop, shifting right (see shl note).
            let bS := emitExpr typeMap b
            (da ++
              [ s!"        uint32_t {tmp}[{nWords}];"
              , s!"        \{ unsigned {tmp}_sa = (unsigned)({bS}); unsigned {tmp}_k = {tmp}_sa >> 5, {tmp}_r = {tmp}_sa & 31;"
              , s!"          for (unsigned {tmp}_j = 0; {tmp}_j < {nWords}u; {tmp}_j++) \{"
              , s!"            uint32_t {tmp}_lo = ({tmp}_j + {tmp}_k < {srcWords}u) ? {aS}[{tmp}_j + {tmp}_k] : 0u;"
              , s!"            uint32_t {tmp}_hi = ({tmp}_j + {tmp}_k + 1 < {srcWords}u) ? {aS}[{tmp}_j + {tmp}_k + 1] : 0u;"
              , s!"            {tmp}[{tmp}_j] = {tmp}_r ? (({tmp}_lo >> {tmp}_r) | ({tmp}_hi << (32 - {tmp}_r))) : {tmp}_lo;"
              , s!"          }"
              , s!"        }" ], tmp)
        | .op .mux [c, t, f] =>
          -- Nested wide mux (a mux feeding a mux operand): recurse on both
          -- branches, then select per word on the scalar condition.  Without
          -- this arm the fallback rendered `cond ? wide_expr : wide_expr` as
          -- a C ternary over arrays — invalid C (caught by the memcached
          -- CI job after the flat pending-writes rework changed which
          -- expressions stay inline instead of getting their own wires).
          let condS := emitExpr typeMap c
          let (dt, tS) := matWide s!"{label}t" t
          let (df, fS) := matWide s!"{label}e" f
          let tmp := s!"__{label}_{sn}"
          (dt ++ df ++ (s!"        uint32_t {tmp}[{nWords}];"
            :: (List.range nWords).map (fun j =>
                 s!"        {tmp}[{j}] = ({condS}) ? {tS}[{j}] : {fS}[{j}];")), tmp)
        | .op .xor [a, b] =>
          -- Operands recurse through matWide (NOT the generic matOp): they can
          -- themselves be wide shifts/muxes, whose emitExpr is not valid C.
          let (da, sa) := matWide s!"{label}a" a; let (db, sb) := matWide s!"{label}b" b
          let tmp := s!"__{label}_{sn}"
          (da ++ db ++ (s!"        uint32_t {tmp}[{nWords}];"
            :: (List.range nWords).map (fun j => s!"        {tmp}[{j}] = {sa}[{j}] ^ {sb}[{j}];")), tmp)
        | .op .and [a, b] =>
          let (da, sa) := matWide s!"{label}a" a; let (db, sb) := matWide s!"{label}b" b
          let tmp := s!"__{label}_{sn}"
          (da ++ db ++ (s!"        uint32_t {tmp}[{nWords}];"
            :: (List.range nWords).map (fun j => s!"        {tmp}[{j}] = {sa}[{j}] & {sb}[{j}];")), tmp)
        | .op .or [a, b] =>
          let (da, sa) := matWide s!"{label}a" a; let (db, sb) := matWide s!"{label}b" b
          let tmp := s!"__{label}_{sn}"
          (da ++ db ++ (s!"        uint32_t {tmp}[{nWords}];"
            :: (List.range nWords).map (fun j => s!"        {tmp}[{j}] = {sa}[{j}] | {sb}[{j}];")), tmp)
        | .op .add [a, b] =>
          -- operands through matWide: a narrow or compound operand has
          -- no indexable rendering (FMA fed `(x >> 26) & 1` into the
          -- wide borrow chain)
          let (da, sa) := matWide s!"{label}a" a; let (db, sb) := matWide s!"{label}b" b
          let tmp := s!"__{label}_{sn}"
          (da ++ db ++ (s!"        uint32_t {tmp}[{nWords}];"
            :: wideAddSubInto true tmp sa sb nWords), tmp)
        | .op .sub [a, b] =>
          let (da, sa) := matWide s!"{label}a" a; let (db, sb) := matWide s!"{label}b" b
          let tmp := s!"__{label}_{sn}"
          (da ++ db ++ (s!"        uint32_t {tmp}[{nWords}];"
            :: wideAddSubInto false tmp sa sb nWords), tmp)
        | .concat cargs =>
          -- Wide concat: arguments that are themselves wide OPS have no
          -- inline rendering — materialise them first (FMA nests a wide
          -- XOR inside a mux'd concat), then build the compound literal
          -- over refs with a width-shadowed type map.
          let (ds, cargs', tws) := Id.run do
            let mut ds : List String := []
            let mut out : List Expr := []
            let mut tws : List (String × Nat) := []
            let mut i := 0
            for a in cargs do
              let wa := inferExprWidth typeMap a
              let needsMat := wa > 64 && (match a with
                | .ref _ => false | .const _ _ => false | _ => true)
              if needsMat then
                let (da, aS) := matWide s!"{label}k{i}" a
                ds := ds ++ da
                out := out ++ [.ref aS]
                tws := tws ++ [(aS, wa)]
              else
                out := out ++ [a]
              i := i + 1
            return (ds, out, tws)
          let typeMap' := tws.foldl
            (fun tm (n, w) => tm.insert n (HWType.bitVector w)) typeMap
          let tmp := s!"__{label}_{sn}"
          (ds ++ [s!"        uint32_t {tmp}[{nWords}]; memcpy({tmp}, {emitExpr typeMap' (.concat cargs')}, sizeof({tmp}));"], tmp)
        | _ =>
          let tmp := s!"__{label}_{sn}"; let init := emitExpr typeMap e
          ([s!"        uint32_t {tmp}[{nWords}]; memcpy({tmp}, {init}, sizeof({tmp}));"], tmp)
      let parts := match rhs with
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
      | .concat cargs =>
        -- Wide concat whose ARGUMENTS may themselves be wide OPS
        -- (XiangShan CSA4to2: `{…, ((a&b)|(a&c)|(b&c))[…], …}` — a
        -- majority function of 128-bit operands).  `emitExpr` cannot
        -- render a wide op inline (arrays have no `&`), so materialise
        -- every wide non-ref argument through `matWide` first and
        -- rebuild the concat over the temp names.
        let (decls, cargs', tempWidths) := Id.run do
          let mut ds : List String := []
          let mut out : List Expr := []
          let mut tws : List (String × Nat) := []
          let mut i := 0
          for a in cargs do
            let wa := inferExprWidth typeMap a
            let needsMat := wa > 64 && (match a with
              | .ref _ => false | .const _ _ => false | _ => true)
            if needsMat then
              let (da, aS) := matWide s!"cc{i}" a
              ds := ds ++ da
              out := out ++ [.ref aS]
              tws := tws ++ [(aS, wa)]
            else
              out := out ++ [a]
            i := i + 1
          return (ds, out, tws)
        -- the temps are locals, not module wires: shadow the type map so
        -- width inference sees them
        let typeMap' := tempWidths.foldl
          (fun tm (n, w) => tm.insert n (HWType.bitVector w)) typeMap
        let expr := emitExpr typeMap' (.concat cargs')
        { declarations := []
        , evalBody := decls ++
            [s!"        memcpy({sn}, {expr}, sizeof({sn}));"]
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .add [a, b] =>
        -- Wide add: ripple-carry written DIRECTLY into the destination
        -- words.  (Emitting into `sn[j]` avoids the compound-literal
        -- statement-expression whose block-scoped storage dangles by the
        -- time a `memcpy` reads it — that produced garbage, not the sum.
        -- These assignments were also previously dropped entirely by the
        -- `_ => empty` default, reading 0.)
        let (da, sa) := matWide "adda" a; let (db, sb) := matWide "addb" b
        { declarations := []
        , evalBody := da ++ db ++ wideAddSubInto true sn sa sb nWords
        , tickBody := [], resetBody := [], evalTickLocals := [] }
      | .op .sub [a, b] =>
        -- Wide sub: ripple-borrow written directly into the destination.
        let (da, sa) := matWide "suba" a; let (db, sb) := matWide "subb" b
        { declarations := []
        , evalBody := da ++ db ++ wideAddSubInto false sn sa sb nWords
        , tickBody := [], resetBody := [], evalTickLocals := [] }
      | .op .mux [cond, thenVal, elseVal] =>
        -- Wide mux: pick a side per slot via ternary on the
        -- shared scalar condition.  Both branches are wide
        -- and identifier-shaped (a `.ref` or a `.const`); if
        -- a branch is a `.const` we materialise it to a
        -- temporary first (compound literal slot indexing
        -- isn't valid in C without parens).
        let condS := emitExpr typeMap cond
        -- Both branches materialised through `matWide`, which handles ref /
        -- shift / bitwise / add / sub / compound-literal shapes uniformly.
        let (thenDecl, thenSym) := matWide "muxt" thenVal
        let (elseDecl, elseSym) := matWide "muxe" elseVal
        let lines := (List.range nWords).map fun j =>
          s!"        {sn}[{j}] = ({condS}) ? {thenSym}[{j}] : {elseSym}[{j}];"
        { declarations := []
        , evalBody := thenDecl ++ elseDecl ++ lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .or [a, b] =>
        let (da, aS) := matWide "or_a" a
        let (db, bS) := matWide "or_b" b
        let lines := (List.range nWords).map fun j =>
          s!"        {sn}[{j}] = {aS}[{j}] | {bS}[{j}];"
        { declarations := []
        , evalBody := da ++ db ++ lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .and [a, b] =>
        let (da, aS) := matWide "and_a" a
        let (db, bS) := matWide "and_b" b
        let lines := (List.range nWords).map fun j =>
          s!"        {sn}[{j}] = {aS}[{j}] & {bS}[{j}];"
        { declarations := []
        , evalBody := da ++ db ++ lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .xor [a, b] =>
        let (da, aS) := matWide "xor_a" a
        let (db, bS) := matWide "xor_b" b
        let lines := (List.range nWords).map fun j =>
          s!"        {sn}[{j}] = {aS}[{j}] ^ {bS}[{j}];"
        { declarations := []
        , evalBody := da ++ db ++ lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | .op .shl [a, b] =>
        let aS := emitExpr typeMap a
        match b with
        | .const v _ =>
          let shiftAmount := v.toNat
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
        | _ =>
          -- DYNAMIC shift amount: the old fallback treated it as 0.  Runtime
          -- word loop (mirrors the nested matWide arm; see the Phr note there).
          let bS := emitExpr typeMap b
          { declarations := []
          , evalBody :=
              [ s!"        \{ unsigned {sn}_sa = (unsigned)({bS}); unsigned {sn}_k = {sn}_sa >> 5, {sn}_r = {sn}_sa & 31;"
              , s!"          for (unsigned {sn}_j = 0; {sn}_j < {nWords}u; {sn}_j++) \{"
              , s!"            uint32_t {sn}_lo = ({sn}_j >= {sn}_k) ? {aS}[{sn}_j - {sn}_k] : 0u;"
              , s!"            uint32_t {sn}_hi = ({sn}_j >= {sn}_k + 1) ? {aS}[{sn}_j - {sn}_k - 1] : 0u;"
              , s!"            {sn}[{sn}_j] = {sn}_r ? (({sn}_lo << {sn}_r) | ({sn}_hi >> (32 - {sn}_r))) : {sn}_lo;"
              , s!"          }"
              , s!"        }" ]
          , tickBody := []
          , resetBody := []
          , evalTickLocals := [] }
      | .op .shr [a, b] =>
        -- Wide logical shift right.  (Constant amounts were previously
        -- dropped by the `_ => empty` default → the shifted word read 0;
        -- e.g. the bit-serial multiplier's MSB extraction `b >> 255`
        -- always yielded 0, so the whole multiply was silently wrong.
        -- DYNAMIC amounts were then treated as 0 — XiangShan Phr's
        -- `{phr, phr} >> ptr` rotation read the unshifted vector.)
        let aS := emitExpr typeMap a
        let srcWords := wordsOf (inferExprWidth typeMap a)
        match b with
        | .const v _ =>
          let shiftAmount := v.toNat
          let k := shiftAmount / 32
          let r := shiftAmount % 32
          let slot (j : Nat) : String :=
            let idx := j + k
            if idx ≥ srcWords then "0u"
            else if r == 0 then s!"{aS}[{idx}]"
            else
              let hiPart := if idx + 1 < srcWords then s!" | ({aS}[{idx + 1}] << {32 - r})" else ""
              s!"(({aS}[{idx}] >> {r}){hiPart})"
          let lines := (List.range nWords).map fun j =>
            s!"        {sn}[{j}] = {slot j};"
          { declarations := []
          , evalBody := lines
          , tickBody := []
          , resetBody := []
          , evalTickLocals := [] }
        | _ =>
          let bS := emitExpr typeMap b
          { declarations := []
          , evalBody :=
              [ s!"        \{ unsigned {sn}_sa = (unsigned)({bS}); unsigned {sn}_k = {sn}_sa >> 5, {sn}_r = {sn}_sa & 31;"
              , s!"          for (unsigned {sn}_j = 0; {sn}_j < {nWords}u; {sn}_j++) \{"
              , s!"            uint32_t {sn}_lo = ({sn}_j + {sn}_k < {srcWords}u) ? {aS}[{sn}_j + {sn}_k] : 0u;"
              , s!"            uint32_t {sn}_hi = ({sn}_j + {sn}_k + 1 < {srcWords}u) ? {aS}[{sn}_j + {sn}_k + 1] : 0u;"
              , s!"            {sn}[{sn}_j] = {sn}_r ? (({sn}_lo >> {sn}_r) | ({sn}_hi << (32 - {sn}_r))) : {sn}_lo;"
              , s!"          }"
              , s!"        }" ]
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
      | .slice src _hi lo =>
        -- Wide slice `src[hi:lo]`: gather the destination words from the
        -- source array, shifting across word boundaries when `lo` is not
        -- 32-aligned, and masking the partial top word.  (This assignment
        -- shape was previously dropped by the `_ => empty` default — e.g.
        -- the `extractLsb' 0 256` that projects a 257-bit reduce result
        -- back to 256 bits, which silently produced 0.)
        let srcS := emitExpr typeMap src
        let srcWords := wordsOf (inferExprWidth typeMap src)
        let r := lo % 32
        let k := lo / 32
        let topBits := width % 32
        let lines := (List.range nWords).map fun j =>
          let idx := k + j
          let raw :=
            if r == 0 then
              if idx < srcWords then s!"{srcS}[{idx}]" else "0u"
            else
              let lowP := if idx < srcWords then s!"({srcS}[{idx}] >> {r})" else "0u"
              let hiP := if idx + 1 < srcWords then s!"({srcS}[{idx + 1}] << {32 - r})" else "0u"
              s!"({lowP} | {hiP})"
          if j == nWords - 1 && topBits != 0 then
            s!"        {sn}[{j}] = ({raw}) & {(1 <<< topBits) - 1}u;"
          else
            s!"        {sn}[{j}] = {raw};"
        { declarations := []
        , evalBody := lines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      | _ =>
        -- Fallback: attempt a whole-array memcpy from the emitted RHS.
        -- This is correct when `emitExpr` renders an array / compound
        -- literal, and a LOUD compile error (not a silent 0) otherwise —
        -- deliberately, so any remaining unhandled wide-assign shape
        -- surfaces instead of being dropped like the historical
        -- `StmtParts.empty` default did.
        let expr := emitExpr typeMap rhs
        { declarations := []
        , evalBody :=
            ["        /* wide assign fallback: unhandled RHS shape */",
             s!"        memcpy({sn}, {expr}, sizeof({sn}));"]
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      -- A wide value occupies whole 32-bit C words.  Canonicalize the
      -- partial top word after every assignment so padding bits can never
      -- become observable hardware state or feed a later operation.
      let topBits := width % 32
      if topBits == 0 then parts
      else
        let topMask := (1 <<< topBits) - 1
        { parts with
          evalBody := parts.evalBody ++
            [s!"        {sn}[{nWords - 1}] &= {topMask}u;"] }
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
      let nextTypeMap := typeMap.insert nextName (HWType.bitVector width)
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
    let rdInTypeMap := typeMap.fold (fun acc n _ => acc || sanitizeName n == rdName) false
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
-- Accumulator form — the `acc ++ recursive` version was O(nodes × depth)
-- on XiangShan-scale mux chains (see Optimize.collectExprRefsAux).
partial def collectExprRefsAux (acc : List String) : Expr → List String
  | .ref name => name :: acc
  | .const _ _ => acc
  | .slice inner _ _ => collectExprRefsAux acc inner
  | .sliceDim inner _ _ => collectExprRefsAux acc inner
  | .concat args => args.foldl collectExprRefsAux acc
  | .op _ args => args.foldl collectExprRefsAux acc
  | .index arr idx => collectExprRefsAux (collectExprRefsAux acc arr) idx

def collectExprRefs (e : Expr) : List String := collectExprRefsAux [] e

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

/-- Order the eval-relevant statements (assigns, instances, combo-read
    memories) topologically by def-use.  The lowering's `topoSortBody`
    sorts ASSIGNS only and appends instances last, so a parent's
    combinational logic that CONSUMES a child instance's outputs was
    emitted before the child's eval call and read stale values — a
    Mealy path through a sub-module (XiangShan CVT64: parent mantissa
    logic reads the Lzc child's `leadZeros` output).  Registers and
    non-combo memories contribute nothing to eval (they latch in tick),
    so they keep their original relative order at the end; on a
    combinational cycle the remaining statements fall back to source
    order (single-pass semantics, as before). -/
def scheduleEvalBody (design : Option Design) (m : Module)
    (body : List Stmt) : List Stmt := Id.run do
  let childOutputs : Stmt → List String := fun s => match s with
    | .inst modName _ conns =>
      match design.bind (·.findModule modName) with
      | some sm => conns.filterMap (fun (p, e) =>
          if sm.outputs.any (·.name == p) then
            match e with | .ref w => some w | _ => none
          else none)
      | none => []
    | _ => []
  let defsOf : Stmt → List String := fun s => match s with
    | .assign lhs _ => [lhs]
    | .memory _ _ _ _ _ _ _ _ rd cr => if cr then [rd] else []
    | .inst .. => childOutputs s
    | _ => []
  let usesOf : Stmt → List String := fun s => match s with
    | .assign _ rhs => collectExprRefs rhs
    | .memory _ _ _ _ _ _ _ ra _ cr => if cr then collectExprRefs ra else []
    | .inst modName _ conns =>
      let outs := childOutputs s
      match design.bind (·.findModule modName) with
      | some _ => conns.foldl (fun acc (_, e) =>
          acc ++ ((collectExprRefs e).filter (fun r => !outs.contains r))) []
      | none => conns.foldl (fun acc (_, e) => acc ++ collectExprRefs e) []
    | _ => []
  let schedulable : Stmt → Bool := fun s => match s with
    | .assign .. | .inst .. => true
    | .memory _ _ _ _ _ _ _ _ _ cr => cr
    | _ => false
  let (sched, rest) := body.partition schedulable
  -- Which names are produced by a schedulable statement?  Everything
  -- else (inputs, register outputs, latched memory reads) is state and
  -- always ready.
  let producedList := sched.flatMap defsOf
  let produced : Std.HashMap String Bool :=
    producedList.foldl (fun h n => h.insert n true) {}
  let mut done : Std.HashMap String Bool := {}
  let mut result : List Stmt := []
  let mut remaining := sched
  let mut fuel := sched.length + 1
  while !remaining.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let mut next : List Stmt := []
    let mut progressed := false
    for s in remaining do
      let ready := (usesOf s).all fun r =>
        !(produced.getD r false) || done.getD r false
      if ready then
        result := result ++ [s]
        for d in defsOf s do
          done := done.insert d true
        progressed := true
      else
        next := next ++ [s]
    remaining := next
    if !progressed then
      break
  -- cycle (or fuel-out): keep the rest in original order — same
  -- single-pass behaviour as before this pass existed.
  return result ++ remaining ++ rest

/-- Runtime helper for a DYNAMIC shift of a >64-bit value consumed in a
    ≤64-bit context (firtool's flattened packed-array dynamic select:
    `(_GEN >> (addr * 8)) & 0xff` with a multi-word `_GEN`): returns the
    64-bit window starting at bit `amt`.  Emitted (once, guarded) ahead
    of every module so nested wide shifts have a valid C rendering —
    the raw form `array >> amt` is not C at all. -/
def wideShrHelper (funcQual : String) : String :=
  let q := if funcQual.isEmpty then "" else funcQual ++ " "
  "#ifndef SPARKLE_WIDE_SHR64\n" ++
  "#define SPARKLE_WIDE_SHR64\n" ++
  q ++ "static inline uint64_t sparkle_wide_shr64(const uint32_t* a, unsigned words, unsigned amt) {\n" ++
  "    unsigned k = amt >> 5, r = amt & 31;\n" ++
  "    uint64_t w0 = (k < words) ? a[k] : 0u;\n" ++
  "    uint64_t w1 = (k + 1 < words) ? a[k + 1] : 0u;\n" ++
  "    uint64_t w2 = (k + 2 < words) ? a[k + 2] : 0u;\n" ++
  "    uint64_t lo = w0 | (w1 << 32);\n" ++
  "    return r ? ((lo >> r) | (w2 << (32 - r) << 32)) : lo;\n" ++
  "}\n" ++
  "#endif\n\n"


/-- Reject unspecialized parameterized IR at CSim module boundaries before
    concrete-width helpers can observe it.  Use the explicit specialization
    entry points below to emit one fixed-ABI C model for a chosen parameter
    configuration. -/
partial def exprHasSymbolicWidth : Expr → Bool
  | .sliceDim _ _ _ => true
  | .op _ args | .concat args => args.any exprHasSymbolicWidth
  | .slice expr _ _ => exprHasSymbolicWidth expr
  | .index array index => exprHasSymbolicWidth array || exprHasSymbolicWidth index
  | _ => false

def moduleHasSymbolicWidth (m : Module) : Bool :=
  !m.parameters.isEmpty ||
  (m.inputs ++ m.outputs ++ m.wires).any (fun port => port.ty.bitWidth?.isNone) ||
  m.body.any fun stmt => match stmt with
    | .assign _ rhs => exprHasSymbolicWidth rhs
    | .register _ _ _ input _ => exprHasSymbolicWidth input
    | .memory _ _ _ _ wa wd we ra _ _ =>
        exprHasSymbolicWidth wa || exprHasSymbolicWidth wd ||
        exprHasSymbolicWidth we || exprHasSymbolicWidth ra
    | .inst _ _ connections => connections.any (exprHasSymbolicWidth ·.2)

def unsupportedSymbolicWidthError : String :=
  "#error \"Sparkle CSim requires concrete widths; specialize retained parameters before emission\"\n"

/-- Emit a complete C struct + static helpers for a module.
    Returns the full C source fragment (no includes; callers
    add those at design level). -/
def emitModule (m : Module) (design : Option Design := none)
    (observableWires : Option (List String) := none)
    (funcQual : String := "") : String :=
  if moduleHasSymbolicWidth m then
    unsupportedSymbolicWidthError
  else if m.isPrimitive then
    s!"/* Primitive module: {m.name} */\n/* (blackbox - not generated) */\n\n"
  else
    let typeMap := buildTypeMap m
    let className := sanitizeName m.name

    let filteredBody := m.body.filter fun s => match s with
      | .assign lhs (.ref name) => lhs != name
      | _ => true
    let filteredBody := scheduleEvalBody design m filteredBody
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

    -- Callers write the fixed-ABI C storage rather than a native BitVec.
    -- Normalize every packed input before evaluating logic so padding in a
    -- uint8/16/32/64 scalar, or in the last word of a wide value, can never
    -- participate in shifts or comparisons as if it were a hardware bit.
    let inputMaskBody := m.inputs.filterMap fun (p : Port) =>
      match p.ty with
      | .bit =>
        some s!"        {sanitizeName p.name} &= 1u;"
      | .bitVector width =>
        if width == 0 then none
        else if width ≤ 64 then
          let mask := emitMask width
          if mask.isEmpty then none
          else some s!"        {sanitizeName p.name} &= {mask};"
        else
          let topBits := width % 32
          if topBits != 0 then
            let topMask := (1 <<< topBits) - 1
            some s!"        {sanitizeName p.name}[{wordsOf width - 1}] &= {topMask}u;"
          else none
      | _ => none
    let evalBody := inputMaskBody ++
      allParts.foldl (fun acc (p : StmtParts) => acc ++ p.evalBody) []
    let tickBody := allParts.foldl (fun acc (p : StmtParts) => acc ++ p.tickBody) []
    let resetBody := allParts.foldl (fun acc (p : StmtParts) => acc ++ p.resetBody) []
    let evalTickLocals := allParts.foldl (fun acc (p : StmtParts) => acc ++ p.evalTickLocals) []

    let structName := s!"struct {className}"
    let helperPrefix := wideShrHelper funcQual

    let inputSection := if inputDecls.isEmpty then "" else
      "    /* Input ports */\n" ++ String.intercalate "\n" inputDecls ++ "\n\n"
    let outputSection := if outputDecls.isEmpty then "" else
      "    /* Output ports */\n" ++ String.intercalate "\n" outputDecls ++ "\n\n"
    let wireSection := if wireDecls.isEmpty then "" else
      "    /* Internal wires */\n" ++ String.intercalate "\n" wireDecls ++ "\n\n"
    let stmtDeclSection := if stmtDecls.isEmpty then "" else
      "    /* Registers, memories, sub-instances */\n" ++ String.intercalate "\n" stmtDecls ++ "\n\n"

    let structDecl :=
      helperPrefix ++
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

    let qualifyWith (memberSet : Std.HashSet String) (input : String) : String := Id.run do
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
      -- Accumulate into an `Array Char` (O(1) amortised push) instead of
      -- `out := out ++ …` on a `String` — Lean's `String.append`/`push`
      -- reallocates each time, making the old loop O(lineLen²).  Emitted
      -- C lines can be very long (a wide-op eval line), so this keeps
      -- qualification linear in the emitted source size.
      let mut out : Array Char := #[]
      let mut buf : String := ""
      let mut prevC : Char := ' '
      let mut skipNext : Bool := false
      let pushStr (a : Array Char) (s : String) : Array Char := Id.run do
        let mut a := a
        for ch in s.toList do a := a.push ch
        return a
      for c in input.toList do
        if isTokChar c then
          buf := buf.push c
        else
          if !buf.isEmpty then
            if !skipNext && memberSet.contains buf then
              out := pushStr out "self->"
            out := pushStr out buf
            buf := ""
          out := out.push c
          -- Update next-token skip state: skip if this delimiter is `.`
          -- or if the last two chars formed `->`.
          skipNext :=
            c == '.' || (c == '>' && prevC == '-')
          prevC := c
      if !buf.isEmpty then
        if !skipNext && memberSet.contains buf then
          out := pushStr out "self->"
        out := pushStr out buf
      return String.mk out.toList

    let qualify := qualifyWith memberSet
    let evalBodyQ := evalBody.map qualify
    let tickBodyQ := tickBody.map qualify
    let resetBodyQ := resetBody.map qualify

    -- For the FUSED eval_tick, register `_next` temporaries never need
    -- to persist across calls (eval writes them and tick reads them in
    -- the SAME function), so keep them as stack LOCALS instead of
    -- struct fields — one store+reload per register per tick removed.
    -- `evalTickLocals` already carries their `T name = self_reg;`
    -- declarations; we just drop the `_next` names from the qualified
    -- member set so they emit bare.  (The separate eval()/tick() path
    -- still uses the full member set, where `_next` must persist.)
    let regNextSet : Std.HashSet String :=
      (m.body.filterMap (fun s => match s with
        | .register o .. => some (sanitizeName o ++ "_next") | _ => none)).foldl
        (fun s n => s.insert n) ({} : Std.HashSet String)
    let memberSetET : Std.HashSet String :=
      memberSet.fold (fun s n => if regNextSet.contains n then s else s.insert n)
        ({} : Std.HashSet String)
    let qualifyET := qualifyWith memberSetET

    let resetFn :=
      s!"{funcQual}static void sparkle_{className}_reset({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if resetBodyQ.isEmpty then "" else
        String.intercalate "\n" resetBodyQ ++ "\n") ++
      "}\n\n"

    let evalFn :=
      s!"{funcQual}static void sparkle_{className}_eval({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if localWireDecls.isEmpty then "" else
        String.intercalate "\n" localWireDecls ++ "\n") ++
      (if evalBodyQ.isEmpty then "" else
        String.intercalate "\n" evalBodyQ ++ "\n") ++
      "}\n\n"

    let tickFn :=
      s!"{funcQual}static void sparkle_{className}_tick({structName}* self) \{\n" ++
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

    -- eval_tick uses the reduced member set so register `_next`
    -- temporaries emit as bare locals (declared via evalTickLocals).
    let evalTickEvalBody := (evalBody.map qualifyET).map fun line =>
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
    let evalTickTickBody := (tickBody.map qualifyET).filter fun line =>
      !instNames.any (fun inst =>
        (line.splitOn s!"sparkle_evalTick_placeholder_TICK_{inst}").length > 1
        || (line.splitOn s!"_tick(&self->{inst})").length > 1)

    let evalTickFn :=
      s!"{funcQual}static void sparkle_{className}_eval_tick({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if localWireDecls.isEmpty then "" else
        String.intercalate "\n" localWireDecls ++ "\n") ++
      -- Stack-local register `_next` temporaries (pre-init from the
      -- current register value to preserve non-blocking semantics).
      -- Qualified so the `_next` LHS stays bare (local) while the
      -- initialising register read becomes `self->reg`.
      (if evalTickLocals.isEmpty then "" else
        String.intercalate "\n" (evalTickLocals.map qualifyET) ++ "\n") ++
      (if evalTickEvalBody.isEmpty then "" else
        String.intercalate "\n" evalTickEvalBody ++ "\n") ++
      (if evalTickTickBody.isEmpty then "" else
        String.intercalate "\n" evalTickTickBody ++ "\n") ++
      "}\n\n"

    structDecl ++ resetFn ++ evalFn ++ tickFn ++ evalTickFn

/-- Convert a full design to C simulation code (no JIT wrapper) -/
def toCDesign (d : Design)
    (observableWires : Option (List String) := none)
    (funcQual : String := "") : String :=
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
    if m.name == topName then emitModule m (some d) observableWires funcQual
    else emitModule m (some d) none funcQual
  header ++ String.intercalate "\n" code

/-- Specialize retained dimensions for one explicit configuration, then emit
    a fixed-ABI C model for the whole design. -/
def toCDesignWithParameters (d : Design)
    (bindings : Sparkle.IR.Specialize.Bindings)
    (observableWires : Option (List String) := none)
    (funcQual : String := "") : Except String String := do
  let concrete ← Sparkle.IR.Specialize.specializeDesign d bindings
  return toCDesign concrete observableWires funcQual

/-- Convert a single module to C simulation code with includes -/
def toC (m : Module) : String :=
  let includes :=
    "#include <stdint.h>\n" ++
    "#include <stdlib.h>\n" ++
    "#include <string.h>\n\n"
  includes ++ emitModule m

/-- Specialize retained dimensions for one explicit configuration, then emit
    a fixed-ABI C model for a single module. -/
def toCWithParameters (m : Module)
    (bindings : Sparkle.IR.Specialize.Bindings) : Except String String := do
  let concrete ← Sparkle.IR.Specialize.specializeModule m bindings
  return toC concrete

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
private def collectRegisters (body : List Stmt) (typeMap : TypeMap)
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
  -- Wide (>64-bit) input ports are split into `wordsOf w` consecutive
  -- 32-bit slots, exactly mirroring `emitGetOutputSwitch` on the output
  -- side.  Each slot is written by its own `set_input` index with the
  -- low 32 bits of `val`, so a caller drives a 256-bit port with 8
  -- successive `setInput`s.  Without this, wide inputs (e.g. a 256-bit
  -- operand-load port) silently kept only their least-significant word.
  let cases := userInputs.foldl (fun (acc : List String × Nat) (p : Port) =>
    let sName := sanitizeName p.name
    let w := p.ty.bitWidth
    if w > 64 then
      let nWords := wordsOf w
      let wordCases := List.range nWords |>.map fun j =>
        s!"        case {acc.2 + j}: s->{sName}[{j}] = (uint32_t)val; break;"
      (acc.1 ++ wordCases, acc.2 + nWords)
    else
      let cType := emitScalarBase p.ty
      (acc.1 ++ [s!"        case {acc.2}: s->{sName} = ({cType})val; break;"], acc.2 + 1)
  ) ([], 0)
  String.intercalate "\n" cases.1

/-- Number of `set_input` slots a design's user inputs occupy (wide ports
    take `wordsOf w` slots each) — the mirror of `countOutputSlots`. -/
private def countInputSlots (inputs : List Port) : Nat :=
  (inputs.filter (fun p => p.name != "clk")).foldl (fun acc p =>
    let w := p.ty.bitWidth
    if w > 64 then acc + wordsOf w else acc + 1) 0

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
private def toCJITUnchecked (d : Design)
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
      -- Keep `_gen_*` wires (named let-bindings / FSM-state signals)
      -- as struct members so `jit_get_wire` can still read them at
      -- runtime — some drivers sample internal state like
      -- `_gen_phase` / `_gen_done` (e.g. the H.264 encoders).  Only
      -- the anonymous `_tmp_*` combinational intermediates and the
      -- register `_next` temporaries get localised.
      let genWires := m.wires.filterMap fun (w : Port) =>
        let sn := sanitizeName w.name
        if sn.startsWith "_gen_" then some sn else none
      some (tickRefs ++ genWires ++ extra)
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


def toCJIT (d : Design)
    (observableWires : Option (List String) := none) : String :=
  if d.modules.any moduleHasSymbolicWidth then
    unsupportedSymbolicWidthError
  else
    toCJITUnchecked d observableWires

/-- Specialize retained dimensions for one explicit configuration, then emit
    the fixed-ABI C JIT wrapper. -/
def toCJITWithParameters (d : Design)
    (bindings : Sparkle.IR.Specialize.Bindings)
    (observableWires : Option (List String) := none) : Except String String := do
  let concrete ← Sparkle.IR.Specialize.specializeDesign d bindings
  return toCJIT concrete observableWires
end Sparkle.Backend.CSim
