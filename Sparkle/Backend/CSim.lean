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
  -- Memories are declared by `Stmt.memory`, not by a wire, so without
  -- this they were absent from the map and `inferExprWidth` fell back to
  -- 32 for `Memory[addr]`.  A wide memory's row then looked NARROW, and
  -- a masked read-modify-write on it took the scalar path and emitted
  -- `array & array` (invalid C).  Register the array type so row reads
  -- infer the element width.
  let memEntries := m.body.filterMap fun st => match st with
    | .memory name aw dw _ _ _ _ _ _ _ _ _ =>
      some (name, HWType.array (2 ^ aw) (.bitVector dw))
    | _ => none
  (entries ++ memEntries).foldl (fun acc (n, t) => acc.insertIfNew n t) {}

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

/-- Does every value of `e` fit in `w` bits?  `exprIsMasked` takes a `.ref`
    (and a right shift) as already masked, which is true of the
    reference's OWN width only.  IR lowered from Verilog truncates
    implicitly: PicoRV32's 5-bit `reg_sh <= cpuregs_rs2` stores a 32-bit
    wire, and with every arm of the chain a `.ref` no mask was emitted at
    all, leaving bits 5-7 of the uint8 container set. -/
partial def exprFits (typeMap : TypeMap) (w : Nat) : Expr → Bool
  | .ref n => lookupWidth typeMap n ≤ w
  | .op .mux [_, t, e] => exprFits typeMap w t && exprFits typeMap w e
  | .op .and [a, b] => exprFits typeMap w a || exprFits typeMap w b
  | .op .or [a, b] | .op .xor [a, b] => exprFits typeMap w a && exprFits typeMap w b
  | .op .shr [a, _] | .op .asr [a, _] => exprFits typeMap w a
  | _ => true

/-- May `e` be stored into a `w`-bit scalar without a mask? -/
def storeIsMasked (typeMap : TypeMap) (w : Nat) (e : Expr) : Bool :=
  exprIsMasked w e && exprFits typeMap w e

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
  -- A left shift by a constant grows the value: `x << k` needs
  -- `width(x) + k` bits.  Inferring it as `width(x)` (first operand
  -- only) truncated firtool's byte-lane writes — lane 4 of a 128-bit
  -- SRAM is `(wdata >> 16) << 48`, computed in a uint64 scalar, so
  -- every bit destined for words 2-3 was silently dropped.
  | .op .shl [a, .const k _] =>
    inferExprWidth typeMap a + (if k ≥ 0 then k.toNat else 0)
  | .op _ args =>
    match args with
    -- A binary op is as wide as its WIDEST operand — taking only the
    -- first one inferred `(wdata & 16'hffff) & <128-bit mux>` as 16 bits,
    -- so the wide emitter sent it down the scalar uint64 path and
    -- produced `uint64 & uint32_t*` (invalid C) on firtool's masked
    -- read-modify-write SRAMs.
    | [arg1, arg2] => max (inferExprWidth typeMap arg1) (inferExprWidth typeMap arg2)
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
private def wideAddSubExpr (isAdd : Bool) (a b : String) (nWords : Nat)
    (aWide bWide : Bool := true) : String :=
  -- Each operand must be reachable as an indexable word array.
  -- `(uint64_t)(x)[i]` casts BEFORE subscripting, so `[i]` was applied to
  -- a scalar; and a compound-literal operand (wide const / concat /
  -- nested wide op) is not an lvalue to subscript at all — GCC rejects
  -- both.  Bind a wide operand to a `const uint32_t *`, and BOX a narrow
  -- one into a zero-extended word array (XiangShan's CSA tree subtracts
  -- a 1-bit borrow from a 128-bit partial product).
  let boxOf (nm src : String) (wide : Bool) : String :=
    if wide then s!"const uint32_t *{nm} = (const uint32_t *)({src}); "
    else
      s!"uint32_t {nm}_b[{nWords}] = \{0}; \{ uint64_t {nm}_v = (uint64_t)({src}); " ++
      s!"{nm}_b[0] = (uint32_t){nm}_v;" ++
      (if nWords > 1 then s!" {nm}_b[1] = (uint32_t)({nm}_v >> 32);" else "") ++
      s!" } const uint32_t *{nm} = {nm}_b; "
  let binds := boxOf "__wa" a aWide ++ boxOf "__wb" b bWide
  let words := (List.range nWords).map (fun i =>
    let ai := "(uint64_t)__wa[" ++ toString i ++ "]"
    let bi := "(uint64_t)__wb[" ++ toString i ++ "]"
    if isAdd then
      "uint64_t __s" ++ toString i ++ " = " ++ ai ++ " + " ++ bi ++
        " + __c; __c = __s" ++ toString i ++ " >> 32;"
    else
      "int64_t __s" ++ toString i ++ " = (int64_t)" ++ ai ++ " - (int64_t)" ++ bi ++
        " - (int64_t)__c; __c = (__s" ++ toString i ++ " < 0) ? 1 : 0;")
  let elems := String.intercalate ", "
    ((List.range nWords).map (fun i => "(uint32_t)__s" ++ toString i))
  let body := binds ++ "uint64_t __c = 0; " ++ String.intercalate " " words ++
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

/-- Emit the lines of a wide ARITHMETIC shift right into `dst`:
    a sign-extended copy of the source feeds a word-window loop, so words
    beyond the top read the sign fill.  Wide `.op .asr` previously had NO
    wide arm at all — it fell through to the scalar emitter, which cast
    the operand array to `int64_t` (a pointer) and shifted THAT
    (SRT16Divint's remainder alignment). -/
private def wideAsrInto (dst aS bS : String) (nWords srcWords srcW : Nat) : List String :=
  let topBit := (srcW - 1) % 32
  [ s!"        \{ uint32_t {dst}_sf = (({aS}[{srcWords - 1}] >> {topBit}) & 1u) ? 0xFFFFFFFFu : 0u;"
  , s!"          uint32_t {dst}_ext[{srcWords}];"
  , s!"          for (unsigned {dst}_i = 0; {dst}_i < {srcWords}u; {dst}_i++) {dst}_ext[{dst}_i] = {aS}[{dst}_i];"
  ] ++
  (if topBit < 31 then
    [ s!"          if ({dst}_sf) {dst}_ext[{srcWords - 1}] |= ~((1u << {topBit + 1}) - 1u);" ]
   else []) ++
  [ s!"          unsigned {dst}_sa = (unsigned)({bS}); unsigned {dst}_k = {dst}_sa >> 5, {dst}_r = {dst}_sa & 31;"
  , s!"          for (unsigned {dst}_j = 0; {dst}_j < {nWords}u; {dst}_j++) \{"
  , s!"            uint32_t {dst}_lo = ({dst}_j + {dst}_k < {srcWords}u) ? {dst}_ext[{dst}_j + {dst}_k] : {dst}_sf;"
  , s!"            uint32_t {dst}_hi = ({dst}_j + {dst}_k + 1 < {srcWords}u) ? {dst}_ext[{dst}_j + {dst}_k + 1] : {dst}_sf;"
  , s!"            {dst}[{dst}_j] = {dst}_r ? (({dst}_lo >> {dst}_r) | ({dst}_hi << (32 - {dst}_r))) : {dst}_lo;"
  , s!"          }"
  , s!"        }" ]

/-- Same nested-ternary compare, but over caller-supplied per-word slot
    expressions, so a NARROW operand can present zero-extended words
    instead of being subscripted. -/
private def wideCmpSlots (strict : Bool) (a b : Nat → String) (nWords : Nat) : String :=
  let base := if strict then "0" else "1"
  let expr := (List.range nWords).foldl (fun rest i =>
    "(" ++ a i ++ " < " ++ b i ++ " ? 1 : (" ++ a i ++ " > " ++ b i ++ " ? 0 : " ++ rest ++ "))")
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
                  -- A wide `.slice` has NO inline C rendering, so
                  -- `emitExpr` on it used to hand back the BASE with the
                  -- offset silently dropped — `{car[106:1], b}` became
                  -- `(car << 1) | b`, off by one bit through the whole
                  -- vector (VectorFloatFMA's CSA input, a 1-LSB FMA
                  -- rounding error three pipeline stages later).  Fold
                  -- the slice's own offset into the bit index and read
                  -- the base directly.
                  let (arg, argExpr, bitInArgLo) := match arg with
                    | .slice base _ slo =>
                      if inferExprWidth typeMap base > 64 then
                        (base, emitExpr typeMap base, bitInArgLo + slo)
                      else (arg, argExpr, bitInArgLo)
                    | _ => (arg, argExpr, bitInArgLo)
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
        -- sliceWidth > 64: there is no inline C form.  `lo == 0` is a
        -- plain truncation (word-count handled by the consumer), but a
        -- non-zero offset CANNOT be expressed here — returning the base
        -- silently dropped it.  Emit a loud non-compiling token instead;
        -- consumers that can handle this shape (matWide, the concat slot
        -- builder, wideConnLines) all materialise it themselves first.
        if lo == 0 then emitExpr typeMap e
        else s!"SPARKLE_WIDE_SLICE_OFFSET_DROPPED_{lo}"
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
          -- Verilog zero-extends the NARROWER operand of an equality, so
          -- a ≤64-bit side is a C scalar and cannot be indexed `[j]`:
          -- word 0 is its low half, word 1 its high half, and every word
          -- above that is zero.  (RasStack compares a wide hoisted cone
          -- against a 64-bit input; the old code subscripted the input.)
          let slot (e : Expr) (j : Nat) : String :=
            let we := inferExprWidth typeMap e
            let es := emitExpr typeMap e
            if we > 64 then s!"{es}[{j}]"
            else if j == 0 then s!"((uint32_t)({es}))"
            else if j == 1 && we > 32 then s!"((uint32_t)((uint64_t)({es}) >> 32))"
            else "0u"
          let mkTerms (x y : Expr) : String :=
            match y with
            | .const 0 _ =>
              String.intercalate " && " ((List.range n).map (fun j => s!"({slot x j} == 0)"))
            | _ =>
              String.intercalate " && " ((List.range n).map (fun j => s!"({slot x j} == {slot y j})"))
          match arg1, arg2 with
          | _, .const 0 _ => s!"(({mkTerms arg1 arg2}) ? 1 : 0)"
          | .const 0 _, _ => s!"(({mkTerms arg2 arg1}) ? 1 : 0)"
          | _, _          => s!"(({mkTerms arg1 arg2}) ? 1 : 0)"
        else
        -- `{a, b, c, …} == 0` is `(a | b | c | …) == 0`: no need to shift
        -- every part into its position first.  PicoRV32's `instr_trap`
        -- (`!{instr_lui, instr_auipc, …}`, 48 one-bit parts) was 10 % of
        -- the instructions LiteX executes per cycle.
        let zeroTest (x : Expr) : String :=
          match x with
          | .concat parts =>
            let terms := parts.filterMap fun part =>
              let pw := inferExprWidth typeMap part
              if pw == 0 then none
              else
                let ps := emitExpr typeMap part
                -- Only a value that is canonical AS AN EXPRESSION may go
                -- unmasked (there is no store to truncate it here).
                let canonical := match part with
                  | .ref n => lookupWidth typeMap n ≤ pw
                  | .const _ _ | .slice _ _ _ => true
                  | .op .eq _ | .op .lt_u _ | .op .lt_s _ | .op .le_u _
                  | .op .le_s _ | .op .gt_u _ | .op .gt_s _ | .op .ge_u _
                  | .op .ge_s _ => true
                  | _ => false
                some (if canonical || pw ≥ 64 then ps
                  else s!"((uint64_t)({ps}) & 0x{String.ofList (Nat.toDigits 16 (2 ^ pw - 1))}ULL)")
            if terms.length < 2 then s!"(!({emitExpr typeMap x}) ? 1 : 0)"
            else s!"(!({String.intercalate " | " terms}) ? 1 : 0)"
          | _ => s!"(!({emitExpr typeMap x}) ? 1 : 0)"
        match arg1, arg2 with
        | _, .const 0 _ => zeroTest arg1
        | .const 0 _, _ => zeroTest arg2
        | _, _ => s!"({emitExpr typeMap arg1} == {emitExpr typeMap arg2} ? 1 : 0)"
      | .lt_u | .le_u | .gt_u | .ge_u =>
        let w := max (inferExprWidth typeMap arg1) (inferExprWidth typeMap arg2)
        if w > 64 then
          -- Like the eq arm: Verilog zero-extends the NARROWER operand,
          -- so a ≤64-bit side is a C scalar — word 0 its low half,
          -- word 1 its high half, zero above (StreamBitVectorArray
          -- compares an 8-bit constant against a wide cone; the old code
          -- subscripted the constant).
          let slotOf (e : Expr) : Nat → String := fun j =>
            let we := inferExprWidth typeMap e
            let es := emitExpr typeMap e
            if we > 64 then s!"(uint32_t)({es})[{j}]"
            else if j == 0 then s!"((uint32_t)({es}))"
            else if j == 1 && we > 32 then s!"((uint32_t)((uint64_t)({es}) >> 32))"
            else "0u"
          let a := slotOf arg1
          let b := slotOf arg2
          let n := wordsOf w
          -- a≥b ⟺ b≤a ; a>b ⟺ b<a — reuse the (strict) le/lt form by
          -- swapping operands for the ≥/> cases.
          match operator with
          | .lt_u => wideCmpSlots true  a b n
          | .le_u => wideCmpSlots false a b n
          | .gt_u => wideCmpSlots true  b a n
          | _     => wideCmpSlots false b a n   -- .ge_u
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
          -- `(uint64_t)(x)[0]` casts BEFORE subscripting, so `[0]` was
          -- applied to a scalar; and when the operand is itself a
          -- compound literal (a wide const, concat or nested wide op)
          -- the subscript has no array to bind to at all — GCC rejects
          -- it outright.  Bind each wide operand to a local `const
          -- uint32_t *` first, then index THAT.
          let lhsBind := if w1 > 64 then s!"const uint32_t *__ml = (const uint32_t *)({lhsExpr}); " else ""
          let rhsBind := if w2 > 64 then s!"const uint32_t *__mr = (const uint32_t *)({rhsExpr}); " else ""
          let lhsLo64 :=
            if w1 > 64 then "((uint64_t)__ml[0] | ((uint64_t)__ml[1] << 32))"
            else s!"((uint64_t)({lhsExpr}))"
          let rhsLo64 :=
            if w2 > 64 then "((uint64_t)__mr[0] | ((uint64_t)__mr[1] << 32))"
            else s!"((uint64_t)({rhsExpr}))"
          -- The wide-mul value is consumed by `emitStmt`'s
          -- `.op .mul` arm which generates a slot-by-slot
          -- assign, so we expose the three slot expressions
          -- as a marker the assign-side recognises.  Here we
          -- emit a statement-expression that returns a
          -- compound-literal array; this is only used by
          -- `memcpy`-style wide assigns.
          let body :=
            s!"\{ {lhsBind}{rhsBind}__int128 __p = (__int128)(int64_t){lhsLo64} * (__int128)(int64_t){rhsLo64};" ++
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
          (inferExprWidth typeMap arg1 > 64) (inferExprWidth typeMap arg2 > 64)
        else s!"({emitExpr typeMap arg1} + {emitExpr typeMap arg2})"
      | .sub =>
        let w := max (inferExprWidth typeMap arg1) (inferExprWidth typeMap arg2)
        if w > 64 then wideAddSubExpr false (emitExpr typeMap arg1) (emitExpr typeMap arg2) (wordsOf w)
          (inferExprWidth typeMap arg1 > 64) (inferExprWidth typeMap arg2 > 64)
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
  /-- A scalar register only: the lines that update it IN PLACE
      (`reg = …`, nothing when it holds), for the fused eval_tick when no
      later statement still needs its old value. -/
  inPlace         : Option (Unit → List String) := none
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

/-- Is `e` rendered as a C value that is exactly 0 or 1?  Only then may a
    bitwise `a & b` used as a condition be evaluated as `a && b`. -/
private partial def isCBool (typeMap : TypeMap) : Expr → Bool
  | .const v 1 => v == 0 || v == 1
  | .ref n => lookupWidth typeMap n == 1
  | .slice e hi lo => hi == lo && inferExprWidth typeMap e ≤ 64
  | .op .eq _ | .op .lt_u _ | .op .lt_s _ | .op .le_u _
  | .op .le_s _ | .op .gt_u _ | .op .gt_s _ | .op .ge_u _
  | .op .ge_s _ => true
  | .op .not [a] => inferExprWidth typeMap a ≤ 1
  | .op .and [a, b] | .op .or [a, b] => isCBool typeMap a && isCBool typeMap b
  | _ => false

/-- The conjuncts of a condition, outermost guard first.  `a & b` is split
    only when both sides are C booleans. -/
private partial def condConjuncts (typeMap : TypeMap) : Expr → List Expr
  | .op .and [a, b] =>
    if isCBool typeMap a && isCBool typeMap b then
      condConjuncts typeMap a ++ condConjuncts typeMap b
    else [.op .and [a, b]]
  | e => [e]

/-- The constants of an OR of `x == c` tests on one `x`, if `e` is one. -/
private partial def eqConstLeaves : Expr → Option (Expr × List Int)
  | .op .eq [x, .const c _] => if c ≥ 0 then some (x, [c]) else none
  | .op .or [a, b] =>
    match eqConstLeaves a, eqConstLeaves b with
    | some (x, cs), some (y, ds) => if x == y then some (x, cs ++ ds) else none
    | _, _ => none
  | _ => none

/-- Drop the conjuncts another conjunct already implies.  A `case` arm is
    lowered as "none of the earlier labels, and this label":
    `!(s == A | s == B | …) && s == C`.  With `s == C` in the same
    conjunction and `C` different from every earlier label the negation
    is always true; on a one-hot state register it was the larger half
    of every arm's test. -/
private def dropImpliedConjuncts (cs : List Expr) : List Expr :=
  let eqs : List (Expr × Int) := cs.filterMap fun c => match c with
    | .op .eq [x, .const k _] => if k ≥ 0 then some (x, k) else none
    | _ => none
  if eqs.isEmpty then cs
  else cs.filter fun c => match c with
    | .op .not [d] =>
      match eqConstLeaves d with
      | some (x, ks) => !(eqs.any fun (y, k) => y == x && !ks.contains k)
      | none => true
    | _ => true

/- Lines of a priority chain as a short-circuit decision tree.

    A chain `c1 ? v1 : c2 ? v2 : … : d` whose conditions are path guards
    (`resetn & state == S & …`, one conjunction per source branch) costs,
    as one C expression, every guard and every value on every cycle.
    Here consecutive arms that share their leading conjunct are grouped
    under one `if`, the remaining conjuncts are tested with `&&`, and a
    value is computed only in the arm that is taken:

        do {
          if (g) {
            if (a && b) { x = v1; break; }
            if (c)      { x = v2; break; }
          }
          if (h) { x = v3; break; }
          x = d;
        } while (0);

    The arms are tried in the chain's own order and a group whose inner
    arms all miss falls through to the arms after it, so the first arm
    whose full condition holds is the one taken — exactly the chain. -/
mutual
/-- `lhs = e;` — as a nested decision tree when `e` is itself a chain. -/
private partial def muxAssignLines (typeMap : TypeMap) (lhsName : String)
    (maskFn : Expr → String) (hold : Option String) (indent : String) (e : Expr) : List String :=
  let (arms, default_) := flattenMuxChain e
  if arms.isEmpty then
    -- `hold`: the target already has this value (an in-place register
    -- keeping its state), so there is nothing to store.
    if hold.isSome && e == .ref (hold.getD "") then []
    else [s!"{indent}{lhsName} = {maskFn e};"]
  else
    [s!"{indent}do \{"] ++
      muxTreeLines typeMap lhsName maskFn hold (indent ++ "  ")
        (arms.map fun (c, v) => (dropImpliedConjuncts (condConjuncts typeMap c), v)) ++
      muxAssignLines typeMap lhsName maskFn hold (indent ++ "  ") default_ ++
      [s!"{indent}} while (0);"]

private partial def muxTreeLines (typeMap : TypeMap) (lhsName : String)
    (maskFn : Expr → String) (hold : Option String) (indent : String)
    (arms : List (List Expr × Expr)) : List String :=
  -- the taken arm: assign (its value may be a chain of its own), then leave
  let take (ind : String) (v : Expr) : Sum String (List String) :=
    if (flattenMuxChain v).1.isEmpty then
      if hold.isSome && v == .ref (hold.getD "") then .inl "break;"
      else .inl s!"{lhsName} = {maskFn v}; break;"
    else
      .inr (muxAssignLines typeMap lhsName maskFn hold (ind ++ "  ") v ++ [s!"{ind}  break;"])
  match arms with
  | [] => []
  | ([], v) :: _ =>
    match take indent v with
    | .inl one => [s!"{indent}{one}"]
    | .inr ls => [s!"{indent}\{"] ++ ls ++ [s!"{indent}}"]
  | (p :: ps, v) :: rest =>
    let run := (arms.takeWhile fun (c, _) => c.head? == some p)
    let others := arms.drop run.length
    if run.length ≤ 1 then
      let cond := String.intercalate " && " ((p :: ps).map (emitExpr typeMap))
      (match take indent v with
        | .inl one => [s!"{indent}if ({cond}) \{ {one} }"]
        | .inr ls => [s!"{indent}if ({cond}) \{"] ++ ls ++ [s!"{indent}}"]) ++
        muxTreeLines typeMap lhsName maskFn hold indent rest
    else
      [s!"{indent}if ({emitExpr typeMap p}) \{"] ++
        muxTreeLines typeMap lhsName maskFn hold (indent ++ "  ") (run.map fun (c, v) => (c.drop 1, v)) ++
        [s!"{indent}}"] ++
        muxTreeLines typeMap lhsName maskFn hold indent others
end

/-- Emit `lhs = <mux chain>` as a decision tree; `[]` when `rhs` is not a
    mux.  Every chain goes this way, down to a single arm: on LiteX each
    step of the threshold from 16 arms to 1 lowered both the instructions
    executed and the run time (3364 / 3134 / 2936 / 2787 per cycle at
    8 / 4 / 2 / 1). -/
def emitMuxAsTree (typeMap : TypeMap)
    (lhsName : String) (width : Nat) (rhs : Expr) : List String :=
  if (flattenMuxChain rhs).1.isEmpty then []
  else
    let maskFn := fun (e : Expr) =>
      let s := emitExpr typeMap e
      if storeIsMasked typeMap width e then s else applyMask s width
    muxAssignLines typeMap lhsName maskFn none "        " rhs

/-- `reg = input` updating the register in place: a decision tree when the
    input is a chain, no store at all on the paths where it holds. -/
def emitRegInPlace (typeMap : TypeMap)
    (regName : String) (cName : String) (width : Nat) (input : Expr) : List String :=
  let maskFn := fun (e : Expr) =>
    let s := emitExpr typeMap e
    if storeIsMasked typeMap width e then s else applyMask s width
  muxAssignLines typeMap cName maskFn (some regName) "        " input

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
        | .index _ _ =>
          -- `Memory[addr]` on a wide memory IS an indexable uint32 row —
          -- exactly like a `.ref` to a wide wire — so it needs no temp.
          -- Without this arm, a masked read-modify-write on a wide
          -- memory (firtool's byte-enable SRAMs) fell through to the
          -- generic memcpy arm and emitted `array & array`.
          ([], emitExpr typeMap e)
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
            let bS :=
              -- A WIDE dynamic shift amount is an array; casting it to
              -- unsigned takes the POINTER (TIMER's `128'h1 << {121'h0,
              -- addr…}` shifted by garbage).  Read its low word instead
              -- — amounts ≥ 2^32 are already out of range.
              if inferExprWidth typeMap b > 64 then s!"{emitExpr typeMap b}[0]"
              else emitExpr typeMap b
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
            let bS :=
              -- A WIDE dynamic shift amount is an array; casting it to
              -- unsigned takes the POINTER (TIMER's `128'h1 << {121'h0,
              -- addr…}` shifted by garbage).  Read its low word instead
              -- — amounts ≥ 2^32 are already out of range.
              if inferExprWidth typeMap b > 64 then s!"{emitExpr typeMap b}[0]"
              else emitExpr typeMap b
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
        | .op .asr [a, b] =>
          let (da, aS) := matWide s!"{label}s" a
          let tmp := s!"__{label}_{sn}"
          let srcW := inferExprWidth typeMap a
          let bS :=
            if inferExprWidth typeMap b > 64 then s!"{emitExpr typeMap b}[0]"
            else emitExpr typeMap b
          (da ++ (s!"        uint32_t {tmp}[{nWords}];"
            :: wideAsrInto tmp aS bS nWords (wordsOf srcW) srcW), tmp)
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
          -- Same narrower-than-destination hazard as the top-level concat
          -- arm: copy only the concat's OWN words and zero the rest.
          let cw := cargs.foldl (fun acc a => acc + inferExprWidth typeMap a) 0
          let copyWords := min (wordsOf cw) nWords
          (ds ++ [s!"        uint32_t {tmp}[{nWords}] = \{0}; memcpy({tmp}, {emitExpr typeMap' (.concat cargs')}, {copyWords} * sizeof(uint32_t));"], tmp)
        | .slice a hi lo =>
          -- A wide slice is a right-shift by `lo`, truncated to
          -- `hi-lo+1` bits.  Without this arm it fell into the generic
          -- memcpy below, which copies from the operand's BASE word and
          -- so silently DROPPED the `lo` offset: firtool's 138x2 SRAM
          -- wrote `wdata[68:0] << 69` where the RTL says
          -- `wdata[137:69] << 69`.
          let (da, aS) := matWide s!"{label}s" a
          let tmp := s!"__{label}_{sn}"
          let srcWords := wordsOf (inferExprWidth typeMap a)
          let outW := hi - lo + 1
          let topBits := outW - 32 * (nWords - 1)
          (da ++ (s!"        uint32_t {tmp}[{nWords}];"
            :: (List.range nWords).map (fun j =>
                 let v := shrSlot aS lo srcWords j
                 -- Mask the top word so bits above the slice don't leak.
                 if j == nWords - 1 && topBits < 32 then
                   s!"        {tmp}[{j}] = ({v}) & {(2 ^ topBits - 1 : Nat)}u;"
                 else s!"        {tmp}[{j}] = {v};")), tmp)
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
        -- The concat may be NARROWER than its destination (a 96-bit
        -- `{{32{b[63]}}, b[63:32], a[31:0]}` assigned to a 128-bit wire).
        -- `memcpy(dst, lit, sizeof(dst))` then read PAST the compound
        -- literal — 16 bytes out of a 12-byte source — so the top word
        -- held whatever followed it in memory instead of the zero fill.
        let cw := cargs.foldl (fun acc a => acc + inferExprWidth typeMap a) 0
        let srcWords := wordsOf cw
        let copyWords := min srcWords nWords
        { declarations := []
        , evalBody := decls ++
            (if copyWords < nWords then [s!"        memset({sn}, 0, sizeof({sn}));"] else []) ++
            [s!"        memcpy({sn}, {expr}, {copyWords} * sizeof(uint32_t));"]
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
        -- The shifted operand must be an indexable word array.  Calling
        -- `emitExpr` straight produced `(compound literal)[j]` whenever
        -- `a` was a concat or a nested wide op (XiangShan's Booth
        -- partial products are `{{96{b[31]}}, b[31:16]} << 16`), which C
        -- rejects — every other wide arm materialises through `matWide`,
        -- so these two did not need to be the exception.
        let (aDecls, aS) := matWide "sh" a
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
          , evalBody := aDecls ++ lines
          , tickBody := []
          , resetBody := []
          , evalTickLocals := [] }
        | _ =>
          -- DYNAMIC shift amount: the old fallback treated it as 0.  Runtime
          -- word loop (mirrors the nested matWide arm; see the Phr note there).
          let bS :=
              -- A WIDE dynamic shift amount is an array; casting it to
              -- unsigned takes the POINTER (TIMER's `128'h1 << {121'h0,
              -- addr…}` shifted by garbage).  Read its low word instead
              -- — amounts ≥ 2^32 are already out of range.
              if inferExprWidth typeMap b > 64 then s!"{emitExpr typeMap b}[0]"
              else emitExpr typeMap b
          { declarations := []
          , evalBody := aDecls ++
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
        -- Materialise the operand for the same reason as `shl` above.
        let (aDecls, aS) := matWide "sh" a
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
          , evalBody := aDecls ++ lines
          , tickBody := []
          , resetBody := []
          , evalTickLocals := [] }
        | _ =>
          let bS :=
              -- A WIDE dynamic shift amount is an array; casting it to
              -- unsigned takes the POINTER (TIMER's `128'h1 << {121'h0,
              -- addr…}` shifted by garbage).  Read its low word instead
              -- — amounts ≥ 2^32 are already out of range.
              if inferExprWidth typeMap b > 64 then s!"{emitExpr typeMap b}[0]"
              else emitExpr typeMap b
          { declarations := []
          , evalBody := aDecls ++
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
      | .op .asr [a, b] =>
        let (aDecls, aS) := matWide "sh" a
        let srcW := inferExprWidth typeMap a
        let bS :=
          if inferExprWidth typeMap b > 64 then s!"{emitExpr typeMap b}[0]"
          else emitExpr typeMap b
        { declarations := []
        , evalBody := aDecls ++ wideAsrInto sn aS bS nWords (wordsOf srcW) srcW
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
      let ifElseLines := emitMuxAsTree typeMap sn width rhs
      if !ifElseLines.isEmpty then
        { declarations := []
        , evalBody := ifElseLines
        , tickBody := []
        , resetBody := []
        , evalTickLocals := [] }
      else
        let expr := emitExpr typeMap rhs
        let masked := if storeIsMasked typeMap width rhs then expr else applyMask expr width
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
      let inputExpr := if storeIsMasked typeMap width input then rawExpr else applyMask rawExpr width
      let initExpr := emitInitScalar initValue width
      let ifElseLines := emitMuxAsTree typeMap nextName width input
      let nextLocalDecl := s!"        {cType} {nextName} = {outName};"
      let body : List String :=
        if ifElseLines.isEmpty then [s!"        {nextName} = {inputExpr};"]
        else ifElseLines
      { declarations := [s!"    {cType} {outName};", s!"    {cType} {nextName};"]
      , evalBody := body
      , tickBody := [s!"        {outName} = {nextName};"]
      , resetBody := [s!"        {outName} = {initExpr};"]
      , evalTickLocals := [nextLocalDecl]
      , inPlace := some fun _ => emitRegInPlace typeMap output outName width input }

  | .memory name addrWidth dataWidth _clock writeAddr writeData writeEnable
      readAddr readData comboRead extraWrites extraReads =>
    -- Multi-port memory.  Port 0 is the dedicated field set; the extras
    -- carry the additional ports (1R1W, dual-port, two-port, and
    -- XiangShan's 8R8W Difftest array).  Reads land in `evalBody` (or the
    -- latched-address path for synchronous reads) and writes in
    -- `tickBody`, so every port reads the state BEFORE this cycle's
    -- writes; simultaneous same-address writes resolve last-port-wins,
    -- because the write lines are emitted in port order.
    let memSize := 2 ^ addrWidth
    let memName := sanitizeName name
    let elemTy : HWType := .bitVector dataWidth
    let elemSuffix := emitArraySuffix elemTy
    let memDecl := s!"    {emitScalarBase elemTy} {memName}[{memSize}]{elemSuffix};"
    let readPorts := (readAddr, readData) :: extraReads
    let writePorts := (writeAddr, writeData, writeEnable) :: extraWrites
    let rdDecls := readPorts.filterMap fun (_, rd) =>
      let rdName := sanitizeName rd
      let inMap := typeMap.fold (fun acc n _ => acc || sanitizeName n == rdName) false
      if inMap then none else some s!"    {emitFieldDecl elemTy rdName};"
    -- Wide (>64-bit) write data is a uint32 ARRAY, and a wide OP has no
    -- inline C rendering (`array & array` is not C) — the masked
    -- read-modify-write that firtool's byte-enable SRAMs generate lands
    -- exactly there.  Materialise such data into a temp array first, one
    -- 32-bit slot at a time, then memcpy the temp into the row.
    let writeLines := (writePorts.zipIdx).flatMap fun ((a, d, en), pi) =>
      match en with
      | .const 0 _ => []   -- dead port
      | _ =>
        if dataWidth > 64 then
          match d with
          | .ref _ =>
            [s!"        if ({emitExpr typeMap en}) memcpy({memName}[{emitExpr typeMap a}], {emitExpr typeMap d}, sizeof({memName}[0]));"]
          | _ =>
            let tmp := s!"__mw{pi}_{memName}"
            let nWords := (dataWidth + 31) / 32
            [ s!"        \{ uint32_t {tmp}[{nWords}];"
            , s!"          memcpy({tmp}, {emitExpr typeMap d}, sizeof({tmp}));"
            , s!"          if ({emitExpr typeMap en}) memcpy({memName}[{emitExpr typeMap a}], {tmp}, sizeof({tmp})); }" ]
        else
          [s!"        if ({emitExpr typeMap en}) {memName}[{emitExpr typeMap a}] = {emitExpr typeMap d};"]
    let zeroLine := s!"        memset({memName}, 0, sizeof({memName}));"
    if comboRead then
      let readLines := readPorts.map fun (a, rd) =>
        let rdName := sanitizeName rd
        if dataWidth > 64 then
          s!"        memcpy({rdName}, {memName}[{emitExpr typeMap a}], sizeof({rdName}));"
        else
          s!"        {rdName} = {memName}[{emitExpr typeMap a}];"
      { declarations := [memDecl] ++ rdDecls
      , evalBody := readLines
      , tickBody := writeLines
      , resetBody := [zeroLine]
      , evalTickLocals := [] }
    else
      let addrType := emitScalarBase (.bitVector addrWidth)
      let latchName := fun (i : Nat) =>
        if i == 0 then s!"{memName}_raddr" else s!"{memName}_raddr{i}"
      let latchDecls := (readPorts.zipIdx).map fun (_, i) =>
        s!"    {addrType} {latchName i};"
      let latchSets := (readPorts.zipIdx).map fun ((a, _), i) =>
        s!"        {latchName i} = {emitExpr typeMap a};"
      let readTickLines := (readPorts.zipIdx).map fun ((_, rd), i) =>
        let rdName := sanitizeName rd
        if dataWidth > 64 then
          s!"        memcpy({rdName}, {memName}[{latchName i}], sizeof({rdName}));"
        else
          s!"        {rdName} = {memName}[{latchName i}];"
      { declarations := [memDecl] ++ latchDecls ++ rdDecls
      , evalBody := latchSets
      , tickBody := writeLines ++ readTickLines
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
    -- A wide connection expression must be gathered WORD BY WORD: a
    -- `memcpy` from `emitExpr expr` copies from the operand's base word
    -- and so drops a slice's offset.  `LCredit2Decoupled_4` wires the
    -- child's 256-bit data port to `io_in_flit[385:130]`; the memcpy read
    -- from bit 0 instead, so every entry stored in the child's SRAM held
    -- the wrong 256 bits (the IR and the re-emitted Verilog were both
    -- correct — only the JIT was wrong).
    let wideConnLines (dst : String) (expr : Expr) (nWords : Nat) : List String :=
      match expr with
      | .slice inner hi lo =>
        match inner with
        | .ref src =>
          let srcWords := (inferExprWidth typeMap inner + 31) / 32
          let k := lo / 32; let r := lo % 32
          let sn := sanitizeName src
          let outW := hi - lo + 1
          let topBits := outW - 32 * (nWords - 1)
          (List.range nWords).map fun j =>
            let idx := j + k
            let v :=
              if idx ≥ srcWords then "0u"
              else if r == 0 then s!"{sn}[{idx}]"
              else
                let hiPart := if idx + 1 < srcWords then s!" | ({sn}[{idx + 1}] << {32 - r})" else ""
                s!"(({sn}[{idx}] >> {r}){hiPart})"
            if j == nWords - 1 && topBits < 32 then
              s!"        {dst}[{j}] = ({v}) & {(2 ^ topBits - 1 : Nat)}u;"
            else s!"        {dst}[{j}] = {v};"
        | _ => [s!"        memcpy({dst}, {emitExpr typeMap expr}, sizeof({dst}));"]
      | _ => [s!"        memcpy({dst}, {emitExpr typeMap expr}, sizeof({dst}));"]
    let inputConns := connections.filterMap fun (portName, expr) =>
      if !outputPortNames.contains portName then
        let portWidth := match subModule with
          | some sm =>
            match (sm.inputs ++ sm.outputs ++ sm.wires).find? (·.name == portName) with
            | some p => p.ty.bitWidth
            | none => 32
          | none => 32
        if portWidth > 64 then
          some (String.intercalate "\n"
            (wideConnLines s!"{iName}.{sanitizeName portName}" expr ((portWidth + 31) / 32)))
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

/-- A wire is guarded by its readers' conditions only if its expression has
    at least this many nodes, and at least twice as many as the guard. -/
def lazyWireMinSize : Nat := 8

/-- Number of nodes of an expression. -/
partial def exprSize : Expr → Nat
  | .op _ args => args.foldl (fun n a => n + exprSize a) 1
  | .concat args => args.foldl (fun n a => n + exprSize a) 1
  | .slice e _ _ | .sliceDim e _ _ => 1 + exprSize e
  | .index a i => 1 + exprSize a + exprSize i
  | _ => 1

/-- Where a name is read, as a disjunction of conjunctions: each term is a
    list of conjuncts known true at one read.  `[[]]` is "read
    unconditionally".  Terms are cut to `lazyTermDepth` conjuncts and the
    list to `lazyMaxTerms` terms; beyond that it collapses to what all
    terms have in common.  Cutting only weakens the condition. -/
abbrev UseTerms := List (List Expr)

def lazyTermDepth : Nat := 3
def lazyMaxTerms : Nat := 4

/-- Record that `name` is read where the conjuncts `ctx` are known true. -/
private def recordUse (acc : Std.HashMap String UseTerms) (name : String)
    (ctx : List Expr) : Std.HashMap String UseTerms :=
  let ctx := ctx.take lazyTermDepth
  match acc.get? name with
  | none => acc.insert name [ctx]
  | some ts =>
    if ts == [[]] then acc
    else if ctx.isEmpty then acc.insert name [[]]
    -- a recorded term that is weaker than `ctx` already covers it
    else if ts.any (fun t => t.all (ctx.contains ·)) then acc
    else
      -- `ctx` covers the recorded terms that are stronger than it
      let ts := ctx :: ts.filter fun t => !(ctx.all (t.contains ·))
      if ts.length ≤ lazyMaxTerms then acc.insert name ts
      else
        let common := ts.foldl (fun c t => c.filter (t.contains ·)) ctx
        acc.insert name [common]

private def recordUses (acc : Std.HashMap String UseTerms) (ctx : List Expr)
    (e : Expr) : Std.HashMap String UseTerms :=
  let refs := (collectExprRefs e).foldl (fun (h : Std.HashSet String) r => h.insert r) {}
  refs.fold (fun acc r => recordUse acc r ctx) acc

/-- For every name `e` reads, the conjuncts that are known true at the
    read, following the decision tree `muxAssignLines` emits for
    `lhs = e`: conjunct `k` of an arm is evaluated only after conjuncts
    `0..k-1` held, and an arm's value only after all of them did.
    `ctx` is what already holds on entry. -/
private partial def useContexts (typeMap : TypeMap) (ctx : List Expr) (e : Expr)
    (acc : Std.HashMap String UseTerms) : Std.HashMap String UseTerms :=
  let (arms, default_) := flattenMuxChain e
  if arms.isEmpty then recordUses acc ctx e
  else
    let acc := arms.foldl (fun acc (c, v) =>
      let cs := dropImpliedConjuncts (condConjuncts typeMap c)
      let (acc, _) := cs.foldl (fun (acc, pre) ck =>
        (recordUses acc (ctx ++ pre) ck, pre ++ [ck])) (acc, ([] : List Expr))
      useContexts typeMap (ctx ++ cs) v acc) acc
    useContexts typeMap ctx default_ acc

/-- Collect all wire names referenced in tick() bodies. -/
def collectTickRefWires (body : List Stmt) : List String :=
  body.foldl (fun acc stmt =>
    match stmt with
    | .register _ _ _ input _ =>
      acc ++ (collectExprRefs input).map sanitizeName
    | .memory _ _ _ _ wa wd we ra rd cr .. =>
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
    (body : List Stmt) : List Stmt × Bool := Id.run do
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
    | .memory _ _ _ _ _ _ _ _ rd cr .. => if cr then [rd] else []
    | .inst .. => childOutputs s
    | _ => []
  let usesOf : Stmt → List String := fun s => match s with
    | .assign _ rhs => collectExprRefs rhs
    | .memory _ _ _ _ _ _ _ ra _ cr .. => if cr then collectExprRefs ra else []
    | .inst modName _ conns =>
      match design.bind (·.findModule modName) with
      | some sm =>
        -- Only an OUTPUT connection is exempt from counting as a use.
        -- Filtering the instance's outputs out of EVERY connection hid
        -- the back edge: XiangShan's arbiters feed `gnt` (a child output)
        -- back into the child's own `req` input, and once the optimizer
        -- inlines `req` into the connection the instance is the only
        -- statement left — so the cycle became invisible and the emitted
        -- pass read a stale `gnt`.
        conns.foldl (fun acc (p, e) =>
          if sm.outputs.any (·.name == p) then acc
          else acc ++ collectExprRefs e) []
      | none => conns.foldl (fun acc (_, e) => acc ++ collectExprRefs e) []
    | _ => []
  let schedulable : Stmt → Bool := fun s => match s with
    | .assign .. | .inst .. => true
    | .memory _ _ _ _ _ _ _ _ _ cr .. => cr
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
  -- cycle (or fuel-out): keep the rest in original order.  `remaining`
  -- non-empty means a genuine dependency cycle at STATEMENT granularity
  -- — for an `.inst`, the whole child is one node, so a handshake that
  -- goes into the child and back out again (XiangShan's arbiters gate
  -- `req` with the `gnt` the child produces) is a cycle here even though
  -- it is acyclic per signal.  A single pass then reads the STALE value.
  -- The caller re-evaluates to a fixed point instead.
  return (result ++ remaining ++ rest, !remaining.isEmpty)

/-- Wires that some eval statement reads BEFORE the statement that drives
    them, in the emitted order: a combinational cycle at statement
    granularity, or a wire that refers to itself (`x = (x & ~m) | f`, the
    lowering of a part-wise assignment).  Such a read sees the value the
    previous call left behind, so the wire must keep its struct field.

    The flag is true when some statement reads ANOTHER statement's wire
    too early — a real cycle, which one pass does not settle.  A wire that
    only refers to itself does not need a second pass. -/
def evalStaleReads (design : Option Design) (body : List Stmt) : List String × Bool := Id.run do
  let childOutputs : Stmt → List String := fun s => match s with
    | .inst modName _ conns =>
      match design.bind (·.findModule modName) with
      | some sm => conns.filterMap (fun (p, e) =>
          if sm.outputs.any (·.name == p) then
            match e with | .ref w => some w | _ => none
          else none)
      | none => conns.filterMap fun (_, e) => match e with | .ref w => some w | _ => none
    | _ => []
  let defsOf : Stmt → List String := fun s => match s with
    | .assign lhs _ => [lhs]
    | .memory _ _ _ _ _ _ _ _ rd _ _ er => rd :: er.map (·.2)
    | .inst .. => childOutputs s
    | _ => []
  let usesOf : Stmt → List String := fun s => match s with
    | .assign _ rhs => collectExprRefs rhs
    | .memory _ _ _ _ _ _ _ ra _ cr _ er =>
      if cr then er.foldl (fun acc (a, _) => collectExprRefsAux acc a) (collectExprRefs ra) else []
    | .inst _ _ conns => conns.foldl (fun acc (_, e) => collectExprRefsAux acc e) []
    | _ => []
  let produced : Std.HashSet String :=
    body.foldl (fun h s => (defsOf s).foldl (fun h n => h.insert n) h) {}
  -- A latched memory read is state: reading its previous value is the
  -- design's meaning, not an ordering accident.
  let latched : Std.HashSet String := body.foldl (fun h s => match s with
    | .memory _ _ _ _ _ _ _ _ rd cr _ er =>
      if cr then h else er.foldl (fun h (_, r) => h.insert r) (h.insert rd)
    | _ => h) {}
  let mut defined : Std.HashSet String := {}
  let mut stale : List String := []
  let mut cross := false
  for s in body do
    let outs := defsOf s
    for r in usesOf s do
      -- an instance's own output connection is not a read
      let own := match s with | .inst .. => outs.contains r | _ => false
      if !own && produced.contains r && !defined.contains r then
        stale := r :: stale
        if !outs.contains r && !latched.contains r then cross := true
    for d in outs do
      defined := defined.insert d
  return (stale, cross)

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
    | .memory _ _ _ _ wa wd we ra _ _ .. =>
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
    (funcQual : String := "")
    (fusedLocalWires : Option (List String) := none) : String :=
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
    let (filteredBody, hasEvalCycle) := scheduleEvalBody design m filteredBody
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
    -- A wire that is read before the statement that drives it (a cyclic
    -- eval order) must be a struct member.  As an eval-local it was read
    -- UNINITIALISED on the first relaxation round, and the fixed-point
    -- test (`memcmp` of the struct) could not see it change, so the loop
    -- stopped while values were still propagating: VexRiscv's top level
    -- agreed with the reference at -O1 and at no other optimisation
    -- level.
    let (staleNames, crossStale) := evalStaleReads design filteredBody
    let staleReads : Std.HashSet String :=
      staleNames.foldl (fun h n => h.insert (sanitizeName n)) {}
    let memberWires := match observableWires with
      | some ws => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          ws.contains sn || tickRefs.contains sn || staleReads.contains sn
      | none => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          sn.startsWith "_gen_" || tickRefs.contains sn || staleReads.contains sn
    let memoryNames := m.body.filterMap fun s => match s with
      | .memory name _ _ _ _ _ _ _ _ _ .. => some (sanitizeName name) | _ => none
    let localWires := match observableWires with
      | some ws => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          !ws.contains sn && !tickRefs.contains sn && !memoryNames.contains sn &&
            !staleReads.contains sn
      | none => internalWires.filter fun (w : Port) =>
          let sn := sanitizeName w.name
          !sn.startsWith "_gen_" && !tickRefs.contains sn && !memoryNames.contains sn &&
            !staleReads.contains sn

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

    -- ----------------------------------------------------------------
    -- Registers updated IN PLACE by the fused eval_tick.
    --
    -- The general form computes every register's next value into a
    -- `_next` local and copies all of them back at the end: a load and
    -- a store per register per cycle, taken or not.  A register may
    -- instead be written directly, and not at all when it holds, as
    -- long as nothing emitted afterwards still needs its old value.
    -- Everything combinational is emitted before the registers, so the
    -- only later readers are (a) other registers' next-state logic and
    -- (b) the memory statements, which run in the tick part.  (b)
    -- excludes a register outright; (a) is an ordering constraint —
    -- a register is written after every register that reads it — and
    -- the registers on a cycle of such reads (a swap, a ring) keep the
    -- `_next` form.
    -- ----------------------------------------------------------------
    let fusedWireLocals : List Port :=
      match fusedLocalWires with
      | none => []
      | some keep => memberWires.filter fun (w : Port) =>
        !keep.contains (sanitizeName w.name) && !staleReads.contains (sanitizeName w.name) && (match w.ty with
          | .bit => true
          | .bitVector n => n ≤ 64
          | _ => false)
    let stmtParts := filteredBody.zip allParts
    let inPlaceOrder : Array String := Id.run do
      let memRefs : Std.HashSet String := filteredBody.foldl (fun h s => match s with
        | .memory _ _ _ _ wa wd we ra _ _ ew er =>
          let refs := collectExprRefsAux (collectExprRefsAux (collectExprRefsAux (collectExprRefs wa) wd) we) ra
          let refs := ew.foldl (fun acc (a, d, e) =>
            collectExprRefsAux (collectExprRefsAux (collectExprRefsAux acc a) d) e) refs
          let refs := er.foldl (fun acc (a, _) => collectExprRefsAux acc a) refs
          refs.foldl (fun h n => h.insert n) h
        | _ => h) {}
      let cands : List (String × Expr) := stmtParts.filterMap fun (s, p) => match s, p.inPlace with
        | .register out _ _ input _, some _ => if memRefs.contains out then none else some (out, input)
        | _, _ => none
      let candSet : Std.HashSet String := cands.foldl (fun h (o, _) => h.insert o) {}
      -- reads o = the candidate registers, other than o, that o's input reads
      let mut reads : Std.HashMap String (List String) := {}
      let mut readers : Std.HashMap String Nat := {}
      for (o, input) in cands do
        let rs := ((collectExprRefs input).foldl (fun (h : Std.HashSet String) r =>
          if r != o && candSet.contains r then h.insert r else h) {}).toList
        reads := reads.insert o rs
        for r in rs do
          readers := readers.insert r (readers.getD r 0 + 1)
      let mut queue : Array String := #[]
      for (o, _) in cands do
        if readers.getD o 0 == 0 then queue := queue.push o
      let mut i := 0
      while i < queue.size do
        let o := queue[i]!
        i := i + 1
        for r in reads.getD o [] do
          let c := readers.getD r 0 - 1
          readers := readers.insert r c
          if c == 0 then queue := queue.push r
      return queue
    let inPlaceSet : Std.HashSet String := inPlaceOrder.foldl (fun h o => h.insert o) {}
    let inPlaceOf : Std.HashMap String (Unit → List String) := stmtParts.foldl (fun h (s, p) =>
      match s, p.inPlace with
      | .register out .., some f => h.insert out f
      | _, _ => h) {}
    -- ----------------------------------------------------------------
    -- Wires computed only when needed (fused eval_tick, stack-local
    -- wires only).
    --
    -- A wire is computed on every cycle although most cycles never look
    -- at it: PicoRV32's multiplier carry chain while nothing multiplies,
    -- `instr_trap` outside the one state that tests it.  For each local
    -- wire take the conjuncts that are known true at EVERY place that
    -- reads it — what the decision trees have already tested by then —
    -- and compute the wire under those: `if (g1 && g2) w = …;`.  If some
    -- read is unconditional the set is empty and the wire stays as it
    -- is.  A conjunct is kept only if everything it reads is available
    -- where the wire is computed (state, or a wire driven earlier);
    -- dropping one only makes the guard weaker, which is safe.  Readers
    -- are visited before the wires they read, so a wire that feeds only
    -- guarded wires inherits their guards.
    -- ----------------------------------------------------------------
    let lazyGuards : Std.HashMap String UseTerms := Id.run do
      if fusedLocalWires.isNone then return {}
      -- Candidates: the stack-local wires, and the wide (array) wires,
      -- which no one can observe either (`get_wire` is scalar-only).
      -- A skipped wide wire just keeps its previous contents.
      let keep := fusedLocalWires.getD []
      let cand : Std.HashSet String := fusedWireLocals.foldl (fun h w => h.insert w.name) {}
      let cand := internalWires.foldl (fun h (w : Port) =>
        if w.ty.bitWidth > 64 && !keep.contains (sanitizeName w.name) &&
           !staleReads.contains (sanitizeName w.name) then h.insert w.name else h) cand
      if cand.isEmpty then return {}
      let indexed := filteredBody.zip (List.range filteredBody.length)
      -- where each combinationally driven name is driven
      let mut pos : Std.HashMap String Nat := {}
      for (s, i) in indexed do
        match s with
        | .assign lhs _ => pos := pos.insert lhs i
        | .memory _ _ _ _ _ _ _ _ rd _ _ er =>
          pos := pos.insert rd i
          for (_, r) in er do pos := pos.insert r i
        | .inst _ _ conns =>
          for (_, e) in conns do
            match e with
            | .ref w => if !pos.contains w then pos := pos.insert w i
            | _ => pure ()
        | _ => pure ()
      let mut acc : Std.HashMap String UseTerms := {}
      -- the unconditional readers and the registers first …
      for s in filteredBody do
        match s with
        | .register out _ _ input _ =>
          acc := if lookupWidth typeMap out ≤ 64 then useContexts typeMap [] input acc
                 else recordUses acc [] input
        | .memory _ _ _ _ wa wd we ra _ _ ew er =>
          for e in [wa, wd, we, ra] do acc := recordUses acc [] e
          for (a, d, e) in ew do
            for x in [a, d, e] do acc := recordUses acc [] x
          for (a, _) in er do acc := recordUses acc [] a
        | .inst _ _ conns =>
          for (_, e) in conns do acc := recordUses acc [] e
        | _ => pure ()
      -- … then the assigns, last one first
      let mut guards : Std.HashMap String UseTerms := {}
      for (s, i) in indexed.reverse do
        match s with
        | .assign x rhs =>
          let size := exprSize rhs
          let terms : UseTerms :=
            if !cand.contains x || size < lazyWireMinSize then [[]]
            else
              -- keep the conjuncts whose inputs exist where `x` is computed
              let ts := (acc.getD x [[]]).map fun t => t.filter fun c =>
                (collectExprRefs c).all fun r => r != x && (pos.get? r).all (· < i)
              -- … and only if the test is clearly cheaper than the wire
              let cost := ts.foldl (fun n t => t.foldl (fun n c => n + exprSize c) n) 0
              if ts.any (·.isEmpty) || size < 2 * cost then [[]] else ts
          let scalar := lookupWidth typeMap x ≤ 64
          if terms != [[]] then
            guards := guards.insert x terms
            -- the guard itself reads its conjuncts, each after the ones before it
            for t in terms do
              let (acc', _) := t.foldl (fun (acc, pre) ck =>
                (recordUses acc pre ck, pre ++ [ck])) (acc, ([] : List Expr))
              acc := acc'
          for t in terms do
            if scalar then
              acc := useContexts typeMap t rhs acc
            else
              -- A wide mux is emitted word by word as `c ? T[j] : E[j]`.
              -- A compound arm is materialised first, on every pass; an
              -- arm that is a plain wire is only read when selected.
              match rhs with
              | .op .mux [c, .ref r, e] =>
                acc := recordUses acc t c
                acc := recordUse acc r (t ++ dropImpliedConjuncts (condConjuncts typeMap c))
                acc := recordUses acc t e
              | _ => acc := recordUses acc t rhs
        | _ => pure ()
      return guards
    -- `common && (rest1 || rest2 || …)`
    let lazyCond (terms : UseTerms) : String :=
      let conj (cs : List Expr) : String := String.intercalate " && " (cs.map (emitExpr typeMap))
      match terms with
      | [t] => conj t
      | t0 :: _ =>
        let common := terms.foldl (fun c t => c.filter (t.contains ·)) t0
        let rests := terms.map fun t => t.filter (!common.contains ·)
        let alts := String.intercalate " || " (rests.map fun r => s!"({conj r})")
        if rests.any (·.isEmpty) then conj common
        else if common.isEmpty then alts
        else s!"{conj common} && ({alts})"
      | [] => "1"
    let fusedParts : List StmtParts := stmtParts.map fun (s, p) => match s with
      | .register out .. =>
        if inPlaceSet.contains out then
          { p with evalBody := [], tickBody := [], evalTickLocals := [] }
        else p
      | _ => p
    -- The guard line of each statement (lazy wires only).  Neighbours with
    -- the same guard share one block.
    let fusedGuardOf : List (Option String) := stmtParts.map fun (s, _) => match s with
      | .assign x _ => (lazyGuards.get? x).map lazyCond
      | _ => none
    let fusedStmtLines : List String := Id.run do
      let mut out : Array String := #[]
      let mut openGuard : Option String := none
      for (p, g) in fusedParts.zip fusedGuardOf do
        if p.evalBody.isEmpty then continue
        if g != openGuard then
          if openGuard.isSome then out := out.push "        }"
          match g with
          | some c => out := out.push s!"        if ({c}) \{"
          | none => pure ()
          openGuard := g
        out := out ++ p.evalBody.toArray
      if openGuard.isSome then out := out.push "        }"
      return out.toList
    let fusedEvalBody := inputMaskBody ++ fusedStmtLines ++
      inPlaceOrder.foldl (fun acc o => acc ++ (inPlaceOf.getD o (fun _ => [])) ()) []
    let fusedTickBody := fusedParts.foldl (fun acc (p : StmtParts) => acc ++ p.tickBody) []
    let fusedLocals := fusedParts.foldl (fun acc (p : StmtParts) => acc ++ p.evalTickLocals) []

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
    -- `fusedLocalWires := some keep`: inside eval_tick the internal wires
    -- live on the stack as well.  A wire stored into the struct has to be computed on
    -- every cycle; as a local the C compiler drops what is unused and
    -- sinks what only one branch reads.  The price is observability:
    -- after eval_tick() such a wire's struct field (what `get_wire`
    -- reads) is stale until the next eval().  The wires in `keep` stay
    -- members; so do wide (array) wires and any wire that is read before
    -- it is driven (`evalStaleReads`).
    let memberSetET : Std.HashSet String :=
      fusedWireLocals.foldl (fun s w => s.erase (sanitizeName w.name)) memberSetET
    let fusedWireDecls := fusedWireLocals.map fun (p : Port) =>
      s!"    {emitFieldDecl p.ty (sanitizeName p.name)} = 0;"
    let qualifyET := qualifyWith memberSetET

    let resetFn :=
      s!"{funcQual}static void sparkle_{className}_reset({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if resetBodyQ.isEmpty then "" else
        String.intercalate "\n" resetBodyQ ++ "\n") ++
      "}\n\n"

    -- When the schedule could not be topologically ordered, a
    -- combinational dependency runs BACKWARDS through the emitted order
    -- (a handshake into a child instance and back out — the whole child
    -- is one node, so this is a cycle at statement granularity even when
    -- it is acyclic per signal).  One pass reads the stale value, so
    -- relax to a fixed point: re-run the body until the observable state
    -- stops changing.  Bounded, and the bound is not a heuristic —
    -- a settling combinational network converges in at most as many
    -- rounds as it has statements.
    let relaxRounds := evalBodyQ.length + 1
    let evalFn :=
      s!"{funcQual}static void sparkle_{className}_eval({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if localWireDecls.isEmpty then "" else
        String.intercalate "\n" localWireDecls ++ "\n") ++
      (if evalBodyQ.isEmpty then "" else
        (if hasEvalCycle then
          s!"    \{ {structName} __prev; unsigned __round = 0;\n" ++
          s!"      for (; __round < {relaxRounds}u; __round++) \{\n" ++
          "        __prev = *self;\n" ++
          String.intercalate "\n" evalBodyQ ++ "\n" ++
          "        if (__builtin_memcmp(&__prev, self, sizeof(__prev)) == 0) break;\n" ++
          "      } }\n"
        else String.intercalate "\n" evalBodyQ ++ "\n")) ++
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
    let evalTickEvalBody := (fusedEvalBody.map qualifyET).map fun line =>
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
    let evalTickTickBody := (fusedTickBody.map qualifyET).filter fun line =>
      !instNames.any (fun inst =>
        (line.splitOn s!"sparkle_evalTick_placeholder_TICK_{inst}").length > 1
        || (line.splitOn s!"_tick(&self->{inst})").length > 1)

    let fusedTickFn :=
      s!"{funcQual}static void sparkle_{className}_eval_tick({structName}* self) \{\n" ++
      "    (void)self;\n" ++
      (if localWireDecls.isEmpty then "" else
        String.intercalate "\n" localWireDecls ++ "\n") ++
      (if fusedWireDecls.isEmpty then "" else
        String.intercalate "\n" fusedWireDecls ++ "\n") ++
      -- Stack-local register `_next` temporaries (pre-init from the
      -- current register value to preserve non-blocking semantics).
      -- Qualified so the `_next` LHS stays bare (local) while the
      -- initialising register read becomes `self->reg`.
      (if fusedLocals.isEmpty then "" else
        String.intercalate "\n" (fusedLocals.map qualifyET) ++ "\n") ++
      (if evalTickEvalBody.isEmpty then "" else
        String.intercalate "\n" evalTickEvalBody ++ "\n") ++
      (if evalTickTickBody.isEmpty then "" else
        String.intercalate "\n" evalTickTickBody ++ "\n") ++
      "}\n\n"

    -- A real combinational cycle needs eval()'s fixed-point loop; the
    -- single fused pass read stale values (VexRiscv's top level, whose
    -- handshake runs through a child instance and back, disagreed with
    -- the reference through eval_tick).  Such a module steps as eval +
    -- tick.
    let evalTickFn :=
      if crossStale then
        s!"{funcQual}static void sparkle_{className}_eval_tick({structName}* self) \{\n" ++
        s!"    sparkle_{className}_eval(self);\n    sparkle_{className}_tick(self);\n}\n\n"
      else fusedTickFn

    structDecl ++ resetFn ++ evalFn ++ tickFn ++ evalTickFn

/-- Backend-local pre-pass: hoist wide (>64-bit) compound expressions out
    of positions the C emitter cannot render inline, into their own wires.
    C has no expression form for a multi-word value, so a wide compound is
    only renderable where the emitter MATERIALISES it (`matWide` under an
    assign/register, `wideConnLines` for slice connections).  Everywhere
    else — an instance connection built from a mux-of-concats (DivUnit's
    `csa_sel` operands), a wide operand of a comparison (ShiftRightJam's
    `|(io_in & sticky_mask)`), a wide arm of a mux whose RESULT is ≤64
    bits (SBToTL's `cond ? 64'h0 : {…}`) — `emitExpr` used to render a
    compound literal into scalar arithmetic and the C did not compile.
    Hoisting each such subexpression into a wire routes it through the
    well-tested wide-assign machinery; scalar consumers then read the
    wire, which every arm already handles.  Semantically neutral: the
    hoisted cones are combinational and effect-free. -/
def hoistWideForC (m : Module) : Module := Id.run do
  let tm := buildTypeMap m
  let mut counter := 0
  let mut newWires : List Port := []
  let mut newAssigns : List Stmt := []
  -- Hoist `e` into a fresh wire, returning the replacement ref.
  let hoist (e : Expr) (w : Nat) (c : Nat) : Expr × Stmt × Port :=
    let nm := s!"_wide_hoist_{c}"
    (.ref nm, .assign nm e, { name := nm, ty := .bitVector w })
  let isCompound : Expr → Bool := fun e => match e with
    | .ref _ => false | .const _ _ => false | _ => true
  -- Rewrite one expression tree.  `top` marks the RHS root of an
  -- assign/register, where the wide machinery already copes.
  let rec fix (top : Bool) (e : Expr) : StateM (Nat × List Stmt × List Port) Expr := do
    match e with
    | .op .mux [c, t, f] =>
      -- The CONDITION is a truth value, not a bit pattern: a wide ref
      -- there renders as an array name (a pointer — always true), and
      -- truncating it to 64 bits is just as wrong (a value whose only
      -- set bits are above bit 63 must still count as true).  Rewrite
      -- wide conditions as an explicit `!= 0`, which the word-wise eq
      -- arm renders correctly.  Arms keep value semantics.
      let wc := inferExprWidth tm c
      let mut c' ← fix false c
      if wc > 64 then
        if isCompound c' then
          let (n, as_, ws) ← get
          let (r, asg, p) := hoist c' wc n
          set (n + 1, as_ ++ [asg], ws ++ [p])
          c' := r
        c' := .op .not [.op .eq [c', .const 0 wc]]
      let w := inferExprWidth tm e
      let t' ← fix false t
      let f' ← fix false f
      let e' := Expr.op .mux [c', t', f']
      if w > 64 && !top then
        let (n, as_, ws) ← get
        let (r, a, p) := hoist e' w n
        set (n + 1, as_ ++ [a], ws ++ [p])
        return r
      else if w ≤ 64 then
        -- ≤64-bit mux: a wide-ref ARM reads its low 64 bits (context
        -- truncation), same as the scalar-op rule below.
        let wrap := fun (orig : Expr) (a : Expr) => match a with
          | .ref _ => if inferExprWidth tm orig > 64 then Expr.slice a 63 0 else a
          | _ => a
        return Expr.op .mux [c', wrap t t', wrap f f']
      else return e'
    | .op op args =>
      let w := inferExprWidth tm e
      if w > 64 then
        -- Wide result: matWide handles it AT an assign root; anywhere
        -- else it must become a wire itself.
        let args' ← args.mapM (fix false)
        let e' := Expr.op op args'
        if top then return e'
        else
          let (n, as_, ws) ← get
          let (r, a, p) := hoist e' w n
          set (n + 1, as_ ++ [a], ws ++ [p])
          return r
      else
        -- Scalar result: any WIDE COMPOUND operand must become a wire.
        -- A comparison then compares the wire (emitExpr has a word-wise
        -- arm for wide refs); a VALUE context (a mux arm feeding a ≤64-bit
        -- result) instead reads the wire's low 64 bits via `.slice`,
        -- which is exactly Verilog's context-width truncation — a bare
        -- wide ref there would render as an array name in scalar
        -- arithmetic (SBToTL's `cond ? 64'h0 : {…}`).
        let isCmp := match op with
          | .eq | .lt_u | .lt_s | .le_u | .le_s
          | .gt_u | .gt_s | .ge_u | .ge_s => true
          | _ => false
        let args' ← args.mapM fun a => do
          let wa := inferExprWidth tm a
          let mut a' ← fix false a
          if wa > 64 && isCompound a' then
            let (n, as_, ws) ← get
            let (r, asg, p) := hoist a' wa n
            set (n + 1, as_ ++ [asg], ws ++ [p])
            a' := r
          if wa > 64 && !isCmp then
            match a' with
            | .ref _ => return .slice a' 63 0
            | _ => return a'
          else return a'
        return .op op args'
    | .concat args =>
      let w := inferExprWidth tm e
      let args' ← args.mapM (fix false)
      let e' := Expr.concat args'
      if w > 64 && !top then
        let (n, as_, ws) ← get
        let (r, a, p) := hoist e' w n
        set (n + 1, as_ ++ [a], ws ++ [p])
        return r
      else return e'
    | .slice a hi lo =>
      let a' ← fix false a
      -- Compose nested slices: `slice(slice(base, h1, l1), h2, l2)` is
      -- `slice(base, l1+h2, l1+l2)`.  Left nested, the scalar-slice
      -- emitter calls emitExpr on the INNER wide slice — which has no
      -- inline C form and used to hand back the base with its offset
      -- silently dropped (now the loud sentinel; either way, compose).
      match a' with
      | .slice base _ l1 => return .slice base (l1 + hi) (l1 + lo)
      | _ => return .slice a' hi lo
    | .sliceDim a hi lo =>
      let a' ← fix false a
      return .sliceDim a' hi lo
    | .index a i =>
      return .index (← fix false a) (← fix false i)
    | _ => return e
  let runFix (top : Bool) (e : Expr) : StateM (Nat × List Stmt × List Port) Expr :=
    fix top e
  -- `top := true` (skip hoisting: matWide copes) is only sound when the
  -- DESTINATION is itself wide.  A wide RHS landing in a ≤64-bit lhs
  -- (`_GEN_1 = wide & 64'hff…`, MiscResultSelect) took the scalar assign
  -- path and rendered the array name in scalar arithmetic — hoist it and
  -- read the wire's low 64 bits instead (= Verilog context truncation).
  let widthOfName := fun (nm : String) => lookupWidth tm nm
  -- `origWide` is the pre-rewrite RHS width: a freshly hoisted wire is
  -- not in `tm`, so the original expression's width is what says whether
  -- the returned ref needs its low-64 read.
  let scalarize := fun (origWide : Bool) (e : Expr) => match e with
    | .ref nm => if origWide || lookupWidth tm nm > 64 then Expr.slice e 63 0 else e
    | _ => e
  let mut body' : List Stmt := []
  for st in m.body do
    let (st', (c', as_, ws)) := (do
      match st with
      | .assign l r =>
        if widthOfName l > 64 then
          return Stmt.assign l (← runFix true r)
        else
          let wide := inferExprWidth tm r > 64
          let r' ← runFix false r
          return Stmt.assign l (scalarize wide r')
      | .register o ck rs inp init =>
        if widthOfName o > 64 then
          return Stmt.register o ck rs (← runFix true inp) init
        else
          let wide := inferExprWidth tm inp > 64
          let inp' ← runFix false inp
          return Stmt.register o ck rs (scalarize wide inp') init
      | .inst mn inm conns =>
        let conns' ← conns.mapM fun (p, e) => do
          let e' ← runFix false e
          return (p, e')
        return Stmt.inst mn inm conns'
      | .memory n aw dw ck wa wd we ra rd cr ew er =>
        let wdTop := dw > 64
        return Stmt.memory n aw dw ck (← runFix false wa) (← runFix wdTop wd)
          (← runFix false we) (← runFix false ra) rd cr
          (← ew.mapM fun (a, dta, en) =>
            return (← runFix false a, ← runFix wdTop dta, ← runFix false en))
          (← er.mapM fun (a, r) => return (← runFix false a, r))
      : StateM (Nat × List Stmt × List Port) Stmt).run (counter, [], []) |>.run
    counter := c'
    newAssigns := newAssigns ++ as_
    newWires := newWires ++ ws
    body' := body' ++ [st']
  -- No early-out on "nothing hoisted": the pass also performs PURE
  -- rewrites (nested-slice composition, mux-condition truthiness,
  -- scalar-lhs truncation) that must survive even when no wire was
  -- added — keying the return on newAssigns discarded them.
  return { m with body := newAssigns ++ body', wires := m.wires ++ newWires }

/-- Convert a full design to C simulation code (no JIT wrapper) -/
def toCDesign (d : Design)
    (observableWires : Option (List String) := none)
    (funcQual : String := "")
    (fusedLocalWires : Option (List String) := none) : String :=
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
  let code := sorted.map fun m0 =>
    let m := hoistWideForC m0
    if m.name == topName then emitModule m (some d) observableWires funcQual fusedLocalWires
    else emitModule m (some d) none funcQual fusedLocalWires
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
    (observableWires0 : Option (List String) := none)
    (fusedLocalWires : Bool := false) : String :=
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
  -- With `fusedLocalWires` only the wires the caller named are refreshed
  -- by eval_tick(); the others are refreshed by eval() alone.
  let classCode := toCDesign d observableWires ""
    (if fusedLocalWires then some (observableWires0.getD []) else none)
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


/-- The JIT wrapper `.c` for a design.

    `fusedLocalWires := true` is the fast configuration: `eval_tick` keeps
    internal wires on the stack, so after it `get_wire` is current only
    for the wires listed in `observableWires` — call `eval` first to read
    the others.  Registers, memories and outputs are unaffected.  The
    default keeps every named wire current after `eval_tick`. -/
def toCJIT (d : Design)
    (observableWires : Option (List String) := none)
    (fusedLocalWires : Bool := false) : String :=
  if d.modules.any moduleHasSymbolicWidth then
    unsupportedSymbolicWidthError
  else
    toCJITUnchecked d observableWires fusedLocalWires

/-- Specialize retained dimensions for one explicit configuration, then emit
    the fixed-ABI C JIT wrapper. -/
def toCJITWithParameters (d : Design)
    (bindings : Sparkle.IR.Specialize.Bindings)
    (observableWires : Option (List String) := none) : Except String String := do
  let concrete ← Sparkle.IR.Specialize.specializeDesign d bindings
  return toCJIT concrete observableWires
end Sparkle.Backend.CSim
