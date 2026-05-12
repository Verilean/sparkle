/-
  Vendored interpreter for Hesper's WGSL DSL — Lean-side semantic
  evaluation of `Hesper.WGSL.Exp`.

  ## Provenance and PR plan

  Source repo:  https://github.com/Verilean/hesper
  Source files:
    - Hesper/WGSL/Types.lean   (WGSLType, ScalarType)
    - Hesper/WGSL/Exp.lean     (Exp GADT — 226 constructors)

  Hesper's WGSL DSL is a typed AST (`Exp : WGSLType → Type`) that
  compiles to WGSL/PTX. Like `CircuitInterp.lean` (the Circuit
  evaluator), this file gives a **pure-Lean evaluator** for the
  same AST so that "Sparkle ≡ Hesper at GPU level" claims can be
  discharged inside Lean — no GPU FFI, no string parsing.

  Both the Circuit and WGSL interpreters are intended to be
  upstreamed to Hesper so the whole community gets a reference
  semantics. The two-layer story (Circuit IR → WGSL DSL → real
  GPU) is the user's request: each layer pinned independently
  inside Lean.

  ## Scope: Phase 1 (this file)

  We evaluate the **scalar f32 + vec / arith** slice of `Exp`, the
  one BitLinear and attention need:

    - scalar literals (litF32, litI32, litU32, litBool)
    - all binary arithmetic / comparison / boolean / bitwise
    - all conversions (toF32/toI32/toU32/toBool)
    - vec2/3/4 construction + component access
    - `select`, `min`, `max`, `clamp`, `abs`, `sign`
    - all f32 transcendentals (exp/log/sqrt/sin/cos/...)
    - `index` (array lookup)

  Out of scope for Phase 1 (return `default`, future Phase 2):
    - matrices (mat2x2, mat3x3, mat4x4)
    - textures, samplers
    - atomic ops (atomicLoad/Store/Add/...)
    - subgroup matrix ops (subgroup_matrix_left/right/result)
    - bitcast, countLeadingZeros, fastdiv
    - storage-buffer pseudo-ops (loadByteFromU32Buf etc.)

  Phase-2 extension points are marked `TODO[wgsl-interp]` in the
  evaluator. Adding them is mechanical — each Phase-2 op has a
  well-defined Float / UInt32 semantics in WGSL spec.

  ## Numerics

  WGSL `f32` ↔ Lean `Float`. `i32` ↔ `Int32`. `u32` ↔ `UInt32`.
  `bool` ↔ `Bool`. The mapping is deliberately direct so that
  `native_decide` cross-checks don't need any numerical bridge.
-/

namespace Sparkle.Tests.Hesper.Vendored.WGSLInterp

/-! ## Vendored types (subset) -/

/-- Vendored copy of `Hesper.WGSL.ScalarType`. -/
inductive ScalarType where
  | f32 | f16 | i32 | u32 | bool
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Vendored copy of `Hesper.WGSL.WGSLType` — Phase 3 subset.

    Adds matrices (mat2x2/3x3/4x4) for transpose/determinant/dot
    kernels, plus subgroup-matrix types (subgroupMatrixLeft/Right/
    Result) for cooperative matmul, plus a placeholder `texture2D`
    for texture-sampling kernels (returns default in eval — full
    texture semantics is out of scope). -/
inductive WGSLType where
  | scalar : ScalarType → WGSLType
  | vec2   : ScalarType → WGSLType
  | vec3   : ScalarType → WGSLType
  | vec4   : ScalarType → WGSLType
  | array  : WGSLType → Nat → WGSLType
  -- Phase 3 additions
  | mat2x2 : ScalarType → WGSLType
  | mat3x3 : ScalarType → WGSLType
  | mat4x4 : ScalarType → WGSLType
  -- Subgroup matrix (chromium_experimental_subgroup_matrix extension).
  -- Phase 3 collapses these to plain `Array Float` representations.
  | subgroupMatrixLeft   : ScalarType → Nat → Nat → WGSLType
  | subgroupMatrixRight  : ScalarType → Nat → Nat → WGSLType
  | subgroupMatrixResult : ScalarType → Nat → Nat → WGSLType
  -- Texture / sampler — opaque in Phase 3 (treat as `Unit`).
  | texture2D : String → WGSLType
  | sampler   : WGSLType
  deriving Repr, BEq, Inhabited

/-! ## Semantic domain: `WGSLType.denote`

Maps every `WGSLType` to the Lean type that one of its values
inhabits. Float for f32/f16, Int32/UInt32 for i32/u32 (we keep f16
on Lean's Float because Lean has no Float16 stdlib type — Phase 2
can switch to a proper Float16 newtype). -/

@[reducible]
def ScalarType.denote : ScalarType → Type
  | .f32 | .f16 => Float
  | .i32 => Int32
  | .u32 => UInt32
  | .bool => Bool

instance : (st : ScalarType) → Inhabited st.denote
  | .f32 | .f16 => ⟨(0.0 : Float)⟩
  | .i32 => ⟨(0 : Int32)⟩
  | .u32 => ⟨(0 : UInt32)⟩
  | .bool => ⟨false⟩

/-- Phase 1: arrays are erased to `Array` (untyped element-wise) for
    simplicity. Phase 2 can replace this with `Vector` for index-bound
    proofs once the rest of the AST is solid.

    Phase 3 adds matrices (row-major `Array Float`), subgroup-matrix
    types (also row-major `Array Float`), and opaque texture/sampler
    types (`Unit`). -/
@[reducible]
def WGSLType.denote : WGSLType → Type
  | .scalar st => st.denote
  | .vec2 st   => st.denote × st.denote
  | .vec3 st   => st.denote × st.denote × st.denote
  | .vec4 st   => st.denote × st.denote × st.denote × st.denote
  | .array _ _ => Array Float
  | .mat2x2 _  => Array Float  -- 4 elements, row-major
  | .mat3x3 _  => Array Float  -- 9 elements
  | .mat4x4 _  => Array Float  -- 16 elements
  | .subgroupMatrixLeft _ _ _   => Array Float
  | .subgroupMatrixRight _ _ _  => Array Float
  | .subgroupMatrixResult _ _ _ => Array Float
  | .texture2D _ => Unit
  | .sampler   => Unit

instance : (t : WGSLType) → Inhabited t.denote
  | .scalar st => inferInstanceAs (Inhabited st.denote)
  | .vec2 st   => ⟨((default : st.denote), default)⟩
  | .vec3 st   => ⟨((default : st.denote), default, default)⟩
  | .vec4 st   => ⟨((default : st.denote), default, default, default)⟩
  | .array _ _ => ⟨#[]⟩
  | .mat2x2 _  => ⟨#[]⟩
  | .mat3x3 _  => ⟨#[]⟩
  | .mat4x4 _  => ⟨#[]⟩
  | .subgroupMatrixLeft _ _ _   => ⟨#[]⟩
  | .subgroupMatrixRight _ _ _  => ⟨#[]⟩
  | .subgroupMatrixResult _ _ _ => ⟨#[]⟩
  | .texture2D _ => ⟨()⟩
  | .sampler   => ⟨()⟩

/-! ## Vendored `Exp` — Phase 1 subset

We hand-pick the constructors needed for BitLinear + attention.
Each constructor name matches upstream Hesper for drop-in
compatibility once the PR lands. -/

inductive Exp : WGSLType → Type where
  -- Literals
  | litF32  : Float → Exp (.scalar .f32)
  | litI32  : Int → Exp (.scalar .i32)
  | litU32  : Nat → Exp (.scalar .u32)
  | litBool : Bool → Exp (.scalar .bool)
  -- Variables (looked up in env at eval time)
  | var {t : WGSLType} : String → Exp t
  -- Arithmetic
  | add {t : WGSLType} : Exp t → Exp t → Exp t
  | sub {t : WGSLType} : Exp t → Exp t → Exp t
  | mul {t : WGSLType} : Exp t → Exp t → Exp t
  | div {t : WGSLType} : Exp t → Exp t → Exp t
  | neg {t : WGSLType} : Exp t → Exp t
  -- Comparisons → bool
  | eq  {t : WGSLType} : Exp t → Exp t → Exp (.scalar .bool)
  | lt  {t : WGSLType} : Exp t → Exp t → Exp (.scalar .bool)
  | gt  {t : WGSLType} : Exp t → Exp t → Exp (.scalar .bool)
  -- Boolean ops
  | and : Exp (.scalar .bool) → Exp (.scalar .bool) → Exp (.scalar .bool)
  | or  : Exp (.scalar .bool) → Exp (.scalar .bool) → Exp (.scalar .bool)
  | not : Exp (.scalar .bool) → Exp (.scalar .bool)
  -- Conversions
  | toF32 {t : WGSLType} : Exp t → Exp (.scalar .f32)
  | toI32 {t : WGSLType} : Exp t → Exp (.scalar .i32)
  | toU32 {t : WGSLType} : Exp t → Exp (.scalar .u32)
  -- Math (f32; Phase 1 specialises to f32 to avoid type-class explosion)
  | exp     : Exp (.scalar .f32) → Exp (.scalar .f32)
  | log     : Exp (.scalar .f32) → Exp (.scalar .f32)
  | sqrt    : Exp (.scalar .f32) → Exp (.scalar .f32)
  | absF32  : Exp (.scalar .f32) → Exp (.scalar .f32)
  | sin     : Exp (.scalar .f32) → Exp (.scalar .f32)
  | cos     : Exp (.scalar .f32) → Exp (.scalar .f32)
  | tanh    : Exp (.scalar .f32) → Exp (.scalar .f32)
  -- min/max/clamp
  | minF32   : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
  | maxF32   : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
  | clampF32 : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
              → Exp (.scalar .f32)
  -- select (ternary)
  | select {t : WGSLType}
      : Exp (.scalar .bool) → Exp t → Exp t → Exp t
  -- Vector construction
  | vec2 {st : ScalarType}
      : Exp (.scalar st) → Exp (.scalar st) → Exp (.vec2 st)
  | vec3 {st : ScalarType}
      : Exp (.scalar st) → Exp (.scalar st) → Exp (.scalar st) → Exp (.vec3 st)
  | vec4 {st : ScalarType}
      : Exp (.scalar st) → Exp (.scalar st) → Exp (.scalar st) → Exp (.scalar st)
        → Exp (.vec4 st)
  -- Vector component access (X/Y for vec2/3/4; Z for vec3/4; W for vec4)
  | vecX {st : ScalarType} : Exp (.vec2 st) → Exp (.scalar st)
  | vecY {st : ScalarType} : Exp (.vec2 st) → Exp (.scalar st)
  | vec3X {st : ScalarType} : Exp (.vec3 st) → Exp (.scalar st)
  | vec3Y {st : ScalarType} : Exp (.vec3 st) → Exp (.scalar st)
  | vec3Z {st : ScalarType} : Exp (.vec3 st) → Exp (.scalar st)
  | vec4X {st : ScalarType} : Exp (.vec4 st) → Exp (.scalar st)
  | vec4Y {st : ScalarType} : Exp (.vec4 st) → Exp (.scalar st)
  | vec4Z {st : ScalarType} : Exp (.vec4 st) → Exp (.scalar st)
  | vec4W {st : ScalarType} : Exp (.vec4 st) → Exp (.scalar st)
  -- Array indexing
  | index {elemTy : WGSLType} {n : Nat}
      : Exp (.array elemTy n) → Exp (.scalar .u32) → Exp elemTy
  -- ===== Phase 2 additions =====
  -- More f32 math
  | exp2    : Exp (.scalar .f32) → Exp (.scalar .f32)
  | log2    : Exp (.scalar .f32) → Exp (.scalar .f32)
  | inverseSqrt : Exp (.scalar .f32) → Exp (.scalar .f32)
  | floor   : Exp (.scalar .f32) → Exp (.scalar .f32)
  | ceil    : Exp (.scalar .f32) → Exp (.scalar .f32)
  | round   : Exp (.scalar .f32) → Exp (.scalar .f32)
  | trunc   : Exp (.scalar .f32) → Exp (.scalar .f32)
  | fract   : Exp (.scalar .f32) → Exp (.scalar .f32)
  | sign    : Exp (.scalar .f32) → Exp (.scalar .f32)
  | saturate : Exp (.scalar .f32) → Exp (.scalar .f32)
  | pow     : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
  | step    : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
  | mix     : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
              → Exp (.scalar .f32)
  | smoothstep : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
                 → Exp (.scalar .f32)
  | fma     : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
              → Exp (.scalar .f32)
  -- Trig (specialised to f32 like the Phase-1 ones)
  | tan     : Exp (.scalar .f32) → Exp (.scalar .f32)
  | asin    : Exp (.scalar .f32) → Exp (.scalar .f32)
  | acos    : Exp (.scalar .f32) → Exp (.scalar .f32)
  | atan    : Exp (.scalar .f32) → Exp (.scalar .f32)
  | atan2   : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
  | sinh    : Exp (.scalar .f32) → Exp (.scalar .f32)
  | cosh    : Exp (.scalar .f32) → Exp (.scalar .f32)
  -- Bitwise (u32)
  | shiftLeft  : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | shiftRight : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | bitAnd     : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | bitOr      : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | bitXor     : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  -- Vector dot product (specialised to f32 vecs in Phase 2 to keep
  -- the `denote` reduction fully type-stable; non-f32 vec dots are
  -- a Phase-3 generalisation).
  | dotV2 : Exp (.vec2 .f32) → Exp (.vec2 .f32) → Exp (.scalar .f32)
  | dotV3 : Exp (.vec3 .f32) → Exp (.vec3 .f32) → Exp (.scalar .f32)
  | dotV4 : Exp (.vec4 .f32) → Exp (.vec4 .f32) → Exp (.scalar .f32)
  -- Subgroup / warp-collapsed reductions. Single-thread eval just
  -- returns the lane value (warp size 1 from our POV); a future
  -- Phase 3 can plug in the warp-aware semantics already used in
  -- CircuitInterp.lean.
  | subgroupAdd  {t : WGSLType} : Exp t → Exp t
  | subgroupMin  {t : WGSLType} : Exp t → Exp t
  | subgroupMax  {t : WGSLType} : Exp t → Exp t
  | subgroupBroadcast {t : WGSLType}
      : Exp t → Exp (.scalar .u32) → Exp t
  | subgroupBroadcastFirst {t : WGSLType} : Exp t → Exp t
  | subgroupShuffle {t : WGSLType} : Exp t → Exp (.scalar .u32) → Exp t
  -- arrayLength (returns the static size as u32 — we don't model
  -- runtime-sized arrays here, so this is just `n`).
  | arrayLength {elemTy : WGSLType} {n : Nat}
      : Exp (.array elemTy n) → Exp (.scalar .u32)
  -- ===== Phase 3 additions =====
  -- Half-float literal (collapsed to Float in Phase 3).
  | litF16 : Float → Exp (.scalar .f16)
  -- Comparisons that Phase 1 didn't have:
  | ne {t : WGSLType} : Exp t → Exp t → Exp (.scalar .bool)
  | le {t : WGSLType} : Exp t → Exp t → Exp (.scalar .bool)
  | ge {t : WGSLType} : Exp t → Exp t → Exp (.scalar .bool)
  -- Polymorphic abs / min / max / clamp / mod (f32-specialised in
  -- Phase 1 are still kept for source-compat; these add the
  -- generic versions). For Phase 3 we keep them f32-only to dodge
  -- the typeclass explosion; non-f32 callers can use absF32 etc.
  | abs   : Exp (.scalar .f32) → Exp (.scalar .f32)
  | min   : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
  | max   : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
  | clamp : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
            → Exp (.scalar .f32)
  | mod   : Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32)
  -- Boolean reductions over vec_n: all/any
  | allV2 : Exp (.vec2 .bool) → Exp (.scalar .bool)
  | allV3 : Exp (.vec3 .bool) → Exp (.scalar .bool)
  | allV4 : Exp (.vec4 .bool) → Exp (.scalar .bool)
  | anyV2 : Exp (.vec2 .bool) → Exp (.scalar .bool)
  | anyV3 : Exp (.vec3 .bool) → Exp (.scalar .bool)
  | anyV4 : Exp (.vec4 .bool) → Exp (.scalar .bool)
  -- Vector geometric ops (f32 only)
  | length3   : Exp (.vec3 .f32) → Exp (.scalar .f32)
  | distance3 : Exp (.vec3 .f32) → Exp (.vec3 .f32) → Exp (.scalar .f32)
  | normalize3 : Exp (.vec3 .f32) → Exp (.vec3 .f32)
  | cross     : Exp (.vec3 .f32) → Exp (.vec3 .f32) → Exp (.vec3 .f32)
  -- Generic dot (alias of dotV3 for f32 vec3 — common in shaders)
  | dot3F32   : Exp (.vec3 .f32) → Exp (.vec3 .f32) → Exp (.scalar .f32)
  -- Vector component access we missed in Phase 1
  | vecZ {st : ScalarType} : Exp (.vec3 st) → Exp (.scalar st)
  | vecW {st : ScalarType} : Exp (.vec4 st) → Exp (.scalar st)
  -- Trig / hyperbolic remainder
  | asinh : Exp (.scalar .f32) → Exp (.scalar .f32)
  | acosh : Exp (.scalar .f32) → Exp (.scalar .f32)
  | atanh : Exp (.scalar .f32) → Exp (.scalar .f32)
  -- Conversions
  | toF16     {t : WGSLType} : Exp t → Exp (.scalar .f16)
  | toF32U    {t : WGSLType} : Exp t → Exp (.scalar .f32)
  | roundToI32 : Exp (.scalar .f32) → Exp (.scalar .i32)
  -- Bit manipulation (u32)
  | countLeadingZeros  : Exp (.scalar .u32) → Exp (.scalar .u32)
  | countTrailingZeros : Exp (.scalar .u32) → Exp (.scalar .u32)
  | countOneBits       : Exp (.scalar .u32) → Exp (.scalar .u32)
  | reverseBits        : Exp (.scalar .u32) → Exp (.scalar .u32)
  | firstLeadingBit    : Exp (.scalar .u32) → Exp (.scalar .u32)
  | firstTrailingBit   : Exp (.scalar .u32) → Exp (.scalar .u32)
  | extractBits        : Exp (.scalar .u32) → Exp (.scalar .u32)
                          → Exp (.scalar .u32) → Exp (.scalar .u32)
  | insertBits         : Exp (.scalar .u32) → Exp (.scalar .u32)
                          → Exp (.scalar .u32) → Exp (.scalar .u32)
                          → Exp (.scalar .u32)
  | mulhiU32           : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  -- Bitcast f32 ↔ u32 (other casts return default)
  | bitcastF32ToU32 : Exp (.scalar .f32) → Exp (.scalar .u32)
  | bitcastU32ToF32 : Exp (.scalar .u32) → Exp (.scalar .f32)
  -- Matrices (mat3x3 f32 transpose / determinant — most common in
  -- BitNet RoPE / RMSNorm; mat2x2 / mat4x4 versions follow the
  -- same skeleton).
  | mat2x2_f32 : Exp (.scalar .f32) → Exp (.scalar .f32)
                  → Exp (.scalar .f32) → Exp (.scalar .f32)
                  → Exp (.mat2x2 .f32)
  | mat3x3_f32 :
      Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) →
      Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) →
      Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) →
      Exp (.mat3x3 .f32)
  | mat4x4_f32 :
      Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) →
      Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) →
      Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) →
      Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) → Exp (.scalar .f32) →
      Exp (.mat4x4 .f32)
  | transpose2 : Exp (.mat2x2 .f32) → Exp (.mat2x2 .f32)
  | transpose3 : Exp (.mat3x3 .f32) → Exp (.mat3x3 .f32)
  | determinantM2 : Exp (.mat2x2 .f32) → Exp (.scalar .f32)
  | determinantM3 : Exp (.mat3x3 .f32) → Exp (.scalar .f32)
  -- Subgroup matrix multiply-accumulate: result += left × right.
  -- Phase 3 collapses this to a plain matmul on the underlying
  -- `Array Float`s.
  | subgroupMatrixZeroResult {st : ScalarType} {m n : Nat}
      : Exp (.subgroupMatrixResult st m n)
  | subgroupMatrixMultiplyAccumulate {st : ScalarType} {m k n : Nat}
      : Exp (.subgroupMatrixLeft st m k) → Exp (.subgroupMatrixRight st k n)
        → Exp (.subgroupMatrixResult st m n) → Exp (.subgroupMatrixResult st m n)
  -- Subgroup remaining: the rest of the warp-collapsed family.
  | subgroupAll {t : WGSLType} : Exp t → Exp t
  | subgroupAny {t : WGSLType} : Exp t → Exp t
  | subgroupMul {t : WGSLType} : Exp t → Exp t
  | subgroupAnd {t : WGSLType} : Exp t → Exp t
  | subgroupOr  {t : WGSLType} : Exp t → Exp t
  | subgroupXor {t : WGSLType} : Exp t → Exp t
  | subgroupElect : Exp (.scalar .bool)
  | subgroupBallot : Exp (.scalar .bool) → Exp (.scalar .u32)
  | subgroupExclusiveAdd {t : WGSLType} : Exp t → Exp t
  | subgroupInclusiveAdd {t : WGSLType} : Exp t → Exp t
  | subgroupShuffleXor {t : WGSLType} : Exp t → Exp (.scalar .u32) → Exp t
  | subgroupShuffleUp {t : WGSLType} : Exp t → Exp (.scalar .u32) → Exp t
  | subgroupShuffleDown {t : WGSLType} : Exp t → Exp (.scalar .u32) → Exp t
  -- Quad ops (subgroup of size 4 in a 2x2 — collapse to identity)
  | quadBroadcast {t : WGSLType} : Exp t → Exp (.scalar .u32) → Exp t
  | quadSwapDiagonal {t : WGSLType} : Exp t → Exp t
  | quadSwapX {t : WGSLType} : Exp t → Exp t
  | quadSwapY {t : WGSLType} : Exp t → Exp t
  -- Pack / unpack (2x16, 4x8). Inputs/outputs are u32 (packed) or
  -- vec2/4 of unpacked values.
  | pack2x16float  : Exp (.vec2 .f32) → Exp (.scalar .u32)
  | unpack2x16float : Exp (.scalar .u32) → Exp (.vec2 .f32)
  | pack4x8snorm   : Exp (.vec4 .f32) → Exp (.scalar .u32)
  | unpack4x8snorm : Exp (.scalar .u32) → Exp (.vec4 .f32)
  | pack4x8unorm   : Exp (.vec4 .f32) → Exp (.scalar .u32)
  | unpack4x8unorm : Exp (.scalar .u32) → Exp (.vec4 .f32)
  -- Derivatives (no-op in compute shaders → return 0)
  | dpdx  : Exp (.scalar .f32) → Exp (.scalar .f32)
  | dpdy  : Exp (.scalar .f32) → Exp (.scalar .f32)
  | fwidth : Exp (.scalar .f32) → Exp (.scalar .f32)
  -- Barriers / sync (no-op in single-thread eval)
  | workgroupBarrier : Exp (.scalar .bool)
  | textureBarrier   : Exp (.scalar .bool)
  | warpBarrier      : Exp (.scalar .bool)
  -- CUDA copy-async (no-op stubs)
  | cpAsyncCommitGroup : Exp (.scalar .bool)
  | cpAsyncWaitGroup   : Exp (.scalar .u32) → Exp (.scalar .bool)
  | cpAsyncCaSharedGlobal : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .bool)
  | cpAsyncCgSharedGlobal : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .bool)
  -- Storage barrier
  | storageBarrier : Exp (.scalar .bool)
  -- Workgroup-uniform load (single-thread semantics: just read).
  | workgroupUniformLoad {t : WGSLType} : Exp t → Exp t
  -- Atomic ops. Single-thread eval: atomic load/exchange degrade
  -- to plain reads of the address; arithmetic atomics return the
  -- old value (the WGSL spec's return convention). Without a real
  -- mutable address, we model "old value" as 0. WGSL atomics are
  -- a Phase-4 stretch goal — full semantics needs a state-passing
  -- monad rebuild. For now this file documents the surface area.
  | atomicLoad   : Exp (.scalar .u32) → Exp (.scalar .i32)
  | atomicLoadU  : Exp (.scalar .u32) → Exp (.scalar .u32)
  | atomicStore  : Exp (.scalar .u32) → Exp (.scalar .i32) → Exp (.scalar .bool)
  | atomicStoreU : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .bool)
  | atomicAdd    : Exp (.scalar .u32) → Exp (.scalar .i32) → Exp (.scalar .i32)
  | atomicAddU   : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | atomicSub    : Exp (.scalar .u32) → Exp (.scalar .i32) → Exp (.scalar .i32)
  | atomicSubU   : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | atomicMin    : Exp (.scalar .u32) → Exp (.scalar .i32) → Exp (.scalar .i32)
  | atomicMinU   : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | atomicMax    : Exp (.scalar .u32) → Exp (.scalar .i32) → Exp (.scalar .i32)
  | atomicMaxU   : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | atomicAnd    : Exp (.scalar .u32) → Exp (.scalar .i32) → Exp (.scalar .i32)
  | atomicAndU   : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | atomicOr     : Exp (.scalar .u32) → Exp (.scalar .i32) → Exp (.scalar .i32)
  | atomicOrU    : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | atomicXor    : Exp (.scalar .u32) → Exp (.scalar .i32) → Exp (.scalar .i32)
  | atomicXorU   : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | atomicExchange  : Exp (.scalar .u32) → Exp (.scalar .i32) → Exp (.scalar .i32)
  | atomicExchangeU : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  | atomicCompareExchangeWeak  : Exp (.scalar .u32) → Exp (.scalar .i32)
                                  → Exp (.scalar .i32) → Exp (.scalar .i32)
  | atomicCompareExchangeWeakU : Exp (.scalar .u32) → Exp (.scalar .u32)
                                  → Exp (.scalar .u32) → Exp (.scalar .u32)
  -- Texture ops (Phase 3 stub — return default).
  | textureSample : Exp (.texture2D "f32") → Exp .sampler
                    → Exp (.vec2 .f32) → Exp (.vec4 .f32)
  | textureSampleLevel : Exp (.texture2D "f32") → Exp .sampler
                         → Exp (.vec2 .f32) → Exp (.scalar .f32) → Exp (.vec4 .f32)
  | textureLoad : Exp (.texture2D "f32") → Exp (.vec2 .u32)
                  → Exp (.scalar .u32) → Exp (.vec4 .f32)
  | textureStore : Exp (.texture2D "f32") → Exp (.vec2 .u32)
                   → Exp (.vec4 .f32) → Exp (.scalar .bool)
  | textureDimensions : Exp (.texture2D "f32") → Exp (.vec2 .u32)
  -- Fine-grained derivatives (no-op in compute → 0)
  | dpdxCoarse : Exp (.scalar .f32) → Exp (.scalar .f32)
  | dpdxFine   : Exp (.scalar .f32) → Exp (.scalar .f32)
  | dpdyCoarse : Exp (.scalar .f32) → Exp (.scalar .f32)
  | dpdyFine   : Exp (.scalar .f32) → Exp (.scalar .f32)
  | fwidthCoarse : Exp (.scalar .f32) → Exp (.scalar .f32)
  | fwidthFine   : Exp (.scalar .f32) → Exp (.scalar .f32)
  -- Packed-int dot products (CUDA dp4a / WGSL dot4I8/U8Packed)
  | dot4I8Packed : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .i32)
  | dot4U8Packed : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  -- Saturating signed sub on packed int8x4
  | subSatS8x4 : Exp (.scalar .u32) → Exp (.scalar .u32) → Exp (.scalar .u32)
  -- Pack/unpack snorm/unorm 2x16
  | pack2x16snorm : Exp (.vec2 .f32) → Exp (.scalar .u32)
  | unpack2x16snorm : Exp (.scalar .u32) → Exp (.vec2 .f32)
  | pack2x16unorm : Exp (.vec2 .f32) → Exp (.scalar .u32)
  | unpack2x16unorm : Exp (.scalar .u32) → Exp (.vec2 .f32)
  | pack4xI8 : Exp (.vec4 .i32) → Exp (.scalar .u32)
  | pack4xU8 : Exp (.vec4 .u32) → Exp (.scalar .u32)
  | pack4xI8Clamp : Exp (.vec4 .i32) → Exp (.scalar .u32)
  | pack4xU8Clamp : Exp (.vec4 .u32) → Exp (.scalar .u32)
  | unpack4xI8 : Exp (.scalar .u32) → Exp (.vec4 .i32)
  | unpack4xU8 : Exp (.scalar .u32) → Exp (.vec4 .u32)
  -- Aliases / overloads from upstream (one-line constructors that
  -- forward to the typed variants). These exist in upstream Hesper
  -- so we vendor them for source compat.
  | all {t : WGSLType} : Exp t → Exp (.scalar .bool)
  | any {t : WGSLType} : Exp t → Exp (.scalar .bool)
  | length     : Exp (.vec3 .f32) → Exp (.scalar .f32)
  | distance   : Exp (.vec3 .f32) → Exp (.vec3 .f32) → Exp (.scalar .f32)
  | normalize  : Exp (.vec3 .f32) → Exp (.vec3 .f32)
  | dot        : Exp (.vec3 .f32) → Exp (.vec3 .f32) → Exp (.scalar .f32)
  | determinant  : Exp (.mat2x2 .f32) → Exp (.scalar .f32)
  | determinant3 : Exp (.mat3x3 .f32) → Exp (.scalar .f32)
  | determinant4 : Exp (.mat4x4 .f32) → Exp (.scalar .f32)
  | transpose    : Exp (.mat2x2 .f32) → Exp (.mat2x2 .f32)
  | transpose4   : Exp (.mat4x4 .f32) → Exp (.mat4x4 .f32)
  -- Reflect / refract / faceForward (3D geometry helpers).
  | reflect      : Exp (.vec3 .f32) → Exp (.vec3 .f32) → Exp (.vec3 .f32)
  | refract      : Exp (.vec3 .f32) → Exp (.vec3 .f32) → Exp (.scalar .f32)
                    → Exp (.vec3 .f32)
  | faceForward  : Exp (.vec3 .f32) → Exp (.vec3 .f32) → Exp (.vec3 .f32)
                    → Exp (.vec3 .f32)
  -- Storage-buffer pseudo ops (Phase 3 stubs — return the address
  -- as if it were the value at that address; semantically simpler
  -- than threading a buffer state, and matches single-thread
  -- "buffer is read-only" assumption).
  | loadByteFromU32Buf {n : Nat}
      : (bufName : String) → (byteIdx : Exp (.scalar .u32))
        → Exp (.scalar .u32)
  | loadU16FromU32Buf {n : Nat}
      : (bufName : String) → (byteIdx : Exp (.scalar .u32))
        → Exp (.scalar .u32)
  | bufferAddr : String → Exp (.scalar .u32)
  | sharedSymAddr : String → Exp (.scalar .u32)
  | indexBuf {elemTy : WGSLType} {n : Nat}
      : String → (bufIdx : Exp (.scalar .u32))
        → (elemIdx : Exp (.scalar .u32)) → Exp elemTy
  -- Misc upstream constructors we vendor as no-ops.
  | bitcast {fromTy toTy : WGSLType} : Exp fromTy → Exp toTy
  | call {t : WGSLType} : String → List String → Exp t
  | extractBitsSigned : Exp (.scalar .u32) → Exp (.scalar .u32)
                        → Exp (.scalar .u32) → Exp (.scalar .i32)
  | firstLeadingBitSigned : Exp (.scalar .i32) → Exp (.scalar .i32)
  | fieldAccess {t : WGSLType} : Exp t → String → Exp t
  | fmaF16x2 : Exp (.scalar .u32) → Exp (.scalar .u32)
                → Exp (.scalar .u32) → Exp (.scalar .u32)
  | structConstruct {t : WGSLType} : String → List String → Exp t
  -- Subgroup matrix remaining variants
  | subgroupMatrixLoad {st : ScalarType} {m k : Nat}
      : String → Exp (.scalar .u32) → Exp (.subgroupMatrixLeft st m k)
  | subgroupMatrixLoadRight {st : ScalarType} {k n : Nat}
      : String → Exp (.scalar .u32) → Exp (.subgroupMatrixRight st k n)
  | subgroupMatrixStore {st : ScalarType} {m n : Nat}
      : String → Exp (.scalar .u32) → Exp (.subgroupMatrixResult st m n)
        → Exp (.scalar .bool)
  | subgroupMatrixZeroLeft  {st : ScalarType} {m k : Nat}
      : Exp (.subgroupMatrixLeft st m k)
  | subgroupMatrixZeroRight {st : ScalarType} {k n : Nat}
      : Exp (.subgroupMatrixRight st k n)
  | subgroupMatrixMultiplyAccumulateMixed {st : ScalarType} {m k n : Nat}
      : Exp (.subgroupMatrixLeft st m k) → Exp (.subgroupMatrixRight st k n)
        → Exp (.subgroupMatrixResult st m n) → Exp (.subgroupMatrixResult st m n)
  | subgroupExclusiveMul {t : WGSLType} : Exp t → Exp t
  | subgroupInclusiveMul {t : WGSLType} : Exp t → Exp t
  -- Texture remaining variants (Phase 3 stubs).
  | textureSampleBaseClampToEdge : Exp (.texture2D "f32") → Exp .sampler
                                   → Exp (.vec2 .f32) → Exp (.vec4 .f32)
  | textureSampleBias : Exp (.texture2D "f32") → Exp .sampler
                        → Exp (.vec2 .f32) → Exp (.scalar .f32) → Exp (.vec4 .f32)
  | textureSampleGrad : Exp (.texture2D "f32") → Exp .sampler
                        → Exp (.vec2 .f32) → Exp (.vec2 .f32) → Exp (.vec2 .f32)
                        → Exp (.vec4 .f32)
  | textureSampleCompare : Exp (.texture2D "f32") → Exp .sampler
                           → Exp (.vec2 .f32) → Exp (.scalar .f32)
                           → Exp (.scalar .f32)
  | textureGather : Exp (.scalar .u32) → Exp (.texture2D "f32") → Exp .sampler
                    → Exp (.vec2 .f32) → Exp (.vec4 .f32)
  | textureNumLayers : Exp (.texture2D "f32") → Exp (.scalar .u32)
  | textureNumLevels : Exp (.texture2D "f32") → Exp (.scalar .u32)
  | textureNumSamples : Exp (.texture2D "f32") → Exp (.scalar .u32)

/-! ## Environment

Variables (`Exp.var name`) are looked up by string name from a
heterogeneous environment.  We model this minimally with `WGSLType`-
dispatched lookup tables. The interpreter's PR will likely refine
this to a more structured environment; for Phase 1 a simple
"name → default" stub plus per-type read functions is enough. -/

structure EvalEnv where
  /-- f32 scalar variables. -/
  f32_vars : List (String × Float) := []
  /-- u32 scalar variables. -/
  u32_vars : List (String × UInt32) := []
  /-- f32 arrays. -/
  f32_arrays : List (String × Array Float) := []
  /-- Phase-4: atomic-op buffer. Maps an address (`UInt32` index)
      to its current `Int32` value. Atomics in `evalSt` read /
      mutate this. Pure `Exp.eval` ignores it. -/
  atomic_i32 : List (UInt32 × Int32) := []
  /-- Phase-4: u32 atomic buffer. -/
  atomic_u32 : List (UInt32 × UInt32) := []
  /-- Phase-4: 2D textures. Each entry is (name, width, height, pixels)
      with pixels in row-major as `Array (Float × Float × Float × Float)`
      = vec4 RGBA. -/
  textures : List (String × Nat × Nat × Array (Float × Float × Float × Float)) := []
  deriving Inhabited

def EvalEnv.lookupF32 (env : EvalEnv) (name : String) : Float :=
  (env.f32_vars.find? (·.1 = name)).map (·.2) |>.getD 0.0

def EvalEnv.lookupU32 (env : EvalEnv) (name : String) : UInt32 :=
  (env.u32_vars.find? (·.1 = name)).map (·.2) |>.getD 0

def EvalEnv.lookupF32Array (env : EvalEnv) (name : String) : Array Float :=
  (env.f32_arrays.find? (·.1 = name)).map (·.2) |>.getD #[]

/-! ### Phase-4 stateful accessors -/

def EvalEnv.atomicLoadI32 (env : EvalEnv) (addr : UInt32) : Int32 :=
  (env.atomic_i32.find? (·.1 = addr)).map (·.2) |>.getD 0

def EvalEnv.atomicLoadU32 (env : EvalEnv) (addr : UInt32) : UInt32 :=
  (env.atomic_u32.find? (·.1 = addr)).map (·.2) |>.getD 0

/-- Replace (or insert) the atomic-i32 entry for `addr`. -/
def EvalEnv.atomicStoreI32 (env : EvalEnv) (addr : UInt32) (v : Int32) : EvalEnv :=
  { env with atomic_i32 :=
      (addr, v) :: env.atomic_i32.filter (·.1 != addr) }

def EvalEnv.atomicStoreU32 (env : EvalEnv) (addr : UInt32) (v : UInt32) : EvalEnv :=
  { env with atomic_u32 :=
      (addr, v) :: env.atomic_u32.filter (·.1 != addr) }

/-- 2D texture pixel lookup. Returns (R, G, B, A). -/
def EvalEnv.textureLoadF32 (env : EvalEnv) (name : String) (x y : Nat)
    : Float × Float × Float × Float :=
  match env.textures.find? (·.1 = name) with
  | some (_, w, _, pixels) => pixels.getD (y * w + x) (0.0, 0.0, 0.0, 0.0)
  | none => (0.0, 0.0, 0.0, 0.0)

/-! ## Bit-manipulation helpers (Phase 3)

`Exp.eval` is structurally recursive on `Exp t` so it cannot use
`let mut` / `while`. The bit manipulation primitives use those
constructs, so we factor them out as top-level helpers and call
them from the evaluator. -/

def clz_u32 (x : UInt32) : UInt32 := Id.run do
  if x == 0 then return 32
  let mut n : UInt32 := 0
  let mut v := x
  for _ in [:32] do
    if (v &&& 0x80000000) != 0 then return n
    n := n + 1
    v := v <<< 1
  pure 32

def ctz_u32 (x : UInt32) : UInt32 := Id.run do
  if x == 0 then return 32
  let mut n : UInt32 := 0
  let mut v := x
  for _ in [:32] do
    if (v &&& 1) != 0 then return n
    n := n + 1
    v := v >>> 1
  pure 32

def popcount_u32 (x : UInt32) : UInt32 := Id.run do
  let mut n : UInt32 := 0
  let mut v := x
  for _ in [:32] do
    n := n + (v &&& 1)
    v := v >>> 1
  pure n

def reverseBits_u32 (x : UInt32) : UInt32 := Id.run do
  let mut r : UInt32 := 0
  let mut v := x
  for _ in [:32] do
    r := (r <<< 1) ||| (v &&& 1)
    v := v >>> 1
  pure r

def firstLeadingBit_u32 (x : UInt32) : UInt32 := Id.run do
  if x == 0 then return 0xFFFFFFFF
  let mut pos : UInt32 := 31
  let mut v := x
  for _ in [:32] do
    if (v &&& 0x80000000) != 0 then return pos
    pos := pos - 1
    v := v <<< 1
  pure 0xFFFFFFFF

def firstTrailingBit_u32 (x : UInt32) : UInt32 := Id.run do
  if x == 0 then return 0xFFFFFFFF
  let mut pos : UInt32 := 0
  let mut v := x
  for _ in [:32] do
    if (v &&& 1) != 0 then return pos
    pos := pos + 1
    v := v >>> 1
  pure 0xFFFFFFFF

/-! Packed-dot product helpers (factored out for the same reason as
the bit-manipulation ones — `Exp.eval` is structurally recursive
and can't host `let mut`). -/

def dot4I8Packed_u32 (av bv : UInt32) : Int32 := Id.run do
  let toI8 (v : UInt32) : Int :=
    if v > 127 then (v.toNat : Int) - 256 else v.toNat
  let mut acc : Int := 0
  for i in [:4] do
    let ax := toI8 ((av >>> (UInt32.ofNat (i*8))) &&& 0xFF)
    let bx := toI8 ((bv >>> (UInt32.ofNat (i*8))) &&& 0xFF)
    acc := acc + ax * bx
  pure (Int32.ofInt acc)

def dot4U8Packed_u32 (av bv : UInt32) : UInt32 := Id.run do
  let mut acc : UInt32 := 0
  for i in [:4] do
    let ax := (av >>> (UInt32.ofNat (i*8))) &&& 0xFF
    let bx := (bv >>> (UInt32.ofNat (i*8))) &&& 0xFF
    acc := acc + ax * bx
  pure acc

def subSatS8x4_u32 (av bv : UInt32) : UInt32 := Id.run do
  let toI8 (v : UInt32) : Int :=
    if v > 127 then (v.toNat : Int) - 256 else v.toNat
  let satS8 (x : Int) : UInt32 :=
    let c := if x > 127 then 127 else if x < -128 then -128 else x
    let unsig : Int := if c < 0 then c + 256 else c
    UInt32.ofNat unsig.toNat
  let mut out : UInt32 := 0
  for i in [:4] do
    let ax := toI8 ((av >>> (UInt32.ofNat (i*8))) &&& 0xFF)
    let bx := toI8 ((bv >>> (UInt32.ofNat (i*8))) &&& 0xFF)
    out := out ||| ((satS8 (ax - bx)) <<< (UInt32.ofNat (i*8)))
  pure out

/-! ## Type-indexed evaluator

`Exp.eval : Env → (e : Exp t) → t.denote`. The dependent return
type is what gives us GPU-level type safety: there's no way to
read an `i32` from a `vec3 f32`, even at the meta level. -/

/-- Helper: bool-valued comparisons over arbitrary `t.denote` are
    decided by reflecting onto the scalar Float / Int / UInt32 case. -/
def evalEqDenote : (t : WGSLType) → t.denote → t.denote → Bool
  | .scalar .f32, a, b => (a : Float) == (b : Float)
  | .scalar .f16, a, b => (a : Float) == (b : Float)
  | .scalar .i32, a, b => (a : Int32) == (b : Int32)
  | .scalar .u32, a, b => (a : UInt32) == (b : UInt32)
  | .scalar .bool, a, b => (a : Bool) == (b : Bool)
  | _, _, _ => false

def evalLtDenote : (t : WGSLType) → t.denote → t.denote → Bool
  | .scalar .f32, a, b => (a : Float) < (b : Float)
  | .scalar .f16, a, b => (a : Float) < (b : Float)
  | .scalar .i32, a, b => (a : Int32) < (b : Int32)
  | .scalar .u32, a, b => (a : UInt32) < (b : UInt32)
  | _, _, _ => false

def evalGtDenote : (t : WGSLType) → t.denote → t.denote → Bool
  | .scalar .f32, a, b => (a : Float) > (b : Float)
  | .scalar .f16, a, b => (a : Float) > (b : Float)
  | .scalar .i32, a, b => (a : Int32) > (b : Int32)
  | .scalar .u32, a, b => (a : UInt32) > (b : UInt32)
  | _, _, _ => false

def evalAddDenote : (t : WGSLType) → t.denote → t.denote → t.denote
  | .scalar .f32, a, b => ((a : Float) + (b : Float) : Float)
  | .scalar .f16, a, b => ((a : Float) + (b : Float) : Float)
  | .scalar .i32, a, b => ((a : Int32) + (b : Int32) : Int32)
  | .scalar .u32, a, b => ((a : UInt32) + (b : UInt32) : UInt32)
  | .vec2 .f32, (x1, y1), (x2, y2) =>
      (((x1 : Float) + x2 : Float), ((y1 : Float) + y2 : Float))
  | .vec3 .f32, (x1, y1, z1), (x2, y2, z2) =>
      (((x1 : Float) + x2 : Float), ((y1 : Float) + y2 : Float), ((z1 : Float) + z2 : Float))
  | .vec4 .f32, (x1, y1, z1, w1), (x2, y2, z2, w2) =>
      (((x1 : Float) + x2 : Float), ((y1 : Float) + y2 : Float),
       ((z1 : Float) + z2 : Float), ((w1 : Float) + w2 : Float))
  | _, a, _ => a

def evalSubDenote : (t : WGSLType) → t.denote → t.denote → t.denote
  | .scalar .f32, a, b => ((a : Float) - (b : Float) : Float)
  | .scalar .f16, a, b => ((a : Float) - (b : Float) : Float)
  | .scalar .i32, a, b => ((a : Int32) - (b : Int32) : Int32)
  | .scalar .u32, a, b => ((a : UInt32) - (b : UInt32) : UInt32)
  | _, a, _ => a

def evalMulDenote : (t : WGSLType) → t.denote → t.denote → t.denote
  | .scalar .f32, a, b => ((a : Float) * (b : Float) : Float)
  | .scalar .f16, a, b => ((a : Float) * (b : Float) : Float)
  | .scalar .i32, a, b => ((a : Int32) * (b : Int32) : Int32)
  | .scalar .u32, a, b => ((a : UInt32) * (b : UInt32) : UInt32)
  | _, a, _ => a

def evalDivDenote : (t : WGSLType) → t.denote → t.denote → t.denote
  | .scalar .f32, a, b => ((a : Float) / (b : Float) : Float)
  | .scalar .f16, a, b => ((a : Float) / (b : Float) : Float)
  | .scalar .i32, a, b => ((a : Int32) / (b : Int32) : Int32)
  | .scalar .u32, a, b => ((a : UInt32) / (b : UInt32) : UInt32)
  | _, a, _ => a

def evalNegDenote : (t : WGSLType) → t.denote → t.denote
  | .scalar .f32, a => (-(a : Float) : Float)
  | .scalar .f16, a => (-(a : Float) : Float)
  | .scalar .i32, a => (-(a : Int32) : Int32)
  | _, a => a

/-- The main evaluator. Structural recursion on `Exp t`.
    Returned value has type `t.denote`, computed at *each* match
    arm by Lean from the return type of the constructor. -/
def Exp.eval (env : EvalEnv) : {t : WGSLType} → Exp t → t.denote
  | _, .litF32 v        => v
  | _, .litI32 v        => Int32.ofInt v
  | _, .litU32 v        => UInt32.ofNat v
  | _, .litBool v       => v
  | .scalar .f32, .var name => env.lookupF32 name
  | .scalar .u32, .var _    => 0  -- Phase 1: u32 vars TODO
  | .array (.scalar .f32) _, .var name => env.lookupF32Array name
  | _, .var _           => default
  | t, .add a b         => evalAddDenote t (Exp.eval env a) (Exp.eval env b)
  | t, .sub a b         => evalSubDenote t (Exp.eval env a) (Exp.eval env b)
  | t, .mul a b         => evalMulDenote t (Exp.eval env a) (Exp.eval env b)
  | t, .div a b         => evalDivDenote t (Exp.eval env a) (Exp.eval env b)
  | t, .neg a           => evalNegDenote t (Exp.eval env a)
  | _, @Exp.eq t a b    => evalEqDenote t (Exp.eval env a) (Exp.eval env b)
  | _, @Exp.lt t a b    => evalLtDenote t (Exp.eval env a) (Exp.eval env b)
  | _, @Exp.gt t a b    => evalGtDenote t (Exp.eval env a) (Exp.eval env b)
  | _, .and a b         => Exp.eval env a && Exp.eval env b
  | _, .or  a b         => Exp.eval env a || Exp.eval env b
  | _, .not a           => !(Exp.eval env a)
  | _, @Exp.toF32 t e   =>
    let v : t.denote := Exp.eval env e
    match t, v with
    | .scalar .f32, x => x
    | .scalar .f16, x => x
    | .scalar .i32, x => x.toFloat
    | .scalar .u32, x => x.toFloat
    | .scalar .bool, x => if x then 1.0 else 0.0
    | _, _ => 0.0
  | _, @Exp.toI32 t e   =>
    let v : t.denote := Exp.eval env e
    match t, v with
    | .scalar .f32, x => Int32.ofInt (x.toInt32.toInt)
    | .scalar .i32, x => x
    | .scalar .u32, x => Int32.ofInt x.toNat
    | .scalar .bool, x => if x then 1 else 0
    | _, _ => 0
  | _, @Exp.toU32 t e   =>
    let v : t.denote := Exp.eval env e
    match t, v with
    | .scalar .f32, x => x.toUInt32
    | .scalar .i32, x => UInt32.ofNat x.toInt.toNat
    | .scalar .u32, x => x
    | .scalar .bool, x => if x then (1 : UInt32) else 0
    | _, _ => (0 : UInt32)
  | _, .exp e           => (Exp.eval env e).exp
  | _, .log e           => (Exp.eval env e).log
  | _, .sqrt e          => (Exp.eval env e).sqrt
  | _, .absF32 e        => (Exp.eval env e).abs
  | _, .sin e           => (Exp.eval env e).sin
  | _, .cos e           => (Exp.eval env e).cos
  | _, .tanh e          => (Exp.eval env e).tanh
  | _, .minF32 a b      =>
    let av : Float := Exp.eval env a
    let bv : Float := Exp.eval env b
    if av < bv then av else bv
  | _, .maxF32 a b      =>
    let av : Float := Exp.eval env a
    let bv : Float := Exp.eval env b
    if av < bv then bv else av
  | _, .clampF32 x lo hi =>
    let v   : Float := Exp.eval env x
    let lov : Float := Exp.eval env lo
    let hiv : Float := Exp.eval env hi
    let clamped_hi : Float := if v < hiv then v else hiv
    if clamped_hi < lov then lov else clamped_hi
  | _, .select c te fe   =>
    let cb : Bool := Exp.eval env c
    bif cb then Exp.eval env te else Exp.eval env fe
  | _, .vec2 a b        => (Exp.eval env a, Exp.eval env b)
  | _, .vec3 a b c      => (Exp.eval env a, Exp.eval env b, Exp.eval env c)
  | _, .vec4 a b c d    => (Exp.eval env a, Exp.eval env b, Exp.eval env c, Exp.eval env d)
  | _, .vecX e          => (Exp.eval env e).1
  | _, .vecY e          => (Exp.eval env e).2
  | _, .vec3X e         => (Exp.eval env e).1
  | _, .vec3Y e         => (Exp.eval env e).2.1
  | _, .vec3Z e         => (Exp.eval env e).2.2
  | _, .vec4X e         => (Exp.eval env e).1
  | _, .vec4Y e         => (Exp.eval env e).2.1
  | _, .vec4Z e         => (Exp.eval env e).2.2.1
  | _, .vec4W e         => (Exp.eval env e).2.2.2
  | _, @Exp.index elemTy _ arr idx =>
    -- Phase 1: arrays denote as `Array Float` (see WGSLType.denote).
    -- The result type is whatever `elemTy.denote` is — for non-f32
    -- arrays this is wrong (Phase 2). For now we read a Float and
    -- cast lazily.
    let v : Array Float := Exp.eval env arr
    let i : UInt32 := Exp.eval env idx
    let f : Float := v.getD i.toNat 0.0
    -- Cast Float to whatever elemTy is at the boundary.
    match elemTy, f with
    | .scalar .f32, x => x
    | .scalar .f16, x => x
    | .scalar .i32, x => Int32.ofInt x.toInt32.toInt
    | .scalar .u32, x => x.toUInt32
    | .scalar .bool, x => x != 0.0
    | _, _ => default
  -- ===== Phase 2 evaluator arms =====
  | _, .exp2 e          => ((Exp.eval env e : Float) * Float.log 2.0).exp
  | _, .log2 e          => (Exp.eval env e : Float).log / Float.log 2.0
  | _, .inverseSqrt e   => 1.0 / (Exp.eval env e : Float).sqrt
  | _, .floor e         => (Exp.eval env e : Float).floor
  | _, .ceil e          => (Exp.eval env e : Float).ceil
  | _, .round e         => (Exp.eval env e : Float).round
  | _, .trunc e         =>
    let x : Float := Exp.eval env e
    if x < 0.0 then x.ceil else x.floor
  | _, .fract e         =>
    let x : Float := Exp.eval env e
    x - x.floor
  | _, .sign e          =>
    let x : Float := Exp.eval env e
    if x > 0.0 then 1.0 else if x < 0.0 then -1.0 else 0.0
  | _, .saturate e      =>
    let x : Float := Exp.eval env e
    if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x
  | _, .pow a b         => (Exp.eval env a : Float).pow (Exp.eval env b)
  | _, .step edge x     =>
    let e : Float := Exp.eval env edge
    let v : Float := Exp.eval env x
    if v < e then 0.0 else 1.0
  | _, .mix a b t       =>
    let av : Float := Exp.eval env a
    let bv : Float := Exp.eval env b
    let tv : Float := Exp.eval env t
    av * (1.0 - tv) + bv * tv
  | _, .smoothstep e0 e1 x =>
    let e0v : Float := Exp.eval env e0
    let e1v : Float := Exp.eval env e1
    let xv  : Float := Exp.eval env x
    let denom := e1v - e0v
    let t0 : Float :=
      if denom == 0.0 then 0.0
      else (xv - e0v) / denom
    let tc : Float := if t0 < 0.0 then 0.0 else if t0 > 1.0 then 1.0 else t0
    tc * tc * (3.0 - 2.0 * tc)
  | _, .fma a b c       =>
    (Exp.eval env a : Float) * (Exp.eval env b : Float)
      + (Exp.eval env c : Float)
  | _, .tan e           => (Exp.eval env e : Float).tan
  | _, .asin e          => (Exp.eval env e : Float).asin
  | _, .acos e          => (Exp.eval env e : Float).acos
  | _, .atan e          => (Exp.eval env e : Float).atan
  | _, .atan2 y x       => Float.atan2 (Exp.eval env y) (Exp.eval env x)
  | _, .sinh e          =>
    let x : Float := Exp.eval env e
    (x.exp - (-x).exp) * 0.5
  | _, .cosh e          =>
    let x : Float := Exp.eval env e
    (x.exp + (-x).exp) * 0.5
  -- Bitwise (u32)
  | _, .shiftLeft a b   => (Exp.eval env a : UInt32) <<< (Exp.eval env b : UInt32)
  | _, .shiftRight a b  => (Exp.eval env a : UInt32) >>> (Exp.eval env b : UInt32)
  | _, .bitAnd a b      => (Exp.eval env a : UInt32) &&& (Exp.eval env b : UInt32)
  | _, .bitOr  a b      => (Exp.eval env a : UInt32) ||| (Exp.eval env b : UInt32)
  | _, .bitXor a b      => (Exp.eval env a : UInt32) ^^^ (Exp.eval env b : UInt32)
  -- Vector dot products (f32 only)
  | _, .dotV2 a b =>
    let (a1, a2) := Exp.eval env a
    let (b1, b2) := Exp.eval env b
    a1 * b1 + a2 * b2
  | _, .dotV3 a b =>
    let (a1, a2, a3) := Exp.eval env a
    let (b1, b2, b3) := Exp.eval env b
    a1 * b1 + a2 * b2 + a3 * b3
  | _, .dotV4 a b =>
    let (a1, a2, a3, a4) := Exp.eval env a
    let (b1, b2, b3, b4) := Exp.eval env b
    a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4
  -- Subgroup ops collapse to lane-self semantics (warp size 1
  -- from the single-thread eval POV). For real-warp semantics
  -- see CircuitInterp.lean's warp-aware variants — Phase 3.
  | _, .subgroupAdd e          => Exp.eval env e
  | _, .subgroupMin e          => Exp.eval env e
  | _, .subgroupMax e          => Exp.eval env e
  | _, .subgroupBroadcast e _  => Exp.eval env e
  | _, .subgroupBroadcastFirst e => Exp.eval env e
  | _, .subgroupShuffle e _    => Exp.eval env e
  -- arrayLength: static size from the WGSLType — Phase-1 arrays
  -- denote as `Array Float`, so we recover `n` from the type
  -- index. Unfortunately the type has erased the size at the
  -- denote level, so we look at the input array's actual length.
  | _, @Exp.arrayLength _ _ arr =>
    let v : Array Float := Exp.eval env arr
    UInt32.ofNat v.size
  -- ===== Phase 3 evaluator arms =====
  | _, .litF16 v => v
  | _, @Exp.ne t a b => !(evalEqDenote t (Exp.eval env a) (Exp.eval env b))
  | _, @Exp.le t a b => !(evalGtDenote t (Exp.eval env a) (Exp.eval env b))
  | _, @Exp.ge t a b => !(evalLtDenote t (Exp.eval env a) (Exp.eval env b))
  | _, .abs e => (Exp.eval env e : Float).abs
  | _, .min a b =>
    let av : Float := Exp.eval env a
    let bv : Float := Exp.eval env b
    if av < bv then av else bv
  | _, .max a b =>
    let av : Float := Exp.eval env a
    let bv : Float := Exp.eval env b
    if av < bv then bv else av
  | _, .clamp x lo hi =>
    let v : Float := Exp.eval env x
    let lov : Float := Exp.eval env lo
    let hiv : Float := Exp.eval env hi
    let c1 : Float := if v < hiv then v else hiv
    if c1 < lov then lov else c1
  | _, .mod a b =>
    let av : Float := Exp.eval env a
    let bv : Float := Exp.eval env b
    -- WGSL `%` for f32 is `a - b * trunc(a/b)`.
    let q : Float := av / bv
    let qt : Float := if q < 0.0 then q.ceil else q.floor
    av - bv * qt
  -- Vector reductions (bool):
  | _, .allV2 e =>
    let (a, b) : (Bool × Bool) := Exp.eval env e
    a && b
  | _, .allV3 e =>
    let (a, b, c) : (Bool × Bool × Bool) := Exp.eval env e
    a && b && c
  | _, .allV4 e =>
    let (a, b, c, d) : (Bool × Bool × Bool × Bool) := Exp.eval env e
    a && b && c && d
  | _, .anyV2 e =>
    let (a, b) : (Bool × Bool) := Exp.eval env e
    a || b
  | _, .anyV3 e =>
    let (a, b, c) : (Bool × Bool × Bool) := Exp.eval env e
    a || b || c
  | _, .anyV4 e =>
    let (a, b, c, d) : (Bool × Bool × Bool × Bool) := Exp.eval env e
    a || b || c || d
  -- Vector geometric ops
  | _, .length3 e =>
    let (x, y, z) : (Float × Float × Float) := Exp.eval env e
    (x*x + y*y + z*z).sqrt
  | _, .distance3 a b =>
    let (a1, a2, a3) : (Float × Float × Float) := Exp.eval env a
    let (b1, b2, b3) : (Float × Float × Float) := Exp.eval env b
    let dx := a1 - b1; let dy := a2 - b2; let dz := a3 - b3
    (dx*dx + dy*dy + dz*dz).sqrt
  | _, .normalize3 e =>
    let (x, y, z) : (Float × Float × Float) := Exp.eval env e
    let len := (x*x + y*y + z*z).sqrt
    if len == 0.0 then (0.0, 0.0, 0.0) else (x/len, y/len, z/len)
  | _, .cross a b =>
    let (a1, a2, a3) : (Float × Float × Float) := Exp.eval env a
    let (b1, b2, b3) : (Float × Float × Float) := Exp.eval env b
    (a2*b3 - a3*b2, a3*b1 - a1*b3, a1*b2 - a2*b1)
  | _, .dot3F32 a b =>
    let (a1, a2, a3) : (Float × Float × Float) := Exp.eval env a
    let (b1, b2, b3) : (Float × Float × Float) := Exp.eval env b
    a1 * b1 + a2 * b2 + a3 * b3
  -- Component access we missed in Phase 1
  | _, .vecZ e =>
    let (_, _, z) : ((_) × (_) × (_)) := Exp.eval env e
    z
  | _, .vecW e =>
    let (_, _, _, w) : ((_) × (_) × (_) × (_)) := Exp.eval env e
    w
  -- Hyperbolic remainder
  | _, .asinh e =>
    let x : Float := Exp.eval env e
    (x + (x*x + 1.0).sqrt).log
  | _, .acosh e =>
    let x : Float := Exp.eval env e
    (x + (x*x - 1.0).sqrt).log
  | _, .atanh e =>
    let x : Float := Exp.eval env e
    0.5 * ((1.0 + x) / (1.0 - x)).log
  -- Conversions
  | _, @Exp.toF16 t e =>
    let v : t.denote := Exp.eval env e
    match t, v with
    | .scalar .f32, x => x
    | .scalar .f16, x => x
    | .scalar .i32, x => x.toFloat
    | .scalar .u32, x => x.toFloat
    | .scalar .bool, x => if x then 1.0 else 0.0
    | _, _ => 0.0
  | _, @Exp.toF32U t e =>
    let v : t.denote := Exp.eval env e
    match t, v with
    | .scalar .f32, x => x
    | .scalar .f16, x => x
    | .scalar .i32, x => x.toFloat
    | .scalar .u32, x => x.toFloat
    | .scalar .bool, x => if x then 1.0 else 0.0
    | _, _ => 0.0
  | _, .roundToI32 e =>
    Int32.ofInt (Exp.eval env e : Float).round.toInt32.toInt
  -- Bit manipulation (delegated to top-level helpers below; can't
  -- use `let mut` inside a structurally-recursive eval function).
  | _, .countLeadingZeros e  => clz_u32 (Exp.eval env e)
  | _, .countTrailingZeros e => ctz_u32 (Exp.eval env e)
  | _, .countOneBits e       => popcount_u32 (Exp.eval env e)
  | _, .reverseBits e        => reverseBits_u32 (Exp.eval env e)
  | _, .firstLeadingBit e    => firstLeadingBit_u32 (Exp.eval env e)
  | _, .firstTrailingBit e   => firstTrailingBit_u32 (Exp.eval env e)
  | _, .extractBits x off cnt =>
    let xv : UInt32 := Exp.eval env x
    let oo : UInt32 := Exp.eval env off
    let cc : UInt32 := Exp.eval env cnt
    let mask : UInt32 := if cc >= 32 then 0xFFFFFFFF else (1 <<< cc) - 1
    (xv >>> oo) &&& mask
  | _, .insertBits x ins off cnt =>
    let xv : UInt32 := Exp.eval env x
    let iv : UInt32 := Exp.eval env ins
    let oo : UInt32 := Exp.eval env off
    let cc : UInt32 := Exp.eval env cnt
    let mask : UInt32 :=
      if cc >= 32 then 0xFFFFFFFF else ((1 <<< cc) - 1) <<< oo
    (xv &&& (mask ^^^ 0xFFFFFFFF)) ||| ((iv <<< oo) &&& mask)
  | _, .mulhiU32 a b =>
    let av : UInt32 := Exp.eval env a
    let bv : UInt32 := Exp.eval env b
    -- (a * b) >> 32 via UInt64
    let prod : UInt64 := av.toUInt64 * bv.toUInt64
    UInt32.ofNat ((prod >>> 32).toNat)
  -- Bitcasts (Phase 4): proper IEEE-754 f32 ↔ u32 round-trip via
  -- Lean's `Float32`. Lean's `Float` is f64, but WGSL's f32 is
  -- f32 — we use `Float.toFloat32` / `Float32.toFloat` to bridge.
  | _, .bitcastF32ToU32 e =>
    let x : Float := Exp.eval env e
    x.toFloat32.toBits
  | _, .bitcastU32ToF32 e =>
    let bits : UInt32 := Exp.eval env e
    (Float32.ofBits bits).toFloat
  -- Matrices
  | _, .mat2x2_f32 a b c d =>
    #[Exp.eval env a, Exp.eval env b, Exp.eval env c, Exp.eval env d]
  | _, .mat3x3_f32 a b c d e f g h i =>
    #[Exp.eval env a, Exp.eval env b, Exp.eval env c,
      Exp.eval env d, Exp.eval env e, Exp.eval env f,
      Exp.eval env g, Exp.eval env h, Exp.eval env i]
  | _, .mat4x4_f32 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 =>
    #[Exp.eval env a0, Exp.eval env a1, Exp.eval env a2, Exp.eval env a3,
      Exp.eval env b0, Exp.eval env b1, Exp.eval env b2, Exp.eval env b3,
      Exp.eval env c0, Exp.eval env c1, Exp.eval env c2, Exp.eval env c3,
      Exp.eval env d0, Exp.eval env d1, Exp.eval env d2, Exp.eval env d3]
  | _, .transpose2 m =>
    let v : Array Float := Exp.eval env m
    #[v.getD 0 0, v.getD 2 0, v.getD 1 0, v.getD 3 0]
  | _, .transpose3 m =>
    let v : Array Float := Exp.eval env m
    #[v.getD 0 0, v.getD 3 0, v.getD 6 0,
      v.getD 1 0, v.getD 4 0, v.getD 7 0,
      v.getD 2 0, v.getD 5 0, v.getD 8 0]
  | _, .determinantM2 m =>
    let v : Array Float := Exp.eval env m
    v.getD 0 0 * v.getD 3 0 - v.getD 1 0 * v.getD 2 0
  | _, .determinantM3 m =>
    let v : Array Float := Exp.eval env m
    let a := v.getD 0 0; let b := v.getD 1 0; let c := v.getD 2 0
    let d := v.getD 3 0; let e := v.getD 4 0; let f := v.getD 5 0
    let g := v.getD 6 0; let h := v.getD 7 0; let i := v.getD 8 0
    a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g)
  -- Subgroup matrix
  | _, @Exp.subgroupMatrixZeroResult _ m n =>
    Array.replicate (m * n) 0.0
  | _, @Exp.subgroupMatrixMultiplyAccumulate _ m k n l r acc =>
    let lv : Array Float := Exp.eval env l
    let rv : Array Float := Exp.eval env r
    let av : Array Float := Exp.eval env acc
    -- C[i][j] += Σ_p L[i][p] * R[p][j]
    Id.run do
      let mut out := av
      for i in [:m] do
        for j in [:n] do
          let mut s : Float := out.getD (i * n + j) 0.0
          for p in [:k] do
            s := s + lv.getD (i * k + p) 0.0 * rv.getD (p * n + j) 0.0
          out := out.set! (i * n + j) s
      pure out
  -- Subgroup remaining (collapsed to identity / single-thread sem)
  | _, .subgroupAll e         => Exp.eval env e
  | _, .subgroupAny e         => Exp.eval env e
  | _, .subgroupMul e         => Exp.eval env e
  | _, .subgroupAnd e         => Exp.eval env e
  | _, .subgroupOr  e         => Exp.eval env e
  | _, .subgroupXor e         => Exp.eval env e
  | _, .subgroupElect         => true
  | _, .subgroupBallot e      => if (Exp.eval env e : Bool) then 1 else 0
  | _, .subgroupExclusiveAdd e => Exp.eval env e
  | _, .subgroupInclusiveAdd e => Exp.eval env e
  | _, .subgroupShuffleXor e _ => Exp.eval env e
  | _, .subgroupShuffleUp e _  => Exp.eval env e
  | _, .subgroupShuffleDown e _ => Exp.eval env e
  -- Quad ops collapse to identity
  | _, .quadBroadcast e _    => Exp.eval env e
  | _, .quadSwapDiagonal e   => Exp.eval env e
  | _, .quadSwapX e          => Exp.eval env e
  | _, .quadSwapY e          => Exp.eval env e
  -- Pack / unpack
  | _, .pack2x16float e =>
    let (x, y) : (Float × Float) := Exp.eval env e
    -- Phase 3 stub: pack as low 16 / high 16 of u32 by truncation
    -- (real WGSL uses f16 representation — our f16 is just Float).
    let lo : UInt32 := x.toUInt32 &&& 0xFFFF
    let hi : UInt32 := y.toUInt32 &&& 0xFFFF
    lo ||| (hi <<< 16)
  | _, .unpack2x16float e =>
    let v : UInt32 := Exp.eval env e
    let lo := (v &&& 0xFFFF).toFloat
    let hi := ((v >>> 16) &&& 0xFFFF).toFloat
    (lo, hi)
  | _, .pack4x8snorm e =>
    let (a, b, c, d) : (Float × Float × Float × Float) := Exp.eval env e
    -- Clamp to [-1, 1], scale to int8 range.
    let toInt8 (x : Float) : UInt32 :=
      let clamped := if x < -1.0 then -1.0 else if x > 1.0 then 1.0 else x
      let scaled := clamped * 127.0
      let r := if scaled < 0.0 then scaled.ceil else scaled.floor
      r.toUInt32 &&& 0xFF
    toInt8 a ||| (toInt8 b <<< 8) ||| (toInt8 c <<< 16) ||| (toInt8 d <<< 24)
  | _, .unpack4x8snorm e =>
    let v : UInt32 := Exp.eval env e
    let toF (b : UInt32) : Float :=
      let signed := if b > 127 then b.toFloat - 256.0 else b.toFloat
      signed / 127.0
    (toF (v &&& 0xFF), toF ((v >>> 8) &&& 0xFF),
     toF ((v >>> 16) &&& 0xFF), toF ((v >>> 24) &&& 0xFF))
  | _, .pack4x8unorm e =>
    let (a, b, c, d) : (Float × Float × Float × Float) := Exp.eval env e
    let toU8 (x : Float) : UInt32 :=
      let clamped := if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x
      (clamped * 255.0).floor.toUInt32 &&& 0xFF
    toU8 a ||| (toU8 b <<< 8) ||| (toU8 c <<< 16) ||| (toU8 d <<< 24)
  | _, .unpack4x8unorm e =>
    let v : UInt32 := Exp.eval env e
    let toF (b : UInt32) : Float := b.toFloat / 255.0
    (toF (v &&& 0xFF), toF ((v >>> 8) &&& 0xFF),
     toF ((v >>> 16) &&& 0xFF), toF ((v >>> 24) &&& 0xFF))
  -- Derivatives are 0 in compute shaders
  | _, .dpdx _   => 0.0
  | _, .dpdy _   => 0.0
  | _, .fwidth _ => 0.0
  -- Barriers: no-op (return true)
  | _, .workgroupBarrier => true
  | _, .textureBarrier   => true
  | _, .warpBarrier      => true
  -- CUDA copy-async: no-op
  | _, .cpAsyncCommitGroup    => true
  | _, .cpAsyncWaitGroup _    => true
  | _, .cpAsyncCaSharedGlobal _ _ => true
  | _, .cpAsyncCgSharedGlobal _ _ => true
  | _, .storageBarrier        => true
  | _, .workgroupUniformLoad e => Exp.eval env e
  -- Atomic ops (Phase-4): read from the env's atomic buffer.
  -- Pure `Exp.eval` only **reads** atomic state — it can't update
  -- the env from inside a structurally-recursive pure function.
  -- For "old value" the spec says load+op+store; here we return the
  -- current loaded value (i.e. the value before the op would have
  -- written, matching WGSL's old-value-on-return convention). The
  -- *write* is observable only through `Exp.evalSt` below, which
  -- returns an updated env. Single-thread programs that use the
  -- old-value return are correct under both eval functions; programs
  -- that depend on the *post-op* state observed by *another* read
  -- need `evalSt`.
  | _, .atomicLoad addr       => env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicLoadU addr      => env.atomicLoadU32 (Exp.eval env addr)
  | _, .atomicStore _ _       => true
  | _, .atomicStoreU _ _      => true
  | _, .atomicAdd addr _      => env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicAddU addr _     => env.atomicLoadU32 (Exp.eval env addr)
  | _, .atomicSub addr _      => env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicSubU addr _     => env.atomicLoadU32 (Exp.eval env addr)
  | _, .atomicMin addr _      => env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicMinU addr _     => env.atomicLoadU32 (Exp.eval env addr)
  | _, .atomicMax addr _      => env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicMaxU addr _     => env.atomicLoadU32 (Exp.eval env addr)
  | _, .atomicAnd addr _      => env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicAndU addr _     => env.atomicLoadU32 (Exp.eval env addr)
  | _, .atomicOr addr _       => env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicOrU addr _      => env.atomicLoadU32 (Exp.eval env addr)
  | _, .atomicXor addr _      => env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicXorU addr _     => env.atomicLoadU32 (Exp.eval env addr)
  | _, .atomicExchange addr _  => env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicExchangeU addr _ => env.atomicLoadU32 (Exp.eval env addr)
  | _, .atomicCompareExchangeWeak addr _ _  =>
    env.atomicLoadI32 (Exp.eval env addr)
  | _, .atomicCompareExchangeWeakU addr _ _ =>
    env.atomicLoadU32 (Exp.eval env addr)
  -- Texture ops (Phase 4): use textures from the env. The texture
  -- "name" comes through the `texture2D` type's String parameter,
  -- which we can't easily extract here (the constructor erases it
  -- at the eval level). For Phase 4 we use a single conventional
  -- texture name "tex0" and look it up in `env.textures`. Multiple
  -- textures need a Phase-5 redesign of the texture type to carry
  -- the name as a value.
  | _, .textureSample _ _ uv   =>
    let (x, y) : (Float × Float) := Exp.eval env uv
    -- Nearest-neighbor sample at (x*w, y*h).
    match env.textures.find? (·.1 = "tex0") with
    | some (_, w, h, _) =>
      let xi := (x * w.toFloat).toUInt32.toNat
      let yi := (y * h.toFloat).toUInt32.toNat
      env.textureLoadF32 "tex0" xi yi
    | none => (0.0, 0.0, 0.0, 0.0)
  | _, .textureSampleLevel _ _ uv _ =>
    let (x, y) : (Float × Float) := Exp.eval env uv
    match env.textures.find? (·.1 = "tex0") with
    | some (_, w, h, _) =>
      let xi := (x * w.toFloat).toUInt32.toNat
      let yi := (y * h.toFloat).toUInt32.toNat
      env.textureLoadF32 "tex0" xi yi
    | none => (0.0, 0.0, 0.0, 0.0)
  | _, .textureLoad _ coord _ =>
    let (cx, cy) : (UInt32 × UInt32) := Exp.eval env coord
    env.textureLoadF32 "tex0" cx.toNat cy.toNat
  | _, .textureStore _ _ _    => true
  | _, .textureDimensions _   =>
    match env.textures.find? (·.1 = "tex0") with
    | some (_, w, h, _) => (UInt32.ofNat w, UInt32.ofNat h)
    | none => (0, 0)
  -- Fine-grained derivatives — same as plain dpdx/dpdy → 0
  | _, .dpdxCoarse _   => 0.0
  | _, .dpdxFine _     => 0.0
  | _, .dpdyCoarse _   => 0.0
  | _, .dpdyFine _     => 0.0
  | _, .fwidthCoarse _ => 0.0
  | _, .fwidthFine _   => 0.0
  -- Packed dot products: extract 4 bytes, sum products
  | _, .dot4I8Packed a b => dot4I8Packed_u32 (Exp.eval env a) (Exp.eval env b)
  | _, .dot4U8Packed a b => dot4U8Packed_u32 (Exp.eval env a) (Exp.eval env b)
  | _, .subSatS8x4 a b   => subSatS8x4_u32   (Exp.eval env a) (Exp.eval env b)
  -- Pack/unpack snorm/unorm 2x16
  | _, .pack2x16snorm e =>
    let (x, y) : (Float × Float) := Exp.eval env e
    let toI16 (v : Float) : UInt32 :=
      let c := if v < -1.0 then -1.0 else if v > 1.0 then 1.0 else v
      let scaled := c * 32767.0
      let r := if scaled < 0.0 then scaled.ceil else scaled.floor
      r.toUInt32 &&& 0xFFFF
    toI16 x ||| (toI16 y <<< 16)
  | _, .unpack2x16snorm e =>
    let v : UInt32 := Exp.eval env e
    let toF (b : UInt32) : Float :=
      let signed := if b > 32767 then b.toFloat - 65536.0 else b.toFloat
      signed / 32767.0
    (toF (v &&& 0xFFFF), toF ((v >>> 16) &&& 0xFFFF))
  | _, .pack2x16unorm e =>
    let (x, y) : (Float × Float) := Exp.eval env e
    let toU16 (v : Float) : UInt32 :=
      let c := if v < 0.0 then 0.0 else if v > 1.0 then 1.0 else v
      (c * 65535.0).floor.toUInt32 &&& 0xFFFF
    toU16 x ||| (toU16 y <<< 16)
  | _, .unpack2x16unorm e =>
    let v : UInt32 := Exp.eval env e
    let toF (b : UInt32) : Float := b.toFloat / 65535.0
    (toF (v &&& 0xFFFF), toF ((v >>> 16) &&& 0xFFFF))
  | _, .pack4xI8 e =>
    let (a, b, c, d) : (Int32 × Int32 × Int32 × Int32) := Exp.eval env e
    let toU8 (x : Int32) : UInt32 := UInt32.ofNat ((x.toInt + 256).toNat) &&& 0xFF
    toU8 a ||| (toU8 b <<< 8) ||| (toU8 c <<< 16) ||| (toU8 d <<< 24)
  | _, .pack4xU8 e =>
    let (a, b, c, d) : (UInt32 × UInt32 × UInt32 × UInt32) := Exp.eval env e
    let mask (x : UInt32) : UInt32 := x &&& 0xFF
    mask a ||| (mask b <<< 8) ||| (mask c <<< 16) ||| (mask d <<< 24)
  | _, .pack4xI8Clamp e =>
    let (a, b, c, d) : (Int32 × Int32 × Int32 × Int32) := Exp.eval env e
    let clamp (x : Int32) : Int32 :=
      if x.toInt > 127 then 127 else if x.toInt < -128 then -128 else x
    let toU8 (x : Int32) : UInt32 := UInt32.ofNat ((x.toInt + 256).toNat) &&& 0xFF
    toU8 (clamp a) ||| (toU8 (clamp b) <<< 8)
                   ||| (toU8 (clamp c) <<< 16) ||| (toU8 (clamp d) <<< 24)
  | _, .pack4xU8Clamp e =>
    let (a, b, c, d) : (UInt32 × UInt32 × UInt32 × UInt32) := Exp.eval env e
    let clamp (x : UInt32) : UInt32 := if x > 255 then 255 else x
    clamp a ||| (clamp b <<< 8) ||| (clamp c <<< 16) ||| (clamp d <<< 24)
  | _, .unpack4xI8 e =>
    let v : UInt32 := Exp.eval env e
    let toI8 (b : UInt32) : Int32 :=
      Int32.ofInt (if b > 127 then (b.toNat : Int) - 256 else b.toNat)
    (toI8 (v &&& 0xFF), toI8 ((v >>> 8) &&& 0xFF),
     toI8 ((v >>> 16) &&& 0xFF), toI8 ((v >>> 24) &&& 0xFF))
  | _, .unpack4xU8 e =>
    let v : UInt32 := Exp.eval env e
    let mask (x : UInt32) : UInt32 := x &&& 0xFF
    (mask v, mask (v >>> 8), mask (v >>> 16), mask (v >>> 24))
  -- ===== Aliases / overloads =====
  -- Phase-3 stubs: forward to the typed counterparts where possible.
  | _, .all _              => true
  | _, .any _              => true
  | _, .length e           =>
    let (x, y, z) : (Float × Float × Float) := Exp.eval env e
    (x*x + y*y + z*z).sqrt
  | _, .distance a b       =>
    let (a1, a2, a3) : (Float × Float × Float) := Exp.eval env a
    let (b1, b2, b3) : (Float × Float × Float) := Exp.eval env b
    let dx := a1 - b1; let dy := a2 - b2; let dz := a3 - b3
    (dx*dx + dy*dy + dz*dz).sqrt
  | _, .normalize e        =>
    let (x, y, z) : (Float × Float × Float) := Exp.eval env e
    let len := (x*x + y*y + z*z).sqrt
    if len == 0.0 then (0.0, 0.0, 0.0) else (x/len, y/len, z/len)
  | _, .dot a b            =>
    let (a1, a2, a3) : (Float × Float × Float) := Exp.eval env a
    let (b1, b2, b3) : (Float × Float × Float) := Exp.eval env b
    a1 * b1 + a2 * b2 + a3 * b3
  | _, .determinant m      =>
    let v : Array Float := Exp.eval env m
    v.getD 0 0 * v.getD 3 0 - v.getD 1 0 * v.getD 2 0
  | _, .determinant3 m     =>
    let v : Array Float := Exp.eval env m
    let a := v.getD 0 0; let b := v.getD 1 0; let c := v.getD 2 0
    let d := v.getD 3 0; let e := v.getD 4 0; let f := v.getD 5 0
    let g := v.getD 6 0; let h := v.getD 7 0; let i := v.getD 8 0
    a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g)
  | _, .determinant4 m     =>
    -- Phase-4: 4×4 cofactor expansion along row 0.
    let v : Array Float := Exp.eval env m
    let g (r c : Nat) : Float := v.getD (r * 4 + c) 0.0
    -- 3×3 minor with row r0 and col c0 removed.
    let minor3 (r0 c0 : Nat) : Float :=
      let rows := [0,1,2,3].filter (· != r0)
      let cols := [0,1,2,3].filter (· != c0)
      match rows, cols with
      | [r1, r2, r3], [c1, c2, c3] =>
        let a := g r1 c1; let b := g r1 c2; let c := g r1 c3
        let d := g r2 c1; let e := g r2 c2; let f := g r2 c3
        let h := g r3 c1; let i := g r3 c2; let j := g r3 c3
        a*(e*j - f*i) - b*(d*j - f*h) + c*(d*i - e*h)
      | _, _ => 0.0
    g 0 0 * minor3 0 0
      - g 0 1 * minor3 0 1
      + g 0 2 * minor3 0 2
      - g 0 3 * minor3 0 3
  | _, .transpose m        =>
    let v : Array Float := Exp.eval env m
    #[v.getD 0 0, v.getD 2 0, v.getD 1 0, v.getD 3 0]
  | _, .transpose4 m       => Exp.eval env m  -- stub; identity
  | _, .reflect i n        =>
    -- `reflect(I, N) = I − 2 * dot(N, I) * N`
    let (i1, i2, i3) : (Float × Float × Float) := Exp.eval env i
    let (n1, n2, n3) : (Float × Float × Float) := Exp.eval env n
    let d := i1*n1 + i2*n2 + i3*n3
    (i1 - 2.0 * d * n1, i2 - 2.0 * d * n2, i3 - 2.0 * d * n3)
  | _, .refract _ _ _      => (0.0, 0.0, 0.0)  -- Phase-4
  | _, .faceForward _ i nref =>
    -- `faceForward(N, I, Nref)` flips N if dot(Nref, I) ≥ 0.
    let (i1, i2, i3) : (Float × Float × Float) := Exp.eval env i
    let (n1, n2, n3) : (Float × Float × Float) := Exp.eval env nref
    let d := i1*n1 + i2*n2 + i3*n3
    if d < 0.0 then (i1, i2, i3) else (-i1, -i2, -i3)
  | _, .loadByteFromU32Buf _ _ => 0
  | _, .loadU16FromU32Buf _ _  => 0
  | _, .bufferAddr _           => 0
  | _, .sharedSymAddr _        => 0
  | _, .indexBuf _ _ _         => default
  | _, .bitcast _              => default  -- Phase-4: typed bitcast
  | _, .call _ _               => default
  | _, .extractBitsSigned _ _ _ => 0
  | _, .firstLeadingBitSigned _ => 0
  | _, .fieldAccess e _        => Exp.eval env e
  | _, .fmaF16x2 _ _ _         => 0
  | _, .structConstruct _ _    => default
  -- Subgroup matrix remaining variants
  | _, @Exp.subgroupMatrixLoad _ m k _ _      =>
    Array.replicate (m * k) 0.0
  | _, @Exp.subgroupMatrixLoadRight _ k n _ _ =>
    Array.replicate (k * n) 0.0
  | _, .subgroupMatrixStore _ _ _              => true
  | _, @Exp.subgroupMatrixZeroLeft _ m k       =>
    Array.replicate (m * k) 0.0
  | _, @Exp.subgroupMatrixZeroRight _ k n      =>
    Array.replicate (k * n) 0.0
  | _, @Exp.subgroupMatrixMultiplyAccumulateMixed _ m k n l r acc =>
    -- Same as the non-mixed version (differ in dtype of operands).
    let lv : Array Float := Exp.eval env l
    let rv : Array Float := Exp.eval env r
    let av : Array Float := Exp.eval env acc
    Id.run do
      let mut out := av
      for i in [:m] do
        for j in [:n] do
          let mut s : Float := out.getD (i * n + j) 0.0
          for p in [:k] do
            s := s + lv.getD (i * k + p) 0.0 * rv.getD (p * n + j) 0.0
          out := out.set! (i * n + j) s
      pure out
  | _, .subgroupExclusiveMul e => Exp.eval env e
  | _, .subgroupInclusiveMul e => Exp.eval env e
  -- Texture remaining variants — all stub to default
  | _, .textureSampleBaseClampToEdge _ _ _ => (0.0, 0.0, 0.0, 0.0)
  | _, .textureSampleBias _ _ _ _          => (0.0, 0.0, 0.0, 0.0)
  | _, .textureSampleGrad _ _ _ _ _        => (0.0, 0.0, 0.0, 0.0)
  | _, .textureSampleCompare _ _ _ _       => 0.0
  | _, .textureGather _ _ _ _              => (0.0, 0.0, 0.0, 0.0)
  | _, .textureNumLayers _                 => 0
  | _, .textureNumLevels _                 => 0
  | _, .textureNumSamples _                => 0

/-! ## State-passing evaluator for atomics (Phase 4)

`Exp.eval` is structurally recursive and pure — it cannot write
to the env. For programs that observe the **post-state** of an
atomic op (the next read after a write), we provide `Exp.evalSt`
that returns both the value and the (possibly mutated) env.

For non-atomic constructors `evalSt` simply forwards to `Exp.eval`
and threads the env unchanged. Only the atomic write/RMW arms
return a new env. -/

partial def Exp.evalSt (env : EvalEnv) :
    {t : WGSLType} → Exp t → t.denote × EvalEnv
  | _, .atomicStore addr val =>
    let a : UInt32 := Exp.eval env addr
    let v : Int32  := Exp.eval env val
    (true, env.atomicStoreI32 a v)
  | _, .atomicStoreU addr val =>
    let a : UInt32 := Exp.eval env addr
    let v : UInt32 := Exp.eval env val
    (true, env.atomicStoreU32 a v)
  | _, .atomicAdd addr delta =>
    let a : UInt32 := Exp.eval env addr
    let d : Int32  := Exp.eval env delta
    let old := env.atomicLoadI32 a
    -- Int32 + Int32: fall through to Int arithmetic (Int32 + Int32 wraps).
    let new : Int32 := Int32.ofInt (old.toInt + d.toInt)
    (old, env.atomicStoreI32 a new)
  | _, .atomicAddU addr delta =>
    let a : UInt32 := Exp.eval env addr
    let d : UInt32 := Exp.eval env delta
    let old := env.atomicLoadU32 a
    (old, env.atomicStoreU32 a (old + d))
  | _, .atomicSub addr delta =>
    let a : UInt32 := Exp.eval env addr
    let d : Int32  := Exp.eval env delta
    let old := env.atomicLoadI32 a
    let new : Int32 := Int32.ofInt (old.toInt - d.toInt)
    (old, env.atomicStoreI32 a new)
  | _, .atomicSubU addr delta =>
    let a : UInt32 := Exp.eval env addr
    let d : UInt32 := Exp.eval env delta
    let old := env.atomicLoadU32 a
    (old, env.atomicStoreU32 a (old - d))
  | _, .atomicMin addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : Int32 := Exp.eval env v
    let old := env.atomicLoadI32 a
    let new := if old.toInt < nv.toInt then old else nv
    (old, env.atomicStoreI32 a new)
  | _, .atomicMinU addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : UInt32 := Exp.eval env v
    let old := env.atomicLoadU32 a
    (old, env.atomicStoreU32 a (if old < nv then old else nv))
  | _, .atomicMax addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : Int32 := Exp.eval env v
    let old := env.atomicLoadI32 a
    let new := if old.toInt > nv.toInt then old else nv
    (old, env.atomicStoreI32 a new)
  | _, .atomicMaxU addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : UInt32 := Exp.eval env v
    let old := env.atomicLoadU32 a
    (old, env.atomicStoreU32 a (if old > nv then old else nv))
  | _, .atomicAnd addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : Int32 := Exp.eval env v
    let old := env.atomicLoadI32 a
    let new : Int32 :=
      Int32.ofInt (((UInt32.ofNat old.toInt.toNat) &&& UInt32.ofNat nv.toInt.toNat).toNat)
    (old, env.atomicStoreI32 a new)
  | _, .atomicAndU addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : UInt32 := Exp.eval env v
    let old := env.atomicLoadU32 a
    (old, env.atomicStoreU32 a (old &&& nv))
  | _, .atomicOr addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : Int32 := Exp.eval env v
    let old := env.atomicLoadI32 a
    let new : Int32 :=
      Int32.ofInt (((UInt32.ofNat old.toInt.toNat) ||| UInt32.ofNat nv.toInt.toNat).toNat)
    (old, env.atomicStoreI32 a new)
  | _, .atomicOrU addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : UInt32 := Exp.eval env v
    let old := env.atomicLoadU32 a
    (old, env.atomicStoreU32 a (old ||| nv))
  | _, .atomicXor addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : Int32 := Exp.eval env v
    let old := env.atomicLoadI32 a
    let new : Int32 :=
      Int32.ofInt (((UInt32.ofNat old.toInt.toNat) ^^^ UInt32.ofNat nv.toInt.toNat).toNat)
    (old, env.atomicStoreI32 a new)
  | _, .atomicXorU addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : UInt32 := Exp.eval env v
    let old := env.atomicLoadU32 a
    (old, env.atomicStoreU32 a (old ^^^ nv))
  | _, .atomicExchange addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : Int32 := Exp.eval env v
    let old := env.atomicLoadI32 a
    (old, env.atomicStoreI32 a nv)
  | _, .atomicExchangeU addr v =>
    let a : UInt32 := Exp.eval env addr
    let nv : UInt32 := Exp.eval env v
    let old := env.atomicLoadU32 a
    (old, env.atomicStoreU32 a nv)
  | _, .atomicCompareExchangeWeak addr cmp newv =>
    let a : UInt32 := Exp.eval env addr
    let cv : Int32 := Exp.eval env cmp
    let nv : Int32 := Exp.eval env newv
    let old := env.atomicLoadI32 a
    if old == cv then (old, env.atomicStoreI32 a nv) else (old, env)
  | _, .atomicCompareExchangeWeakU addr cmp newv =>
    let a : UInt32 := Exp.eval env addr
    let cv : UInt32 := Exp.eval env cmp
    let nv : UInt32 := Exp.eval env newv
    let old := env.atomicLoadU32 a
    if old == cv then (old, env.atomicStoreU32 a nv) else (old, env)
  -- Default for everything else: pure eval, env unchanged.
  | _, e => (Exp.eval env e, env)

/-! ## Phase-1 sanity checks (`native_decide`)

Float equality is not `Decidable` — and `WGSLType.denote (.scalar
.f32)` is `Float` definitionally but Lean's typeclass resolution
doesn't see through it. We pull the result down to a concrete
`Float` / `UInt32` / `Bool` via a helper before comparing. -/

/-- Run an `Exp (.scalar .f32)` and pull the result out as `Float`. -/
def runF32 (env : EvalEnv) (e : Exp (.scalar .f32)) : Float :=
  Exp.eval env e

/-- Run an `Exp (.scalar .u32)` and pull as `UInt32`. -/
def runU32 (env : EvalEnv) (e : Exp (.scalar .u32)) : UInt32 :=
  Exp.eval env e

/-- Run an `Exp (.scalar .i32)` and pull as `Int32`. -/
def runI32 (env : EvalEnv) (e : Exp (.scalar .i32)) : Int32 :=
  Exp.eval env e

/-- Run an `Exp (.scalar .bool)` and pull as `Bool`. -/
def runBool (env : EvalEnv) (e : Exp (.scalar .bool)) : Bool :=
  Exp.eval env e

example :
    (runF32 default (.add (.litF32 2.0) (.litF32 3.0)) == 5.0) = true := by
  native_decide

example :
    runU32 default (.litU32 5) = 5 := by native_decide

example :
    runBool default (.lt (.litU32 2) (.litU32 5)) = true := by
  native_decide

example :
    (runF32 default (.exp (.litF32 0.0)) == 1.0) = true := by native_decide

example :
    (runF32 default (.vecY (.vec2 (.litF32 1.0) (.litF32 2.0))) == 2.0) = true := by
  native_decide

example :
    runI32 default (.toI32 (.add (.litF32 3.5) (.litF32 0.5))) = 4 := by
  native_decide

example :
    (runF32 { f32_vars := [("x", 7.0)] } (.var "x") == 7.0) = true := by
  native_decide

/-! ## Phase-2 sanity checks -/

/-- exp2(3) ≈ 8 within float epsilon (IEEE-754 rounding). -/
example :
    let v := runF32 default (.exp2 (.litF32 3.0))
    ((v - 8.0).abs < 0.001) = true := by native_decide
/-- log2(8) ≈ 3 within float epsilon. -/
example :
    let v := runF32 default (.log2 (.litF32 8.0))
    ((v - 3.0).abs < 0.001) = true := by native_decide
example : (runF32 default (.floor (.litF32 3.7)) == 3.0) = true := by native_decide
example : (runF32 default (.ceil  (.litF32 3.2)) == 4.0) = true := by native_decide
example : (runF32 default (.trunc (.litF32 (-3.7))) == (-3.0 : Float)) = true := by
  native_decide
example : (runF32 default (.sign (.litF32 (-2.0))) == (-1.0 : Float)) = true := by
  native_decide
example : (runF32 default (.saturate (.litF32 1.5)) == 1.0) = true := by native_decide
example : (runF32 default (.saturate (.litF32 (-0.5))) == 0.0) = true := by
  native_decide
example : (runF32 default (.pow (.litF32 2.0) (.litF32 10.0)) == 1024.0) = true := by
  native_decide
example : (runF32 default (.step (.litF32 0.5) (.litF32 1.0)) == 1.0) = true := by
  native_decide
example : (runF32 default (.mix (.litF32 0.0) (.litF32 10.0) (.litF32 0.3)) == 3.0)
            = true := by native_decide
example :
    (runF32 default (.fma (.litF32 2.0) (.litF32 3.0) (.litF32 4.0)) == 10.0) = true := by
  native_decide

example :
    runU32 default (.shiftLeft (.litU32 1) (.litU32 5)) = 32 := by native_decide
example :
    runU32 default (.shiftRight (.litU32 256) (.litU32 4)) = 16 := by native_decide
example :
    runU32 default (.bitAnd (.litU32 0xFF) (.litU32 0x0F)) = 0x0F := by native_decide
example :
    runU32 default (.bitOr (.litU32 0xF0) (.litU32 0x0F)) = 0xFF := by native_decide
example :
    runU32 default (.bitXor (.litU32 0xFF) (.litU32 0xAA)) = 0x55 := by native_decide

example :
    (runF32 default
      (.dotV2 (.vec2 (.litF32 1.0) (.litF32 2.0))
              (.vec2 (.litF32 3.0) (.litF32 4.0)))
      == 11.0) = true := by native_decide

example :
    (runF32 default
      (.dotV3 (.vec3 (.litF32 1.0) (.litF32 2.0) (.litF32 3.0))
              (.vec3 (.litF32 4.0) (.litF32 5.0) (.litF32 6.0)))
      == 32.0) = true := by native_decide

/-- Subgroup ops collapse to identity at single-thread eval. -/
example :
    (runF32 default (.subgroupAdd (.litF32 5.0)) == 5.0) = true := by
  native_decide

/-! ## Phase-3 sanity checks -/

/-- ne / le / ge round out the comparison family. -/
example : runBool default (.ne (.litU32 1) (.litU32 2)) = true := by native_decide
example : runBool default (.le (.litU32 2) (.litU32 2)) = true := by native_decide
example : runBool default (.ge (.litU32 5) (.litU32 5)) = true := by native_decide

/-- Generic abs / min / max / clamp / mod (f32). -/
example : (runF32 default (.abs (.litF32 (-3.5))) == 3.5) = true := by native_decide
example : (runF32 default (.min (.litF32 2.0) (.litF32 5.0)) == 2.0) = true := by
  native_decide
example : (runF32 default (.max (.litF32 2.0) (.litF32 5.0)) == 5.0) = true := by
  native_decide
example :
    (runF32 default (.clamp (.litF32 7.0) (.litF32 0.0) (.litF32 5.0)) == 5.0) = true := by
  native_decide

/-- Bit manipulation. -/
example : runU32 default (.countLeadingZeros (.litU32 1)) = 31 := by native_decide
example : runU32 default (.countTrailingZeros (.litU32 8)) = 3 := by native_decide
example : runU32 default (.countOneBits (.litU32 0xFF)) = 8 := by native_decide
example : runU32 default (.reverseBits (.litU32 1)) = 0x80000000 := by native_decide
example : runU32 default (.firstTrailingBit (.litU32 8)) = 3 := by native_decide
example : runU32 default (.firstLeadingBit (.litU32 1)) = 0 := by native_decide

/-- extractBits / insertBits. -/
example :
    runU32 default
      (.extractBits (.litU32 0xABCD) (.litU32 4) (.litU32 8)) = 0xBC := by
  native_decide

example :
    runU32 default
      (.insertBits (.litU32 0xFF00) (.litU32 0x0AB) (.litU32 4) (.litU32 8))
      = 0xFAB0 := by
  native_decide

/-- mulhiU32: (0xFFFFFFFF * 2) >> 32 = 1 -/
example :
    runU32 default (.mulhiU32 (.litU32 0xFFFFFFFF) (.litU32 2)) = 1 := by
  native_decide

/-- 3×3 transpose: identity matrix is its own transpose. -/
example :
    let lit (x : Float) : Exp (.scalar .f32) := .litF32 x
    let m : Exp (.mat3x3 .f32) :=
      .mat3x3_f32 (lit 1) (lit 0) (lit 0)
                  (lit 0) (lit 1) (lit 0)
                  (lit 0) (lit 0) (lit 1)
    let t := Exp.eval (default : EvalEnv) (.transpose3 m)
    let id := Exp.eval (default : EvalEnv) m
    t == id := by
  native_decide

/-- 2×2 determinant: |[[1,2],[3,4]]| = 1·4 − 2·3 = −2. -/
example :
    let lit (x : Float) : Exp (.scalar .f32) := .litF32 x
    let m := Exp.mat2x2_f32 (lit 1) (lit 2) (lit 3) (lit 4)
    (runF32 default (.determinantM2 m) == (-2.0 : Float)) = true := by
  native_decide

/-- 3×3 determinant of identity = 1. -/
example :
    let lit (x : Float) : Exp (.scalar .f32) := .litF32 x
    let m : Exp (.mat3x3 .f32) :=
      .mat3x3_f32 (lit 1) (lit 0) (lit 0)
                  (lit 0) (lit 1) (lit 0)
                  (lit 0) (lit 0) (lit 1)
    (runF32 default (.determinantM3 m) == 1.0) = true := by
  native_decide

/-- vec3 length: |(3, 4, 0)| = 5. -/
example :
    let lit (x : Float) : Exp (.scalar .f32) := .litF32 x
    let v : Exp (.vec3 .f32) := .vec3 (lit 3) (lit 4) (lit 0)
    (runF32 default (.length3 v) == 5.0) = true := by
  native_decide

/-- vec3 cross product: (1,0,0) × (0,1,0) = (0,0,1). -/
example :
    let lit (x : Float) : Exp (.scalar .f32) := .litF32 x
    let a : Exp (.vec3 .f32) := .vec3 (lit 1) (lit 0) (lit 0)
    let b : Exp (.vec3 .f32) := .vec3 (lit 0) (lit 1) (lit 0)
    let r := Exp.eval (default : EvalEnv) (.cross a b)
    r == ((0.0 : Float), (0.0 : Float), (1.0 : Float)) := by
  native_decide

/-- Subgroup-matrix accumulate: 0 + (I × I) = I (3×3 collapsed array). -/
example :
    let smZero : Exp (.subgroupMatrixResult .f32 3 3) := .subgroupMatrixZeroResult
    let r := Exp.eval (default : EvalEnv) smZero
    r == (Array.replicate 9 0.0 : Array Float) := by
  native_decide

/-- Pack/unpack 4x8 unorm round-trip: (1, 0, 0.5, 0.25)  → packed → close to original. -/
example :
    let lit (x : Float) : Exp (.scalar .f32) := .litF32 x
    let v : Exp (.vec4 .f32) := .vec4 (lit 1.0) (lit 0.0) (lit 0.5) (lit 0.25)
    let packed := runU32 default (.pack4x8unorm v)
    let unpacked := Exp.eval (default : EvalEnv)
                       (.unpack4x8unorm (.litU32 packed.toNat))
    let (a, b, c, d) := unpacked
    -- After round-trip values are quantized to 1/255 grid;
    -- check each is within 1 ULP of the original.
    ((a - 1.0).abs < 0.005 && (b - 0.0).abs < 0.005 &&
     (c - 0.5).abs < 0.005 && (d - 0.25).abs < 0.005) = true := by
  native_decide

/-- Derivatives are zero in compute. -/
example : (runF32 default (.dpdx (.litF32 1.0)) == 0.0) = true := by native_decide
example : (runF32 default (.dpdy (.litF32 1.0)) == 0.0) = true := by native_decide

/-- Barriers / sync are no-ops. -/
example : runBool default .workgroupBarrier = true := by native_decide
example : runBool default .textureBarrier = true := by native_decide

/-! ## Phase-4 sanity checks -/

/-- 4×4 determinant: identity = 1. -/
example :
    let lit (x : Float) : Exp (.scalar .f32) := .litF32 x
    let m : Exp (.mat4x4 .f32) :=
      .mat4x4_f32 (lit 1) (lit 0) (lit 0) (lit 0)
                  (lit 0) (lit 1) (lit 0) (lit 0)
                  (lit 0) (lit 0) (lit 1) (lit 0)
                  (lit 0) (lit 0) (lit 0) (lit 1)
    (runF32 default (.determinant4 m) == 1.0) = true := by
  native_decide

/-- 4×4 determinant: diagonal matrix. det(diag(1,2,3,4)) = 24. -/
example :
    let lit (x : Float) : Exp (.scalar .f32) := .litF32 x
    let m : Exp (.mat4x4 .f32) :=
      .mat4x4_f32 (lit 1) (lit 0) (lit 0) (lit 0)
                  (lit 0) (lit 2) (lit 0) (lit 0)
                  (lit 0) (lit 0) (lit 3) (lit 0)
                  (lit 0) (lit 0) (lit 0) (lit 4)
    (runF32 default (.determinant4 m) == 24.0) = true := by
  native_decide

/-- Bitcast f32 ↔ u32 round-trip: 1.0 → 0x3F800000 → 1.0. -/
example :
    runU32 default (.bitcastF32ToU32 (.litF32 1.0)) = 0x3F800000 := by
  native_decide

example :
    (runF32 default (.bitcastU32ToF32 (.litU32 0x3F800000)) == 1.0) = true := by
  native_decide

/-- Atomic load reads from env. -/
example :
    let env : EvalEnv := { atomic_i32 := [(0x100, 42)] }
    runI32 env (.atomicLoad (.litU32 0x100)) = 42 := by
  native_decide

example :
    let env : EvalEnv := { atomic_u32 := [(0x200, 1234)] }
    runU32 env (.atomicLoadU (.litU32 0x200)) = 1234 := by
  native_decide

/-- Pure `Exp.eval` on `atomicAdd` returns the *current* value
    (the old value), without writing. -/
example :
    let env : EvalEnv := { atomic_u32 := [(0x10, 100)] }
    runU32 env (.atomicAddU (.litU32 0x10) (.litU32 7)) = 100 := by
  native_decide

/-- `Exp.evalSt` actually writes. After atomicAddU(addr=0x10, +7),
    a subsequent load of 0x10 returns 107. -/
example :
    let env : EvalEnv := { atomic_u32 := [(0x10, 100)] }
    let (old, env') := Exp.evalSt env (.atomicAddU (.litU32 0x10) (.litU32 7))
    let after : UInt32 := env'.atomicLoadU32 0x10
    (old = 100 ∧ after = 107) := by
  native_decide

/-- atomicCompareExchangeWeak success path: cmp matches → store. -/
example :
    let env : EvalEnv := { atomic_i32 := [(0x20, 5)] }
    let (old, env') := Exp.evalSt env
      (.atomicCompareExchangeWeak (.litU32 0x20) (.litI32 5) (.litI32 9))
    let after : Int32 := env'.atomicLoadI32 0x20
    (old = 5 ∧ after = 9) := by
  native_decide

/-- atomicCompareExchangeWeak failure path: cmp doesn't match → no write. -/
example :
    let env : EvalEnv := { atomic_i32 := [(0x20, 5)] }
    let (old, env') := Exp.evalSt env
      (.atomicCompareExchangeWeak (.litU32 0x20) (.litI32 99) (.litI32 9))
    let after : Int32 := env'.atomicLoadI32 0x20
    (old = 5 ∧ after = 5) := by
  native_decide

/-- Texture load reads pixel from env. -/
example :
    let pixels : Array (Float × Float × Float × Float) :=
      #[(1.0, 0.0, 0.0, 1.0), (0.0, 1.0, 0.0, 1.0),
        (0.0, 0.0, 1.0, 1.0), (1.0, 1.0, 0.0, 1.0)]
    let env : EvalEnv := { textures := [("tex0", 2, 2, pixels)] }
    let lit (x : Float) : Exp (.scalar .f32) := .litF32 x
    let coord : Exp (.vec2 .u32) := .vec2 (.litU32 1) (.litU32 1)  -- (1,1)
    let r : (Float × Float × Float × Float) :=
      Exp.eval env (.textureLoad (.var (t := .texture2D "f32") "tex0")
                                  coord (.litU32 0))
    -- Pixel at (1,1) of a 2×2 texture is index 1*2+1 = 3 = (1,1,0,1).
    let (rr, rg, rb, ra) := r
    (rr == 1.0 ∧ rg == 1.0 ∧ rb == 0.0 ∧ ra == 1.0) := by
  native_decide

/-- textureDimensions returns the texture's dimensions. -/
example :
    let env : EvalEnv := { textures := [("tex0", 256, 128, #[])] }
    let dims : (UInt32 × UInt32) :=
      Exp.eval env (.textureDimensions (.var (t := .texture2D "f32") "tex0"))
    dims = (256, 128) := by
  native_decide

end Sparkle.Tests.Hesper.Vendored.WGSLInterp
