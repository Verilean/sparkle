/-
  EquivDemo — Interactive showcase for the `#verify_eq` command.

  ⚠  RUN INTERACTIVELY — NOT VIA `lake build`.

  `#verify_eq` invokes `bv_decide`, which (per docs/KnownIssues.md Issue 2)
  hangs in compilation mode on Lean 4.28.0-rc1. This file is therefore
  DELIBERATELY NOT imported from `Sparkle.lean`, `Tests/AllTests.lean`,
  or any `lean_exe` root. It is meant to be opened in VSCode or executed
  with:

      lake env lean Tests/Verification/EquivDemo.lean

  Every `#verify_eq` below should print

      ✅ verified: `<lhs>_eq_<rhs>` — ...

  at the command's position. Uncomment the BUG variants to see
  `bv_decide` produce a counterexample.
-/

import Sparkle.Verification.Equivalence

-- ============================================================================
-- 1. Distributivity:  (a+b)(c+d) = ac + ad + bc + bd   on BitVec 4
--    (Using 4-bit so `bv_decide` finishes in milliseconds. 8-bit
--    distributivity over multiply pushes the SAT solver over the default
--    timeout; enable `acNf` in a future v2 or bump `timeout`.)
-- ============================================================================

def distrib_lhs (a b c d : BitVec 4) : BitVec 4 :=
  (a + b) * (c + d)

def distrib_rhs (a b c d : BitVec 4) : BitVec 4 :=
  a * c + a * d + b * c + b * d

#verify_eq distrib_lhs distrib_rhs

-- BUG variant: drop the `b * d` term.
-- Uncomment to see `bv_decide` produce a concrete counterexample.
--
-- def distrib_rhs_buggy (a b c d : BitVec 4) : BitVec 4 :=
--   a * c + a * d + b * c
-- #verify_eq distrib_lhs distrib_rhs_buggy


-- ============================================================================
-- 2. Add associativity:  (a+b)+c = a+(b+c)   on BitVec 8
-- ============================================================================

def addAssocL (a b c : BitVec 8) : BitVec 8 := (a + b) + c
def addAssocR (a b c : BitVec 8) : BitVec 8 := a + (b + c)

#verify_eq addAssocL addAssocR


-- ============================================================================
-- 3. Mul commutativity:  a*b = b*a   on BitVec 8
-- ============================================================================

def mulCommL (a b : BitVec 8) : BitVec 8 := a * b
def mulCommR (a b : BitVec 8) : BitVec 8 := b * a

#verify_eq mulCommL mulCommR


-- ============================================================================
-- 4. De Morgan:  ~(a & b) = ~a | ~b   on BitVec 8
-- ============================================================================

def deMorganL (a b : BitVec 8) : BitVec 8 := ~~~(a &&& b)
def deMorganR (a b : BitVec 8) : BitVec 8 := ~~~ a ||| ~~~ b

#verify_eq deMorganL deMorganR


-- ============================================================================
-- 5. XOR-swap one lane:  ((a ⊕ b) ⊕ b) = a   on BitVec 8
--    (The core identity that makes XOR-swap work.)
-- ============================================================================

def xorSwapRoundTrip (a b : BitVec 8) : BitVec 8 := (a ^^^ b) ^^^ b
def xorSwapIdentity  (a _b : BitVec 8) : BitVec 8 := a

#verify_eq xorSwapRoundTrip xorSwapIdentity


-- ============================================================================
-- 6. Carry-save adder step identity on 4 bits.
--    The full 64-bit version lives in Sparkle/Verification/MulProps.lean;
--    we scale it down here so `bv_decide` finishes in sub-second time.
--    Identity: XOR + (shifted majority) = sum of three inputs.
-- ============================================================================

def carrySaveLhs4 (a b c : BitVec 4) : BitVec 4 :=
  (a ^^^ b ^^^ c) + (((a &&& b) ||| (a &&& c) ||| (b &&& c)) <<< 1)

def carrySaveRhs4 (a b c : BitVec 4) : BitVec 4 := a + b + c

#verify_eq carrySaveLhs4 carrySaveRhs4


-- ============================================================================
-- 7. Ripple-carry vs built-in add on 4 bits.
--    Shows that a "from-scratch" 1-bit full-adder ripple implementation
--    matches `BitVec.+` exactly.
-- ============================================================================

/-- Expand each bit independently, add them with explicit carries, OR
    back into one BitVec. This is a deliberately "dumb" ripple-carry. -/
def rippleAdd4 (a b : BitVec 4) : BitVec 4 :=
  let a0 := (a >>> 0) &&& 1
  let a1 := (a >>> 1) &&& 1
  let a2 := (a >>> 2) &&& 1
  let a3 := (a >>> 3) &&& 1
  let b0 := (b >>> 0) &&& 1
  let b1 := (b >>> 1) &&& 1
  let b2 := (b >>> 2) &&& 1
  let b3 := (b >>> 3) &&& 1
  let s0  := a0 ^^^ b0
  let c1  := a0 &&& b0
  let s1  := a1 ^^^ b1 ^^^ c1
  let c2  := (a1 &&& b1) ||| (c1 &&& (a1 ^^^ b1))
  let s2  := a2 ^^^ b2 ^^^ c2
  let c3  := (a2 &&& b2) ||| (c2 &&& (a2 ^^^ b2))
  let s3  := a3 ^^^ b3 ^^^ c3
  s0 ||| (s1 <<< 1) ||| (s2 <<< 2) ||| (s3 <<< 3)

def plainAdd4 (a b : BitVec 4) : BitVec 4 := a + b

#verify_eq rippleAdd4 plainAdd4


-- ============================================================================
-- 8. (Stretch, still <1s) Shift-and-add multiply on 4 bits.
--    Unrolled long-multiplication: for each bit of `b`, conditionally
--    add a shifted `a`. Equivalent to plain `*` for BitVec 4.
-- ============================================================================

def shiftAddMul4 (a b : BitVec 4) : BitVec 4 :=
  let m0 := if b &&& 1 != 0 then a       else 0
  let m1 := if b &&& 2 != 0 then a <<< 1 else 0
  let m2 := if b &&& 4 != 0 then a <<< 2 else 0
  let m3 := if b &&& 8 != 0 then a <<< 3 else 0
  m0 + m1 + m2 + m3

def plainMul4 (a b : BitVec 4) : BitVec 4 := a * b

#verify_eq shiftAddMul4 plainMul4
