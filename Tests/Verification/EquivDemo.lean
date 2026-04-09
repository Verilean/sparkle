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

import Sparkle
import Sparkle.Verification.Equivalence
import IP.YOLOv8.Types    -- for the §13 #verify_eq_git demo

open Sparkle.Core.Domain
open Sparkle.Core.Signal

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


-- ============================================================================
-- LAYER 2 DEMOS — Signal DSL equivalence at N cycles via `#verify_eq_at`
-- ============================================================================
--
-- These demos use `#verify_eq_at (cycles := N) (latency := L) impl spec`
-- to prove that an implementation matches a specification at every time
-- `t ∈ [L, L + N)`, where `latency` models how many cycles the
-- implementation is delayed behind the spec. The typical use case is
-- proving that a pipelined version of a combinational circuit produces
-- the same result as the single-cycle spec, delayed by the pipeline's
-- own latency.
--
-- Limitations (v1):
--   • No `Signal.loop` / feedback circuits (opaque to unfold).
--   • No memory / register-file primitives.
--   • BitVec widths above ~8 and cycle counts above ~8 may time out.
-- ============================================================================

-- ----------------------------------------------------------------------------
-- 9. Refactoring with identical latency: two ways to express a 2-cycle delay.
--    `simp only` alone closes this; bv_decide is not even needed.
-- ----------------------------------------------------------------------------

def delay2A (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  Signal.register 0#4 (Signal.register 0#4 x)

def delay2B (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  Signal.register 0#4 (Signal.register 0#4 x)

#verify_eq_at (cycles := 4) delay2A delay2B


-- ----------------------------------------------------------------------------
-- 10. Register-position refactor (latency 0):
--     Is `register each input then add` the same as `add then register twice`?
--     Both complete their addition and hold the result with the same delay.
-- ----------------------------------------------------------------------------

def addPipeInputFirst (a b : Signal defaultDomain (BitVec 4))
    : Signal defaultDomain (BitVec 4) :=
  let ra := Signal.register 0#4 a
  let rb := Signal.register 0#4 b
  Signal.register 0#4 (ra + rb)

def addPipeOutputFirst (a b : Signal defaultDomain (BitVec 4))
    : Signal defaultDomain (BitVec 4) :=
  let s := a + b
  Signal.register 0#4 (Signal.register 0#4 s)

#verify_eq_at (cycles := 4) addPipeInputFirst addPipeOutputFirst


-- ----------------------------------------------------------------------------
-- 11. ★ HEADLINE USE CASE ★
--     Single-cycle MAC vs 3-stage pipelined MAC, latency = 2.
--
--     macSingle: out(t) = a(t)*b(t) + c(t)                 (1-cycle critical path)
--     macPipe:   stage1: latch a, b, c
--                stage2: product register + aligned c register
--                stage3: sum
--
--     Proves that for every t ≥ 2,
--         macPipe.val t = macSingle.val (t - 2)
--     i.e. the pipeline reproduces the single-cycle answer exactly,
--     two clocks late. This is the bread-and-butter "clock-frequency-
--     optimization preserves functional correctness" proof.
-- ----------------------------------------------------------------------------

def macSingle (a b c : Signal defaultDomain (BitVec 4))
    : Signal defaultDomain (BitVec 4) :=
  a * b + c

def macPipe (a b c : Signal defaultDomain (BitVec 4))
    : Signal defaultDomain (BitVec 4) :=
  let ra := Signal.register 0#4 a
  let rb := Signal.register 0#4 b
  let rc := Signal.register 0#4 c
  let prod2 := Signal.register 0#4 (ra * rb)
  let c2    := Signal.register 0#4 rc
  prod2 + c2

#verify_eq_at (cycles := 4) (latency := 2) macPipe macSingle

-- BUG variant #1: dropped `c` from the pipeline. Uncomment to see
-- bv_decide's counterexample AND a 💡 hint saying "no nearby latency
-- makes these match — likely functionally incorrect".
--
-- def macPipeBuggy (a b _c : Signal defaultDomain (BitVec 4))
--     : Signal defaultDomain (BitVec 4) :=
--   let ra := Signal.register 0#4 a
--   let rb := Signal.register 0#4 b
--   Signal.register 0#4 (ra * rb)
-- #verify_eq_at (cycles := 3) (latency := 2) macPipeBuggy macSingle

-- BUG variant #2: write the *wrong latency* for the CORRECT pipeline.
-- Uncomment to see the hint saying "the circuit DOES match at
-- latency := 2 — re-run as ..." with the exact corrected command.
-- This is the typical case when a designer misremembers the pipeline
-- depth of their own module.
--
-- #verify_eq_at (cycles := 3) (latency := 1) macPipe macSingle


-- ----------------------------------------------------------------------------
-- 12. 2-tap FIR filter, single-cycle vs 1-stage pipeline (latency = 1)
--     Single: y(t) = a*x(t) + b*x(t-1)
--     Pipe:   stage1: register the sum, latency increases by 1
-- ----------------------------------------------------------------------------

def fir2Single (a b : BitVec 4) (x : Signal defaultDomain (BitVec 4))
    : Signal defaultDomain (BitVec 4) :=
  let x1 := Signal.register 0#4 x
  (a * x) + (b * x1)

def fir2Pipe (a b : BitVec 4) (x : Signal defaultDomain (BitVec 4))
    : Signal defaultDomain (BitVec 4) :=
  let x1 := Signal.register 0#4 x
  Signal.register 0#4 ((a * x) + (b * x1))

#verify_eq_at (cycles := 3) (latency := 1) fir2Pipe fir2Single


-- ============================================================================
-- LAYER 3 DEMO — Time-travel equivalence via `#verify_eq_git`
-- ============================================================================
--
-- `#verify_eq_git <commit-ref> <ident>` pulls the old version of an
-- imported definition from git and proves the current version equivalent
-- to it. Use case: PR regression checks, "did my refactor preserve
-- behavior?", bisecting when a function first broke.
--
-- Requirements: the target must be (a) in an IMPORTED module, not the
-- current file, and (b) a pure `BitVec … → BitVec …` function (same
-- restriction as `#verify_eq`).
-- ============================================================================

-- ----------------------------------------------------------------------------
-- 13. IP.YOLOv8.Types.reluInt8 at HEAD = current (smoke test).
--     Proves `reluInt8` is trivially equivalent to itself at HEAD.
--     Replace `HEAD` with a branch name (`main`) or earlier commit
--     (`HEAD~5`) to actually time-travel.
-- ----------------------------------------------------------------------------

section GitDemo
open Sparkle.IP.YOLOv8

#verify_eq_git HEAD reluInt8

end GitDemo
