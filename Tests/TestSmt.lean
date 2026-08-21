/-
  SMT bridge tests, Layer 1: emitted-query shape, rejection errors, and
  solver-output parsing — no z3 required (Layer 2 = `lake exe smt-bmc-test`
  runs the real solver and replays counterexamples on the CSim reference).
-/

import Sparkle.Backend.Smt
import Sparkle.IR.AST
import Sparkle.IR.Type
import LSpec

namespace Sparkle.Test.Smt

open Sparkle.Backend.Smt
open Sparkle.IR.AST
open Sparkle.IR.Type
open LSpec

private def hasSubstr (s : String) (sub : String) : Bool :=
  decide ((s.splitOn sub).length > 1)

private def errorContainsAll (result : Except String String)
    (needles : List String) : Bool :=
  match result with
  | .ok _ => false
  | .error message => needles.all (hasSubstr message)

/-! ### Fixtures (shared with the Layer-2 driver) -/

/-- Saturating counter: sticks at 5.  Assertion `count ≤ 5` holds forever
    → BMC is **unsat** at any bound. -/
def goodCounter : Module := {
  name        := "GoodCounter"
  isPrimitive := false
  inputs      := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
  outputs     := [⟨"count_o", .bitVector 8⟩]
  wires       := [⟨"at5", .bitVector 1⟩, ⟨"nxt", .bitVector 8⟩,
                  ⟨"count", .bitVector 8⟩]
  body := [
    .assign "at5" (.op .eq [.ref "count", .const 5 8]),
    .assign "nxt" (.op .mux [.ref "at5", .const 5 8,
                             .op .add [.ref "count", .const 1 8]]),
    .register "count" "clk" ("rst", .synchronous) (.ref "nxt") 0,
    .assign "count_o" (.ref "count") ]
  assertions := [("count_le_5", .op .le_u [.ref "count", .const 5 8])]
}

/-- Wrapping 4-bit counter.  Assertion `count < 12` is violated at cycle 12
    → BMC at k ≥ 12 is **sat**, and the counterexample must replay on CSim. -/
def buggyCounter : Module := {
  name        := "BuggyCounter"
  isPrimitive := false
  inputs      := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
  outputs     := [⟨"count_o", .bitVector 4⟩]
  wires       := [⟨"nxt", .bitVector 4⟩, ⟨"count", .bitVector 4⟩]
  body := [
    .assign "nxt" (.op .add [.ref "count", .const 1 4]),
    .register "count" "clk" ("rst", .synchronous) (.ref "nxt") 0,
    .assign "count_o" (.ref "count") ]
  assertions := [("count_lt_12", .op .lt_u [.ref "count", .const 12 4])]
}

/-- Memory write-then-readback (QF_ABV — what `bv_decide` cannot express):
    every cycle writes input `x` to address 0 of a comboRead memory and
    registers `x` into `xr`.  The read (pre-write, CSim eval order) always
    equals `xr` → **unsat**. -/
def memGood : Module := {
  name        := "MemGood"
  isPrimitive := false
  inputs      := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"x", .bitVector 8⟩]
  outputs     := [⟨"rd_o", .bitVector 8⟩]
  wires       := [⟨"rd", .bitVector 8⟩, ⟨"xr", .bitVector 8⟩]
  body := [
    .memory "m" 2 8 "clk" (.const 0 2) (.ref "x") (.const 1 1) (.const 0 2)
      "rd" (comboRead := true),
    .register "xr" "clk" ("rst", .synchronous) (.ref "x") 0,
    .assign "rd_o" (.ref "rd") ]
  assertions := [("rd_eq_xr", .op .eq [.ref "rd", .ref "xr"])]
}

/-- Same datapath, wrong assertion: the read equals the CURRENT `x` — false
    whenever `x` changes between cycles (or `x ≠ 0` at cycle 0) → **sat**. -/
def memBuggy : Module := {
  memGood with
  name := "MemBuggy"
  assertions := [("rd_eq_x", .op .eq [.ref "rd", .ref "x"])]
}

/-- Hierarchical module — v1 must reject with a "FLAT" error. -/
def instTop : Module := {
  name        := "InstTop"
  isPrimitive := false
  inputs      := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
  outputs     := []
  wires       := []
  body        := [.inst "GoodCounter" "c0" [("clk", .ref "clk")]]
  assertions  := [("t", .const 1 1)]
}


/-- A retained-width top-bit property. The assertion is violated only when
    bit W-1 is set, so W=65 counterexample replay must exercise the third
    32-bit CSim word. -/
def parameterizedZeroAssertion : Module := {
  name := "ParameterizedZeroAssertion"
  parameters := [{ name := "W", defaultValue := 8 }]
  inputs := [⟨"x", .bitVectorDim (.parameter "W")⟩]
  outputs := []
  wires := []
  body := []
  assertions := [
    ("top_bit_is_zero", .op .eq [
      .sliceDim (.ref "x")
        (.sub (.parameter "W") (.literal 1))
        (.sub (.parameter "W") (.literal 1)),
      .const 0 1
    ])
  ]
}

/-- Exercises both a derived width (W+1) and a symbolic W-1 slice bound.
    The output is defined by that same slice, so the assertion is UNSAT. -/
def parameterizedDerivedSlice : Module := {
  name := "ParameterizedDerivedSlice"
  parameters := [{ name := "W", defaultValue := 8 }]
  inputs := [
    ⟨"x", .bitVectorDim (.add (.parameter "W") (.literal 1))⟩
  ]
  outputs := [⟨"low", .bitVectorDim (.parameter "W")⟩]
  wires := []
  body := [
    .assign "low" (.sliceDim (.ref "x")
      (.sub (.parameter "W") (.literal 1)) (.literal 0))
  ]
  assertions := [
    ("low_matches", .op .eq [
      .ref "low",
      .sliceDim (.ref "x")
        (.sub (.parameter "W") (.literal 1)) (.literal 0)
    ])
  ]
}

def zeroWidthPort : Module := {
  name := "ZeroWidthPort"
  inputs := [⟨"z", .bitVector 0⟩]
  outputs := []
  wires := []
  body := []
  assertions := [("true", .const 1 1)]
}

def zeroWidthMemory : Module := {
  name := "ZeroWidthMemory"
  inputs := [⟨"clk", .bit⟩]
  outputs := []
  wires := [⟨"rd", .bitVector 8⟩]
  body := [
    .memory "m" 0 8 "clk" (.const 0 0) (.const 0 8) (.const 0 1)
      (.const 0 0) "rd" (comboRead := true)
  ]
  assertions := [("true", .const 1 1)]
}

def oneBitMemoryAssertion : Module := {
  name := "OneBitMemoryAssertion"
  inputs := [{ name := "clk", ty := .bit }]
  outputs := []
  wires := [{ name := "rd", ty := .bit }]
  body := [
    .memory "m" 1 1 "clk" (.const 0 1) (.const 0 1) (.const 0 1)
      (.const 0 1) "rd" (comboRead := true)
  ]
  assertions := [
    ("memory_bit", .index (.ref "m") (.const 0 1))
  ]
}

/-- Regression for natural-width inference through a nested memory select.
    The shift amount must be emitted at the memory's 65-bit data width, not
    at the generic 32-bit fallback. -/
def wideMemoryShiftAssertion : Module := {
  name := "WideMemoryShiftAssertion"
  inputs := [{ name := "clk", ty := .bit }]
  outputs := []
  wires := [{ name := "rd", ty := .bitVector 65 }]
  body := [
    .memory "m" 1 65 "clk" (.const 0 1) (.const 0 65) (.const 0 1)
      (.const 0 1) "rd" (comboRead := true)
  ]
  assertions := [
    ("shifted_zero", .op .eq [
      .op .shr [.index (.ref "m") (.const 0 1), .const 64 7],
      .const 0 1
    ])
  ]
}

private def okOut : Except String String → String
  | .ok s => s
  | .error e => s!"<EMIT ERROR: {e}>"

private def errMsg : Except String String → String
  | .ok _ => ""
  | .error e => e

/-! ### Tests -/

def smtTests : IO TestSeq := do
  let goodQ := okOut (toSmtBmcQuery goodCounter 8)

  let param3Q := okOut
    (toSmtBmcQueryWithParameters parameterizedZeroAssertion [("W", 3)] 0)
  let param17Q := okOut
    (toSmtBmcQueryWithParameters parameterizedZeroAssertion [("W", 17)] 0)
  let param65Q := okOut
    (toSmtBmcQueryWithParameters parameterizedZeroAssertion [("W", 65)] 0)
  let derived65Q := okOut
    (toSmtBmcQueryWithParameters parameterizedDerivedSlice [("W", 65)] 0)
  let memQ := okOut (toSmtBmcQuery memGood 4)
  let memBitQ := okOut (toSmtBmcQuery oneBitMemoryAssertion 0)
  let wideMemQ := okOut (toSmtBmcQuery wideMemoryShiftAssertion 0)

  -- parser unit tests (no solver needed)
  let unsatR := parseZ3Output "unsat\n" 5
  let unsatOk : Bool := match unsatR with | .ok .unsat => true | _ => false
  let satR := parseZ3Output
    "sat\n((|x_c0| #b00000011)\n (|x_c1| (_ bv5 8))\n (|x_c2| #x1f))" 2
  let satOk : Bool := match satR with
    | .ok (.sat cex) =>
      cex[0]! == [("x", 3)] && cex[1]! == [("x", 5)] && cex[2]! == [("x", 31)]
    | _ => false

  return group "SMT Bridge Tests" (
    group "toSmtBmcQuery: shape" (
      test "QF_BV logic without memories"     (hasSubstr goodQ "(set-logic QF_BV)") $
      test "frame-0 register init"            (hasSubstr goodQ "(define-fun |count_c0| () (_ BitVec 8) (_ bv0 8))") $
      test "inputs declared per frame"        (hasSubstr goodQ "(declare-const |rst_c3| (_ BitVec 1))") $
      test "next-state define into frame+1"   (hasSubstr goodQ "(define-fun |count_c1| () (_ BitVec 8)") $
      test "mux lowered to ite-vs-zero"       (hasSubstr goodQ "(ite (= |at5_c0| (_ bv0 1))") $
      test "violation disjunction"            (hasSubstr goodQ "(= |_assert_count_le_5_c0| #b0)") $
      test "check-sat + get-value"            (hasSubstr goodQ "(check-sat)" && hasSubstr goodQ "(get-value") $
      test "solver-compatible logic with memories" (hasSubstr memQ "(set-logic ALL)") $
      test "memory as constant-0 array"       (hasSubstr memQ "((as const (Array (_ BitVec 2) (_ BitVec 8))) (_ bv0 8))") $
      test "memory write is a guarded store"  (hasSubstr memQ "(store |m_c0|") $
      test "comboRead is a pre-write select"  (hasSubstr memQ "(define-fun |rd_c0| () (_ BitVec 8) (select |m_c0|") $
      test "1-bit memory-select assertion remains valid"
        (hasSubstr memBitQ "(define-fun |_assert_memory_bit_c0| () (_ BitVec 1) (select |m_c0|") $
      test "nested 65-bit memory select keeps its natural width"
        (hasSubstr wideMemQ "(bvlshr (select |m_c0| (_ bv0 1)) (_ bv64 65))")
    ) ++
    group "toSmtBmcQueryWithParameters" (
      test "W=3 emits a concrete 3-bit solver input"
        (hasSubstr param3Q "(declare-const |x_c0| (_ BitVec 3))") $
      test "W=17 emits a concrete 17-bit solver input"
        (hasSubstr param17Q "(declare-const |x_c0| (_ BitVec 17))") $
      test "W=65 emits a concrete 65-bit solver input"
        (hasSubstr param65Q "(declare-const |x_c0| (_ BitVec 65))") $
      test "derived W+1 input becomes 66 bits"
        (hasSubstr derived65Q "(declare-const |x_c0| (_ BitVec 66))") $
      test "derived W-1 slice becomes [64:0]"
        (hasSubstr derived65Q "((_ extract 64 0) |x_c0|)") $
      test "raw symbolic SMT emission remains rejected"
        (errorContainsAll
          (toSmtBmcQuery parameterizedZeroAssertion 0)
          ["retained", "specialized"]) $
      test "missing binding is rejected"
        (errorContainsAll
          (toSmtBmcQueryWithParameters parameterizedZeroAssertion [] 0)
          ["missing", "W"]) $
      test "unknown binding is rejected"
        (errorContainsAll
          (toSmtBmcQueryWithParameters parameterizedZeroAssertion
            [("W", 3), ("TYPO", 17)] 0)
          ["unknown", "TYPO"]) $
      test "duplicate binding is rejected"
        (errorContainsAll
          (toSmtBmcQueryWithParameters parameterizedZeroAssertion
            [("W", 3), ("W", 17)] 0)
          ["duplicate", "W"]) $
      test "zero binding is rejected"
        (errorContainsAll
          (toSmtBmcQueryWithParameters parameterizedZeroAssertion
            [("W", 0)] 0)
          ["W", "zero", "positive"])
    ) ++
    group "toSmtBmcQuery: rejections" (
      test "hierarchical module rejected"
        (hasSubstr (errMsg (toSmtBmcQuery instTop 4)) "FLAT") $
      test "assertion-free module rejected"
        (hasSubstr (errMsg (toSmtBmcQuery { goodCounter with assertions := [] } 4)) "no assertions") $
      test "zero-width port rejected"
        (errorContainsAll (toSmtBmcQuery zeroWidthPort 0) ["positive", "zero-width"]) $
      test "zero-width memory address rejected"
        (errorContainsAll (toSmtBmcQuery zeroWidthMemory 0) ["memory", "address"]) $
      test "non-1-bit assertion rejected"
        (errorContainsAll
          (toSmtBmcQuery { goodCounter with assertions := [("wide", .ref "count")] } 0)
          ["assertion", "wide", "8", "1 bit"])
    ) ++
    group "parseZ3Output" (
      test "unsat parsed" unsatOk $
      test "sat model parsed (#b, (_ bvN w), #x forms)" satOk
    )
  )

end Sparkle.Test.Smt
