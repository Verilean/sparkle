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

private def okOut : Except String String → String
  | .ok s => s
  | .error e => s!"<EMIT ERROR: {e}>"

private def errMsg : Except String String → String
  | .ok _ => ""
  | .error e => e

/-! ### Tests -/

def smtTests : IO TestSeq := do
  let goodQ := okOut (toSmtBmcQuery goodCounter 8)
  let memQ  := okOut (toSmtBmcQuery memGood 4)

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
      test "QF_ABV logic with memories"       (hasSubstr memQ "(set-logic QF_ABV)") $
      test "memory as constant-0 array"       (hasSubstr memQ "((as const (Array (_ BitVec 2) (_ BitVec 8))) (_ bv0 8))") $
      test "memory write is a guarded store"  (hasSubstr memQ "(store |m_c0|") $
      test "comboRead is a pre-write select"  (hasSubstr memQ "(define-fun |rd_c0| () (_ BitVec 8) (select |m_c0|")
    ) ++
    group "toSmtBmcQuery: rejections" (
      test "hierarchical module rejected"
        (hasSubstr (errMsg (toSmtBmcQuery instTop 4)) "FLAT") $
      test "assertion-free module rejected"
        (hasSubstr (errMsg (toSmtBmcQuery { goodCounter with assertions := [] } 4)) "no assertions")
    ) ++
    group "parseZ3Output" (
      test "unsat parsed" unsatOk $
      test "sat model parsed (#b, (_ bvN w), #x forms)" satOk
    )
  )

end Sparkle.Test.Smt
