import Sparkle
import LSpec

/-! DRC rules on hand-built IR modules: each rule fires on a module that
violates it and stays silent on a clean one. -/

namespace Sparkle.Tests.DRCTest

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.Compiler.DRC LSpec

def bv (n : String) (w : Nat) : Port := { name := n, ty := .bitVector w }

def rules (m : Module) : List String := (checkModule m).map (·.rule)

/-- A clean registered design: no findings at all. -/
def clean : Module :=
  { name := "clean", inputs := [bv "clk" 1, bv "rst" 1, bv "a" 8], outputs := [bv "q" 8],
    wires := [bv "r" 8, bv "n" 8],
    body := [.assign "n" (.op .add [.ref "r", .ref "a"]),
             .register "r" "clk" ("rst", .asynchronous) (.ref "n") 0,
             .assign "q" (.ref "r")] }

def loop : Module :=
  { name := "loop", inputs := [bv "a" 8], outputs := [bv "q" 8],
    wires := [bv "x" 8, bv "y" 8],
    body := [.assign "x" (.op .add [.ref "y", .ref "a"]),
             .assign "y" (.ref "x"),
             .assign "q" (.ref "x")] }

def multi : Module :=
  { name := "multi", inputs := [bv "a" 8, bv "b" 8], outputs := [bv "q" 8], wires := [],
    body := [.assign "q" (.ref "a"), .assign "q" (.ref "b")] }

def undriven : Module :=
  { name := "undriven", inputs := [bv "a" 8], outputs := [bv "q" 8, bv "z" 8],
    wires := [bv "w" 8],
    body := [.assign "q" (.op .add [.ref "a", .ref "w"])] }

def undeclared : Module :=
  { name := "undeclared", inputs := [bv "a" 8], outputs := [bv "q" 8], wires := [],
    body := [.assign "q" (.op .add [.ref "a", .ref "ghost"])] }

def badClock : Module :=
  { name := "badClock", inputs := [bv "a" 8], outputs := [bv "q" 8], wires := [bv "r" 8],
    body := [.register "r" "clk" ("rst", .asynchronous) (.ref "a") 0,
             .assign "q" (.ref "r")] }

def truncating : Module :=
  { name := "truncating", inputs := [bv "a" 16], outputs := [bv "q" 8], wires := [],
    body := [.assign "q" (.ref "a")] }

def unusedIn : Module :=
  { name := "unusedIn", inputs := [bv "a" 8, bv "b" 8], outputs := [bv "q" 8], wires := [],
    body := [.assign "q" (.ref "a")] }

def zeroPort : Module :=
  { name := "zeroPort", inputs := [bv "a" 8, bv "e" 0], outputs := [bv "q" 8], wires := [],
    body := [.assign "q" (.op .add [.ref "a", .ref "e"])] }

/-- DRC010 looks through alias chains: q = s, s = r, r a register. -/
def aliasChain : Module :=
  { name := "aliasChain", inputs := [bv "clk" 1, bv "rst" 1, bv "a" 8], outputs := [bv "q" 8],
    wires := [bv "r" 8, bv "s" 8],
    body := [.register "r" "clk" ("rst", .asynchronous) (.ref "a") 0,
             .assign "s" (.ref "r"),
             .assign "q" (.ref "s")] }

/-- A concatenation of register bits counts as registered. -/
def concatRegs : Module :=
  { name := "concatRegs", inputs := [bv "clk" 1, bv "rst" 1, bv "a" 8], outputs := [bv "q" 16],
    wires := [bv "r" 8, bv "c" 16],
    body := [.register "r" "clk" ("rst", .asynchronous) (.ref "a") 0,
             .assign "c" (.concat [.ref "r", .ref "r"]),
             .assign "q" (.ref "c")] }

/-- A wire driven by a sub-module instance's output is driven. -/
def instDriven : Module :=
  { name := "instDriven", inputs := [bv "a" 8], outputs := [bv "q" 8], wires := [bv "w" 8],
    body := [.inst "child" "u0" [("x", .ref "a"), ("y", .ref "w")],
             .assign "q" (.ref "w")] }

/-- Sequential module whose output is logic on a register: DRC010. -/
def seqComb : Module :=
  { name := "seqComb", inputs := [bv "clk" 1, bv "rst" 1, bv "a" 8], outputs := [bv "q" 8],
    wires := [bv "r" 8],
    body := [.register "r" "clk" ("rst", .asynchronous) (.ref "a") 0,
             .assign "q" (.op .add [.ref "r", .ref "a"])] }

def tests : TestSeq :=
  group "DRC rules" (
    test "clean design: no findings" (rules clean == []) $
    test "DRC001 combinational loop" ((rules loop).contains "DRC001") $
    test "DRC001 not on registered feedback" (!(rules clean).contains "DRC001") $
    test "DRC002 multiple drivers" ((rules multi).contains "DRC002") $
    test "DRC003 undriven output and wire" ((rules undriven).count "DRC003" == 2) $
    test "DRC004 undeclared name" ((rules undeclared).contains "DRC004") $
    test "DRC003 not on instance-driven wires" (!(rules instDriven).contains "DRC003") $
    test "DRC005 register clock/reset not declared" ((rules badClock).count "DRC005" == 2) $
    test "DRC010 not on purely combinational modules" (!(rules loop).contains "DRC010") $
    test "DRC010 on a sequential module's combinational output"
      ((rules seqComb).contains "DRC010") $
    test "DRC010 follows alias chains" (!(rules aliasChain).contains "DRC010") $
    test "DRC010 accepts concatenated registers" (!(rules concatRegs).contains "DRC010") $
    test "DRC011 truncating assign" ((rules truncating).contains "DRC011") $
    test "DRC012 unused input" ((rules unusedIn).contains "DRC012") $
    test "DRC013 zero-width port" ((rules zeroPort).contains "DRC013") $
    test "error-class rules are errors"
      (((checkModule loop).filter (·.rule == "DRC001")).all (·.severity == .error)) $
    test "warning-class rules are warnings"
      (((checkModule unusedIn).filter (·.rule == "DRC012")).all (·.severity == .warning)))

end Sparkle.Tests.DRCTest
