/-
  C++ Simulation Backend Tests

  Tests that the CppSim backend generates correct C++ code from IR modules.
-/

import Sparkle.Backend.CppSim
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Builder
import LSpec

namespace Sparkle.Test.CppSim

open Sparkle.Backend.CppSim
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.IR.Builder
open CircuitM
open LSpec

/-- Check if a string contains a substring -/
private def hasSubstr (s : String) (sub : String) : Bool :=
  decide ((s.splitOn sub).length > 1)

/-- Build a counter module: clk, rst, en → 8-bit count_out -/
def counterModule : Module :=
  runModule "Counter8" do
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "en" (.bitVector 8)
    addOutput "count_out" (.bitVector 8)
    -- inc = count + 1
    let inc ← makeWire "inc" (.bitVector 8)
    -- count register (output of register)
    let count ← emitRegister "count" "clk" "rst" (.ref inc) 0 (.bitVector 8)
    -- inc = count + 1
    emitAssign inc (.op .add [.ref count, .const 1 8])
    -- next = en ? inc : count
    let next ← makeWire "next" (.bitVector 8)
    emitAssign next (.op .mux [.ref "en", .ref inc, .ref count])
    -- count_out = count
    emitAssign "count_out" (.ref count)

/-- Build a memory module: write addr/data/en, read addr → read data -/
def memoryModule : Module :=
  runModule "MemTest" do
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "wr_addr" (.bitVector 4)
    addInput "wr_data" (.bitVector 8)
    addInput "wr_en" .bit
    addInput "rd_addr" (.bitVector 4)
    addOutput "rd_data" (.bitVector 8)
    let rdWire ← emitMemoryComboRead "mem" 4 8 "clk"
      (.ref "wr_addr") (.ref "wr_data") (.ref "wr_en") (.ref "rd_addr")
    emitAssign "rd_data" (.ref rdWire)

/-- Build a combinational module: a, b → add_out, and_out, mux_out -/
def combModule : Module :=
  runModule "CombOps" do
    addInput "a" (.bitVector 8)
    addInput "b" (.bitVector 8)
    addInput "sel" .bit
    addOutput "add_out" (.bitVector 8)
    addOutput "and_out" (.bitVector 8)
    addOutput "mux_out" (.bitVector 8)
    emitAssign "add_out" (.op .add [.ref "a", .ref "b"])
    emitAssign "and_out" (.op .and [.ref "a", .ref "b"])
    emitAssign "mux_out" (.op .mux [.ref "sel", .ref "a", .ref "b"])

/-- Build a module with registered (non-combo) memory read -/
def registeredMemModule : Module :=
  runModule "RegMemTest" do
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "wr_addr" (.bitVector 4)
    addInput "wr_data" (.bitVector 8)
    addInput "wr_en" .bit
    addInput "rd_addr" (.bitVector 4)
    addOutput "rd_data" (.bitVector 8)
    let rdWire ← emitMemory "rmem" 4 8 "clk"
      (.ref "wr_addr") (.ref "wr_data") (.ref "wr_en") (.ref "rd_addr")
    emitAssign "rd_data" (.ref rdWire)

def cppSimTests : IO TestSeq := do
  let counterCpp := toCppSim counterModule
  let memoryCpp := toCppSim memoryModule
  let combCpp := toCppSim combModule
  let regMemCpp := toCppSim registeredMemModule

  return group "C++ Simulation Backend Tests" (
    group "Counter Module" (
      test "has class declaration" (hasSubstr counterCpp "class Counter8") $
      test "has eval method" (hasSubstr counterCpp "void eval()") $
      test "has tick method" (hasSubstr counterCpp "void tick()") $
      test "has reset method" (hasSubstr counterCpp "void reset()") $
      test "has uint8_t port type" (hasSubstr counterCpp "uint8_t") $
      test "has _next suffix for register" (hasSubstr counterCpp "_next") $
      test "has addition operator" (hasSubstr counterCpp " + ") $
      test "has ternary for mux" (hasSubstr counterCpp " ? ") $
      test "has constructor" (hasSubstr counterCpp "Counter8()") $
      test "has include cstdint" (hasSubstr counterCpp "#include <cstdint>")
    ) ++
    group "Memory Module" (
      test "has class declaration" (hasSubstr memoryCpp "class MemTest") $
      test "has std::array for memory" (hasSubstr memoryCpp "std::array<") $
      test "has fill(0) in reset" (hasSubstr memoryCpp ".fill(0)") $
      test "has eval method" (hasSubstr memoryCpp "void eval()") $
      test "has tick method" (hasSubstr memoryCpp "void tick()")
    ) ++
    group "Combinational Module" (
      test "has class declaration" (hasSubstr combCpp "class CombOps") $
      test "has addition" (hasSubstr combCpp " + ") $
      test "has bitwise AND" (hasSubstr combCpp " & ") $
      test "has ternary for mux" (hasSubstr combCpp " ? ") $
      test "has uint8_t types" (hasSubstr combCpp "uint8_t")
    ) ++
    group "Registered Memory Module" (
      test "has class declaration" (hasSubstr regMemCpp "class RegMemTest") $
      test "has std::array" (hasSubstr regMemCpp "std::array<") $
      test "has read addr latch" (hasSubstr regMemCpp "_raddr")
    )
  )

end Sparkle.Test.CppSim
