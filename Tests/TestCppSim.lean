/-
  C Simulation Backend Tests

  Tests that the CSim backend generates correct C code from IR modules.
  (Kept under the legacy filename to minimise churn for `Tests.AllTests`;
  the namespace is renamed to `Sparkle.Test.CSim` so post-rename
  consistency is preserved.)
-/

import Sparkle.Backend.CSim
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Builder
import LSpec

namespace Sparkle.Test.CppSim

open Sparkle.Backend.CSim
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
    let inc ← makeWire "inc" (.bitVector 8)
    let count ← emitRegister "count" "clk" "rst" (.ref inc) 0 (.bitVector 8)
    emitAssign inc (.op .add [.ref count, .const 1 8])
    let next ← makeWire "next" (.bitVector 8)
    emitAssign next (.op .mux [.ref "en", .ref inc, .ref count])
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
  let counterC := toC counterModule
  let memoryC := toC memoryModule
  let combC := toC combModule
  let regMemC := toC registeredMemModule

  return group "C Simulation Backend Tests" (
    group "Counter Module" (
      test "has struct declaration" (hasSubstr counterC "struct Counter8") $
      test "has eval helper" (hasSubstr counterC "sparkle_Counter8_eval") $
      test "has tick helper" (hasSubstr counterC "sparkle_Counter8_tick") $
      test "has reset helper" (hasSubstr counterC "sparkle_Counter8_reset") $
      test "has uint8_t port type" (hasSubstr counterC "uint8_t") $
      test "has _next suffix for register" (hasSubstr counterC "_next") $
      test "has addition operator" (hasSubstr counterC " + ") $
      test "has ternary for mux" (hasSubstr counterC " ? ") $
      test "has stdint header" (hasSubstr counterC "#include <stdint.h>")
    ) ++
    group "Memory Module" (
      test "has struct declaration" (hasSubstr memoryC "struct MemTest") $
      test "has plain C array for memory" (hasSubstr memoryC "[16]") $
      test "has memset in reset" (hasSubstr memoryC "memset(") $
      test "has eval helper" (hasSubstr memoryC "sparkle_MemTest_eval") $
      test "has tick helper" (hasSubstr memoryC "sparkle_MemTest_tick")
    ) ++
    group "Combinational Module" (
      test "has struct declaration" (hasSubstr combC "struct CombOps") $
      test "has addition" (hasSubstr combC " + ") $
      test "has bitwise AND" (hasSubstr combC " & ") $
      test "has ternary for mux" (hasSubstr combC " ? ") $
      test "has uint8_t types" (hasSubstr combC "uint8_t")
    ) ++
    group "Registered Memory Module" (
      test "has struct declaration" (hasSubstr regMemC "struct RegMemTest") $
      test "has plain C array" (hasSubstr regMemC "[16]") $
      test "has read addr latch" (hasSubstr regMemC "_raddr")
    )
  )

end Sparkle.Test.CppSim
