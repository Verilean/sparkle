-- JIT simulation of the modular ALU (native, ~1M cyc/s).  Replaces the
-- iverilog testbench: compiles the #sim-generated C and drives it via the
-- Sparkle JIT vtable.  Exercises the wide-input (256-bit `loadData`) path
-- that the CSim `emitSetInputSwitch` fix enabled.
--
-- Generate the C first:  lake env lean fpga/tangNano20k/build/GenAluSim.lean
-- Then:                   lake exe ecdsa-sign-small-jit
import Sparkle.Core.JIT
import IP.Crypto.Secp256k1Field
import IP.Crypto.Secp256k1ECDSA

open Sparkle.Core.JIT

namespace Sparkle.Tests.Drivers.EcdsaSignSmallJIT

-- Input-port slot map (from the generated set_input switch):
--   0 start · 1 op · 2 srcA · 3 srcB · 4 dst · 5 loadEn · 6 loadAddr
--   7..14 loadData word[0..7]      Output out word[0..7] via get_output.

def jitPath : String := ".lake/build/gen/sim/aluTop_jit.c"

def p : Nat := Sparkle.IP.Crypto.Secp256k1Field.p
def n : Nat := Sparkle.IP.Crypto.Secp256k1ECDSA.n

def main : IO Unit := do
  let h ← JIT.compileAndLoad jitPath
  JIT.reset h

  let si (idx : Nat) (v : Nat) : IO Unit :=
    JIT.setInput h idx.toUInt32 (UInt64.ofNat (v % 0x10000000000000000))
  let set256 (base : Nat) (v : Nat) : IO Unit := do
    for j in [0:8] do
      si (base + j) ((v >>> (32 * j)) &&& 0xFFFFFFFF)
  let get256 : IO Nat := do
    let mut acc : Nat := 0
    for j in [0:8] do
      let w ← JIT.getOutput h j.toUInt32
      acc := acc ||| (w.toNat <<< (32 * j))
    pure acc

  -- reg[addr] = val  (one idle cycle with loadEn asserted)
  let loadReg (addr val : Nat) : IO Unit := do
    si 0 0; si 1 0; si 5 1; si 6 addr; set256 7 val
    JIT.evalTick h
    si 5 0
    JIT.evalTick h

  -- reg[d] = reg[a] OP reg[b]; hold op/src/dst for `waitc` cycles, read out.
  let runOp (op a b d waitc : Nat) : IO Nat := do
    si 1 op; si 2 a; si 3 b; si 4 d; si 5 0; si 0 1
    JIT.evalTick h
    si 0 0
    for _ in [0:waitc] do JIT.evalTick h
    JIT.eval h
    get256

  let check (name : String) (got exp : Nat) : IO Bool := do
    if got == exp then IO.println s!"PASS {name} = {got}"; pure true
    else do IO.println s!"FAIL {name}: got={got} exp={exp}"; pure false

  loadReg 0 5
  loadReg 1 7
  let r1 ← check "ADDP 5+7" (← runOp 2 0 1 2 14) 12
  let r2 ← check "SUBP 5-7" (← runOp 3 0 1 3 14) (p - 2)
  let r3 ← check "ADDN 5+7" (← runOp 4 0 1 5 14) 12
  let r4 ← check "SUBN 5-7" (← runOp 5 0 1 6 14) (n - 2)
  let r5 ← check "MULP 5*7" (← runOp 0 0 1 4 300) 35
  let r6 ← check "MULN 5*7" (← runOp 1 0 1 7 300) 35

  JIT.destroy h
  if r1 && r2 && r3 && r4 && r5 && r6 then IO.println "ALL PASS (Sparkle JIT sim)"
  else do IO.println "FAILURES"; IO.Process.exit 1

end Sparkle.Tests.Drivers.EcdsaSignSmallJIT

def main : IO Unit := Sparkle.Tests.Drivers.EcdsaSignSmallJIT.main
