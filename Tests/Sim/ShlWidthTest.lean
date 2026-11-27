/-
  Left-shift width regressions, checked by VALUE through the C simulator.

  * A fixed-width Signal shift (`x <<< 25` on 32 bits, the SHA-256 σ₀ shape)
    truncates to its operand width even when it feeds a wider expression.
  * A Verilog shift is sized by its context: `(x << k) >> k` into a wider
    target keeps the bits shifted past the operand width, whatever the
    width of the amount literal (same width, narrow, or wide).
  * firtool's SRAM byte lane `(wdata >> 16) << 48` in a 128-bit context
    keeps the words above bit 63.
-/
import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Core.JIT
import Sparkle.Core.SimTyped
import Sparkle.Backend.CSim
import Sparkle.IR.Optimize
import Tools.SVParser

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT

namespace Sparkle.Tests.Sim.ShlWidthTest

abbrev D := defaultDomain

/-- σ₀-shaped: a fixed-width shift, summed, then concatenated. -/
def sigmaTop (x y : Signal D (BitVec 32)) : Signal D (BitVec 64) :=
  let c25 : Signal D (BitVec 32) := Signal.pure 25#32
  let c7  : Signal D (BitVec 32) := Signal.pure 7#32
  let a : Signal D (BitVec 32) := (x >>> c7) ||| (x <<< c25)
  let s : Signal D (BitVec 32) := a + y
  s ++ a

#sim sigmaTop

/-- Single-use shift and sum feeding a concat directly (the inliner can
    fold them into the concat operand, as in `sha256Block`'s W buffer). -/
def inlineTop (x y : Signal D (BitVec 32)) : Signal D (BitVec 64) :=
  let c25 : Signal D (BitVec 32) := Signal.pure 25#32
  ((x <<< c25) + y) ++ y

#sim inlineTop

private def inlineRef (x y : BitVec 32) : BitVec 64 := ((x <<< (25#32)) + y) ++ y

private def sigmaRef (x y : BitVec 32) : BitVec 64 :=
  let a : BitVec 32 := (x >>> (7#32)) ||| (x <<< (25#32))
  (a + y) ++ a

private def sigmaCases : List (BitVec 32 × BitVec 32) :=
  [ (0x80000000#32, 0#32), (0xFFFFFFFF#32, 1#32), (0x12345678#32, 0xDEADBEEF#32)
  , (0x00000001#32, 0xFFFFFFFF#32), (0xCAFEBABE#32, 0x0F0F0F0F#32) ]

private def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

private def check (ok : IO.Ref Bool) (label : String) (got want : Nat) : IO Unit := do
  if got == want then IO.println s!"  ✓ {label}: {hex got}"
  else
    IO.println s!"  ✗ {label}: got {hex got}, expected {hex want}"
    ok.set false

private def sigmaTest (ok : IO.Ref Bool) : IO Unit := do
  let sim ← sigmaTop.Sim.load
  for (x, y) in sigmaCases do
    Sparkle.Core.Sim.Sim.reset sim
    Sparkle.Core.Sim.Sim.step sim ({ _gen_x := x, _gen_y := y } : sigmaTop.Sim.SimInput)
    let o ← Sparkle.Core.Sim.Sim.read sim
    check ok s!"Signal σ₀ x={hex x.toNat} y={hex y.toNat}" o.out.toNat (sigmaRef x y).toNat
  -- the Signal semantics themselves (not just a BitVec twin)
  for (x, y) in sigmaCases do
    let v := (sigmaTop (Signal.pure x) (Signal.pure y)).atTime 0
    check ok s!"Signal.val σ₀ x={hex x.toNat}" v.toNat (sigmaRef x y).toNat
  sim.destroy
  let sim2 ← inlineTop.Sim.load
  for (x, y) in sigmaCases do
    Sparkle.Core.Sim.Sim.reset sim2
    Sparkle.Core.Sim.Sim.step sim2 ({ _gen_x := x, _gen_y := y } : inlineTop.Sim.SimInput)
    let o ← Sparkle.Core.Sim.Sim.read sim2
    check ok s!"Signal (x<<<25 + y) ++ y x={hex x.toNat}" o.out.toNat (inlineRef x y).toNat
  sim2.destroy

/-- Run an SV combinational module through the C simulator; return the
    outputs for the given inputs.  `opt` also runs the IR optimizer. -/
private def runSV (src : String) (tag : String) (opt : Bool)
    (ins : List UInt64) (outIdx : List Nat) : IO (List UInt64) := do
  let design ← IO.ofExcept (Tools.SVParser.Lower.parseAndLower src)
  let design := if opt then Sparkle.IR.Optimize.optimizeDesign design else design
  let path := s!".lake/build/gen/sim/shlwidth_{tag}.c"
  IO.FS.createDirAll ".lake/build/gen/sim"
  IO.FS.writeFile path (Sparkle.Backend.CSim.toCJIT design)
  let h ← JIT.compileAndLoad path
  JIT.reset h
  let mut i : UInt32 := 0
  for v in ins do
    JIT.setInput h i v
    i := i + 1
  JIT.eval h
  let mut outs := []
  for j in outIdx do
    outs := outs ++ [← JIT.getOutput h j.toUInt32]
  JIT.destroy h
  return outs

private def svTests (ok : IO.Ref Bool) : IO Unit := do
  for opt in [false, true] do
    let o := if opt then "opt" else "raw"
    -- bit 31 shifted to bit 39 and back: the context is 64 bits wide
    for (amt, tag) in [("32'd8", "same"), ("8'd8", "n8"), ("3'd5", "n3"), ("64'd8", "w64")] do
      let k : Nat := (amt.splitOn "'d").getLast!.toNat!
      let src := s!"module m(input [31:0] x, output [63:0] y);\n  assign y = (x << {amt}) >> {amt};\nendmodule\n"
      let r ← runSV src s!"{tag}_{o}" opt [0x80000000] [0]
      check ok s!"SV (x << {amt}) >> {amt} [{o}]" (r.getD 0 0).toNat (0x80000000 <<< k >>> k)
    let r ← runSV
      "module m(input [31:0] x, output [63:0] y);\n  assign y = x << 8'd8;\nendmodule\n"
      s!"plain_{o}" opt [0x80000000] [0]
    check ok s!"SV x << 8'd8 into 64 bits [{o}]" (r.getD 0 0).toNat (0x80000000 <<< 8)
    -- firtool SRAM byte lane: (wdata >> 16) << 48 in a 128-bit context
    -- (the 128-bit `y` takes output slots 0-3, so `lo`/`hi` are 4 and 5)
    let src := "module m(input [63:0] wdata, output [127:0] y, output [63:0] lo, output [63:0] hi);\n" ++
      "  assign y = (wdata >> 16) << 48;\n  assign lo = y[63:0];\n  assign hi = y[127:64];\nendmodule\n"
    let w : Nat := 0xFFFFFFFFFFFFFFFF
    let want := (w >>> 16) <<< 48
    let r ← runSV src s!"sram_{o}" opt [w.toUInt64] [4, 5]
    check ok s!"SV SRAM lane lo [{o}]" (r.getD 0 0).toNat (want % 2^64)
    check ok s!"SV SRAM lane hi [{o}]" (r.getD 1 0).toNat (want / 2^64)

def main : IO Unit := do
  IO.println "=== left-shift width regressions (C sim vs semantics) ==="
  let ok ← IO.mkRef true
  sigmaTest ok
  svTests ok
  if !(← ok.get) then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.Sim.ShlWidthTest
