import Tools.SVParser
import Sparkle.Backend.CSim
open Tools.SVParser.Lower

/-- `lake env lean --run bench/gate/gen.lean <in.v> <out.c>`: the CSim JIT
    C for a flat SystemVerilog design (bench/gate/run.sh). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [src, out] =>
    let design ← IO.ofExcept (parseAndLowerFlat (← IO.FS.readFile src))
    IO.FS.writeFile out (Sparkle.Backend.CSim.toCJIT design)
    return 0
  | _ => IO.eprintln "usage: gen.lean <in.v> <out.c>"; return 1
