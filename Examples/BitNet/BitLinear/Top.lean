import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Examples.BitNet.Config
import Examples.BitNet.BitLinear.Core

namespace Sparkle.Examples.BitNet.BitLinear

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open CircuitM

def buildTop (weights : Array Int) (cfg : GeneratorConfig) : Module :=
  let activeCount := weights.foldl (fun acc w => if w != 0 then acc + 1 else acc) 0
  CircuitM.runModule s!"BitLinearPipelined_{activeCount}active" do
    generateBitLinearPipelined weights cfg

end Sparkle.Examples.BitNet.BitLinear
