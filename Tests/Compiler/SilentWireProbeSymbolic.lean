/-
  Silent-wire audit probes, parameterized (symbolic-width) synthesis:
  `hwType = .bitVectorDim _` reaches the `| _ => 8` width defaults.
-/
import Sparkle
import Sparkle.Compiler.Elab
import Tests.Compiler.SilentWireProbeLib

namespace Sparkle.Tests.Compiler.SilentWireProbe

open Sparkle.Core.Domain
open Sparkle.Core.Signal

def sy01 {dom : DomainConfig} {W : Nat} (p : Signal dom (BitVec W × BitVec W)) :
    Signal dom (BitVec W) := Signal.fst p
#probeP "sy01_symbolic_Signal_fst" sy01 "out" "~dimslice" "W" 16

def sy02 {dom : DomainConfig} {W : Nat} (p : Signal dom (BitVec W × BitVec W)) :
    Signal dom (BitVec W) := Signal.snd p
#probeP "sy02_symbolic_Signal_snd" sy02 "out" "~dimslice" "W" 16

def sy03 {dom : DomainConfig} {W : Nat} (p : Signal dom (BitVec W × BitVec W)) :
    Signal dom (BitVec W) := p.map Prod.fst
#probeP "sy03_symbolic_map_Prod_fst" sy03 "out" "~dimslice" "W" 16

def sy04 {dom : DomainConfig} {W : Nat} (x : Signal dom (BitVec W)) :
    Signal dom (BitVec W) := x.map (fun v => v ||| 0#W)
#probeP "sy04_symbolic_map_lambda" sy04 "out" "~or" "W" 16

end Sparkle.Tests.Compiler.SilentWireProbe
