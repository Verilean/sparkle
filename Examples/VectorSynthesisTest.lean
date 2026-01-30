/-
  Vector Type Synthesis Test

  Simple test that synthesizes vector operations to Verilog.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Vector
open Sparkle.Compiler.Elab

namespace Sparkle.Examples.VectorSynthesis

/--
  Simple register file read: index into a 4-element vector of 8-bit values.

  This should generate Verilog array like:
    input logic [7:0] vec [3:0];
    input logic [1:0] idx;
    output logic [7:0] out;
    assign out = vec[idx];
-/
def registerFileRead (vec : Signal defaultDomain (HWVector (BitVec 8) 4))
    (idx : Signal defaultDomain (BitVec 2)) : Signal defaultDomain (BitVec 8) :=
  (fun v i => v.get ⟨i.toNat, by omega⟩) <$> vec <*> idx

#sparkle_synth registerFileRead to "/tmp/vector_register_file.v"

/--
  Constant index: read element 2 from the vector.
-/
def constantIndex (vec : Signal defaultDomain (HWVector (BitVec 8) 4))
    : Signal defaultDomain (BitVec 8) :=
  vec.map (fun v => v.get ⟨2, by omega⟩)

#sparkle_synth constantIndex to "/tmp/vector_constant_index.v"

/--
  16-bit register file: 8 elements of 16 bits each
-/
def registerFile16 (vec : Signal defaultDomain (HWVector (BitVec 16) 8))
    (idx : Signal defaultDomain (BitVec 3)) : Signal defaultDomain (BitVec 16) :=
  (fun v i => v.get ⟨i.toNat, by omega⟩) <$> vec <*> idx

#sparkle_synth registerFile16 to "/tmp/vector_register_file_16.v"

end Sparkle.Examples.VectorSynthesis
