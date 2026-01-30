/-
  Vector Type Tests

  Tests for hardware vector types and array indexing synthesis.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Vector
open Sparkle.Compiler.Elab
open Sparkle.Backend.Verilog

namespace Sparkle.Test.Vector

/--
  Simple 4-element register file: reads from a vector at an index.

  This tests:
  - HWVector type inference
  - Array indexing synthesis
  - Verilog array emission
-/
def registerFileRead (vec : Signal defaultDomain (HWVector (BitVec 8) 4))
    (idx : Signal defaultDomain (BitVec 2)) : Signal defaultDomain (BitVec 8) :=
  (fun v i => v.get ⟨i.toNat, by omega⟩) <$> vec <*> idx

/--
  Test vector literal access: read element 2 from a 4-element vector.
-/
def vectorLiteral (vec : Signal defaultDomain (HWVector (BitVec 8) 4))
    : Signal defaultDomain (BitVec 8) :=
  vec.map (fun v => v.get ⟨2, by omega⟩)

end Sparkle.Test.Vector
