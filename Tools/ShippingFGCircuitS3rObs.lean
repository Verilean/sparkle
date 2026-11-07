import Tools.ShippingFGCircuitS3rArtifact
import Tools.ShippingFGCircuitS3rGen
import Tools.ShippingFGCircuitS3rKernel
import Tools.ShippingFGCircuitS1kRoot
import Tools.ShippingHierSVSoundness
set_option autoImplicit false
-- FG circuit pilot S3r, step 2 (observation): the closed terms of `Tools.ShippingFGCircuitS3rArtifact` EQUAL what the compiler returns, checked by RE-RUNNING `pilotEntry3 hftRoot` at elaboration time and comparing with the compiled `BEq`.  An OBSERVATION: it is executed code (the compiler, `BEq`), not a kernel fact; a mismatch makes the build fail, a match proves nothing in the kernel.  Nothing here is trusted.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §68.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3rObs
open Lean Elab Command Sparkle.IR.AST Tools.ShippingFGCircuitS3rArtifact

/-- the compiled sequential-fragment check at the emitter's width map (executed code; the KERNEL cannot reduce it, `sanitizeName` uses `String.all`) -/
def seqOk (m : Sparkle.IR.AST.Module) : Bool :=
  Tools.SVParser.EmitSem.seqCheck (Tools.SVParser.RoundtripProof.moduleWof m)
    (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) m.body

-- re-run the entry; compare the returned `(b, D)` and the shipped form with the generated terms; negative controls: altered copies differ from the run; compiled `shipsHierCheck`/`seqCheck` on the returned values
run_cmd liftTermElabM do
  let (b, D) ← Tools.ShippingFGCircuitS3jStart.pilotEntry3 Tools.ShippingFGCircuitS1kStmt.hftRoot
  let s := Sparkle.IR.OptCheck.checkedOptimize b
  unless b == pilotB0 do throwError "FGCIRCUIT56 OBS: the returned top module differs from pilotB0"
  unless D.topModule == pilotD0.topModule && D.modules.length == pilotD0.modules.length &&
      (D.modules.zip pilotD0.modules).all (fun (x, y) => x == y) do
    throwError "FGCIRCUIT56 OBS: the returned design differs from pilotD0"
  unless s == pilotS0 do throwError "FGCIRCUIT56 OBS: checkedOptimize of the returned module differs from pilotS0"
  -- negative controls of the observation: altered copies are not the run
  unless !(({ b with body := b.body.drop 1 } : Sparkle.IR.AST.Module) == pilotB0) do throwError "FGCIRCUIT56 OBS: control failed (dropped statement)"
  unless !(({ b with name := b.name ++ "x" } : Sparkle.IR.AST.Module) == pilotB0) do throwError "FGCIRCUIT56 OBS: control failed (renamed)"
  unless !(({ s with body := s.body.reverse } : Sparkle.IR.AST.Module) == pilotS0) do throwError "FGCIRCUIT56 OBS: control failed (reversed shipped body)"
  let ships := Tools.ShippingHierPremisesBase.shipsHierCheck (Tools.ShippingMachineLinked.childMap D.modules) b
  unless ships do throwError "FGCIRCUIT56 OBS: shipsHierCheck is not true on the returned values (compiled)"
  let sq := D.modules.map seqOk ++ [seqOk s]
  unless sq.all id do throwError "FGCIRCUIT56 OBS: seqCheck is not true on the returned values (compiled)"
  logInfo m!"FGCIRCUIT56 OBS (one run, compiled code, NOT a kernel fact): re-running pilotEntry3 hftRoot returned (b, D) == (pilotB0, pilotD0) ({b.body.length} + {D.modules.map (·.body.length)} statements) and checkedOptimize b == pilotS0 ({s.body.length}); 3 altered copies differ; compiled shipsHierCheck = {ships}, compiled seqCheck on the two children and the shipped form = {sq}"

end Tools.ShippingFGCircuitS3rObs
