import Tools.ShippingMachineCommand
import IP.YOLOv8.Primitives.Requantize

/-! Sign extension and arithmetic right shift on the machine route.

The reader takes `signExtend` / `sshiftRight` / `Signal.ashr` in their
derived form over the certified operators (`Sparkle.Compiler.MachSignOps`);
the generator rewrites the declaration with the Signal-level equations of
`Tools.ShippingSignOps`, proves the endpoint for the rewritten value and
transports it back: `f.machine_sound` is about `f` itself
(`f.machineSourceDecl`). -/
namespace Sparkle.Tests.Compiler.ShippingSignOpsTest
open Sparkle.Core.Domain Sparkle.Core.Signal

def sext (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 16) :=
  a.map (BitVec.signExtend 16 ·)
def ashrK (a : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  Signal.map (fun x => BitVec.sshiftRight x 10) a
abbrev S := Signal defaultDomain (BitVec 4)
def shiftSurface (a b : S) : S := (fun x y => BitVec.sshiftRight x y.toNat) <$> a <*> b
def ashrSig (a b : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  Signal.ashr a b
def scaleMul (acc : Signal defaultDomain (BitVec 48)) (scale : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 32) :=
  let accExt : Signal defaultDomain (BitVec 80) := acc.map (BitVec.signExtend 80 ·)
  let scaleExt : Signal defaultDomain (BitVec 80) := scale.map (BitVec.signExtend 80 ·)
  let prod := accExt * scaleExt
  prod.map (BitVec.extractLsb' 24 32 ·)

#machine_endpoint sext
#machine_endpoint ashrK
#machine_endpoint shiftSurface
#machine_endpoint ashrSig
#machine_endpoint scaleMul
#machine_endpoint Sparkle.IP.YOLOv8.Primitives.Requantize.requantize

open Lean in
run_cmd do
  if (← get).messages.hasErrors then throwError "sign-operation regression failed"
  for name in [``sext.machine_sound, ``ashrK.machine_sound, ``shiftSurface.machine_sound,
      ``ashrSig.machine_sound, ``scaleMul.machine_sound,
      ``Sparkle.IP.YOLOv8.Primitives.Requantize.requantize.machine_sound,
      ``Tools.ShippingSignOps.map_signExtend, ``Tools.ShippingSignOps.ashr_eq] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  -- the theorem speaks about the declaration itself
  let some (.defnInfo d) := (← getEnv).find? ``sext.machineSourceDecl
    | throwError "sext: no source observations of the declaration"
  unless (d.value.find? (·.isConstOf ``sext)).isSome do
    throwError "sext.machine_sound is not about sext"
  Lean.logInfo m!"SIGN OPERATIONS: sign extension and arithmetic shifts with kernel-checked endpoints"

/-! ## To the emitted Verilog, across the sign normalisation

The endpoints above are proved for the rewritten value and transported back
to the declaration; `f.machine_ships_comb` is transported the same way. -/

run_cmd do
  let env ← Lean.getEnv
  for n in [``sext, ``ashrK, ``shiftSurface, ``ashrSig, ``scaleMul,
      ``Sparkle.IP.YOLOv8.Primitives.Requantize.requantize] do
    unless env.contains (n ++ `machine_ships_comb) do throwError "{n}: no machine_ships_comb"
    unless env.contains (n ++ `machineSourceDecl) do throwError "{n}: not transported"
    for ax in ← Lean.collectAxioms (n ++ `machine_ships_comb) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"SIGN OPS SHIP: six transported endpoints, each to its emitted Verilog"

end Sparkle.Tests.Compiler.ShippingSignOpsTest
