import Sparkle
import Tools.ShippingMachineMemCommand
import IP.Video.H264.QuantSynth

/-! # loop-pkg step 0: generator probe on the real IP top `quantModule` (LOOPPKG_FREEZE.md §3 step 0)

Runs the generator (`#machine_endpoint`) and the memory-composed command (`#machine_composedT`, the loop `MemFacts`)
on `Sparkle.IP.Video.H264.QuantSynth.quantModule`, then lists every generated constant with its type (the inventory
the review asks for). Measurement: a refusal is reported as a blocker, not worked around. -/
set_option maxHeartbeats 4000000

#machine_endpoint Sparkle.IP.Video.H264.QuantSynth.quantModule
#machine_composedT Sparkle.IP.Video.H264.QuantSynth.quantModule

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pre := `Sparkle.IP.Video.H264.QuantSynth.quantModule
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₂.toList do
    if pre.isPrefixOf n && n != pre then names := names.push n
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  for n in sorted do
    let some ci := env.find? n | continue
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque" | _ => "other"
    let ty ← liftTermElabM <| Meta.ppExpr ci.type
    let tyS := toString ty
    logInfo m!"QUANT GEN {kind} {n} : {if tyS.length > 600 then (String.ofList (tyS.toList.take 600)) ++ " …" else tyS}"

#print axioms Sparkle.IP.Video.H264.QuantSynth.quantModule.machine_sound
