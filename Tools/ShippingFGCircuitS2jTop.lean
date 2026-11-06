import Tools.ShippingFGCircuitS2gGates
import Tools.ShippingGen2OneOutTopO
import Tools.ShippingGen2SlotlessLeaf
set_option autoImplicit false
open Tools.ShippingFGCircuitS1kRoot
example : synth_hftPcieOutByte.machineData.shape.instFields = [] := by decide +kernel
example : synth_hftPcieOutByte.machineData.shape.layout.slots ≠ [] := by decide +kernel
#check @Tools.ShippingGen2.oneOut_topShipsO
#check @Tools.ShippingGen2.slotlessLeaf_ships
#print Tools.ShippingGen2.SoundXAt
#check @Tools.ShippingGen2.soundX_ships_ran
#check @Tools.ShippingMachineTraceX.MachineTraceLBX
#print Tools.ShippingGen2.OneOutWidth
#print Tools.ShippingGen2.LeafDataOk
#check @Tools.ShippingRanABridge.machineRanA_of_runJQC
#check @Tools.ShippingFGCircuitS1qEndpoint.machineRunJQC_of_closesCOff
