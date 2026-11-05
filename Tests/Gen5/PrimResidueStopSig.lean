import Lean
import Sparkle
import Tests.SignalLoopTest
import Tests.Gen5.PrimResidueStopLib
/-! Driver: the three Signal roots of `Tests.SignalLoopTest` (not corpus roots), both modes. -/
#prim_residue_stop_named "Sig" 400000 Sparkle.Tests.SignalLoopTest.counterLoop Sparkle.Tests.SignalLoopTest.shift4Loop Sparkle.Tests.SignalLoopTest.counterEnableLoop
#prim_residue_stop_dyn_ctl
