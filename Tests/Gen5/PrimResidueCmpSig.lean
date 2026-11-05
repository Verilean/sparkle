import Lean
import Sparkle
import Tests.SignalLoopTest
import Tests.Gen5.PrimResidueCmpLib
/-! Driver: the three Signal roots of `Tests.SignalLoopTest` (not corpus roots), all 6 stages. -/
#prim_residue_cmp_named "Sig" 400000 Sparkle.Tests.SignalLoopTest.counterLoop Sparkle.Tests.SignalLoopTest.shift4Loop Sparkle.Tests.SignalLoopTest.counterEnableLoop
#prim_residue_cmp_ctl
