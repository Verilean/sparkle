import Lean
import Sparkle
import Tests.SignalLoopTest
import Tests.Gen5.PrimResidueTraceLib
/-! Driver: the three Signal roots of `Tests.SignalLoopTest` (not corpus roots), all 6 stages. -/
#prim_residue_trace_named "Sig" 400000 Sparkle.Tests.SignalLoopTest.counterLoop Sparkle.Tests.SignalLoopTest.shift4Loop Sparkle.Tests.SignalLoopTest.counterEnableLoop
#prim_residue_trace_ctl
