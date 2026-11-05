import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGenTest
import Tests.Gen5.PrimResidueTraceLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGenTest` alone (it cannot be imported together with the others; see PrimResidueTraceLib). -/
#prim_residue_trace "M4" 400000
