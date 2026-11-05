import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGateTypedAllTest
import Tests.Gen5.PrimResidueTraceLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGateTypedAllTest` alone (it cannot be imported together with the others; see PrimResidueTraceLib). -/
#prim_residue_trace "M3" 400000
