import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGateDesignTest
import Tests.Gen5.PrimResidueTraceLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGateDesignTest` alone (it cannot be imported together with the others; see PrimResidueTraceLib). -/
#prim_residue_trace "M2" 400000
