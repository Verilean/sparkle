import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionDesignTest
import Tests.Gen5.PrimResidueTraceLib
/-! Driver: module `Tests.Compiler.MemNameCollisionDesignTest` alone (it cannot be imported together with the others; see PrimResidueTraceLib). -/
#prim_residue_trace "M1" 400000
