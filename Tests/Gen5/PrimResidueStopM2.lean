import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGateDesignTest
import Tests.Gen5.PrimResidueStopLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGateDesignTest` alone (it cannot be imported together with the others; see PrimResidueStopLib). -/
#prim_residue_stop "M2" 400000
