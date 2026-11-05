import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionDesignTest
import Tests.Gen5.PrimResidueStopLib
/-! Driver: module `Tests.Compiler.MemNameCollisionDesignTest` alone (it cannot be imported together with the others; see PrimResidueStopLib). -/
#prim_residue_stop "M1" 400000
