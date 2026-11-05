import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGateDesignTest
import Tests.Gen5.PrimResidueCmpLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGateDesignTest` alone (it cannot be imported together with the others; see PrimResidueCmpLib). -/
#prim_residue_cmp "M2" 400000
