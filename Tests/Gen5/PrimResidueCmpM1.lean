import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionDesignTest
import Tests.Gen5.PrimResidueCmpLib
/-! Driver: module `Tests.Compiler.MemNameCollisionDesignTest` alone (it cannot be imported together with the others; see PrimResidueCmpLib). -/
#prim_residue_cmp "M1" 400000
