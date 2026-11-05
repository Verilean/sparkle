import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGenTest
import Tests.Gen5.PrimResidueCmpLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGenTest` alone (it cannot be imported together with the others; see PrimResidueCmpLib). -/
#prim_residue_cmp "M4" 400000
