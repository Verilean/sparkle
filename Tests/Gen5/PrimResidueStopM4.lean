import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGenTest
import Tests.Gen5.PrimResidueStopLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGenTest` alone (it cannot be imported together with the others; see PrimResidueStopLib). -/
#prim_residue_stop "M4" 400000
