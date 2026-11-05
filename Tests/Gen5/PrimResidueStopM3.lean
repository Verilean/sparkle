import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGateTypedAllTest
import Tests.Gen5.PrimResidueStopLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGateTypedAllTest` alone (it cannot be imported together with the others; see PrimResidueStopLib). -/
#prim_residue_stop "M3" 400000
