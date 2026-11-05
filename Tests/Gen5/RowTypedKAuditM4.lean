import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGenTest
import Tests.Gen5.RowTypedKAuditLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGenTest` alone (it cannot be imported together with the others; see RowTypedKAuditLib). -/
#row_typed_audit "M4" 400000
#row_typed_audit_neg 400000
