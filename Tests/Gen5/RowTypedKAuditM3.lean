import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGateTypedAllTest
import Tests.Gen5.RowTypedKAuditLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGateTypedAllTest` alone (it cannot be imported together with the others; see RowTypedKAuditLib). -/
#row_typed_audit "M3" 400000
#row_typed_audit_neg 400000
