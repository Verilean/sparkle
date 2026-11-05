import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGateDesignTest
import Tests.Gen5.RowTypedKAuditLib
/-! Driver: module `Tests.Compiler.MemNameCollisionGateDesignTest` alone (it cannot be imported together with the others; see RowTypedKAuditLib). -/
#row_typed_audit "M2" 400000
#row_typed_audit_neg 400000
