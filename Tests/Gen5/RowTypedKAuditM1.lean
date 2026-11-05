import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionDesignTest
import Tests.Gen5.RowTypedKAuditLib
/-! Driver: module `Tests.Compiler.MemNameCollisionDesignTest` alone (it cannot be imported together with the others; see RowTypedKAuditLib). -/
#row_typed_audit "M1" 400000
#row_typed_audit_neg 400000
