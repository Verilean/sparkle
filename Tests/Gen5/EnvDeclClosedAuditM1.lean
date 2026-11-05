import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionDesignTest
import Tests.Gen5.EnvDeclClosedAuditLib
/-! Driver: one MemNameCollision module alone (it cannot be imported together with the others; see EnvDeclClosedAuditLib). -/
#env_decl_closed_audit "M1" 400000
