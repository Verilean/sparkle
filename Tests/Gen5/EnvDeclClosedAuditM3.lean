import Lean
import Sparkle
import Tests.Compiler.MemNameCollisionGateTypedAllTest
import Tests.Gen5.EnvDeclClosedAuditLib
/-! Driver: one MemNameCollision module alone (it cannot be imported together with the others; see EnvDeclClosedAuditLib). -/
#env_decl_closed_audit "M3" 400000
