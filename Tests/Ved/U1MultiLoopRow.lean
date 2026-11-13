import Tools.VedU1Entry

/-!
# Shared commands for the `Signal.loop` row checks (sparkle-ved-u1-multiloop)

`#ved_u1_row M n` runs `#ved_u1` on the `private` declaration `n` of module `M` and the strict audit;
`checkRows` compares each stored type with `==` against `U1Stmt <decl>.ved_contract <decl>.ved_mod <decl>`
and checks the axioms are within std3.  Used by `U1MultiLoopCheck` (PR: representative rows and the
refusal controls), `U1MultiLoopFull1..4` (the other rows) and `U1MultiLoopAll` (all 28 rows together).
-/

namespace Tests.Ved.U1MultiLoopRow

open Lean Elab Command Term Meta
open Tools.VedU1Contract Tools.VedU1Entry

/-- the `private` declaration `user` of module `modName` (`_private.<mod>.0.<user>`) -/
def privName (modName user : Name) : Name :=
  Name.mkNum (`_private ++ modName) 0 ++ user

/-- the declaration of a row: the `private` declaration `user` of module `m`, or the public declaration `user`
when `m` is anonymous -/
def declOf (m user : Name) : Name := if m.isAnonymous then user else privName m user

/-- `#ved_u1` for a public declaration (full name), with the strict audit -/
elab "#ved_u1_pub " n:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload n
  Command.liftTermElabM do
    let (_, _, thm, _) ← vedU1EntryS decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    logInfo m!"VED U1 OK {decl}: {Tools.VedStrictAudit.showNames r.axioms}"

/-- `#ved_u1` for a `private` declaration named by its module and user-facing name -/
elab "#ved_u1_row " m:ident n:ident : command => do
  let decl := privName m.getId n.getId
  Command.liftTermElabM do
    let (_, _, thm, _) ← vedU1EntryS decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    logInfo m!"VED U1 OK {n.getId}: {Tools.VedStrictAudit.showNames r.axioms}"

/-- the stored type is `U1Stmt c m F` with `F` the bare constant (no domain argument on these rows),
compared with `==`; axioms within std3 -/
def checkRow (decl : Name) : CoreM Unit := do
  let nm := Names.ofBase decl
  let thm := decl ++ `ved_u1
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst decl]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m {decl}"
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) do throwError "{thm}: axioms {ax}"

/-- `checkRow` on every `(module, name)` of `rows` -/
def checkRows (rows : List (Name × Name)) : CommandElabM Unit := liftCoreM do
  for (m, n) in rows do checkRow (declOf m n)
  logInfo m!"OK {rows.length} rows: stored type = U1Stmt c m F, axioms within std3"

end Tests.Ved.U1MultiLoopRow
