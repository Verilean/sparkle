import Tools.VedU1HierEntry

/-!
# Check for `#ved_u1_hier` on declarations whose design has NO child module (`Tools/VedU1HierEntry.lean`)

The small examples here are NOT part of the 327 inventory rows.

The generated script of a design with no instance and no child used to contain empty simp elements
(`cellVals, , , body`), which did not parse (`expected ']'`).  The generator now leaves no empty
element, unfolds the file-local callees of the statement, and finishes operator bodies with the
leaf entry's simp set.

* ENTRY RUNS: a `Signal.mux` parent and a parent calling two file-local helpers that the synthesis
  inlines; the exact theorem type and the standard three axioms are checked.
* CONTROL: the checker `checkU1H` on the returned module with ONE piece altered (the mux branches
  exchanged) is refused at `[proof]` and leaves no constant of its base.
-/

namespace Tests.Ved.U1HierFlatCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry

def fmux (c : Signal defaultDomain Bool) (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.mux c a b

def fadd (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := a + b
def fsub (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := a - b

def falu (op : Signal defaultDomain Bool) (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.mux op (fsub a b) (fadd a b)

/-- Same shape as `fmux`, for the control. -/
def fctl (c : Signal defaultDomain Bool) (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.mux c a b

def expectedOf (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U1HStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

def checkOk (decl : Name) : CommandElabM Unit := liftTermElabM do
  let (_, d, thm, nDom, _) ← vedU1HierEntry decl
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U1HStmt c m d decl"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"hier OK {thm} children {d.modules.map (·.name)}"

/-- info: hier OK Tests.Ved.U1HierFlatCheck.fmux.ved_u1 children [] -/
#guard_msgs in
run_cmd checkOk ``fmux

/-- info: hier OK Tests.Ved.U1HierFlatCheck.falu.ved_u1 children [] -/
#guard_msgs in
run_cmd checkOk ``falu

/-- The control: the mux branches exchanged in the returned module -> refused at `[proof]`, nothing left. -/
def controlRun : CommandElabM Unit := liftTermElabM do
  let decl := ``fctl
  let (m, d) ← Sparkle.Compiler.Elab.synthesizeCombinational decl
  let before := (← getEnv).constants.map₂.toList.filterMap fun (n, _) => if decl.isPrefixOf n then some n else none
  let swap : Stmt → Stmt
    | .assign l (.op .mux [c, a, b]) => .assign l (.op .mux [c, b, a])
    | s => s
  let (stmt, nDom) ← specialiseDomain decl
  let r ← try
      discard <| checkU1H decl stmt nDom { m with body := m.body.map swap } d
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  match r with
  | none => throwError "the altered module was ACCEPTED"
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [proof]" do throwError "unexpected refusal: {msg}"
  let nm := HNames.ofBase decl
  for n in [nm.mod, nm.design, nm.contract, nm.outs, nm.body, nm.thm] do
    if (← getEnv).contains n then throwError "{n} is still in the environment after the refusal"
  let after := (← getEnv).constants.map₂.toList.filterMap fun (n, _) => if decl.isPrefixOf n then some n else none
  unless after.all before.contains do throwError "constants left after the refusal"
  logInfo m!"control refused"

/-- info: control refused -/
#guard_msgs in
run_cmd controlRun

end Tests.Ved.U1HierFlatCheck
