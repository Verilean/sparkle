import Tools.VedU2HierRegEntry
import Tools.VedStrictAudit
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Helpers of `Tests/Ved/ComposeStepCheck.lean`

The helpers the composed-step Check shares with `Tests/Ved/U2HierWireCheck.lean` (copied from there, same definitions), in a
module that imports only the checker.  `ComposeStepCheck` used to import `Tests.Ved.U2HierWireCheck` for them, a ~470 s
module that was rebuilt on every change of `Tools/VedU2HierMultiChain.lean`.

`std3`, `std3Only` (the axioms of a theorem are within the standard three), `expectedOf` (the checker's exact expected
statement `U2HRStmt`), `synthOf` (the real synthesis), `localConsts`, `expectRefused` (the checker refuses an altered
`(m, d)` at a named stage and leaves no constant behind), `setConnAt` (replace one connection of one instance).
-/

namespace Tests.Ved.ComposeCheckUtil

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
  Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- MACHINE check: every axiom in the reachable closure of `n` is one of the standard three. -/
def std3Only (n : Name) : CoreM Unit := do
  let axs ← collectAxioms n
  unless axs.all (std3.contains ·) do throwError "{n}: axioms outside the standard three: {axs}"

/-- The checker's exact expected statement for `decl` (the H2b statement, UNCHANGED). -/
def expectedOf (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

def synthOf (decl : Name) : CommandElabM (Sparkle.IR.AST.Module × Design) := liftTermElabM do
  Sparkle.Compiler.Elab.synthesizeCombinational decl

def localConsts : CommandElabM NameSet := do
  return (← getEnv).constants.map₂.toList.foldl (fun s (n, _) => s.insert n) {}

def expectRefused (decl : Name) (stage : String) (needle : String) (m : Sparkle.IR.AST.Module)
    (d : Design) : CommandElabM Unit := do
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let r ← try
      discard <| checkU2HR decl stmt nDom m d none
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  let pre := s!"VED U1 REFUSED {decl} [{stage}]"
  match r with
  | none => throwError "{decl}: expected a refusal at [{stage}], the checker ACCEPTED"
  | some msg =>
    unless msg.startsWith pre do throwError "expected {pre} (needle `{needle}`), got: {msg}"
    if needle == "?" then logInfo m!"{pre}: {msg.take 260}"
    else unless (msg.splitOn needle).length > 1 do throwError "the refusal does not name `{needle}`: {msg}"
  let after ← localConsts
  let added := after.toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left after the refusal: {added}"

/-- Replace the connection of port `p` by `e` in the instance NUMBER `k` (0-based). -/
def setConnAt (k : Nat) (p : String) (e : Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  let rec go : List Stmt → Nat → List Stmt
    | [], _ => []
    | s :: r, n =>
      match s with
      | .inst mn i cs => (if n == k then .inst mn i (cs.map fun q => if q.1 == p then (p, e) else q) else s) :: go r (n + 1)
      | _ => s :: go r n
  go b 0

end Tests.Ved.ComposeCheckUtil
