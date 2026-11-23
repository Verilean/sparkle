import Tools.VedU1Entry
import Tools.VedU1Contract

/-!
# The leaf cache of the nested route: keyed by the leaf module VALUE and its stored statement (CANDIDATE)

A leaf (a module without instances) that is both a direct child of the parent and a grandchild (a child of a middle module, as `keccakRcHW`
in R163's `wKeccakF`) gets its `U1Stmt` theorem from the ordinary child stage (`checkU1E`) under `<decl>.ved_child.<leaf>`, once per
declaration that has it as a child.  With the option `ved.compose.leafCache` (default off) the child stage first looks for an already
stored theorem of the same leaf, and reuses it ONLY after the check below; a name never hits alone:

* the theorem's type is `U1Stmt c m s` where `c`, `m` are the four stored constants of the theorem's base (`<base>.ved_contract`,
  `ved_mod`, `ved_outs`, `ved_body`, the names `Names.ofBase` gives) and `s` IS the leaf declaration's statement term (`==`);
* `<base>.ved_mod` holds `toExpr` of the leaf MODULE of the parent's design (by value, not by name), `<base>.ved_contract` holds the
  contract expression the child stage would build for this leaf (`contractOf` of its table, output names, clock/reset, module),
  `ved_outs` and `ved_body` hold the leaf's output ports and the arrangement of its body;
* for a leaf with several outputs, `<base>.ved_bundle` holds the statement term.

Nothing here is a theorem: the check only decides whether a theorem the child stage produced earlier IS the theorem the stage would
produce now (same module value, same contract value, same statement term).  A same-name different leaf, or a different statement, finds no
candidate and the ordinary stage runs.  Observed on toys; not a ledger row.
-/

namespace Tools.VedU2HierRecLeafCache

open Lean Meta Elab Term
open Tools.VedU1Contract Tools.VedU1Entry

register_option ved.compose.leafCache : Bool := {
  defValue := false
  descr := "nested route: a leaf child whose U1Stmt theorem was produced earlier (same module value, same statement) reuses it"
}

/-- `base` is a stored child base of the leaf `cm`: the constants of `Names.ofBase base` hold exactly what the child stage would
define for this leaf, and the theorem `base.ved_u1` states `U1Stmt <contract> <mod> stmt`.  The reason for a refusal, else `none`. -/
def checkStoredLeaf (base : Name) (stmt : Lean.Expr) (cm : Sparkle.IR.AST.Module) (tbl : DeclTable) (outNames : List String)
    (multi : Bool) : MetaM (Option String) := do
  let env ← getEnv
  let nm := Names.ofBase base
  let some (.thmInfo ti) := env.find? nm.thm | return some s!"{nm.thm} is not a theorem"
  unless ti.type.getAppFn.isConstOf ``U1Stmt && ti.type.getAppNumArgs == 3 do return some s!"{nm.thm}: the stored statement is not U1Stmt"
  let args := ti.type.getAppArgs
  unless args[0]! == Lean.mkConst nm.contract && args[1]! == Lean.mkConst nm.mod do
    return some s!"{nm.thm}: the statement is not over the stored constants {nm.contract}, {nm.mod}"
  unless args[2]! == stmt do return some s!"{nm.thm}: the stored statement term is not the declaration's own"
  let some (.defnInfo mi) := env.find? nm.mod | return some s!"{nm.mod} is not a definition"
  unless mi.value == toExpr cm do return some s!"{nm.mod} is not the leaf module {cm.name} (same name, different module)"
  let clkRst := clkRstOf cm
  let tbl' := { tbl with binders := tbl.binders.map fun b => (b.splitOn "._@.").headD b }
  let cE := mkAppN (Lean.mkConst ``contractOf) #[toExpr tbl', toExpr outNames, toExpr clkRst, Lean.mkConst nm.mod]
  let some (.defnInfo ci) := env.find? nm.contract | return some s!"{nm.contract} is not a definition"
  unless ci.value == cE do return some s!"{nm.contract} is not the contract of this leaf"
  let c := contractOf tbl' outNames clkRst cm
  let some (.defnInfo oi) := env.find? nm.outs | return some s!"{nm.outs} is not a definition"
  unless oi.value == toExpr c.outputs do return some s!"{nm.outs} does not hold the leaf's output ports"
  let some (.defnInfo bi) := env.find? nm.body | return some s!"{nm.body} is not a definition"
  unless bi.value == toExpr (orderBody cm.body) do return some s!"{nm.body} does not hold the arrangement of the leaf's body"
  if multi then
    let some (.defnInfo gi) := env.find? (base ++ `ved_bundle) | return some s!"{base}.ved_bundle is missing"
    unless gi.value == stmt do return some s!"{base}.ved_bundle is not the declaration's statement"
  return none

/-- The stored child bases of the leaf `cdecl` in the environment of the current file (`<..>.ved_child.<cdecl>`): a base `b` with
`b.ved_u1` a constant and `b = <prefix>.ved_child ++ cdecl`.  Candidates only; every one is checked by `checkStoredLeaf`. -/
def candidateBases (cdecl : Name) : MetaM (List Name) := do
  let env ← getEnv
  let suffix := `ved_child ++ cdecl
  return env.constants.map₂.foldl (fun acc n _ =>
    match n with
    | .str b "ved_u1" => if suffix.isSuffixOf b then b :: acc else acc
    | _ => acc) []

/-- The first candidate base that passes the check (module value, contract value, statement term), if any. -/
def findStoredLeaf (cdecl : Name) (stmt : Lean.Expr) (cm : Sparkle.IR.AST.Module) (tbl : DeclTable) (outNames : List String)
    (multi : Bool) : MetaM (Option Name) := do
  for b in ← candidateBases cdecl do
    if (← checkStoredLeaf b stmt cm tbl outNames multi).isNone then return some b
  return none

end Tools.VedU2HierRecLeafCache
