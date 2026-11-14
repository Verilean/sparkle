import Lean
import Tools.VedU1Entry

/-!
# U1 entry: structure (record) results, read as the tuple of their fields

A declaration whose result is a structure of signals (`RxOut dom`, fields
`Signal dom _`) is not a `Signal defaultDomain _`, so the table reader
(`readTableOfType`) refuses it at `table`.  The synthesizer already treats such a
result as one output port per field (`splitReturnLeaves`, Sparkle/Compiler/Elab.lean):
a field of a structure is named by its field name (`prefix_field` under a prefix), the
two sides of a product `prefix_0`, `prefix_1`, left-first.

This file reads the result type as a tree whose leaves are `Signal defaultDomain _`
(a `Prod`, a single-constructor non-recursive structure, or a signal) and builds
the statement term the same way the product entry does (`bundledStmt`):

    fun xs => bundle2 (D xs).f₁ (bundle2 (D xs).f₂ …)

where `D` is the ORIGINAL declaration (or `@D defaultDomain`) and `fᵢ` are the
structure's own projection functions, in constructor field order.  Nothing is
trusted:

* the correspondence field ↦ output port is the kernel's: the statement is
  `U1Stmt c m (fun xs => bundle2 …)`, the contract's i-th output port is compared
  with the i-th projection of THIS term by `OutputsStmt`, so swapped fields,
  a wrong width or a missing field fail in `ShapeStmt` / the proof;
* the port names are derived from the structure by the compiler's rule, and the
  entry REQUIRES them to be exactly the returned module's output names, in order
  (`vedU1EntryOn`);
* `U1Stmt` is unchanged (`f : c.table.Ty`: the lambda's type is the table's);
  the statement is built from the declaration, the entry (checkU1E) is the standard one.

Everything else is the standard entry: one `synthesizeCombinational` call, the
returned module, the standard checker (register-free bodies for more than one
output), kernel, strict audit.  The command is `#ved_u1_struct decl`.
-/

namespace Tools.VedU1StructOut

open Lean Meta Elab Term Command
open Tools.VedU1Contract Tools.VedU1Entry

/-- The leaves of the result tree: statement (bundled signal) and port names,
left-first.  `pre?` is the compiler's name prefix (`splitReturnLeaves`). -/
partial def bundleTree (ty e : Lean.Expr) (pre? : Option String) :
    MetaM (Lean.Expr × List String) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFn with
  | .const ``Sparkle.Core.Signal.Signal _ => pure (e, [pre?.getD "out"])
  | .const ``Prod _ =>
    let some (a, b) := (match ty.getAppArgs with | #[a, b] => some (a, b) | _ => none)
      | throwError "ved_struct%: malformed product {ty}"
    let p := pre?.getD "out"
    let (l, ln) ← bundleTree a (← mkAppM ``Prod.fst #[e]) (some (p ++ "_0"))
    let (r, rn) ← bundleTree b (← mkAppM ``Prod.snd #[e]) (some (p ++ "_1"))
    return (← mkAppM ``Sparkle.Core.Signal.bundle2 #[l, r], ln ++ rn)
  | .const ind _ =>
    let some (.inductInfo iv) := (← getEnv).find? ind
      | throwError "ved_struct%: {ty} is not a structure of signals"
    unless iv.ctors.length == 1 && !iv.isRec && iv.numIndices == 0 do
      throwError "ved_struct%: {ind} is not a single-constructor structure"
    let some sinfo := getStructureInfo? (← getEnv) ind
      | throwError "ved_struct%: {ind} is not a structure"
    if sinfo.fieldNames.isEmpty then throwError "ved_struct%: {ind} has no fields"
    -- fields, constructor order (the compiler's order: the ctor's binder names)
    let mut leaves : Array (Lean.Expr × List String) := #[]
    for f in sinfo.fieldNames do
      let pj ← mkProjection e f
      let fty ← inferType pj
      let nm := match pre? with | none => f.toString | some p => p ++ "_" ++ f.toString
      leaves := leaves.push (← bundleTree fty pj (some nm))
    -- right-nested pairs: f₁, (f₂, (… fₙ))
    let mut acc := leaves.back!
    for i in (List.range (leaves.size - 1)).reverse do
      let (l, ln) := leaves[i]!
      acc := (← mkAppM ``Sparkle.Core.Signal.bundle2 #[l, acc.1], ln ++ acc.2)
    return acc
  | _ => throwError "ved_struct%: {ty} is not a signal, a product or a structure"

/-- Does the result type contain a structure (so that the product entry does not apply)? -/
def stmtOfStruct (declName : Name) : TermElabM (Lean.Expr × Nat × List String) := do
  let (stmt, nDom) ← try specialiseDomain declName catch e => refuse declName "table" e.toMessageData
  let b ← forallTelescopeReducing (← inferType stmt) fun xs res => do
    let (bt, ns) ← try bundleTree res (mkAppN stmt xs) none
      catch e => refuse declName "table" e.toMessageData
    return (← mkLambdaFVars xs bt, ns)
  -- the table of the bundled statement (domain, widths, Bool/BitVec leaves only)
  let tbl ← try readTableOfType declName (← inferType b.1) catch e => refuse declName "table" e.toMessageData
  unless tbl.out.flat.length == b.2.length do
    refuse declName "table" m!"{tbl.out.flat.length} projections for {b.2.length} port names"
  return (b.1, nDom, b.2)

/-- The entry: `stmtOf` as before; a structure result goes through `stmtOfStruct`. -/
def vedU1EntryStruct (declName : Name) : TermElabM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design × Name × Nat) := do
  let (stmt, nDom, names) ←
    try stmtOf declName catch e =>
      if ← isRefusal e then stmtOfStruct declName else throw e
  let (m, d) ← try Sparkle.Compiler.Elab.synthesizeCombinational declName
    catch e => refuse declName "synthesis" e.toMessageData
  let (thm, _) ← vedU1EntryOn declName stmt nDom names m
  return (m, d, thm, nDom)

elab "#ved_u1_struct " id:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, _, thm, nDom) ← vedU1EntryStruct decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U1 OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\n{repr m}"

end Tools.VedU1StructOut
