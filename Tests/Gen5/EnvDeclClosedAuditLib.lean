import Lean
import Sparkle
import Tools.ShippingGen5ConstValueESL
import Tests.Gen5.PrimResidueKeyLib
/-! # `EnvDeclClosed` audit (issue sparkle-ledger-dd4-sound, SoundS3): a META AUDIT, NOT a proof.
`EnvDeclClosed env` (Tools.ShippingGen5ConstValueESL) says: every stored `ci.type` and every `defnInfo` value has `lbr = 0` (no loose bound variable).
Here `lbr` is evaluated on the real environment by `lbrM`, a memoised transcription of `Tools.ShippingGen5ConstValueESoundK.lbr` (same clauses, `Nat` subtraction included), and cross-checked
against Lean's own `Expr.looseBVarRange`.
Two scopes, per driver environment (the 47 modules do not import together: 43 in one environment, 4 `MemNameCollision*` modules in one environment each, as in `PrimResidueKey*`):
* REACHED: the declarations reached from the corpus roots (same roots / traversal as `PrimResidueKey*`: `reach` from `(X, LS env X)`, fuel-checked by `checkFuel`).
* ALL: every constant of the environment (a superset: this is the literal `EnvDeclClosed env` for that environment).
Counterexamples are enumerated (name, part, lbr); none is hidden. If the traversal fuel is exceeded (`checkFuel`) or elaboration times out, the command FAILS and returns no partial result.
Raw rows: `$KJOB_REPORT_PATH.dcl.<tag>` (not in the source tree). No theorem. -/
open Lean Meta Elab Command
open Tests.Gen5.PrimResidueKey
open Tools.ShippingGen5ConstValueE (LS)

namespace Tests.Gen5.EnvDeclClosedAudit

/-- Memoised transcription of `Tools.ShippingGen5ConstValueESoundK.lbr` (cache keyed by the structurally-hashed `Expr`). -/
partial def lbrM (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  match e with
  | .bvar i => return i + 1
  | .fvar _ | .mvar _ | .lit _ | .sort _ | .const .. => return 0
  | _ =>
    if let some r := (← get).get? e then return r
    let r ← match e with
      | .app f a => return max (← lbrM f) (← lbrM a)
      | .lam _ A b _ | .forallE _ A b _ => do
        let a ← lbrM A
        let b ← lbrM b
        pure (max a (b - 1))
      | .letE _ A v b _ => do
        let a ← lbrM A
        let v ← lbrM v
        let b ← lbrM b
        pure (max (max a v) (b - 1))
      | .mdata _ x | .proj _ _ x => lbrM x
      | _ => pure 0
    modify (·.insert e r)
    return r

/-- violations of `EnvDeclClosed` for one declaration: `(part, lbr)` for the type and (for `defnInfo`) the value, plus a disagreement with `Expr.looseBVarRange`. -/
def ciViolations (ci : ConstantInfo) : StateM (Std.HashMap Expr Nat) (Array (String × Nat)) := do
  let mut out : Array (String × Nat) := #[]
  let t ← lbrM ci.type
  if t != 0 then out := out.push ("type", t)
  if ci.type.looseBVarRange != t then out := out.push ("type-range-mismatch", ci.type.looseBVarRange)
  if let .defnInfo d := ci then
    let v ← lbrM d.value
    if v != 0 then out := out.push ("value", v)
    if d.value.looseBVarRange != v then out := out.push ("value-range-mismatch", d.value.looseBVarRange)
  return out

structure Tally where
  decls : Nat := 0
  defns : Nat := 0
  missing : Nat := 0
  bad : Array (Name × String × Nat) := #[]

def scan (env : Environment) (names : Array Name) : Tally × Nat := Id.run do
  let mut t : Tally := {}
  let mut cache : Std.HashMap Expr Nat := {}
  for n in names do
    match env.find? n with
    | none => t := { t with missing := t.missing + 1 }
    | some ci =>
      let (vs, c') := (ciViolations ci).run cache
      cache := c'
      t := { t with decls := t.decls + 1, defns := t.defns + (if ci.isDefinition then 1 else 0) }
      for (p, k) in vs do t := { t with bad := t.bad.push (n, p, k) }
  return (t, cache.size)

def allNames (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do out := out.push n
  for (n, _) in env.constants.map₂.toList do out := out.push n
  return out

def fmtBad (bad : Array (Name × String × Nat)) : String :=
  if bad.isEmpty then "  (none)" else "\n".intercalate (bad.toList.map fun (n, p, k) => s!"  COUNTEREXAMPLE {n}\t{p}\t{k}")

elab "#env_decl_closed_audit " tag:str fuel:num : command => do
  let env ← getEnv
  let tag := tag.getString
  let fuel := fuel.getNat
  let roots := machineRoots env
  checkFuel env roots fuel   -- throws (no partial result) when any traversal runs out of fuel
  let mut reached : Std.HashSet Name := {}
  let mut mods : Std.HashSet Name := {}
  for (r, _) in roots do
    mods := mods.insert (rootModule env r)
    let (seen, todo) := reach env r fuel
    if todo.size > 0 then throwError "fuel exhausted at root {r} (should have been caught by checkFuel)"
    for ((n, _), _) in seen.toList do reached := reached.insert n
  let reachedArr := reached.toArray.qsort (fun a b => a.toString < b.toString)
  let (tr, cr) := scan env reachedArr
  let all := allNames env
  let (ta, ca) := scan env all
  let msg := s!"[{tag}] count: {roots.size} roots, {mods.size} modules (modules: {mods.toList.map toString}); fuel {fuel}: all worklists empty\n" ++
    s!"REACHED: {reachedArr.size} distinct names, {tr.decls} found in env ({tr.defns} defnInfo), {tr.missing} not in env, counterexamples: {tr.bad.size} (cache {cr})\n{fmtBad tr.bad}\n" ++
    s!"ALL: {all.size} constants, {ta.decls} scanned ({ta.defns} defnInfo), {ta.missing} missing, counterexamples: {ta.bad.size} (cache {ca})\n{fmtBad (ta.bad.extract 0 50)}"
  logInfo msg
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    let mut raw := ""
    for n in reachedArr do raw := raw ++ s!"{n}\n"
    IO.FS.writeFile (path ++ ".dcl." ++ tag) raw
    IO.FS.writeFile (path ++ ".dcl-summary." ++ tag) s!"{tag}\troots={roots.size}\tmods={mods.size}\treached={reachedArr.size}\treached_found={tr.decls}\treached_bad={tr.bad.size}\tall={all.size}\tall_bad={ta.bad.size}\n"

/-- Negative controls. (1) With fuel 50 the fuel check must fail (no partial result). (2) The detector flags a `ConstantInfo` whose type / value has a loose bound variable. -/
elab "#env_decl_closed_audit_neg " fuel:num : command => do
  let env ← getEnv
  let roots := machineRoots env
  let failed ← try checkFuel env roots fuel.getNat; pure none
    catch e => pure (some (← e.toMessageData.toString))
  match failed with
  | some _ => logInfo s!"negative control (fuel) ok: fuel={fuel.getNat} fails as required"
  | none => throwError "negative control FAILED: fuel={fuel.getNat} did not exhaust"
  let ok : Expr := .lam `x (.sort 0) (.bvar 0) .default
  let openV : Expr := .lam `x (.sort 0) (.bvar 1) .default
  let mk (ty v : Expr) : ConstantInfo := .defnInfo { name := `neg, levelParams := [], type := ty, value := v, hints := .opaque, safety := .safe }
  let run (ci : ConstantInfo) := ((ciViolations ci).run {}).1
  let a := run (mk (.sort 1) ok)
  let b := run (mk (.sort 1) openV)
  let c := run (mk (.bvar 0) ok)
  unless a.isEmpty && b == #[("value", 1)] && c == #[("type", 1)] do
    throwError "negative control FAILED: detector gave {a} / {b} / {c}"
  logInfo s!"negative control (detector) ok: closed {a}, open value {b}, open type {c}"

end Tests.Gen5.EnvDeclClosedAudit
