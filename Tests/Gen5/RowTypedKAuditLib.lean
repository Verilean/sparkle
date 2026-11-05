import Lean
import Sparkle
import Tests.Gen5.PrimResidueKeyLib
/-! # `OblRowTypedK` audit (issue sparkle-ledger-dd4-sound): a META AUDIT, NOT a proof.
For every residue key `(c, ls)` of the corpus (the same keys as `PrimResidueKey*`: reached from `(root, LS env root)`, kind ctor/rec/induct/quot/axiom/opaque),
this checks mechanically, in the environment of the module that is imported:
* arity: `ls.length = ci.levelParams.length` (so `instantiateLevelParams` replaces every parameter);
* const: `inferType (mkConst c ls)` against `ci.type.instantiateLevelParams ci.levelParams ls` (syntactic equality, else `isDefEq`, else mismatch);
* spine: for every prefix `xs[:j]` of the binder telescope of that type (fresh fvars), `inferType (mkAppN (mkConst c ls) xs[:j])` against `instForall T0 xs[:j]` (the syntactic result type of the `prim` rule);
* sort class of the declared type (`Prop` / `Type 0` / higher / other): informational, a value of type `T0` can be a `Dyn` (`ty : Type`) only when `T0 : Type`.
What this does NOT show: any `RowTypedAt` (no row exists in this audit; `row.den`, `ArgsDenK`, `TDenK` are not touched), nor the kernel typing of arguments. A match shows only that the
`ConstantInfo.type` / `instForall` side of the obligation agrees with Lean's own `inferType` on the key. Raw rows: `$KJOB_REPORT_PATH.audit.<tag>` (not in the source tree). No theorem. -/
open Lean Meta Elab Command
open Tests.Gen5.PrimResidueKey
open Tools.ShippingGen5ConstValueE (LS instForall)

namespace Tests.Gen5.RowTypedKAudit

/-- the traversal of `PrimResidueKey.reach`, keeping the level lists (same worklist discipline: each `(name, ls)` is pushed once) -/
def reachLs (env : Environment) (root : Name) (fuel0 : Nat) :
    Std.HashMap (Name × String) (List Level) × Array (Name × List Level) := Id.run do
  let r0 := LS env root
  let mut seen : Std.HashMap (Name × String) (List Level) := ({} : Std.HashMap (Name × String) (List Level)).insert (root, lvlKey r0) r0
  let mut todo : Array (Name × List Level) := #[(root, r0)]
  let mut fuel := fuel0
  while fuel > 0 && todo.size > 0 do
    fuel := fuel - 1
    let (n, ls) := todo.back!
    todo := todo.pop
    match env.find? n with
    | some (.defnInfo d) =>
      let body := d.value.instantiateLevelParams d.levelParams ls
      for (c, cl) in occs env body #[] do
        let k := (c, lvlKey cl)
        if !seen.contains k then
          seen := seen.insert k cl
          todo := todo.push (c, cl)
    | _ => pure ()
  return (seen, todo)

def sortClass : Level → String
  | l => match l.normalize with
    | .zero => "Prop"
    | .succ .zero => "Type0"
    | .succ (.succ _) => "higher"
    | _ => "other"

/-- `a == b` syntactically, else defeq, else mismatch -/
def cmpExpr (a b : Expr) : MetaM String := do
  if a == b then return "syn"
  if (← try isDefEq a b catch _ => pure false) then return "defeq" else return "mismatch"

def worse (a b : String) : String :=
  let rk (s : String) := if s == "mismatch" then 2 else if s == "defeq" then 1 else 0
  if rk a ≥ rk b then a else b

/-- one key: `name \t kind \t lsKey \t arity \t const \t spine \t sort \t binders` -/
def auditKey (n : Name) (ls : List Level) (shift : Bool := false) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? n | return s!"{n}\t{kindOf env n}\t{lvlKey ls}\tabsent\t-\t-\t-\t0"
  let arity := if ls.length == ci.levelParams.length then "ok" else "bad"
  let ls' := if shift then ls.map Level.succ else ls
  let T0 := ci.type.instantiateLevelParams ci.levelParams ls'
  let t1 ← try inferType (mkConst n ls) catch _ => pure (mkConst `inferTypeFailed)
  let c1 ← cmpExpr t1 T0
  let sc ← try (do let s ← whnf (← inferType T0); match s with | .sort l => pure (sortClass l) | _ => pure "nonsort") catch _ => pure "err"
  let (c2, nb) ← try (forallTelescope T0 fun xs _ => do
      let mut acc := "syn"
      for j in [0:xs.size + 1] do
        let pre := xs.extract 0 j
        let t ← try instantiateMVars (← inferType (mkAppN (mkConst n ls) pre)) catch _ => pure (mkConst `inferTypeFailed)
        acc := worse acc (← cmpExpr t (instForall T0 pre.toList))
      pure (acc, xs.size)) catch _ => pure ("err", 0)
  return s!"{n}\t{kindOf env n}\t{lvlKey ls}\t{arity}\t{c1}\t{c2}\t{sc}\t{nb}"

def collectKeys (env : Environment) (fuel : Nat) : CommandElabM (Std.HashMap (Name × String) (List Level)) := do
  let roots := machineRoots env
  let mut keys : Std.HashMap (Name × String) (List Level) := {}
  let mut bad : Array String := #[]
  for (r, _) in roots do
    let (seen, todo) := reachLs env r fuel
    if todo.size > 0 then bad := bad.push s!"{r}: {todo.size} todo left"
    for ((n, k), ls) in seen.toList do
      if kindOf env n != "none" then keys := keys.insert (n, k) ls
  if bad.size > 0 then throwError "fuel={fuel} exhausted: {bad.size} roots incomplete:\n{"\n".intercalate bad.toList}"
  return keys

def tally (rows : Array String) (col : Nat) : List (String × Nat) :=
  let m := rows.foldl (fun (m : Std.HashMap String Nat) r => let k := (r.splitOn "\t")[col]!; m.insert k (m.getD k 0 + 1)) {}
  m.toList.toArray.qsort (fun a b => a.1 < b.1) |>.toList

elab "#row_typed_audit " tag:str fuel:num : command => do
  let env ← getEnv
  let keys ← collectKeys env fuel.getNat
  let mut rows : Array String := #[]
  for ((n, _), ls) in keys.toList do
    rows := rows.push (← liftTermElabM (auditKey n ls))
  let sorted : Array String := rows.qsort (· < ·)
  let fmt (c : Nat) := ", ".intercalate ((tally sorted c).map fun (k, v) => s!"{k} {v}")
  logInfo s!"[{tag.getString}] audited keys: {sorted.size}\nkind: {fmt 1}\narity: {fmt 3}\nconst inferType vs instantiateLevelParams: {fmt 4}\nspine (all prefixes) inferType vs instForall: {fmt 5}\nsort of declared type: {fmt 6}"
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    IO.FS.writeFile (path ++ ".audit." ++ tag.getString) ("\n".intercalate sorted.toList ++ "\n")

/-- negative control: comparing against the type instantiated at the WRONG levels (`ls` shifted by `succ`) must produce mismatches on level-polymorphic keys -/
elab "#row_typed_audit_neg " fuel:num : command => do
  let env ← getEnv
  let keys ← collectKeys env fuel.getNat
  let mut mism : Nat := 0
  let mut poly : Nat := 0
  for ((n, _), ls) in keys.toList do
    if !ls.isEmpty then
      poly := poly + 1
      let r ← liftTermElabM (auditKey n ls true)
      if (r.splitOn "\t")[4]! == "mismatch" then mism := mism + 1
  if mism == 0 then throwError "negative control FAILED: no mismatch among {poly} level-polymorphic keys"
  logInfo s!"negative control ok: {mism} of {poly} level-polymorphic keys mismatch when the levels are shifted"

end Tests.Gen5.RowTypedKAudit
