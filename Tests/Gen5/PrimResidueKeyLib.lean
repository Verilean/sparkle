import Lean
import Sparkle
import Tools.ShippingGen5ConstValueELS
/-! # Residue count under the level-indexed key `Name × List Level` (issue sparkle-ledger-dd4-key): shared measurement
Measurement only. Corpus: every module that runs `#machine_endpoint`, every `X` with `X.machine_source`.
The 47 modules cannot all be imported into one environment (4 `MemNameCollision*` modules conflict with a transitive import),
so the measurement is a command run once per driver (`PrimResidueKey` = 43 modules, `PrimResidueKeyM1..M4` = one module each)
and the raw rows are merged by `scripts/gen5/merge_prim_residue_key.py`.
Traversal from `(X, LS env X)` as in `LSCorpus`: unfold `defnInfo` at the instantiated levels, record each reached `(c, ls)` (levels `normalize`d);
proof terms (theorem-headed applications) are not entered. RESIDUE = reached constants that are not `defnInfo`/`thmInfo`
(constructor, recursor, quot, inductive type former, axiom, opaque).
Fuel check: the traversal stops after `fuel` pops; if a worklist remains the command fails (`throwError`) with the number of
leftover items and the root. `#prim_residue_key_neg tag fuel` is the negative control: it must fail.
Raw rows go to `$KJOB_REPORT_PATH.key.<tag>` (residue rows) and `.roots.<tag>` (root, module, leftover). No theorem, no sorry. -/
open Lean Meta Elab Command
open Tools.ShippingGen5ConstValueE (LS)

namespace Tests.Gen5.PrimResidueKey

def isMachineSource (n : Name) : Bool := match n with | .str _ "machine_source" => true | _ => false

partial def occs (env : Environment) (e : Expr) (acc : Array (Name × List Level)) : Array (Name × List Level) :=
  match e with
  | .const n ls => acc.push (n, ls)
  | .app .. =>
    let f := e.getAppFn
    match f with
    | .const n ls =>
      if (env.find? n).any (·.isTheorem) then acc
      else e.getAppArgs.foldl (fun a x => occs env x a) (acc.push (n, ls))
    | _ => e.getAppArgs.foldl (fun a x => occs env x a) (occs env f acc)
  | .lam _ t b _ | .forallE _ t b _ => occs env b (occs env t acc)
  | .letE _ t v b _ => occs env b (occs env v (occs env t acc))
  | .mdata _ b | .proj _ _ b => occs env b acc
  | _ => acc

def lvlKey (ls : List Level) : String := toString (ls.map (fun l => toString l.normalize))

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.ctorInfo _) => "ctor" | some (.recInfo _) => "rec" | some (.inductInfo _) => "induct"
  | some (.quotInfo _) => "quot" | some (.axiomInfo _) => "axiom" | some (.opaqueInfo _) => "opaque"
  | _ => "none"

/-- reached `(c, key)` pairs from `(root, LS env root)` (with whether the levels are closed) and the worklist left when fuel ran out -/
def reach (env : Environment) (root : Name) (fuel0 : Nat) :
    Std.HashMap (Name × String) Bool × Array (Name × List Level) := Id.run do
  let mut seen : Std.HashMap (Name × String) Bool := {}
  let mut todo : Array (Name × List Level) := #[(root, LS env root)]
  let mut fuel := fuel0
  while fuel > 0 && todo.size > 0 do
    fuel := fuel - 1
    let (n, ls) := todo.back!
    todo := todo.pop
    let k := (n, lvlKey ls)
    if seen.contains k then continue
    seen := seen.insert k (ls.all (fun l => !l.hasParam && !l.hasMVar))
    match env.find? n with
    | some (.defnInfo d) =>
      let body := d.value.instantiateLevelParams d.levelParams ls
      todo := (occs env body #[]).foldl (fun a x => a.push x) todo
    | _ => pure ()
  return (seen, todo)

def machineRoots (env : Environment) : Array Name := Id.run do
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isMachineSource n then
      let x := n.getPrefix
      if (env.find? x).any (·.isDefinition) then roots := roots.push x
  return roots.qsort (fun a b => a.toString < b.toString)

def rootModule (env : Environment) (root : Name) : Name :=
  match env.getModuleIdxFor? (root ++ `machine_source) with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_current

/-- fuel check: every root's traversal must finish (empty worklist), else `throwError` with leftover count and root -/
def checkFuel (env : Environment) (roots : Array Name) (fuel : Nat) : CommandElabM Unit := do
  let mut bad : Array String := #[]
  for r in roots do
    let (_, todo) := reach env r fuel
    if todo.size > 0 then bad := bad.push s!"{r}: {todo.size} todo left"
  if bad.size > 0 then
    throwError "fuel={fuel} exhausted: {bad.size} of {roots.size} roots incomplete (leftover todo count, root):\n{"\n".intercalate bad.toList}"

elab "#prim_residue_key " tag:str fuel:num : command => do
  let env ← getEnv
  let tag := tag.getString
  let fuel := fuel.getNat
  let roots := machineRoots env
  checkFuel env roots fuel
  let mut keys : Std.HashMap (Name × String) (Bool × Nat) := {}   -- residue key -> (closed, roots reaching)
  let mut names : Std.HashMap Name (Std.HashSet String) := {}
  let mut perRootMax := 0
  let mut perRootNameMax := 0
  let mut rootPoly := 0
  let mut mods : Std.HashSet Name := {}
  let mut rootRows := ""
  for r in roots do
    if (env.find? r).any (fun ci => !ci.levelParams.isEmpty) then rootPoly := rootPoly + 1
    let m := rootModule env r
    mods := mods.insert m
    rootRows := rootRows ++ s!"{r}\t{m}\t0\n"
    let (seen, _) := reach env r fuel
    let mut cnt := 0
    let mut nm : Std.HashSet Name := {}
    for ((n, k), closed) in seen.toList do
      if kindOf env n != "none" then
        cnt := cnt + 1
        nm := nm.insert n
        let (c0, m0) := keys.getD (n, k) (closed, 0)
        keys := keys.insert (n, k) (c0 && closed, m0 + 1)
        names := names.insert n ((names.getD n {}).insert k)
    perRootMax := max perRootMax cnt
    perRootNameMax := max perRootNameMax nm.size
  let kinds := ["ctor", "rec", "induct", "quot", "axiom", "opaque"]
  let mut msg := s!"[{tag}] count: {roots.size} roots, {mods.size} modules with `X.machine_source` (modules: {mods.toList.map toString}); fuel {fuel}: all worklists empty; roots whose own decl has levelParams: {rootPoly}\n"
  msg := msg ++ s!"residue rows, Name-only key (PrimTable): {names.size}; level-indexed key (PrimTableK): {keys.size}\n"
  for k in kinds do
    let nk := (names.toList.filter (fun (n, _) => kindOf env n == k)).length
    let kk := (keys.toList.filter (fun ((n, _), _) => kindOf env n == k)).length
    msg := msg ++ s!"  {k}: names {nk}, (name, ls) keys {kk}\n"
  let multi := names.toList.filter (fun (_, s) => s.size > 1)
  msg := msg ++ s!"names with >1 distinct ls: {multi.length} of {names.size}; keys not closed: {(keys.toList.filter (fun (_, (c, _)) => !c)).length}\n"
  msg := msg ++ s!"max residue keys per root: {perRootMax}; max residue names per root: {perRootNameMax}\n"
  logInfo msg
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    let mut raw := ""
    for ((n, k), (c, m)) in keys.toList do raw := raw ++ s!"{n}\t{kindOf env n}\t{k}\tclosed={c}\troots={m}\n"
    IO.FS.writeFile (path ++ ".key." ++ tag) raw
    IO.FS.writeFile (path ++ ".roots." ++ tag) rootRows

/-- negative control: with this (too small) fuel the fuel check must fail; the command errors if it does not -/
elab "#prim_residue_key_neg " fuel:num : command => do
  let env ← getEnv
  let roots := machineRoots env
  let failed ← try checkFuel env roots fuel.getNat; pure none
    catch e => pure (some (← e.toMessageData.toString))
  match failed with
  | some m => logInfo s!"negative control ok: fuel={fuel.getNat} fails as required; first lines:\n{"\n".intercalate (m.splitOn "\n" |>.take 3)}"
  | none => throwError "negative control FAILED: fuel={fuel.getNat} did not exhaust"

end Tests.Gen5.PrimResidueKey
