import Lean
import Sparkle
import Tests.Gen5.PrimResidueKeyLib
/-! # Residue under a STOP SET (issue sparkle-ledger-dd4-final, Q-A): shared measurement
Measurement only. Same traversal, roots and residue as `PrimResidueKey` (unchanged, reused), plus a stop set:
a reached `(c, ls)` with `c` a definition whose name lies in the stop namespace (default `Sparkle.Core.Signal`, i.e. every definition of
`Sparkle/Core/Signal.lean`: `Signal.loop`, `Signal.register`, `Signal.mux`, `Signal.map`, instances, ...) is recorded as STOPPED and its body is NOT unfolded
(an opaque row of PT). Each root is measured twice: without stop set (= `PrimResidueKey`) and with the stop set.
Fuel exhausted in either mode => `throwError` (no partial result).
For every stopped `(c, ls)` we also check whether its declared type, instantiated at `ls`, fits `Dyn` (`Type 0`): every binder is a `Type`
or a term of a `Type 0` type (no Prop binder, no binder above `Type 0`), and the result is `Type` or a term of a `Type 0` type.
Raw rows: `$KJOB_REPORT_PATH.stopkey.<tag>` (mode, name, kind, ls, closed, roots), `.stoppedrows.<tag>` (name, ls, roots, dyn verdict), `.stoproots.<tag>` (root, module, per-mode counts), `.stopreach.<tag>` (mode, root, name, ls: residue keys per root).
No theorem, no sorry. -/
open Lean Meta Elab Command
open Tests.Gen5.PrimResidueKey

namespace Tests.Gen5.PrimResidueStop

def inStop (stopNs : Name) (env : Environment) (n : Name) : Bool :=
  stopNs.isPrefixOf n && (match env.find? n with | some (.defnInfo _) => true | _ => false)

/-- like `PrimResidueKey.reach`, but a node accepted by `inStop` is recorded and not entered; also returns the stopped keys -/
def reachS (env : Environment) (root : Name) (fuel0 : Nat) (stopNs : Option Name) :
    Std.HashMap (Name × String) Bool × Array (Name × List Level) × Std.HashMap (Name × String) (List Level) := Id.run do
  let closedL (ls : List Level) := ls.all (fun l => !l.hasParam && !l.hasMVar)
  let r0 := LS env root
  let mut seen : Std.HashMap (Name × String) Bool := ({} : Std.HashMap (Name × String) Bool).insert (root, lvlKey r0) (closedL r0)
  let mut stopped : Std.HashMap (Name × String) (List Level) := {}
  let mut todo : Array (Name × List Level) := #[(root, r0)]
  let mut fuel := fuel0
  while fuel > 0 && todo.size > 0 do
    fuel := fuel - 1
    let (n, ls) := todo.back!
    todo := todo.pop
    if let some ns := stopNs then
      if inStop ns env n then
        stopped := stopped.insert (n, lvlKey ls) ls
        continue
    match env.find? n with
    | some (.defnInfo d) =>
      let body := d.value.instantiateLevelParams d.levelParams ls
      for (c, cl) in occs env body #[] do
        let k := (c, lvlKey cl)
        if !seen.contains k then
          seen := seen.insert k (closedL cl)
          todo := todo.push (c, cl)
    | _ => pure ()
  return (seen, todo, stopped)

/-- `Dyn` (Type 0) fit of the declared type of `c` at `ls`: `none` if it fits, else the reason -/
def dynFit (c : Name) (ls : List Level) : MetaM (Option String) := do
  let env ← getEnv
  let some ci := env.find? c | return some "no declaration"
  if ls.any (fun l => l.hasParam || l.hasMVar) then return some "levels not closed"
  if ls.length != ci.levelParams.length then return some "level arity"
  let ty := ci.type.instantiateLevelParams ci.levelParams ls
  let sortOf (t : Expr) : MetaM (Option Level) := do
    match (← whnf (← inferType t)) with
    | .sort l => pure (some l.normalize)
    | _ => pure none
  forallTelescope ty fun xs r => do
    for x in xs do
      let t ← inferType x
      match ← sortOf t with
      | some l =>
        if l == Level.zero then return some s!"proof binder ({t})"
        else if l != Level.one then return some s!"binder above Type 0 ({t} : Sort {l})"
      | none =>
        match (← whnf t) with
        | .sort l => if l.normalize != Level.one then return some s!"universe-valued binder Sort {l.normalize}" 
        | _ => return some s!"binder type has no sort ({t})"
    match (← whnf r) with
    | .sort l => if l.normalize != Level.one then return some s!"result is Sort {l.normalize}" else return none
    | _ =>
      match ← sortOf r with
      | some l => if l == Level.one then return none else return some s!"result type above Type 0 or Prop ({r} : Sort {l})"
      | none => return some "result has no sort"

def fuelCheck (env : Environment) (roots : Array Name) (fuel : Nat) (stopNs : Option Name) : CommandElabM Unit := do
  let mut bad : Array String := #[]
  for r in roots do
    let (_, todo, _) := reachS env r fuel stopNs
    if todo.size > 0 then bad := bad.push s!"{r}: {todo.size} todo left"
  if bad.size > 0 then
    throwError "fuel={fuel} exhausted (stop={stopNs}): {bad.size} of {roots.size} roots incomplete:\n{"\n".intercalate bad.toList}"

def stopNs : Name := `Sparkle.Core.Signal

def measure (tag : String) (fuel : Nat) (rootList : Array (Name × String)) : CommandElabM Unit := do
  let env ← getEnv
  let roots := rootList.map (·.1)
  fuelCheck env roots fuel none
  fuelCheck env roots fuel (some stopNs)
  let mut keyRows := ""
  let mut stoppedRows := ""
  let mut rootRows := ""
  let mut reachRows := ""
  let mut stoppedAgg : Std.HashMap (Name × String) (Nat × List Level) := {}
  for (mode, sn) in [("nostop", (none : Option Name)), ("stop", some stopNs)] do
    let mut keys : Std.HashMap (Name × String) Nat := {}
    for (r, m) in rootList do
      let (seen, _, stopped) := reachS env r fuel sn
      let mut cnt := 0
      for ((n, k), closed) in seen.toList do
        if kindOf env n != "none" then
          cnt := cnt + 1
          keys := keys.insert (n, k) (keys.getD (n, k) 0 + 1)
          reachRows := reachRows ++ s!"{mode}\t{r}\t{n}\t{kindOf env n}\t{k}\t{closed}\n"
      rootRows := rootRows ++ s!"{mode}\t{r}\t{m}\t{cnt}\t{stopped.size}\n"
      if mode == "stop" then
        for ((n, k), ls) in stopped.toList do
          stoppedAgg := stoppedAgg.insert (n, k) ((stoppedAgg.getD (n, k) (0, ls)).1 + 1, ls)
    for ((n, k), c) in keys.toList do keyRows := keyRows ++ s!"{mode}\t{n}\t{kindOf env n}\t{k}\t{c}\n"
  for ((n, k), (c, ls)) in stoppedAgg.toList do
    let v ← liftTermElabM (dynFit n ls)
    stoppedRows := stoppedRows ++ s!"{n}\t{k}\t{c}\t{match v with | none => "fits" | some w => "NO: " ++ w}\n"
  logInfo m!"[{tag}] {roots.size} roots, fuel {fuel}, all worklists empty in both modes; stopped distinct (name, ls): {stoppedAgg.size}"
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    IO.FS.writeFile (path ++ ".stopkey." ++ tag) keyRows
    IO.FS.writeFile (path ++ ".stoppedrows." ++ tag) stoppedRows
    IO.FS.writeFile (path ++ ".stoproots." ++ tag) rootRows
    IO.FS.writeFile (path ++ ".stopreach." ++ tag) reachRows

/-- corpus roots (same as `#prim_residue_key`) -/
elab "#prim_residue_stop " tag:str fuel:num : command => do
  let env ← getEnv
  let roots := (machineRoots env).map fun (r, _) => (r, toString (rootModule env r))
  measure tag.getString fuel.getNat roots

/-- explicit roots (the three `Tests.SignalLoopTest` roots are not corpus roots) -/
elab "#prim_residue_stop_named " tag:str fuel:num roots:ident* : command => do
  let env ← getEnv
  let rs := roots.map fun i => (i.getId, "named")
  for (r, _) in rs do unless (env.find? r).any (·.isDefinition) do throwError "{r} is not a definition"
  measure tag.getString fuel.getNat rs

/-- negative control: with a too small fuel the check must fail in the stop mode too -/
elab "#prim_residue_stop_neg " fuel:num : command => do
  let env ← getEnv
  let roots := (machineRoots env).map (·.1)
  let failed ← try fuelCheck env roots fuel.getNat (some stopNs); pure none
    catch e => pure (some (← e.toMessageData.toString))
  match failed with
  | some m => logInfo s!"negative control ok: fuel={fuel.getNat} fails as required; first lines:\n{"\n".intercalate (m.splitOn "\n" |>.take 3)}"
  | none => throwError "negative control FAILED: fuel={fuel.getNat} did not exhaust"

end Tests.Gen5.PrimResidueStop
