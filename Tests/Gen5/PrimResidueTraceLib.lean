import Lean
import Sparkle
import Tools.ShippingGen5ConstValueELS
import Tests.Gen5.PrimResidueKeyLib
import Tests.Gen5.PrimResidueStopLib
/-! # Where do the recursors come from? (issue sparkle-ledger-dd4-final, Q-A continued (i)): shared measurement
Measurement only. Same traversal, roots and residue as `PrimResidueKey` / `PrimResidueStop` (both unchanged, reused), with
* TRACE mode: the traversal is breadth first and records for every reached `(c, ls)` the node it was FIRST reached from, so every reached
  recursor has a chain `root > ... > parent > recursor` (shortest in the call graph) and a direct parent definition;
* STAGES: nested stop sets, measured in one pass per root (a reached definition of the stop set is recorded as stopped and not unfolded):
  0 none; 1 `Sparkle.Core.Signal` defns; 2 +BitVec defns (prefix `BitVec` or name mentioning `BitVec`); 3 +`Decidable.*` / `Nat.*` defns;
  4 +every defn whose name mentions `Decidable` / `decEq` / `decLe` / `decLt` / `decide` (instDecidableEq family);
  5 +every other defn that comes from a module of `Init` / `Std` / `Lean`. (Stage 5 is the widest: only definitions of Sparkle itself are unfolded.)
Per stage: the residue keys (kind, `Dyn` verdict of the declared type), the stopped keys (with the §Stop 4 `Dyn` (Type 0) verdict), and for each reached recursor the chain and parent.
Fuel exhausted in any stage => `throwError` (no partial result). No axiom, no sorry, no theorem.
Raw rows: `$KJOB_REPORT_PATH.trkeys.<tag>` (stage, name, kind, ls, roots, dyn), `.trstopped.<tag>` (stage, name, ls, roots, dyn),
`.trrec.<tag>` (stage, root, recursor key, parent key, chain), `.trroots.<tag>` (stage, root, module, residue count, stopped count). -/
open Lean Meta Elab Command
open Tests.Gen5.PrimResidueKey
open Tests.Gen5.PrimResidueStop (dynFit)
open Tools.ShippingGen5ConstValueE (LS)

namespace Tests.Gen5.PrimResidueTrace

def stageCount : Nat := 6

def mentions (n : Name) (pats : List String) : Bool :=
  let s := toString n
  pats.any fun p => (s.splitOn p).length > 1

def fromCoreLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean
  | none => false

/-- is the definition `n` (a `defnInfo`) in the stop set of `stage`? -/
def stopAt (env : Environment) (stage : Nat) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo _) =>
    (stage ≥ 1 && Name.isPrefixOf `Sparkle.Core.Signal n)
    || (stage ≥ 2 && (Name.isPrefixOf `BitVec n || mentions n ["BitVec"]))
    || (stage ≥ 3 && (Name.isPrefixOf `Decidable n || Name.isPrefixOf `Nat n))
    || (stage ≥ 4 && mentions n ["Decidable", "decEq", "decLe", "decLt", "decide"])
    || (stage ≥ 5 && fromCoreLib env n)
  | _ => false

structure Node where
  name : Name
  ls : List Level
  parent : Option Nat  -- index into the node array

/-- breadth first from `(root, LS root)`; returns all nodes (in discovery order, with first parent), stopped flags, leftover worklist size -/
def traceReach (env : Environment) (root : Name) (fuel0 : Nat) (stage : Nat) : Array Node × Array Bool × Nat := Id.run do
  let r0 := LS env root
  let mut nodes : Array Node := #[⟨root, r0, none⟩]
  let mut stopped : Array Bool := #[false]
  let mut seen : Std.HashSet (Name × String) := ({} : Std.HashSet (Name × String)).insert (root, lvlKey r0)
  let mut head := 0
  let mut fuel := fuel0
  while fuel > 0 && head < nodes.size do
    fuel := fuel - 1
    let i := head
    head := head + 1
    let nd := nodes[i]!
    if stage > 0 && stopAt env stage nd.name then
      stopped := stopped.set! i true
      continue
    match env.find? nd.name with
    | some (.defnInfo d) =>
      let body := d.value.instantiateLevelParams d.levelParams nd.ls
      for (c, cl) in occs env body #[] do
        let k := (c, lvlKey cl)
        if !seen.contains k then
          seen := seen.insert k
          nodes := nodes.push ⟨c, cl, some i⟩
          stopped := stopped.push false
    | _ => pure ()
  return (nodes, stopped, nodes.size - head)

def keyStr (n : Name) (ls : List Level) : String := s!"{n}{lvlKey ls}"

def chainOf (nodes : Array Node) (i : Nat) : String := Id.run do
  let mut out : List String := []
  let mut cur : Option Nat := some i
  let mut guard := nodes.size + 1
  while guard > 0 do
    guard := guard - 1
    match cur with
    | some j => out := keyStr nodes[j]!.name nodes[j]!.ls :: out; cur := nodes[j]!.parent
    | none => break
  return " > ".intercalate out

def fuelCheckT (env : Environment) (roots : Array Name) (fuel : Nat) : CommandElabM Unit := do
  let mut bad : Array String := #[]
  for st in List.range stageCount do
    for r in roots do
      let (_, _, left) := traceReach env r fuel st
      if left > 0 then bad := bad.push s!"stage {st} {r}: {left} todo left"
  if bad.size > 0 then
    throwError "fuel={fuel} exhausted: {bad.size} (stage, root) pairs incomplete:\n{"\n".intercalate (bad.toList.take 20)}"

def measureT (tag : String) (fuel : Nat) (rootList : Array (Name × String)) : CommandElabM Unit := do
  let env ← getEnv
  fuelCheckT env (rootList.map (·.1)) fuel
  let mut keyRows := ""
  let mut stoppedRows := ""
  let mut rootRows := ""
  let mut recRows := ""
  let mut dynCache : Std.HashMap (Name × String) String := {}
  for st in List.range stageCount do
    let mut keys : Std.HashMap (Name × String) (Nat × List Level) := {}
    let mut stoppedAgg : Std.HashMap (Name × String) (Nat × List Level) := {}
    for (r, m) in rootList do
      let (nodes, stopped, _) := traceReach env r fuel st
      let mut cnt := 0
      let mut scnt := 0
      for i in [0:nodes.size] do
        let nd := nodes[i]!
        let k := (nd.name, lvlKey nd.ls)
        if stopped[i]! then
          scnt := scnt + 1
          stoppedAgg := stoppedAgg.insert k ((stoppedAgg.getD k (0, nd.ls)).1 + 1, nd.ls)
        if kindOf env nd.name != "none" then
          cnt := cnt + 1
          keys := keys.insert k ((keys.getD k (0, nd.ls)).1 + 1, nd.ls)
          if kindOf env nd.name == "rec" then
            let par := match nd.parent with | some p => keyStr nodes[p]!.name nodes[p]!.ls | none => "-"
            recRows := recRows ++ s!"{st}\t{r}\t{keyStr nd.name nd.ls}\t{par}\t{chainOf nodes i}\n"
      rootRows := rootRows ++ s!"{st}\t{r}\t{m}\t{cnt}\t{scnt}\n"
    for ((n, k), (c, ls)) in keys.toList do
      let v ← match dynCache[(n, k)]? with
        | some v => pure v
        | none => do
          let v := match ← liftTermElabM (dynFit n ls) with | none => "fits" | some w => "NO: " ++ w
          dynCache := dynCache.insert (n, k) v
          pure v
      keyRows := keyRows ++ s!"{st}\t{n}\t{kindOf env n}\t{k}\t{c}\t{v}\n"
    for ((n, k), (c, ls)) in stoppedAgg.toList do
      let v ← match dynCache[(n, k)]? with
        | some v => pure v
        | none => do
          let v := match ← liftTermElabM (dynFit n ls) with | none => "fits" | some w => "NO: " ++ w
          dynCache := dynCache.insert (n, k) v
          pure v
      stoppedRows := stoppedRows ++ s!"{st}\t{n}\t{k}\t{c}\t{v}\n"
  logInfo m!"[{tag}] {rootList.size} roots, fuel {fuel}, {stageCount} stages, all worklists empty"
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    IO.FS.writeFile (path ++ ".trkeys." ++ tag) keyRows
    IO.FS.writeFile (path ++ ".trstopped." ++ tag) stoppedRows
    IO.FS.writeFile (path ++ ".trroots." ++ tag) rootRows
    IO.FS.writeFile (path ++ ".trrec." ++ tag) recRows

/-- corpus roots (same as `#prim_residue_key`) -/
elab "#prim_residue_trace " tag:str fuel:num : command => do
  let env ← getEnv
  measureT tag.getString fuel.getNat ((machineRoots env).map fun (r, _) => (r, toString (rootModule env r)))

/-- explicit roots (the three `Tests.SignalLoopTest` roots) -/
elab "#prim_residue_trace_named " tag:str fuel:num roots:ident* : command => do
  let env ← getEnv
  let rs := roots.map fun i => (i.getId, "named")
  for (r, _) in rs do unless (env.find? r).any (·.isDefinition) do throwError "{r} is not a definition"
  measureT tag.getString fuel.getNat rs

/-- negative control: a too small fuel must make the check fail -/
elab "#prim_residue_trace_neg " fuel:num : command => do
  let env ← getEnv
  let roots := (machineRoots env).map (·.1)
  let failed ← try fuelCheckT env roots fuel.getNat; pure none
    catch e => pure (some (← e.toMessageData.toString))
  match failed with
  | some m => logInfo s!"negative control ok: fuel={fuel.getNat} fails as required; first lines:\n{"\n".intercalate (m.splitOn "\n" |>.take 3)}"
  | none => throwError "negative control FAILED: fuel={fuel.getNat} did not exhaust"

/-- control for the stages and the chain: `Nat.rec` is reached through a short constructed path; stage sets are nested and recognise their members -/
elab "#prim_residue_trace_ctl" : command => do
  let env ← getEnv
  let chk (stage : Nat) (n : Name) (want : Bool) : CommandElabM Unit := do
    if stopAt env stage n != want then throwError "stage control failed: stage {stage} {n} expected {want}"
  chk 0 ``Nat.add false
  chk 1 `Sparkle.Core.Signal.register true
  chk 1 ``Nat.add false
  chk 2 ``BitVec.add true
  chk 3 ``Nat.add true
  chk 3 ``Nat.rec false
  chk 4 ``instDecidableEqNat true
  chk 4 ``List.map false
  chk 5 ``List.map true
  chk 5 `Sparkle.Core.Signal.register true
  -- chain control: `Nat.add` unfolds to `Nat.rec` at stage 0; the recursor's direct parent is a definition in Init
  let (nodes, _, left) := traceReach env ``Nat.add 1000 0
  if left != 0 then throwError "ctl: worklist left"
  match nodes.findIdx? (fun nd => nd.name == ``Nat.rec) with
  | some i =>
    logInfo m!"trace control ok: {chainOf nodes i}"
  | none => throwError "trace control failed: Nat.rec not reached from Nat.add"

end Tests.Gen5.PrimResidueTrace
