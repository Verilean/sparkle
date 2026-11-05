import Lean
import Sparkle
import Tests.Gen2.QuantEndpoint
import Tests.Compiler.KaryGenTest
import Tests.Compiler.ApplicativeSemanticsTest
import Tests.Compiler.ShippingMachineInstTest
import Tests.Compiler.ShippingSignOpsTest
import Tests.Compiler.ShippingMachineNormTest
import Tests.Compiler.ShippingCallsCloseTest
import Tests.Compiler.NoPortsMemSeqGenNew2Test
import Tests.Compiler.MemNameCollisionDesignTest
import Tests.Compiler.SeqDeepGenKeyTest
import Tests.Compiler.MemNameCollisionGateDesignTest
import Tests.Compiler.KaryThreeTest
import Tests.Compiler.ShippingMachineLoopTest
import Tests.Compiler.ShippingMachineSeqLinkedTest
import Tests.Compiler.ShippingPremiseEvalTest
import Tests.Compiler.MemNameCollisionGateTypedAllTest
import Tests.Compiler.ShippingMachineRawTest
import Tests.Compiler.ShippingMachineCombTest
import Tests.Compiler.LeafDeadInitTest
import Tests.Compiler.DepthSwitchSpongeTest
import Tests.Compiler.ShippingMachineLinkedTest
import Tests.Compiler.OneOutWKeccakFTest
import Tests.Compiler.MemNameCollisionGenTest
import Tests.Compiler.NoPortsMemKidTest
import Tests.Compiler.ShippingMachineClosesTest
import Tests.Compiler.NonzeroInitParentTest
import Tests.Compiler.ShippingMachineMemLinkedTest
import Tests.Compiler.ShippingChildBoundaryTest
import Tests.Compiler.DepthRegsChildTest
import Tests.Compiler.SharedLeafMemKidTest
import Tests.Compiler.ShippingMachineCommandTest
import Tests.Compiler.ShippingMachineSeqTest
import Tests.Compiler.SharedLeafGenTest
import Tests.Compiler.ShippingMachineNestTest
import Tests.Compiler.SeqDeepGenInstTest
import Tests.Compiler.SharedLeafGenNoOldChainTest
import Tests.Compiler.ShippingDesignSVTest
import Tests.Compiler.SharedLeafGenDefaultHbTest
import Tests.Compiler.OneOutInnerPickTest
import Tests.Compiler.SeqDeepGenArgsTest
import Tests.Compiler.ShippingDesignSVMemTest
import Tests.Compiler.NoPortsMemSeqGenNewTest
import Tests.Compiler.SharedLeafGenFallbackTest
import Tests.Compiler.ShippingMachineSeqLoopTest
import Tests.Compiler.ShippingMachineDepthHTest
import Tests.Compiler.ShippingMachineTeleTest
import Tests.Compiler.SeqDeepGenDiffTest
import Tools.ShippingGen5ConstValueELS
/-! # Residue count under the level-indexed key `Name × List Level` (issue sparkle-ledger-dd4-key)
Measurement only. Corpus: every module that runs `#machine_endpoint` (47 modules imported above), every `X` with `X.machine_source`.
Traversal from `(X, LS env X)` as in `LSCorpus`: unfold `defnInfo` at the instantiated levels, record each reached `(c, ls)` (levels `normalize`d);
proof terms (theorem-headed applications) are not entered. RESIDUE = reached constants that are not `defnInfo`/`thmInfo`
(constructor, recursor, quot, inductive type former, axiom, opaque). Rows under three keys: Name-only (`PrimTable`, one row per name),
level-indexed (`PrimTableK`, one row per `(name, ls)`), level-polymorphic (one row per name, `ls` an argument). Aggregates by `logInfo`;
raw rows to `$KJOB_REPORT_PATH.key` if set. No theorem, no sorry. -/
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

/-- reached `(c, key)` pairs from `(root, LS env root)`, together with whether the levels are closed -/
def reach (env : Environment) (root : Name) : Std.HashMap (Name × String) Bool := Id.run do
  let mut seen : Std.HashMap (Name × String) Bool := {}
  let mut todo : Array (Name × List Level) := #[(root, LS env root)]
  let mut fuel := 400000
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
  return seen

elab "#prim_residue_key" : command => do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isMachineSource n then
      let x := n.getPrefix
      if (env.find? x).any (·.isDefinition) then roots := roots.push x
  roots := roots.qsort (fun a b => a.toString < b.toString)
  let mut keys : Std.HashMap (Name × String) (Bool × Nat) := {}   -- residue key -> (closed, roots reaching)
  let mut names : Std.HashMap Name (Std.HashSet String) := {}
  let mut perRootMax := 0
  let mut perRootNameMax := 0
  let mut rootPoly := 0
  for r in roots do
    if (env.find? r).any (fun ci => !ci.levelParams.isEmpty) then rootPoly := rootPoly + 1
    let seen := reach env r
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
  let mut msg := s!"CORPUS: {roots.size} roots with `X.machine_source` (47 modules); roots whose own decl has levelParams: {rootPoly}\n"
  msg := msg ++ s!"residue rows, Name-only key (PrimTable): {names.size}\n"
  msg := msg ++ s!"residue rows, level-indexed key (PrimTableK, Name x List Level): {keys.size}\n"
  msg := msg ++ s!"residue rows, level-polymorphic (one per name, ls an argument): {names.size} (same count as Name-only)\n"
  for k in kinds do
    let nk := (names.toList.filter (fun (n, _) => kindOf env n == k)).length
    let kk := (keys.toList.filter (fun ((n, _), _) => kindOf env n == k)).length
    msg := msg ++ s!"  {k}: names {nk}, (name, ls) keys {kk}\n"
  let multi := names.toList.filter (fun (_, s) => s.size > 1)
  msg := msg ++ s!"names with >1 distinct ls (the Name-only collision): {multi.length} of {names.size}\n"
  let maxVar := names.toList.foldl (fun m (_, s) => max m s.size) 0
  msg := msg ++ s!"max ls-variants for one name: {maxVar}; extra rows over Name-only: {keys.size - names.size}\n"
  let nonClosed := (keys.toList.filter (fun (_, (c, _)) => !c)).length
  msg := msg ++ s!"keys whose ls is not closed (param/mvar after instantiation): {nonClosed}\n"
  msg := msg ++ s!"max residue keys per root: {perRootMax}; max residue names per root: {perRootNameMax}\n"
  let top := multi.toArray.qsort (fun a b => a.2.size > b.2.size || (a.2.size == b.2.size && a.1.toString < b.1.toString))
  msg := msg ++ "top names by ls-variants (name [kind] variants):\n"
  for (n, s) in top.toList.take 15 do msg := msg ++ s!"  {n} [{kindOf env n}] {s.size}\n"
  logInfo msg
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    let mut raw := ""
    for ((n, k), (c, m)) in keys.toList do raw := raw ++ s!"{n}\t{kindOf env n}\t{k}\tclosed={c}\troots={m}\n"
    IO.FS.writeFile (path ++ ".key") raw

#prim_residue_key

end Tests.Gen5.PrimResidueKey
