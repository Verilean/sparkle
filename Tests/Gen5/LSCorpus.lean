import Lean
import Sparkle
import Tools.ShippingGen5ConstValueELS
import Tests.Compiler.ShippingMachineSeqTest
import Tests.Compiler.ShippingMachineInstTest
import Tests.Compiler.ShippingMachineSeqLoopTest
import Tests.Compiler.ShippingMachineLoopTest
import Tests.Compiler.ShippingMachineCombTest
import Tests.Compiler.ShippingMachineRawTest
import Tests.Compiler.ShippingMachineTeleTest
import Tests.Compiler.ShippingMachineNestTest
import Tests.Compiler.ShippingMachineFuseTest
import Tests.Compiler.ShippingMachineLinkedTest
import Tests.Compiler.ShippingSignOpsTest
import Tests.Compiler.ShippingMachineMemLinkedTest
import Tests.Compiler.ShippingMachineNormTest
import Tests.Compiler.ShippingMachineClosesTest
import Tests.Compiler.ShippingMachineSeqLinkedTest
import Tests.Compiler.ShippingMachineDepthHTest
/-! # Universe-instance measurement for `LS env X` (issue sparkle-ledger-dd4-ls), a SAMPLE (same 59 roots as PrimResidueCount)
Measurement only. (A) the `ls` of every `const c ls` in the value of each root and of each reached `defnInfo` (raw, before instantiation);
(B) a faithful traversal from `(X, LS env X)`: unfold `defnInfo` at the instantiated levels (`instantiateLevelParams`), record every
`(c, ls)` reached, and report the names reached with more than one distinct `ls` (after `Level.normalize`). Proof terms are skipped
(application headed by a theorem is not entered). Aggregates by `logInfo`; raw rows to `$KJOB_REPORT_PATH.ls` if set. No theorem, no sorry. -/
open Lean Meta Elab Command
open Tools.ShippingGen5ConstValueE (LS)

namespace Tests.Gen5.LSCorpus

def isMachineSource (n : Name) : Bool := match n with | .str _ "machine_source" => true | _ => false

/-- all `(c, ls)` const occurrences, not entering theorem-headed applications -/
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

/-- class of a level list (raw use) -/
def classOf (ls : List Level) : String :=
  if ls.isEmpty then "empty"
  else if ls.all (fun l => l.normalize == Level.zero) then "all-zero"
  else if ls.all (fun l => !l.hasParam && !l.hasMVar) then "closed-nonzero"
  else if ls.all (fun l => match l with | .param _ => true | _ => false) then "params-only"
  else "param-expr"

/-- traversal from `(X, LS env X)`; returns the visited `(c, key)` set and the number of unfolded defs -/
def reach (env : Environment) (root : Name) : Std.HashSet (Name × String) × Nat := Id.run do
  let mut seen : Std.HashSet (Name × String) := {}
  let mut todo : Array (Name × List Level) := #[(root, LS env root)]
  let mut nun := 0
  let mut fuel := 200000
  while fuel > 0 && todo.size > 0 do
    fuel := fuel - 1
    let (n, ls) := todo.back!
    todo := todo.pop
    let k := (n, lvlKey ls)
    if seen.contains k then continue
    seen := seen.insert k
    match env.find? n with
    | some (.defnInfo d) =>
      nun := nun + 1
      let body := d.value.instantiateLevelParams d.levelParams ls
      todo := (occs env body #[]).foldl (fun a x => a.push x) todo
    | _ => pure ()
  return (seen, nun)

elab "#ls_corpus" : command => do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isMachineSource n then
      let x := n.getPrefix
      if (env.find? x).any (·.isDefinition) then roots := roots.push x
  roots := roots.qsort (fun a b => a.toString < b.toString)
  -- (A) raw classes over the unique reached defs
  let mut cls : Std.HashMap String Nat := {}
  let mut rootPoly := 0
  let mut multi : Array (Name × Array String × Array Name) := #[]   -- name, distinct keys, roots
  let mut multiRoots : Std.HashMap Name (Std.HashSet String) := {}
  let mut multiBy : Std.HashMap Name (Std.HashSet Name) := {}
  let mut rootsWithMulti := 0
  let mut rawRows := ""
  let mut totalPairs := 0
  for r in roots do
    if (env.find? r).any (fun ci => !ci.levelParams.isEmpty) then rootPoly := rootPoly + 1
    let (seen, nun) := reach env r
    totalPairs := totalPairs + seen.size
    let mut byName : Std.HashMap Name (Array String) := {}
    for (n, k) in seen.toList do
      byName := byName.insert n ((byName.getD n #[]).push k)
    let mut hasMulti := false
    for (n, ks) in byName.toList do
      if ks.size > 1 then
        hasMulti := true
        multiRoots := multiRoots.insert n ((multiRoots.getD n {}).insertMany ks)
        multiBy := multiBy.insert n ((multiBy.getD n {}).insert r)
    if hasMulti then rootsWithMulti := rootsWithMulti + 1
    rawRows := rawRows ++ s!"root\t{r}\tpairs={seen.size}\tunfolded={nun}\n"
    -- raw classes: occurrences in root body and all reached defs (by name, any instantiation)
    let mut names : Std.HashSet Name := {}
    for (n, _) in seen.toList do names := names.insert n
    for n in names.toList do
      if let some (.defnInfo d) := env.find? n then
        for (c, ls) in occs env d.value #[] do
          let k := classOf ls
          cls := cls.insert k (cls.getD k 0 + 1)
  let mut msg := s!"SAMPLE: {roots.size} roots; roots whose own decl has levelParams: {rootPoly}\n"
  msg := msg ++ s!"(A) raw `const c ls` occurrences in reached defn bodies, by class of ls (counted per root x occurrence):\n"
  for (k, v) in cls.toList.toArray.qsort (fun a b => a.2 > b.2) do msg := msg ++ s!"  {k}: {v}\n"
  msg := msg ++ s!"(B) traversal from (X, LS env X): total distinct (const, ls) pairs over roots: {totalPairs}\n"
  msg := msg ++ s!"  roots reaching some name with >1 distinct instantiated ls: {rootsWithMulti} / {roots.size}\n"
  msg := msg ++ s!"  distinct names reached with >1 distinct ls: {multiRoots.size}\n"
  let rows := multiRoots.toList.toArray.qsort (fun a b => (multiBy.getD a.1 {}).size > (multiBy.getD b.1 {}).size || ((multiBy.getD a.1 {}).size == (multiBy.getD b.1 {}).size && a.1.toString < b.1.toString))
  for (n, ks) in rows.toList.take 25 do
    let ci := env.find? n
    let kind := match ci with | some (.defnInfo _) => "defn" | some (.ctorInfo _) => "ctor" | some (.inductInfo _) => "induct" | some (.recInfo _) => "rec" | _ => "other"
    msg := msg ++ s!"  {n} [{kind}] roots={(multiBy.getD n {}).size} ls-variants={ks.size}: {ks.toList.take 4}\n"
  logInfo msg
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    for (n, ks) in rows.toList do
      rawRows := rawRows ++ s!"multi\t{n}\troots={(multiBy.getD n {}).size}\t{ks.toList}\n"
    IO.FS.writeFile (path ++ ".ls") rawRows

#ls_corpus

end Tests.Gen5.LSCorpus
