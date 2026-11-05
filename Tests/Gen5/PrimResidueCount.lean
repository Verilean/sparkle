import Lean
import Sparkle
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
/-! # Residue count for the `ConstValueE` primitive table (option B), a SAMPLE
Measurement only (D.D-4, issue sparkle-ledger-dd4). For each declaration `X` of the imported corpus modules with `X.machine_source`
(the compiler succeeded), unfold every `defnInfo` transitively and count the distinct constants that remain, by kind.
Proof terms are skipped (an application headed by a theorem is not entered). Output: `logInfo` aggregates; the raw rows go to `$KJOB_REPORT_PATH.prim` if set.
No theorem, no sorry. -/
open Lean Meta Elab Command

namespace Tests.Gen5.PrimResidueCount

inductive Kind | ctor | recur | quot | opaqueExt | opaquePlain | typeFormer | axiom | defnExt | other
  deriving BEq, Repr, Hashable

def Kind.label : Kind → String
  | .ctor => "constructor" | .recur => "recursor" | .quot => "quot" | .opaqueExt => "opaque/extern/implemented_by"
  | .opaquePlain => "opaque(plain)" | .typeFormer => "type-former(inductive)" | .axiom => "axiom"
  | .defnExt => "defn-with-extern/implemented_by(unfolded)" | .other => "other"

def hasImpl (env : Environment) (n : Name) : Bool :=
  (Compiler.getImplementedBy? env n).isSome || (isExtern env n)

/-- Headed-by-theorem applications are proofs: do not enter them. -/
partial def consts (env : Environment) (e : Expr) (acc : NameSet) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app .. =>
    let f := e.getAppFn
    match f with
    | .const n _ =>
      if (env.find? n).any (·.isTheorem) then acc
      else e.getAppArgs.foldl (fun a x => consts env x a) (acc.insert n)
    | _ => e.getAppArgs.foldl (fun a x => consts env x a) (consts env f acc)
  | .lam _ t b _ | .forallE _ t b _ => consts env b (consts env t acc)
  | .letE _ t v b _ => consts env b (consts env v (consts env t acc))
  | .mdata _ b | .proj _ _ b => consts env b acc
  | _ => acc

structure Clo where
  residue : NameMap Kind := {}
  unfolded : Nat := 0
  extUnfolded : NameSet := {}
  thms : Nat := 0

def closureOf (env : Environment) (root : Name) : Clo := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut c : Clo := { residue := {} }
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      match ci with
      | .defnInfo d =>
        c := { c with unfolded := c.unfolded + 1 }
        if hasImpl env n then c := { c with extUnfolded := c.extUnfolded.insert n }
        todo := (consts env d.value {}).toList.foldl (fun a x => a.push x) todo
      | .thmInfo _ => c := { c with thms := c.thms + 1 }
      | .ctorInfo _ => c := { c with residue := c.residue.insert n .ctor }
      | .recInfo _ => c := { c with residue := c.residue.insert n .recur }
      | .quotInfo _ => c := { c with residue := c.residue.insert n .quot }
      | .inductInfo _ => c := { c with residue := c.residue.insert n .typeFormer }
      | .axiomInfo _ => c := { c with residue := c.residue.insert n .axiom }
      | .opaqueInfo _ =>
        c := { c with residue := c.residue.insert n (if hasImpl env n then .opaqueExt else .opaquePlain) }
  return c

def hit (s : String) (n : Name) : Bool := (n.toString).startsWith s

def isMachineSource (n : Name) : Bool :=
  match n with
  | .str _ "machine_source" => true
  | _ => false

def interesting : List String :=
  ["Sparkle.Core.Signal.Signal", "Sparkle.Core.Signal.Signal.register", "Sparkle.Core.Signal.Signal.loop", "Sparkle.Core.Signal.Signal.loopGo",
   "Sparkle.Core.Signal.Signal.registerWithEnable", "Sparkle.Core.Signal.Signal.mux", "Sparkle.Core.Signal.Signal.memory",
   "BitVec.add", "BitVec.and", "BitVec.ult", "BitVec.ofNat", "BitVec.extractLsb'", "BitVec.append", "BitVec.toNat", "Bool.and", "Prod.mk", "ite", "Nat.add", "HAdd.hAdd", "Nat.mod", "Nat.rec", "WellFounded.fix"]

elab "#prim_residue_count" : command => do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isMachineSource n then
      let x := n.getPrefix
      if (env.find? x).any (·.isDefinition) then roots := roots.push x
  let mut perRoot : Array (Name × Clo) := #[]
  for r in roots do
    perRoot := perRoot.push (r, closureOf env r)
  -- aggregate: distinct residue constants, with number of roots reaching each
  let mut agg : NameMap (Kind × Nat) := {}
  let mut ext : NameMap Nat := {}
  for (_, c) in perRoot do
    for (n, k) in c.residue.toList do
      agg := agg.insert n (k, ((agg.get? n).map (·.2)).getD 0 + 1)
    for n in c.extUnfolded.toList do
      ext := ext.insert n (ext.getD n 0 + 1)
  let rows := agg.toList.toArray.qsort (fun a b => a.2.2 > b.2.2 || (a.2.2 == b.2.2 && a.1.toString < b.1.toString))
  let kinds := [Kind.ctor, .recur, .quot, .opaqueExt, .opaquePlain, .typeFormer, .axiom]
  let mut msg := s!"SAMPLE: {roots.size} declarations with `X.machine_source` in the imported modules\n"
  msg := msg ++ s!"distinct residue constants (union over roots): {rows.size}\n"
  for k in kinds do
    msg := msg ++ s!"  {k.label}: {(rows.filter (·.2.1 == k)).size}\n"
  msg := msg ++ s!"defnInfo carrying extern/implemented_by that were UNFOLDED (distinct): {ext.size}\n"
  let maxPer := perRoot.foldl (fun m (_, c) => max m c.residue.size) 0
  let unfoldedMax := perRoot.foldl (fun m (_, c) => max m c.unfolded) 0
  msg := msg ++ s!"max residue per declaration: {maxPer}; max unfolded defnInfo per declaration: {unfoldedMax}\n"
  msg := msg ++ "top residue (name [kind] roots-reaching):\n"
  for (n, k, c) in rows.toList.take 30 |>.map (fun r => (r.1, r.2.1, r.2.2)) do
    msg := msg ++ s!"  {n} [{k.label}] {c}\n"
  msg := msg ++ "named constants of interest (kind of the constant itself; in residue? reached roots):\n"
  for s in interesting do
    let n := s.toName
    let kind := match env.find? n with
      | some (.defnInfo _) => if hasImpl env n then "defn+extern/implemented_by" else "defn"
      | some (.opaqueInfo _) => "opaque" | some (.ctorInfo _) => "ctor" | some (.recInfo _) => "rec"
      | some (.inductInfo _) => "inductive" | some (.thmInfo _) => "thm" | some (.axiomInfo _) => "axiom"
      | some (.quotInfo _) => "quot" | none => "absent"
    let reachedByUnfold := perRoot.foldl (fun a (_, c) => a + (if c.extUnfolded.contains n then 1 else 0)) 0
    let inRes := (agg.get? n).map (·.2) |>.getD 0
    msg := msg ++ s!"  {s}: {kind}; unfolded-with-impl in {reachedByUnfold} roots; residue in {inRes} roots\n"
  logInfo msg
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    let mut raw := ""
    for (n, k, c) in rows.toList.map (fun r => (r.1, r.2.1, r.2.2)) do
      raw := raw ++ s!"{n}\t{k.label}\t{c}\n"
    IO.FS.writeFile (path ++ ".prim") raw

#prim_residue_count

end Tests.Gen5.PrimResidueCount
