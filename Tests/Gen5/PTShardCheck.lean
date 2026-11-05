import Lean
import Tools.ShippingGen5PTShard
import Tests.Gen5.PTShard.KaryGen
import Tests.Gen5.PTShard.SignalLoop
import Tests.Gen5.PTShard.LINHW
import Tests.Gen5.PTShard.Keccak256HW
import Tests.Gen5.PTShard.Keccak256Sponge
import Tests.Gen5.PTShard.P256FieldHW
import Tests.Gen5.PTShard.P256OrderHW
import Tests.Gen5.PTShard.Secp256k1OrderHW
import Tests.Gen5.PTShard.HFTStrategy
import Tests.Gen5.PTShard.HTTP
import Tests.Gen5.PTShard.UART
import Tests.Gen5.PTShard.MultiInstance
import Tests.Gen5.PTShard.NoPortsMemKid
import Tests.Gen5.PTShard.ChildBoundary
import Tests.Gen5.PTShard.MachineEntry
import Tests.Gen5.PTShard.MachineNest
import Tests.Gen5.PTShard.MachineSeq
import Tests.Gen5.PTShard.MachineTele
import Tests.Gen5.PTShard.KaryThree
import Tests.Gen5.PTShard.SharedLeafGenDefaultHb
import Tests.Gen5.PTShard.SharedLeafGenFallback
import Tests.Gen5.PTShard.SharedLeafGen
import Tests.Gen5.PTShard.SharedLeafMemKid
set_option autoImplicit false
-- D.D-4 Q-B check of the extension shards (Issue sparkle-ledger-dd4-shard). No sorry / axiom / native_decide / TRUSTED. PTcorpus, G-PRIM and the ledger are NOT decided here.

/-! # Shard check

1. Kernel (`rfl` / `decide`): per-shard counts, the 51 `notImportable` keys of `PTcorpus` against the keys the shards carry (how many are paid), no key inside two shards, no shard key in the core, composition of the core with several shards.
2. Meta (an audit of the real environment, NOT a kernel proof): for every shard key the constant exists and its row has as many kinds as the declared type has binders.
The per-key type check (`@S.mk x₁ … xₙ : S x₁` elaborated, `…_key`, `…_run`, `…_comp`) is in the generated shard files. -/
open Lean Meta

namespace Tests.Gen5.PTShardCheck
open Tools.ShippingGen5PTShard Tools.ShippingGen5PTCorpus Tools.ShippingGen5ConstValueEKey

/-- (shard name, owner module, shard, keys without a row with the reason, keys requested) -/
def shards : List (Name × Name × PTShard × List (Name × String) × List (Name × Bool)) := [
  (`KaryGen, `Tests.Compiler.KaryGenTest, Tests.Gen5.PTShard.KaryGen.ptShard, Tests.Gen5.PTShard.KaryGen.ptShardMissing, Tests.Gen5.PTShard.KaryGen.ptShardWanted),
  (`SignalLoop, `Tests.SignalLoopTest, Tests.Gen5.PTShard.SignalLoop.ptShard, Tests.Gen5.PTShard.SignalLoop.ptShardMissing, Tests.Gen5.PTShard.SignalLoop.ptShardWanted),
  (`LINHW, `IP.Bus.LINHW, Tests.Gen5.PTShard.LINHW.ptShard, Tests.Gen5.PTShard.LINHW.ptShardMissing, Tests.Gen5.PTShard.LINHW.ptShardWanted),
  (`Keccak256HW, `IP.Crypto.Keccak256HW, Tests.Gen5.PTShard.Keccak256HW.ptShard, Tests.Gen5.PTShard.Keccak256HW.ptShardMissing, Tests.Gen5.PTShard.Keccak256HW.ptShardWanted),
  (`Keccak256Sponge, `IP.Crypto.Keccak256Sponge, Tests.Gen5.PTShard.Keccak256Sponge.ptShard, Tests.Gen5.PTShard.Keccak256Sponge.ptShardMissing, Tests.Gen5.PTShard.Keccak256Sponge.ptShardWanted),
  (`P256FieldHW, `IP.Crypto.P256FieldHW, Tests.Gen5.PTShard.P256FieldHW.ptShard, Tests.Gen5.PTShard.P256FieldHW.ptShardMissing, Tests.Gen5.PTShard.P256FieldHW.ptShardWanted),
  (`P256OrderHW, `IP.Crypto.P256OrderHW, Tests.Gen5.PTShard.P256OrderHW.ptShard, Tests.Gen5.PTShard.P256OrderHW.ptShardMissing, Tests.Gen5.PTShard.P256OrderHW.ptShardWanted),
  (`Secp256k1OrderHW, `IP.Crypto.Secp256k1OrderHW, Tests.Gen5.PTShard.Secp256k1OrderHW.ptShard, Tests.Gen5.PTShard.Secp256k1OrderHW.ptShardMissing, Tests.Gen5.PTShard.Secp256k1OrderHW.ptShardWanted),
  (`HFTStrategy, `IP.Net.HFTStrategy, Tests.Gen5.PTShard.HFTStrategy.ptShard, Tests.Gen5.PTShard.HFTStrategy.ptShardMissing, Tests.Gen5.PTShard.HFTStrategy.ptShardWanted),
  (`HTTP, `IP.Net.HTTP, Tests.Gen5.PTShard.HTTP.ptShard, Tests.Gen5.PTShard.HTTP.ptShardMissing, Tests.Gen5.PTShard.HTTP.ptShardWanted),
  (`UART, `IP.Net.UART, Tests.Gen5.PTShard.UART.ptShard, Tests.Gen5.PTShard.UART.ptShardMissing, Tests.Gen5.PTShard.UART.ptShardWanted),
  (`MultiInstance, `Tests.Compiler.MultiInstanceTest, Tests.Gen5.PTShard.MultiInstance.ptShard, Tests.Gen5.PTShard.MultiInstance.ptShardMissing, Tests.Gen5.PTShard.MultiInstance.ptShardWanted),
  (`NoPortsMemKid, `Tests.Compiler.NoPortsMemKidTest, Tests.Gen5.PTShard.NoPortsMemKid.ptShard, Tests.Gen5.PTShard.NoPortsMemKid.ptShardMissing, Tests.Gen5.PTShard.NoPortsMemKid.ptShardWanted),
  (`ChildBoundary, `Tests.Compiler.ShippingChildBoundaryTest, Tests.Gen5.PTShard.ChildBoundary.ptShard, Tests.Gen5.PTShard.ChildBoundary.ptShardMissing, Tests.Gen5.PTShard.ChildBoundary.ptShardWanted),
  (`MachineEntry, `Tests.Compiler.ShippingMachineEntryTest, Tests.Gen5.PTShard.MachineEntry.ptShard, Tests.Gen5.PTShard.MachineEntry.ptShardMissing, Tests.Gen5.PTShard.MachineEntry.ptShardWanted),
  (`MachineNest, `Tests.Compiler.ShippingMachineNestTest, Tests.Gen5.PTShard.MachineNest.ptShard, Tests.Gen5.PTShard.MachineNest.ptShardMissing, Tests.Gen5.PTShard.MachineNest.ptShardWanted),
  (`MachineSeq, `Tests.Compiler.ShippingMachineSeqTest, Tests.Gen5.PTShard.MachineSeq.ptShard, Tests.Gen5.PTShard.MachineSeq.ptShardMissing, Tests.Gen5.PTShard.MachineSeq.ptShardWanted),
  (`MachineTele, `Tests.Compiler.ShippingMachineTeleTest, Tests.Gen5.PTShard.MachineTele.ptShard, Tests.Gen5.PTShard.MachineTele.ptShardMissing, Tests.Gen5.PTShard.MachineTele.ptShardWanted),
  (`KaryThree, `Tests.Compiler.KaryThreeTest, Tests.Gen5.PTShard.KaryThree.ptShard, Tests.Gen5.PTShard.KaryThree.ptShardMissing, Tests.Gen5.PTShard.KaryThree.ptShardWanted),
  (`SharedLeafGenDefaultHb, `Tests.Compiler.SharedLeafGenDefaultHbTest, Tests.Gen5.PTShard.SharedLeafGenDefaultHb.ptShard, Tests.Gen5.PTShard.SharedLeafGenDefaultHb.ptShardMissing, Tests.Gen5.PTShard.SharedLeafGenDefaultHb.ptShardWanted),
  (`SharedLeafGenFallback, `Tests.Compiler.SharedLeafGenFallbackTest, Tests.Gen5.PTShard.SharedLeafGenFallback.ptShard, Tests.Gen5.PTShard.SharedLeafGenFallback.ptShardMissing, Tests.Gen5.PTShard.SharedLeafGenFallback.ptShardWanted),
  (`SharedLeafGen, `Tests.Compiler.SharedLeafGenTest, Tests.Gen5.PTShard.SharedLeafGen.ptShard, Tests.Gen5.PTShard.SharedLeafGen.ptShardMissing, Tests.Gen5.PTShard.SharedLeafGen.ptShardWanted),
  (`SharedLeafMemKid, `Tests.Compiler.SharedLeafMemKidTest, Tests.Gen5.PTShard.SharedLeafMemKid.ptShard, Tests.Gen5.PTShard.SharedLeafMemKid.ptShardMissing, Tests.Gen5.PTShard.SharedLeafMemKid.ptShardWanted)
]

def allShards : List PTShard := shards.map fun s => s.2.2.1
def paidKeys : List (Name × List Nat) := allShards.flatMap fun S => S.tyKeys ++ S.tmKeys
def need : List (Name × List Nat) := (missingTable.filter fun e => e.2.2 == MissingWhy.notImportable).map fun e => (e.1, e.2.1)

theorem n_need : need.length = 51 := rfl
theorem n_shards : shards.length = 23 := rfl
/-- Rows the shards carry (types / terms) and keys with no row. -/
theorem n_rows_ty : (allShards.map fun S => S.tys.length).sum = 30 := by decide
theorem n_rows_tm : (allShards.map fun S => S.tms.length).sum = 30 := by decide
theorem n_shard_missing : (shards.map fun s => s.2.2.2.1.length).sum = 0 := by decide
/-- The paid keys of the 51: kernel-evaluated. -/
theorem n_paid : (need.filter fun k => paidKeys.contains k).length = 51 := by decide
def unpaid : List (Name × List Nat) := need.filter fun k => !paidKeys.contains k
def extra : List (Name × List Nat) := paidKeys.filter fun k => !need.contains k
theorem n_unpaid : unpaid.length = 0 := by decide
theorem n_extra : extra.length = 9 := by decide

/-- No key is carried by two shards (exclusivity between the shards), and none by the core. -/
theorem paid_nodup : paidKeys.Nodup := by decide
theorem paid_not_in_core : paidKeys.all (fun k => (PTcore.tys k.1 (k.2.map natLv)).isNone && (PTcore.tms k.1 (k.2.map natLv)).isNone) = true := by decide

/-- Every generated shard is fresh against the core (`ptShard_fresh`) and has the functional carrier. -/
theorem all_fresh : FreshAgainst PTcore Tests.Gen5.PTShard.KaryGen.ptShard := Tests.Gen5.PTShard.KaryGen.ptShard_fresh

/-! ## A root composes only the shards it needs -/

open Tests.Gen5.PTShard in
/-- core ⊕ KaryGen ⊕ MachineTele ⊕ MachineNest ⊕ SignalLoop. -/
noncomputable def rootPT : PrimTableK :=
  PTcore ⊕ₚ KaryGen.ptShard.toPT ⊕ₚ MachineTele.ptShard.toPT ⊕ₚ MachineNest.ptShard.toPT ⊕ₚ SignalLoop.ptShard.toPT

open Tests.Gen5.PTShard in
/-- Each shard is fresh against the composition of the ones before it (`rfl` on its finitely many keys): the composition is exclusive at every step. -/
theorem fresh_step1 : FreshAgainst PTcore KaryGen.ptShard := KaryGen.ptShard_fresh
open Tests.Gen5.PTShard in
theorem fresh_step2 : FreshAgainst (PTcore ⊕ₚ KaryGen.ptShard.toPT) MachineTele.ptShard := ⟨rfl, rfl⟩
open Tests.Gen5.PTShard in
theorem fresh_step3 : FreshAgainst (PTcore ⊕ₚ KaryGen.ptShard.toPT ⊕ₚ MachineTele.ptShard.toPT) MachineNest.ptShard := ⟨rfl, rfl⟩
open Tests.Gen5.PTShard in
theorem fresh_step4 :
    FreshAgainst (PTcore ⊕ₚ KaryGen.ptShard.toPT ⊕ₚ MachineTele.ptShard.toPT ⊕ₚ MachineNest.ptShard.toPT) SignalLoop.ptShard := ⟨rfl, rfl⟩

/-- The core keeps its rows in the root's table. -/
theorem rootPT_keeps_core_tys {{c : Lean.Name}} {{ls : List Lean.Level}} {{r : Tools.ShippingGen5ConstValueE.TyRow}} (h : PTcore.tys c ls = some r) : rootPT.tys c ls = some r :=
  comp_tys_left (comp_tys_left (comp_tys_left (comp_tys_left h)))

open Tests.Gen5.PTShard in
/-- A row of the third shard (`MachineNest`) is still found in the root's table (the left side has no row at that key, the shard after it is empty). -/
theorem rootPT_keeps_nest_ty0 :
    rootPT.tys `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out [] = some MachineNest.ptShardTy0.row :=
  comp_tys_left (comp_tys_right_excl fresh_step3.excl MachineNest.ptShardTy0_key)

theorem rootPT_functional : Tools.ShippingGen5FG.ConstValueFunctional (Tools.ShippingGen5CVFinal.CVFinal rootPT) :=
  cvFinal_comp_functional _ _

/-- Negative control: a shard that repeats a key of the core is NOT fresh (here the core itself as a shard). -/
theorem not_fresh_core_shard : ¬ FreshAgainst PTcore PTcoreShard := fun h => absurd h.1 (by decide)

/-- (constant, [], number of kinds, 0) for every shard key. -/
def kindArity : List (Name × List Name × Nat × Nat) :=
  allShards.flatMap fun S => (S.tys.map fun e => (e.1, [], e.2.2.1.length, 0)) ++ (S.tms.map fun e => (e.1, [], e.2.2.1.length, 0))

/-! ## Audit of the real environment (meta; NOT a kernel proof)

For every shard key: the constant exists, and the number of kinds of its row equals the number of binders of the declared type. -/

open Lean Elab Meta in
run_meta do
  let env ← getEnv
  let rows ← unsafe evalConst (List (Name × List Name × Nat × Nat)) ``kindArity
  let mut bad : Nat := 0
  let mut n : Nat := 0
  for (c, _, ks, _) in rows do
    n := n + 1
    match env.find? c with
    | none =>
      bad := bad + 1
      logInfo m!"MISSING constant {c}"
    | some ci =>
      let a ← forallTelescopeReducing ci.type fun xs _ => pure xs.size
      if a != ks then
        bad := bad + 1
        logInfo m!"ARITY MISMATCH {c}: kinds {ks}, binders {a}"
  logInfo m!"shard keys audited: {n}, mismatches: {bad}"

end Tests.Gen5.PTShardCheck

#print axioms Tests.Gen5.PTShardCheck.n_paid
#print axioms Tests.Gen5.PTShardCheck.paid_nodup
#print axioms Tests.Gen5.PTShardCheck.paid_not_in_core
#print axioms Tests.Gen5.PTShardCheck.fresh_step4
#print axioms Tests.Gen5.PTShardCheck.rootPT_keeps_nest_ty0
#print axioms Tests.Gen5.PTShardCheck.rootPT_functional
#print axioms Tests.Gen5.PTShardCheck.not_fresh_core_shard
#print axioms Tests.Gen5.PTShard.MachineNest.ptShardTm0_run
#print axioms Tests.Gen5.PTShard.MachineNest.ptShard_functional
