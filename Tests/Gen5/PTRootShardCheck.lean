import Lean
import Tools.ShippingGen5PTRootShard
import Tests.Gen5.PTShardCheck
import Tests.Gen5.CVFinalCheck
import Tests.Gen5.PrimResidueKeyLib
set_option autoImplicit false
-- D.D-4 Q-B connection check per root (Issue sparkle-ledger-dd4-shard). No sorry / axiom / native_decide / TRUSTED. PTcorpus, G-PRIM and the ledger are NOT decided here.

/-! # Root check: `PT := PTcore ⊕ (the shards the root needs)`

For representative roots (a root of `Tests.SignalLoopTest`, whose shard is empty, and roots of corpus modules that have shards):

1. Kernel (`rfl` / `decide`, per root): the chain of freshness of the shards in the root's list, the pairwise exclusivity, `Covers` (every key of every needed shard has a row in the root table),
   the negative control `Covers (rootPT (Ss without S)) S = false` (without the shard the keys are missing), the bridges of the statement, the split of the named premises, the standard-axiom check.
2. Meta (an audit of the real environment, NOT a kernel proof):
   * the list of the shards a root needs is DERIVED from the keys of the generated shards: the constants reached from the root through definition bodies (`PrimResidueKey.reach`) that are keys of some shard;
     it must be equal to the list the kernel statement uses (`ssXxx`), and every listed shard has a reached key (minimality).
   * the census of the unfolded statement `FGLedgerPremisesStmtRoot ssXxx`: it is the text of `FGLedgerPremisesStmtPTC` with `PTcorpus` replaced by `rootPT ssXxx` (`==`),
     binder counts, no `PrimTableK` binder, the named premises, and the shard constants that occur in the statement.
   * control: without that replacement the two texts differ. -/
open Lean Meta

namespace Tests.Gen5.PTRootShardCheck
open Tools.ShippingGen5PTShard Tools.ShippingGen5PTRootShard Tools.ShippingGen5PTCorpus
open Tests.Gen5.PTShardCheck (shards paidKeys paid_nodup)
open Tests.Gen5.PTShard

/-! ## The shard lists of the roots (kernel data) -/

/-- `Sparkle.Tests.SignalLoopTest.counterLoop`: reaches no key of any shard (its module shard is empty). -/
def ssLoop : List PTShard := []
/-- `Tests.Compiler.KaryGenTest.topshare3`. -/
def ssKary : List PTShard := [KaryGen.ptShard]
/-- `Sparkle.Tests.Compiler.ShippingMachineNestTest.consumer`. -/
def ssNest : List PTShard := [MachineNest.ptShard]
/-- `Sparkle.IP.Bus.LINHW.checksumHW`. -/
def ssLin : List PTShard := [LINHW.ptShard]
/-- `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two`: the shard of its own module and the one of the module of its child. -/
def ssChild : List PTShard := [ChildBoundary.ptShard, MachineSeq.ptShard]
/-- `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte`: it needs the shards of two OTHER modules and not that of its own module. -/
def ssHft : List PTShard := [HFTStrategy.ptShard, HTTP.ptShard]
/-- `Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW`. -/
def ssSponge : List PTShard := [Keccak256HW.ptShard, Keccak256Sponge.ptShard]
/-- `Sparkle.Tests.Compiler.ShippingMachineTeleTest.divInLoop`: a root of a module that has a shard but needs none. -/
def ssDiv : List PTShard := []

/-- (root, shard names it needs, the list of shards used by the kernel statement as names) -/
def rootTable : List (Name × List Name) := [
  (`Sparkle.Tests.SignalLoopTest.counterLoop, []),
  (`Tests.Compiler.KaryGenTest.topshare3, [`KaryGen]),
  (`Sparkle.Tests.Compiler.ShippingMachineNestTest.consumer, [`MachineNest]),
  (`Sparkle.IP.Bus.LINHW.checksumHW, [`LINHW]),
  (`Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two, [`ChildBoundary, `MachineSeq]),
  (`Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte, [`HFTStrategy, `HTTP]),
  (`Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW, [`Keccak256HW, `Keccak256Sponge]),
  (`Sparkle.Tests.Compiler.ShippingMachineTeleTest.divInLoop, [])]

/-- the constant holding the shard list of each root, in the order of `rootTable` -/
def ssNames : List Name :=
  [`Tests.Gen5.PTRootShardCheck.ssLoop, `Tests.Gen5.PTRootShardCheck.ssKary, `Tests.Gen5.PTRootShardCheck.ssNest, `Tests.Gen5.PTRootShardCheck.ssLin,
   `Tests.Gen5.PTRootShardCheck.ssChild, `Tests.Gen5.PTRootShardCheck.ssHft, `Tests.Gen5.PTRootShardCheck.ssSponge, `Tests.Gen5.PTRootShardCheck.ssDiv]

/-- (shard name, constants that are keys of the shard) -/
def shardKeyNames : List (Name × List Name) := shards.map fun s => (s.1, (s.2.2.1.tyKeys ++ s.2.2.1.tmKeys).map (·.1))

/-! ## Kernel facts per root -/

theorem n_roots : rootTable.length = 8 := rfl
theorem n_ssNames : ssNames.length = 8 := rfl

/-- The key sets of all 23 shards are pairwise disjoint (re-stated from `PTShardCheck`): a shard key belongs to exactly one shard. -/
theorem keys_disjoint : paidKeys.Nodup := paid_nodup

-- freshness chains: each shard is fresh against the core composed with the shards before it
theorem chain_kary : FreshChain PTcore ssKary := ⟨⟨rfl, rfl⟩, trivial⟩
theorem chain_nest : FreshChain PTcore ssNest := ⟨⟨rfl, rfl⟩, trivial⟩
theorem chain_lin : FreshChain PTcore ssLin := ⟨⟨rfl, rfl⟩, trivial⟩
theorem chain_child : FreshChain PTcore ssChild := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩
theorem chain_hft : FreshChain PTcore ssHft := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩
theorem chain_sponge : FreshChain PTcore ssSponge := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩
theorem chain_loop : FreshChain PTcore ssLoop := trivial
theorem chain_div : FreshChain PTcore ssDiv := trivial

-- pairwise exclusivity of the shards of one root (the shard tables among themselves)
theorem excl_child : Excl ChildBoundary.ptShard.toPT MachineSeq.ptShard.toPT := (show FreshAgainst ChildBoundary.ptShard.toPT MachineSeq.ptShard from ⟨rfl, rfl⟩).excl
theorem excl_hft : Excl HFTStrategy.ptShard.toPT HTTP.ptShard.toPT := (show FreshAgainst HFTStrategy.ptShard.toPT HTTP.ptShard from ⟨rfl, rfl⟩).excl
theorem excl_sponge : Excl Keccak256HW.ptShard.toPT Keccak256Sponge.ptShard.toPT := (show FreshAgainst Keccak256HW.ptShard.toPT Keccak256Sponge.ptShard from ⟨rfl, rfl⟩).excl

-- coverage: every key of every needed shard has a row in the root table
theorem covers_kary : ssKary.all (Covers (rootPT ssKary)) = true := rfl
theorem covers_nest : ssNest.all (Covers (rootPT ssNest)) = true := rfl
theorem covers_lin : ssLin.all (Covers (rootPT ssLin)) = true := rfl
theorem covers_child : ssChild.all (Covers (rootPT ssChild)) = true := rfl
theorem covers_hft : ssHft.all (Covers (rootPT ssHft)) = true := rfl
theorem covers_sponge : ssSponge.all (Covers (rootPT ssSponge)) = true := rfl

-- negative controls: the composition without a needed shard does not cover its keys
theorem lack_kary : Covers (rootPT []) KaryGen.ptShard = false := rfl
theorem lack_nest : Covers (rootPT []) MachineNest.ptShard = false := rfl
theorem lack_lin : Covers (rootPT []) LINHW.ptShard = false := rfl
theorem lack_child_1 : Covers (rootPT [MachineSeq.ptShard]) ChildBoundary.ptShard = false := rfl
theorem lack_child_2 : Covers (rootPT [ChildBoundary.ptShard]) MachineSeq.ptShard = false := rfl
theorem lack_hft_1 : Covers (rootPT [HTTP.ptShard]) HFTStrategy.ptShard = false := rfl
theorem lack_hft_2 : Covers (rootPT [HFTStrategy.ptShard]) HTTP.ptShard = false := rfl
theorem lack_sponge_1 : Covers (rootPT [Keccak256Sponge.ptShard]) Keccak256HW.ptShard = false := rfl
theorem lack_sponge_2 : Covers (rootPT [Keccak256HW.ptShard]) Keccak256Sponge.ptShard = false := rfl
/-- The core alone does not cover a shard that has keys; the same shard composed does. -/
theorem lack_core_vs_comp : Covers PTcore KaryGen.ptShard = false ∧ Covers (rootPT ssKary) KaryGen.ptShard = true := ⟨rfl, rfl⟩

-- a row of a needed shard is found in the root table (generic theorem + the generated `_key`)
theorem hft_row_kept : (rootPT ssHft).tys `Sparkle.IP.Net.HTTP.HttpEmitOut [] = some HTTP.ptShardTy0.row :=
  rootPT_keeps_shard_tys chain_hft (S := HTTP.ptShard) (by simp [ssHft]) HTTP.ptShardTy0_key

-- the root whose only (empty) shard is dropped keeps the statement of `FGLedgerPremisesStmtPTC`
theorem loop_stmt_iff : FGLedgerPremisesStmtRoot ssLoop ↔ FGLedgerPremisesStmtPTC := fgLedgerPremisesStmtRoot_nil_iff
/-- The module shard of `Tests.SignalLoopTest` is empty: composing it changes nothing. -/
theorem signalLoop_shard_empty : SignalLoop.ptShard.tys = [] ∧ SignalLoop.ptShard.tms = [] := ⟨rfl, rfl⟩
theorem signalLoop_stmt_iff : FGLedgerPremisesStmtRoot [SignalLoop.ptShard] ↔ FGLedgerPremisesStmtPTC := by
  have : SignalLoop.ptShard = PTShard.empty := rfl
  rw [this]; exact fgLedgerPremisesStmtRoot_empty_iff

-- bridges from the statements already in the development
theorem stmt_kary : Tools.ShippingGen5CVFinal.FGLedgerPremisesStmtCV → FGLedgerPremisesStmtRoot ssKary := fun h => fgLedgerPremisesStmtRoot_of_CV h _
theorem stmt_child : Tools.ShippingGen5CVFinal.FGLedgerPremisesStmtCV → FGLedgerPremisesStmtRoot ssChild := fun h => fgLedgerPremisesStmtRoot_of_CV h _
theorem stmt_hft : Tools.ShippingGen5SM1.FGLedgerPremisesStmtH → FGLedgerPremisesStmtRoot ssHft := fun h => fgLedgerPremisesStmtRoot_of_H h _
theorem functional_hft : Tools.ShippingGen5FG.ConstValueFunctional (Tools.ShippingGen5CVFinal.CVFinal (rootPT ssHft)) := cvFinal_rootPT_functional _

-- the split of the named premises of a root: the premises of the shards of a root are exactly one pair per shard
theorem split_hft (env : Lean.Environment) :
    (Tools.ShippingGen5CVFinal.LitRows (rootPT ssHft) env ∧ Tools.ShippingGen5RowTypedV.OblRowTypedV (rootPT ssHft) env ∧
      ∀ c ls, Tools.ShippingGen5ConstValueEVL.RowTeleEvAt (rootPT ssHft) env c ls) ↔ RootNamed ssHft env := rootNamed_iff _ _
theorem split_sponge (env : Lean.Environment) :
    (Tools.ShippingGen5CVFinal.LitRows (rootPT ssSponge) env ∧ Tools.ShippingGen5RowTypedV.OblRowTypedV (rootPT ssSponge) env ∧
      ∀ c ls, Tools.ShippingGen5ConstValueEVL.RowTeleEvAt (rootPT ssSponge) env c ls) ↔ RootNamed ssSponge env := rootNamed_iff _ _
/-- The literal rows are the core's: the two env facts give `LitRows` for every root. -/
theorem lit_hft (env : Lean.Environment) (hN : ¬ Tools.ShippingGen5ConstValueE.IsDefn env `Nat) (hS : ¬ Tools.ShippingGen5ConstValueE.IsDefn env `String) :
    Tools.ShippingGen5CVFinal.LitRows (rootPT ssHft) env := litRows_rootPT_of_env hN hS

/-- Rows carrying a shard premise: the term rows of the shards of the root (types need none: only `tms` rows enter `RowTypedAtV` / `RowTeleEvAt`). -/
def shardTmRows (Ss : List PTShard) : Nat := (Ss.map fun S => S.tms.length).sum
def shardTyRows (Ss : List PTShard) : Nat := (Ss.map fun S => S.tys.length).sum

/-- (type rows, term rows) of the shards of each root, in the order of `rootTable`: the term rows are the keys that carry a shard premise. -/
def rowCounts : List (Nat × Nat) :=
  [ssLoop, ssKary, ssNest, ssLin, ssChild, ssHft, ssSponge, ssDiv].map fun Ss => (shardTyRows Ss, shardTmRows Ss)

theorem rowCounts_eq : rowCounts = [(0, 0), (1, 1), (2, 2), (2, 2), (2, 2), (4, 4), (3, 3), (0, 0)] := rfl

/-! ## Meta audit of the real environment (NOT a kernel proof) -/

open Tests.Gen5.CVFinalCheck (valOf headOf)

/-- Unfold `FGLedgerPremisesStmtRoot Ss` (two definitional unfoldings: `Root Ss`, `RootAt (rootPT Ss)`). -/
def unfoldedRoot (ssVal : Expr) : MetaM Expr := do
  let e0 := mkApp (mkConst ``FGLedgerPremisesStmtRoot) ssVal
  let some e1 ← unfoldDefinition? e0 | throwError "cannot unfold FGLedgerPremisesStmtRoot"
  let some e2 ← unfoldDefinition? e1 | throwError "cannot unfold FGLedgerPremisesStmtRootAt"
  return e2

def shardConsts (e : Expr) : List Name :=
  (e.foldConsts ([] : List Name) fun c acc => if c.isSuffixOf `ptShard || (c.getString! == "ptShard") then c :: acc else acc).eraseDups

run_meta do
  let env ← getEnv
  let tbl ← unsafe evalConst (List (Name × List Name)) ``rootTable
  let ssNs ← unsafe evalConst (List Name) ``ssNames
  let sk ← unsafe evalConst (List (Name × List Name)) ``shardKeyNames
  let ptc ← valOf ``FGLedgerPremisesStmtPTC
  let (oP, iP) ← forallTelescope ptc fun xs co => do
    let i ← if co.isAppOfArity ``And 2 then forallTelescope co.appArg! fun ys _ => pure ys.size else pure 0
    pure (xs.size, i)
  let mut report : Array String := #[]
  for ((root, declared), ssN) in tbl.zip ssNs do
    -- 1. the shards of the root derived from the keys of the generated shards
    let (seen, todo) := Tests.Gen5.PrimResidueKey.reach env root 400000
    unless todo.isEmpty do throwError "{root}: fuel exhausted"
    let names := seen.toList.map (·.1.1)
    let derived := sk.filter (fun (_, ks) => ks.any names.contains) |>.map (·.1)
    unless derived == declared do throwError "{root}: shards derived from the keys {derived} differ from the declared {declared}"
    -- minimality: every declared shard has a reached key; the reached keys per shard
    let mut hits : List String := []
    for sn in declared do
      let some (_, ks) := sk.find? (·.1 == sn) | throwError "unknown shard {sn}"
      let h := (ks.filter names.contains).eraseDups
      if h.isEmpty then throwError "{root}: shard {sn} has no reached key"
      hits := hits ++ [s!"{sn}: {h.length} reached keys"]
    -- 2. census of the unfolded statement
    let some ci := env.find? ssN | throwError "{ssN}"
    let ssVal := ci.value!
    let e1 ← unfoldedRoot ssVal
    let rootPTe := mkApp (mkConst ``rootPT) ssVal
    let ePtc := ptc.replace fun e => if e.isConstOf ``PTcorpus then some rootPTe else none
    unless e1 == ePtc do throwError "{root}: the statement is not FGLedgerPremisesStmtPTC with PTcorpus := rootPT Ss"
    if ptc == e1 && !declared.isEmpty then throwError "{root}: control failed, the statement equals the PTcorpus one"
    let (o1, i1, heads, nPT) ← (forallTelescope e1 fun xs co => do
      let mut nPT : Nat := 0
      for x in xs do
        if (← x.fvarId!.getDecl).type.isConstOf ``Tools.ShippingGen5ConstValueEKey.PrimTableK then nPT := nPT + 1
      if co.isAppOfArity ``And 2 then
        forallTelescope co.appArg! fun ys _ => do
          let mut hs : List Name := []
          for y in ys do hs := hs ++ [← headOf (← y.fvarId!.getDecl).type]
          pure (xs.size, ys.size, hs, nPT)
      else pure (xs.size, 0, [], nPT) : MetaM (Nat × Nat × List Name × Nat))
    unless o1 == oP && i1 == iP && nPT == 0 do throwError "{root}: census differs: outer {o1}/{oP}, inner {i1}/{iP}, PrimTableK binders {nPT}"
    let named := heads.filter fun h => [``Tools.ShippingGen5EnvDeclClosed.KernelClosedInvariant, ``Tools.ShippingGen5CVFinal.LitRows,
      ``Tools.ShippingGen5RowTypedV.OblRowTypedV, ``Tools.ShippingGen5ConstValueEVL.RowTeleEvAt].contains h
    unless named.length == 4 do throwError "{root}: named inner premises {named}"
    let inStmt : List String := (shardConsts e1).map (fun c => c.getPrefix.getString!)
    unless (inStmt.toArray.qsort (· < ·)) == ((declared.map toString).toArray.qsort (· < ·)) do throwError "{root}: shards in the statement {inStmt} differ from {declared}"
    report := report.push s!"{root}: needs {declared} ({hits}); statement = PTC[PTcorpus := rootPT]: outer {o1}, inner {i1}, PrimTableK binders {nPT}, named inner premises {named.length}, shards in the statement {inStmt}"
  logInfo m!"ROOT CENSUS (PTC: outer {oP}, inner {iP})\n{"\n".intercalate report.toList}\nnamed premises of every root: OblLbrZero (outer), KernelClosedInvariant, LitRows (rootPT), OblRowTypedV (rootPT), RowTeleEvAt (rootPT) = 5; per shard: one pair (RowTypedAtV, RowTeleEvAt) at the shard's term keys"
  -- control: the census text for a root differs from the PTcorpus one iff the table is replaced (a root with shards)
  let rc ← unsafe evalConst (List (Nat × Nat)) ``rowCounts
  logInfo m!"shard rows per root (type rows, term rows; each term row carries the pair RowTypedAtV / RowTeleEvAt): {rc}"
  logInfo m!"CONTROL ok: for roots with shards the statement text differs from FGLedgerPremisesStmtPTC"

end Tests.Gen5.PTRootShardCheck

#print axioms Tests.Gen5.PTRootShardCheck.chain_sponge
#print axioms Tests.Gen5.PTRootShardCheck.covers_sponge
#print axioms Tests.Gen5.PTRootShardCheck.lack_sponge_1
#print axioms Tests.Gen5.PTRootShardCheck.hft_row_kept
#print axioms Tests.Gen5.PTRootShardCheck.signalLoop_stmt_iff
#print axioms Tests.Gen5.PTRootShardCheck.stmt_hft
#print axioms Tests.Gen5.PTRootShardCheck.split_sponge
#print axioms Tests.Gen5.PTRootShardCheck.lit_hft
#print axioms Tests.Gen5.PTRootShardCheck.functional_hft
#print axioms Tests.Gen5.PTRootShardCheck.rowCounts_eq
#print axioms Tests.Gen5.PTRootShardCheck.lack_child_1
#print axioms Tests.Gen5.PTRootShardCheck.excl_hft
