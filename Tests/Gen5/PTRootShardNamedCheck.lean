import Lean
import Tools.ShippingGen5PTRootShardNamed
import Tests.Gen5.PTRootShardCheck
import Tests.Gen5.PTShardCheck
import Tests.Gen5.CVFinalCheck
import Tests.Gen5.PrimResidueKeyLib
set_option autoImplicit false
-- D.D-4 Q-B check, root-name-fixed statements (Issue sparkle-ledger-dd4-shard, changes_requested fixes 1-4). No sorry / axiom / native_decide / TRUSTED. PTcorpus, G-PRIM and the ledger are NOT decided here.

/-! # Root check, root name in the statement

Fixes over `PTRootShardCheck` (that file is unchanged):

1. Root name. `FGLedgerPremisesStmtRootEntry root Ss` (`Tools.ShippingGen5PTRootShardNamed`) has the entry name `root` inside the statement.
   Per representative root there is a constant `stmtXxx := FGLedgerPremisesStmtRootEntry <root> ssXxx` (kernel data). The meta audit reads that constant and checks:
   the name inside it is the root name of `rootTable` and a constant of the environment; the shard list is the constant `ssXxx`;
   the unfolded statement is, as an expression, `FGLedgerPremisesStmtPTC` with `PTcorpus := rootPT ssXxx` and the quantifier `∀ declName` instantiated with that name (`==`);
   the name occurs in the statement. Negative control: the statement of the SAME shard list with another root's name is not the same expression (all ordered pairs; two roots with an empty list included).
2. Bridges. The bridges below are SPECIALISATIONS of `FGLedgerPremisesStmtCV` / `H` (unproved statements). `FGLedgerPremisesStmtRoot Ss` is equivalent to `FGLedgerPremisesStmtPTC` only for `Ss = []` or the empty shard.
   They are not a proof that a real root exists, that its shards are what it needs, or that any semantics is preserved.
3. Shard selection is by NAME. The derivation of the shard list from the reached constants is a selection of CANDIDATES by name: not a proof that the listed shards cover every key a root needs, and not minimal.
   Added here: (a) keys matched as Name × levels, (b) the constants of the types of the reached constants too (binder types and result types). The counts of the three variants are reported and compared.
4. `CoreRowTypedV` / `CoreRowTeleEv` are predicates on the COMPOSED table `rootPT Ss`. The proofs of `PTcorpus` rows (Q-C) are about `PTcorpus`; they do not transfer as they are
   (see the lemma shape in the output of this file; it is a shape, not proved here). -/
open Lean Meta

namespace Tests.Gen5.PTRootShardNamedCheck
open Tools.ShippingGen5PTShard Tools.ShippingGen5PTRootShard Tools.ShippingGen5PTCorpus
open Tests.Gen5.PTShardCheck (shards)
open Tests.Gen5.PTShard
open Tests.Gen5.PTRootShardCheck

/-! ## The statement of each representative root (kernel data) -/

noncomputable def stmtLoop : Prop := FGLedgerPremisesStmtRootEntry `Sparkle.Tests.SignalLoopTest.counterLoop ssLoop
noncomputable def stmtKary : Prop := FGLedgerPremisesStmtRootEntry `Tests.Compiler.KaryGenTest.topshare3 ssKary
noncomputable def stmtNest : Prop := FGLedgerPremisesStmtRootEntry `Sparkle.Tests.Compiler.ShippingMachineNestTest.consumer ssNest
noncomputable def stmtLin : Prop := FGLedgerPremisesStmtRootEntry `Sparkle.IP.Bus.LINHW.checksumHW ssLin
noncomputable def stmtChild : Prop := FGLedgerPremisesStmtRootEntry `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two ssChild
noncomputable def stmtHft : Prop := FGLedgerPremisesStmtRootEntry `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte ssHft
noncomputable def stmtSponge : Prop := FGLedgerPremisesStmtRootEntry `Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW ssSponge
noncomputable def stmtDiv : Prop := FGLedgerPremisesStmtRootEntry `Sparkle.Tests.Compiler.ShippingMachineTeleTest.divInLoop ssDiv

/-- the constant of each root's statement, in the order of `rootTable` -/
def stmtNames : List Name :=
  [`Tests.Gen5.PTRootShardNamedCheck.stmtLoop, `Tests.Gen5.PTRootShardNamedCheck.stmtKary, `Tests.Gen5.PTRootShardNamedCheck.stmtNest, `Tests.Gen5.PTRootShardNamedCheck.stmtLin,
   `Tests.Gen5.PTRootShardNamedCheck.stmtChild, `Tests.Gen5.PTRootShardNamedCheck.stmtHft, `Tests.Gen5.PTRootShardNamedCheck.stmtSponge, `Tests.Gen5.PTRootShardNamedCheck.stmtDiv]

theorem n_stmtNames : stmtNames.length = 8 := rfl

/-- the shard list is CHOSEN from the entry name inside the quantifier (`FGLedgerPremisesStmtRootBy`): a table on the representative roots, `[]` elsewhere -/
def tabK (d : Name) : List PTShard :=
  if d == `Tests.Compiler.KaryGenTest.topshare3 then ssKary
  else if d == `Sparkle.Tests.Compiler.ShippingMachineNestTest.consumer then ssNest
  else if d == `Sparkle.IP.Bus.LINHW.checksumHW then ssLin
  else if d == `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two then ssChild
  else if d == `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte then ssHft
  else if d == `Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW then ssSponge
  else []

theorem tabK_hft : tabK `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte = ssHft := rfl
theorem tabK_sponge : tabK `Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW = ssSponge := rfl
theorem tabK_child : tabK `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two = ssChild := rfl
theorem tabK_loop : tabK `Sparkle.Tests.SignalLoopTest.counterLoop = [] := rfl
/-- control: the table is indexed by the root name: the hft root and the sponge root get different lists -/
theorem tabK_ne : tabK `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte ≠ tabK `Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW :=
  fun h => absurd (congrArg (fun l => l.map PTShard.tyKeys) h) (by decide)

-- bridges: SPECIALISATIONS of CV / H (unproved statements); not a proof about a real root
theorem stmt_hft_of_CV : Tools.ShippingGen5CVFinal.FGLedgerPremisesStmtCV → stmtHft := fun h => fgLedgerPremisesStmtRootEntry_of_CV h _ _
theorem stmt_sponge_of_H : Tools.ShippingGen5SM1.FGLedgerPremisesStmtH → stmtSponge := fun h => fgLedgerPremisesStmtRootEntry_of_H h _ _
theorem by_of_CV : Tools.ShippingGen5CVFinal.FGLedgerPremisesStmtCV → FGLedgerPremisesStmtRootBy tabK := fun h => fgLedgerPremisesStmtRootBy_of_CV h _
/-- chosen-inside form gives the fixed-name form for the root and the list the table chooses for it -/
theorem entry_of_by_hft (h : FGLedgerPremisesStmtRootBy tabK) : FGLedgerPremisesStmtRootEntry `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte ssHft := by
  have this : FGLedgerPremisesStmtRootEntry `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte (tabK `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte) :=
    fgLedgerPremisesStmtRootEntry_of_By h _
  rwa [tabK_hft] at this
/-- the only equivalence with `PTC` is for the empty list: `Root [] ↔ PTC` (`Iff.rfl`, all entries); for one entry, `PTC → RootEntry root []` -/
theorem loop_of_PTC : Tools.ShippingGen5PTCorpus.FGLedgerPremisesStmtPTC → stmtLoop := fun h => fgLedgerPremisesStmtRootEntry_nil_of_PTC h _

/-! ## Meta audit (NOT a kernel proof) -/

open Tests.Gen5.CVFinalCheck (valOf headOf)
open Tests.Gen5.PrimResidueKey (occs lvlKey)
open Tools.ShippingGen5ConstValueE (LS)

/-- `reach` of `PrimResidueKey`, and in addition the constants of the TYPE of every reached constant (binder types and result type) -/
def reachT (env : Environment) (root : Name) (fuel0 : Nat) : Std.HashMap (Name × String) Bool × Array (Name × List Level) := Id.run do
  let closedL (ls : List Level) := ls.all (fun l => !l.hasParam && !l.hasMVar)
  let r0 := LS env root
  let mut seen : Std.HashMap (Name × String) Bool := ({} : Std.HashMap (Name × String) Bool).insert (root, lvlKey r0) (closedL r0)
  let mut todo : Array (Name × List Level) := #[(root, r0)]
  let mut fuel := fuel0
  while fuel > 0 && todo.size > 0 do
    fuel := fuel - 1
    let (n, ls) := todo.back!
    todo := todo.pop
    match env.find? n with
    | some ci =>
      let mut found : Array (Name × List Level) := #[]
      if ls.length == ci.levelParams.length then
        found := occs env (ci.type.instantiateLevelParams ci.levelParams ls) found
        if let .defnInfo d := ci then
          found := occs env (d.value.instantiateLevelParams d.levelParams ls) found
      for (c, cl) in found do
        let k := (c, lvlKey cl)
        if !seen.contains k then
          seen := seen.insert k (closedL cl)
          todo := todo.push (c, cl)
    | none => pure ()
  return (seen, todo)

def subterm? (e : Expr) (t : Expr) : Bool := (e.find? (· == t)).isSome

/-- expected statement of `root`: the unfolded `PTC` with `PTcorpus := rootPT Ss` and `∀ declName` instantiated with `nameE` -/
def expectedStmt (ptc : Expr) (ssVal nameE : Expr) : MetaM Expr := do
  let ptcR := ptc.replace fun e => if e.isConstOf ``PTcorpus then some (mkApp (mkConst ``rootPT) ssVal) else none
  forallTelescope ptcR fun xs co => do
    unless co.isAppOfArity ``And 2 do throwError "PTC conclusion is not a conjunction"
    let g := co.appArg!
    unless g.isForall do throwError "PTC second conjunct is not a ∀"
    mkForallFVars xs (mkApp2 (mkConst ``And) co.appFn!.appArg! (g.bindingBody!.instantiate1 nameE))

def unfoldedEntry (nameE ssVal : Expr) : MetaM Expr := do
  let e0 := mkApp2 (mkConst ``FGLedgerPremisesStmtRootEntry) nameE ssVal
  let some e1 ← unfoldDefinition? e0 | throwError "cannot unfold FGLedgerPremisesStmtRootEntry"
  let some e2 ← unfoldDefinition? e1 | throwError "cannot unfold FGLedgerPremisesStmtEntryAt"
  return e2

/-- all keys of a shard as Name × levels -/
def shardKeyLevels : List (Name × List (Name × List Nat)) := shards.map fun s => (s.1, s.2.2.1.tyKeys ++ s.2.2.1.tmKeys)

run_meta do
  let env ← getEnv
  let tbl ← unsafe evalConst (List (Name × List Name)) ``rootTable
  let stmts ← unsafe evalConst (List Name) ``stmtNames
  let ssNs ← unsafe evalConst (List Name) ``ssNames
  let skl ← unsafe evalConst (List (Name × List (Name × List Nat))) ``shardKeyLevels
  let ptc ← valOf ``Tools.ShippingGen5PTCorpus.FGLedgerPremisesStmtPTC
  let mut report : Array String := #[]
  let mut ens : Array (Name × Expr × Expr × Expr) := #[]   -- root, nameE, ssVal, unfolded statement
  -- 1. root name inside the statement
  for ((root, declared), (sN, ssN)) in tbl.zip (stmts.zip ssNs) do
    let some ci := env.find? sN | throwError "{sN}"
    let args := ci.value!.getAppArgs
    unless ci.value!.getAppFn.isConstOf ``FGLedgerPremisesStmtRootEntry && args.size == 2 do throwError "{sN}: not FGLedgerPremisesStmtRootEntry root Ss"
    let nameE := args[0]!
    let ssE := args[1]!
    let nameV ← unsafe evalExpr Name (mkConst ``Name) nameE
    unless nameV == root do throwError "{sN}: the name in the statement is {nameV}, the root of rootTable is {root}"
    unless env.contains root do throwError "{root}: not a constant of the environment"
    unless ssE.isConstOf ssN do throwError "{sN}: shard list {ssE} is not {ssN}"
    let ssVal := (env.find? ssN).get!.value!
    let e1 ← unfoldedEntry nameE ssVal
    unless e1 == (← expectedStmt ptc ssVal nameE) do throwError "{root}: the statement is not PTC[PTcorpus := rootPT Ss, declName := root]"
    unless subterm? e1 nameE do throwError "{root}: the root name does not occur in the statement"
    unless (← forallTelescope e1 fun xs _ => pure xs.size) == 13 do throwError "{root}: outer binders differ"
    ens := ens.push (root, nameE, ssVal, e1)
    report := report.push s!"{root}: name in statement = rootTable name, constant of the environment, shards {declared}, statement = PTC[PTcorpus := rootPT Ss][declName := root]"
  logInfo m!"ROOT NAME IN STATEMENT (8 roots)\n{"\n".intercalate report.toList}"
  -- 2. negative control: same shard list, another root's name (all ordered pairs)
  let mut pairs : Nat := 0
  let mut samelist : Nat := 0
  for (ri, _, ssi, ei) in ens do
    for (rj, nj, _, _) in ens do
      if ri != rj then
        let ej ← unfoldedEntry nj ssi
        if ej == ei then throwError "control failed: the statement of {ri} equals the one with the name {rj} and the same shard list"
        if (← expectedStmt ptc ssi nj) == ei then throwError "control failed (expected): {ri} vs {rj}"
        if subterm? ei nj then throwError "control: the name of {rj} occurs in the statement of {ri}"
        pairs := pairs + 1
  for (ri, _, ssi, _) in ens do
    for (rj, _, ssj, _) in ens do
      if ri != rj && ssi == ssj then samelist := samelist + 1
  logInfo m!"CONTROL ok: {pairs} ordered pairs (root i, name of root j): the statement with the shard list of i and the name of j differs from the statement of i ({samelist} of the pairs have identical shard-list constants, e.g. the two roots with the empty list)"
  -- 3. candidates by name / Name × levels / + types
  let mut rows : Array String := #[]
  let mut totN : Nat := 0
  let mut totL : Nat := 0
  let mut totT : Nat := 0
  for ((root, declared), _) in tbl.zip ssNs do
    let (seen, todo) := Tests.Gen5.PrimResidueKey.reach env root 400000
    unless todo.isEmpty do throwError "{root}: fuel exhausted"
    let (seenT, todoT) := reachT env root 400000
    unless todoT.isEmpty do throwError "{root}: fuel exhausted (types)"
    let names := seen.toList.map (·.1.1)
    let namesT := seenT.toList.map (·.1.1)
    -- by name only (the selection the kernel statement was checked against)
    let derived := skl.filter (fun (_, ks) => ks.any (fun k => names.contains k.1)) |>.map (·.1)
    unless derived == declared do throwError "{root}: shards selected by name {derived} differ from the declared {declared}"
    let lvKey (k : Name × List Nat) : Name × String := (k.1, lvlKey (k.2.map Level.ofNat))
    let hitN (m : Std.HashMap (Name × String) Bool) (nm : List Name) : Nat := skl.foldl (fun a (_, ks) => a + (ks.filter (fun k => nm.contains k.1)).length) 0
    let hitL (m : Std.HashMap (Name × String) Bool) : Nat := skl.foldl (fun a (_, ks) => a + (ks.filter (fun k => m.contains (lvKey k))).length) 0
    let nN := hitN seen names
    let nL := hitL seen
    let nT := hitL seenT
    let nTN := hitN seenT namesT
    let derL := skl.filter (fun (_, ks) => ks.any (fun k => seen.contains (lvKey k))) |>.map (·.1)
    let derT := skl.filter (fun (_, ks) => ks.any (fun k => seenT.contains (lvKey k))) |>.map (·.1)
    let derTN := skl.filter (fun (_, ks) => ks.any (fun k => namesT.contains k.1)) |>.map (·.1)
    -- the keys whose name is reached but not at the shard's levels
    let lvMiss := skl.foldl (fun a (_, ks) => a ++ (ks.filter (fun k => names.contains k.1 && !seen.contains (lvKey k))).map (·.1)) ([] : List Name)
    totN := totN + nN; totL := totL + nL; totT := totT + nT
    rows := rows.push s!"{root}: declared {declared}; by name {nN} keys {derived}; Name×levels (body) {nL} keys {derL}; Name×levels + types {nT} keys {derT}; by name + types {nTN} keys {derTN}; name reached at other levels: {lvMiss}; reached nodes body {seen.size} / body+types {seenT.size}"
  logInfo m!"SHARD CANDIDATES (selection by NAME; not a proof of coverage of the keys a root needs, not minimal)\n{"\n".intercalate rows.toList}\ntotal shard keys hit over the 8 roots: by name {totN}, Name×levels (body) {totL}, Name×levels + types {totT}"
  logInfo m!"LEMMA SHAPE (not proved here): for the core rows to transfer from PTcorpus to rootPT Ss one needs, for the derivations behind RowTypedAtV / RowTeleEvAt, monotonicity in the table: ∀ A B, (∀ c ls r, A.tms c ls = some r → B.tms c ls = some r) ∧ (same for tys) → ∀ env c ls, RowTypedAtV A env c ls → RowTypedAtV B env c ls (and the same for RowTeleEvAt). With such a lemma and rootPT_keeps_core_tms / tys, CoreRowTypedV (rootPT Ss) would follow from the PTcorpus rows. The predicates are on the composed table, so without this lemma the Q-C proofs do not apply."

end Tests.Gen5.PTRootShardNamedCheck

#print axioms Tests.Gen5.PTRootShardNamedCheck.stmt_hft_of_CV
#print axioms Tests.Gen5.PTRootShardNamedCheck.stmt_sponge_of_H
#print axioms Tests.Gen5.PTRootShardNamedCheck.by_of_CV
#print axioms Tests.Gen5.PTRootShardNamedCheck.entry_of_by_hft
#print axioms Tests.Gen5.PTRootShardNamedCheck.loop_of_PTC
#print axioms Tests.Gen5.PTRootShardNamedCheck.tabK_ne
#print axioms Tests.Gen5.PTRootShardNamedCheck.tabK_hft
