import Lean
import Tools.ShippingGen5PTCorpus
import Tests.Gen5.CVFinalCheck
import Tests.Gen5.PrimResidueKeyLib
import Tests.SignalLoopTest
set_option autoImplicit false
-- D.D-4 final, PTcorpus census (Issue sparkle-ledger-dd4-final). No sorry / axiom / native_decide. The net delta of the ledger is NOT decided here.

/-! # `PTcorpus`: the table, the obligations that remain, and the statement census

1. Kernel-checked counts of the generated table (`rfl`): 50 type rows, 51 term rows, 106 keys without a row (by reason), 204 = 98 + 106 keys of the K1 list (the table has 3 extra closure rows: `String`, `ActiveEdge`, `ResetKind`).
2. Which `RowTypedAtV` / `RowTeleEvAt` rows are proved (a theorem of that name exists in the environment) and the list of the OTHER present rows (named obligations, one per key).
3. `FGLedgerPremisesStmtCV` → `FGLedgerPremisesStmtPTC`: binder census with `compareCV` of `CVFinalCheck` (removed `[PT]`, nothing added, the four inner premises unchanged); `H → PTC`: removed `[CV]`, added `[h_D_LBR]`, four inner premises.
4. The env facts that the proved row theorems take as hypotheses are evaluated in the real environment.
5. For three Signal roots of the corpus module `Tests.SignalLoopTest`: the residue keys they reach and whether each has a row in `PTcorpus` (necessary condition for the derivation, see the note in the output). -/
open Lean Meta

namespace Tests.Gen5.PTCorpusCheck
open Tools.ShippingGen5PTCorpus Tests.Gen5.CVFinalCheck

theorem n_ty : tysTable.length = 50 := rfl
theorem n_tm : tmsTable.length = 51 := rfl
theorem n_miss : missingTable.length = 106 := rfl
theorem n_recursor : (missingTable.filter fun e => e.2.2 == MissingWhy.recursor).length = 15 := rfl
theorem n_notImportable : (missingTable.filter fun e => e.2.2 == MissingWhy.notImportable).length = 51 := rfl
theorem n_binderAbove : (missingTable.filter fun e => e.2.2 == MissingWhy.binderAboveType0).length = 25 := rfl
theorem n_propBinder : (missingTable.filter fun e => e.2.2 == MissingWhy.propBinder).length = 6 := rfl
theorem n_resultAbove : (missingTable.filter fun e => e.2.2 == MissingWhy.resultAboveType0).length = 4 := rfl
theorem n_familyNot : (missingTable.filter fun e => e.2.2 == MissingWhy.familyNotType0).length = 5 := rfl
/-- 204 keys of K1 = 98 rows from the list (50 + 51 − 3 closure rows) + 106 without a row. -/
theorem n_k1 : tysTable.length + tmsTable.length - 3 + missingTable.length = 204 := rfl

def tmKeys : List (Name × List Nat × List Bool) := tmsTable.map fun e => (e.1, e.2.1, e.2.2.1)
def tyKeys : List (Name × List Nat × List Bool) := tysTable.map fun e => (e.1, e.2.1, e.2.2.1)
def missKeys : List (Name × List Nat × String) := missingTable.map fun e => (e.1, e.2.1, reprStr e.2.2)

def lvStr (ns : List Nat) : String := "[" ++ ", ".intercalate (ns.map toString) ++ "]"

/-- Present term rows whose `RowTypedAtV` is proved by a theorem of this development (not by hypothesis-free construction: the env facts stay hypotheses). -/
def manualRowTypedProved : List Name :=
  [``Nat.zero, ``Bool.false, ``Bool.true, ``PUnit.unit, `Sparkle.Core.Domain.ActiveEdge.rising, `Sparkle.IR.Type.ResetKind.synchronous,
   ``Nat.succ, ``Int.ofNat, ``Int.negSucc, `Sparkle.Core.Domain.DomainConfig.mk]
def manualTeleEvProved : List Name := [``Nat.succ, ``Int.ofNat, ``Int.negSucc, `Sparkle.Core.Domain.DomainConfig.mk]

def PTC := ``Tools.ShippingGen5PTCorpus.FGLedgerPremisesStmtPTC

run_meta do
  let env ← getEnv
  let tm ← unsafe evalConst (List (Name × List Nat × List Bool)) ``tmKeys
  let ty ← unsafe evalConst (List (Name × List Nat × List Bool)) ``tyKeys
  let miss ← unsafe evalConst (List (Name × List Nat × String)) ``missKeys
  -- 2. proved rows
  let mut provedTyped : Array String := #[]
  let mut openTyped : Array String := #[]
  let mut provedTele : Array String := #[]
  let mut openTele : Array String := #[]
  let mut i := 0
  for (n, ns, ks) in tm do
    let key := s!"{n} {lvStr ns} kinds={ks}"
    let dep := env.contains (Name.mkStr (`Tools.ShippingGen5PTCorpus) s!"ptc_rowTypedV_tm_{i}")
    if dep || manualRowTypedProved.contains n then provedTyped := provedTyped.push key else openTyped := openTyped.push key
    if ks.isEmpty || manualTeleEvProved.contains n then provedTele := provedTele.push key else openTele := openTele.push key
    i := i + 1
  logInfo m!"PTcorpus rows: type {ty.length}, term {tm.length}; no row: {miss.length}\nRowTypedAtV proved for {provedTyped.size} of {tm.length} term rows (6 nullary + 3 closed + DomainConfig.mk + 22 first-argument dependent); OPEN {openTyped.size}:\n{"\n".intercalate openTyped.toList}\nRowTeleEvAt proved for {provedTele.size} (6 nullary + 4 closed-constant telescopes); OPEN {openTele.size} (first 8: {openTele.toList.take 8})"
  if provedTyped.size + openTyped.size != 51 then throwError "row count"
  -- every proved-by-name theorem exists
  for t in [``ptc_rowTypedV_Nat_zero, ``ptc_rowTypedV_Bool_false, ``ptc_rowTypedV_Bool_true, ``ptc_rowTypedV_PUnit_unit1, ``ptc_rowTypedV_ActiveEdge_rising,
      ``ptc_rowTypedV_ResetKind_synchronous, ``ptc_rowTypedV_Nat_succ, ``ptc_rowTypedV_Int_ofNat, ``ptc_rowTypedV_Int_negSucc, ``ptc_rowTypedV_DomainConfig_mk,
      ``ptc_teleEv_Nat_succ, ``ptc_teleEv_Int_ofNat, ``ptc_teleEv_Int_negSucc, ``ptc_teleEv_DomainConfig_mk, ``ptc_teleEv_nullary, ``ptcorpus_litRows,
      ``fgLedgerPremisesStmtPTC_of_CV, ``fgLedgerPremisesStmtPTC_of_H, ``firstArgSpec_ty, ``TmTele.run_ty] do
    unless env.contains t do throwError "{t} missing"
    let ax ← Lean.collectAxioms t
    unless ax.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do throwError "{t}: non-standard axioms {ax}"
  let nDep := (List.range 51).filter (fun j => env.contains (Name.mkStr `Tools.ShippingGen5PTCorpus s!"ptc_rowTypedV_tm_{j}")) |>.length
  unless nDep == 22 do throwError "first-argument dependent theorems: {nDep}"
  for j in List.range 51 do
    let t := Name.mkStr `Tools.ShippingGen5PTCorpus s!"ptc_rowTypedV_tm_{j}"
    if env.contains t then
      let ax ← Lean.collectAxioms t
      unless ax.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do throwError "{t}: non-standard axioms {ax}"
  -- 3. census
  let rP (xn : Array Expr) (nameN : Array Name) : MetaM (Option (Name × Expr)) := pure (some (`PT, mkConst ``PTcorpus))
  let dCP ← compareCV C PTC rP
  let dHP ← compareCV H PTC (fun xn nameN => do
    let some j := (List.range xn.size).find? fun j => nameN[j]! == `PT | pure none
    pure none)
  let dHP2 ← compareCV H PTC (fun _ _ => pure (some (`CV, mkApp (mkConst ``Tools.ShippingGen5CVFinal.CVFinal) (mkConst ``PTcorpus))))
  unless dCP.removed == [`PT] && dCP.added.isEmpty && dCP.changed.isEmpty && dCP.firstConj && dCP.innerRemoved == 0 && dCP.innerAdded.isEmpty && dCP.concl do
    throwError "CV vs PTC: unexpected diff {repr dCP}"
  unless dHP2.removed == [`CV] && dHP2.added == [`h_D_LBR] && dHP2.changed.isEmpty && dHP2.firstConj && dHP2.innerRemoved == 0 &&
      dHP2.innerAdded == [``Tools.ShippingGen5EnvDeclClosed.KernelClosedInvariant, ``Tools.ShippingGen5CVFinal.LitRows,
        ``Tools.ShippingGen5RowTypedV.OblRowTypedV, ``Tools.ShippingGen5ConstValueEVL.RowTeleEvAt] && dHP2.concl do
    throwError "H vs PTC: unexpected diff {repr dHP2}"
  -- controls: without the substitution PT := PTcorpus the census does not pass; H against PTC without CV := CVFinal PTcorpus does not pass
  if (← compareCV C PTC (fun _ _ => pure none)).removed.isEmpty then throwError "CONTROL: census passes without PT := PTcorpus"
  let hasPT : Nat ← forallTelescope (← valOf PTC) fun xs _ => do
    let mut c : Nat := 0
    for x in xs do
      if (← x.fvarId!.getDecl).type.isConstOf ``Tools.ShippingGen5ConstValueEKey.PrimTableK then c := c + 1
    return c
  unless hasPT == 0 do throwError "PrimTableK binders left in PTC: {hasPT}"
  let (oC, oP, iC, iP) := (← outerCount C, ← outerCount PTC, ← innerCount C, ← innerCount PTC)
  unless oP + 1 == oC && iP == iC do throwError "binder counts: outer {oC} -> {oP}, inner {iC} -> {iP}"
  let (oH, iH) := (← outerCount H, ← innerCount H)
  logInfo m!"CENSUS: FGLedgerPremisesStmtCV -> FGLedgerPremisesStmtPTC: removed {repr dCP.removed}, added {repr dCP.added}, inner added {repr dCP.innerAdded}; PrimTableK binders left 0; outer binders {oC} -> {oP}, inner hypotheses {iC} -> {iP}\nFGLedgerPremisesStmtH -> PTC: removed {repr dHP2.removed}, added {repr dHP2.added}, inner added {repr dHP2.innerAdded.length} ({repr dHP2.innerAdded}); outer binders {oH} -> {oP}, inner hypotheses {iH} -> {iP}\nremaining named premises of the statement: OblLbrZero (outer), KernelClosedInvariant, LitRows PTcorpus (provable from the two env facts, ptcorpus_litRows), OblRowTypedV PTcorpus, RowTeleEvAt PTcorpus"
  -- 4. env facts of the proved rows, in the real environment
  let isDefn (c : Name) : Bool := match env.find? c with | some (.defnInfo _) => true | _ => false
  for c in [``Nat, ``Int, ``Bool, ``PUnit, `String, `Sparkle.Core.Domain.ActiveEdge, `Sparkle.Core.Domain.DomainConfig] do
    if isDefn c then throwError "{c} is a definition (hnd fails)"
  logInfo m!"env facts: Nat Int Bool PUnit String ActiveEdge DomainConfig are not definitions (hnd holds); ResetKind is {if isDefn `Sparkle.IR.Type.ResetKind then "a definition (alias)" else "not a definition"}"
  -- 5. Signal roots of the corpus module
  let tmSet : Std.HashSet String := tm.foldl (fun s (n, ns, _) => s.insert s!"{n}|{lvStr ns}") {}
  let tySet : Std.HashSet String := ty.foldl (fun s (n, ns, _) => s.insert s!"{n}|{lvStr ns}") {}
  let missMap : Std.HashMap String String := miss.foldl (fun m (n, ns, w) => m.insert s!"{n}|{lvStr ns}" w) {}
  for root in [`Sparkle.Tests.SignalLoopTest.counterLoop, `Sparkle.Tests.SignalLoopTest.shift4Loop, `Sparkle.Tests.SignalLoopTest.counterEnableLoop] do
    let (seen, todo) := Tests.Gen5.PrimResidueKey.reach env root 400000
    unless todo.isEmpty do throwError "{root}: fuel exhausted"
    let mut withRow := 0
    let mut noRow : Array String := #[]
    let mut unknown : Array String := #[]
    for ((n, k), _) in seen.toList do
      let kind := Tests.Gen5.PrimResidueKey.kindOf env n
      if kind == "none" then continue
      let key := s!"{n}|{k}"
      if tmSet.contains key || tySet.contains key then withRow := withRow + 1
      else match missMap.get? key with
        | some w => noRow := noRow.push s!"{n} {k} ({kind}; {w})"
        | none => unknown := unknown.push s!"{n} {k} ({kind}; not in the K1 list)"
    logInfo m!"root {root}: residue keys reached {withRow + noRow.size + unknown.size}: with a row {withRow}, without a row {noRow.size}, outside the K1 list {unknown.size}\n  without a row: {noRow.toList}\n  outside K1: {unknown.toList}"

end Tests.Gen5.PTCorpusCheck

#print axioms Tests.Gen5.PTCorpusCheck.n_k1
