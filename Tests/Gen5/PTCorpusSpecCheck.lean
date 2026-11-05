import Lean
import Tools.ShippingGen5PTCorpusSpec
import Tests.SignalLoopTest
set_option autoImplicit false
-- D.D-4 Q-C, Spec supply for `PTcorpus` (Issue sparkle-ledger-dd4-deprows). No sorry / axiom / native_decide. The net delta of the ledger is NOT decided here.

/-! # `PTcorpus`: which rows the Specs close

Before: `RowTypedAtV` proved for 32 of the 51 term rows, `RowTeleEvAt` for 10 (`Tests/Gen5/PTCorpusCheck.lean`). Here:
1. the term rows are classified by the theorem that closes `RowTypedAtV` (existing: nullary / closed / DomainConfig / 22 first-argument; new: 19 `ptc_spine_rowTypedV_*`), the count AFTER;
2. the env facts that those theorems take as hypotheses (`¬ IsDefn env D`, `EnvDepSpine`) are evaluated in the real environment, one by one;
3. the 26 keys of `DepRows` have no row in `PTcorpus`: no Spec can be supplied (proved), listed with the reason;
4. `RowTeleEvAt`: unchanged, 10 of 51; the open 41 and the four named obligations (`Fin.mk`, `BitVec.ofFin`, `Decidable.isTrue`, `Decidable.isFalse`) are listed;
5. negative controls; `#print axioms`.

A Spec being stated does not pay a row: a row is counted as closed only when its theorem exists AND its env facts hold in the real environment. -/
open Lean Meta

namespace Tests.Gen5.PTCorpusSpecCheck
open Tools.ShippingGen5PTCorpus Tools.ShippingGen5PTCorpusSpec

def tmKeys : List (Name × List Nat × List Bool) := tmsTable.map fun e => (e.1, e.2.1, e.2.2.1)
def tyKeys : List (Name × List Nat × List Bool) := tysTable.map fun e => (e.1, e.2.1, e.2.2.1)
def missKeys : List (Name × List Nat × String) := missingTable.map fun e => (e.1, e.2.1, reprStr e.2.2)

def lvStr (ns : List Nat) : String := "[" ++ ", ".intercalate (ns.map toString) ++ "]"
def natLevel : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (natLevel n)

/-- The row theorems of the development before this issue (as in `PTCorpusCheck`). -/
def manualRowTypedProved : List Name :=
  [``Nat.zero, ``Bool.false, ``Bool.true, ``PUnit.unit, `Sparkle.Core.Domain.ActiveEdge.rising, `Sparkle.IR.Type.ResetKind.synchronous,
   ``Nat.succ, ``Int.ofNat, ``Int.negSucc, `Sparkle.Core.Domain.DomainConfig.mk]
def manualTeleEvProved : List Name := [``Nat.succ, ``Int.ofNat, ``Int.negSucc, `Sparkle.Core.Domain.DomainConfig.mk]

/-- Decidable evaluation of the env fact `EnvDepSpine`: the instantiated declared type of `c` is `n` binders and then `D Ls` applied to `bvar (n-1), …, bvar (n-m)`. -/
def envDepSpineB (env : Environment) (c : Name) (ls : List Level) (n m : Nat) (D : Name) (Ls : List Level) : Bool :=
  match env.find? c with
  | none => false
  | some ci =>
    let rec go : Nat → Expr → Option Expr
      | 0, e => some e
      | k + 1, .forallE _ _ b _ => go k b
      | _, _ => none
    match go n (ci.type.instantiateLevelParams ci.levelParams ls) with
    | none => false
    | some body => body == mkAppN (.const D Ls) ((spine n m).toArray)

def isDefnB (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _) => true
  | _ => false

def tagOf (n : Name) : String := (n.toString).replace "." "_"

run_meta do
  let env ← getEnv
  let tm ← unsafe evalConst (List (Name × List Nat × List Bool)) ``tmKeys
  let ty ← unsafe evalConst (List (Name × List Nat × List Bool)) ``tyKeys
  let miss ← unsafe evalConst (List (Name × List Nat × String)) ``missKeys
  let axOk (t : Name) : MetaM Unit := do
    unless env.contains t do throwError "{t} missing"
    let ax ← Lean.collectAxioms t
    unless ax.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do throwError "{t}: non-standard axioms {ax}"
  -- 1. classification of the 51 term rows
  let mut before : Array String := #[]
  let mut viaSpine : Array String := #[]
  let mut notClosed : Array String := #[]
  let mut factFail : Array String := #[]
  let mut i := 0
  for (n, ns, ks) in tm do
    let key := s!"{n} {lvStr ns}"
    let dep := env.contains (Name.mkStr `Tools.ShippingGen5PTCorpus s!"ptc_rowTypedV_tm_{i}")
    if dep || manualRowTypedProved.contains n then before := before.push key
    else
      let thm := Name.mkStr `Tools.ShippingGen5PTCorpusSpec s!"ptc_spine_rowTypedV_{tagOf n}"
      if env.contains thm then
        axOk thm
        axOk (Name.mkStr `Tools.ShippingGen5PTCorpusSpec s!"spec_{tagOf n}")
        -- env facts, evaluated in the real environment
        let D : Name := if n == `BitVec.ofFin then `BitVec else n.getPrefix
        let some (_, _, kD) := ty.find? (fun (m, l, _) => m == D && l == ns) | throwError "no type row for {D}"
        let ls := ns.map natLevel
        let ok1 := !isDefnB env D
        let ok2 := envDepSpineB env n ls ks.length kD.length D ls
        if ok1 && ok2 then viaSpine := viaSpine.push key
        else factFail := factFail.push s!"{key} (hnd {ok1}, EnvDepSpine {ok2})"
      else notClosed := notClosed.push key
    i := i + 1
  if before.size != 32 then throwError "before count {before.size} (expected 32)"
  logInfo m!"RowTypedAtV, term rows of PTcorpus: {tm.length}\nBEFORE (PTCorpusCheck): {before.size}/{tm.length}\nAFTER: {before.size + viaSpine.size}/{tm.length}  (= {before.size} + {viaSpine.size} rows closed by `rowTypedAtV_spine` with `SpineSpec` supplied by `spineSpec_of_refines`)\nclosed by the new theorems (env facts verified in the real environment): {viaSpine.toList}\nenv facts that FAILED in the real environment: {factFail.toList}\nnot closed: {notClosed.toList}"
  if viaSpine.size != 19 then throwError "spine rows: {viaSpine.size}"
  unless factFail.isEmpty && notClosed.isEmpty do throwError "env facts / open rows"
  -- 3. the 26 keys of DepRows have no row
  let mut noRow : Array String := #[]
  for c in deprowKeys do
    match miss.find? (fun (m, l, _) => m == c && l.isEmpty) with
    | some (_, _, why) => noRow := noRow.push s!"{c} ({why})"
    | none => throwError "{c}: not in the missing table"
    if tm.any (fun (m, _, _) => m == c) then throwError "{c} has a row"
  axOk ``deprowKeys_noRow
  axOk ``deprows_noFirstArgSpec
  logInfo m!"DepRows keys without a PTcorpus row: {noRow.size}/26 (no FirstArgSpec / DomFieldsSpec can be supplied: `deprows_noFirstArgSpec`); all `notImportable`:\n{"\n".intercalate noRow.toList}"
  -- 4. RowTeleEvAt: unchanged
  let mut teleProved : Array String := #[]
  let mut teleOpen : Array String := #[]
  for (n, ns, ks) in tm do
    let key := s!"{n} {lvStr ns} kinds={ks}"
    if ks.isEmpty || manualTeleEvProved.contains n then teleProved := teleProved.push key else teleOpen := teleOpen.push key
  if teleProved.size != 10 then throwError "RowTeleEvAt proved: {teleProved.size}"
  let four := [``Fin.mk, ``BitVec.ofFin, ``Decidable.isTrue, ``Decidable.isFalse]
  let mut fourRep : Array String := #[]
  for c in four do
    let row := tm.any (fun (m, _, _) => m == c)
    let why := (miss.find? (fun (m, l, _) => m == c && l.isEmpty)).map (·.2.2)
    let obl := env.contains (Name.mkStr `Tools.ShippingGen5DepRows s!"OblTeleEv_{tagOf c}")
    fourRep := fourRep.push s!"{c}: row in PTcorpus {row}; no-row reason {why}; named obligation `OblTeleEv_*` present {obl}"
  logInfo m!"RowTeleEvAt, term rows of PTcorpus: {tm.length}\nBEFORE: {teleProved.size}/{tm.length}; AFTER: {teleProved.size}/{tm.length} (no row of the 41 is closed by this issue); OPEN {teleOpen.size}:\n{"\n".intercalate teleOpen.toList}\nThe 26 `teleEvDep_*` theorems need `DomFieldsSpec` of a row; their keys have no row (above), so they close 0 of the 51. The open 41 are not `(dom) (fields : Signal dom α)` constructors: their binder types mention the earlier type arguments and need `TDenV` of the substituted binder type (a `tdenv_wk` argument under `EnvClosedL`) per key: NOT supplied here.\nThe four named obligations:\n{"\n".intercalate fourRep.toList}"
  -- 5. controls
  let ls3 := [0, 0, 0].map natLevel
  if envDepSpineB env `HAdd.mk ls3 4 2 `HAdd ls3 then throwError "CONTROL: wrong m accepted"
  if envDepSpineB env `HAdd.mk ls3 3 3 `HAdd ls3 then throwError "CONTROL: wrong n accepted"
  if envDepSpineB env `HAdd.mk ls3 4 3 `HMul ls3 then throwError "CONTROL: wrong D accepted"
  unless envDepSpineB env `HAdd.mk ls3 4 3 `HAdd ls3 do throwError "CONTROL: right fact rejected"
  unless isDefnB env `Sparkle.Core.Domain.ResetKind do throwError "CONTROL: Domain.ResetKind should be a definition"
  if envDepSpineB env `Nonexistent.mk [] 1 1 `Nonexistent [] then throwError "CONTROL: missing constant accepted"
  axOk ``control_spineSpec_wrongKinds
  axOk ``rowTypedAtV_spine
  axOk ``instForallS_spine
  axOk ``refines_run
  logInfo m!"CONTROLS ok: wrong m / n / D rejected by the env-fact evaluator, definition key (ResetKind) detected, missing constant rejected; SpineSpec with wrong kinds refuted (`control_spineSpec_wrongKinds`)"

end Tests.Gen5.PTCorpusSpecCheck

#print axioms Tools.ShippingGen5PTCorpusSpec.instForallS_spine
#print axioms Tools.ShippingGen5PTCorpusSpec.rowTypedAtV_spine
#print axioms Tools.ShippingGen5PTCorpusSpec.refines_run
#print axioms Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HAdd_mk
#print axioms Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_Sparkle_Core_Signal_Signal_mk
#print axioms Tools.ShippingGen5PTCorpusSpec.deprows_noFirstArgSpec
#print axioms Tools.ShippingGen5PTCorpusSpec.control_spineSpec_wrongKinds
