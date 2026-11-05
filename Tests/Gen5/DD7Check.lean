import Lean
import Tools.ShippingGen5DCEntryV
set_option autoImplicit false
-- D.D-7 check (scripts/gen5/DD7_FREEZE.md): structural Expr telescope walk (rev 2: types compared with Expr ==, not strings) of the OLD and NEW root theorems; `hno` absent; every new binder listed.

/-! # D.D-7: binder-list comparison

For each pair (old, new) the binders of the two constants are read with `forallTelescope` (name, binder info, type) in ONE walk (`diff`)
and the types compared with structural `Expr` `==`. The result must be exactly the listed removed / added / changed names. NEGATIVE controls: the same
comparison against a list without the exception (without `hno`, without the added rows) must FAIL. -/
open Lean Meta

namespace Tests.Gen5.DD7Check

/-- One walk over the OLD and NEW telescopes. The NEW telescope is opened once; each OLD binder is instantiated with the NEW
free variable of the same name when there is one (and its type compared with `==`, i.e. structural `Expr` equality up to
alpha-equivalence), otherwise with a fresh local (a removed binder). The conclusions are compared with `==` after this
substitution. `pairs` lists (old name, new name) whose instantiated types must be `==` (renamed binders). -/
structure Diff where
  removed : List Name
  added : List Name
  changed : List Name
  sameConcl : Bool
  noRaw : Bool
  pairsOk : List Bool
  deriving Inhabited

partial def walkOld (ys : Array (Name × BinderInfo × Expr × Expr)) :
    Expr → List Name → List Name → List (Name × Expr) → (Expr → List Name → List Name → List (Name × Expr) → MetaM Diff) →
      MetaM Diff
  | .forallE n d b bi, rm, ch, tys, k =>
    match ys.find? (·.1 == n) with
    | some (_, bi', fv, ty') =>
      let ch := if bi == bi' && d == ty' then ch else ch ++ [n]
      walkOld ys (b.instantiate1 fv) rm ch (tys ++ [(n, d)]) k
    | none =>
      withLocalDecl n bi d fun x => walkOld ys (b.instantiate1 x) (rm ++ [n]) ch (tys ++ [(n, d)]) k
  | body, rm, ch, tys, k => k body rm ch tys

def diff (old new : Name) (pairs : List (Name × Name) := []) : MetaM Diff := do
  let oci ← getConstInfo old
  let nci ← getConstInfo new
  forallTelescope nci.type fun xs nbody => do
    let mut ys : Array (Name × BinderInfo × Expr × Expr) := #[]
    for x in xs do
      let dcl ← x.fvarId!.getDecl
      ys := ys.push (dcl.userName, dcl.binderInfo, x, dcl.type)
    let ys' := ys
    walkOld ys' oci.type [] [] [] fun obody rm ch tys => do
      let oldNames := tys.map (·.1)
      let added := (ys'.toList.filter fun y => !oldNames.contains y.1).map (·.1)
      let noRaw := ys'.all fun y => !(y.2.2.2.getUsedConstants.contains ``Tools.ShippingGen5DCEntryR.NoRawBelow)
      let pairsOk := pairs.map fun (a, b) =>
        match tys.find? (·.1 == a), ys'.find? (·.1 == b) with
        | some (_, ta), some (_, _, _, tb) => ta == tb
        | _, _ => false
      return { removed := rm, added, changed := ch, sameConcl := obody == nbody, noRaw, pairsOk }

def hasBinder (c nm : Name) : MetaM Bool := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => xs.anyM fun x => return (← x.fvarId!.getDecl).userName == nm

/-- some binder (named or anonymous arrow premise) of `c` uses `NoRawBelow` (by the constants of its type) -/
def hasNoRawBinder (c : Name) : MetaM Bool := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => xs.anyM fun x => do
    return (← x.fvarId!.getDecl).type.getUsedConstants.contains ``Tools.ShippingGen5DCEntryR.NoRawBelow

def matches' (d : Diff) (rm ad ch : List Name) (concl : Bool) : Bool :=
  d.removed == rm && d.added == ad && d.changed == ch && d.sameConcl == concl && d.noRaw

open Tools.ShippingGen5DCEntryV in
def rootsAdded : List Name :=
  [`ι, `dom, `mref, `cref, `L, `mctx, `cctx, `w, `w1, `declName, `p, `hS, `hr, `hpost, `hdef, `hcl, `hdata]

-- `resetNk_transport` (old, has `hno`) vs `resetNk_transportR` (new)
run_meta do
  let old := `Tools.ShippingGen5DCEntryR.resetNk_transport
  let new := `Tools.ShippingGen5DCEntryV.resetNk_transportR
  unless ← hasBinder old `hno do throwError "OLD resetNk_transport lacks hno (check is vacuous)"
  if ← hasBinder new `hno then throwError "NEW resetNk_transportR still has hno"
  let d ← diff old new [(`h, `hpost), (`h, `hS)]
  logInfo m!"resetNk: removed {d.removed} added {d.added} changed {d.changed} sameConcl {d.sameConcl} noRawBelowInBinders {!d.noRaw}"
  unless matches' d [`h, `hno] rootsAdded [] true do throwError "resetNk_transportR binder diff unexpected"
  unless d.pairsOk == [true, false] do throwError "resetNk_transportR: old h must be == new hpost and != new hS (structural), got {d.pairsOk}"
  -- NEGATIVE CONTROLS (must be rejected)
  if matches' d [`h] rootsAdded [] true then throwError "NEG1: comparison without the hno exception passed"
  if matches' d [`h, `hno] (rootsAdded.drop 1) [] true then throwError "NEG2: comparison missing an added row passed"
  if matches' d [`h, `hno] rootsAdded [] false then throwError "NEG3: wrong conclusion flag passed"

-- `runModuleTG_transport` (old, has the anonymous `NoRawBelow … →` premise) and U `coreRun_transport` vs `coreRun_transportAll` (new)
run_meta do
  let oldT := `Tools.ShippingGen5DCEntryT.runModuleTG_transport
  let oldU := `Tools.ShippingGen5DCEntryU.coreRun_transport
  let new := `Tools.ShippingGen5DCEntryV.coreRun_transportAll
  unless ← hasNoRawBinder oldT do throwError "OLD runModuleTG_transport lacks the NoRawBelow premise (check is vacuous)"
  if ← hasBinder new `hno then throwError "NEW coreRun_transportAll still has hno"
  let dT ← diff oldT new
  logInfo m!"vs runModuleTG_transport: removed {dT.removed} added {dT.added} changed {dT.changed}"
  unless dT.noRaw && !(← hasNoRawBinder new) do throwError "coreRun_transportAll vs runModuleTG_transport unexpected"
  let dU ← diff oldU new [(`hpost, `hpost), (`hS, `hS), (`hr, `hr), (`hS, `hr)]
  logInfo m!"vs U.coreRun_transport: removed {dU.removed} added {dU.added} changed {dU.changed} sameConcl {dU.sameConcl}"
  -- d : MachineData is replaced by the package p (d := p.d); hins/hf are gone; hdata is the DataOk row
  unless matches' dU [`d, `hins, `hf] [`ι, `dom, `p, `hdata] [`hdef, `hcl] true do
    throwError "coreRun_transportAll vs coreRun_transport binder diff unexpected"
  unless dU.pairsOk == [true, true, true, false] do
    throwError "hpost/hS/hr must be == (structural) and the control hS/hr must differ, got {dU.pairsOk}"
  -- NEGATIVE CONTROLS
  if matches' dU [`d] [`ι, `dom, `p, `hdata] [`hdef, `hcl] true then throwError "NEG4 passed"
  if matches' dU [`d, `hins, `hf] [`ι, `dom, `p] [`hdef, `hcl] true then throwError "NEG5 (hdata not listed) passed"
  if matches' dU [`d, `hins, `hf] [`ι, `dom, `p, `hdata] [] true then throwError "NEG6 passed"

-- (a3) root at `checkedOptimize b`
run_meta do
  let new := `Tools.ShippingGen5DCEntryV.coreRun_transportOpt
  if ← hasBinder new `hno then throwError "NEW coreRun_transportOpt still has hno"
  if ← hasNoRawBinder new then throwError "coreRun_transportOpt: a binder uses NoRawBelow"
  if ← hasNoRawBinder `Tools.ShippingGen5DCEntryV.noRawBelow_checkedOptimize_of_coreRun then
    throwError "noRawBelow_checkedOptimize_of_coreRun: a binder uses NoRawBelow"
  -- structural: the (a3) root against coreRun_transportAll differs only in `hdata` (MemParentDataOk vs the disjunction)
  -- and in the conclusion (checkedOptimize b).body vs raw.body
  let dO ← diff `Tools.ShippingGen5DCEntryV.coreRun_transportAll new
  logInfo m!"coreRun_transportOpt vs coreRun_transportAll: removed {dO.removed} added {dO.added} changed {dO.changed} sameConcl {dO.sameConcl}"
  unless matches' dO [] [] [`hdata] false do throwError "coreRun_transportOpt vs coreRun_transportAll unexpected"
  -- NEGATIVE CONTROL: a theorem compared with itself has no difference and the same conclusion
  let dS ← diff new new
  unless matches' dS [] [] [] true do throwError "NEG7: self-comparison is not empty"
  if matches' dO [] [] [] true then throwError "NEG8: (a3) root compared as identical to coreRun_transportAll"

#print axioms Tools.ShippingGen5DCEntryV.noRawBelow_of_coreRunAll
#print axioms Tools.ShippingGen5DCEntryV.resetNk_transportR
#print axioms Tools.ShippingGen5DCEntryV.coreRun_transportAll
#print axioms Tools.ShippingGen5DCEntryV.coreRun_transportOpt

end Tests.Gen5.DD7Check
