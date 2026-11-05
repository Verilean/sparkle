import Lean
import Tools.ShippingGen5DCEntryV
set_option autoImplicit false
-- D.D-7 check (scripts/gen5/DD7_FREEZE.md): telescope walk of the OLD and NEW root theorems; `hno` absent; every new binder listed.

/-! # D.D-7: binder-list comparison

For each pair (old, new) the binders of the two constants are read with `forallTelescope` (name, binder info, pretty-printed type)
and compared with `==`. The result must be exactly the listed removed / added / changed names. NEGATIVE controls: the same
comparison against a list without the exception (without `hno`, without the added rows) must FAIL. -/
open Lean Meta

namespace Tests.Gen5.DD7Check

structure B where
  name : Name
  info : BinderInfo
  ty : String

def binders (c : Name) : MetaM (Array B × String) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs body => do
    let mut out : Array B := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      out := out.push ⟨d.userName, d.binderInfo, toString (← ppExpr d.type)⟩
    return (out, toString (← ppExpr body))

structure Diff where
  removed : List Name
  added : List Name
  changed : List Name
  sameConcl : Bool
  noRaw : Bool

def diff (old new : Name) : MetaM Diff := do
  let (o, oc) ← binders old
  let (n, nc) ← binders new
  return {
    removed := (o.toList.filter fun b => !n.any (·.name == b.name)).map (·.name)
    added := (n.toList.filter fun b => !o.any (·.name == b.name)).map (·.name)
    changed := (o.toList.filter fun b => n.any fun b' => b'.name == b.name && !(b'.info == b.info && b'.ty == b.ty)).map (·.name)
    sameConcl := oc == nc
    noRaw := !(n.any fun b => (b.ty.splitOn "NoRawBelow").length > 1) }

def hasBinder (c nm : Name) : MetaM Bool := do
  let (o, _) ← binders c
  return o.any (·.name == nm)

/-- some binder (named or anonymous arrow premise) of `c` has a `NoRawBelow` type -/
def hasNoRawBinder (c : Name) : MetaM Bool := do
  let (o, _) ← binders c
  return o.any fun b => (b.ty.splitOn "NoRawBelow").length > 1

/-- the type of binder `a` of `c₁` equals the type of binder `b` of `c₂` -/
def sameTy (c₁ : Name) (a : Name) (c₂ : Name) (b : Name) : MetaM Bool := do
  let (o, _) ← binders c₁
  let (n, _) ← binders c₂
  match o.find? (·.name == a), n.find? (·.name == b) with
  | some x, some y => return x.info == y.info && x.ty == y.ty
  | _, _ => return false

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
  let d ← diff old new
  logInfo m!"resetNk: removed {d.removed} added {d.added} changed {d.changed} sameConcl {d.sameConcl} noRawBelowInBinders {!d.noRaw}"
  unless matches' d [`h, `hno] rootsAdded [] true do throwError "resetNk_transportR binder diff unexpected"
  unless ← sameTy old `h new `hpost do throwError "resetNk_transportR: hpost type differs from old h"
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
  let dU ← diff oldU new
  logInfo m!"vs U.coreRun_transport: removed {dU.removed} added {dU.added} changed {dU.changed} sameConcl {dU.sameConcl}"
  -- d : MachineData is replaced by the package p (d := p.d); hins/hf are gone; hdata is the DataOk row
  unless matches' dU [`d, `hins, `hf] [`ι, `dom, `p, `hdata] [`hdef, `hcl] true do
    throwError "coreRun_transportAll vs coreRun_transport binder diff unexpected"
  unless ← sameTy oldU `hpost new `hpost do throwError "hpost differs"
  unless ← sameTy oldU `hS new `hS do throwError "hS differs"
  unless ← sameTy oldU `hr new `hr do throwError "hr differs"
  -- NEGATIVE CONTROLS
  if matches' dU [`d] [`ι, `dom, `p, `hdata] [`hdef, `hcl] true then throwError "NEG4 passed"
  if matches' dU [`d, `hins, `hf] [`ι, `dom, `p] [`hdef, `hcl] true then throwError "NEG5 (hdata not listed) passed"
  if matches' dU [`d, `hins, `hf] [`ι, `dom, `p, `hdata] [] true then throwError "NEG6 passed"

-- (a3) root at `checkedOptimize b`
run_meta do
  let new := `Tools.ShippingGen5DCEntryV.coreRun_transportOpt
  if ← hasBinder new `hno then throwError "NEW coreRun_transportOpt still has hno"
  let (bs, _) ← binders new
  logInfo m!"coreRun_transportOpt binders: {bs.toList.map (·.name)}"
  let (bs, _) ← binders `Tools.ShippingGen5DCEntryV.noRawBelow_checkedOptimize_of_coreRun
  if bs.any (fun b => (b.ty.splitOn "NoRawBelow").length > 1 && b.name != `hdata) then
    throwError "a binder mentions NoRawBelow"

#print axioms Tools.ShippingGen5DCEntryV.noRawBelow_of_coreRunAll
#print axioms Tools.ShippingGen5DCEntryV.resetNk_transportR
#print axioms Tools.ShippingGen5DCEntryV.coreRun_transportAll
#print axioms Tools.ShippingGen5DCEntryV.coreRun_transportOpt

end Tests.Gen5.DD7Check
