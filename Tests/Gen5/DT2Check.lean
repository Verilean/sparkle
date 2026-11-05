import Lean
import Tools.ShippingGen5Flow1Tie
set_option autoImplicit false
-- D.T-2 check (scripts/gen5/DT2_NOTE.md): the CallTie roots take no `CallOutRange` binder; the old `callTie_of_served` does.

/-! # D.T-2: `CallOutRange` is not a binder of the CallTie roots

For each constant the binders are read with `forallTelescope`; a binder "mentions" a constant when that constant is among
`Expr.getUsedConstants` of its (instantiated) type. The roots must mention neither `CallOutRange` nor `CallOutWidthAt`;
the old `callTie_of_served` (control) must mention `CallOutRange`. The binder names of each root are printed so that the
note can map each of them to an existing ledger row. -/
open Lean Meta

namespace Tests.Gen5.DT2Check

def bindersMentioning (c target : Name) : MetaM (List Name) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => do
    let mut out : List Name := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      let ty ← instantiateMVars d.type
      if ty.getUsedConstants.contains target then out := out ++ [d.userName]
    return out

def binderNames (c : Name) : MetaM (List Name) := do
  let ci ← getConstInfo c
  forallTelescope ci.type fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getDecl).userName

def roots : List Name :=
  [``Tools.ShippingGen5Flow1Tie.callTie_of_run_one_ex,
   ``Tools.ShippingGen5Flow1Tie.callTie_of_run_group_kidW,
   ``Tools.ShippingGen2.callTie_of_served_oneOut_t1ND,
   ``Tools.ShippingGen2.callTie_of_served_kidW_closing_t1ND]

run_meta do
  -- control: the old root takes the range row
  let old ← bindersMentioning ``Tools.ShippingGen2.callTie_of_served ``Tools.ShippingGen2.CallOutRange
  unless old == [`hDG_SEM_range] do throwError "CONTROL: callTie_of_served should take exactly hDG_SEM_range, got {old}"
  logInfo m!"CONTROL callTie_of_served CallOutRange binders: {old}"
  let mut n : Nat := 0
  for r in roots do
    let a ← bindersMentioning r ``Tools.ShippingGen2.CallOutRange
    let b ← bindersMentioning r ``Tools.ShippingGen2.CallOutWidthAt
    unless a.isEmpty && b.isEmpty do throwError "{r}: binder mentions CallOutRange/CallOutWidthAt: {a} {b}"
    let ci ← getConstInfo r
    unless (← forallTelescope ci.type fun _ body => return body.getUsedConstants.contains ``Tools.ShippingGen2.CallTie) do
      throwError "{r}: conclusion is not a CallTie statement"
    logInfo m!"ROOT {r} binders: {← binderNames r}"
    n := n + 1
  logInfo m!"DT2 COUNTS: roots {n} without CallOutRange binder, control 1"

#print axioms Tools.ShippingGen5Flow1Tie.callTie_of_run_one_ex
#print axioms Tools.ShippingGen5Flow1Tie.callTie_of_run_group_kidW
#print axioms Tools.ShippingGen2.callTie_of_served_oneOut_t1ND
#print axioms Tools.ShippingGen2.callTie_of_served_kidW_closing_t1ND

end Tests.Gen5.DT2Check
