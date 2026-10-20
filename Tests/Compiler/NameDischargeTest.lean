import Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest
import Tools.ShippingMemOnlyNames
import Tools.ShippingClosesNames

/-! # Name hypotheses discharged from the injective module names: `mixedMems` (round par/b-29)

WRITTEN, NOT BUILT. Every expectation below is from reading; the `run_cmd`s
THROW where one fails.

## The endpoint

`mixedMems.machine_design_noPortsR0_closed`
(`Tests/Compiler/NoPortsMemOnlyClosedMixedMemsTest.lean`, BUILT, in
`Tests.AllTests`): a memory-only parent with TWO different memory modules.
Its closing `mixedMems_closes` is
`Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData` applied to two
NAME hypotheses proved per declaration:

    mixedMems_sep    -- hsep:    memNameAt d k = memNameAt d k' → one callee
                     --          by names_ne : nameC ≠ nameS  (`decide`: the kernel
                     --          EVALUATES the two module-name strings and compares them)
    mixedMems_parent -- hparent: memNameAt d k ≠ ofDecl ``mixedMems
                     --          by mixedMems_notinC / mixedMems_notinS (`name_not_mem`)

## What this file does

`mixedMems_closesN` is the same closing by
`Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names`, which has
NO name hypothesis: `hsep` and `hparent` follow from "every call entry is a
memory placeholder" (already a field of the built `mixedMems_data`) by
`ofMem_injective` and `ofDecl_ne_ofMem`. `mixedMems_closes_any` states it for
EVERY parent declaration name — the closing does not depend on what the
parent is called.

`mixedMems.machine_design_noPortsR0_closedN` is the open endpoint closed with
`mixedMems_closesN` (the same `closeLast`).

## EXPECTED (asserted below)

| | before (BUILT) | after (this file) |
|---|---|---|
| hypotheses of the general closing theorem that mention `ofDecl` / `ofMem` / `memNameAt` / `Name.toString` | 2 (`hsep`, `hparent` of `machineClosesAt_of_memOnlyData`) | 0 (`machineClosesAt_of_memOnlyData_names`) |
| per-declaration name lemmas under the closing | `names_ne`, `mixedMems_notinC`, `mixedMems_notinS`, `mixedMems_atC`, `mixedMems_atS`, `mixedMems_sep`, `mixedMems_parent` | none |
| `Tools.ShippingNameSep` under the closing | whatever `name_not_mem` chose (LOGGED here: `Enc.not_mem_cons_mem` or `Enc.not_mem_of`) | none |
| proposition binders of the closed endpoint | the run (`RunsTo`), `MachineDefines mixedMems` | THE SAME TWO |
| antecedent under the existentials | `ChildBnd` | THE SAME |
| premises NOT ALLOWED (goal-gap classifier) | 0 | 0 |

So the closed ENDPOINT's premise list does not change — it had no name
binder: its name conditions were decided per declaration inside the
closing's proof. What goes away is that per-declaration decision (two
hypotheses of the general theorem and seven hand lemmas, one of them a
kernel string comparison). The statement of `…_closedN` is asserted
definitionally equal to the built `…_closed`.

The data conditions stay per declaration (`mixedMems_data`,
`mixedMems_closeData`: decided, conditions not reductions), `hout` among
them (no output of the parent starts with `i` — `hfresh`, a port against an
instance name, not a declaration-name condition).

## Also checked: the closing theorems restated about declarations

`Tools/ShippingClosesNames.lean` (`machineClosesAt_of_gateKidsN`,
`…_seqKidsN`, `…_kidsDN`): the number of proposition hypotheses mentioning
`ofDecl`, before and after (3 → 1, 3 → 1, 6 → 2: what is left is `hfresh`,
and for the deep closing the children's interface, whose name table is
`(declsK k).map ofDecl`). No generator uses them in this round.

SCOPE: one declaration (`mixedMems`), depth 0, a memory-only parent; the
general theorem covers every memory-only parent with the built `MemOnlyData`
and `MemOnlyCloseData`. NOT: a memory beside a declaration child, a
generator, the other four memory-only tests (unchanged). -/

namespace Tests.Compiler.NameDischargeTest
open Lean Meta
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Tools.ShippingNameDischarge

/-! ## The pure lemmas, on names the candidate check could not separate -/

-- Finding H's pair: both printed `#ccp.k`; `sepB` is false on it.
example : ofDecl (Name.str Name.anonymous "#ccp.k") ≠
    ofDecl (Name.str (Name.str Name.anonymous "#ccp") "k") :=
  Tools.ShippingModuleName.ofDecl_ne (by decide)

example : ∀ c ∈ [(Name.str Name.anonymous "#ccp.k", ()), (`A.b, ())],
    ofDecl c.1 ≠ ofDecl (Name.str (Name.str Name.anonymous "#ccp") "k") :=
  parent_ne _ _ (by decide)

example : ofDecl `A.b ∉ [`A.c, `B.b, `A.b.c].map (fun n => ofDecl n) :=
  not_mem_map (by decide)

-- a declaration named like a memory module, against memory modules
example : ofDecl (Name.str Name.anonymous "SparkleMem_combo_4_8") ∉
    ([(true, 4, 8), (false, 4, 8)] : List (Bool × Nat × Nat)).map
      (fun p => ofMem p.1 p.2.1 p.2.2) :=
  not_mem_mems _ _

example : ofMem true 4 8 ≠ ofMem false 4 8 :=
  mems_ne (by decide)

/-! ## The closing of `mixedMems` without a name lemma -/

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt mixedMems`**, from the built data only: no name lemma. -/
theorem mixedMems_closesN {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape :=
  Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names
    Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_data
    Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_closeData

set_option maxHeartbeats 4000000 in
/-- The same for EVERY parent declaration name: the closing of a memory-only
shape does not depend on what the parent is called. -/
theorem mixedMems_closes_any (declName : Lean.Name) {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref declName
      (Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machineData).shape :=
  Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names
    Tests.Compiler.NoPortsMemOnlyAtMixedMemsTest.mixedMems_data
    Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_closeData

/-! ## The audit's tools -/

/-- The constants a name condition is written with. -/
def nameConsts : List Name :=
  [``Lean.Name.toString, ``Sparkle.IR.ModuleName.ofDecl, ``Sparkle.IR.ModuleName.ofMem,
   ``Tools.ShippingMemOnlyCloses.memNameAt]

/-- The proposition binders of `thm` that mention one of `consts`, printed. -/
def hypsWith (thm : Name) (consts : List Name) : MetaM (Array String) := do
  let info ← getConstInfo thm
  forallTelescope info.type fun xs _ => do
    let mut acc : Array String := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then
        if (t.find? (fun e => consts.any fun c => e.isConstOf c)).isSome then
          acc := acc.push (toString (← ppExpr t))
    return acc

/-- Is `n` a declaration of the toolchain (not followed by `depsOf`)? -/
def isCore (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let root := (env.header.moduleNames[i.toNat]!).getRoot
    root == `Init || root == `Lean || root == `Std || root == `Lake
  | none => false

/-- Every constant a declaration's statement and PROOF reach, through
theorems and definitions alike (the toolchain's own declarations are
recorded but not followed). -/
partial def depsOf (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then depsOf env rest seen
    else
      let seen := seen.insert n
      if isCore env n then depsOf env rest seen
      else
        match env.find? n with
        | some (.thmInfo ti) =>
          depsOf env (ti.type.getUsedConstants.toList ++ ti.value.getUsedConstants.toList ++ rest)
            seen
        | some (.defnInfo di) =>
          depsOf env (di.type.getUsedConstants.toList ++ di.value.getUsedConstants.toList ++ rest)
            seen
        | some ci => depsOf env (ci.type.getUsedConstants.toList ++ rest) seen
        | none => depsOf env rest seen

/-- The per-declaration name lemmas of the built closing of `mixedMems`. -/
def oldNameLemmas : List Name :=
  [``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.names_ne,
   ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_notinC,
   ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_notinS,
   ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_atC,
   ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_atS,
   ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_sep,
   ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_parent]

/-- The string-level name machinery (`Tools/ShippingNameSep.lean`). -/
def nameSepConsts : List Name :=
  [``Tools.ShippingNameSep.cands, ``Tools.ShippingNameSep.sepB, ``Tools.ShippingNameSep.sep,
   ``Tools.ShippingNameSep.sepFast, ``Tools.ShippingNameSep.Enc.sep_ne,
   ``Tools.ShippingNameSep.Enc.not_mem_of, ``Tools.ShippingNameSep.Enc.fresh_of,
   ``Tools.ShippingNameSep.Enc.not_mem_nil, ``Tools.ShippingNameSep.Enc.not_mem_cons_mem,
   ``Tools.ShippingNameSep.Enc.not_mem_map_of, ``Tools.ShippingNameSep.Enc.hparent_of,
   ``Tools.ShippingNameSep.Enc.hnames_of]

/-- The audit of `mixedMems.machine_design_noPortsR0_closedN` (an error on
any failure); run after the endpoint is added. -/
def audit : MetaM Unit := do
  let env ← Lean.getEnv
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
  let openN := f ++ `machine_design_noPortsR0
  let closed := f ++ `machine_design_noPortsR0_closed
  let closedN := f ++ `machine_design_noPortsR0_closedN
  let clOld := ``Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest.mixedMems_closes
  let clNew := ``Tests.Compiler.NameDischargeTest.mixedMems_closesN
  let genOld := ``Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData
  let genNew := ``Tools.ShippingMemOnlyNames.machineClosesAt_of_memOnlyData_names
  -- (a) standard axioms
  for n in [``Tools.ShippingNameDischarge.names_inj, ``Tools.ShippingNameDischarge.parent_ne,
      ``Tools.ShippingNameDischarge.not_mem_map, ``Tools.ShippingNameDischarge.disjoint_map,
      ``Tools.ShippingNameDischarge.nodup_map, ``Tools.ShippingNameDischarge.parentD_of,
      ``Tools.ShippingNameDischarge.selfD_of, ``Tools.ShippingNameDischarge.disjD_of,
      ``Tools.ShippingNameDischarge.not_mem_mems, ``Tools.ShippingNameDischarge.mem_not_mem_decls,
      ``Tools.ShippingNameDischarge.not_mem_append, ``Tools.ShippingNameDischarge.mems_ne,
      ``Tools.ShippingMemOnlyNames.memModule_name, ``Tools.ShippingMemOnlyNames.memChild_shape,
      ``Tools.ShippingMemOnlyNames.memChild_name_of, ``Tools.ShippingMemOnlyNames.memNameAt_ofMem,
      ``Tools.ShippingMemOnlyNames.memOnly_parent, ``Tools.ShippingMemOnlyNames.memOnly_sep,
      ``Tools.ShippingMemOnlyNames.machineClosesAt_memOnly_names, genNew,
      ``Tools.ShippingClosesNames.machineClosesAt_of_gateKidsN,
      ``Tools.ShippingClosesNames.machineClosesAt_of_seqKidsN,
      ``Tools.ShippingClosesNames.machineClosesAt_of_kidsDN,
      clNew, ``Tests.Compiler.NameDischargeTest.mixedMems_closes_any, closedN] do
    unless env.contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) the general theorem: the name hypotheses, before and after
  let hOld ← hypsWith genOld nameConsts
  let hNew ← hypsWith genNew nameConsts
  Lean.logInfo m!"NAMEDISCHARGE HYPS {genOld}: {hOld.size} name hypotheses — {hOld}"
  Lean.logInfo m!"NAMEDISCHARGE HYPS {genNew}: {hNew.size} name hypotheses — {hNew}"
  unless hOld.size == 2 do
    throwError "{genOld}: {hOld.size} hypotheses mention a name constant, expected 2 (hsep, hparent): {hOld}"
  unless hNew.isEmpty do
    throwError "{genNew}: a hypothesis still mentions a name constant: {hNew}"
  -- the new closing has no proposition premise and concludes the closing of `f`
  let clB ← Tests.Compiler.NoPortsMemSeqMemClosedTest.propBinders (← Lean.getConstInfo clNew).type
  unless clB.isEmpty do throwError "{clNew}: proposition premises {clB}, expected none"
  -- (c) what the two closings rest on (statement and proof, transitively)
  let dOld := depsOf env [clOld] {}
  let dNew := depsOf env [clNew] {}
  Lean.logInfo m!"NAMEDISCHARGE DEPS: {clOld} reaches {dOld.size} constants, {clNew} reaches {dNew.size}"
  for n in oldNameLemmas ++ nameSepConsts do
    unless env.contains n do throwError "the audit's list is stale: {n}"
  -- the audit SEES the name lemmas under the built closing …
  for n in oldNameLemmas do
    unless dOld.contains n do
      throwError "{clOld} does not reach {n}: the audit does not see what it is meant to (or the inventory is wrong)"
  for n in [``Tools.ShippingMemCloses.machineClosesAt_of_kidsDM,
      ``Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly] do
    unless dOld.contains n && dNew.contains n do
      throwError "one of the closings does not reach {n}: the traversal is too shallow"
  let sepOld := nameSepConsts.filter dOld.contains
  Lean.logInfo m!"NAMEDISCHARGE MEASURED: under {clOld}, Tools.ShippingNameSep constants reached: {sepOld} (Enc.not_mem_cons_mem = name_not_mem took the structural branch; Enc.not_mem_of = the kernel evaluated ofDecl)"
  -- … and none under the new one
  for n in oldNameLemmas ++ nameSepConsts do
    if dNew.contains n then
      throwError "{clNew} still rests on {n}"
  for n in [``Tools.ShippingModuleName.ofMem_injective, ``Tools.ShippingModuleName.ofDecl_ne_ofMem,
      ``Tools.ShippingMemOnlyNames.memOnly_sep, ``Tools.ShippingMemOnlyNames.memOnly_parent] do
    unless dNew.contains n do throwError "{clNew} does not reach {n} (expected: the general lemmas)"
  -- (d) the closed endpoint: the built statement, the same premise list
  let tC := (← Lean.getConstInfo closed).type
  let tN := (← Lean.getConstInfo closedN).type
  unless ← isDefEq tN tC do
    throwError "{closedN}: its statement is not the statement of {closed}"
  let bN ← Tests.Compiler.NoPortsMemSeqMemClosedTest.propBinders tN
  Lean.logInfo m!"NAMEDISCHARGE BINDERS {closedN}: {bN}"
  let headsOk ← Tests.Compiler.NoPortsMemOnlyClosed.allPropsOk tN f
    [``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingMachineEntry.MachineDefines]
  unless headsOk do
    throwError "{closedN}: its proposition binders are not (RunsTo …, MachineDefines … {f} …): {bN}"
  if (tN.find? (fun e => e.isConstOf ``Lean.Name.toString ||
      e.isConstOf ``Tools.ShippingMemOnlyCloses.memNameAt ||
      e.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closedN}: the statement writes a name condition or asks MachineClosesAt"
  let inner ← forallTelescope tN fun _ body => Tests.Compiler.NoPortsTest.innerAntecedents body
  unless inner.size == 1 && inner[0]!.2 do
    throwError "{closedN}: expected ONE allowed antecedent under the existentials: {inner.map (·.1)}"
  unless (tN.find? (·.isConstOf ``Tools.ShippingChildInv.ChildBnd)).isSome do
    throwError "{closedN}: does not mention ChildBnd"
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closedN
  let (linesC, badC) ← Tests.Compiler.NoPortsTest.premiseLines closed
  let (linesO, badO) ← Tests.Compiler.NoPortsTest.premiseLines openN
  Lean.logInfo m!"NAMEDISCHARGE PREMISES {closedN}:\n{String.intercalate "\n" lines.toList}"
  unless bad.isEmpty && badC.isEmpty do
    throwError "{closedN}: premises NOT ALLOWED: {bad} (built closed form: {badC})"
  -- each line starts with the endpoint's own name: compare with that label replaced
  unless lines.map (·.replace (toString closedN) (toString closed)) == linesC do
    throwError "{closedN}: its premise list differs from {closed}'s:\n{lines}\nvs\n{linesC}"
  unless badO.size == 1 && lines.size + 1 == linesO.size do
    throwError "{openN}: {badO.size} NOT ALLOWED, {linesO.size} lines against {lines.size} (expected 1, and one more)"
  -- (e) the closing theorems restated about declarations: hypotheses mentioning ofDecl
  let od := [``Sparkle.IR.ModuleName.ofDecl]
  for (old, new, nOld, nNew) in
      [(``Tools.ShippingCallsGate.machineClosesAt_of_gateKids,
        ``Tools.ShippingClosesNames.machineClosesAt_of_gateKidsN, 3, 1),
       (``Tools.ShippingCallsSeqKids.machineClosesAt_of_seqKids,
        ``Tools.ShippingClosesNames.machineClosesAt_of_seqKidsN, 3, 1),
       (``Tools.ShippingCallsKidsD.machineClosesAt_of_kidsD,
        ``Tools.ShippingClosesNames.machineClosesAt_of_kidsDN, 6, 2)] do
    let a ← hypsWith old od
    let b ← hypsWith new od
    Lean.logInfo m!"NAMEDISCHARGE HYPS {old}: {a.size} mention ofDecl; {new}: {b.size} — {b}"
    unless a.size == nOld && b.size == nNew do
      throwError "{old} / {new}: {a.size} / {b.size} hypotheses mention ofDecl, expected {nOld} / {nNew}:\n{a}\nvs\n{b}"
  Lean.logInfo m!"NAMEDISCHARGE AUDIT {f}: {closedN} is the statement of the built {closed} (two proposition binders: the run, MachineDefines {f}; one antecedent: ChildBnd; {lines.size} premises listed, 0 NOT ALLOWED), on standard axioms, and its closing {clNew} rests on none of the per-declaration name lemmas {oldNameLemmas} nor on Tools.ShippingNameSep: the general theorem {genNew} has NO hypothesis mentioning ofDecl / ofMem / memNameAt / Name.toString, where {genOld} has two (hsep, hparent). The endpoint's premise list is UNCHANGED (it had no name binder); what is gone is the per-declaration decision of the two name hypotheses. SCOPE: one declaration, a memory-only parent, depth 0; data conditions decided per declaration (hout — no output starts with i — among them: a port against an instance name, not a declaration-name condition); the run, the reflection of {f} and ChildBnd remain premises; DesignSV of the module list, not the SV string, not #sim. NOT covered: a memory beside a declaration child, any generator, the other memory-only tests (unchanged)."

end Tests.Compiler.NameDischargeTest

/-! ## The closed endpoint, by the new closing -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
  let closedN := f ++ `machine_design_noPortsR0_closedN
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsMemSeqMemClosedTest.closeLast f (f ++ `machine_design_noPortsR0)
      ``Tests.Compiler.NameDischargeTest.mixedMems_closesN closedN
  Lean.logInfo m!"NAMEDISCHARGE [{closedN}]: {f}.machine_design_noPortsR0 with its binder MachineClosesAt {f} discharged by mixedMems_closesN (machineClosesAt_of_memOnlyData_names: no name hypothesis, no per-declaration name lemma)"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM Tests.Compiler.NameDischargeTest.audit
