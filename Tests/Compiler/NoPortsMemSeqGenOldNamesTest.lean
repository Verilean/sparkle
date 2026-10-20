import Tests.Compiler.NoPortsMemSeqGenNewTest

/-! # `#machine_no_ports_memseq`: the name lemmas by the general lemmas, against the previous proofs, on ONE tree (round par/b-30)

WRITTEN, NOT BUILT. TARGET-ONLY by default (it adds only `…_regen` names of
`seqTwoMem`, so it clashes with nothing; it is kept out of `AllTests` because
it rebuilds a whole endpoint a second time).

`Tests.Compiler.NoPortsMemSeqGenNewTest` generated the endpoints of
`seqTwoMem` (two leaf callees `cnt`, `acc`; two memory placeholders) with the
DEFAULT path: the name lemmas `seqTwoMem.noPortsMemSeq_notinP{j}`,
`…_leafNotin{i}_{j}`, `…_leafNeParent{i}`, `…_leafNe0_1`, `…_memNe0_1` proved
by `Tools.ShippingMemSeqNames` / `Tools.ShippingModuleName.ofDecl_ne`.

Here the command runs again on `seqTwoMem` with
`shipping.nameCandidates := true` (the previous proofs: `name_not_mem`,
`Enc.sep_ne` on the candidate renderings, a kernel string comparison for
`memNe`). Every name exists, so the command takes its compare path on EVERY
generated name: the declaration is elaborated again under `…_regen`
(kernel-checked) and its statement (a table: its value) must be `isDefEq`
the existing one — or the command fails. Expected class: `REBUILT`.

Asserted afterwards (an error otherwise): for each name lemma and for the two
endpoints the `…_regen` exists, on standard axioms, with an `isDefEq`
statement (kernel `isDefEq` of the two types — not a hash); `leafNe0_1`
applies `ofDecl_ne` and its `_regen` applies `Enc.sep_ne`; `memNe0_1` applies
`memName_ne` and its `_regen` does not; `notinP0` applies
`decl_not_mem_memName`. -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option shipping.nameCandidates true in
#machine_no_ports_memseq_try Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem "REBUILT"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem
  let env ← Lean.getEnv
  let direct (n : Lean.Name) : Lean.MetaM (Array Lean.Name) := do
    match (← Lean.getEnv).find? n with
    | some (.thmInfo ti) => return ti.value.getUsedConstants
    | _ => throwError "{n}: not a theorem"
  let nameLemmas : List String :=
    ["notinP0", "notinP1", "leafNotin0_0", "leafNotin0_1", "leafNotin1_0", "leafNotin1_1",
     "leafNeParent0", "leafNeParent1", "leafNe0_1", "memNe0_1"]
  let names := (nameLemmas ++ ["sep", "parent", "parentD", "disj", "closes"]).map
      (fun s => "noPortsMemSeq_" ++ s) ++
    ["machine_design_noPortsR0", "machine_design_noPortsR0_closed"]
  for s in names do
    let a := f ++ Lean.Name.mkSimple s
    let r := f ++ Lean.Name.mkSimple (s ++ "_regen")
    unless env.contains a do throwError "{a}: missing"
    unless env.contains r do throwError "{r}: missing — the previous path did not rebuild {a}"
    Tests.Compiler.NoPortsTest.stdAxioms r
    unless ← Lean.Meta.isDefEq (← Lean.getConstInfo a).type (← Lean.getConstInfo r).type do
      throwError "{r}: its statement is not that of {a}"
  let lem (s : String) : Lean.Name := f ++ Lean.Name.mkSimple ("noPortsMemSeq_" ++ s)
  let uNe ← direct (lem "leafNe0_1")
  let uNeR ← direct (lem "leafNe0_1_regen")
  unless uNe.contains ``Tools.ShippingModuleName.ofDecl_ne &&
      !uNe.contains ``Tools.ShippingNameSep.Enc.sep_ne do
    throwError "leafNe0_1: expected ofDecl_ne, found {uNe}"
  unless uNeR.contains ``Tools.ShippingNameSep.Enc.sep_ne do
    throwError "leafNe0_1_regen: expected Enc.sep_ne, found {uNeR}"
  let uMem ← direct (lem "memNe0_1")
  let uMemR ← direct (lem "memNe0_1_regen")
  unless uMem.contains ``Tools.ShippingMemSeqNames.memName_ne do
    throwError "memNe0_1: expected memName_ne, found {uMem}"
  if uMemR.contains ``Tools.ShippingMemSeqNames.memName_ne then
    throwError "memNe0_1_regen: the previous path was not taken: {uMemR}"
  let uNot ← direct (lem "notinP0")
  unless uNot.contains ``Tools.ShippingMemSeqNames.decl_not_mem_memName do
    throwError "notinP0: expected decl_not_mem_memName, found {uNot}"
  let uNotR ← direct (lem "notinP0_regen")
  Lean.logInfo m!"NOPORTS MEMSEQ OLDNAMES COMPARE {f}: the previous path (shipping.nameCandidates) rebuilt every generated name as …_regen; for {names} the rebuilt statement isDefEq the one the default path generated (kernel isDefEq of the types), standard axioms. Proofs: leafNe0_1 by ofDecl_ne (decide on Lean.Name) against Enc.sep_ne (candidate renderings); memNe0_1 by memName_ne (decide on the parameters) against a decided string comparison; notinP0 by decl_not_mem_memName against name_not_mem (MEASURED here — the previous notinP0's direct constants: {uNotR}). NAMES and TYPES unchanged; only proofs differ."
