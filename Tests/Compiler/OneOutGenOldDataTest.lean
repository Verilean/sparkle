import Tests.Compiler.OneOutFamilyTest

/-! # `#machine_oneout`: the output facts FROM THE READER against the previous data path, on ONE tree (round par/r-5)

WRITTEN, NOT BUILT.

## TARGET-ONLY — never in `Tests/AllTests.lean`

It KEEPS scratch constants `n.oneout_expected` of the five declarations'
parent names. It may be co-imported with `Tests.Compiler.OneOutAnyGenOldDataTest`
(that one keeps the scratch of OTHER parents: `callerL`, `callerLN`,
`hftByte`, `callerMix`), but nothing needs that.

## What is compared

`Tests.Compiler.OneOutFamilyTest` (in `AllTests`) ran the DEFAULT path of
`#machine_oneout` (par/r-5: no `f.oneout_outTy` / `_outScalar` decided; the
six lemmas of the head pass `Tools.ShippingReaderOutsInv.outTy_of_core hcore
entry` and, in `portsRawH`, `hierTypedH`, `designFullH`, `outScalar_of_core
hcore entry`) on `caller`, `callerTwice`, `callerD`, `callerNested`,
`callerRep`. Here the PREVIOUS data path (`#machine_oneout_olddata_try f
"PRESENT"`) runs on the same five in the SAME environment — a different
generator path from the one that made the existing names. Every parent name
the two paths share exists, so `emitOrVerify (keep := true)` re-derives it
under `n.oneout_expected` (kernel-checked, standard axioms), requires the two
TYPES to be `isDefEq` (a definition: also the values) and KEEPS the scratch.
The two names only the old path has (`oneout_outTy`, `oneout_outScalar`) are
GENERATED now. The endpoint exists: its statement rebuilt from the (existing)
lemmas is compared as before — class `PRESENT`.

Asserted after the five runs (an error otherwise), per declaration:

* the 17 shared parent names (10 data lemmas `oneout_{callsOk, slotLen,
  domB, insts, instFields, nomem, slots, outChars, callArgs, entries}`, the
  definition `oneout_kidIns`, the six `machine_{factsH, outsH, portsRawH,
  portsShippedH, hierTypedH, designFullH}`): `n` and `n.oneout_expected`
  exist, the scratch is on standard axioms, the TYPES are `isDefEq`
  (`Lean.Meta.isDefEq`; the number also syntactically equal is logged);
* the six lemmas: the NEW proof's direct constants contain `outTy_of_core`
  and not `f.oneout_outTy`, the OLD (`….oneout_expected`) the reverse; in
  `portsRawH`, `hierTypedH`, `designFullH` likewise `outScalar_of_core` /
  `f.oneout_outScalar`;
* `f.oneout_outTy` / `_outScalar` exist now, standard axioms, with no
  `.oneout_expected` (they did not exist before the old path ran);
* acceptance: compared pairs `= 5 × 17 = 85`, non-zero.

The callees' facts (`c.gate_*`) are re-derived and compared by the old path
too, but dropped (they never read an output fact; several parents share a
callee). -/

set_option maxHeartbeats 0 in
#machine_oneout_olddata_try Sparkle.Tests.Compiler.ShippingMachineInstTest.caller "PRESENT"

set_option maxHeartbeats 0 in
#machine_oneout_olddata_try Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice "PRESENT"

set_option maxHeartbeats 0 in
#machine_oneout_olddata_try Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD "PRESENT"

set_option maxHeartbeats 0 in
#machine_oneout_olddata_try Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested "PRESENT"

set_option maxHeartbeats 0 in
#machine_oneout_olddata_try callerRep "PRESENT"

namespace Tests.Compiler.OneOutGenOldDataTest
open Lean Meta

/-- The data lemmas both paths generate. -/
def dataNames : List String :=
  ["callsOk", "slotLen", "domB", "insts", "instFields", "nomem", "slots", "outChars",
   "callArgs", "entries"]

/-- The six lemmas of the head, and whether each takes `outScalar`. -/
def runNames : List (Name × Bool) :=
  [(`machine_factsH, false), (`machine_outsH, false), (`machine_portsRawH, true),
   (`machine_portsShippedH, false), (`machine_hierTypedH, true),
   (`machine_designFullH, true)]

def direct (n : Name) : MetaM (Array Name) := do
  match (← getEnv).find? n with
  | some (.thmInfo ti) => return ti.value.getUsedConstants
  | _ => throwError "{n}: not a theorem"

/-- The comparison on one declaration; returns (compared pairs, syntactically
equal types among them). -/
def compare (f : Name) : MetaM (Nat × Nat) := do
  let env ← getEnv
  let shared : List Name :=
    (dataNames ++ ["kidIns"]).map (fun s => f ++ Name.mkSimple ("oneout_" ++ s)) ++
      runNames.map (fun p => f ++ p.1)
  let mut count := 0
  let mut syn := 0
  for n in shared do
    let r := n ++ `oneout_expected
    unless env.contains n do throwError "{n}: missing (the family test is not in the imports)"
    unless env.contains r do throwError "{r}: missing — the previous data path did not re-derive {n}"
    Tests.Compiler.OneOutFamilyTest.std r
    let tn := (← getConstInfo n).type
    let tr := (← getConstInfo r).type
    unless ← isDefEq tn tr do
      throwError "{r}: its statement is not that of {n}"
    count := count + 1
    if tn == tr then syn := syn + 1
  let outTyN := f ++ `oneout_outTy
  let outScN := f ++ `oneout_outScalar
  for (s, sc) in runNames do
    let n := f ++ s
    let r := n ++ `oneout_expected
    let uNew ← direct n
    let uOld ← direct r
    unless uNew.contains ``Tools.ShippingReaderOutsInv.outTy_of_core && !uNew.contains outTyN do
      throwError "{n}: expected the NEW path's outTy_of_core (and not {outTyN}): {uNew}"
    unless uOld.contains outTyN && !uOld.contains ``Tools.ShippingReaderOutsInv.outTy_of_core do
      throwError "{r}: expected the PREVIOUS path's {outTyN} (and not outTy_of_core): {uOld}"
    if sc then
      unless uNew.contains ``Tools.ShippingReaderOutsInv.outScalar_of_core &&
          !uNew.contains outScN do
        throwError "{n}: expected outScalar_of_core (and not {outScN}): {uNew}"
      unless uOld.contains outScN &&
          !uOld.contains ``Tools.ShippingReaderOutsInv.outScalar_of_core do
        throwError "{r}: expected {outScN} (and not outScalar_of_core): {uOld}"
  for n in [outTyN, outScN] do
    unless env.contains n do throwError "{n}: missing — the previous data path decides it"
    Tests.Compiler.OneOutFamilyTest.std n
    if env.contains (n ++ `oneout_expected) then
      throwError "{n}: has a scratch — it existed before the previous path ran (the default path decided it)"
  logInfo m!"ONEOUT OLDDATA COMPARE {f}: the previous data path re-derived {count} shared parent names as ….oneout_expected ({syn} of them with syntactically equal types); each isDefEq the one the default path generated; the six lemmas apply outTy_of_core (portsRawH / hierTypedH / designFullH also outScalar_of_core) at hcore, entry (new) / {outTyN}, {outScN} (old); {outTyN} and {outScN} were generated by the OLD path only."
  return (count, syn)

end Tests.Compiler.OneOutGenOldDataTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let fs : List Lean.Name :=
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller,
     ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice,
     ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD,
     ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested,
     ``callerRep]
  let mut total := 0
  let mut syn := 0
  for f in fs do
    let (n, s) ← Tests.Compiler.OneOutGenOldDataTest.compare f
    unless n == 17 do
      throwError "ONEOUT OLDDATA COMPARE {f}: {n} pairs compared, expected 17"
    total := total + n
    syn := syn + s
  unless total == fs.length * 17 && total == 85 && total != 0 do
    throwError "ONEOUT OLDDATA COMPARE: {total} pairs compared, expected 85"
  for n in [``Tools.ShippingReaderOutsInv.outTy_of_core,
      ``Tools.ShippingReaderOutsInv.outScalar_of_core] do
    Tests.Compiler.OneOutFamilyTest.std n
  Lean.logInfo m!"ONEOUT OLDDATA COMPARE: {total} pairs over {fs.length} declarations, all isDefEq ({syn} syntactically equal); per declaration the default path decides 2 output facts fewer (oneout_outTy, oneout_outScalar)."
