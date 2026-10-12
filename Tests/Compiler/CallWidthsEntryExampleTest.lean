import Tests.Compiler.ShippingMachineLinkedTest
import Tools.ShippingCallWidthsEntry

/-! # ONE example: `callerL → pickByteH` — the data condition `callWidthsStrict`, two ways

`Tests/Compiler/ShippingMachineLinkedTest.lean`: `pickByteH` is a
`@[hardware_module]` with ONE Signal result (`BitVec 8`), a slotless leaf on
the MACHINE route (shared `let`s; `#machine_endpoint pickByteH` exists, so
`pickByteH.machineData` is its reflected reader result); `callerL` is a
state machine (one register) calling it once, result kind `.bits 8`, read by
`machInstance` with `instStruct` untouched — the one-output closing
(`instFields = []`). This is the case the reader lemmas of this line are
about (`docs/parallel/B-readerinv.md` §8: why this pair and not
`caller → pick`, whose child is a GATE, nor `hftByte → httpGetByte`).

* **Way 1** (`callerL_strict_decide`): today's way — one `decide` on the
  two reflected data.
* **Way 2** (`callerL_strict_links`): `callWidthsStrict_of_links`. Decided
  here: `R5ok` (`callerL_r5Ok`) and `R1all` (`callerL_instKinds`). LEFT as
  hypotheses, by name: the reflection links `LinkP`, `LinkC`, the
  generator's count `NIN`, and `ResC` (the result kind of the type of the
  constant the child's shape was read from).
* **Way 2, declared callee** (`callerL_entry_declared`): the same with the
  callee's identity (`callerL_callee`, decided), its signature and constant
  in an environment `env`, and R1 as the reader's invariant `R1At` — all
  hypotheses.

So for this example:

    callWidthsStrict (ONE decide)
      ↦ R5ok (decide) + R1all (decide)
        + LinkP + LinkC   (from MachineDefines under run facts: `link_of_defines`)
        + NIN             (the generator's knowledge; no kernel statement)
        + ResC            (P1 for a declared constant; P5 for the unfolding)

NOT a reduction of the premise list: way 2 has more obligations than way 1,
and two of them (`NIN`, `ResC` for the unfolded entry constant) are provided
by nothing. Nothing here is connected to an endpoint.

The expected data (`insts` kinds `[.bits 8]`, callee `pickByteH`) is read
off the SOURCE, not off the reflected data: a failing `decide` below is a
wrong guess about that data, not a fact about the compiler.

UNVERIFIED: written, not built. -/
namespace Tests.Compiler.CallWidthsEntryExampleTest
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Tools.ShippingMachineAuto
open Tools.ShippingCallWidthsStrict Tools.ShippingCallWidthsDeclared
open Tools.ShippingCallWidthsEntry Tools.ShippingR5Check

/-! ## Way 1 -/

theorem callerL_strict_decide :
    callWidthsStrict callerL.machineData (closingNDecl callerL.machineData.shape)
      (fun _ => pickByteH.machineData.shape.layout.outs) = true := by
  first
    | decide
    | decide +kernel

/-! ## Way 2: the decided parts -/

/-- R5 as data: the binder count of `callerL` at its `nIn`. -/
theorem callerL_r5Ok : callerL.machineData.r5Ok = true := by
  first
    | decide
    | decide +kernel

/-- R1 as data: every call entry of `callerL` has the kind `.bits 8`. -/
theorem callerL_instKinds :
    ∀ kd ∈ callerL.machineData.shape.insts.map (·.2.2), kd = MixedGateBinder.bits 8 := by
  first
    | decide
    | decide +kernel

/-- The callee of entry 0 is `pickByteH`. -/
theorem callerL_callee :
    (callerL.machineData.shape.insts.map (·.1))[0]? = some ``pickByteH := by
  first
    | rfl
    | decide
    | decide +kernel

/-- The one-output closing: no field list. -/
theorem callerL_instFields : callerL.machineData.shape.instFields = [] := by
  first
    | rfl
    | decide

/-! ## Way 2: what is left -/

/-- **`callWidthsStrict` of `callerL` against `pickByteH`'s layout, through
the reader lemmas.** Hypotheses = the obligations way 2 leaves. -/
theorem callerL_strict_links
    {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal} {senvP : StructEnv}
    {allowP : Bool}
    (LinkP : machineShape? symP paramsP (.defnInfo dP) senvP allowP =
      some callerL.machineData.shape)
    (NIN : ∀ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs dP.value) = some (bs, e) →
      callerL.machineData.nIn = bs.length + callerL.machineData.shape.insts.length)
    {dC : DefinitionVal}
    {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv} {allowC : Bool}
    (LinkC : machineShape? symC paramsC (.defnInfo dC) senvC allowC =
      some pickByteH.machineData.shape)
    (ResC : machResultKind? dC.type = some (MixedGateBinder.bits 8)) :
    callWidthsStrict callerL.machineData (closingNDecl callerL.machineData.shape)
      (fun _ => pickByteH.machineData.shape.layout.outs) = true :=
  callWidthsStrict_of_links LinkP NIN callerL_r5Ok LinkC ResC (fun _ _ => rfl)
    callerL_instKinds

/-- **Entry 0, declared callee**: with `pickByteH`'s signature and constant
in `env`, the parent's shape read with `structEnv env`, the child's shape
read from that DECLARED constant, and R1 at entry 0. -/
theorem callerL_entry_declared {env : Environment}
    {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal} {allowP : Bool}
    (LinkP : machineShape? symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some callerL.machineData.shape)
    (NIN : ∀ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs dP.value) = some (bs, e) →
      callerL.machineData.nIn = bs.length + callerL.machineData.shape.insts.length)
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {dC : DefinitionVal}
    {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv} {allowC : Bool}
    (hinst : (structEnv env).inst ``pickByteH = some (kinds, res))
    (hfind : env.find? ``pickByteH = some (.defnInfo dC))
    (LinkC : machineShape? symC paramsC (.defnInfo dC) senvC allowC =
      some pickByteH.machineData.shape)
    (hk : 0 < callerL.machineData.shape.insts.length)
    (R1 : R1At env callerL.machineData.shape 0) :
    entryStrict callerL.machineData (closingNDecl callerL.machineData.shape)
      (fun _ => pickByteH.machineData.shape.layout.outs) 0 = true :=
  entryStrict_of_links_declared LinkP NIN callerL_r5Ok callerL_callee hinst hfind LinkC rfl hk R1

open Lean Elab Command in
run_cmd liftTermElabM do
  let names := [``Tools.ShippingCallWidthsEntry.machineShape?_defn,
    ``Tools.ShippingCallWidthsEntry.link_of_defines,
    ``Tools.ShippingCallWidthsEntry.entryStrict_of_child,
    ``Tools.ShippingCallWidthsEntry.entryStrict_of_links,
    ``Tools.ShippingCallWidthsEntry.callWidthsStrict_of_links,
    ``Tools.ShippingCallWidthsEntry.resC_of_declared,
    ``Tools.ShippingCallWidthsEntry.entryStrict_of_links_declared,
    ``Tools.ShippingR5Check.r5_of_count, ``Tools.ShippingR5Check.count_of_r5,
    ``Tools.ShippingR5Check.r5_of_r5Ok,
    ``callerL_strict_decide, ``callerL_r5Ok, ``callerL_instKinds, ``callerL_callee,
    ``callerL_instFields, ``callerL_strict_links, ``callerL_entry_declared]
  for n in names do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"CALL WIDTHS EXAMPLE callerL → pickByteH: {names.length} theorems; callWidthsStrict by ONE decide (way 1) and through the reader lemmas (way 2) with the hypotheses LinkP, LinkC, NIN, ResC left and R5ok, R1all decided — standard axioms only; NOT a reduction of the premise list; not connected to an endpoint"

end Tests.Compiler.CallWidthsEntryExampleTest
