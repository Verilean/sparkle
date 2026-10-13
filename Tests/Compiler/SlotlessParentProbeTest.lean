import Tests.Compiler.ShippingHierarchySoundnessTest
import Tests.Compiler.GateDesignSweepTest
import Tools.ShippingGateDesignCommand

/-! # Parents WITHOUT a register whose calls are combinational: which route, which endpoints (round par/b-36)

WRITTEN, NOT BUILT. TARGET-ONLY. A MEASUREMENT of classes, not a proof and
not a regression test: `#slotless_parent_probe f` logs, for one declaration,
what the readers say; it asserts nothing and is an error in no case (eight
`SLOTLESSPARENT RESULT` lines are expected in the log).

The declarations are the instance-root / cone-over-instance parents of
`Tests/Compiler/ShippingHierarchySoundnessTest.lean` (BUILT, in
`Tests.AllTests`): `parentUse` (the body IS one call of a combinational
`@[hardware_module]` on its binders), `wrapAdd` (the same at a concrete
domain), `parentMix` (`childAdd a b + a`), `parentTwoCalls`,
`parentRepeat`, `parentCmp` (Bool result), `parentNested` (a call whose
operand is a call) — and one NEW declaration, `wrapPick`: the smallest
parent of a child that HAS a design-level endpoint (`pick.gate_design0`,
BUILT at 0a0a4f71).

For each, logged (each step in its own `try`):

* MACHINE READER: `Tools.ShippingMachineCommand.readMachine f` — reads it
  (slots, call entries, structure fields) or refuses (its message).
  PREDICTED by reading `Sparkle/Compiler/Elab.lean` 5131–5136: REFUSED — a
  body without a slot whose calls are one-output combinational is not a
  machine shape (`n = 0 && !st.insts.isEmpty && !st.instStruct`).
* GATE: on the entry constant (`entryConst`, as `gateDefs` computes it):
  `certifiedShape?`, `mixedCertifiedShape?` WITHOUT the instance predicate
  and WITH it, and which instance disjunct accepts the peeled body
  (`unifiedInstanceRoot` / `hierGateRoot` / `hierInstRoot`). PREDICTED:
  accepted only with the instance predicate.
* `#gate_child`'s reading: `generateGateChild f` in a `try`, the
  environment put back. PREDICTED: REFUSED ("the body is not read as a
  term": the gate's `Term` has no call) — so `#gate_design0` /
  `#gate_design0S` do not apply.
* CONSTANTS: which of `f.machineData`, `f.gateValue`, `f.machine_sound`,
  `f.gate_child`, `f.gate_design0`, `f.gate_design0S`,
  `f.machine_design_comb0` exist. PREDICTED: none — and therefore these
  declarations have NO ROW in the coverage census (`#design_coverage`
  collects declarations with `machineData` or `gateValue` only).
* THE REAL COMPILE: `synthesizeCombinational f` — the number of instance
  statements of the returned module and the names of the design's modules.

What a line means: the class of ONE declaration by the readers of this
environment. It is not a statement about any endpoint. -/
namespace Sparkle.Tests.Compiler.SlotlessParentProbeTest
open Lean Meta Elab Command
open Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineInstTest (pick)

/-- The smallest parent of a child with a design-level endpoint: no
register, the body is one call of the gate-route child `pick`. -/
def wrapPick (sel : Signal defaultDomain (BitVec 2)) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  pick sel x

private def short (s : String) : String :=
  let t := s.replace "\n" " "
  if t.length ≤ 300 then t else String.ofList (t.toList.take 300) ++ " …"

elab "#slotless_parent_probe " d:ident : command => do
  let shown : String := toString d.getId
  IO.eprintln s!"SLOTLESSPARENT START {shown}"
  logInfo m!"SLOTLESSPARENT START {shown}"
  let f? : Option Name ← try
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
      pure (some n)
    catch _ => pure none
  match f? with
  | none =>
    logInfo m!"SLOTLESSPARENT RESULT {shown}: UNRESOLVED"
  | some f =>
    let env ← getEnv
    -- the machine reader
    let reader : String ← try
        let r ← liftTermElabM (Tools.ShippingMachineCommand.readMachine f)
        pure s!"READS it: slots {r.shape.layout.slots.length}, call entries {r.shape.insts.map (·.1)}, structure fields {r.shape.instFields}"
      catch ex =>
        let msg ← ex.toMessageData.toString
        pure s!"REFUSES it: {short msg}"
    logInfo m!"SLOTLESSPARENT {f} MACHINE READER: {reader}"
    -- the gates, on the entry constant
    let gate : String ← try
        let ci0 ← liftCoreM (getConstInfo f)
        let ci := entryConst true false [] ci0 (instancePredicate env) (userInliner env)
          (structEnv env)
        let first : Bool := (certifiedShape? false [] ci).isSome
        let plain : Bool := (mixedCertifiedShape? false [] ci).isSome
        let withI : Bool := (mixedCertifiedShape? false [] ci (instancePredicate env)).isSome
        let roots : String := match ci.value? with
          | none => "no value"
          | some v =>
            match mixedGatePeel v with
            | none => "the value does not peel"
            | some (bs, body) =>
              let kinds := (bs.map (·.2)).toArray
              let isI := instancePredicate env
              let mods := (body.getUsedConstants.filter fun c =>
                Sparkle.Compiler.isHardwareModule env c).toList
              s!"unifiedInstanceRoot {unifiedInstanceRoot isI kinds body}, hierGateRoot {hierGateRoot isI kinds body}, hierInstRoot {hierInstRoot isI kinds body}; @[hardware_module] constants in the body {mods}"
        pure s!"certifiedShape? {first}; mixedCertifiedShape? without the instance predicate {plain}, with it {withI}; {roots}"
      catch ex =>
        let msg ← ex.toMessageData.toString
        pure s!"ERROR {short msg}"
    logInfo m!"SLOTLESSPARENT {f} GATE: {gate}"
    -- `#gate_child`'s reading (the environment is put back)
    let savedEnv ← getEnv
    let savedMsgs := (← get).messages
    let gchild : String ← try
        let n ← Tools.ShippingGateChildCommand.generateGateChild f
        pure s!"GENERATED {n} (then removed again)"
      catch ex =>
        let msg ← ex.toMessageData.toString
        pure s!"REFUSED / FAILED: {short msg}"
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
    logInfo m!"SLOTLESSPARENT {f} #gate_child: {gchild}"
    -- the constants
    let names : List String := ["machineData", "gateValue", "machine_sound", "gate_child",
      "gate_design0", "gate_design0S", "machine_design_comb0"]
    let have_ := names.filter fun s => env.contains (f ++ Name.mkSimple s)
    logInfo m!"SLOTLESSPARENT {f} CONSTANTS: of {names} — present {have_}; a row in the coverage census: {have_.contains "machineData" || have_.contains "gateValue"}"
    -- the real compile
    let comp : String ← try
        let (m, D) ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeCombinational f)
        let insts := (m.body.filter fun st => match st with
          | .inst .. => true
          | _ => false).length
        pure s!"module {m.name}: {m.body.length} statements, {insts} instance statements; design modules {D.modules.map (·.name)}"
      catch ex =>
        let msg ← ex.toMessageData.toString
        pure s!"ERROR {short msg}"
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
    logInfo m!"SLOTLESSPARENT {f} COMPILE: {comp}"
    logInfo m!"SLOTLESSPARENT RESULT {f}: reader [{reader}]; gate [{gate}]; #gate_child [{gchild}]; constants present {have_}; compile [{comp}]. A class by the readers of this environment — not a statement about any endpoint."

end Sparkle.Tests.Compiler.SlotlessParentProbeTest

#slotless_parent_probe Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentUse
#slotless_parent_probe Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.wrapAdd
#slotless_parent_probe Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentMix
#slotless_parent_probe Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentTwoCalls
#slotless_parent_probe Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentRepeat
#slotless_parent_probe Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentCmp
#slotless_parent_probe Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentNested
#slotless_parent_probe Sparkle.Tests.Compiler.SlotlessParentProbeTest.wrapPick
