import Lean.Elab.Command
import Tests.Compiler.SlotlessParentProbeTest
import Tests.Compiler.NestedFailRestoreTest
import Tests.Compiler.MixDeepOutermostTest
import Tests.Compiler.ShippingMachineMemLinkedTest

/-! # Digests of what the entry returns — a companion probe for TWO trees

WRITTEN, NOT BUILT, NOT RUN (`fix/env-capture-a`). TARGET-ONLY. LOGS ONLY: it
asserts nothing and never throws. It uses no declaration of the
environment-capture unit, so it builds on poc (`80745d94`) and on the
candidate; the integrator runs it on both and DIFFS the `ENVCAPTURE DIGEST`
lines. They must be identical: this is the MEASURED part of "the one entry
returns what the old entry returned" (docs/parallel/M-env-capture-a.md, (d));
it is a comparison on these declarations, not a statement about all inputs.

For each declaration: `synthesizeCombinational f` at depth 0, then

    ENVCAPTURE START <f>                                        (standard error, flushed, before the run)
    ENVCAPTURE DIGEST <f>: returned=<T or F> module=<hash> design=<hash> stmts=<n> insts=<n> modules=<names>

`hash` is the hash of the `repr` of the value, as a string. A declaration
that is not in the environment gives `ENVCAPTURE DIGEST <f>: MISSING`.

The declarations:

* the eight gate-route parents of `SlotlessParentProbeTest` (instance roots
  and cones over instance leaves: the class the unit is for);
* the two legacy-route controls of `NestedFailRestoreTest` (`okW`, `kSD`):
  the calls of `okW` go through the instance arm too;
* a SPREAD taken from the environment itself, so that both trees take the
  same one: every constant tagged `@[hardware_module]` whose name starts
  with `Sparkle.Tests.Compiler` or `Tests.Compiler`, sorted by name, the
  first `SPARKLE_ENVCAPTURE_SPREAD` of them (default 30) — leaves (their own
  entry), machine parents with gate children, memory parents; and the named
  machine parents `mixDeep`, `mid2`, `memCounter`. -/
namespace Tests.Compiler.EnvCaptureDigestProbe
open Lean Meta
open Sparkle.Compiler.Elab

def bs (b : Bool) : String := if b then "T" else "F"

def emit (s : String) : MetaM Unit := do
  IO.eprintln s
  (← IO.getStderr).flush
  logInfo m!"{s}"

/-- The declarations, by name (looked up at run time). -/
def decls : List Name :=
  [`Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentUse,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.wrapAdd,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentMix,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentTwoCalls,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentRepeat,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentCmp,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentNested,
   `Sparkle.Tests.Compiler.SlotlessParentProbeTest.wrapPick,
   `Tests.Compiler.NestedFailRestoreTest.okW,
   `Tests.Compiler.NestedFailRestoreTest.kSD,
   `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep,
   `Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2,
   `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentSeq,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentSeq2,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentUse3,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentHi,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentLo,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentTwo,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentSeqMix,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentPipeSeq,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentProjLeaf,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentProjArg,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentW8,
   `Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.parentW16]

def instCount (m : Sparkle.IR.AST.Module) : Nat :=
  (m.body.filter fun s => match s with
    | .inst .. => true
    | _ => false).length

def digestLine (f : Name) (r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) : String :=
  match r with
  | none => s!"ENVCAPTURE DIGEST {f}: returned=F module=0 design=0 stmts=0 insts=0 modules=[]"
  | some (m, d) =>
    let hm : UInt64 := hash (toString (repr m))
    let hd : UInt64 := hash (toString (repr d))
    s!"ENVCAPTURE DIGEST {f}: returned=T module={hm} design={hd} stmts={m.body.length} insts={instCount m} modules={d.modules.map (·.name)}"

def inTests (n : Name) : Bool :=
  let s := toString n
  s.startsWith "Sparkle.Tests.Compiler." || s.startsWith "Tests.Compiler."

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let k := ((← IO.getEnv "SPARKLE_ENVCAPTURE_SPREAD").bind String.toNat?).getD 30
  let mut tagged : Array Name := #[]
  for (n, _) in env.constants.toList do
    if inTests n && Sparkle.Compiler.isHardwareModule env n then tagged := tagged.push n
  let spread := (tagged.qsort (fun a b => toString a < toString b)).toList.take k
  emit s!"ENVCAPTURE SPREAD: {tagged.size} tagged test declarations, the first {spread.length} taken"
  for f in decls ++ spread.filter (fun n => !decls.contains n) do
    if env.contains f then
      emit s!"ENVCAPTURE START {f}"
      sparkleSynthDepth.set 0
      let r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) ←
        try
          let res ← Sparkle.Compiler.Elab.synthesizeCombinational f
          pure (some res)
        catch _ => pure none
      sparkleSynthDepth.set 0
      emit (digestLine f r)
    else
      emit s!"ENVCAPTURE DIGEST {f}: MISSING"

end Tests.Compiler.EnvCaptureDigestProbe
