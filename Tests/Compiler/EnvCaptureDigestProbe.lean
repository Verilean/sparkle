import Lean.Elab.Command
import Tests.Compiler.SlotlessParentProbeTest
import Tests.Compiler.NestedFailRestoreTest

/-! # Digests of what the entry returns for the gate-route parents (a companion probe for BOTH trees)

WRITTEN, NOT BUILT, NOT RUN (`fix/inst-arm-env`). TARGET-ONLY. LOGS ONLY: it
asserts nothing and never throws. It uses no declaration of the proposal, so
it builds on poc (`f1ed620f`) and on the candidate; the integrator runs it on
both and DIFFS the `ENVCAPTURE DIGEST` lines (they must be identical: the
proposal leaves `synthesizeCombinational` — the entry every command uses — a
function of the same term).

For each declaration: `synthesizeCombinational f` at depth 0, then

    ENVCAPTURE START <f>                                        (standard error, flushed, before the run)
    ENVCAPTURE DIGEST <f>: returned=<T or F> module=<hash> design=<hash> stmts=<n> insts=<n> modules=<names>

`hash` is the hash of the `repr` of the value, as a string. A declaration
that is not in the environment gives `ENVCAPTURE DIGEST <f>: MISSING`.

The declarations: the eight parents of `SlotlessParentProbeTest` (instance
roots and cones over instance leaves, the class the proposal is for); and, as
controls, the two legacy-route declarations of `NestedFailRestoreTest`
(`okW`, `kSD`): the calls of `okW` go through the instance arm too. -/
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
   `Tests.Compiler.NestedFailRestoreTest.kSD]

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

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  for f in decls do
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
