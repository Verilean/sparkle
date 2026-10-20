import Tests.Compiler.LeafDeadInitSatTest
import Tools.ShippingLeafDesignClosedCommand
-- BUILT by the integrator: ld1 exit 1 (test helper name), ld2 exit 1 (audit flagged the uniqueness clause's DesignSV run; refined), ld3 exit 0 (608 jobs); the audit factored into `auditDesignClosed` (reused by LeafDesignClosedFamilyTest), lf1 exit 0. Integrator-written.

/-! # dead7: the leaf design endpoint with no checker antecedent

`dead7` (Tests/Compiler/LeafDeadInitTest.lean) is a leaf whose reset-7 register the optimizer removes
(asserted there). `#machine_leaf_entry` adds `dead7.machine_leafKid` / `dead7.machine_closes`;
`#machine_leaf_design_closed` adds `dead7.machine_design_closed` (the generator,
Tools/ShippingLeafDesignClosedCommand.lean). AUDIT (throws): standard axioms; the outer premises are
exactly the run, `MachineDefines`, `ChildBnd`; and NO antecedent anywhere in the statement — walking
every nested `∀`/`→`, including inside `∃` and `∧` — other than the `DesignSV` run quantified by the
uniqueness clause, mentions `seqCheck`, `simpleBody`, `seqStmtOk`,
`seqNames`, `Bounded`, `seedIn`, `slotInit`, `declWidth` or `weS`. -/

#machine_leaf_entry Sparkle.Tests.Compiler.LeafDeadInitTest.dead7
#machine_leaf_design_closed Sparkle.Tests.Compiler.LeafDeadInitTest.dead7

namespace Sparkle.Tests.Compiler.LeafDesignClosedTest
open Lean Elab Command Meta Term

/-- Every antecedent (domain of a non-dependent or dependent `∀` whose domain is a `Prop`),
anywhere in `e` (under `∃`, `∧`, `∨`, lambdas and applications). -/
partial def antecedents (e : Lean.Expr) : MetaM (List Lean.Expr) := do
  match e with
  | .forallE n d b bi =>
    let here ← if (← isProp d) then pure [d] else pure []
    let inD ← antecedents d
    withLocalDecl n bi d fun x => do
      let rest ← antecedents (b.instantiate1 x)
      return here ++ inD ++ rest
  | .lam n d b bi =>
    withLocalDecl n bi d fun x => antecedents (b.instantiate1 x)
  | .app f a => return (← antecedents f) ++ (← antecedents a)
  | .mdata _ e => antecedents e
  | _ => return []

/-- The audit of a `f.machine_design_closed` (THROWS): standard axioms; the
outer premises are exactly the run, `MachineDefines`, `ChildBnd`; no
antecedent anywhere (nested), other than a `DesignSV` run, mentions a checker /
seeding / width constant. Returns (antecedents walked, `DesignSV` runs). -/
def auditDesignClosed (n : Name) : TermElabM (Nat × Nat) := do
  Sparkle.Tests.Compiler.LeafDeadInitTest.stdAx n
  let ty := (← getConstInfo n).type
  -- outer Prop premises
  let outer ← forallTelescope ty fun xs _ => do
    let mut ps : Array Lean.Expr := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then ps := ps.push t
    return ps
  unless outer.size == 3 do throwError "{n}: {outer.size} outer premises, 3 expected"
  let heads := outer.map (·.getAppFn.constName?)
  unless heads.contains (some ``Tools.ShippingEntrySoundness.RunsTo) &&
      heads.contains (some ``Tools.ShippingMachineEntry.MachineDefines) &&
      heads.contains (some ``Tools.ShippingChildInv.ChildBnd) do
    throwError "{n}: outer premises are not the run, MachineDefines, ChildBnd: {heads}"
  -- every antecedent anywhere
  let ants ← antecedents ty
  let bad := [``Tools.SVParser.EmitSem.seqCheck, ``Sparkle.IR.OptCheck.simpleBody,
    ``Sparkle.IR.OptCheck.seqStmtOk, ``Tools.ShippingSeqSVSoundness.seqNames,
    ``Sparkle.IR.Semantics.Bounded, ``Tools.ShippingSeqOptSoundness.seedIn,
    ``Tools.ShippingSatAssemblyS.slotInit, ``Sparkle.IR.RegDedup.declWidth,
    ``Tools.ShippingDesignSV.weS]
  -- the uniqueness clause `∀ envs', DesignSV … envs' → envs' = envsO` legitimately mentions the seeding
  -- and the start state: an antecedent HEADED by `DesignSV` is the run being quantified, not a condition
  let isRun (a : Lean.Expr) : Bool := a.getAppFn.isConstOf ``Tools.ShippingDesignSV.DesignSV
  let runs := ants.filter isRun
  for a in ants.filter (!isRun ·) do
    for c in bad do
      if (a.find? (·.isConstOf c)).isSome then
        throwError "{n}: an antecedent mentions {c}: {a}"
  logInfo m!"LEAFDESIGN AUDIT OK: {n}: standard axioms; outer premises exactly run / MachineDefines / ChildBnd; {ants.length} antecedents walked (nested; {runs.length} are DesignSV runs of the uniqueness clause), no other mentions {bad}"
  return (ants.length, runs.length)

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  discard <| auditDesignClosed ``Sparkle.Tests.Compiler.LeafDeadInitTest.dead7.machine_design_closed

end Sparkle.Tests.Compiler.LeafDesignClosedTest
