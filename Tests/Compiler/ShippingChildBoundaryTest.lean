import Tests.Compiler.ShippingMachineSeqLinkedTest
import Tests.Compiler.ShippingDesignSVTest
import Tools.ShippingMachineSeqCommandR
import Tools.ShippingMachineDepthCommandR
import Tools.ShippingMachineComposeRCommand

/-! The child-run boundary DERIVED on real compiles (`#machine_design_svR0`).

The source → closed-emitted-texts endpoint whose run boundary is the session
boundary `ChildSynthIs` and the children's reflection facts, in the run's own
contexts — no premise about the parent's instances (`BoundaryOf` /
`InstOfCall`). Positive cases: one sequential child (`parent`), the same child
called twice (`chained`), two DIFFERENT sequential children (`two`) and a
sequential child next to a memory read (`seqMem`): for the last two the old
premise `BoundaryOf` is false (each child's premise would need the other
instance to be its run), which the evaluator reports as MISMATCH. -/
namespace Sparkle.Tests.Compiler.ShippingChildBoundaryTest
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

structure AccOut (dom : DomainConfig) where
  s : Signal dom (BitVec 8)
  odd : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (AccOut dom) dom := ⟨⟩

/-- An accumulator: a second, different sequential child. -/
@[hardware_module] def acc {dom : DomainConfig} (x : Signal dom (BitVec 8)) : AccOut dom :=
  circuit do
    let a ← Signal.reg 0#8
    let as := (a : Signal dom (BitVec 8))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 1#8 : Signal dom (BitVec 8)) } : AccOut dom)

/-- Two different sequential children. -/
def two (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let a := acc rs
    r <~ Signal.mux k.hit (a.s + k.n) rs
    return rs

/-- A sequential child next to a memory read. -/
def seqMem (en : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let rd := Signal.memoryComboRead wa wd en wa
    r <~ Signal.mux k.hit (rd + k.n) rs
    return rs

#machine_endpoint two
#machine_endpoint seqMem

set_option maxHeartbeats 0 in
#machine_design_svR0 Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent
set_option maxHeartbeats 0 in
#machine_design_svR0 Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained
set_option maxHeartbeats 0 in
#machine_design_svR0 two
set_option maxHeartbeats 0 in
#machine_design_svR0 seqMem

-- the old route, for comparison: its boundary premise `BoundaryOf` as stated
set_option maxHeartbeats 0 in
#machine_composedTS two
set_option maxHeartbeats 0 in
#machine_ships_hier two
set_option maxHeartbeats 0 in
#machine_composedTS seqMem
set_option maxHeartbeats 0 in
#machine_ships_hier seqMem

def rEndpoints : List Lean.Name :=
  [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_svR0,
   ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained.machine_design_svR0,
   ``two.machine_design_svR0, ``seqMem.machine_design_svR0]

/-- `c` occurs in `e` (a constant, also inside the bodies of local definitions it unfolds to). -/
def mentions (e : Lean.Expr) (c : Lean.Name) : Bool := (e.find? (·.isConstOf c)).isSome

-- the derived boundary: the endpoint states `ChildSynthIs` and the children's
-- reflection in the run's contexts, and NO premise about the parent's
-- instances; existence and all closed runs, `outsCheck` explicit
run_cmd Lean.Elab.Command.liftTermElabM do
  for e in rEndpoints do
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    for c in [``Tools.ShippingChildSynth.ChildSynthIs, ``Tools.ShippingMachineEntry.MachineDefines,
        ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingDesignSVBack.outsCheck,
        ``Tools.ShippingDesignSV.designCheck, ``Tools.ShippingDesignSV.DesignSV] do
      unless mentions ty c do throwError "{e}: {c} missing"
    for c in [``Tools.ShippingMachineSeqCommand.BoundaryOf, ``Tools.ShippingMachineCallsLinkedT.InstOfCall,
        ``Tools.ShippingGateChild.MachineRun, ``Tools.ShippingGateChild.GateRun,
        ``Tools.ShippingMachineDepthRun.MachineRunN] do
      if mentions ty c then throwError "{e}: still mentions {c}"
    -- and its proof is built from the derived composition, not the old one
    let some (.thmInfo ti) := (← Lean.getEnv).find? e | throwError "{e}"
    let ships := (ti.value.find? fun x => x.isConstOf (e.getPrefix ++ `machine_ships_hierR)).isSome
    unless ships do throwError "{e}: not built from machine_ships_hierR"
  Lean.logInfo m!"DERIVED BOUNDARY: {rEndpoints.length} endpoints state ChildSynthIs + the children's reflection, no BoundaryOf / InstOfCall / MachineRun premise"

-- the shipped designs pass the decidable premises the endpoints state
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained, ``two, ``seqMem] do
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless Tools.ShippingHierPremisesBase.shipsHierCheck C b do throwError "{n}: shipsHierCheck"
    unless Tools.ShippingDesignSV.designCheck C 0 o do throwError "{n}: designCheck 0"
    unless Tools.ShippingDesignSVBack.outsCheck C 0 o do throwError "{n}: outsCheck 0"
    unless Tools.ShippingMachineShipsHier.kidsMixed C b.body do throwError "{n}: kidsMixed"
  Lean.logInfo m!"DERIVED BOUNDARY: shipsHierCheck, designCheck 0, outsCheck 0, kidsMixed hold on the four shipped designs"

-- negative: the OLD premise pairs every instance with every sequential
-- child; with two different children, or a child next to a memory, that
-- pairing is false (MISMATCH, not applying); with one child it matches
open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``two, ``seqMem] do
    let v ← evalShipsHierSeq n none
    unless v.traceTag == "TRACE:MISMATCH" && !v.applies do throwError "{n}: {v.tag}\n{v.report}"
  let vp ← evalShipsHierSeq ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent none
  unless vp.traceTag == "TRACE:MATCHED" do throwError "parent: {vp.tag}"
  Lean.logInfo m!"OLD BOUNDARY: false for two / seqMem (MISMATCH), matched for one child"

run_cmd do
  for name in rEndpoints ++ [``two.machine_ships_hierR, ``seqMem.machine_ships_hierR,
      ``two.machine_composedTR, ``seqMem.machine_composedTR] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"DERIVED BOUNDARY AXIOMS: standard only"

/-! ### At depth: children with calls of their own -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 1
set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH 1
set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 2

/-- The constants `e` mentions, unfolding the generated boundary definitions
(`….machineBoundN…`) it refers to. -/
partial def mentionsDeep (env : Lean.Environment) (e : Lean.Expr) (c : Lean.Name) : Bool :=
  mentions e c || (e.getUsedConstants.any fun n =>
    (n.toString.splitOn "machineBoundN").length > 1 &&
      match env.find? n >>= (·.value?) with
      | some v => mentionsDeep env v c
      | none => false)

def nrEndpoints : List (Lean.Name × Nat) :=
  [(``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1, 1),
   (``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, 1),
   (``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, 2)]

-- the instance binding derived at depth: `ChildSynthIs` and per child its
-- premise (reflection; or every run of its entry satisfying its depth
-- conditions, `MachineRunN`), no premise about the parent's instances
run_cmd Lean.Elab.Command.liftTermElabM do
  for (f, n) in nrEndpoints do
    let e := f ++ Lean.Name.mkSimple s!"machine_design_svNR{n}"
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    for c in [``Tools.ShippingChildSynth.ChildSynthIs, ``Tools.ShippingDesignSVBack.outsCheck,
        ``Tools.ShippingDesignSV.designCheck, ``Tools.ShippingDesignSV.DesignSV] do
      unless mentions ty c do throwError "{e}: {c} missing"
    for c in [``Tools.ShippingMachineSeqCommand.BoundaryOf, ``Tools.ShippingMachineDepthCommand.BoundaryOfN,
        ``Tools.ShippingMachineCallsLinkedT.InstOfCall] do
      if mentions ty c then throwError "{e}: still mentions {c}"
      -- and below the top level: the children's own boundaries are derived too
      if mentionsDeep (← Lean.getEnv) ty c then throwError "{e}: a child's boundary mentions {c}"
    for c in [``Tools.ShippingMachineDepthH.BndH, ``Tools.ShippingMachineDepthH.BoundH,
        ``Tools.ShippingGateChild.GateRun, ``Tools.ShippingGateChild.MachineRun,
        ``Tools.ShippingMachineDepthRun.MachineRunN, ``Tools.ShippingMachineDepthRun.MachineRunNC] do
      if mentionsDeep (← Lean.getEnv) ty c then throwError "{e}: the boundary mentions {c}"
    -- the grandchild level: the combinational grandchild `rcH`'s reflection
    unless mentions ty ``Tools.ShippingInlineSoundness.EntryDefines do
      throwError "{e}: no grandchild reflection fact"
    for ax in ← Lean.collectAxioms e do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{e} uses a non-standard axiom: {ax}"
  -- the shipped designs pass the decidable premises at their depth
  for (f, n) in nrEndpoints do
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore f [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational f
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless Tools.ShippingDesignSV.designCheck C n o && Tools.ShippingDesignSVBack.outsCheck C n o &&
        Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body do
      throwError "{f}: a decidable premise fails on the shipped design"
  Lean.logInfo m!"DERIVED BOUNDARY AT DEPTH: mixD1 (two different children), grandH, topD2 — at every level: no BoundaryOf / BoundaryOfN / InstOfCall / BndH / BoundH / GateRun / MachineRun(N/NC) premise; the boundary is ChildSynthIs and the descendants' reflection facts; decidable premises hold; standard axioms"

/-! ### Depth is an upper bound: shallow subtrees under deeper parents -/

open Sparkle.Tests.Compiler.ShippingMachineDepthHTest (midH) in
open Sparkle.Tests.Compiler.ShippingDesignSVTest (mid2) in
/-- A deep branch (`mid2 → midH → rcH`), a shallow one (`midH → rcH`) and a
leaf (`cnt`) under one parent. -/
def mixDeep (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := mid2 en
    let b := midH en
    let c := cnt en
    r <~ Signal.mux a.hit (rs + b.n + c.n) rs
    return rs

#machine_endpoint mixDeep

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH 2
set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 2
set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 3
set_option maxHeartbeats 0 in
#machine_design_svNR mixDeep 2

run_cmd Lean.Elab.Command.liftTermElabM do
  for (f, n) in [(``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, 2),
      (``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1, 2),
      (``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, 3), (``mixDeep, 2)] do
    let e := f ++ Lean.Name.mkSimple s!"machine_design_svNR{n}"
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    for c in [``Tools.ShippingMachineSeqCommand.BoundaryOf, ``Tools.ShippingMachineDepthCommand.BoundaryOfN,
        ``Tools.ShippingMachineCallsLinkedT.InstOfCall, ``Tools.ShippingMachineDepthH.BndH,
        ``Tools.ShippingMachineDepthH.BoundH, ``Tools.ShippingGateChild.GateRun,
        ``Tools.ShippingGateChild.MachineRun, ``Tools.ShippingMachineDepthRun.MachineRunN,
        ``Tools.ShippingMachineDepthRun.MachineRunNC] do
      if mentionsDeep (← Lean.getEnv) ty c then throwError "{e}: the boundary mentions {c}"
    unless mentions ty ``Tools.ShippingChildSynth.ChildSynthIs && mentions ty ``Tools.ShippingDesignSV.DesignSV do
      throwError "{e}: shape"
    for ax in ← Lean.collectAxioms e do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{e} uses a non-standard axiom: {ax}"
    -- the decidable premises at that depth on the shipped design
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore f [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational f
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless Tools.ShippingDesignSV.designCheck C n o && Tools.ShippingDesignSVBack.outsCheck C n o &&
        Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body do
      throwError "{f}: a decidable premise fails at depth {n}"
  -- too shallow: `mixDeep`'s deep branch needs depth 2
  let r ← try
      discard <| Tools.ShippingMachineDepthCommand.generateDesignNR ``mixDeep 1
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  match r with
  | none => throwError "mixDeep at depth 1 was generated"
  | some msg =>
    unless (msg.splitOn "too shallow").length > 1 do throwError "mixDeep at depth 1 failed otherwise: {msg}"
  Lean.logInfo m!"MIXED DEPTH: grandH at 2, mixD1 at 2, topD2 at 3, mixDeep (deep + shallow + leaf) at 2 — derived boundary, decidable premises hold, standard axioms; mixDeep at depth 1 refused"

/-! ### Combinational children (the one-output closing) -/

set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH

def hrDecls : List Lean.Name :=
  [``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller,
   ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH]

-- the calls' premise is gone (the trivial `R`), the boundary is `ChildSynthIs`
-- and the children's `EntryDefines`, in the run's contexts
run_cmd Lean.Elab.Command.liftTermElabM do
  for f in hrDecls do
    let e := f ++ `machine_design_svHR
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    for c in [``Tools.ShippingChildSynth.ChildSynthIs, ``Tools.ShippingInlineSoundness.EntryDefines,
        ``Tools.ShippingDesignSVBack.outsCheck, ``Tools.ShippingDesignSV.designCheck,
        ``Tools.ShippingDesignSV.DesignSV] do
      unless mentions ty c do throwError "{e}: {c} missing"
    for c in [``Tools.ShippingGateChild.GateRun, ``Tools.ShippingGateChild.MachineRun,
        ``Tools.ShippingMachineDepthH.BoundH, ``Tools.ShippingMachineDepthH.BndH,
        ``Tools.ShippingMachineCompose.ChildFn] do
      if mentionsDeep (← Lean.getEnv) ty c then throwError "{e}: still mentions {c}"
    for ax in ← Lean.collectAxioms e do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{e} uses a non-standard axiom: {ax}"
    -- the decidable premises on the shipped design
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore f [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational f
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless Tools.ShippingHierPremises.shipsHierHCheck D.modules b &&
        Tools.ShippingMachineDepthH.kidsComb D.modules o.body &&
        Tools.ShippingDesignSV.designCheck C 0 o && Tools.ShippingDesignSVBack.outsCheck C 0 o do
      throwError "{f}: a decidable premise fails on the shipped design"
  Lean.logInfo m!"DERIVED BOUNDARY (COMBINATIONAL): caller, midH — ChildSynthIs + EntryDefines, no GateRun / MachineRun / BoundH / ChildFn premise; decidable premises hold; standard axioms"

end Sparkle.Tests.Compiler.ShippingChildBoundaryTest
