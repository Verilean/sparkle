import Tests.Compiler.ShippingMachineSeqLinkedTest
import Tests.Compiler.ShippingMachineLinkedTest
import Tests.Compiler.ShippingMachineTeleTest
import Tests.Compiler.ShippingPremiseEvalTest
import Tests.Compiler.ShippingDesignSVTest
import Tools.ShippingMachineSeqCommandR
import Tools.ShippingMachineDepthCommandR
import Tools.ShippingMachineComposeRCommand
import Tools.ShippingChildRun
import Tools.ShippingChildLegacy
import Tools.ShippingMachineClosesAtGen

/-! The child-run boundary DERIVED on real compiles (`#machine_design_svR0`).

The source → closed-emitted-texts endpoint whose run boundary is the child
boundary `ChildBnd` (the generic ref laws and the two scoped pre/post
conditions, and the cache invariant in the run's START world) and the
children's reflection facts, in the run's own contexts — no premise about the parent's instances (`BoundaryOf` /
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

-- the derived boundary: the endpoint states `ChildBnd` and the children's
-- reflection in the run's contexts, and NO premise about the parent's
-- instances; existence and all closed runs, `outsCheck` explicit
run_cmd Lean.Elab.Command.liftTermElabM do
  for e in rEndpoints do
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    for c in [``Tools.ShippingChildInv.ChildBnd, ``Tools.ShippingMachineEntry.MachineDefines,
        -- the parent's closing at invariant worlds (not the all-worlds `MachineCloses`)
        ``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingDesignSVBack.outsCheck,
        ``Tools.ShippingDesignSV.designCheck, ``Tools.ShippingDesignSV.DesignSV] do
      unless mentions ty c do throwError "{e}: {c} missing"
    for c in [``Tools.ShippingMachineSeqCommand.BoundaryOf, ``Tools.ShippingMachineCallsLinkedT.InstOfCall,
        ``Tools.ShippingGateChild.MachineRun, ``Tools.ShippingGateChild.GateRun,
        ``Tools.ShippingMachineDepthRun.MachineRunN, ``Tools.ShippingMachineEntry.MachineCloses] do
      if mentions ty c then throwError "{e}: still mentions {c}"
    -- and its proof is built from the derived composition, not the old one
    let some (.thmInfo ti) := (← Lean.getEnv).find? e | throwError "{e}"
    let ships := (ti.value.find? fun x => x.isConstOf (e.getPrefix ++ `machine_ships_hierR)).isSome
    unless ships do throwError "{e}: not built from machine_ships_hierR"
  Lean.logInfo m!"DERIVED BOUNDARY: {rEndpoints.length} endpoints state ChildBnd + the children's reflection, no BoundaryOf / InstOfCall / MachineRun premise"

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
      ``two.machine_composedTRA, ``seqMem.machine_composedTRA] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"DERIVED BOUNDARY AXIOMS: standard only"

/-! ### At depth: children with calls of their own -/

-- `midH` (a machine calling the gate child `rcH`) closes by its own
-- children's reflection: generated BEFORE the depth endpoints, so they use it
set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH

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

/-- Which of `cands` a closing premise `k` (`MachineCloses` / `MachineClosesAt`)
is stated about in `e`, the generated boundary definitions unfolded. -/
partial def closersOf (env : Lean.Environment) (k : Lean.Name) (cands : List Lean.Name)
    (e : Lean.Expr) : List Lean.Name :=
  let here := cands.filter fun c =>
    (e.find? fun x => x.isAppOfArity k 6 && x.getArg! 4 == Lean.toExpr c).isSome
  let below := e.getUsedConstants.toList.flatMap fun n =>
    if (n.toString.splitOn "machineBoundN").length > 1 then
      match env.find? n >>= (·.value?) with
      | some v => closersOf env k cands v
      | none => []
    else []
  (here ++ below).eraseDups

-- the closing premises at depth, by declaration. `MachineClosesAt` replaced
-- the all-worlds `MachineCloses` of every declaration WITH calls (a
-- migration: a weaker premise, not a discharge). DISCHARGED: `midH`'s, by
-- `midH.machine_closes_at` at the contexts and world of the child's own run
-- (its boundary gives `rcH`'s reflection there) — in `grandH` and under
-- `mid2` in `topD2`. What stays: the parents' own (sequential children: B2).
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  let midH := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let cands := [``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1,
    ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH,
    ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2,
    ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2, midH,
    ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH,
    ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt]
  let mut report : Lean.MessageData := m!""
  for (f, n) in [(``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1, 1),
      (``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH, 1),
      (``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2, 2)] do
    let e := f ++ Lean.Name.mkSimple s!"machine_design_svNR{n}"
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    let all := closersOf env ``Tools.ShippingMachineEntry.MachineCloses cands ty
    let at' := closersOf env ``Tools.ShippingChildInv.MachineClosesAt cands ty
    if all.contains midH || at'.contains midH then
      throwError "{e}: midH's closing is still asked ({all}, {at'})"
    if !at'.contains f then throwError "{e}: the parent's own MachineClosesAt is not stated"
    if all.contains f then throwError "{e}: the parent's all-worlds MachineCloses is still asked"
    -- the name separation `midH.machine_closes_at` asks is stated
    if f != ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 &&
        !mentionsDeep env ty ``Lean.Name.toString then
      throwError "{e}: the name-separation obligation of midH is not stated"
    report := report ++ m!"\n  {e}: MachineClosesAt asked of {at'}, all-worlds MachineCloses of {all}"
  Lean.logInfo m!"CLOSING AT DEPTH: midH's closing is discharged in every depth endpoint (midH.machine_closes_at at the child's own contexts); name separation stated.{report}"

-- the instance binding derived at depth: `ChildBnd` and per child its
-- premise (reflection; or every run of its entry satisfying its depth
-- conditions, `MachineRunN`), no premise about the parent's instances
run_cmd Lean.Elab.Command.liftTermElabM do
  for (f, n) in nrEndpoints do
    let e := f ++ Lean.Name.mkSimple s!"machine_design_svNR{n}"
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    for c in [``Tools.ShippingChildInv.ChildBnd, ``Tools.ShippingDesignSVBack.outsCheck,
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
  Lean.logInfo m!"DERIVED BOUNDARY AT DEPTH: mixD1 (two different children), grandH, topD2 — at every level: no BoundaryOf / BoundaryOfN / InstOfCall / BndH / BoundH / GateRun / MachineRun(N/NC) premise; the boundary is ChildBnd and the descendants' reflection facts; decidable premises hold; standard axioms"

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
    unless mentions ty ``Tools.ShippingChildInv.ChildBnd &&
        mentions ty ``Tools.ShippingDesignSV.DesignSV do
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
-- the nested and tele endpoint heads, and two different children
set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested
set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN
set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte
set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix
set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice
set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD
set_option maxHeartbeats 0 in
#machine_design_svHR Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL

def hrDecls : List Lean.Name :=
  [``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller,
   ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
   ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested,
   ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN,
   ``Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte,
   ``Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix,
   ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice,
   ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD,
   ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL]

-- the calls' premise is gone (the trivial `R`), the boundary is `ChildBnd`
-- and the children's `EntryDefines`, in the run's contexts
run_cmd Lean.Elab.Command.liftTermElabM do
  for f in hrDecls do
    let e := f ++ `machine_design_svHR
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    for c in [``Tools.ShippingChildInv.ChildBnd,
        ``Tools.ShippingDesignSVBack.outsCheck, ``Tools.ShippingDesignSV.designCheck,
        ``Tools.ShippingDesignSV.DesignSV] do
      unless mentions ty c do throwError "{e}: {c} missing"
    -- each child's reflection: `EntryDefines` (gate-compiled) or `MachineDefines` (machine route)
    unless mentions ty ``Tools.ShippingInlineSoundness.EntryDefines ||
        mentions ty ``Tools.ShippingMachineEntry.MachineDefines do
      throwError "{e}: no child reflection fact"
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
  Lean.logInfo m!"DERIVED BOUNDARY (COMBINATIONAL): {hrDecls.length} parents (data, nested and tele heads; callerMix with two different children) — ChildBnd + the children's EntryDefines / MachineDefines, no GateRun / MachineRun / BoundH / ChildFn premise; decidable premises hold; standard axioms"

/-! ### The child boundary along the run (`ChildBnd`), checked unfolded

Every derived endpoint states `ChildBnd ctx w` for the world `w` its run of the
entry STARTS in — not a statement about every world — and nothing of the
replaced boundaries (`ChildSynthIs`, `RefIs`, `CacheReads`) remains anywhere,
also inside the children's boundaries. Unfolded, `ChildBnd` is: generic laws
(`RefLaws`: the three refs and Lean's primitives — nothing about the compiler;
the body `bodyRel` and the translator — harness `harnessRel_of`, fuel
recursion, arms, legacy block `legacyRel` — are proved under them), and the start condition `StartW` of that world (the synthesis ref
reads `synthesizeChild`, and the depth reads 0 or the cache satisfies the
invariant). That the entry itself keeps the invariant is no premise: it is
`entry_keeps`, by induction on the synthesis depth. -/

/-- The `ChildBnd` occurrences of `ty`: how many are at the start world of the
endpoint's run (a top-level `RunsTo` binder's world), and whether every other
one is at a world bound inside the statement (a child's premise
`∀ wc, ChildBnd … wc → …`; `forEachExpr` opens such binders as fresh locals,
outside the endpoint's own binders), never at another world of the endpoint. -/
def boundaryWorlds (ty : Lean.Expr) : Lean.MetaM (Nat × Bool) :=
  Lean.Meta.forallTelescope ty fun xs body => do
    let mut starts : Array Lean.Expr := #[]
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo && t.getAppArgs.size == 9 then
        starts := starts.push t.getAppArgs[6]!
    let mut parts : Array Lean.Expr := #[body]
    for x in xs do parts := parts.push (← Lean.Meta.inferType x)
    let found ← IO.mkRef (#[] : Array Lean.Expr)
    for e in parts do
      Lean.Meta.forEachExpr (← Lean.instantiateMVars e) fun y => do
        if y.isAppOfArity ``Tools.ShippingChildInv.ChildBnd 3 then found.modify (·.push y.appArg!)
    let mut n := 0
    let mut ok := true
    for wv in ← found.get do
      if starts.contains wv then n := n + 1
      -- a world of the endpoint's own binders that is not a run's start
      else if xs.contains wv then ok := false
    return (n, ok)

run_cmd Lean.Elab.Command.liftTermElabM do
  let es := rEndpoints ++ hrDecls.map (· ++ `machine_design_svHR) ++
    nrEndpoints.map (fun (f, n) => f ++ Lean.Name.mkSimple s!"machine_design_svNR{n}") ++
    [``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_design_svNR2,
     ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_svNR2,
     ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2.machine_design_svNR3, ``mixDeep.machine_design_svNR2]
  for e in es do
    let ty ← Lean.instantiateMVars (← Lean.Meta.inferType (Lean.mkConst e))
    for old in [`Tools.ShippingChildSynth.ChildSynthIs, `Tools.ShippingChildCache.RefIs,
        `Tools.ShippingChildCache.CacheReads] do
      if mentionsDeep (← Lean.getEnv) ty old then throwError "{e}: still assumes {old}"
    let (n, ok) ← boundaryWorlds ty
    unless n ≥ 1 do throwError "{e}: no ChildBnd at the start world of the endpoint's run"
    unless ok do throwError "{e}: a ChildBnd at a world that is not the run's start"
  -- unfolded, the boundary is the generic laws, the two scoped pre/post
  -- conditions and the invariant of the start world
  let unfoldAt (c : Lean.Name) : Lean.MetaM Lean.Expr := do
    Lean.Meta.forallTelescope (← Lean.Meta.inferType (Lean.mkConst c)) fun xs _ =>
      Lean.Meta.whnfD (Lean.mkAppN (Lean.mkConst c) xs)
  let body ← unfoldAt ``Tools.ShippingChildInv.ChildBnd
  -- ONE law witness, with the start condition by ITS values and the start
  -- world quiet for IT — not laws and a start condition side by side
  for c in [``Tools.ShippingChildInv.RefLaws, ``Tools.ShippingChildInv.StartV,
      ``Tools.ShippingChildInv.RefLaws.quiet] do
    unless mentions body c do throwError "ChildBnd unfolds without {c}"
  for c in [``Tools.ShippingChildInv.ChildLaws, ``Tools.ShippingChildInv.StartW] do
    if mentions body c then throwError "ChildBnd still separates the laws from the world ({c})"
  unless body.isAppOf ``Exists do throwError "ChildBnd is not one witness: {body}"
  -- the diagnostic operations are not generic frame laws: they are the class
  -- `Diag`, whose law is asked in quiet worlds only
  let env ← Lean.getEnv
  for d in [`ppExpr, `ioEprintln, `msgToString, `ioGetStderr, `stderrFlush, `ioHandleMk,
      `ioHandlePutStrLn, `ioHandleFlush, `profLog] do
    if env.contains (``Tools.ShippingChildInv.Framed ++ d) then
      throwError "Framed.{d}: a diagnostic operation is still an unconditional frame law"
    unless env.contains (``Tools.ShippingChildInv.Diag ++ d) do throwError "Diag.{d} missing"
  let fieldTy (f : Lean.Name) : Lean.MetaM Lean.Expr := do
    Lean.Meta.inferType (Lean.mkConst (``Tools.ShippingChildInv.RefLaws ++ f))
  let diagTy ← fieldTy `diag
  unless mentions diagTy ``Tools.ShippingChildInv.Diag &&
      mentions diagTy ``Tools.ShippingChildInv.RefLaws.quiet do
    throwError "RefLaws.diag is not conditioned on quiet"
  let frameTy ← fieldTy `frame
  if mentions frameTy ``Tools.ShippingChildInv.Diag then
    throwError "RefLaws.frame covers a diagnostic operation"
  let laws ← unfoldAt ``Tools.ShippingChildInv.ChildLaws
  for c in [``Tools.ShippingChildInv.RefLaws] do
    unless mentions laws c do throwError "ChildLaws unfolds without {c}"
  -- the body, the harness, the translator and its legacy block are no longer assumed
  for c in [``Tools.ShippingChildInv.BodyRel, ``Tools.ShippingChildInv.HarnessRel,
      ``Tools.ShippingChildInv.TranslateRel, ``Tools.ShippingChildInv.LegacyRel,
      ``Tools.ShippingChildInv.ChildKeeps, ``Tools.ShippingChildInv.Keeps,
      ``Sparkle.Compiler.Elab.synthesizeFromConst, ``Sparkle.Compiler.Elab.translateExprToWire] do
    if mentions laws c then throwError "ChildLaws still assumes {c}"
  -- the (proved) statement about the legacy block is about its two entry
  -- points, relative to the recursive argument
  let lg ← unfoldAt ``Tools.ShippingChildInv.LegacyRel
  for c in [``Sparkle.Compiler.Elab.Rec.translateExprToWireCached,
      ``Sparkle.Compiler.Elab.Rec.translateExprToWireImpl,
      ``Tools.ShippingChildInv.ChildKeeps, ``Tools.ShippingChildInv.KeepsC] do
    unless mentions lg c do throwError "LegacyRel: no {c}"
  -- (the call-key helper is proved now: `canonHardwareKey_keeps`)
  for c in [``Sparkle.Compiler.Elab.translateExprToWire, ``Sparkle.Compiler.Elab.translateFallback,
      ``Sparkle.Compiler.Elab.translateStep, ``Sparkle.Compiler.Elab.canonHardwareKey] do
    if mentions lg c then throwError "LegacyRel mentions {c}"
  -- the two conditions are RELATIVE (their premise is the child entry's
  -- keeping the invariant), about every outcome (`Keeps`, by the end world),
  -- and speak of the entry's own logger only, not of an arbitrary callback
  for (c, ds) in [(``Tools.ShippingChildInv.BodyRel, [``Tools.ShippingChildInv.ChildKeeps,
        ``Tools.ShippingChildInv.Keeps, ``Tools.ShippingChildInv.profLogIO]),
      (``Tools.ShippingChildInv.HarnessRel, [``Tools.ShippingChildInv.ChildKeeps,
        ``Tools.ShippingChildInv.Keeps, ``Tools.ShippingChildInv.profLogIO]),
      (``Tools.ShippingChildInv.TranslateRel, [``Tools.ShippingChildInv.ChildKeeps,
        ``Tools.ShippingChildInv.KeepsC, ``Sparkle.Compiler.Elab.translateExprToWire])] do
    let b ← unfoldAt c
    for d in ds do
      unless mentions b d do throwError "{c}: no {d}"
    if (b.find? fun e => e.isForall && e.bindingDomain!.isArrow &&
        e.bindingDomain!.bindingDomain!.isConstOf ``String).isSome then
      throwError "{c} quantifies over a logger callback"
  unless mentions (← unfoldAt ``Tools.ShippingChildInv.Keeps) ``Tools.ShippingChildInv.endW do
    throwError "Keeps is not about the end world of every outcome"
  -- the entry's keeping the invariant is a theorem from `BodyRel` alone
  let ek ← Lean.Meta.inferType (Lean.mkConst ``Tools.ShippingChildInv.entry_keeps)
  unless mentions ek ``Tools.ShippingChildInv.BodyRel && mentions ek ``Tools.ShippingChildInv.Keeps do
    throwError "entry_keeps: shape"
  if mentions ek ``Tools.ShippingChildInv.HarnessRel || mentions ek ``Tools.ShippingChildInv.ChildKeeps ||
      mentions ek ``Tools.ShippingChildInv.TranslateRel then
    throwError "entry_keeps assumes more than BodyRel"
  -- no law says a ref operation can run: that is proved
  let lawsT ← Lean.Meta.inferType (Lean.mkConst ``Tools.ShippingChildInv.RefLaws.mk)
  if (lawsT.find? fun e => e.isAppOf ``Exists).isSome then throwError "RefLaws has a totality law"
  for name in [``Tools.ShippingChildInv.core_reads_inv, ``Tools.ShippingChildInv.synthesizeChild_inv,
      ``Tools.ShippingChildInv.closeInstsGM_inv, ``Tools.ShippingChildInv.closeInstsM_inv,
      ``Tools.ShippingChildInv.synthesizeFromConst_machine_inv,
      ``Tools.ShippingChildInv.synthesizeMachineCertified_inv,
      ``Tools.ShippingChildInv.machine_children_real, ``Tools.ShippingChildInv.machine_run_of_core,
      ``Tools.ShippingChildInv.inv_clear, ``Tools.ShippingChildInv.cacheInv_insert,
      ``Tools.ShippingChildInv.entry_keeps, ``Tools.ShippingChildInv.child_keeps,
      ``Tools.ShippingChildInv.core_keeps, ``Tools.ShippingChildInv.full_keeps,
      ``Tools.ShippingChildInv.entry_inv, ``Tools.ShippingChildInv.harness_inv,
      ``Tools.ShippingChildInv.Triple.tryFinally, ``Tools.ShippingChildInv.refGet_runs,
      ``Tools.ShippingChildInv.refSet_runs, ``Tools.ShippingChildInv.refModify_runs,
      ``Tools.ShippingChildInv.throwError_not_runs, ``Tools.ShippingChildInv.machine_keeps,
      ``Tools.ShippingChildInv.closeInstsM_keeps, ``Tools.ShippingChildInv.closeInstsGM_keeps,
      ``Tools.ShippingChildInv.harnessRel_of, ``Tools.ShippingChildInv.emitLeaves_tripleC,
      ``Tools.ShippingChildInv.bindMixedCertifiedInputs_tripleC,
      ``Tools.ShippingChildInv.finishSynth_triple,
      ``Tools.ShippingChildInv.translateRel_of_legacy, ``Tools.ShippingChildInv.fallbackRel_of_legacy,
      ``Tools.ShippingChildInv.legacyRel, ``Tools.ShippingChildInv.translateRel,
      ``Tools.ShippingChildInv.bodyRel, ``Tools.ShippingChildInv.body_keeps,
      ``Tools.ShippingChildInv.childKeeps, ``Tools.ShippingChildInv.synthesizeCertified_keeps,
      ``Tools.ShippingChildInv.openRecordInputs_keeps, ``Tools.ShippingChildInv.splitReturnLeaves_keeps,
      ``Tools.ShippingChildInv.bindInputsLegacy_keepsC,
      ``Tools.ShippingChildInv.translateExprToWireImpl_keeps,
      ``Tools.ShippingChildInv.translateExprToWireCached_keeps,
      ``Tools.ShippingChildInv.toIR_keepsC,
      ``Tools.ShippingChildInv.translateRel_of_fallback, ``Tools.ShippingChildInv.fuelFix_keepsC,
      ``Tools.ShippingChildInv.translateStepWith_keepsC, ``Tools.ShippingChildInv.translateCore_keepsC,
      ``Tools.ShippingChildInv.translateFallback_keepsC,
      ``Tools.ShippingChildInv.translateInstanceOrFallback_keepsC,
      ``Tools.ShippingChildInv.translateBoolUncachedWith_keepsC,
      ``Tools.ShippingChildInv.translateCircuitDo2UncachedWith_keepsC,
      ``Tools.ShippingChildInv.translateMemoryUncachedWith_keepsC,
      ``Tools.ShippingChildInv.childSynthEntry_keeps, ``Tools.ShippingChildInv.Keeps.tryCatch,
      ``Tools.ShippingChildInv.canonHardwareKey_keeps, ``Tools.ShippingChildInv.extractNat_keeps,
      ``Tools.ShippingChildInv.inferHWType_keeps, ``Tools.ShippingChildInv.fuelFixM_keepsC,
      ``Tools.ShippingChildInv.Keeps.forIn_range, ``Tools.ShippingChildInv.KeepsC.bindE,
      ``Tools.ShippingChildInv.handleDefinitionUnfold_keeps, ``Tools.ShippingChildInv.handleLoop_keeps,
      ``Tools.ShippingChildInv.translateExprToWireApp_keeps] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"CHILD BOUNDARY ALONG THE RUN: {es.length} derived endpoints state ChildBnd at their run's start world (children's at worlds their premises bind), no ChildSynthIs / RefIs / CacheReads at any level; ChildBnd is ONE law witness with the start condition by its values and the start world quiet for it (∃ L, StartV L w ∧ L.quiet w); the diagnostic operations (Diag) are no generic frame law — RefLaws.diag is asked in quiet worlds only; the body, harness, translator and legacy block are proved under the laws, not assumed. NOT a runtime model: the laws stay assumptions, and Diag.msgToString is still for every message (G5 part 2 open)"

/-! ### The cache on real compiles: repeated, nested, sequential + memory

After a top-level run, every entry of `sparkleChildCache` is what a FRESH
top-level run of the entry on its name returns (the content the invariant
`RealChild` speaks about, observed), the same child called twice is stored
once, and a nested compile stores the grandchild before the child. -/

/-- The cache's entries after a top-level run of `f`, as names and output digests. -/
def cacheAfter (f : Lean.Name) : Lean.MetaM (List (Lean.Name × String)) := do
  discard <| Sparkle.Compiler.Elab.synthesizeCombinational f
  let m ← Sparkle.Compiler.Elab.sparkleChildCache.get
  return (m.toList.map fun (n, (mo, d)) =>
    (n, toString (hash (repr mo).pretty) ++ "/" ++ toString (hash (repr d.modules).pretty))).mergeSort
      (fun a b => a.1.toString ≤ b.1.toString)

run_cmd Lean.Elab.Command.liftTermElabM do
  let cases : List Lean.Name :=
    [ -- the same sequential child called twice
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained,
      -- the same combinational child called twice
      ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice,
      -- a sequential child next to a memory read
      ``seqMem,
      -- nested: a child with calls and its grandchild
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH,
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2]
  for f in cases do
    let entries ← cacheAfter f
    if entries.isEmpty then throwError "{f}: no child cached"
    -- the same name at most once (a hit, not a second insertion)
    unless (entries.map (·.1)).eraseDups.length == entries.length do throwError "{f}: duplicate entries"
    -- each entry is what a fresh top-level run on its name returns
    for (c, dg) in entries do
      let (mo, d) ← Sparkle.Compiler.Elab.synthesizeCombinational c
      let fresh := toString (hash (repr mo).pretty) ++ "/" ++ toString (hash (repr d.modules).pretty)
      unless fresh == dg do throwError "{f}: the cached {c} differs from a fresh run"
    Lean.logInfo m!"{f}: cached {entries.map (·.1)} — each equal to a fresh run"
  -- nested: the grandchild was cached by the child's own run (the inner miss)
  let g ← cacheAfter ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
  unless g.length ≥ 2 do throwError "grandH: the nested compile cached {g.map (·.1)}"
  Lean.logInfo m!"CACHE ON REAL COMPILES: repeated children stored once, nested misses store the grandchild, every entry equals a fresh run"

/-! ### The depth guard

The entry refuses to start at `sparkleSynthDepthLimit` (the measure of the
induction in `entry_keeps`), before changing anything: the depth is left as
it was. Below the limit it runs as before. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained
  let lim := Sparkle.Compiler.Elab.sparkleSynthDepthLimit
  Sparkle.Compiler.Elab.sparkleSynthDepth.set lim
  let r ← try
      discard <| Sparkle.Compiler.Elab.synthesizeCombinational f
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  let after ← Sparkle.Compiler.Elab.sparkleSynthDepth.get
  Sparkle.Compiler.Elab.sparkleSynthDepth.set 0
  match r with
  | none => throwError "the entry ran at the depth limit"
  | some msg =>
    unless (msg.splitOn "depth limit").length > 1 do throwError "failed otherwise: {msg}"
  unless after == lim do throwError "the refused run changed the depth ({after})"
  -- a failing run below the limit restores the depth (the `finally`)
  let bad ← try
      discard <| Sparkle.Compiler.Elab.synthesizeCombinational ``Nat.add
      pure false
    catch _ => pure true
  unless bad do throwError "Nat.add synthesized"
  unless (← Sparkle.Compiler.Elab.sparkleSynthDepth.get) == 0 do
    throwError "a failing run left the depth raised"
  -- and the entry still runs
  discard <| Sparkle.Compiler.Elab.synthesizeCombinational f
  unless (← Sparkle.Compiler.Elab.sparkleSynthDepth.get) == 0 do throwError "depth not restored"
  Lean.logInfo m!"DEPTH GUARD: refused at the limit ({lim}) with the depth untouched; a failing run and a returning run both leave the depth at 0"

/-! No frame law about a caller-supplied action. A `Framed` constructor whose
argument is a stream (`IO.FS.Stream` is a structure of closures) or a function
into a monad of effects states a frame for an ARBITRARY action; with the cache
laws that is a contradiction (it was: `ioFlush (h : IO.FS.Stream)`, removed
2026-10-11 — a stream whose `flush` writes the cache gave `RefLaws → False`).
Checked on every constructor's argument TYPES at the surface. This is NOT a
consistency audit: a structure argument can hide a callback (it does:
`msgToString (m : MessageData)` — `MessageData.ofLazy` holds a `BaseIO`
thunk that rendering runs; and `ppExpr` runs the environment's registered
printers). Those two laws are false of an adversarial message / environment.
They are not refutable in the kernel (`MessageData.formatAux` is `opaque`,
the environment is read from an opaque ref — probe `laws4.lean`), so they do
not make the laws inconsistent the way `ioFlush` did; they are assumptions
about the environment: no registered printer and no thrown message writes the
three refs. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let some (.inductInfo ii) := (← Lean.getEnv).find? ``Tools.ShippingChildInv.Framed
    | throwError "Framed"
  let effect (e : Lean.Expr) : Bool :=
    (e.find? fun x => x.isConstOf ``IO.FS.Stream || x.isConstOf ``EIO || x.isConstOf ``BaseIO ||
      x.isConstOf ``IO || x.isConstOf ``EST || x.isConstOf ``ST || x.isConstOf ``Lean.Meta.MetaM ||
      x.isConstOf ``Lean.Core.CoreM).isSome
  let mut n : Nat := 0
  for c in ii.ctors do
    let t ← Lean.Meta.inferType (Lean.mkConst c [])
    let bad ← Lean.Meta.forallTelescope t fun xs _ => do
      let mut bad := #[]
      for x in xs do
        let ty ← Lean.Meta.inferType x
        if effect ty then bad := bad.push ty
      return bad
    unless bad.isEmpty do
      throwError "{c}: a frame law about a caller-supplied action ({bad})"
    n := n + 1
  Lean.logInfo m!"FRAMED: {n} constructors, none takes a stream or an action as a surface argument (not a consistency audit: msgToString and ppExpr run thunks / registered printers — environment assumptions, kernel-unrefutable since the renderer is opaque); the stderr flush is the named action flushStderr"

end Sparkle.Tests.Compiler.ShippingChildBoundaryTest
