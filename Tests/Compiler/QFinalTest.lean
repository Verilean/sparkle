import Tests.Compiler.QComposedTest
import Tests.Compiler.QHCallsTest
import Tests.Compiler.Srm33EndpointTest
set_option autoImplicit false
set_option Elab.async false
-- C5 FINAL (issue sparkle-gen-c5-assembly; integration kjob/c5-int).
-- (1) `qSharedLeaf_ships : FrozenC5`: the frozen C5 statement (scripts/c5/C5_STATEMENT.lean.txt, elaborated as QDef.FrozenC5), with NO
--     hypothesis: QComposed.qSharedLeaf_ships_of_hcalls with its one staged hypothesis supplied by QHCalls.hcalls_of_classQ.
-- (2) topshareQ_hierC_noHstR (Srm33EndpointTest) recovered with its EXACT type from qSharedLeaf_ships (P_Q hgrp): TqBnd supplies the
--     contract binders and TqGrp; hcl / TqHcallsP / TqFQ / kidsMaskedN are unused (derived inside the generic theorem).
-- (3) G-MASK for the Q class: kidsMasked_of_class audited, topshareQ_kidsMasked recovered with its exact type.
-- (4) audits: full type and full binder list against FrozenC5, closure walk, axioms.
-- SCOPE: the Q-shape class only. No production change; not G3.
namespace Tests.Compiler.QFinal
open Tests.Compiler.CDef Tests.Compiler.QDef Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.Srm9ComposedTest

/-- **C5**: the frozen Q statement, no hypothesis -/
theorem qSharedLeaf_ships : FrozenC5 := fun P =>
  Tests.Compiler.QComposed.qSharedLeaf_ships_of_hcalls P
    (fun w hw m design => Tests.Compiler.QHCalls.hcalls_of_classQ P w hw m design)

/-- **topshareQ recovered**: exactly the type of the instance endpoint, from the generic C5 theorem -/
theorem topshareQ_hierC_of_class : type_of% @Tests.Compiler.Srm33EndpointTest.topshareQ_hierC_noHstR := by
  intro mctx mref cctx cref w w1 b raw D hcore hpost entry _ hB _
  obtain ⟨O, T, hA, hR0, _, entry₁, entry₂, _, _, hgrp, hw⟩ := hB
  exact qSharedLeaf_ships (P_Q hgrp) O T hA hR0 (Tests.Compiler.QCloses.P_Q_entryW hgrp entry₁ entry₂) entry hw hcore hpost

/-- G-MASK projection: the instance's kidsMaskedN theorem with its exact type (plus TqGrp to form P_Q), from the generic one -/
theorem topshareQ_kidsMasked_of_class (hgrp : TqGrp) : type_of% @Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_kidsMasked := by
  intro mctx mref cctx cref O T hA hR0 _ entry₁ entry₂ entry w w1 raw b D hcore hpost hw
  exact Tests.Compiler.QShips.kidsMasked_of_class (P_Q hgrp) O T hA hR0
    (Tests.Compiler.QCloses.P_Q_entryW hgrp entry₁ entry₂) entry hcore hpost hw

open Lean Meta in
/-- closure walk from a root: every `Tests.*` constant reached (bodies read from thmInfo / defnInfo) -/
def closureOf (root : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut work : List Name := [root]
  let mut reached : Array Name := #[]
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "QFINAL CLOSURE FAILED: {n} not found"
    let body? : Option Lean.Expr := match ci with
      | .thmInfo t => some t.value
      | .defnInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    for c in ci.type.getUsedConstants ++ (body?.map Lean.Expr.getUsedConstants).getD #[] do
      if (c.toString.splitOn "Tests.").length > 1 && !seen.contains c && !reached.contains c then
        reached := reached.push c
        work := c :: work
  return reached

open Lean Meta in
def checkGeneric (root : Name) (okPfx : List String) : MetaM Nat := do
  let reached ← closureOf root
  for c in reached do
    unless okPfx.any (fun p => (c.toString.splitOn p).length > 1) do
      throwError "QFINAL CLOSURE FAILED: {root} reaches {c} (outside the class definition and the generic C5 files)"
    for comp in c.components.map (·.toString) do
      if ["P_Q", "P_M", "wrapP", "wrapQ", "leafP", "wrapM", "wrapM3", "leafM", "qLeafP", "wrapPPkg", "wrapQPkg", "wrapPDat", "wrapQDat"].contains comp
          || comp.startsWith "topshare" || comp.startsWith "Tq" || comp.startsWith "Tm" then
        throwError "QFINAL CLOSURE FAILED: {root} reaches {c} (instance component {comp})"
  return reached.size

open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- (1) the final theorem: type, full binder list of the unfolded frozen statement
  let ci ← getConstInfo ``qSharedLeaf_ships
  let fz ← getConstInfo ``FrozenC5
  let some fv := fz.value? | throwError "QFINAL AUDIT FAILED: FrozenC5 has no value"
  unless ← isDefEq ci.type (mkConst ``FrozenC5) do throwError "QFINAL AUDIT FAILED: type is not FrozenC5"
  let frozenNames : List String := ["P", "mctx", "mref", "cctx", "cref", "w", "w1", "O", "T", "hA", "entryL", "entryW", "entry", "hw",
    "b", "raw", "D", "hcore", "hpost"]
  let frozenImplicit : List String := ["mctx", "mref", "cctx", "cref", "w", "w1", "b", "raw", "D"]
  forallTelescope fv fun xs _ => do
    unless xs.size == frozenNames.length do throwError "QFINAL AUDIT FAILED: FrozenC5 has {xs.size} binders, expected {frozenNames.length}"
    for (x, nm) in xs.toList.zip frozenNames do
      let u := (← x.fvarId!.getUserName).toString
      unless u == nm do throwError "QFINAL AUDIT FAILED: binder {u}, frozen {nm}"
      let bi ← x.fvarId!.getBinderInfo
      unless (bi == .implicit) == frozenImplicit.contains nm do throwError "QFINAL AUDIT FAILED: binder {nm} info {repr bi}"
  -- no hypothesis beyond the frozen binders: the proof applies qSharedLeaf_ships_of_hcalls to hcalls_of_classQ
  let some (.thmInfo t) := (← getEnv).find? ``qSharedLeaf_ships | throwError "QFINAL AUDIT FAILED: not a theorem"
  unless t.value.getUsedConstants.contains ``Tests.Compiler.QHCalls.hcalls_of_classQ do
    throwError "QFINAL AUDIT FAILED: qSharedLeaf_ships does not use hcalls_of_classQ"
  let okPfx := ["Tests.Compiler.CDef.", "Tests.Compiler.QDef.", "Tests.Compiler.QCloses.", "Tests.Compiler.QHCalls.",
    "Tests.Compiler.QShips.", "Tests.Compiler.QComposed.", "Tests.Compiler.QFinal.qSharedLeaf_ships"]
  let n ← checkGeneric ``qSharedLeaf_ships okPfx
  logInfo m!"QFINAL|ships ok: qSharedLeaf_ships : FrozenC5 ({frozenNames.length} binders, names / binder info), no hypothesis, closure {n} constants (class + generic C5 files only)"
  -- (2) the topshareQ endpoint recovered
  let a ← getConstInfo ``topshareQ_hierC_of_class
  let e ← getConstInfo ``Tests.Compiler.Srm33EndpointTest.topshareQ_hierC_noHstR
  unless ← isDefEq a.type e.type do throwError "QFINAL AUDIT FAILED: corollary type differs from topshareQ_hierC_noHstR"
  let some (.thmInfo ta) := (← getEnv).find? ``topshareQ_hierC_of_class | throwError "QFINAL AUDIT FAILED: corollary not a theorem"
  unless ta.value.getUsedConstants.contains ``qSharedLeaf_ships do throwError "QFINAL AUDIT FAILED: corollary does not use qSharedLeaf_ships"
  if ta.value.getUsedConstants.contains ``Tests.Compiler.Srm33EndpointTest.topshareQ_hierC_noHstR then
    throwError "QFINAL AUDIT FAILED: corollary uses the instance proof"
  logInfo "QFINAL|ok|topshareQ_hierC_of_class : type_of% topshareQ_hierC_noHstR (isDefEq), proved from qSharedLeaf_ships (P_Q hgrp)"
  -- (3) G-MASK
  let m ← checkGeneric ``Tests.Compiler.QShips.kidsMasked_of_class ["Tests.Compiler.CDef.", "Tests.Compiler.QDef.", "Tests.Compiler.QCloses.", "Tests.Compiler.QShips."]
  let pj ← getConstInfo ``topshareQ_kidsMasked_of_class
  let inst ← getConstInfo ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_kidsMasked
  forallBoundedTelescope pj.type (some 1) fun _ rest => do
    unless ← isDefEq rest inst.type do throwError "QFINAL GMASK FAILED: projection type differs from topshareQ_kidsMasked"
  logInfo m!"QFINAL|gmask ok: kidsMasked_of_class closure {m} constants (generic), topshareQ_kidsMasked recovered (isDefEq)"
  -- (4) axioms
  for n in [``qSharedLeaf_ships, ``topshareQ_hierC_of_class, ``topshareQ_kidsMasked_of_class, ``Tests.Compiler.QShips.kidsMasked_of_class] do
    for x in ← Lean.collectAxioms n do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "QFINAL AUDIT FAILED: {x} in {n}"
  logInfo "QFINAL|axioms ok: propext, Classical.choice, Quot.sound only"

#print axioms qSharedLeaf_ships
#print axioms topshareQ_hierC_of_class

end Tests.Compiler.QFinal
