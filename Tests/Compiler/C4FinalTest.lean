import Tests.Compiler.C4ComposedTest
import Tests.Compiler.Srm33EndpointTest
set_option autoImplicit false
set_option Elab.async false
-- C4 FINAL (issue sparkle-gen-c4-assembly; integration kjob/c4-int).
-- (1) the existing instance endpoint Tests.Compiler.Srm33EndpointTest.topshareM_hierC_noHstR, with its EXACT type, recovered from the
--     generic theorem Tests.Compiler.C4Composed.memSharedLeaf_ships at the member P_M hgrp. Its instance antecedent TmBnd supplies the
--     contract binders and the class assumption TmGrp; kidsMaskedN is unused (it is derived inside the generic theorem).
-- (2) the axioms of the generic theorem and of the corollary.
-- SCOPE: the M-shape class only (AMENDMENT 3; P_Q is not a member, Q shape = sparkle-gen-c5-qshape). No production change; not G3.
namespace Tests.Compiler.C4Final
open Tests.Compiler.CDef Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.Srm9ComposedTest

/-- **topshareM recovered**: exactly the type of the instance endpoint, from the generic C4 theorem -/
theorem topshareM_hierC_of_class : type_of% @Tests.Compiler.Srm33EndpointTest.topshareM_hierC_noHstR := by
  intro mctx mref cctx cref w w1 b raw D hcore hpost entry _ hB _
  obtain ⟨O, T, hA, entryL, entry₁, entry₂, _, _, hgrp, hw⟩ := hB
  exact Tests.Compiler.C4Composed.memSharedLeaf_ships (P_M hgrp) O T hA entryL
    (fun wp hwp => by
      simp only [P_M, List.mem_cons, List.not_mem_nil, or_false] at hwp
      rcases hwp with rfl | rfl
      · exact entry₁
      · exact entry₂)
    entry hw hcore hpost

open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- the corollary's type IS the instance endpoint's type
  let a ← getConstInfo ``topshareM_hierC_of_class
  let e ← getConstInfo ``Tests.Compiler.Srm33EndpointTest.topshareM_hierC_noHstR
  unless ← isDefEq a.type e.type do throwError "C4FINAL AUDIT FAILED: corollary type differs from topshareM_hierC_noHstR"
  -- the corollary is proved FROM the generic theorem (its body mentions memSharedLeaf_ships, not the instance endpoint)
  let some (.thmInfo t) := (← getEnv).find? ``topshareM_hierC_of_class | throwError "C4FINAL AUDIT FAILED: corollary not a theorem"
  let cs := t.value.getUsedConstants
  unless cs.contains ``Tests.Compiler.C4Composed.memSharedLeaf_ships do throwError "C4FINAL AUDIT FAILED: corollary does not use memSharedLeaf_ships"
  if cs.contains ``Tests.Compiler.Srm33EndpointTest.topshareM_hierC_noHstR then throwError "C4FINAL AUDIT FAILED: corollary uses the instance proof"
  for n in [``Tests.Compiler.C4Composed.memSharedLeaf_ships, ``topshareM_hierC_of_class] do
    let axs ← Lean.collectAxioms n
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "C4FINAL AUDIT FAILED: {x} in {n}"
    logInfo m!"C4FINAL|axioms {n}: {axs}"
  logInfo "C4FINAL|ok|topshareM_hierC_of_class : type_of% topshareM_hierC_noHstR (isDefEq), proved from memSharedLeaf_ships (P_M hgrp)"

/-! ## G-MASK (sparkle-gen-c4-gmask): the generic kidsMaskedN (Tests.Compiler.C4Ships.kidsMasked_of_class) -/

/-- topshareM projection: the instance's kidsMaskedN theorem with its exact type (plus the class assumption TmGrp needed to form P_M),
from the generic one -/
theorem topshareM_kidsMasked_of_class (hgrp : TmGrp) : type_of% @Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_kidsMasked := by
  intro mctx mref cctx cref O T hA entryL entry₁ entry₂ entry w w1 raw b D hcore hpost hw
  exact Tests.Compiler.C4Ships.kidsMasked_of_class (P_M hgrp) O T hA entryL
    (fun wp hwp => by
      simp only [P_M, List.mem_cons, List.not_mem_nil, or_false] at hwp
      rcases hwp with rfl | rfl
      · exact entry₁
      · exact entry₂)
    entry hcore hpost hw

open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- the generic statement: P plus the contract binders and the run only (no instance binder)
  let ci ← getConstInfo ``Tests.Compiler.C4Ships.kidsMasked_of_class
  forallTelescope ci.type fun xs body => do
    unless body.isAppOf ``Eq do throwError "C4FINAL GMASK FAILED: conclusion is not kidsMaskedN … = true"
    unless (body.getUsedConstants.contains ``Tools.ShippingMachineShipsDepth.kidsMaskedN) do
      throwError "C4FINAL GMASK FAILED: conclusion does not mention kidsMaskedN"
    for x in xs do
      let t ← inferType x
      for c in t.getUsedConstants do
        if (c.toString.splitOn "Tests.").length > 1 && (c.toString.splitOn "Tests.Compiler.CDef.MemSharedLeafParent").length == 1
            && (c.toString.splitOn "Tests.Compiler.CDef.GenPkg").length == 1 then
          throwError "C4FINAL GMASK FAILED: binder {← x.fvarId!.getUserName} mentions {c}"
  -- closure from kidsMasked_of_class: class + generic C4 files only (bodies from thmInfo)
  let mut seen : NameSet := {}
  let mut work : List Name := [``Tests.Compiler.C4Ships.kidsMasked_of_class]
  let mut reached : Array Name := #[]
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "C4FINAL GMASK FAILED: {n} not found"
    let body? : Option Lean.Expr := match ci with
      | .thmInfo t => some t.value
      | .defnInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    for c in ci.type.getUsedConstants ++ (body?.map Lean.Expr.getUsedConstants).getD #[] do
      if (c.toString.splitOn "Tests.").length > 1 && !seen.contains c then
        reached := reached.push c
        work := c :: work
  let okPfx := ["Tests.Compiler.CDef.", "Tests.Compiler.C4Kid.", "Tests.Compiler.C4Closes.", "Tests.Compiler.C4Ships."]
  for c in reached do
    unless okPfx.any (fun p => (c.toString.splitOn p).length > 1) do throwError "C4FINAL GMASK FAILED: reaches {c}"
    for comp in c.components.map (·.toString) do
      if ["P_M", "P_Q", "wrapM", "wrapM3", "leafM", "leafP", "wrapP", "wrapQ"].contains comp
          || comp.startsWith "topshare" || comp.startsWith "wrapM" || comp.startsWith "P_M" || comp.startsWith "Tm" then
        throwError "C4FINAL GMASK FAILED: reaches {c} (instance component {comp})"
  for h in [``Tests.Compiler.C4Kid.c4_hkid, ``Tests.Compiler.C4Closes.ranA_of_class] do
    unless reached.contains h do throwError "C4FINAL GMASK FAILED: expected {h} not reached"
  -- the projection's type IS the instance theorem's type (after the TmGrp binder)
  let pj ← getConstInfo ``topshareM_kidsMasked_of_class
  let inst ← getConstInfo ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_kidsMasked
  forallBoundedTelescope pj.type (some 1) fun _ rest => do
    unless ← isDefEq rest inst.type do throwError "C4FINAL GMASK FAILED: projection type differs from topshareM_kidsMasked"
  for n in [``Tests.Compiler.C4Ships.kidsMasked_of_class, ``topshareM_kidsMasked_of_class] do
    for x in ← Lean.collectAxioms n do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "C4FINAL GMASK FAILED: {x} in {n}"
  logInfo m!"C4FINAL|gmask ok: kidsMasked_of_class generic (class + contract binders), closure {reached.size} constants (CDef/C4Kid/C4Closes/C4Ships only), topshareM_kidsMasked recovered (isDefEq), standard axioms"

#print axioms Tests.Compiler.C4Composed.memSharedLeaf_ships
#print axioms topshareM_hierC_of_class

end Tests.Compiler.C4Final
