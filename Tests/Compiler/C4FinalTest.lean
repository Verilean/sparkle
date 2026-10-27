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

#print axioms Tests.Compiler.C4Composed.memSharedLeaf_ships
#print axioms topshareM_hierC_of_class

end Tests.Compiler.C4Final
