import Tools.ShippingKaryReturned
import Tools.ShippingKaryBridge
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit SR22): r1 exit 0 (dev run; 823 jobs); the final-SHA rebuild is in REPORT-SR22.md.
-- SCOPE (binding, ledger L8bb): the K = 2 AUDIT of the RETURNED / WIRED theorems.  `quad_returned` and `quad_wired` are RE-DERIVED here, with their OLD statements (`type_of%` of the old constant),
-- from `kary_returned` / `kary_wired` at the callee list `quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂` and the bridged data bundles (`Tools/ShippingKaryBridge.lean`; the old per-block premises over `QuadBnd`
-- are transported to `KaryBnd` by `quadBnd_ofKary`, which only re-uses `MachineDefines` of the leaf for its second occurrence).  A `run_cmd` checks (1) the statement of the re-derivation is `isDefEq` to the
-- statement of the old constant, (2) the closure contains the K-ary theorem and NOT the old one, (3) standard axioms only, plus mismatch checks (returned vs wired are NOT judged equal).
-- This shows the K-ary theorems SPECIALISE to the old ones at K = 2; it does not show that the K-ary class contains more than QUAD for any data (the three-callee example does).  No `sorry`, no `axiom`.
section
open Tools.ShippingKaryRun Tools.ShippingKaryEntry Tools.ShippingKaryLeafGeneric Tools.ShippingKaryComposed Tools.ShippingKaryCalls Tools.ShippingKaryBridge Tools.ShippingKaryReturned
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadReturned Tools.ShippingQuadComposed Tools.ShippingQuadCalls
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingTopShareRun
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineCausal Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineCloses

namespace Tests.Compiler.KaryReturnedAuditTest

theorem quadBnd_ofKary {c₁ c₂ G : Name} {d₁ d₂ dG : MachineData} {n₁ n₂ : Nat} (src₁ src₂ : KSrc)
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : KaryBnd (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) G dG mctx mref cctx cref w m design) :
    QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w m design := by
  obtain ⟨O, T, hA, hM0, hM1, hR0, hw⟩ := h
  exact ⟨O, T, hA, hM0, hR0, hM1, hR0, hw⟩

theorem returned_via_kary : type_of% @Tools.ShippingQuadReturned.quad_returned := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ n kD ι dom src ext extB lsrc srcL extL extBL soundL composed houtTy hFacts hOuts hBdRun hdc
    O T hA hP hG h₁ h₂ entryP entry₁ entry₂ hR0 hcl w w' y hw h
  obtain ⟨Y, t, t', d₀, M, Dg, w10, wc, hlen, hlets, hrr, hj, hcv, hcc, hkt, hcoh, hget, hcross, hshared, hcore, hcvwc, hpost, hno, hy2, hcomp, hsem⟩ :=
    kary_returned (src := src) (ext := ext) (extB := extB) (lsrc := lsrc) (srcL := srcL) (extL := extL) (extBL := extBL) (cs := quad2 c₁ c₂ d₁ d₂ n₁ n₂ (fun _ _ _ => []) (fun _ _ _ => []))
      (fun hcore entry hB => soundL hcore entry (quadBnd_ofKary _ _ hB))
      (fun hcore entry hB => composed hcore entry (quadBnd_ofKary _ _ hB))
      houtTy
      (fun hcore hpost entry hB => hFacts hcore hpost entry (quadBnd_ofKary _ _ hB))
      (fun hcore hpost entry hg hB => hOuts hcore hpost entry hg (quadBnd_ofKary _ _ hB))
      (fun hcore hpost entry hB => hBdRun hcore hpost entry (quadBnd_ofKary _ _ hB))
      (fun hcore hpost entry hB => hdc hcore hpost entry (quadBnd_ofKary _ _ hB))
      O T hA (KaryParentData.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hP) hG
      (KaryCallees.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hG h₁ h₂)
      (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) entryP hR0 hcl hw h
  rcases Y with _ | ⟨y₁, _ | ⟨y₂, _ | ⟨y₃, Y⟩⟩⟩
  · simp [quad2] at hlen
  · simp [quad2] at hlen
  · refine ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hrr, hj, hcv, hcc, hkt, hcoh, ?_, ?_, ?_, ?_, hcore, hcvwc, hpost, hno, hy2, hcomp, hsem⟩
    · obtain ⟨y, hy, hg⟩ := hget 0 (by simp [quad2])
      have : y = y₁ := (Option.some.inj hy).symm
      subst this; exact hg
    · obtain ⟨y, hy, hg⟩ := hget 1 (by simp [quad2])
      have : y = y₂ := (Option.some.inj hy).symm
      subst this; exact hg
    · exact hcross 0 (by simp [quad2]) 1 (by simp [quad2]) y₁ y₂ rfl rfl
    · exact hshared 0 (by simp [quad2]) 1 (by simp [quad2]) y₁ y₂ rfl rfl
  · simp [quad2] at hlen

theorem wired_via_kary : type_of% @Tools.ShippingQuadReturned.quad_wired := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ n kD ι dom src ext extB lsrc srcL extL extBL soundL composed houtTy hFacts hOuts hBdRun hdc
    O T hA hP hG h₁ h₂ entryP entry₁ entry₂ hR0 hcl w w' y hw h
  obtain ⟨Y, t, t', d₀, M, Dg, w10, wc, hlen, hlets, hrr, hj, hcv, hcc, hkt, hcoh, hget, hcross, hshared, hcore, hcvwc, hpost, hcomp, hsem, hlook⟩ :=
    kary_wired (src := src) (ext := ext) (extB := extB) (lsrc := lsrc) (srcL := srcL) (extL := extL) (extBL := extBL) (cs := quad2 c₁ c₂ d₁ d₂ n₁ n₂ (fun _ _ _ => []) (fun _ _ _ => []))
      (fun hcore entry hB => soundL hcore entry (quadBnd_ofKary _ _ hB))
      (fun hcore entry hB => composed hcore entry (quadBnd_ofKary _ _ hB))
      houtTy
      (fun hcore hpost entry hB => hFacts hcore hpost entry (quadBnd_ofKary _ _ hB))
      (fun hcore hpost entry hg hB => hOuts hcore hpost entry hg (quadBnd_ofKary _ _ hB))
      (fun hcore hpost entry hB => hBdRun hcore hpost entry (quadBnd_ofKary _ _ hB))
      (fun hcore hpost entry hB => hdc hcore hpost entry (quadBnd_ofKary _ _ hB))
      O T hA (KaryParentData.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hP) hG
      (KaryCallees.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hG h₁ h₂)
      (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) entryP hR0 hcl hw h
  rcases Y with _ | ⟨y₁, _ | ⟨y₂, _ | ⟨y₃, Y⟩⟩⟩
  · simp [quad2] at hlen
  · simp [quad2] at hlen
  · refine ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hrr, hj, hcv, hcc, hkt, hcoh, ?_, ?_, ?_, ?_, hcore, hcvwc, hpost, hcomp, hsem, hlook⟩
    · obtain ⟨y, hy, hg⟩ := hget 0 (by simp [quad2])
      have : y = y₁ := (Option.some.inj hy).symm
      subst this; exact hg
    · obtain ⟨y, hy, hg⟩ := hget 1 (by simp [quad2])
      have : y = y₂ := (Option.some.inj hy).symm
      subst this; exact hg
    · exact hcross 0 (by simp [quad2]) 1 (by simp [quad2]) y₁ y₂ rfl rfl
    · exact hshared 0 (by simp [quad2]) 1 (by simp [quad2]) y₁ y₂ rfl rfl
  · simp [quad2] at hlen

/-! ## the audit -/

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let pairs : List (Name × Name × Name) :=
    [(``returned_via_kary, ``Tools.ShippingQuadReturned.quad_returned, ``Tools.ShippingKaryReturned.kary_returned),
     (``wired_via_kary, ``Tools.ShippingQuadReturned.quad_wired, ``Tools.ShippingKaryReturned.kary_wired)]
  for (nw, old, kary) in pairs do
    let tn := (← getConstInfo nw).type
    let to := (← getConstInfo old).type
    unless (← isDefEq tn to) do throwError "SR22 AUDIT FAILED: the statement of {nw} differs from {old}"
    let cl ← Tests.Compiler.ChildVertAuditTest.depClosure nw
    unless cl.contains kary do throwError "SR22 AUDIT FAILED: {kary} is not in the closure of {nw}"
    if cl.contains old then throwError "SR22 AUDIT FAILED: the OLD theorem {old} is in the closure of {nw}"
    Tests.Compiler.ChildVertAuditTest.stdAxioms nw
  if (← isDefEq (← getConstInfo ``returned_via_kary).type (← getConstInfo ``Tools.ShippingQuadReturned.quad_wired).type) then
    throwError "SR22 AUDIT FAILED: returned and wired were judged equal (the audit would not discriminate)"
  if (← isDefEq (← getConstInfo ``wired_via_kary).type (← getConstInfo ``Tools.ShippingQuadReturned.quad_returned).type) then
    throwError "SR22 AUDIT FAILED: wired and returned were judged equal (the audit would not discriminate)"
  logInfo m!"SR22 K=2 AUDIT: kary_returned / kary_wired re-derive the OLD quad_returned / quad_wired statements (isDefEq), depend on the K-ary theorem and not on the old one, standard axioms only; 2 mismatched pairs REJECTED"

end Tests.Compiler.KaryReturnedAuditTest
end

#print axioms Tests.Compiler.KaryReturnedAuditTest.returned_via_kary
#print axioms Tests.Compiler.KaryReturnedAuditTest.wired_via_kary
