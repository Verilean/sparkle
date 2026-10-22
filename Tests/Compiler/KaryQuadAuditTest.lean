import Tools.ShippingKaryBridge
import Tests.Compiler.ChildVertAuditTest
-- UNBUILT (unit SR21): see STATUS-SR21.md for the run names.
-- SCOPE (binding, ledger L8ba): the K = 2 AUDIT.  Each parent-level generic lemma of the two-callee QUAD class (`quad_closes0`, `quad_machineRun`, `quad_entry_run_ret_np`, `quad_ranA`, `quad_hkid`,
-- `quad_runFacts`, `quad_outsCheck`, `quad_kidsMasked`, `quad_designCheck`, `quad_traceXA`, `quad_soundLA`, `quad_composed_split`) is RE-DERIVED here, with its OLD statement (`type_of%` of the old
-- constant), from the K-ary lemma at the callee list `quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂` and the bridged data bundles (`Tools/ShippingKaryBridge.lean`).  The old lemmas are untouched and stay in the
-- library; a `run_cmd` then checks, for each pair, that (1) the statement of the re-derivation is `isDefEq` to the statement of the old constant (same binders), (2) the re-derivation's dependency
-- closure contains the K-ary lemma and does NOT contain the old lemma, (3) standard axioms only; plus mismatch checks (the statement of a different old lemma is NOT `isDefEq`).
-- This shows the K-ary lemmas SPECIALISE to the old ones at K = 2 (given the data-bundle bridge); it does not show that the K-ary class contains more than QUAD for any data — that is the
-- three-callee example (`Tests/Compiler/KaryThreeTest.lean`).  No `sorry`, no `axiom`, no `native_decide`.
section
open Tools.ShippingKaryRun Tools.ShippingKaryEntry Tools.ShippingKaryLeafGeneric Tools.ShippingKaryComposed Tools.ShippingKaryCalls Tools.ShippingKaryBridge
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadReturned Tools.ShippingQuadComposed Tools.ShippingQuadCalls
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingTopShareRun
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineCausal Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineCloses

namespace Tests.Compiler.KaryQuadAuditTest

/-! ## the generic run lemmas -/

theorem closes0_via_kary : type_of% @Tools.ShippingQuadLeafGeneric.quad_closes0 := by
  intro mctx mref cctx cref O T hA dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ hP hG h₁ h₂ entry₁ entry₂ hR0 hcl
  exact kary_closes0 O T hA (KaryParentData.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hP) hG
    (KaryCallees.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hG h₁ h₂)
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) hR0 hcl

theorem machineRun_via_kary : type_of% @Tools.ShippingQuadLeafGeneric.quad_machineRun := by
  intro mctx mref cctx cref O T hA dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ hP hG h₁ h₂ entryP entry₁ entry₂ hR0 hcl w w' m design hw hcore
  exact kary_machineRun O T hA (KaryParentData.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hP) hG
    (KaryCallees.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hG h₁ h₂)
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) entryP hR0 hcl hw hcore

theorem entry_run_ret_np_via_kary : type_of% @Tools.ShippingQuadLeafGeneric.quad_entry_run_ret_np := by
  intro mctx mref cctx cref O T hA dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ hP hG h₁ h₂ entryP entry₁ entry₂ hR0 hcl w w' y hw h
  obtain ⟨Y, t, t', d₀, M, Dg, w10, wc, hlen, hlets, hrr, hj, hcv, hcc, hkt, hcoh, hget, hcross, hshared, hcore, hcvwc, hpost, hno⟩ :=
    kary_entry_run O T hA (KaryParentData.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hP) hG
      (KaryCallees.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) hG h₁ h₂)
      (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) entryP hR0 hcl hw h
  rcases Y with _ | ⟨y₁, _ | ⟨y₂, _ | ⟨y₃, Y⟩⟩⟩
  · simp [quad2] at hlen
  · simp [quad2] at hlen
  · refine ⟨y₁, y₂, t, t', d₀, M, Dg, w10, wc, hlets, hrr, hj, hcv, hcc, hkt, hcoh, ?_, ?_, ?_, ?_, hcore, hcvwc, hpost, hno⟩
    · obtain ⟨y, hy, hg⟩ := hget 0 (by simp [quad2])
      have : y = y₁ := (Option.some.inj hy).symm
      subst this; exact hg
    · obtain ⟨y, hy, hg⟩ := hget 1 (by simp [quad2])
      have : y = y₂ := (Option.some.inj hy).symm
      subst this; exact hg
    · exact hcross 0 (by simp [quad2]) 1 (by simp [quad2]) y₁ y₂ rfl rfl
    · exact hshared 0 (by simp [quad2]) 1 (by simp [quad2]) y₁ y₂ rfl rfl
  · simp [quad2] at hlen

/-! ## the parent blocks -/

theorem ranA_via_kary : type_of% @Tools.ShippingQuadComposed.quad_ranA := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ O T hA Q entry₁ entry₂ hR0 hcl w w1 raw D hcore entry hw
  exact kary_ranA O T hA (KaryAll.ofQuad (fun _ _ _ => []) (fun _ _ _ => []) Q)
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) hR0 hcl hcore entry hw

theorem hkid_via_kary : type_of% @Tools.ShippingQuadComposed.quad_hkid := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ O T Q entry₁ entry₂ hR0 hcl m k hk
  have := kary_hkid O T (KaryAll.ofQuad (fun _ _ _ => []) (fun _ _ _ => []) Q)
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) hR0 hcl m k hk
  rwa [kOutsOf_quad2, kWidthsOf_quad2] at this

theorem runFacts_via_kary : type_of% @Tools.ShippingQuadComposed.quad_runFacts := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ O T m hA Q entry₁ entry₂ hR0 hcl w w1 raw b D hcore hpost entry hw
  exact kary_runFacts O T m hA (KaryAll.ofQuad (fun _ _ _ => []) (fun _ _ _ => []) Q)
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) hR0 hcl hcore hpost entry hw

theorem outsCheck_via_kary : type_of% @Tools.ShippingQuadComposed.quad_outsCheck := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ O T m hA Q entry₁ entry₂ hR0 hcl w w1 raw b D hcore hpost entry hw
  exact kary_outsCheck O T m hA (KaryAll.ofQuad (fun _ _ _ => []) (fun _ _ _ => []) Q)
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) hR0 hcl hcore hpost entry hw

theorem kidsMasked_via_kary : type_of% @Tools.ShippingQuadComposed.quad_kidsMasked := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ O T m hA Q entry₁ entry₂ hR0 hcl w w1 raw b D hcore hpost entry hw
  exact kary_kidsMasked O T m hA (KaryAll.ofQuad (fun _ _ _ => []) (fun _ _ _ => []) Q)
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) hR0 hcl hcore hpost entry hw

theorem designCheck_via_kary : type_of% @Tools.ShippingQuadComposed.quad_designCheck := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ O T m hA Q entry₁ entry₂ hR0 hcl w w1 raw b D hcore hpost entry hw
  exact kary_designCheck O T m hA (KaryAll.ofQuad (fun _ _ _ => []) (fun _ _ _ => []) Q)
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) hR0 hcl hcore hpost entry hw

theorem traceXA_via_kary : type_of% @Tools.ShippingQuadComposed.quad_traceXA := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ ι dom ρ instP initsP bodyP obsRP extP extBP srcP O T hA Q GP entryP entry₁ entry₂ hR0 hcl w w' m design hw hcore
  exact kary_traceXA O T hA (KaryAll.ofQuad (fun _ _ _ => []) (fun _ _ _ => []) Q) GP entryP
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) hR0 hcl hw hcore

theorem soundLA_via_kary : type_of% @Tools.ShippingQuadComposed.quad_soundLA := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ ι dom ρ instP initsP bodyP obsRP extP extBP srcP O T hA Q GP entryP entry₁ entry₂ hR0 hcl w w' m design hw hcore
  exact kary_soundLA O T hA (KaryAll.ofQuad (fun _ _ _ => []) (fun _ _ _ => []) Q) GP entryP
    (KaryEntries.ofQuad (src₁ := fun _ _ _ => []) (src₂ := fun _ _ _ => []) entry₁ entry₂) hR0 hcl hw hcore

theorem composed_split_via_kary : type_of% @Tools.ShippingQuadCalls.quad_composed_split := by
  intro mctx mref cctx cref dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂ ι dom ρ instP initsP bodyP obsRP extP extBP srcP inst₁ inst₂ ρ₁ ρ₂
    inits₁ body₁ obsR₁ ext₁ extB₁ src₁ inits₂ body₂ obsR₂ ext₂ extB₂ src₂ srcG Q GP G₁ G₂ hrun hF₁ hF₂ hFP hextB₁ hext₁ hextB₂ hext₂ hcl
    w w' m design hcore entry hB
  have hFP' : CallFactF dP nP (letObsB dP dom initsP bodyP extP extBP)
      (fun i bools bits => extP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (fun i bools bits => extBP i bools bits (stateLoop initsP (bodyP i bools bits)))
      (kOutsOf (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂)) (kSrcF (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂)) := by
    have e1 : kOutsOf (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) = quadOutsOf c₁ c₂ d₁ d₂ := funext (kOutsOf_quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂)
    have e2 : (kSrcF (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) : ι → Name → (Nat → List Nat) → List (Nat → Nat)) =
        quadSrcF c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂ :=
      funext fun i => funext fun n => kSrcF_quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂ i n
    rw [e1, e2]; exact hFP
  exact kary_composed_split (cs := quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) (KaryAll.ofQuad src₁ src₂ Q) GP
    (fun e he => by
      simp only [quad2, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact { inh := inst₁, ρ := ρ₁, inits := inits₁, body := body₁, obsR := obsR₁, ext := ext₁, extB := extB₁, gen := G₁,
                hF := hF₁, hextB := hextB₁, hext := hext₁ }
      · exact { inh := inst₂, ρ := ρ₂, inits := inits₂, body := body₂, obsR := obsR₂, ext := ext₂, extB := extB₂, gen := G₂,
                hF := hF₂, hextB := hextB₂, hext := hext₂ })
    hrun hFP' hcl hcore entry (KaryBnd.ofQuad src₁ src₂ hB)

/-! ## the audit -/

open Lean Elab Command Meta in
set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let pairs : List (Name × Name × Name) :=
    [(``closes0_via_kary, ``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingKaryLeafGeneric.kary_closes0),
     (``machineRun_via_kary, ``Tools.ShippingQuadLeafGeneric.quad_machineRun, ``Tools.ShippingKaryLeafGeneric.kary_machineRun),
     (``entry_run_ret_np_via_kary, ``Tools.ShippingQuadLeafGeneric.quad_entry_run_ret_np, ``Tools.ShippingKaryLeafGeneric.kary_entry_run),
     (``ranA_via_kary, ``Tools.ShippingQuadComposed.quad_ranA, ``Tools.ShippingKaryComposed.kary_ranA),
     (``hkid_via_kary, ``Tools.ShippingQuadComposed.quad_hkid, ``Tools.ShippingKaryComposed.kary_hkid),
     (``runFacts_via_kary, ``Tools.ShippingQuadComposed.quad_runFacts, ``Tools.ShippingKaryComposed.kary_runFacts),
     (``outsCheck_via_kary, ``Tools.ShippingQuadComposed.quad_outsCheck, ``Tools.ShippingKaryComposed.kary_outsCheck),
     (``kidsMasked_via_kary, ``Tools.ShippingQuadComposed.quad_kidsMasked, ``Tools.ShippingKaryComposed.kary_kidsMasked),
     (``designCheck_via_kary, ``Tools.ShippingQuadComposed.quad_designCheck, ``Tools.ShippingKaryComposed.kary_designCheck),
     (``traceXA_via_kary, ``Tools.ShippingQuadComposed.quad_traceXA, ``Tools.ShippingKaryComposed.kary_traceXA),
     (``soundLA_via_kary, ``Tools.ShippingQuadComposed.quad_soundLA, ``Tools.ShippingKaryComposed.kary_soundLA),
     (``composed_split_via_kary, ``Tools.ShippingQuadCalls.quad_composed_split, ``Tools.ShippingKaryCalls.kary_composed_split)]
  for (nw, old, kary) in pairs do
    let tn := (← getConstInfo nw).type
    let to := (← getConstInfo old).type
    unless (← isDefEq tn to) do throwError "SR21 AUDIT FAILED: the statement of {nw} differs from {old}"
    let cl ← Tests.Compiler.ChildVertAuditTest.depClosure nw
    unless cl.contains kary do throwError "SR21 AUDIT FAILED: {kary} is not in the closure of {nw}"
    if cl.contains old then throwError "SR21 AUDIT FAILED: the OLD lemma {old} is in the closure of {nw} (the re-derivation would prove nothing)"
    Tests.Compiler.ChildVertAuditTest.stdAxioms nw
  -- mismatch audit: the statement of a re-derivation is NOT the statement of a different old lemma
  let mism : List (Name × Name) :=
    [(``ranA_via_kary, ``Tools.ShippingQuadComposed.quad_hkid), (``runFacts_via_kary, ``Tools.ShippingQuadComposed.quad_outsCheck),
     (``outsCheck_via_kary, ``Tools.ShippingQuadComposed.quad_kidsMasked), (``traceXA_via_kary, ``Tools.ShippingQuadComposed.quad_soundLA),
     (``closes0_via_kary, ``Tools.ShippingQuadLeafGeneric.quad_machineRun), (``machineRun_via_kary, ``Tools.ShippingQuadLeafGeneric.quad_closes0)]
  for (nw, old) in mism do
    if (← isDefEq (← getConstInfo nw).type (← getConstInfo old).type) then
      throwError "SR21 AUDIT FAILED: {nw} and {old} were judged equal (the audit would not discriminate)"
  logInfo m!"SR21 K=2 AUDIT: {pairs.length} re-derivations of the old QUAD statements from the K-ary lemmas are isDefEq to the old statements, depend on the K-ary lemma and not on the old one, use standard axioms only; {mism.length} mismatched pairs are REJECTED"

end Tests.Compiler.KaryQuadAuditTest
end

#print axioms Tests.Compiler.KaryQuadAuditTest.composed_split_via_kary
#print axioms Tests.Compiler.KaryQuadAuditTest.entry_run_ret_np_via_kary
