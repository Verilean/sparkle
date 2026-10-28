import Tools.ShippingKaryCalls
-- BUILT (unit SR21): k7 exit 0 (Tools.ShippingKaryBridge, dev run); the final-SHA rebuild is in REPORT-SR21.md.
-- SCOPE (binding, ledger L8ba): the K = 2 BRIDGE.  The two-callee QUAD bundles (`QuadParentData`, `QuadAll`, `QuadBnd`) and tables (`quadOutsOf`, `quadWidthsOf`, `quadBsF`, `quadSrcF`, `quadPC`,
-- `quadNk`, `quadOuts`) are shown to be the K-ary ones at the callee list `quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂ = [⟨c₁, d₁, n₁, src₁⟩, ⟨c₂, d₂, n₂, src₂⟩]`: `KaryParentData.ofQuad`, `KaryAll.ofQuad`, `KaryBnd.ofQuad`,
-- and the table equalities.  `Tests/Compiler/KaryQuadAuditTest.lean` uses them to re-derive the OLD statements (`quad_closes0`, `quad_entry_run_ret_np`, `quad_ranA`, `quad_hkid`, `quad_runFacts`,
-- `quad_outsCheck`, `quad_kidsMasked`, `quad_designCheck`, `quad_traceXA`, `quad_soundLA`, `quad_composed_split`) from the K-ary lemmas and checks the statements by `isDefEq`.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingKaryBridge
open Tools.ShippingKaryRun Tools.ShippingKaryEntry Tools.ShippingKaryLeafGeneric Tools.ShippingKaryComposed Tools.ShippingKaryCalls
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadReturned Tools.ShippingQuadComposed Tools.ShippingQuadCalls
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildVCA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPinC Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingSharedLeafCoh
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses
open Tools.ShippingMachineAuto
open Tools.ShippingShipsFree
open Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMachineCausal Tools.ShippingServedRealA
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMixedSourceBridge

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the callee list of the QUAD class -/
def quad2 (c₁ c₂ : Name) (d₁ d₂ : MachineData) (n₁ n₂ : Nat) (src₁ src₂ : KSrc) : List KCal := [⟨c₁, d₁, n₁, src₁⟩, ⟨c₂, d₂, n₂, src₂⟩]

section Tables
variable (c₁ c₂ : Name) (d₁ d₂ : MachineData) (n₁ n₂ : Nat) (src₁ src₂ : KSrc)

theorem kNk_quad2 {k : Nat} (hk : k < 4) : kNk (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) k = quadNk d₁ d₂ k := by
  rcases k with _ | _ | _ | _ | k
  · simp [kNk, quad2, quadNk]
  · simp [kNk, quad2, quadNk]
  · simp [kNk, quad2, quadNk]
  · simp [kNk, quad2, quadNk]
  · omega

theorem kOuts_quad2 {k : Nat} (hk : k < 4) : kOuts (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) k = quadOuts d₁ d₂ k := by
  rcases k with _ | _ | _ | _ | k
  · simp [kOuts, quad2, quadOuts]
  · simp [kOuts, quad2, quadOuts]
  · simp [kOuts, quad2, quadOuts]
  · simp [kOuts, quad2, quadOuts]
  · omega

theorem kOutsOf_quad2 (n : Name) : kOutsOf (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) n = quadOutsOf c₁ c₂ d₁ d₂ n := by
  by_cases h1 : n = c₁
  · simp [kOutsOf, kFind, quad2, quadOutsOf, h1]
  · by_cases h2 : n = c₂
    · subst h2
      simp [kOutsOf, kFind, quad2, quadOutsOf, h1, Ne.symm h1]
    · simp [kOutsOf, kFind, quad2, quadOutsOf, h1, h2, Ne.symm h1, Ne.symm h2]

theorem kWidthsOf_quad2 (n : Name) : kWidthsOf (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) n = quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ n := by
  by_cases h1 : n = c₁
  · simp [kWidthsOf, kFind, quad2, quadWidthsOf, h1]
  · by_cases h2 : n = c₂
    · subst h2
      simp [kWidthsOf, kFind, quad2, quadWidthsOf, h1, Ne.symm h1]
    · simp [kWidthsOf, kFind, quad2, quadWidthsOf, h1, h2, Ne.symm h1, Ne.symm h2]

theorem kBsF_quad2 (n : Name) : kBsF (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) n = quadBsF c₁ c₂ d₁ d₂ n₁ n₂ n := by
  by_cases h1 : n = c₁
  · simp [kBsF, kFind, quad2, quadBsF, h1]
  · by_cases h2 : n = c₂
    · subst h2
      simp [kBsF, kFind, quad2, quadBsF, h1, Ne.symm h1]
    · simp [kBsF, kFind, quad2, quadBsF, h1, h2, Ne.symm h1, Ne.symm h2]

theorem kSrcF_quad2 {ι : Type} (i : ι) (n : Name) :
    kSrcF (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) i n = quadSrcF c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂ i n := by
  by_cases h1 : n = c₁
  · simp [kSrcF, kFind, quad2, quadSrcF, h1]
  · by_cases h2 : n = c₂
    · subst h2
      simp [kSrcF, kFind, quad2, quadSrcF, h1, Ne.symm h1]
    · simp [kSrcF, kFind, quad2, quadSrcF, h1, h2, Ne.symm h1, Ne.symm h2]

theorem kPC_quad2 (O : RefLawsAOps MkRefd mref cref) (design : Sparkle.IR.AST.Design) (G : Name) (dG : MachineData)
    (n : Name) (mc : Sparkle.IR.AST.Module) :
    kPC O design G dG (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) n mc = quadPC O design c₁ c₂ G d₁ d₂ dG n mc := by
  by_cases h1 : n = c₁
  · simp [kPC, kFind, quad2, quadPC, h1]
  · by_cases h2 : n = c₂
    · subst h2
      simp [kPC, kFind, quad2, quadPC, h1, Ne.symm h1]
    · simp [kPC, kFind, quad2, quadPC, h1, h2, Ne.symm h1, Ne.symm h2]

end Tables

variable {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}

theorem KaryParentData.ofQuad (src₁ src₂ : KSrc) (hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP) :
    KaryParentData dP (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) c G nP :=
  { ok := hP.ok, body := hP.body, alias := hP.alias, callsOk := hP.callsOk, slots := hP.slots, domB := hP.domB,
    insts_ne := hP.insts_ne, fne := hP.fne
    names := by simpa [quad2] using hP.names
    child := hP.child, nomemKey := hP.nomemKey
    argsN := fun k hk => (kNk_quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂ (hP.len4 ▸ hk)).trans (hP.argsN k hk)
    fieldOut := fun k hk => by rw [kOuts_quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂ (hP.len4 ▸ hk)]; exact hP.fieldOut k hk
    fieldsNd := hP.fieldsNd, outHead := hP.outHead
    nodup := by simp [quad2, hP.c12]
    cne := fun e he => by
      simp only [quad2, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact hP.cne1
      · exact hP.cne2
    cneG := hP.cneG }

theorem KaryParentExtra.ofQuad (src₁ src₂ : KSrc) (h : QuadParentExtra dP d₁ d₂ c₁ c₂ nP n₁ n₂) :
    KaryParentExtra dP (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) nP := by
  have e1 : (fun k => kOutsOf (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) (quadCalleeAt dP k)) = (fun k => quadOutsOf c₁ c₂ d₁ d₂ (quadCalleeAt dP k)) :=
    funext fun k => kOutsOf_quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂ _
  have e2 : (fun k => kWidthsOf (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) (quadCalleeAt dP k)) = (fun k => quadWidthsOf c₁ c₂ d₁ d₂ n₁ n₂ (quadCalleeAt dP k)) :=
    funext fun k => kWidthsOf_quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂ _
  exact { slotsNe := h.slotsNe, outTy := h.outTy, nomem := h.nomem
          callWidths := by rw [e1]; exact h.callWidths
          callArgs := by rw [e2]; exact h.callArgs
          outsClean := h.outsClean, scalar := h.scalar, hkD := h.hkD, hIlen := h.hIlen, hSL := h.hSL, hSlen := h.hSlen,
          hLlen := h.hLlen, hNIn := h.hNIn }

theorem KaryCallees.ofQuad (src₁ src₂ : KSrc) (hG : LeafData dG) (h₁ : LeafCalleeData d₁ dG c₁ G n₁) (h₂ : LeafCalleeData d₂ dG c₂ G n₂) :
    KaryCallees (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) dG G := by
  intro e he
  simp only [quad2, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact h₁
  · exact h₂

theorem KaryEntries.ofQuad (src₁ src₂ : KSrc) (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape) :
    KaryEntries mctx mref cctx cref (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) := by
  intro e he
  simp only [quad2, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact entry₁
  · exact entry₂

theorem KaryAll.ofQuad (src₁ src₂ : KSrc) (Q : QuadAll dP d₁ d₂ dG c c₁ c₂ G nP n₁ n₂) :
    KaryAll dP dG (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) c G nP :=
  { hP := KaryParentData.ofQuad src₁ src₂ Q.hP, hPX := KaryParentExtra.ofQuad src₁ src₂ Q.hPX, hG := Q.hG, hK := Q.hK
    hC := KaryCallees.ofQuad src₁ src₂ Q.hG Q.hC₁ Q.hC₂
    hX := fun e he => by
      simp only [quad2, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact Q.hX₁
      · exact Q.hX₂ }

theorem KaryBnd.ofQuad (src₁ src₂ : KSrc) {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : QuadBnd c₁ c₂ G d₁ d₂ dG mctx mref cctx cref w m design) :
    KaryBnd (quad2 c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂) G dG mctx mref cctx cref w m design := by
  obtain ⟨O, T, hA, hM0, hR0, hM1, -, hw⟩ := h
  exact ⟨O, T, hA, hM0, hM1, hR0, hw⟩

end Tools.ShippingKaryBridge
