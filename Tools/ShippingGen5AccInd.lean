import Tools.ShippingGen5Acc
import Tools.ShippingGen2Keep
import Tools.ShippingGen2T1
import Tools.ShippingDesignWriterRun
set_option autoImplicit false
-- Clean issue-linked build ac4v-5aab73de: exit 0, 714 jobs, source=base=end, dirty=false, scoped approved at 5aab73de. Earlier Pod builds: g5ac-r3 at 174b92b3. No sorry / axiom / native_decide.

/-! # DG-ACC unit A4: the Acc induction skeleton, CONDITIONAL (scripts/gen5/DG_ACC_FREEZE_REV1.md §B.2-B.3, REV2 §B)

`InvAt`/`IHAt`/`BodyKeepsInv`/`ChildKeepsInv`/`KeepChildStmt`/`ServedShips0Stmt` of Gen2 with `CacheShips`/`ShipsRes` replaced by
`CacheAcc K Reach` / `Acc (CallRel K) c`. PROVED here: `stableA_accInvAt`, `accKeepBody` (the copy of `keepBody`), `accIHAt_limit`
(the copy of `ihAt_limit`), `accIHAt_step` (from `AccServed0Stmt`), `acc_of_run` (the copy of `ih_allPF`'s induction).
NOT supplied (premises): `AccServed0Stmt` (A5), `AccKeepChildStmt` (A5). Nothing says a real run satisfies them. -/
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res Keeps profLogIO)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildVCA (JQ StableA)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildBndCore (cv dv sv)
open Tools.ShippingChildFrontCP
open Tools.ShippingChildDepthC
open Tools.ShippingChildComposeC
open Tools.ShippingChildPinC
open Tools.ShippingChildFresh
open Tools.ShippingChildCoreC
open Tools.ShippingChildTranslateA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildBndInit

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
variable (K : AssignKit ι dom env₀)

section Ind
open Classical

def AccInvAt (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Void IO.RealWorld → Prop :=
  fun w => JQC L.O D w ∧ CacheAcc K Reach (cv w)

def AccIHAt (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context) (u u' : Void IO.RealWorld) (r : Res),
    AdmCtx L.O.quiet mctx cctx → AccInvAt K L Reach D u →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref u r u' → Acc (CallRel K) c

def AccBodyKeeps (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Keeps mctx mref cctx cref (AccInvAt K L Reach D)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)

def AccChildKeeps (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ChildSynthA L.O (AccInvAt K L Reach D)

def AccKeepBodyStmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ D, AccChildKeeps K L Reach D → AccBodyKeeps K L Reach D

def AccKeepChildStmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ D, 1 ≤ D → (D < sparkleSynthDepthLimit → AccBodyKeeps K L Reach (D + 1)) →
    AccIHAt K L Reach D → AccChildKeeps K L Reach D

def AccServed0Stmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ (X : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    Reach X → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → (dv w = 0 ∨ CacheAcc K Reach (cv w)) →
    AccIHAt K L Reach (dv w + 1) → AccChildKeeps K L Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w r w' →
    ∀ c, CallEdge K X c → Acc (CallRel K) c

def AccIHAtStepStmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  AccServed0Stmt K L Reach → ∀ (D : Nat), AccIHAt K L Reach (D + 1) → AccChildKeeps K L Reach (D + 1) →
    AccIHAt K L Reach D

def AccOfRunStmt (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  LimitStmt L → AccServed0Stmt K L Reach → AccKeepChildStmt K L Reach →
    ∀ D, 1 ≤ D → AccIHAt K L Reach D ∧ AccChildKeeps K L Reach D

/-- Copy of `stableA_invAt` (Gen2Connect:41). -/
theorem stableA_accInvAt (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) :
    StableA L.O.quiet (AccInvAt K L Reach D) :=
  ⟨fun _ h => h.1.1.1, fun w w' hc hs hd hq h =>
    ⟨(Tools.ShippingChildCacheA.stableA_JQC L.O D).2 w w' hc hs hd hq h.1, by rw [hc]; exact h.2⟩⟩

theorem accInvAt_sv (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) :
    ∀ w, AccInvAt K L Reach D w → sv w = some synthesizeChild :=
  fun _ h => h.1.1.2.1

/-- The translator keeps `AccInvAt D` from the child hook (copy of `translate_keepsInv_of_tele`). -/
theorem translate_keepsAcc_of_tele (L : Laws mref cref) (Reach : Name → Prop) (D : Nat)
    (hC : AccChildKeeps K L Reach D) (tenv : Lean.Environment) :
    RecA L.O (AccInvAt K L Reach D) (fun e h t n => translateExprToWire tenv e h t n) :=
  have hS := stableA_accInvAt K L Reach D
  have hchild : ChildEntryA L.O (AccInvAt K L Reach D) :=
    childEntryA_of_childSynthA L.O hS (accInvAt_sv K L Reach D) hC
  have hcanon : CanonKeyA L.O (AccInvAt K L Reach D) := Tools.ShippingChildCanonKeyA.canonKeyA L.O hS
  have hImpl : LegacyImplA L.O (AccInvAt K L Reach D) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_tele L.O hS L.T hcanon hchild
  translate_keepsA L.O hS tenv hImpl
    (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl L.O hS hImpl) hcanon
    (Tools.ShippingChildProjFieldA.projFieldNameA L.O L.T hS) hchild

/-- Copy of `keepBody` (Gen2Keep:54): the child hook at `D` gives the body's all-outcome keep at `D`. -/
theorem accKeepBody (L : Laws mref cref) (Reach : Name → Prop) : AccKeepBodyStmt K L Reach := by
  intro D hC
  have hS := stableA_accInvAt K L Reach D
  have hchild : ChildEntryA L.O (AccInvAt K L Reach D) :=
    childEntryA_of_childSynthA L.O hS (accInvAt_sv K L Reach D) hC
  have hcanon : CanonKeyA L.O (AccInvAt K L Reach D) := Tools.ShippingChildCanonKeyA.canonKeyA L.O hS
  have hImpl : LegacyImplA L.O (AccInvAt K L Reach D) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_tele L.O hS L.T hcanon hchild
  exact fun mctx cctx hA declName tenv b ci isInst =>
    fromConst_frontends_of_handlers L.O hA hS hImpl
      (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl L.O hS hImpl) hcanon
      (Tools.ShippingChildProjFieldA.projFieldNameA L.O L.T hS) hC (accInvAt_sv K L Reach D)
      tenv b declName ci isInst
      (fun _ _ => Tools.ShippingChildLegacyTailA.legacyTailA_generic L.O L.T hS hA _
        (translate_keepsAcc_of_tele K L Reach D hC tenv) b declName ci isInst)

/-- Copy of `ihAt_limit` (Gen2T1:149). -/
theorem accIHAt_limit (L : Laws mref cref) (Reach : Name → Prop) (hL : LimitStmt L) {D : Nat}
    (hD : sparkleSynthDepthLimit ≤ D) : AccIHAt K L Reach D := by
  intro c _ mctx cctx u u' r hA hu hr
  obtain ⟨M', Dg'⟩ := r
  obtain ⟨M, Dg, w1, hcore, -, -, -⟩ :=
    Tools.ShippingDesignWriterRun.synthesizeCombinational_designTop hr
  exact (hL c mctx cctx u w1 (M, Dg) D hA hu.1.1 hD hcore).elim

/-- The step: `AccIHAt (D+1)` and `AccChildKeeps (D+1)` give `AccIHAt D` under `AccServed0Stmt`
(`Acc.intro c` from the served callees; `CallRel K c' c = CallEdge K c c'`). -/
theorem accIHAt_step (L : Laws mref cref) (Reach : Name → Prop) : AccIHAtStepStmt K L Reach := by
  intro hS D hIH hKI c hc mctx cctx u u' r hA hu hr
  obtain ⟨M', Dg'⟩ := r
  obtain ⟨M, Dg, w1, hcore, -, -, -⟩ :=
    Tools.ShippingDesignWriterRun.synthesizeCombinational_designTop hr
  have hdv : dv u = D := hu.1.1.2.2
  have hjqc : JQC L.O (dv u) u := by rw [hdv]; exact hu.1
  have hIH' : AccIHAt K L Reach (dv u + 1) := by rw [hdv]; exact hIH
  have hKI' : AccChildKeeps K L Reach (dv u + 1) := by rw [hdv]; exact hKI
  have hsrv := hS c mctx cctx u w1 (M, Dg) hc hA hjqc (Or.inr hu.2) hIH' hKI' hcore
  exact Acc.intro c fun y hy => hsrv y hy

/-- The depth induction (copy of `ih_allPF`, Gen2T1:198). CONDITIONAL on `AccServed0Stmt`, `AccKeepChildStmt`. -/
theorem acc_of_run (L : Laws mref cref) (Reach : Name → Prop) : AccOfRunStmt K L Reach := by
  intro hLim hSS hKC
  have key : ∀ k D, sparkleSynthDepthLimit - D = k → 1 ≤ D →
      AccIHAt K L Reach D ∧ AccChildKeeps K L Reach D := by
    intro k
    induction k with
    | zero =>
      intro D hk hD1
      have hle : sparkleSynthDepthLimit ≤ D := by omega
      have hI : AccIHAt K L Reach D := accIHAt_limit K L Reach hLim hle
      exact ⟨hI, hKC D hD1 (fun hlt => absurd hle (by omega)) hI⟩
    | succ k ih =>
      intro D hk hD1
      have hN := ih (D + 1) (by omega) (by omega)
      have hI : AccIHAt K L Reach D := accIHAt_step K L Reach hSS D hN.1 hN.2
      exact ⟨hI, hKC D hD1 (fun _ => accKeepBody K L Reach (D + 1) hN.2) hI⟩
  intro D hD1
  exact key _ D rfl hD1

end Ind

end Tools.ShippingGen5Acc
