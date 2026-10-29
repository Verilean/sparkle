import Tools.ShippingGen2Defs
import Tools.ShippingGen2Keep
import Tools.ShippingChildCoreC
import Tools.ShippingDesignWriterRun

set_option autoImplicit false

/-! # Gen2 M3 lead: the T1 induction-step connection (scripts/gen2/T1_CONNECT_FREEZE.md, approved eae85955)

**CONDITIONAL skeleton.** `t1_of_step` is conditional on `StepStmt` (M2-b), `KeepChildStmt` (G-KEEP-CHILD),
`ServedShips0Stmt` (G-SERVED + G-START) and `NoTopStmt` (G-POST). It is NOT M2 or M3 completion and is not counted
as progress toward `done` for either.

PROVED here (no premise beyond what `L` gives): `LimitStmt` (`limitStmt_proved`, the limit-branch prefix of
`core_tripleAC`, Tools/ShippingChildCoreC.lean:128-133, at `JQ` instead of `JQC`); `servedShipsStmt_of_0`
(`ServedShips0Stmt → ServedShipsStmt`, by `Or.inr`; no strictness claim); `childShips_congr`.

Reviewer corrections applied: `ih_all` takes `T1Hyp` explicitly; `LimitStmt` is proved; `servedShipsStmt_of_0`;
G-MEMO is only a DISPATCH exclusion for reached names under `T1Hyp.defines`/`closes` (the memo branch comes after
the machine branch returns) — no cache invariant about the memo map is stated or used here.

Scope: `T1Hyp` as frozen, so the skeleton covers machine-route trees only (freeze §5.2).

BUILT: g3in-b6625408 at b6625408 (exit 0); axiom audit g3in-ax-c6516331 at c6516331 (exit 0, standard axioms only). -/

namespace Tools.ShippingGen2

/-! ## 1. The limit: from `JQ` at a depth `≥ sparkleSynthDepthLimit` the core entry throws -/

section Limit
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA

/-- The limit-branch prefix of `core_tripleAC` (Tools/ShippingChildCoreC.lean:113-133) at the invariant `JQ`
(stable by `stableA_JQ`): from a `JQ quiet D` world with `sparkleSynthDepthLimit ≤ D` the core entry never
returns. `JQ` gives `dv w = D` (its third conjunct, ChildVCA.lean:53-54), which is what the depth read returns. -/
theorem core_limit_triple {Fresh : (σ : Type) → IO.Ref σ → Prop} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (declName : Name) (hD : sparkleSynthDepthLimit ≤ D) :
    Triple mctx mref cctx cref (JQ O.quiet D) (synthesizeCombinationalCore declName [] false)
      (fun _ _ => False) (fun e w => JQ O.quiet D w ∧ OkExc e) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQ O.quiet D) (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsA_diag O hA (stableA_JQ O.quiet D)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.conseq (tripleA_depthGet O hA (stableA_JQ O.quiet D)) (fun _ h => h)
      (Q' := fun d w => JQ O.quiet D w ∧ d = D)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.2.2⟩) (fun _ _ h => h)) ?_
  intro d hd
  subst hd
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · -- at the limit: the entry throws before touching the depth
    refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr O hA (stableA_JQ O.quiet _) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · -- below the limit: excluded by `hD`
    exact absurd hD (by omega)

end Limit

/-! ## 2. The statements of this unit (freeze §2) -/

open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Tools.ShippingChildInvA (RefLawsAOps AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC CacheInvA)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingServedRealA (MachineRunJQC)

variable {ι : Type} {dom : ι → DomainConfig}

/-- **The limit** (proved below as `limitStmt_proved`): from a `JQ` world at a depth `≥ sparkleSynthDepthLimit`,
in an admissible context, the core entry does not return. -/
def LimitStmt {mref cref} (L : Laws mref cref) : Prop :=
  ∀ (c : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res) (D : Nat),
    AdmCtx L.O.quiet mctx cctx → JQ L.O.quiet D w → sparkleSynthDepthLimit ≤ D →
    ¬ RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w r w'

/-- **G-POST** (premise): no module of a reached declaration's core design is named as its core module. -/
def NoTopStmt {mref cref} (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ (c : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw : Sparkle.IR.AST.Module) (Dg : Design),
    Reach c → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, Dg) w1 →
    ∀ x ∈ Dg.modules, x.name ≠ raw.name

/-- **G-SERVED + G-START** (premise): `ServedShipsStmt` with `InvAt (dv w) w` replaced by `JQC (dv w) w` and
the cache half `dv w = 0 ∨ CacheShips …` (the outermost start gives only `JQC 0 w`). A NEW statement next to the
frozen `ServedShipsStmt`, which is not changed. -/
def ServedShips0Stmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
    (raw : Sparkle.IR.AST.Module) (D : Design),
    Reach p.decl → P p.decl = some p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    (dv w = 0 ∨ CacheShips L P Reach (cv w)) →
    IHAt L P Reach (dv w + 1) → ChildKeepsInv L P Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w' →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc

/-! ## 3. Proved pieces -/

/-- **`LimitStmt`, PROVED** from `L` alone (`core_limit_triple` at `L.O`). -/
theorem limitStmt_proved {mref cref} (L : Laws mref cref) : LimitStmt L := by
  intro c mctx cctx w w' r D hA hw hD hr
  have h := core_limit_triple L.O hA D c hD w hw
  unfold RunsTo at hr
  rw [hr] at h
  exact h

/-- `ServedShips0Stmt` gives the frozen `ServedShipsStmt` (`InvAt` = `JQC ∧ CacheShips`; the cache disjunct by
`Or.inr`). No converse or strictness is claimed. -/
theorem servedShipsStmt_of_0 {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) (h : ServedShips0Stmt L P Reach DataOk) : ServedShipsStmt L P Reach DataOk := by
  intro hT p mctx cctx w w' raw D hR hP hA hInv hI hK hr
  exact h hT p mctx cctx w w' raw D hR hP hA hInv.1 (Or.inr hInv.2) hI hK hr

/-- `ChildShips` reads `Dc.modules` only. -/
theorem childShips_congr (q : Pkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) {D1 D2 : Design}
    (h : D1.modules = D2.modules) (hc : ChildShips q n mc D1) : ChildShips q n mc D2 := by
  intro dsn hg hmc i
  exact hc dsn (by rw [h]; exact hg) hmc i

/-- **Base case**: at or above the depth limit `IHAt` holds vacuously (the full entry contains a core run, which
throws there). -/
theorem ihAt_limit {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hL : LimitStmt L) {D : Nat} (hD : sparkleSynthDepthLimit ≤ D) : IHAt L P Reach D := by
  intro c _ mctx cctx u u' r hA hu hr
  obtain ⟨M', Dg'⟩ := r
  obtain ⟨M, Dg, w1, hcore, -, -, -⟩ :=
    Tools.ShippingDesignWriterRun.synthesizeCombinational_designTop hr
  exact (hL c mctx cctx u w1 (M, Dg) D hA hu.1.1 hD hcore).elim

/-- **Step**: `IHAt (D + 1)` and `ChildKeepsInv (D + 1)` give `IHAt D`, under the four conditional premises
(`StepStmt`, `ServedShips0Stmt`, `NoTopStmt`) and `T1Hyp`. -/
theorem ihAt_step {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) (hT : T1Hyp L P Reach DataOk)
    (hStep : StepStmt L P DataOk) (hSS : ServedShips0Stmt L P Reach DataOk) (hNT : NoTopStmt L Reach)
    (D : Nat) (hIH : IHAt L P Reach (D + 1)) (hKI : ChildKeepsInv L P Reach (D + 1)) :
    IHAt L P Reach D := by
  intro c hc mctx cctx u u' r hA hu hr
  have hreal : RealChildA L.O c r := RealChildA.of_jqc L.O hA hu.1 hr
  obtain ⟨M', Dg'⟩ := r
  obtain ⟨M, Dg, w1, hcore, hb, -, hmods⟩ :=
    Tools.ShippingDesignWriterRun.synthesizeCombinational_designTop hr
  obtain ⟨q, hPq, hqd, hDq⟩ := hT.pkg c hc
  subst hqd
  have hdv : dv u = D := hu.1.1.2.2
  have hjqc : JQC L.O (dv u) u := by rw [hdv]; exact hu.1
  have hIH' : IHAt L P Reach (dv u + 1) := by rw [hdv]; exact hIH
  have hKI' : ChildKeepsInv L P Reach (dv u + 1) := by rw [hdv]; exact hKI
  have hdef : MachineDefines mctx mref cctx cref q.decl q.d.shape := hT.defines q.decl hc q hPq mctx cctx hA
  have hcl : MachineClosesAtA L.O mctx cctx q.decl q.d.shape := hT.closes q.decl hc q hPq mctx cctx hA
  -- G-SERVED + G-START: the trace with every served instance shipping
  have hsrv := hSS hT q mctx cctx u w1 M Dg hc hPq hA hjqc (Or.inr hu.2) hIH' hKI' hcore
  -- route evidence of this run (G-MEMO for this reached name: the machine branch returns)
  have htaken : MachineTaken L mctx cctx (dv u + 1) q.decl q.d.shape M Dg :=
    Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hA hcore hdef hcl hjqc.1 (Or.inr hu.1.2)
  obtain ⟨n, -, hCS⟩ :=
    hStep q mctx cctx u w1 M M' Dg hPq hDq hA hjqc hcore hb hdef htaken (hT.dec q.decl hc q hPq) hsrv
  -- G-POST: the full entry's design has the core design's modules
  have hmodsEq : Dg'.modules = Dg.modules := hmods (hNT q.decl mctx cctx u w1 M Dg hc hA hjqc hcore)
  exact ⟨hreal, q, n, hPq, rfl, childShips_congr q n M' hmodsEq.symm hCS⟩

/-- **The depth induction** (on `sparkleSynthDepthLimit - D`, the shape of `childKeepsC_all`,
ChildDepthC.lean:94): both halves of the IH at every depth `≥ 1`. -/
theorem ih_all {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) (hT : T1Hyp L P Reach DataOk)
    (hStep : StepStmt L P DataOk) (hKC : KeepChildStmt L P Reach)
    (hSS : ServedShips0Stmt L P Reach DataOk) (hNT : NoTopStmt L Reach) (hLim : LimitStmt L) :
    ∀ D, 1 ≤ D → IHAt L P Reach D ∧ ChildKeepsInv L P Reach D := by
  have key : ∀ k D, sparkleSynthDepthLimit - D = k → 1 ≤ D →
      IHAt L P Reach D ∧ ChildKeepsInv L P Reach D := by
    intro k
    induction k with
    | zero =>
      intro D hk hD1
      have hle : sparkleSynthDepthLimit ≤ D := by omega
      have hI : IHAt L P Reach D := ihAt_limit L P Reach hLim hle
      exact ⟨hI, hKC D hD1 (fun hlt => absurd hle (by omega)) hI⟩
    | succ k ih =>
      intro D hk hD1
      have hN := ih (D + 1) (by omega) (by omega)
      have hI : IHAt L P Reach D := ihAt_step L P Reach DataOk hT hStep hSS hNT D hN.1 hN.2
      exact ⟨hI, hKC D hD1 (fun _ => keepBody L P Reach (D + 1) hN.2) hI⟩
  intro D hD1
  exact key _ D rfl hD1

/-! ## 4. The conditional skeleton (freeze §3) -/

/-- **T1 from the one-level rule — CONDITIONAL** on `StepStmt`, `KeepChildStmt`, `ServedShips0Stmt`, `NoTopStmt`
(`hLim` is kept as in the freeze; `limitStmt_proved` discharges it, see `t1_of_step'`). Not M2/M3 completion. -/
theorem t1_of_step {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hStep : StepStmt L P DataOk) (hKC : KeepChildStmt L P Reach)
    (hSS : ServedShips0Stmt L P Reach DataOk) (hNT : NoTopStmt L Reach) (hLim : LimitStmt L) :
    T1Stmt L P Reach DataOk := by
  intro hT c mctx cctx w w1 raw b Dg hc hS hr hb
  obtain ⟨hA, hj0⟩ := hS
  obtain ⟨q, hPq, hqd, hDq⟩ := hT.pkg c hc
  subst hqd
  have hdv : dv w = 0 := hj0.1.2.2
  obtain ⟨hI1, hK1⟩ := ih_all L P Reach DataOk hT hStep hKC hSS hNT hLim 1 (Nat.le_refl 1)
  have hjqc : JQC L.O (dv w) w := by rw [hdv]; exact hj0
  have hI1' : IHAt L P Reach (dv w + 1) := by rw [hdv]; exact hI1
  have hK1' : ChildKeepsInv L P Reach (dv w + 1) := by rw [hdv]; exact hK1
  have hdef : MachineDefines mctx mref cctx cref q.decl q.d.shape := hT.defines q.decl hc q hPq mctx cctx hA
  have hcl : MachineClosesAtA L.O mctx cctx q.decl q.d.shape := hT.closes q.decl hc q hPq mctx cctx hA
  have hsrv := hSS hT q mctx cctx w w1 raw Dg hc hPq hA hjqc (Or.inl hdv) hI1' hK1' hr
  have htaken : MachineTaken L mctx cctx (dv w + 1) q.decl q.d.shape raw Dg :=
    Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hA hr hdef hcl hjqc.1 (Or.inl hdv)
  obtain ⟨n, hTop, -⟩ :=
    hStep q mctx cctx w w1 raw b Dg hPq hDq hA hjqc hr hb hdef htaken (hT.dec q.decl hc q hPq) hsrv
  exact ⟨q, n, hPq, hTop⟩

/-- `t1_of_step` with `hLim` discharged by `limitStmt_proved`. Still CONDITIONAL on the other four premises. -/
theorem t1_of_step' {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hStep : StepStmt L P DataOk) (hKC : KeepChildStmt L P Reach)
    (hSS : ServedShips0Stmt L P Reach DataOk) (hNT : NoTopStmt L Reach) :
    T1Stmt L P Reach DataOk :=
  t1_of_step L P Reach DataOk hStep hKC hSS hNT (limitStmt_proved L)

end Tools.ShippingGen2
