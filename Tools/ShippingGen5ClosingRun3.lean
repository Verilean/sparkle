import Tools.ShippingGen5ClosingRun2
import Tools.ShippingGen3HrowGate
set_option autoImplicit false
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # Run-local `hord` / `hrow` (scripts/gen5/HORD_RUN_FREEZE.md; ledger rows A.P-26, C.CR-1)

`closingShared_of_run`, `closingRun0_of_run` (`Tools.ShippingGen5ClosingRun2`) and `closingRun_of_run`
(`Tools.ShippingGen5ClosingRun`) take, over EVERY package `q` with `DataOk q`, the origin row `hord` (or the row `hrow`).
Each proof uses it only at the run's own package `p`. The run's `RunReadsAt.shapeEq`
(`machineShape? … = some p.d.shape`) and the compiler's final gate (`machineShape?_noMemRow`, hrow-gate) give
`noMemRowS p.d.shape`, hence that use (`hord_of_rowS`). The `…R` theorems below are the same statements with the
`hord` / `hrow` binder removed; the proofs are copies with that one use replaced. The conclusions are unchanged.
No existing file, statement or definition is changed. OPEN (unchanged): `hGen` / `GeneratedAt`, `hIH` / `hKI`, non-vacuity,
depth-0 `stop`, T1 / FG. -/

namespace Tools.ShippingGen5ClosingRun3
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun Tools.ShippingGen5ClosingRun2

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The origin row of the run's own shape.** -/
theorem hord_of_runReadsAt {mctx : Meta.Context} {cctx : Core.Context} {X : Name}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6)
    (hf : shape.instFields = []) (k : Nat) (hk : k < shape.insts.length) :
    (shape.instOrigins.getD k .ord).child? = none :=
  Tools.ShippingGen2DataBridge.hord_of_rowS (Tools.ShippingGen3HrowGate.machineShape?_noMemRow hr.shapeEq) hf hk

/-- `closingShared_of_run` without `hord`. -/
theorem closingShared_of_runR (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D := by
  obtain ⟨q, hPq, hqd, -⟩ := hT.pkg X hR
  have hpq : p = q := Option.some.inj (hP.symm.trans hPq)
  have hdecl : p.decl = X := by rw [hpq]; exact hqd
  have hdef : MachineDefines mctx mref cctx cref X p.d.shape := hT.defines X hR p hP mctx cctx hA
  have hcl : MachineClosesAtA L.O mctx cctx X p.d.shape := hT.closes X hR p hP mctx cctx hA
  have hc' : dv w = 0 ∨ CacheInvA L.O (cv w) := hc.imp id (fun _ => hw.2)
  obtain ⟨b, ci, envR, envR', w5, w6, hrr, -⟩ :=
    runReads_of_run L.O hA hw.1 hc' hrun hdef hcl
  have hw5 := invAt_w5_of_runReadsAt_JQC L P Reach hA hw hc hrr
  obtain ⟨t, t', d₀, children, hmix, hcl', hmt⟩ : ∃ (t t' : Sparkle.IR.AST.Module) (d₀ : Design)
      (children : List Res),
      MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
      closeLets p.d.shape.layout.lets t = some t' ∧
      ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
       (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
        ChildrenShipsI L P Reach p.d.shape children)) := by
    obtain ⟨t, t', d₀, hmix, hcl', hmt⟩ :=
      synthesizeMachineCertified_runsS L P Reach hA hIH hKI hw5 (RunReadsAt.machineRun hrr)
    rcases hmt with ⟨hi, hm, hd⟩ | ⟨hne, children, hcc, hch⟩
    · exact ⟨t, t', d₀, [], hmix, hcl', Or.inl ⟨hi, rfl, hm, hd⟩⟩
    · exact ⟨t, t', d₀, children, hmix, hcl', Or.inr ⟨hne, hcc, hch⟩⟩
  have hX : SoundXAt (PortsServed L P p.decl p.d.shape t raw D) p.decl p.d.shape raw D := by
    rw [hdecl]
    exact soundX_ships_at L P Reach hmix hcl' hmt
      (fun k hk hn => hT.closed X hR p hP k hk hn)
      (fun hf k hk => hord_of_runReadsAt hrr hf k hk)
  have htr := trace_of_soundX_at L P p hX
  rw [hdecl] at htr
  exact ⟨b, ci, envR, envR', w5, w6, t, t', d₀, children, hrr, hGen b ci envR envR' w5 w6 hrr, hw5, hmix, hcl', hmt, htr⟩

/-- `closingRun0_of_run` without `hord`. -/
theorem closingRun0_of_runR (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D := by
  have hw : JQC L.O (dv w) w := by rw [hd0]; exact hs.2
  have h1 : dv w + 1 = 1 := by rw [hd0]
  rw [← h1] at hIH hKI
  exact ⟨hrun, hs, hd0, closingShared_of_runR L P Reach DataOk hT hs.1 hR hP hw (Or.inl hd0) hIH hKI hrun Gen hGen⟩

/-- `closingRun_of_run` (`Tools.ShippingGen5ClosingRun`) without `hrow`. -/
theorem closingRun_of_runR (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D := by
  obtain ⟨q, hPq, hqd, -⟩ := hT.pkg X hR
  have hpq : p = q := Option.some.inj (hP.symm.trans hPq)
  have hdecl : p.decl = X := by rw [hpq]; exact hqd
  have hdef : MachineDefines mctx mref cctx cref X p.d.shape := hT.defines X hR p hP mctx cctx hA
  have hcl : MachineClosesAtA L.O mctx cctx X p.d.shape := hT.closes X hR p hP mctx cctx hA
  obtain ⟨b, ci, envR, envR', w5, w6, hrr, -⟩ :=
    runReads_of_run L.O hA hst.1.1 (Or.inr hst.1.2) hrun hdef hcl
  have hw5 := invAt_w5_of_runReadsAt L P Reach hA hst hrr
  obtain ⟨t, t', d₀, children, hmix, hcl', hmt⟩ : ∃ (t t' : Sparkle.IR.AST.Module) (d₀ : Design)
      (children : List Res),
      MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
      closeLets p.d.shape.layout.lets t = some t' ∧
      ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
       (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
        ChildrenShipsI L P Reach p.d.shape children)) := by
    obtain ⟨t, t', d₀, hmix, hcl', hmt⟩ :=
      synthesizeMachineCertified_runsS L P Reach hA hIH hKI hw5 (RunReadsAt.machineRun hrr)
    rcases hmt with ⟨hi, hm, hd⟩ | ⟨hne, children, hcc, hch⟩
    · exact ⟨t, t', d₀, [], hmix, hcl', Or.inl ⟨hi, rfl, hm, hd⟩⟩
    · exact ⟨t, t', d₀, children, hmix, hcl', Or.inr ⟨hne, hcc, hch⟩⟩
  have hX : SoundXAt (PortsServed L P p.decl p.d.shape t raw D) p.decl p.d.shape raw D := by
    rw [hdecl]
    exact soundX_ships_at L P Reach hmix hcl' hmt
      (fun k hk hn => hT.closed X hR p hP k hk hn)
      (fun hf k hk => hord_of_runReadsAt hrr hf k hk)
  have htr := trace_of_soundX_at L P p hX
  rw [hdecl] at htr
  exact ⟨hrun, hA, hst, stop_of_run L P Reach hA h1 hKI hst hrun,
    b, ci, envR, envR', w5, w6, t, t', d₀, children, hrr, hGen b ci envR envR' w5 w6 hrr, hw5, hmix, hcl', hmt, htr⟩

/-- `closingRun_of_run_ga` without `hrow`. -/
theorem closingRun_of_run_gaR (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (GA : ConstantInfo → StructEnv → Pkg ι dom → Prop)
    (hGA : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
      GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') p) :
    ClosingRun L P Reach mctx cctx X p
      (fun ci envR envR' => GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (structEnv envR') p) w w' raw D :=
  closingRun_of_runR L P Reach DataOk hT hA hR hP hst hIH hKI h1 hrun _ hGA

/-- `ClosingPremises` without the `hrow` field. -/
structure ClosingPremisesR (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design)
    (Gen : ConstantInfo → Environment → Environment → Prop) : Prop where
  hT   : T1HypND L P Reach DataOk
  hA   : AdmCtx L.O.quiet mctx cctx
  hR   : Reach X
  hP   : P X = some p
  hst  : InvAt L P Reach (dv w) w
  hIH  : IHAt L P Reach (dv w + 1)
  hKI  : ChildKeepsInv L P Reach (dv w + 1)
  h1   : 1 ≤ dv w
  hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  hGen : ∀ b ci envR envR' w5 w6,
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'

theorem closingRun_nonempty_of_premisesR {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {DataOk : Pkg ι dom → Prop} {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    (h : ClosingPremisesR L P Reach DataOk mctx cctx X p w w' raw D Gen) :
    Nonempty (ClosingRun L P Reach mctx cctx X p Gen w w' raw D) :=
  ⟨closingRun_of_runR L P Reach DataOk h.hT h.hA h.hR h.hP h.hst h.hIH h.hKI h.h1 h.hrun Gen h.hGen⟩

end Tools.ShippingGen5ClosingRun3

#print axioms Tools.ShippingGen5ClosingRun3.hord_of_runReadsAt
#print axioms Tools.ShippingGen5ClosingRun3.closingShared_of_runR
#print axioms Tools.ShippingGen5ClosingRun3.closingRun0_of_runR
#print axioms Tools.ShippingGen5ClosingRun3.closingRun_of_runR
#print axioms Tools.ShippingGen5ClosingRun3.closingRun_of_run_gaR
#print axioms Tools.ShippingGen5ClosingRun3.closingRun_nonempty_of_premisesR
