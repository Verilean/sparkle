import Tools.ShippingGen5ClosingRun
set_option autoImplicit false
-- Clean issue-linked build cr5v-f2e763d0 (exit 0, 757 jobs, standard axioms), scoped approved at f2e763d0.
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # DG-CLOSINGRUN next unit (scripts/gen5/DG_CLOSINGRUN_FREEZE_R4.md)

Depth-0 shared-block connection (`invAt_w5_of_runReadsAt_JQC`, `closingShared_of_run`, `ClosingRun0`, `closingRun0_of_run`) and
packaging (`closingRun_of_run_ga`, `ClosingPremises`, `closingRun_nonempty_of_premises`, projections). U-B / U-C are packaging,
not supply. OPEN: `hord`/`hrow`, `hGen` / `GeneratedAt`, non-vacuity, depth-0 `stop`, the T1 induction supplying `hIH`/`hKI`,
final T1/FG connection. `stop_of_run` of `Tools.ShippingGen5ClosingRun` is untouched. -/

namespace Tools.ShippingGen5ClosingRun2
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

def ClosingShared (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    InvAt L P Reach (dv w + 1) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children)) ∧
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc

theorem ClosingRun.closingShared {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingRun L P Reach mctx cctx X p Gen w w' raw D) :
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D := h.shared

theorem invAt_w5_of_runReadsAt_JQC (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    InvAt L P Reach (dv w + 1) w5 := by
  obtain ⟨s, w1, w2, w3, w4, wl, -, hh, hget, henv, henv', -⟩ := hr.chain
  have hw1 := coreHead_invAt0 L P Reach hA hw hc hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (dv w + 1))
    (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (dv w + 1))
    FramedA.env)) hw2 henv
  exact triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (dv w + 1))
    FramedA.env)) hw3 henv'

theorem closingShared_of_run (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
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
  obtain ⟨q, hPq, hqd, hDq⟩ := hT.pkg X hR
  have hpq : p = q := Option.some.inj (hP.symm.trans hPq)
  have hDp : DataOk p := by rw [hpq]; exact hDq
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
      (fun hf k hk => hord p hDp hf k hk)
  have htr := trace_of_soundX_at L P p hX
  rw [hdecl] at htr
  exact ⟨b, ci, envR, envR', w5, w6, t, t', d₀, children, hrr, hGen b ci envR envR' w5 w6 hrr, hw5, hmix, hcl', hmt, htr⟩

structure ClosingRun0 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run    : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  start0 : Start L mctx cctx w
  depth0 : dv w = 0
  shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D

theorem closingRun0_of_run (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
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
  exact ⟨hrun, hs, hd0, closingShared_of_run L P Reach DataOk hord hT hs.1 hR hP hw (Or.inl hd0) hIH hKI hrun Gen hGen⟩

theorem closingRun_of_run_ga (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
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
  closingRun_of_run L P Reach DataOk hrow hT hA hR hP hst hIH hKI h1 hrun _ hGA

structure ClosingPremises (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design)
    (Gen : ConstantInfo → Environment → Environment → Prop) : Prop where
  hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true
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

theorem closingRun_nonempty_of_premises {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {DataOk : Pkg ι dom → Prop} {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    (h : ClosingPremises L P Reach DataOk mctx cctx X p w w' raw D Gen) :
    Nonempty (ClosingRun L P Reach mctx cctx X p Gen w w' raw D) :=
  ⟨closingRun_of_run L P Reach DataOk h.hrow h.hT h.hA h.hR h.hP h.hst h.hIH h.hKI h.h1 h.hrun Gen h.hGen⟩

theorem gen_of_closingShared {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingShared L P Reach mctx cctx X p Gen w w' raw D) :
    ∃ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧ Gen ci envR envR' := by
  obtain ⟨b, ci, envR, envR', w5, w6, -, -, -, -, hr, hg, -⟩ := h
  exact ⟨b, ci, envR, envR', w5, w6, hr, hg⟩

theorem not_closingShared_false {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingShared L P Reach mctx cctx X p (fun _ _ _ => False) w w' raw D) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := h
  exact hg

end Tools.ShippingGen5ClosingRun2

#print axioms Tools.ShippingGen5ClosingRun2.ClosingRun.closingShared
#print axioms Tools.ShippingGen5ClosingRun2.invAt_w5_of_runReadsAt_JQC
#print axioms Tools.ShippingGen5ClosingRun2.closingShared_of_run
#print axioms Tools.ShippingGen5ClosingRun2.closingRun0_of_run
#print axioms Tools.ShippingGen5ClosingRun2.closingRun_of_run_ga
#print axioms Tools.ShippingGen5ClosingRun2.closingRun_nonempty_of_premises
#print axioms Tools.ShippingGen5ClosingRun2.gen_of_closingShared
#print axioms Tools.ShippingGen5ClosingRun2.not_closingShared_false
