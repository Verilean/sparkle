import Tools.ShippingGen5RunReads
import Tools.ShippingGen5T1ND
import Tools.ShippingGen2Served
import Tools.ShippingGen2Keep
import Tools.ShippingGen2KeepChild
import Tools.ShippingGen2DataBridge
set_option autoImplicit false
-- Built in the Pod (kjob lake build Tools.ShippingGen5ClosingRun, exit 0, standard axioms) on the tree of 0bdad261; clean issue-linked build crv-6f3c8ee5 exit 0 (755 jobs), scoped approved at 6f3c8ee5.
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # DG-CLOSINGRUN (scripts/gen5/DG_CLOSINGRUN_FREEZE.md)

`ClosingRun`: ONE shared `∃` block (`ci`, `envR`, `envR'`, `t`, `t'`, `d₀`, `children`) over the reads chain of the run
(`RunReadsAt`), the generation proposition `Gen` (a PARAMETER, `GeneratedAt` is not in the tree), the machine
synthesis result, and the served trace at `PortsServed`.

* (CR0) `RunReadsAt.machineRun`, (CR1) `coreHead_invAt0` + `invAt_w5_of_runReadsAt` (the head of the reads chain is peeled
  at `InvAt`; `core_reads_invAt0` is NOT used), (CR2) `soundX_ships_at`, (CR3) `trace_of_soundX_at`, (CR4) `stop_of_run`.
* `closingRun_of_run`: the assembly, CONDITIONAL on `hrow`, `hGen` and the premises named in its binders. INTERMEDIATE:
  it is not a T1 / FG / M5 completion, and the depth-0 (`dv w = 0`) start / stop are not supplied.

Nothing here claims `ClosingRun` is inhabited for a concrete run. -/

namespace Tools.ShippingGen5ClosingRun
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids
open Tools.ShippingGen2 Tools.ShippingGen5RunReads

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- The trace predicate: the trace's own `ids`/`cache` give the ports of THE mixed-synthesis result `t`, and serve every
instance with a shipping result. -/
def PortsServed (L : Laws mref cref) (P : Pkgs ι dom) (X : Name) (shape : MachineShape)
    (t raw : Sparkle.IR.AST.Module) (D : Design) :
    List FVarId → IO.Ref (ExprStructMap String) → Prop :=
  fun ids cache => machPorts X ids cache shape.binders = t.inputs ∧
    ServedP (ShipsRes L P) X shape raw D ids cache

/-- `Gen` is ABSTRACT in this unit (DG-GENP instantiates it); the SHARED `∃` block is kept exactly as DGEN rev2. -/
structure ClosingRun (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  adm   : AdmCtx L.O.quiet mctx cctx
  start : InvAt L P Reach (dv w) w
  stop  : InvAt L P Reach (dv w) w'
  shared : ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
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

/-! ## CR0 -/

/-- (CR0) The machine run of the reads chain, as a stand-alone run at `w5`. A projection of `RunReadsAt.chain`. -/
theorem _root_.Tools.ShippingGen5RunReads.RunReadsAt.machineRun {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool} {ci : ConstantInfo} {envR envR' : Environment}
    {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (h : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire envR e hint top named)
      (profLogIO b) X shape) mctx mref cctx cref w5 (some (raw, D)) w6 := by
  obtain ⟨s, w1, w2, w3, w4, wl, -, -, -, -, -, hm, -⟩ := h.chain
  exact hm

/-! ## CR1 -/

/-- The core head establishes `InvAt (D+1)` (the peel of `coreHead` at `InvAt`: `coreHead_jqcA` with `core_reads_invAt0`'s
`InvAt` steps; the start is `JQC D` and `D = 0 ∨ CacheShips`, as `core_reads_invAt0`). -/
theorem coreHead_invAt0 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx) {X : Name} {D : Nat}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQC L.O D w) (hc : D = 0 ∨ CacheShips L P Reach (cv w))
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1) :
    InvAt L P Reach (D + 1) w1 := by
  have h := hh
  unfold Tools.ShippingEntryReadsLinked.coreHead at h
  by_cases h0 : D = 0
  · subst h0
    replace hw := hw.1
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_JQ _ 0) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag L.O hA (stableA_JQ _ 0)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet L.O hA (stableA_JQ _ 0)) hw s3
    have hdD : d = 0 := hd.2.trans hd.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    simp only [↓reduceIte, beq_self_eq_true] at h
    peelP h; peelP h; peelP h; peelP h; peelP h; peelP h; peelP h
    peelF L.O hA (stableA_JQ _ 0) h hw; peelF L.O hA (stableA_JQ _ 0) h hw
    peelF L.O hA (stableA_JQ _ 0) h hw; peelF L.O hA (stableA_JQ _ 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleInv_clear L P Reach hA 0 (R := fun _ _ => False)) hw step
    clear step
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleInv_depthSet L P Reach hA 0 (0 + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw
  · replace hw : InvAt L P Reach D w := ⟨hw, hc.resolve_left h0⟩
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach D)
      (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag L.O hA (stableA_invAt L P Reach D)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet L.O hA (stableA_invAt L P Reach D)) hw s3
    have hdD : d = D := hd.2.trans hd.1.1.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    have h0' : ¬ ((d == 0) = true) := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleInv_depthSet L P Reach hA d (d + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨-, rfl⟩ := RunsTo.pure_world h
    exact hw

/-- (CR1) `InvAt (dv w + 1)` at the machine run's START world `w5` OF THE READS CHAIN (the chain's own `w5`, by peeling the
chain's `coreHead` and then the three framed reads; no existence-matching by determinism). -/
theorem invAt_w5_of_runReadsAt (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hst : InvAt L P Reach (dv w) w)
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    InvAt L P Reach (dv w + 1) w5 := by
  obtain ⟨s, w1, w2, w3, w4, wl, -, hh, hget, henv, henv', -⟩ := hr.chain
  have hw1 := coreHead_invAt0 L P Reach hA hst.1 (Or.inr hst.2) hh
  have hw2 := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (dv w + 1))
    (FramedA.constInfo _))) hw1 hget
  have hw3 := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (dv w + 1))
    FramedA.env)) hw2 henv
  exact triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (dv w + 1))
    FramedA.env)) hw3 henv'

/-! ## CR2 -/

/-- (CR2) The text of `soundX_ships_ran` after its `obtain`, with `t t' d₀ children` and their facts as ARGUMENTS (no
re-obtaining; no identification of two `t` by determinism). -/
theorem soundX_ships_at (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {tenv : Environment} {b : Bool} {X : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    {t t' : Sparkle.IR.AST.Module} {d₀ : Design} {children : List Res}
    (hmix : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) X shape.binders shape.body)
      (t, d₀))
    (hcl : closeLets shape.layout.lets t = some t')
    (hmt : (shape.insts = [] ∧ children = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
      (shape.insts ≠ [] ∧ CloseCalls shape t (closeMachine shape.layout t') d₀ children m d ∧
        ChildrenShipsI L P Reach shape children))
    (hreach : ∀ k (hk : k < shape.insts.length),
      (shape.instOrigins.getD k .ord).child? = none → Reach (shape.insts[k]).1)
    (hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
      (shape.instOrigins.getD k .ord).child? = none) :
    SoundXAt (PortsServed L P X shape t m d) X shape m d := by
  intro bsIn slotBs letBs hbs hlets positive slotKinds letKinds layW outsOk outsNodup
  have hmt0 : (shape.insts = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
      (shape.insts ≠ [] ∧ ∃ children,
        CloseCalls shape t (closeMachine shape.layout t') d₀ children m d) := by
    rcases hmt with ⟨hi, -, h, hd⟩ | ⟨hi, hcc, -⟩
    · exact Or.inl ⟨hi, h, hd⟩
    · exact Or.inr ⟨hi, children, hcc⟩
  refine synthesizeMachineCertified_soundX _ hmix hcl hmt0 ?_ hbs hlets positive slotKinds
    letKinds layW outsOk outsNodup
  intro ids cache regs lets wired hmp notInst
  have h0 : ∀ st ∈ (closeMachine shape.layout t').body, isInst st = false := fun st hs => by
    cases hi : isInst st
    · rfl
    · exact absurd (notInst st hs hi) id
  refine ⟨hmp, ?g, ?o⟩
  case o =>
    intro hfe1 k hk args mc st hargs hst hcs hmod
    rcases hmt with ⟨h0', _, _, _⟩ | ⟨_, hcc, hreal⟩
    · rw [h0'] at hk; exact absurd hk (Nat.not_lt_zero _)
    rcases hcc with ⟨_, hC⟩ | ⟨hfe0, _, _⟩
    case inr => exact absurd hfe1 hfe0
    rw [hmp] at hcs
    obtain ⟨y, hy, hmcy⟩ := Tools.ShippingChildServe.closeInsts_serves hC h0 hst hcs hmod
    have hyc := (Tools.ShippingChildServe.closeInsts_acyclic hC).2.2.2 y (List.mem_of_getElem? hy)
    obtain ⟨_, hkr⟩ := hreal
    obtain ⟨y', hy', hor⟩ := hkr k hk
    rw [hy] at hy'; cases hy'
    subst hmcy
    rcases hor with hmem | ⟨_, hS⟩
    · exact Or.inl ⟨y, hmem, rfl⟩
    · exact Or.inr ⟨y.2, hS (hreach k hk (hord1 hfe1 k hk)), hyc⟩
  case g =>
  intro hfe k hk mc iname argWs outs outWs hst hout hke hmod
  rcases hmt with ⟨h0, _, _, _⟩ | ⟨_, hcc, hreal⟩
  · rw [h0] at hk; exact absurd hk (Nat.not_lt_zero _)
  rcases hcc with ⟨hfe0, _⟩ | ⟨_, hG, hmemc⟩
  · exact absurd hfe0 hfe
  have hall := wired.2.1
  rw [hmp] at hall hout
  have hcr : "clk" ∉ t.inputs.map (·.name) ∧ "rst" ∉ t.inputs.map (·.name) :=
    ⟨fun h => (Tools.ShippingMachineTraceX.allocated_ne (hall _ h)).1 rfl, fun h => (Tools.ShippingMachineTraceX.allocated_ne (hall _ h)).2 rfl⟩
  obtain ⟨y, hy, hmcy⟩ := Tools.ShippingChildServe.closeInstsG_serves hG
    (fun st hs => by
      cases hi : isInst st
      · rfl
      · exact absurd (notInst st hs hi) id)
    hcr hk hst hout hke hmod
  have hyc := ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y (List.mem_of_getElem? hy)).2
  obtain ⟨_, hkr⟩ := hreal
  obtain ⟨y', hy', hor⟩ := hkr k hk
  rw [hy] at hy'; cases hy'
  subst hmcy
  rcases hor with hmem | ⟨_, hS⟩
  · exact Or.inl ⟨y, hmem, rfl⟩
  · cases hco : (shape.instOrigins.getD k .ord).child? with
    | none => exact Or.inr ⟨y.2, hS (hreach k hk hco), hyc⟩
    | some md =>
      have hy2 := hmemc k hk md hco
      rw [hy] at hy2
      exact Or.inl ⟨md, by first | exact hco | rfl, by rw [Option.some.inj hy2]⟩

/-! ## CR3 -/

/-- (CR3) `Pkg.traceX` at `PortsServed` (no new proof). All binders explicit. -/
theorem trace_of_soundX_at (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {t m : Sparkle.IR.AST.Module} {d : Design}
    (hX : SoundXAt (PortsServed L P p.decl p.d.shape t m d) p.decl p.d.shape m d) :
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P p.decl p.d.shape t m d) p.decl p.d m d dom
      p.src p.extS p.extBS p.lsrc :=
  Pkg.traceX p hX

/-! ## CR4 -/

/-- (CR4) `stop`: the nested core run keeps `InvAt (dv w)`. `core_tripleAInv` with `hbody` from `keepBody` at `dv w + 1`;
the `hbody` binder `D < sparkleSynthDepthLimit →` is not used (`keepBody` gives the keep at every depth), so there is NO
`hlim` premise. -/
theorem stop_of_run (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h1 : 1 ≤ dv w) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hst : InvAt L P Reach (dv w) w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w') :
    InvAt L P Reach (dv w) w' :=
  triple_runs (core_tripleAInv L P Reach hA (dv w) h1 X
    (fun {tenv} _ b ci isInst => keepBody L P Reach (dv w + 1) hKI mctx cctx hA X tenv b ci isInst)) hst hrun

/-! ## The connection theorem (CONDITIONAL, INTERMEDIATE) -/

/-- **`closingRun_of_run`** — CONDITIONAL on `hrow` (G-DATA, unsupplied), `hGen` (unsupplied: DG-GENP / DG-COVER / DG-ENV),
`h1` (`1 ≤ dv w`), `hIH`, `hKI` at `dv w + 1`, `hst`. INTERMEDIATE: not T1 / FG / M5 completion; depth 0 is not covered. -/
theorem closingRun_of_run (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
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
  obtain ⟨q, hPq, hqd, hDq⟩ := hT.pkg X hR
  have hpq : p = q := Option.some.inj (hP.symm.trans hPq)
  have hDp : DataOk p := by rw [hpq]; exact hDq
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
      (fun hf k hk => Tools.ShippingGen2DataBridge.hord_of_row (hrow p hDp) hf k hk)
  have htr := trace_of_soundX_at L P p hX
  rw [hdecl] at htr
  exact ⟨hrun, hA, hst, stop_of_run L P Reach hA h1 hKI hst hrun,
    b, ci, envR, envR', w5, w6, t, t', d₀, children, hrr, hGen b ci envR envR' w5 w6 hrr, hw5, hmix, hcl', hmt, htr⟩

end Tools.ShippingGen5ClosingRun

#print axioms Tools.ShippingGen5RunReads.RunReadsAt.machineRun
#print axioms Tools.ShippingGen5ClosingRun.coreHead_invAt0
#print axioms Tools.ShippingGen5ClosingRun.invAt_w5_of_runReadsAt
#print axioms Tools.ShippingGen5ClosingRun.soundX_ships_at
#print axioms Tools.ShippingGen5ClosingRun.trace_of_soundX_at
#print axioms Tools.ShippingGen5ClosingRun.stop_of_run
#print axioms Tools.ShippingGen5ClosingRun.closingRun_of_run
