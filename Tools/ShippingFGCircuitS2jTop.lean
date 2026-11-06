import Tools.ShippingFGCircuitS2jKid
import Tools.ShippingFGCircuitS2jCopy
set_option autoImplicit false
-- FG circuit pilot S2j: `htop` (the non-leaf root's `TopShips` on the core design) from the same run. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §36.

namespace Tools.ShippingFGCircuitS2jTop
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Tools.ShippingFGCircuitS2dKids Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS2jKid
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

/-! ## 1. the served evidence upgraded: `ServedRealA` → `ServedP (ShipsRes L P)`, and the trace is monotone in its served predicate -/

theorem servedP_of_real {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {dsn : Sparkle.IR.AST.Design}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hkid : ∀ k (hk : k < shape.insts.length) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design),
      RealChildA L.O (shape.insts[k]).1 (mc, Dc) → ShipsRes L P (shape.insts[k]).1 (mc, Dc))
    (h : Tools.ShippingServedRealA.ServedRealA L.O declName shape m dsn ids cache) :
    ServedP (ShipsRes L P) declName shape m dsn ids cache := by
  refine ⟨?_, ?_⟩
  · intro hf k hk mc iname argWs outs outWs h1 h2 h3 h4
    rcases h.1 hf k hk mc iname argWs outs outWs h1 h2 h3 h4 with h5 | ⟨Dc, h5, h6⟩
    · exact Or.inl h5
    · exact Or.inr ⟨Dc, hkid k hk mc Dc h5, h6⟩
  · intro hf k hk args mc st h1 h2 h3 h4
    rcases h.2 hf k hk args mc st h1 h2 h3 h4 with h5 | ⟨Dc, h5, h6⟩
    · exact Or.inl h5
    · exact Or.inr ⟨Dc, hkid k hk mc Dc h5, h6⟩

theorem traceLBX_mono {X Y : List FVarId → IO.Ref (ExprStructMap String) → Prop} {declName : Name} {d : Tools.ShippingMachineAuto.MachineData}
    {m : Sparkle.IR.AST.Module} {dsn : Sparkle.IR.AST.Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) →
      Nat → Sparkle.Core.Signal.Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (hXY : ∀ ids cache, X ids cache → Y ids cache)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX X declName d m dsn dom src ext extB lsrc) :
    Tools.ShippingMachineTraceX.MachineTraceLBX Y declName d m dsn dom src ext extB lsrc := by
  obtain ⟨ids, a, b, cache, regs, c, e, lets, f, wired, hX, H⟩ := h
  exact ⟨ids, a, b, cache, regs, c, e, lets, f, wired, hXY _ _ hX, H⟩

/-! ## 2. the root's and the children's data (kernel facts about the `machineData` literals) -/

theorem hft_memData : (synth_hftPcieOutByte.machineData.ok && synth_hftPcieOutByte.machineData.callsOk 5 &&
    decide (synth_hftPcieOutByte.machineData.ss.length = synth_hftPcieOutByte.machineData.shape.layout.slots.length) &&
    decide (∀ o ∈ synth_hftPcieOutByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width) &&
    decide (∀ b ∈ synth_hftPcieOutByte.machineData.shape.binders.drop 5, b.2 ≠ .domain)) = true := by decide +kernel
theorem hft_ord : ∀ k, k < synth_hftPcieOutByte.machineData.shape.insts.length →
    (synth_hftPcieOutByte.machineData.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none := by decide +kernel
theorem hft_instFields : synth_hftPcieOutByte.machineData.shape.instFields = [] := by decide +kernel
theorem hft_slots_ne : synth_hftPcieOutByte.machineData.shape.layout.slots ≠ [] := by decide +kernel
theorem hft_insts_ne : synth_hftPcieOutByte.machineData.shape.insts ≠ [] := by decide +kernel
theorem http_ss0 : httpGetByte.machineData.ss = [] := http_ss
theorem http_leafData : (httpGetByte.machineData.ok && httpGetByte.machineData.callsOk (Tools.ShippingGen5Sem.kDOf httpGetByte.machineData) &&
    decide (httpGetByte.machineData.ss.length = httpGetByte.machineData.shape.layout.slots.length) &&
    decide (∀ o ∈ httpGetByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width)) = true := by decide +kernel
theorem tlp_leafData : (tlpCplByte.machineData.ok && tlpCplByte.machineData.callsOk (Tools.ShippingGen5Sem.kDOf tlpCplByte.machineData) &&
    decide (tlpCplByte.machineData.ss.length = tlpCplByte.machineData.shape.layout.slots.length) &&
    decide (∀ o ∈ tlpCplByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width)) = true := by decide +kernel
/-- the width of the root's call-result binder of call 0 (`httpGetByte`) is the child's one output width -/
theorem hft_width0 : ∀ o ∈ httpGetByte.machineData.shape.layout.outs,
    (synth_hftPcieOutByte.machineData.shape.binders[5 + 0]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some o.ty.bitWidth := by decide +kernel
theorem hft_width1 : ∀ o ∈ tlpCplByte.machineData.shape.layout.outs,
    (synth_hftPcieOutByte.machineData.shape.binders[5 + 1]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some o.ty.bitWidth := by decide +kernel

/-! ## 3. the run-local supply of `htop` -/

/-- **`hdec`** (NAMED HYPOTHESIS, FG D.D-4 `G-CALLDEC` / T2-TIE; package-level, no run): every call `k` of the root's package has its callee's package in the table and the call decoding `CallDec`.
It splits (docs §36.3) into `GenExtAtCall` (derivable: `hDT1_of_genGP`), `CallOutRange` (open), the field row (from the run's `CallStmt` and the callee's `ShipsRes`) and static data checks (kernel). -/
def HftCallDec {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftRoot = some p →
    ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, GPt (ι := ι) lvl env (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k

section Main
variable {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`htop` from the run** -/
theorem hftTop_of_run (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hkenv : HftKidsStartEnv L.O (envAt cref w)) (hkgfacts : HftKidsGateFacts (envAt cref w))
    (hdec : HftCallDec (ι := ι) lvl (envAt cref w)) :
    ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p := by
  intro p hP hdRun raw D₀ w1 hrun hpe
  have hg : HftKidsGates (envAt cref w) := hftKidsGates_of_facts hkgfacts
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hrun)
  obtain ⟨E, hEnt, hsh, hdat⟩ := hRead
  obtain ⟨g, hgr, hgd⟩ := canon_row (lvl := lvl) (env := envAt cref w) root_wf hsh hdat
  obtain ⟨Eh, hEh, hshh, hdath⟩ := id hreadH
  obtain ⟨gh, hgh, hghd⟩ := canon_row (lvl := lvl) (env := envAt cref w) http_wf hshh hdath
  obtain ⟨Et, hEt, hsht, hdatt⟩ := id hreadT
  obtain ⟨gt, hgt, hgtd⟩ := canon_row (lvl := lvl) (env := envAt cref w) tlp_wf hsht hdatt
  have hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : Tools.ShippingGen5Sem.GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) Ec (structEnv (envAt cref w))),
      Tools.ShippingGen5Acc.entry₀ (envAt cref w) c = some Ec ∧ canonGD lvl (envAt cref w) Ec = some gc ∧ gc.d.shape.insts = [] := by
    intro c hc
    rw [hgd, root_insts] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Eh, gh, hEh, hgh, by rw [hghd]; exact http_leaf⟩
    · exact ⟨Et, gt, hEt, hgt, by rw [hgtd]; exact tlp_leaf⟩
  obtain ⟨p', hP', hdecl, hpd, hkp⟩ := genGP_root_kids (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) hEnt hgr hkids
  obtain rfl : p' = p := Option.some.inj (hP'.symm.trans hP)
  rw [hgd] at hpd
  have hkD : p'.kD = 5 := by rw [hkp, hgd]; exact root_kD
  -- the two children's packages are `.comb` rows of the same table
  obtain ⟨cpH, hPH, hdeclH, hdH, hkH⟩ := kid_pkg (ι := ι) lvl (envAt cref w) hreadH http_wf http_leaf http_ss
  obtain ⟨cpT, hPT, hdeclT, hdT, hkT⟩ := kid_pkg (ι := ι) lvl (envAt cref w) hreadT tlp_wf tlp_leaf tlp_ss
  -- the children's actual results ship
  have hkidH : ∀ y, RealChildA L.O hftHttp y → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) hftHttp y := fun y h =>
    kid_shipsRes (lvl := lvl) (e := envAt cref w) L hcell (nDecl := httpGetByte.machineData.nIn) httpGetByte.machineData httpGetByte.machine_ok httpGetByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hreadH hg.1 hkenv.1 (fun mc cc => httpGetByte.machine_closes mc _ cc _) (GPt (ι := ι) lvl (envAt cref w)) cpH hPH hdeclH hdH
      (leafDataOk_comb cpH hdH hkH http_leafData) h
  have hkidT : ∀ y, RealChildA L.O hftTlp y → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) hftTlp y := fun y h =>
    kid_shipsRes (lvl := lvl) (e := envAt cref w) L hcell (nDecl := tlpCplByte.machineData.nIn) tlpCplByte.machineData tlpCplByte.machine_ok tlpCplByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hreadT hg.2 hkenv.2 (fun mc cc => tlpCplByte.machine_closes mc _ cc _) (GPt (ι := ι) lvl (envAt cref w)) cpT hPT hdeclT hdT
      (leafDataOk_comb cpT hdT hkT tlp_leafData) h
  -- the names of the calls
  have hmapP : p'.d.shape.insts.map (·.1) = [hftHttp, hftTlp] := by rw [hpd]; exact root_insts
  have hk01 : ∀ (k : Nat) (hk : k < p'.d.shape.insts.length),
      ((p'.d.shape.insts[k]).1 = hftHttp ∧ k = 0) ∨ ((p'.d.shape.insts[k]).1 = hftTlp ∧ k = 1) := by
    intro k hk
    have hlen : p'.d.shape.insts.length = 2 := by have := congrArg List.length hmapP; simpa using this
    have h1 := congrArg (fun l => l[k]?) hmapP
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk] at h1
    have hk2 : k < 2 := hlen ▸ hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · left; exact ⟨Option.some.inj (by simpa using h1), rfl⟩
    · right; exact ⟨Option.some.inj (by simpa using h1), rfl⟩
  have hkid : ∀ (k : Nat) (hk : k < p'.d.shape.insts.length) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design),
      RealChildA L.O (p'.d.shape.insts[k]).1 (mc, Dc) → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) (p'.d.shape.insts[k]).1 (mc, Dc) := by
    intro k hk mc Dc h
    rcases hk01 k hk with ⟨hn, -⟩ | ⟨hn, -⟩
    · rw [hn] at h ⊢; exact hkidH _ h
    · rw [hn] at h ⊢; exact hkidT _ h
  -- the machine run of the root
  have hdv : dv w = 0 := hstart.2.1.2.2
  have ranR : MachineTaken L mctx cctx (dv w + 1) hftRoot synth_hftPcieOutByte.machineData.shape raw D₀ := by
    have := machineRunJQC_of_closesCOff L.O hstart.1 hrun (hdRun raw D₀ w1)
      (hft_closesAtK L.O L.T hstart.1 hcell hreadH hreadT hg hkenv) hstart.2.1 (Or.inl rfl)
    rw [hdv]; exact this
  have ranP : MachineTaken L mctx cctx (dv w + 1) p'.decl p'.d.shape raw D₀ := by rw [hdecl, hpd]; exact ranR
  -- the trace with the served children shipping
  have hL : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L (GPt (ι := ι) lvl (envAt cref w))) p'.decl p'.d.shape raw D₀)
      p'.decl p'.d raw D₀ (fun _ => defaultDomain) p'.src p'.extS p'.extBS p'.lsrc :=
    traceLBX_mono (fun _ _ hX => servedP_of_real L _ hkid hX) (Pkg.trace L.O L.T hstart.1 p' ranP)
  -- the one-output widths
  have hW : ∀ k, OneOutWidth (GPt (ι := ι) lvl (envAt cref w)) p' k := by
    intro k hk q hq o ho
    rw [hpd, hkD]
    rcases hk01 k hk with ⟨hn, rfl⟩ | ⟨hn, rfl⟩
    · rw [hn] at hq
      obtain rfl : q = Pkg.comb cpH := (Option.some.inj ((show GPt (ι := ι) lvl (envAt cref w) hftHttp = some (Pkg.comb cpH) from hPH).symm.trans hq)).symm
      exact hft_width0 o (by have : (Pkg.comb cpH).d.shape.layout.outs = [o] := ho; rw [show (Pkg.comb cpH).d = cpH.d from rfl, hdH] at this; rw [this]; exact List.mem_singleton_self o)
    · rw [hn] at hq
      obtain rfl : q = Pkg.comb cpT := (Option.some.inj ((show GPt (ι := ι) lvl (envAt cref w) hftTlp = some (Pkg.comb cpT) from hPT).symm.trans hq)).symm
      exact hft_width1 o (by have : (Pkg.comb cpT).d.shape.layout.outs = [o] := ho; rw [show (Pkg.comb cpT).d = cpT.d from rfl, hdT] at this; rw [this]; exact List.mem_singleton_self o)
  have hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) :=
    hpe.imp And.left And.left
  have key := oneOut_topShipsOff L (GPt (ι := ι) lvl (envAt cref w)) p' (mctx := mctx) (cctx := cctx) (w := w) (w1 := w1) (raw := raw) (b := b) (D := D₀)
    (by unfold MemParentDataOk MemParentDataOkB; rw [hpd, hkD]; exact hft_memData)
    (fun k hk => by rw [hpd]; exact hft_ord k (by rw [← hpd]; exact hk))
    (by rw [hpd]; exact hft_insts_ne) (by rw [hpd]; exact hft_instFields) (by rw [hpd]; exact hft_slots_ne) hstart.1
    (by rw [hdecl]; exact hrun) hpost (by rw [hdecl, hpd]; exact hdRun raw D₀ w1) ranP (hdec p' hP) hL hW 0
  exact ⟨0 + 1, by rw [← hdecl]; exact key⟩

end Main

end Tools.ShippingFGCircuitS2jTop

#print axioms Tools.ShippingFGCircuitS2jTop.servedP_of_real
#print axioms Tools.ShippingFGCircuitS2jTop.traceLBX_mono
#print axioms Tools.ShippingFGCircuitS2jTop.hft_width1
#print axioms Tools.ShippingFGCircuitS2jTop.hftTop_of_run
