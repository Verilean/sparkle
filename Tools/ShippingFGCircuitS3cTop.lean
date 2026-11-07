import Tools.ShippingFGCircuitS2rFinal
import Tools.ShippingFGCircuitS2sAdmS2nAdm
import Tools.ShippingFGCircuitS2sAdmS2kRun
import Tools.ShippingFGCircuitS2sAdmS2jKid
set_option autoImplicit false
-- FG circuit pilot S3c, part 1: the TOP route (hftTop_of_runR of S2r) on the context-predicate bundle, so that it needs no hadm and no hdown. The laws L : Laws stay as in v6 (ShipsRes L, MachineTaken L, oneOut_topShipsOff); the history bundle is ropsRX L.toX.O, whose context predicate is AdmCtx L.O.quiet itself, so the weakening back to L.O is the identity on contexts. No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md S52.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3cTop
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
open Tools.ShippingFGCircuitS2dKids Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS2jKid Tools.ShippingFGCircuitS2jTop
open Tools.ShippingFGCircuitS2hHist Tools.ShippingFGCircuitS2kRun
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt headAt_of_profileOff)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe
open Meta Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildInv (Res)
open Tools.ShippingFGCircuitFinal4 (EntryGates)

open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2kFinal (servedP_mono)
open Tools.ShippingFGCircuitS2lDec (hftCallDec_of_checked)
open Tools.ShippingChildCacheA (JQC CacheInvA)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingGen5Env (readsAt_self)

open Tools.ShippingFGCircuitS2hHist Tools.ShippingFGCircuitS2kRun Tools.ShippingFGCircuitS2jKid
open Tools.ShippingGen2 (Laws LawsX Start StartX)
open Tools.ShippingChildInvA Tools.ShippingChildCacheA
open Tools.ShippingFGCircuitS2sAdmS2nAdm

/-! ## 0.  and the weakening / bridge lemmas -/
/-- the existing laws as the context-predicate laws at  -/
def _root_.Tools.ShippingGen2.Laws.toX {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) : LawsX mref cref :=
  ⟨L.O.toX, L.T.toX⟩

section Weak
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem realChildAX_weak {O' : RefLawsAOpsX MkRefd mref cref} {O : RefLawsAOps MkRefd mref cref} (hq : ∀ w, O'.quiet w → O.quiet w)
    (hadm : ∀ (mctx : Meta.Context) (cctx : Core.Context), O'.adm mctx cctx → AdmCtx O.quiet mctx cctx)
    {c : Name} {r : Res} (h : RealChildAX O' c r) : RealChildA O c r := by
  induction h with
  | run mctx cctx w w' adm cache synth quiet hr ih =>
    exact RealChildA.run mctx cctx w w' (hadm _ _ adm) (fun c' r' h' => ih c' r' h') synth (hq _ quiet) hr

theorem jqcX_weak {O' : RefLawsAOpsX MkRefd mref cref} {O : RefLawsAOps MkRefd mref cref} (hq : ∀ w, O'.quiet w → O.quiet w)
    (hadm : ∀ (mctx : Meta.Context) (cctx : Core.Context), O'.adm mctx cctx → AdmCtx O.quiet mctx cctx)
    {D : Nat} {w : Void IO.RealWorld} (h : JQCX O' D w) : JQC O D w :=
  ⟨⟨hq _ h.1.1, h.1.2⟩, fun c r hm => realChildAX_weak hq hadm (h.2 c r hm)⟩

/-- the plain cache invariant is the context-predicate one at  -/
theorem realChildA_toX {O : RefLawsAOps MkRefd mref cref} {c : Name} {r : Res} (h : RealChildA O c r) : RealChildAX O.toX c r := by
  induction h with
  | run mctx cctx w w' adm cache synth quiet hr ih =>
    exact RealChildAX.run mctx cctx w w' adm (fun c' r' h' => ih c' r' h') synth quiet hr

theorem jqc_toX {O : RefLawsAOps MkRefd mref cref} {D : Nat} {w : Void IO.RealWorld} (h : JQC O D w) : JQCX O.toX D w :=
  ⟨h.1, fun c r hm => realChildA_toX (h.2 c r hm)⟩

end Weak

section Kid
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- `kid_shipsResE` (S2k) at a stronger bundle `O'` (`O'.quiet → L.O.quiet`, admissibility likewise): the child is a `RealChildEX O'` and its result is a `ShipsRes L` -/
theorem kid_shipsResWX {ι : Type} (L : Laws mref cref) (O' : RefLawsAOpsX MkRefd mref cref) (T' : RefLawsATeleX O'.quiet O'.adm mref cref)
    (hq : ∀ w, O'.quiet w → L.O.quiet w)
    (hadmW : ∀ (mctx : Meta.Context) (cctx : Core.Context), O'.adm mctx cctx → AdmCtx L.O.quiet mctx cctx) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hRead : RootReader lvl e c d) (hgates : EntryGates e c)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), MachineCloses mctx' mref cctx' cref c d.shape)
    (P : Pkgs ι (fun _ => Sparkle.Core.Domain.defaultDomain)) (cp : CombPkg ι (fun _ => Sparkle.Core.Domain.defaultDomain))
    (hP : P c = some (Pkg.comb cp)) (hdecl : cp.decl = c) (hcd : cp.d = d)
    (hdata : LeafDataOk (Pkg.comb cp))
    {y : Res} (h : RealChildEX O' (KidEv mref cref e) c y) : ShipsRes L P c y := by
  have h0 := realChildAX_weak hq hadmW h.toA
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr ev =>
    obtain ⟨b, design⟩ := y
    obtain ⟨hRA, hprof⟩ := ev
    obtain ⟨M, D, w1, hcore, hpost, hran, hD0, -, -, -, hdes⟩ :=
      kidRunKX O' T' adm d ok hbody hS hK hno hsl houts outTy ⟨⟨quiet, synth, rfl⟩, fun c' r' h' => (cache c' r' h').toA⟩ hr
        (fun _ => machineDefinesLinked_of_readerE hRA (headAt_of_profileOff c hcell hprof) (getEnvFrame_of_cellPrem hcell) hRead hgates)
        (closes mctx' cctx')
    have hran' : MachineTaken L mctx' cctx' (dv w + 1) (Pkg.comb cp).decl (Pkg.comb cp).d.shape M D := by
      show Tools.ShippingServedRealA.MachineRunJQC L.O mctx' cctx' (dv w + 1) cp.decl cp.d.shape M D
      rw [hdecl, hcd]
      obtain ⟨tenv, b', w9, w10, hrun9, hw9⟩ := hran
      exact ⟨tenv, b', w9, w10, hrun9, jqcX_weak hq hadmW hw9⟩
    refine ⟨h0, ⟨Pkg.comb cp, 0, hP, hdecl, ?_⟩, ?_⟩
    · exact childShips_congr _ 0 b (by rw [hD0, hdes])
        (Tools.ShippingGen2.slotlessLeaf_childShips_of_ran L (Pkg.comb cp) hdata
          ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩ (by show cp.d.shape.insts = []; rw [hcd]; exact hno)
          (by show cp.d.shape.layout.slots = []; rw [hcd]; exact hsl) (hadmW _ _ adm) hpost hran' 0)
    · intro g hg
      rw [show (b, design).2 = design from rfl, hdes] at hg
      cases hg

end Kid

section Main
variable {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`htop` from the run, X version** (`hftTop_of_runR` of S2r on the context-predicate bundle): the premises are `hstart hcell hchk hreadH hreadT hkgfacts` and the five run-local hypotheses `hD hG hT hs h0` in their X forms (`DRowEnvRX`, `DiagEnvRX`, `TeleRX`, `ProfStepRX` at `L.toX.O`, and `ProfOffW`); the run and the served children are at the history bundle `ropsRX L.toX.O`, whose context predicate is `AdmCtx L.O.quiet` itself, so there is no `hadm` and no `hdown`. `hdec` is not a premise: it is `hftCallDec_of_checked` with `hfind` from the core run `hrun` of the actual root run (`root_find_of_headAtOff` of the `hcell`-derived `HeadAtOff`). -/
theorem hftTop_of_runRX (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hkgfacts : HftKidsGateFacts (envAt cref w))
    (hD : DRowEnvRX L.toX.O (envAt cref w) w)
    (hG : DiagEnvRX L.toX.O (envAt cref w) w) (hT : TeleRX L.toX.O (envAt cref w) w)
    (hs : ProfStepRX L.toX.O w) (h0 : ProfOffW mref cref w) :
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
  -- the children's actual results ship (from the reads their own run saved)
  have hkidH : ∀ y, RealChildEX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) hftHttp y → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) hftHttp y := fun y h =>
    kid_shipsResWX (lvl := lvl) (e := envAt cref w) L (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hT (fun _ h => h.1) (fun _ _ h => h) hcell (nDecl := httpGetByte.machineData.nIn) httpGetByte.machineData httpGetByte.machine_ok httpGetByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hreadH hg.1 (fun mc cc => httpGetByte.machine_closes mc _ cc _) (GPt (ι := ι) lvl (envAt cref w)) cpH hPH hdeclH hdH
      (leafDataOk_comb cpH hdH hkH http_leafData) h
  have hkidT : ∀ y, RealChildEX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) hftTlp y → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) hftTlp y := fun y h =>
    kid_shipsResWX (lvl := lvl) (e := envAt cref w) L (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hT (fun _ h => h.1) (fun _ _ h => h) hcell (nDecl := tlpCplByte.machineData.nIn) tlpCplByte.machineData tlpCplByte.machine_ok tlpCplByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hreadT hg.2 (fun mc cc => tlpCplByte.machine_closes mc _ cc _) (GPt (ι := ι) lvl (envAt cref w)) cpT hPT hdeclT hdT
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
      RealChildEX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) (p'.d.shape.insts[k]).1 (mc, Dc) → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) (p'.d.shape.insts[k]).1 (mc, Dc) := by
    intro k hk mc Dc h
    rcases hk01 k hk with ⟨hn, -⟩ | ⟨hn, -⟩
    · rw [hn] at h ⊢; exact hkidH _ h
    · rw [hn] at h ⊢; exact hkidT _ h
  -- the machine run of the root, from the history world at the head of the run
  have hdv : dv w = 0 := hstart.2.1.2.2
  have ranH : MachineRunJQHX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) mctx cctx (0 + 1) hftRoot synth_hftPcieOutByte.machineData.shape raw D₀ :=
    machineRunJQH_of_closesHOffX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hstart.1 hrun (hdRun raw D₀ w1)
      (hft_closesAtHX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hT hstart.1 hcell hreadH hreadT hg (missRX h0 hs))
      ⟨⟨hstart.2.1.1, readsAt_self cref w, .start⟩, hstart.2.1.2⟩
  have ranR : MachineTaken L mctx cctx (dv w + 1) hftRoot synth_hftPcieOutByte.machineData.shape raw D₀ := by
    rw [hdv]
    obtain ⟨tenv, b', w9, w10, hrun9, hw9⟩ := ranH.toCX
    exact ⟨tenv, b', w9, w10, hrun9, jqcX_weak (O' := ropsRX L.toX.O hcell (envAt cref w) w hD hG) (O := L.O) (fun _ h => h.1) (fun _ _ h => h) hw9⟩
  have ranP : MachineTaken L mctx cctx (dv w + 1) p'.decl p'.d.shape raw D₀ := by rw [hdecl, hpd]; exact ranR
  have ranHP : MachineRunJQHX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) (KidEv mref cref (envAt cref w)) mctx cctx (0 + 1) p'.decl p'.d.shape raw D₀ := by rw [hdecl, hpd]; exact ranH
  -- the trace with the served children shipping
  have hL : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L (GPt (ι := ι) lvl (envAt cref w))) p'.decl p'.d.shape raw D₀)
      p'.decl p'.d raw D₀ (fun _ => defaultDomain) p'.src p'.extS p'.extBS p'.lsrc :=
    traceLBX_mono (fun _ _ hX => servedP_mono hkid hX)
      (Pkg.traceX p' (soundX_served_EX (ropsRX L.toX.O hcell (envAt cref w) w hD hG) hT (missRX h0 hs) hstart.1 (by omega) ranHP))
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
    (by rw [hdecl]; exact hrun) hpost (by rw [hdecl, hpd]; exact hdRun raw D₀ w1) ranP (hftCallDec_of_checked (ι := ι) (mref := mref) lvl env₀ hchk (root_find_of_headAtOff hhead hrun) hreadH hreadT p' hP) hL hW 0
  exact ⟨0 + 1, by rw [← hdecl]; exact key⟩

end Main

end Tools.ShippingFGCircuitS3cTop

#print axioms Tools.ShippingFGCircuitS3cTop.kid_shipsResWX
#print axioms Tools.ShippingFGCircuitS3cTop.hftTop_of_runRX
