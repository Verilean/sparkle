import Tools.ShippingFGCircuitS2kFinal
import Tools.ShippingFGCircuitS2mReach3
import Tools.ShippingFGCircuitS2lDec
set_option autoImplicit false
-- FG circuit pilot S2r: the combined final statement v2 (`HftFinalStmtOffCombined2`). Compared with S2k's `HftFinalStmtOffCombined`: (a) `hdec` is REMOVED (`hftCallDec_of_checked`, with `hfind` from the core run of the actual `hr` via `root_find_of_headAtOff`); (b) `hmiss` is replaced by the 7 premises of `hftCoreCloses_of_kidsR` (S2m, FG D.T-4m1..m7), the served children being `RealChildE` of the strengthened bundle `ropsR` (the same history). No `MissE`, no `KidStartEnv`, no all-world `MachineDefines`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §42.

namespace Tools.ShippingFGCircuitS2rFinal
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

/-! ## 1. the strengthened history bundle implies the plain one (for the `ShipsRes` side of `L`) -/

section Weak
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

theorem realChildA_weak {O' O : RefLawsAOps MkRefd mref cref} (hq : ∀ w, O'.quiet w → O.quiet w)
    (hadm : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O'.quiet mctx cctx → AdmCtx O.quiet mctx cctx)
    {c : Name} {r : Res} (h : RealChildA O' c r) : RealChildA O c r := by
  induction h with
  | run mctx cctx w w' adm cache synth quiet hr ih =>
    exact RealChildA.run mctx cctx w w' (hadm _ _ adm) (fun c' r' h' => ih c' r' h') synth (hq _ quiet) hr

theorem jqc_weak {O' O : RefLawsAOps MkRefd mref cref} (hq : ∀ w, O'.quiet w → O.quiet w)
    (hadm : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O'.quiet mctx cctx → AdmCtx O.quiet mctx cctx)
    {D : Nat} {w : Void IO.RealWorld} (h : JQC O' D w) : JQC O D w :=
  ⟨⟨hq _ h.1.1, h.1.2⟩, fun c r hm => realChildA_weak hq hadm (h.2 c r hm)⟩

end Weak

/-! ## 2. a slotless combinational callee's actual result ships — from the saved reads of its run, in the strengthened bundle -/

section Kid
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- `kid_shipsResE` (S2k) at a stronger bundle `O'` (`O'.quiet → L.O.quiet`, admissibility likewise): the child is a `RealChildE O'` and its result is a `ShipsRes L` -/
theorem kid_shipsResW {ι : Type} (L : Laws mref cref) (O' : RefLawsAOps MkRefd mref cref) (T' : RefLawsATele O'.quiet mref cref)
    (hq : ∀ w, O'.quiet w → L.O.quiet w)
    (hadmW : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O'.quiet mctx cctx → AdmCtx L.O.quiet mctx cctx) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
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
    {y : Res} (h : RealChildE O' (KidEv mref cref e) c y) : ShipsRes L P c y := by
  have h0 := realChildA_weak hq hadmW h.toA
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr ev =>
    obtain ⟨b, design⟩ := y
    obtain ⟨hRA, hprof⟩ := ev
    obtain ⟨M, D, w1, hcore, hpost, hran, hD0, -, -, -, hdes⟩ :=
      kidRunK O' T' adm d ok hbody hS hK hno hsl houts outTy ⟨⟨quiet, synth, rfl⟩, fun c' r' h' => (cache c' r' h').toA⟩ hr
        (fun _ => machineDefinesLinked_of_readerE hRA (headAt_of_profileOff c hcell hprof) (getEnvFrame_of_cellPrem hcell) hRead hgates)
        (closes mctx' cctx')
    have hran' : MachineTaken L mctx' cctx' (dv w + 1) (Pkg.comb cp).decl (Pkg.comb cp).d.shape M D := by
      show Tools.ShippingServedRealA.MachineRunJQC L.O mctx' cctx' (dv w + 1) cp.decl cp.d.shape M D
      rw [hdecl, hcd]
      obtain ⟨tenv, b', w9, w10, hrun9, hw9⟩ := hran
      exact ⟨tenv, b', w9, w10, hrun9, jqc_weak hq hadmW hw9⟩
    refine ⟨h0, ⟨Pkg.comb cp, 0, hP, hdecl, ?_⟩, ?_⟩
    · exact childShips_congr _ 0 b (by rw [hD0, hdes])
        (Tools.ShippingGen2.slotlessLeaf_childShips_of_ran L (Pkg.comb cp) hdata
          ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩ (by show cp.d.shape.insts = []; rw [hcd]; exact hno)
          (by show cp.d.shape.layout.slots = []; rw [hcd]; exact hsl) (hadmW _ _ adm) hpost hran' 0)
    · intro g hg
      rw [show (b, design).2 = design from rfl, hdes] at hg
      cases hg

end Kid

/-! ## 3. `htop` from the run, with the children on the strengthened HISTORY (`ropsR`), and `hdec` from the checked start -/

section Main
variable {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`htop` from the run, v2** (`hftTop_of_runH` of S2k): `hmiss` is replaced by the 7 premises of S2m (`hadm hdown hD hG hT hs h0`; the run and the served children are at `JQHR`, i.e. `RealChildE` of `ropsR`, one history), and `hdec` is no longer a premise: it is `hftCallDec_of_checked` with `hfind` from the core run `hrun` of the actual root run (`root_find_of_headAtOff` of the `hcell`-derived `HeadAtOff`). -/
theorem hftTop_of_runR (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hkgfacts : HftKidsGateFacts (envAt cref w))
    (hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx)
    (hdown : AdmDownR L.O (envAt cref w) w) (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleR L.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w) :
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
  have hkidH : ∀ y, RealChildE (ropsR L.O hcell (envAt cref w) w hdown hD hG) (KidEv mref cref (envAt cref w)) hftHttp y → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) hftHttp y := fun y h =>
    kid_shipsResW (lvl := lvl) (e := envAt cref w) L (ropsR L.O hcell (envAt cref w) w hdown hD hG) hT (fun _ h => h.1) (fun _ _ h => hdown _ _ h) hcell (nDecl := httpGetByte.machineData.nIn) httpGetByte.machineData httpGetByte.machine_ok httpGetByte.machine_body
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨_, rfl, rfl⟩ (by decide +kernel)
      hreadH hg.1 (fun mc cc => httpGetByte.machine_closes mc _ cc _) (GPt (ι := ι) lvl (envAt cref w)) cpH hPH hdeclH hdH
      (leafDataOk_comb cpH hdH hkH http_leafData) h
  have hkidT : ∀ y, RealChildE (ropsR L.O hcell (envAt cref w) w hdown hD hG) (KidEv mref cref (envAt cref w)) hftTlp y → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) hftTlp y := fun y h =>
    kid_shipsResW (lvl := lvl) (e := envAt cref w) L (ropsR L.O hcell (envAt cref w) w hdown hD hG) hT (fun _ h => h.1) (fun _ _ h => hdown _ _ h) hcell (nDecl := tlpCplByte.machineData.nIn) tlpCplByte.machineData tlpCplByte.machine_ok tlpCplByte.machine_body
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
      RealChildE (ropsR L.O hcell (envAt cref w) w hdown hD hG) (KidEv mref cref (envAt cref w)) (p'.d.shape.insts[k]).1 (mc, Dc) → ShipsRes L (GPt (ι := ι) lvl (envAt cref w)) (p'.d.shape.insts[k]).1 (mc, Dc) := by
    intro k hk mc Dc h
    rcases hk01 k hk with ⟨hn, -⟩ | ⟨hn, -⟩
    · rw [hn] at h ⊢; exact hkidH _ h
    · rw [hn] at h ⊢; exact hkidT _ h
  -- the machine run of the root, from the history world at the head of the run
  have hdv : dv w = 0 := hstart.2.1.2.2
  have ranH : MachineRunJQH (ropsR L.O hcell (envAt cref w) w hdown hD hG) (KidEv mref cref (envAt cref w)) mctx cctx (0 + 1) hftRoot synth_hftPcieOutByte.machineData.shape raw D₀ :=
    machineRunJQH_of_closesHOff (ropsR L.O hcell (envAt cref w) w hdown hD hG) hadm hrun (hdRun raw D₀ w1)
      (hft_closesAtH (ropsR L.O hcell (envAt cref w) w hdown hD hG) hT hadm hcell hreadH hreadT hg (missR h0 hs))
      ⟨⟨hstart.2.1.1, readsAt_self cref w, .start⟩, hstart.2.1.2⟩
  have ranR : MachineTaken L mctx cctx (dv w + 1) hftRoot synth_hftPcieOutByte.machineData.shape raw D₀ := by
    rw [hdv]
    obtain ⟨tenv, b', w9, w10, hrun9, hw9⟩ := ranH.toC
    exact ⟨tenv, b', w9, w10, hrun9, jqc_weak (O' := ropsR L.O hcell (envAt cref w) w hdown hD hG) (O := L.O) (fun _ h => h.1) (fun _ _ h => hdown _ _ h) hw9⟩
  have ranP : MachineTaken L mctx cctx (dv w + 1) p'.decl p'.d.shape raw D₀ := by rw [hdecl, hpd]; exact ranR
  have ranHP : MachineRunJQH (ropsR L.O hcell (envAt cref w) w hdown hD hG) (KidEv mref cref (envAt cref w)) mctx cctx (0 + 1) p'.decl p'.d.shape raw D₀ := by rw [hdecl, hpd]; exact ranH
  -- the trace with the served children shipping
  have hL : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L (GPt (ι := ι) lvl (envAt cref w))) p'.decl p'.d.shape raw D₀)
      p'.decl p'.d raw D₀ (fun _ => defaultDomain) p'.src p'.extS p'.extBS p'.lsrc :=
    traceLBX_mono (fun _ _ hX => servedP_mono hkid hX)
      (Pkg.traceX p' (soundX_served_E (ropsR L.O hcell (envAt cref w) w hdown hD hG) hT (missR h0 hs) hadm (by omega) ranHP))
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

/-! ## 4. the combined final statement v2 -/
section Final
open Tools.ShippingFGCircuitS1xNoRaw Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD

/-- **`HftFinalStmtOffCombined2`**: S2k's `HftFinalStmtOffCombined` with `hdec` REMOVED and `hmiss` replaced, at the same position, by the 7 run-local premises of S2m's `hftCoreCloses_of_kidsR` (FG D.T-4m6 `hadm`, m7 `hdown`, m1 `hD`, m2 `hG`, m3 `hT`, m4 `hs`, m5 `h0`). 19 explicit hypotheses (14 - 2 + 7). -/
def HftFinalStmtOffCombined2 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx)
    (hdown : AdmDownR L.O (envAt cref w) w) (hD : DRowEnvR L.O (envAt cref w) w)
    (hG : DiagEnvR L.O (envAt cref w) w) (hT : TeleR L.O (envAt cref w) w)
    (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w)
    (hkgfacts : HftKidsGateFacts (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffCombined2 (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffCombined2 Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hadm hdown hD hG hT hs h0 hkgfacts
  exact synth_hftPcieOutByte_finalOffLNL CV Ob hOb hlink L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD
    (hftTop_of_runR L lvl env₀ hstart hcell hchk hRdH hRdT hkgfacts hadm hdown hD hG hT hs h0)
    (hftCoreCloses_of_kidsR L hstart hcell hRdH hRdT (hftKidsGates_of_facts hkgfacts) hadm hdown hD hG hT hs h0)

theorem synth_hftPcieOutByte_finalOffCombined2_Z : HftFinalStmtOffCombined2 HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffCombined2 cdvZ _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffCombined2_Y : HftFinalStmtOffCombined2 HftObCDY cdvY := synth_hftPcieOutByte_finalOffCombined2 cdvY _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffCombined2_X : HftFinalStmtOffCombined2 HftObCDX cdvX := synth_hftPcieOutByte_finalOffCombined2 cdvX _ (fun _ h => h)

end Final

end Tools.ShippingFGCircuitS2rFinal

#print axioms Tools.ShippingFGCircuitS2rFinal.kid_shipsResW
#print axioms Tools.ShippingFGCircuitS2rFinal.hftTop_of_runR
#print axioms Tools.ShippingFGCircuitS2rFinal.synth_hftPcieOutByte_finalOffCombined2_Z
#print axioms Tools.ShippingFGCircuitS2rFinal.synth_hftPcieOutByte_finalOffCombined2_Y
#print axioms Tools.ShippingFGCircuitS2rFinal.synth_hftPcieOutByte_finalOffCombined2_X
