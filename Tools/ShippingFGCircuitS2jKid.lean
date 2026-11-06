import Tools.ShippingFGCircuitS2dKids
import Tools.ShippingGen2SlotlessLeaf
import Tools.ShippingFGCircuitS2jCopy
import Tools.ShippingFGCircuitS1uSrc
set_option autoImplicit false
-- FG circuit pilot S2j, unit 2: a combinational leaf child's `ShipsRes` from its own run (the children of the non-leaf root). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. docs/FG-CIRCUIT-PILOT.md §36.

/-! ## `ChildShips` of a slotless leaf from the machine run alone (no all-world `MachineDefines`) -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildBndCore (cv dv)
open Sparkle.Core Sparkle.Core.Domain
variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- `slotlessLeaf_ships`' `ChildShips` conjunct with the (unused) all-world `MachineDefines` and `JQC` and the core run dropped: the proof body is `slotlessLeaf_ships`' verbatim -/
theorem slotlessLeaf_childShips_of_ran (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : LeafDataOk p) (hext : ExtInS p) (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D) (n : Nat) :
    ChildShips p n b D := by
  obtain ⟨hok, hco, hSS, houtTy⟩ := hdata.rows
  have htake := leaf_take p.d p.kD hok hco hnoI
  have hL := (Pkg.trace L.O L.T hA p ran).toLB
  have hclosed0 := slotless_closed_ofRun L p (b := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
    hdata hnoI hsl0 hA (Or.inl rfl) ran
  have hclosedB := slotless_closed_ofRun L p hdata hnoI hsl0 hA hpost ran
  have hinA := slotless_inputs_alloc_ofRun L p hdata hnoI hsl0 htake ran
  exact slotlessLeaf_childShips_of_LB p hL hext hnoI hsl0 hok hSS houtTy htake hclosed0 hclosedB hinA hpost n

end Tools.ShippingGen2

namespace Tools.ShippingFGCircuitS2jKid
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingMachineChildComb Tools.ShippingTransitionClosed Tools.ShippingCallsGate
open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingGen2 Tools.ShippingChildBndCore Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitLinked
open Tools.ShippingFGCircuitS1iHead (HeadAt)
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt headAt_of_profileOff)
open Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitFinal4
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1hFrame (getEnvFrame_of_cellPrem)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- (S2j copy of `machineChild_ifaceK`, conclusion extended by the core run, the machine run and `D.modules = []`) **`machineChild_ifaceA` with the all-world `MachineDefines` replaced by the run-local linked boundary** (the machine run is taken by `machine_run_of_coreC` on the run's own core chain; `entry` is asked only of THIS child run's core run, at its start world `w`) ( `synthesizeMachineCertified_runsA`; the rest of the proof is the old one) -/
theorem kidRunK (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQC O (dv w) w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : ∀ {M : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 →
      MachineDefinesLinked mctx mref cctx cref c d.shape w M D w1)
    (closes : MachineCloses mctx mref cctx cref c d.shape) :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 ∧
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      Tools.ShippingServedRealA.MachineRunJQC O mctx cctx (dv w + 1) c d.shape M D ∧ D.modules = [] ∧
      (ChildComb b ∧
        b.inputs.length = ((d.shape.binders.take nDecl).filter fun x => x.2 != .domain).length ∧
        b.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ design.modules = []) := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ :=
    machine_run_of_coreC O hA hcore (entry hcore) hw.1 (Or.inr hw.2)
  have hne := closes (profLogIO bb) w9 r w10 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ :=
    synthesizeMachineCertified_runsA O (bodyStepC_of_tele O T) hA (htr_of_tele O hA T (dv w) tenv) hw9 hrun9
  rcases hmt with ⟨-, hMeq, hDeq⟩ | ⟨hne', -⟩
  rotate_left
  · exact absurd hno hne'
  simp only [MachineData.gateCallsOk, MachineData.callsOk, Bool.and_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at hS
  obtain ⟨⟨⟨⟨⟨⟨hnIn, hargs⟩, hfields⟩, hcoreR⟩, hslots⟩, hdomB⟩, -⟩ := hS
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, _, _, _, outsOk, outsNodup, hwf, hb, hv,
    _, _, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  obtain ⟨hfitL, -⟩ := scoped_fit d.letBs d.letFields _ hscoped
  have hlsLen : d.letFields.length = d.ls.length := by simp [MachineData.letFields]
  have hletBs : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
    simp [MachineData.letBs]
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  have hA : (d.shape.binders.take nDecl).length = nDecl := by
    rw [List.length_take]
    omega
  have hsplit : d.shape.binders = d.shape.binders.take nDecl ++ d.shape.binders.drop nDecl :=
    (List.take_append_drop ..).symm
  have hKne : d.letBs.length ≠ 0 := by rw [← hlets]; exact hK
  have hBlen : (d.shape.binders.drop nDecl).length =
      d.shape.insts.length + d.ss.length + d.letBs.length := by
    rw [List.length_drop]
    omega
  have hcoreWF := core_wf d.core.2 d.letFields hwf
  obtain ⟨PI, ls, bodyB, w, P, bnd, hin, hPI, hlsL, hndI, hinW, hwAlloc, hbodyT, hacy, hnamed, hnw,
      hP, hF, hdes, hname⟩ :=
    transition_calls_facts (cs := d.callBounds) nd len hrun hm nameLegal hposv d.letFields d.core.2
      hwf hb' hv' hbody hsplit hdomB hBlen hfitL
      (by rw [hA]; exact fieldsOK_of_B d.letFields 0 d.core.2 hfields hwf)
      (by
        rw [hA, hlsLen]
        exact uses_of_reads (fun j hj hr => ⟨hj, posOk_rule hr⟩)
          (fun j hj hr => ⟨hj, posOk_rule hr⟩) d.core.2 hcoreWF hcoreR)
  obtain ⟨hclosedT, -, ⟨ow, pb⟩, ready, -, -⟩ :=
    transition_closed nd len hrun hm nameLegal hposv d.packed hwf hb' hv' hbody
  rw [hlets] at hcl
  have hss : d.ss.length = 0 := by rw [hslots, hsl]; rfl
  have h0 : d.shape.insts.length + d.ss.length = 0 := by rw [hno, hss]; rfl
  obtain ⟨hC, hI, hN⟩ := slotless_childComb_full (b := b) hKne hcl hin (by rw [hlsL, h0]; omega)
    hndI hinW hwAlloc hbodyT hacy hnamed
    (fun al core h => by
      obtain ⟨es, ws, hf, hal, hc⟩ := hF al core h
      rw [h0, List.drop_zero] at hal
      exact ⟨es, ws, hf, hal, hc⟩)
    hclosedT ready.typed ready.wiresNodup pb.wires outsOk outTy hsl houts (hMeq ▸ hpost)
  have hD0 : D.modules = [] := by rw [hDeq, hD, hdes]; rfl
  exact ⟨M, D, w1, hcore, hpost, ⟨tenv, bb, w9, w10, hrun9, hw9⟩, hD0, hC, by rw [hI, hPI], by rw [hN, hname], hdesM hD0⟩

/-! ## the package of a combinational leaf row is a `.comb` package -/
section Pkg
open Tools.ShippingGen5Acc Tools.ShippingGen5DataOf Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1 Tools.ShippingGen5Sem
open Tools.ShippingGen5Sem (kDOf GenWF)
open Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1kPkg
open Sparkle.Core.Domain

/-- **a combinational leaf row's package is `.comb`** (`ss = []`, `insts = []`): the table `genGP` at the canonical rows returns `.comb cp` with the row's declaration, data and `kD` -/
theorem kid_pkg {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) {X : Name} {d : MachineData}
    (hR : RootReader lvl env X d) (hwf : GenWF d = true) (hleaf : d.shape.insts = []) (hss : d.ss = []) :
    ∃ cp : CombPkg ι (fun _ => Sparkle.Core.Domain.defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (dataOfSound_initsOf lvl) (canonGD lvl) env X = some (.comb cp) ∧
      cp.decl = X ∧ cp.d = d ∧ cp.kD = kDOf d := by
  obtain ⟨E, hE, hsh, hdat⟩ := hR
  obtain ⟨g, hg, hgd⟩ := canon_row (lvl := lvl) (env := env) hwf hsh hdat
  have hleaf' : g.d.shape.insts = [] := by rw [hgd]; exact hleaf
  obtain ⟨p, hp, hdecl, hpd, hkD⟩ := Tools.ShippingFGCircuitCover.genGP_root (ι := ι) (dom := fun _ => defaultDomain) lvl (dataOfSound_initsOf lvl) (canonGD lvl) env hE hg hleaf'
  have hF := factsOf_genS_assembled'' (ι := ι) (dom := fun _ => defaultDomain) (dataOfSound_initsOf lvl) (canonGD lvl env)
  obtain ⟨s, hs, hps⟩ := genP_some_inv (genKit (ι := ι) (dom := fun _ => defaultDomain) lvl (dataOfSound_initsOf lvl) env (canonGD lvl env)) hF hp
  have hsE := genS_leaf_eq (ι := ι) (dom := fun _ => defaultDomain) lvl (dataOfSound_initsOf lvl) (canonGD lvl) env hE hg hleaf'
  rw [hsE] at hs
  have hs' := Option.some.inj hs
  have hc : ((g.toIn (dataOfSound_initsOf lvl)).d.ss.isEmpty && (g.toIn (dataOfSound_initsOf lvl)).d.shape.insts.isEmpty) = true := by
    show (g.d.ss.isEmpty && g.d.shape.insts.isEmpty) = true
    rw [hgd, hss, hleaf]; rfl
  have hps' : p.toSem = SemPkg.comb (genSemComb X (g.toIn (dataOfSound_initsOf lvl))) := by
    rw [hps, ← hs']; unfold genSemI; rw [if_pos hc]
  cases p with
  | comb cp => exact ⟨cp, hp, hdecl, hpd.trans hgd, hkD.trans (by rw [hgd])⟩
  | gen q => simp only [Pkg.toSem] at hps'; cases hps'
  | loop q => simp only [Pkg.toSem] at hps'; cases hps'

end Pkg

open Tools.ShippingFGCircuitS2dKids (KidStartEnv machineDefinesLinked_of_readerE)
open Tools.ShippingGen2 (ShipsRes InstClosed ChildShips LeafDataOk LeafDataOkB ExtInS CombPkg Pkg Pkgs Laws MachineTaken childShips_congr)

/-- the leaf data check of a `.comb` package from the Boolean of its row (kernel-decided at the two children) -/
theorem leafDataOk_comb {ι : Type} (cp : CombPkg ι (fun _ => Sparkle.Core.Domain.defaultDomain)) {d : MachineData}
    (hcd : cp.d = d) (hkD : cp.kD = Tools.ShippingGen5Sem.kDOf d)
    (h : (d.ok && d.callsOk (Tools.ShippingGen5Sem.kDOf d) && decide (d.ss.length = d.shape.layout.slots.length) &&
      decide (∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)) = true) : LeafDataOk (Pkg.comb cp) := by
  unfold LeafDataOk LeafDataOkB
  show (cp.d.ok && cp.d.callsOk cp.kD && decide (cp.d.ss.length = cp.d.shape.layout.slots.length) &&
      decide (∀ o ∈ cp.d.shape.layout.outs, o.ty.bitWidth = o.width)) = true
  rw [hcd, hkD]; exact h

/-- **a slotless combinational callee's actual result ships** (`ShipsRes`), from its own run: the machine run by `kidRunK` (run-local entry), `ChildShips` by `slotlessLeaf_childShips_of_ran`, the design is empty -/
theorem kid_shipsRes {ι : Type} (L : Laws mref cref) (hcell : CellPrem MkRefd mref cref) {lvl : Lean.Expr → Nat} {e : Environment}
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hS : d.gateCallsOk nDecl = true) (hK : d.shape.layout.lets ≠ 0)
    (hno : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (houts : ∃ o, d.shape.layout.outs = [o] ∧ o.name = "out")
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hRead : RootReader lvl e c d) (hgates : EntryGates e c) (hk : KidStartEnv L.O e c)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), MachineCloses mctx' mref cctx' cref c d.shape)
    (P : Pkgs ι (fun _ => Sparkle.Core.Domain.defaultDomain)) (cp : CombPkg ι (fun _ => Sparkle.Core.Domain.defaultDomain))
    (hP : P c = some (Pkg.comb cp)) (hdecl : cp.decl = c) (hcd : cp.d = d)
    (hdata : LeafDataOk (Pkg.comb cp))
    {y : Res} (h : RealChildA L.O c y) : ShipsRes L P c y := by
  have h0 := h
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    obtain ⟨b, design⟩ := y
    obtain ⟨hRA, hprof⟩ := hk mctx' cctx' w w' _ adm cache synth quiet hr
    obtain ⟨M, D, w1, hcore, hpost, hran, hD0, -, -, -, hdes⟩ :=
      kidRunK L.O L.T adm d ok hbody hS hK hno hsl houts outTy ⟨⟨quiet, synth, rfl⟩, cache⟩ hr
        (fun _ => machineDefinesLinked_of_readerE hRA (headAt_of_profileOff c hcell hprof) (getEnvFrame_of_cellPrem hcell) hRead hgates)
        (closes mctx' cctx')
    have hran' : MachineTaken L mctx' cctx' (dv w + 1) (Pkg.comb cp).decl (Pkg.comb cp).d.shape M D := by
      show Tools.ShippingServedRealA.MachineRunJQC L.O mctx' cctx' (dv w + 1) cp.decl cp.d.shape M D
      rw [hdecl, hcd]; exact hran
    refine ⟨h0, ⟨Pkg.comb cp, 0, hP, hdecl, ?_⟩, ?_⟩
    · exact childShips_congr _ 0 b (by rw [hD0, hdes])
        (Tools.ShippingGen2.slotlessLeaf_childShips_of_ran L (Pkg.comb cp) hdata
          ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩ (by show cp.d.shape.insts = []; rw [hcd]; exact hno)
          (by show cp.d.shape.layout.slots = []; rw [hcd]; exact hsl) adm hpost hran' 0)
    · intro g hg
      rw [show (b, design).2 = design from rfl, hdes] at hg
      cases hg


end Tools.ShippingFGCircuitS2jKid

#print axioms Tools.ShippingFGCircuitS2jKid.kidRunK
#print axioms Tools.ShippingFGCircuitS2jKid.kid_pkg
#print axioms Tools.ShippingFGCircuitS2jKid.kid_shipsRes
