import Tools.ShippingSeqChildDeepKidFactsA
import Tools.ShippingSrm4Core3
import Tools.ShippingSrm4Core4
-- BUILT (unit SRM4): c6 exit 0 (dev run, default heartbeats); the final-SHA rebuild is in REPORT-SRM4.md.
-- SCOPE (binding, residue R2): SCRIPTED copies (`scripts/srm4/port_srm4.py`, specs `scripts/srm4/spec*.json`) of `deepChild_ifaceA'`, `deepChild_ranA`, `deepChild_outsMaskedA`, from the A-form originals in `Tools/ShippingSeqChildDeepConsumerA.lean`, `Tools/ShippingSeqChildDeepFactsA.lean`, `Tools/ShippingSeqChildDeepMaskedA.lean`, with the memory entries of the callee allowed.  The script's changes, all of them:
-- the theorem's name gets the suffix `M`; the binder `hnomem` is removed and `hfne : d.shape.instFields ≠ []` is added after `hins` where the original had none; a call of a copied theorem calls the copy; `RealChildA O (d.shape.insts[k]).1 y` (the kid of
-- call entry `k`) becomes `KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y` (the origin's built module, or a `RealChildA` when the origin builds none); the three lines refuting the memory case of a child (`rw [nomem_tag hnomem …] at hmem; cases hmem`) become
-- `kidTA_ofO` (from `MemChildren` of the closing, taken from the closing's own statement); `set_option maxHeartbeats … in` lines are DROPPED (the copies run at the default budget).  Nothing is routed through the old-form `RealChild` / `MachineRan` / `MachineClosesAt` or `kidsChild_of_realM`.
-- The per-kid facts stay hypotheses over `KidTA`.  `RealChildA` is a history of past synthesis results, not freshness or semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingSrm4Core5
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingKidsChildIface
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
open Tools.ShippingInstStmtG
open Sparkle.IR.RefineCheck (mergeChecked hierGate)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingSeqChildDeepConsumerA
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingPortWidthsPure
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingParentRanA Tools.ShippingKidsSelfA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentTailsA
open Tools.ShippingSrm3Iface Tools.ShippingCallsMemA Tools.ShippingSrm4Core1 Tools.ShippingSrm4Core2 Tools.ShippingSrm4Core3 Tools.ShippingSrm4Core4
open Tools.ShippingInstTagged (originAt)

/-- **`deepChild_ifaceA` with `closes` asked in `AdmCtx` contexts only.** -/
theorem deepChild_ifaceA'M (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (w w1 : Void IO.RealWorld)
      (M : Sparkle.IR.AST.Module) (D : Design),
      AdmCtx O.quiet mctx' cctx' ∧ JQ O.quiet (dv w) w ∧ CacheInvA O (cv w) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx' mref cctx' cref w (M, D) w1 ∧
      (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      y.2.modules = D.modules ∧
      M.name = (Sparkle.IR.ModuleName.ofDecl c) ∧ y.1.body = M.body ∧ y.1.outputs = M.outputs ∧
      (∀ mn i conns, Stmt.inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc) ∧
      (∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
        Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y' ∧ (g = y'.1 ∨ g ∈ y'.2.modules) ∧
        ∀ g2 ∈ y'.1 :: y'.2.modules, ∃ g' ∈ D.modules, g'.name = g2.name) ∧
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ := synthesizeCombinational_designL hr
    have hw : JQ O.quiet (dv w) w := ⟨quiet, synth, rfl⟩
    have hc : CacheInvA O (cv w) := fun c r h => cache c r h
    have ran := machineRanA_main O adm T hcore (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
      (closes mctx' cctx' adm) hw (Or.inr hc)
    obtain ⟨hMn, hb, ho, hinst, hreal, hassign⟩ :=
      core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
    refine ⟨mctx', cctx', w, w1, M, D, adm, hw, hc, hcore, hpost, hdesL ?_, hMn, hb, ho, hinst,
      hreal, hassign⟩
    intro x hx e
    obtain ⟨k, hk, y', hre, hor, -⟩ := hreal x hx
    refine hsep k hk y' hre x ?_ (e.trans hMn)
    rcases hor with heq | hin
    · rw [heq]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hin

/-- **The run of a `RealChildA` of a machine with calls, as `MachineRanA`**: the served module is the post-processing of the
run's module and the served design IS the run's design. -/
theorem deepChild_ranAM (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (M : Sparkle.IR.AST.Module) (D : Design),
      (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      y.2.modules = D.modules ∧ MachineRanA O mctx' cctx' c d.shape M D := by
  obtain ⟨mctx', cctx', w, w1, M, D, adm, hw, hc, hcore, hpost, hdes, -⟩ :=
    deepChild_ifaceA'M O T d ok hbody hC hslots hdomB hins hfne outTy hsep entry closes h
  exact ⟨mctx', cctx', M, D, hpost, hdes, machineRanA_main O adm T hcore
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx' adm) hw (Or.inr hc)⟩

/-- **`outsMaskedN` of the served module of a NON-leaf child** (the `masked` field of `KidFacts`/`GenKid`), over
`RealChildA`.  Minimal consumer: `outsMaskedN_of_callsG`. -/
theorem deepChild_outsMaskedAM (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsl : d.shape.layout.slots ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, adm, hw, hc, hcore, hpost, -⟩ :=
    deepChild_ifaceA'M O T d ok hbody hC hslots hdomB hins hfne outTy hsep entry closes h
  have ran := machineRanA_main O adm T hcore (Tools.ShippingReflectCtx.MachineDefines.ctx entry)
    (closes mctx' cctx' adm) hw (Or.inr hc)
  obtain ⟨hP, hO⟩ := core_calls_portsG_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hsl
    kD hkD hIlen hSL hSlen hLlen hNIn hpost ran
  exact Tools.ShippingCallsPortsG.outsMaskedN_of_callsG hP
    (Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran hon hoty)
    hO
    (core_conn_refsG_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran)

end Tools.ShippingSrm4Core5
