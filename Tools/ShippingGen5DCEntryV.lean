import Tools.ShippingGen5DCEntryU
import Tools.ShippingGen5DCEntryS
import Tools.ShippingGen2Pkg
import Tools.ShippingGen2MemData
import Tools.ShippingGen2CallDec
import Tools.ShippingGen2Leaf
import Tools.ShippingGen2MemParent
import Tools.ShippingParentDesignO
import Tools.ShippingSeqChildIface
import Tools.ShippingChecksDerived
import Tools.ShippingChecksDepthGate
import Tools.ShippingClosedKinds
import Tools.ShippingCallsSeqKids
set_option autoImplicit false
-- D.D-7, scripts/gen5/DD7_FREEZE.md. NOT BUILT (agent incremental build only; clean build is the coder's).

/-! # D.D-7: `NoRawBelow` for a real core run in all three cases (no `hins`/`hf`/`hno`)

The `MachineRanA` of the run is split: one-output / group by `closeInsts` / `closeInstsG` acyclicity, leaf by the closed body's
statement kinds. The leaf case reads the package `p` (`T1Hyp.pkg`): `Pkg.ok`, `Pkg.body_eq` and the `LeafDataOk` rows `callsOk`, `ss.length`. -/

namespace Tools.ShippingGen5DCEntryV
open Tools.ShippingGen2

theorem hdomB_of_leaf {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} (p : Pkg ι dom)
    (hco : p.d.callsOk p.kD = true) (hnoI : p.d.shape.insts = []) :
    ∀ b ∈ p.d.shape.binders.drop p.kD, b.2 ≠ .domain := by
  have hok := Pkg.ok p
  have hn := callsOk_nIn p.d p.kD hco
  rw [hnoI] at hn
  simp only [List.length_nil, Nat.add_zero] at hn
  have hSL := data_hSL p.d hok
  intro b hb
  apply hSL b
  rw [hn] at hb
  unfold Tools.ShippingMachineAuto.MachineData.slotBs Tools.ShippingMachineAuto.MachineData.letBs
  have hsplit : p.d.shape.binders.drop p.d.nIn =
      (p.d.shape.binders.drop p.d.nIn).take p.d.ss.length ++
        p.d.shape.binders.drop (p.d.nIn + p.d.ss.length) := by
    simpa [List.drop_drop, Nat.add_comm] using
      (List.take_append_drop p.d.ss.length (List.drop p.d.nIn p.d.shape.binders)).symm
  rw [hsplit] at hb
  exact hb

theorem noRawBelow_of_coreRunRows
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (p : Pkg ι dom)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName p.d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName p.d.shape)
    (hco : p.d.callsOk p.kD = true) (hss : p.d.ss.length = p.d.shape.layout.slots.length) :
    ∀ k : Nat, Tools.ShippingGen5DCEntryR.NoRawBelow D raw.name k raw := by
  obtain ⟨hA, hj0⟩ := hS
  have taken := Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hA hr hdef hcl hj0.1 (Or.inl rfl)
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T taken
  obtain ⟨_, _, _, _, _, t, t', d₀, run, hcl', hmt⟩ := ranA
  rcases hmt with ⟨hnoI, hM, hD⟩ | ⟨-, children, hcc, -⟩
  · -- leaf: the closed body has assignments and registers only, the design no module
    obtain ⟨hseq, -, hd0⟩ := Tools.ShippingClosedKinds.closedBody_kinds_of_run p.d (Pkg.ok p) (Pkg.body_eq p) hco hss
      (hdomB_of_leaf p hco hnoI) run hcl'
    subst hM hD
    refine fun k => Tools.ShippingGen5DCEntryS.noRawBelow_of_noInstOf ?_ k _
      (Tools.ShippingChildServe.noInstOf_of_B (Tools.ShippingCallsSeqKids.noInstOfB_of_seqOk hseq _))
    intro g hg
    rw [hd0] at hg
    exact absurd hg List.not_mem_nil
  · rcases hcc with ⟨-, hI⟩ | ⟨-, hG, -⟩
    · exact Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInsts hI
    · exact Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInstsG hG

theorem dataRows_of_data {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {p : Pkg ι dom}
    (hdata : LeafDataOk p ∨ MemParentDataOk p) :
    p.d.callsOk p.kD = true ∧ p.d.ss.length = p.d.shape.layout.slots.length :=
  hdata.elim (fun h => ⟨h.rows.2.1, h.rows.2.2.1⟩) (fun h => ⟨h.rows.2.1, h.rows.2.2.1⟩)

theorem noRawBelow_of_coreRunAll
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (p : Pkg ι dom)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName p.d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName p.d.shape)
    (hdata : LeafDataOk p ∨ MemParentDataOk p) :
    ∀ k : Nat, Tools.ShippingGen5DCEntryR.NoRawBelow D raw.name k raw :=
  noRawBelow_of_coreRunRows p hS hr hdef hcl (dataRows_of_data hdata).1 (dataRows_of_data hdata).2

theorem resetNk_transportR
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (p : Pkg ι dom)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName p.d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName p.d.shape)
    (hdata : LeafDataOk p ∨ MemParentDataOk p)
    (n : Nat) (kids : String → Tools.ShippingHierStateG.KT n) :
    Tools.ShippingMachineShipsDepth.ResetNk n raw D kids ↔ Tools.ShippingMachineShipsDepth.ResetNk n raw D' kids :=
  Tools.ShippingGen5DCEntryR.resetNk_transport hpost n kids (noRawBelow_of_coreRunAll p hS hr hdef hcl hdata (n + 1))

theorem coreRun_transportAll
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (p : Pkg ι dom)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName p.d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName p.d.shape)
    (hdata : LeafDataOk p ∨ MemParentDataOk p)
    (n : Nat) (we : Sparkle.IR.Semantics.WEnv)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T : Nat)
    (s : Tools.ShippingHierStateG.KState (Tools.ShippingHierStateG.KT n)) :
    Tools.ShippingHierStateG.runModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) n) we
        (Tools.ShippingMachineLinked.childMap D'.modules) raw.body seed T s =
      Tools.ShippingHierStateG.runModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) n) we
        (Tools.ShippingMachineLinked.childMap D.modules) raw.body seed T s :=
  Tools.ShippingGen5DCEntryT.runModuleTG_transport (Tools.ShippingGen5DCEntryU.hlk_of_postEntry hpost) n raw we seed T s
    (noRawBelow_of_coreRunAll p hS hr hdef hcl hdata (n + 1))

/-! ## (a3): the module actually run is `checkedOptimize b` -/

theorem dropZeroWidth_seqOk {m : Sparkle.IR.AST.Module}
    (h : m.body.all Sparkle.IR.OptCheck.seqStmtOk = true) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body.all Sparkle.IR.OptCheck.seqStmtOk = true := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split
  · exact h
  · rw [List.all_eq_true]
    intro st hst
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp hst
    have hs' := List.all_eq_true.mp h s hs
    cases s with
    | assign l r =>
      simp only [Sparkle.IR.ZeroWidth.dzStmt] at hst
      split at hst
      · cases hst
      · cases hst; rfl
    | register o c rs i iv =>
      simp only [Sparkle.IR.ZeroWidth.dzStmt, Option.some.injEq] at hst
      subst hst; rfl
    | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [Sparkle.IR.OptCheck.seqStmtOk] at hs'
    | inst _ _ _ => simp [Sparkle.IR.OptCheck.seqStmtOk] at hs'

theorem noRawBelow_mono {D : Sparkle.IR.AST.Design} {rn : String} {mc mc' : Sparkle.IR.AST.Module}
    (hsub : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc'.body → Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body) :
    ∀ k, Tools.ShippingGen5DCEntryR.NoRawBelow D rn k mc → Tools.ShippingGen5DCEntryR.NoRawBelow D rn k mc' := by
  intro k
  cases k with
  | zero => intro _; exact trivial
  | succ k =>
    rintro ⟨hnm, hrec⟩
    refine ⟨fun mn iname conns hm => hnm mn iname conns (hsub mn iname conns hm), ?_⟩
    intro mn iname conns mc'' hm hl
    exact hrec mn iname conns mc'' (hsub mn iname conns hm) hl

theorem checkedOptimize_inst_subset_of_coreRun
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (p : Pkg ι dom)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName p.d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName p.d.shape)
    (hdata : MemParentDataOk p) :
    ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ raw.body := by
  obtain ⟨hok, hco, hss, houtTy, hdomB⟩ := hdata.rows
  have hpost' := Tools.ShippingGen5DCEntryD.postEntry_postT1 hpost
  obtain ⟨hA, hj0⟩ := hS
  have taken := Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hA hr hdef hcl hj0.1 (Or.inl rfl)
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T taken
  have ranA2 := ranA
  intro mn iname conns hm
  obtain ⟨_, _, _, _, _, t, t', d₀, run, hcl', hmt⟩ := ranA
  rcases hmt with ⟨hnoI, hM, hD⟩ | ⟨hne, children, hcc, -⟩
  · -- leaf: no instance statement anywhere
    obtain ⟨hseq, -, -⟩ := Tools.ShippingClosedKinds.closedBody_kinds_of_run p.d hok (Pkg.body_eq p) hco hss
      (hdomB_of_leaf p hco hnoI) run hcl'
    have hseqRaw : raw.body.all Sparkle.IR.OptCheck.seqStmtOk = true := hM ▸ hseq
    have hb : b.body.all Sparkle.IR.OptCheck.seqStmtOk = true := by
      rcases hpost' with e | e
      · rw [e]; exact dropZeroWidth_seqOk hseqRaw
      · rw [e]; exact Tools.ShippingSeqChildIface.mergeChecked_seqOk (dropZeroWidth_seqOk hseqRaw)
    have hc := Tools.ShippingChecksDerived.checkedOptimize_seqOk_all hb
    have := List.all_eq_true.mp hc _ hm
    simp [Sparkle.IR.OptCheck.seqStmtOk] at this
  · have hg := Tools.ShippingParentDesignO.core_hierGate_anyO L.O p.d hok (Pkg.body_eq p) hco hss hdomB hne houtTy
      hpost' ranA2
    have hbody := Tools.ShippingParentTailsO.core_bodyEq_ranO L.O p.d hok (Pkg.body_eq p) hco hss hdomB hne houtTy
      hpost' ranA2
    rw [← hbody]
    exact (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hg mn iname conns).mp hm

theorem noRawBelow_checkedOptimize_of_coreRun
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (p : Pkg ι dom)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName p.d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName p.d.shape)
    (hdata : MemParentDataOk p) :
    ∀ k : Nat, Tools.ShippingGen5DCEntryR.NoRawBelow D raw.name k (Sparkle.IR.OptCheck.checkedOptimize b) :=
  fun k => noRawBelow_mono (checkedOptimize_inst_subset_of_coreRun p hS hr hpost hdef hcl hdata) k
    (noRawBelow_of_coreRunAll p hS hr hdef hcl (Or.inr hdata) k)

theorem coreRun_transportOpt
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design}
    (p : Pkg ι dom)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName p.d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName p.d.shape)
    (hdata : MemParentDataOk p)
    (n : Nat) (we : Sparkle.IR.Semantics.WEnv)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T : Nat)
    (s : Tools.ShippingHierStateG.KState (Tools.ShippingHierStateG.KT n)) :
    Tools.ShippingHierStateG.runModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) n) we
        (Tools.ShippingMachineLinked.childMap D'.modules) (Sparkle.IR.OptCheck.checkedOptimize b).body seed T s =
      Tools.ShippingHierStateG.runModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) n) we
        (Tools.ShippingMachineLinked.childMap D.modules) (Sparkle.IR.OptCheck.checkedOptimize b).body seed T s :=
  Tools.ShippingGen5DCEntryT.runModuleTG_transport (Tools.ShippingGen5DCEntryU.hlk_of_postEntry hpost) n
    (Sparkle.IR.OptCheck.checkedOptimize b) we seed T s
    (noRawBelow_checkedOptimize_of_coreRun p hS hr hpost hdef hcl hdata (n + 1))

end Tools.ShippingGen5DCEntryV
