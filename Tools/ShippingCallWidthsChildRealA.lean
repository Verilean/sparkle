import Tools.ShippingChildLinkA
import Tools.ShippingChildRunAKids
import Tools.ShippingChildIfaceTy
-- BUILT (unit L2, par/u-l2): l2a stopped (pod restart), l2b exit 1 (opens), l2c exit 0, audit l2d exit 0.
-- At integration (par/int-r5) the duplicate `entryStrict_realA` was replaced by unit L1's (LinkA).
-- SCOPE: the result is about the PORT WIDTHS of non-memory LEAF children only. `LeafKid.closes`
-- remains a PREMISE. It is NOT general hierarchical semantic preservation.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Law witness `O : RefLawsAOps MkRefd mref cref`.
/-! # Unit L2: the `ChildrenReal` consumers of the call-width chain on `RealChildA` / `ChildrenRealA`

Ports of `Tools.ShippingCallWidthsChildReal.{realChild_of_childrenReal, entryStrict_real,
callWidthsStrict_real, children_widths_real, parent_children_widths_real}` and of
`Tools.ShippingChildIfaceTy.{leaf_run_outputs, leaf_real_outTys}` (needed by `children_widths_real`)
to the new boundary. Recipe of unit K: the old proofs' `hy.inv` + `core_reads_inv L` become `cases hy`
+ `childLink_realA` (law-free `synthesizeCombinationalCore_reads`).

New premises of the leaf port (`leaf_run_outputsA`): the old one used `machine_run_of_core` (needs
`ChildBnd`) and `MachineCloses`; the new one uses `machine_run_of_coreA` at the world recorded by
`RealChildA` (depth := `dv w`, cache half = the recorded `cache`) and takes `MachineClosesAtA`
(derived from the old `LeafKid.closes` in `children_widths_realA`, which is stronger). A leaf
(`insts = []`) needs no `BodyStepC`/`htr`: `synthesizeMachineCertified_leaf_runs` unfolds the run directly.

`parent_children_widths_realA` takes G's conclusion (the statement of `machine_children_realA'`'s
conclusion) as the hypothesis `hkids`; `parent_children_widths_realA_of_run` composes it with
`machine_children_realA'` (premises `BodyStepC`, `htr`, `MachineClosesAtA` of that theorem).

`RealChildA` / `ChildrenRealA` are HISTORIES of past synthesis results, not semantic correctness in
the current environment; this is not a runtime-fit proof. Conclusions are about output port widths. -/
namespace Tools.ShippingCallWidthsChildRealA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildCacheA Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildLinkA
open Tools.ShippingCallWidthsStrict Tools.ShippingCallWidthsDeclared Tools.ShippingCallWidthsEntry
open Tools.ShippingCallWidthsChildReal
open Tools.ShippingPortsMatchRawLeaf (LeafKid)
open Tools.ShippingChildIfaceTy (ChildOutTys)
open Tools.ShippingMixedEntrySoundness Tools.ShippingGateChildComb
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Tools.ShippingMachineClosesData Tools.ShippingMachineCloses

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## Origin-built or `RealChildA` -/

/-- A non-memory entry of `ChildrenRealA` is a `RealChildA` of its callee. -/
theorem realChildA_of_childrenRealA {O : RefLawsAOps MkRefd mref cref} {shape : MachineShape}
    {children : List Res} (hreal : ChildrenRealA O shape children)
    {k : Nat} (hk : k < shape.insts.length)
    (hno : (shape.instOrigins.getD k .ord).child? = none)
    {y : Res} (hy : children[k]? = some y) :
    RealChildA O (shape.insts[k]).1 y := by
  obtain ⟨y', hy', hor⟩ := hreal.2 k hk
  have hyy : y' = y := Option.some.inj (hy'.symm.trans hy)
  subst hyy
  rcases hor with h | h
  · rw [hno] at h
    cases h
  · exact h

-- `entryStrict_realA`: unit L1's `Tools.ShippingChildLinkA.entryStrict_realA` (same statement, generic
-- in `Fresh`); L2's identical copy was dropped at integration (par/int-r5).

/-- **`callWidthsStrict` with `kidOuts` the REAL callee shapes**, from `ChildrenRealA`. -/
theorem callWidthsStrict_realA {O : RefLawsAOps MkRefd mref cref} {d : MachineData}
    {children : List Res}
    (hreal : ChildrenRealA O d.shape children)
    (sc : Nat → MachineShape) (res : Nat → MixedGateBinder)
    (hnomem : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (entry : ∀ k (hk : k < d.shape.insts.length),
      MachineDefines mctx mref cctx cref (d.shape.insts[k]).1 (sc k))
    (ResD : ∀ k (hk : k < d.shape.insts.length), ResDeclAt mref cref (d.shape.insts[k]).1 (res k))
    (P5 : ∀ k (hk : k < d.shape.insts.length), P5At mref cref (d.shape.insts[k]).1 (res k))
    (PB : ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => kindTy bn.2) =
        some (machHWType (res k))) :
    callWidthsStrict d (closingNDecl d.shape) (fun k => (sc k).layout.outs) = true := by
  apply callWidthsStrict_of_entries
  intro k hk
  obtain ⟨y, hy, _⟩ := hreal.2 k hk
  exact Tools.ShippingChildLinkA.entryStrict_realA rfl (entry k hk) (ResD k hk) (P5 k hk)
    (realChildA_of_childrenRealA hreal hk (Tools.ShippingChildInv.notag_at hnomem hk) hy) (PB k hk)

/-! ## A leaf child's output ports, from a `RealChildA` -/

/-- A returning run of `synthesizeMachineCertified` for a shape WITHOUT calls: no invariant is
needed (the closing of calls is not reached). -/
theorem synthesizeMachineCertified_leaf_runs {tenv : Lean.Environment} {b : Bool}
    {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    {w w' : Void IO.RealWorld}
    (hno : shape.insts = [])
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀ := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    split at hr
    · rename_i hi
      have eq := RunsTo.pure_eq hr
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨hm, hd⟩ := eq
      exact ⟨t, t', d', run.mreturns, hcl, hm, hd⟩
    · rename_i hi
      rw [hno] at hi
      exact absurd hi (by simp)
  · have eq := RunsTo.pure_eq hr
    cases eq

set_option maxHeartbeats 2000000 in
/-- **A leaf machine's returned module has the layout's output ports, with their types**, over a
run of the full entry from a `JQ` world with the cache half (new boundary; port of
`leaf_run_outputs`). Premise `closes`: `MachineClosesAtA` (instead of `MachineCloses`). -/
theorem leaf_run_outputsA {O : RefLawsAOps MkRefd mref cref} (hA : AdmCtx O.quiet mctx cctx)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {D : Nat} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c d.shape) :
    b.outputs = d.shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
  obtain ⟨M, D₁, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ := machine_run_of_coreA O hA hcore entry hw hc
  have hne := closes bb _ _ _ _ hw9 (by omega) hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hMeq, hDeq⟩ := synthesizeMachineCertified_leaf_runs hno hrun9
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok
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
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  -- the transition ends in `assign out = w`, and so does the `let`-closed one
  obtain ⟨wP, hpw⟩ := Tools.ShippingChecksPacked.transition_packed nd len hrun hm d.packed hwf
    hb' hv' hbody
  obtain ⟨wP', hpw'⟩ := Option.isSome_iff_exists.mp
    (Tools.ShippingChecksPacked.closeLets_packed hcl hpw)
  have hrawA : Tools.ShippingDesignSVBack.outsAssigned M = true := by
    rw [hMeq]
    exact Tools.ShippingChecksDerived3.closeMachine_outsAssigned hpw'
  -- the raw module's wiring: the core entry's theorem at this run
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeMachineCertified_sound hrun9.mreturns d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, rlen, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := wired
  obtain ⟨⟨hzb, -, -, hzo⟩, -, hregs, -, -, -, -, -, -⟩ := hclean hno outTy
  -- the core module has a register (a slot)
  obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons f _ => exact ⟨f, rfl⟩
  obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
    cases hrs : regs with
    | nil =>
      have hreg0 : regs.length = 0 := by simp [hrs]
      have hsb : d.slotBs.length = d.ss.length := by
        simp only [MachineData.slotBs, List.length_take, List.length_drop]
        omega
      have : d.shape.layout.slots.length = 0 := by omega
      rw [List.length_eq_zero_iff] at this; exact absurd this hsl
    | cons r _ => exact ⟨r, rfl⟩
  obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
  have hnA : M.body.all Sparkle.IR.RegDedup.isAssign = false := by
    apply List.all_eq_false.mpr
    exact ⟨_, hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
  have hMout : M.outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
    rw [hMeq]
    exact Tools.ShippingChecksCore.closeMachine_outputs hpw'
  rcases hpost with h | h
  · rw [h, hzo]
    exact hMout
  · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)).2.1, hzo]
    exact hMout

/-- **A real leaf child's output ports, with their types**, from a `RealChildA`. -/
theorem leaf_real_outTysA {O : RefLawsAOps MkRefd mref cref} {c : Name} (d : MachineData)
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) : ChildOutTys d.shape.layout.outs y.1 := by
  obtain ⟨M', D'⟩ := y
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact ⟨leaf_run_outputsA adm d ok hbody hno hsl hSS outTy (D := dv w) ⟨quiet, synth, rfl⟩
      (Or.inr cache) hr (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')⟩

/-! ## The whole condition -/

/-- **The emitted children's connected output ports, leaf callees**, from `ChildrenRealA`. -/
theorem children_widths_realA {O : RefLawsAOps MkRefd mref cref} {d : MachineData}
    {children : List Res}
    (hreal : ChildrenRealA O d.shape children)
    (kid : Nat → MachineData) (res : Nat → MixedGateBinder)
    (hnomem : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (hkid : ∀ k (hk : k < d.shape.insts.length),
      LeafKid mctx mref cctx cref (d.shape.insts[k]).1 (kid k))
    (ResD : ∀ k (hk : k < d.shape.insts.length), ResDeclAt mref cref (d.shape.insts[k]).1 (res k))
    (P5 : ∀ k (hk : k < d.shape.insts.length), P5At mref cref (d.shape.insts[k]).1 (res k))
    (PB : ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => kindTy bn.2) =
        some (machHWType (res k))) :
    callWidthsStrict d (closingNDecl d.shape) (fun k => (kid k).shape.layout.outs) = true ∧
    ∀ k (hk : k < d.shape.insts.length) (y : Res), children[k]? = some y →
      ChildOutTys (kid k).shape.layout.outs y.1 ∧
      ∀ p ∈ y.1.outputs, (∀ f, d.shape.instFields[k]? = some f → p.name = f) →
        (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth := by
  have hcw : callWidthsStrict d (closingNDecl d.shape) (fun k => (kid k).shape.layout.outs) =
      true :=
    callWidthsStrict_realA hreal (fun k => (kid k).shape) res hnomem
      (fun k hk => (hkid k hk).entry) ResD P5 PB
  have hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChildA O (d.shape.insts[k]).1 y → ChildOutTys (kid k).shape.layout.outs y.1 := by
    intro k hk y hy
    have K := hkid k hk
    exact leaf_real_outTysA (kid k) K.ok K.body K.leaf K.slots K.ss K.outTy K.entry
      (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => K.closes mctx' cctx' (profLogIO b) w r w' hr) hy
  refine ⟨hcw, fun k hk y hy => ?_⟩
  have hyR := realChildA_of_childrenRealA hreal hk (Tools.ShippingChildInv.notag_at hnomem hk) hy
  refine ⟨hkidT k hk y hyR, ?_⟩
  intro p hp hpn
  rw [(hkidT k hk y hyR).outputs] at hp
  obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
  have h := callWidthsStrict_at hcw hk ho (by
    intro f hf
    have := hpn f hf
    rw [← e] at this
    exact this)
  rw [← e]
  exact h

/-- **From the children of one successful parent run** (G's conclusion, the conclusion of
`machine_children_realA'`, taken as the hypothesis `hkids`): `children_widths_realA`. -/
theorem parent_children_widths_realA {O : RefLawsAOps MkRefd mref cref} {d : MachineData}
    {m : Sparkle.IR.AST.Module} {D : Design}
    (hkids : ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets d.shape.layout.lets t = some t' ∧
      CloseCalls d.shape t (Sparkle.IR.Machine.closeMachine d.shape.layout t') d₀ children m D ∧
      ChildrenRealA O d.shape children)
    (kid : Nat → MachineData) (res : Nat → MixedGateBinder)
    (hnomem : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (hkid : ∀ k (hk : k < d.shape.insts.length),
      LeafKid mctx mref cctx cref (d.shape.insts[k]).1 (kid k))
    (ResD : ∀ k (hk : k < d.shape.insts.length), ResDeclAt mref cref (d.shape.insts[k]).1 (res k))
    (P5 : ∀ k (hk : k < d.shape.insts.length), P5At mref cref (d.shape.insts[k]).1 (res k))
    (PB : ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => kindTy bn.2) =
        some (machHWType (res k))) :
    callWidthsStrict d (closingNDecl d.shape) (fun k => (kid k).shape.layout.outs) = true ∧
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets d.shape.layout.lets t = some t' ∧
      CloseCalls d.shape t (Sparkle.IR.Machine.closeMachine d.shape.layout t') d₀ children m D ∧
      ∀ k (hk : k < d.shape.insts.length) (y : Res), children[k]? = some y →
        ChildOutTys (kid k).shape.layout.outs y.1 ∧
        ∀ p ∈ y.1.outputs, (∀ f, d.shape.instFields[k]? = some f → p.name = f) →
          (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
            some p.ty.bitWidth := by
  obtain ⟨t, t', d₀, children, hcl, hcc, hreal⟩ := hkids
  obtain ⟨hcw, hports⟩ := children_widths_realA hreal kid res hnomem hkid ResD P5 PB
  exact ⟨hcw, t, t', d₀, children, hcl, hcc, hports⟩

/-- **The same from the run**, composing G's `machine_children_realA'` (its premises `BodyStepC`,
`htr`, `MachineClosesAtA` and the start world `JQ O.quiet D` + cache half are this theorem's). -/
theorem parent_children_widths_realA_of_run {O : RefLawsAOps MkRefd mref cref}
    (hB : BodyStepC O) (hA : AdmCtx O.quiet mctx cctx) {d : MachineData} {declName : Name} {D₀ : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, D) w')
    (entryP : MachineDefines mctx mref cctx cref declName d.shape)
    (htr : ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O (D₀ + 1))
      (translateExprToWire tenv e hint top named))
    (closesP : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName d.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) (hi : d.shape.insts ≠ [])
    (kid : Nat → MachineData) (res : Nat → MixedGateBinder)
    (hnomem : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (hkid : ∀ k (hk : k < d.shape.insts.length),
      LeafKid mctx mref cctx cref (d.shape.insts[k]).1 (kid k))
    (ResD : ∀ k (hk : k < d.shape.insts.length), ResDeclAt mref cref (d.shape.insts[k]).1 (res k))
    (P5 : ∀ k (hk : k < d.shape.insts.length), P5At mref cref (d.shape.insts[k]).1 (res k))
    (PB : ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => kindTy bn.2) =
        some (machHWType (res k))) :
    callWidthsStrict d (closingNDecl d.shape) (fun k => (kid k).shape.layout.outs) = true ∧
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets d.shape.layout.lets t = some t' ∧
      CloseCalls d.shape t (Sparkle.IR.Machine.closeMachine d.shape.layout t') d₀ children m D ∧
      ∀ k (hk : k < d.shape.insts.length) (y : Res), children[k]? = some y →
        ChildOutTys (kid k).shape.layout.outs y.1 ∧
        ∀ p ∈ y.1.outputs, (∀ f, d.shape.instFields[k]? = some f → p.name = f) →
          (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
            some p.ty.bitWidth :=
  parent_children_widths_realA
    (machine_children_realA' O hB hA hr entryP htr closesP hw hc hi) kid res hnomem hkid ResD P5 PB

end Tools.ShippingCallWidthsChildRealA
