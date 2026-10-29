import Tools.ShippingGen2TopNC
import Tools.ShippingGen2SlotlessParentRun
import Tools.ShippingGen2OneOutTopO
import Tools.ShippingHierOptRunHNoRst
import Tools.ShippingRefineNoRst
import Tools.ShippingReaderOutNames
set_option autoImplicit false
-- WRITTEN, NOT BUILT. No `sorry`, no `axiom`, no `native_decide`.

/-! # S5 stage C: the slotless one-output TOP without clock/reset premises (S5_SLOTLESS_FREEZE.md rev1 §5 + rev1.1)

Shared definitions are NOT edited (`TopShipsNC` is C2, in Tools/ShippingGen2TopNC.lean).

* C1 `hierRefineCheck_linked_noRst` (KS level): `hierRefineCheck_linked` (HierOptRun:532-655) with `hrstIn`,
  `hrstZ`, `hfitR` deleted and `hnoR : seqRegs m = []` added last; in the proof the `hrstIn'`/`hrstZ'` block is
  removed and `refineCheck_transfer` becomes `refineCheck_transfer_noReg` (RefineNoRst:224) with
  `hnoR' := seqRegs_openFlat ▸ hnoR` (HierOptRunHNoRst:46) — HierOptRunHNoRst:56's change rule moved to `KS`.
* C3 `RunFactsNR`: `RunFacts` (GuardsSound:314-322) without `rst`; `RunFacts.toNR` its projection.
* `outNameOk_of_run` (rev1.1 note 2: the `outNameOk` SUPPLIER, full type, not a premise): from the SAME `hcore` and
  `entry` C4 already takes, by the reader's output-name invariant (`outNames_of_core`,
  Tools/ShippingReaderOutNames.lean:179). It is the "equivalent named lemma" of the note: `outsExtracted` +
  `NoTouchZ` alone do not constrain the OUTPUT names (`outsExtracted` is about instance outputs; an output that no
  statement drives keeps its seeded value), so the names come from the reader, which refuses `rst`/`clk` outputs
  (`outNameOk`).
* `seqRegsL_nil_of_noTouch`: a `NoTouchZ` body has no register statement. It replaces the freeze's planned
  `seqRegs_nil_of_wired_sl` (C4's `hnoR`): `hZ` already excludes every non-assign/non-inst statement, so `wired` is
  not needed for it.
* C4 `machine_ships_hierC_runNR`: copy of `machine_ships_hierC_run` (FitChain:1073-1232). Binders: `hinitW` deleted,
  `hslots`/`hsl0` added after `houtTy`, `facts` targets `RunFactsNR`, `hnR`/`hnC`/`hZ` added after `facts`; the
  conclusion line :1145 (rst and clk) deleted. Proof: `regs = []` (`rlen`, `hslots`, `hsl0`); `H` at the zeroed seed
  `slSeedZ b ins` (S5 A3's def; its rst/clk premises from `hnR`/`hnC` via `hbI`); A2 `runModuleTG_seed_offZ` at
  `Z := ["rst","clk"]` on `raw.body` to `seedIn b ins`; outputs off `Z` by the supplier (`outName_notZ`);
  `KSBoundedRun` off `Z` by `hZ`'s instance clause; `hierRefineCheck_linked` → C1 with `hnoR`; otherwise verbatim.
* C5a `oneOutSl_topShipsNC` (published by name): `oneOut_topShipsO` (OneOutTopO:334-415) with `hsl` → `hsl0`, one
  new case binder `hrst`, conclusion `TopShipsNC`; `hnC` from A1 (`calls_ports_sl … |>.2.1`, resolved by `hrst`) on
  the trace's wiring; `RunFactsNR` field by field from the `O` lemmas that take no `hsl` (`core_runFactsHO` is NOT
  used); `hZ` from B1; then C4.

No new semantic premise (`hZ` internal, B1; `hnR`/`hnC` the case discriminant from the actual inputs; `hslots`/`hsl0`
the slotless shape). No `SeqKid`, no compiler change, no Defs edit. C4/C5a must not reach `TopShips` or
`topShips_of_NC` (audit in Tests/Gen2/TopNCCheck.lean). -/

/-! ## C1, C3, supplier, C4 (ambient: FitChain Block C, Tools/ShippingGen2FitChain.lean:1054-1068) -/
namespace Tools.ShippingGen2SlotlessTop
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tools.ShippingSrm25Init (SourceRegsAreSlots)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingGen2SlotlessParent (NoTouchZ noTouchZ_tail slSeedZ slSeedZ_agree runModuleTG_seed_offZ
  outName_notZ)

set_option maxHeartbeats 4000000 in
/-- **C1** `hierRefineCheck_linked` (HierOptRun:532-655) for a register-free module, at KS level: no reset premise,
no register start-value bound (`hrstIn`, `hrstZ`, `hfitR` deleted; `hnoR` added last). -/
theorem hierRefineCheck_linked_noRst {σ : Type} (KS : KStep σ) (hloc : KSLocal KS)
    (children : String → Option (Module × WEnv)) {m o : Module}
    (hchk : Sparkle.IR.RefineCheck.hierRefineCheck m o = true)
    (hwfM : linkedWF children m.body = true) (hwfO : linkedWF children o.body = true)
    (hndM : (instNames m.body).Nodup) (hndO : (instNames o.body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hOutM : ∀ w ∈ bodyInstOuts children m.body, w ∈ (openIns m).map (·.name))
    (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs)
    (hfitX : ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x)
    (hnoR : Sparkle.IR.OptCheck.seqRegs m = []) :
    o.inputs = m.inputs ∧ o.outputs = m.outputs ∧
    ∃ envsO, runModuleTG KS (declWidth o) children o.body (seedIn m ins) T s = some envsO ∧
      envsO.length = envs.length ∧
      ∀ p ∈ m.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name := by
  -- the check, taken apart
  simp only [Sparkle.IR.RefineCheck.hierRefineCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hk1, hk2⟩, hconnB⟩, hXdOB⟩, hrc⟩ := hchk
  have hOM := Tools.ShippingHierOptSoundness.instsKept_mem hk1
  have hMO := Tools.ShippingHierOptSoundness.instsKept_mem hk2
  have hXin : ∀ n ∈ (openIns m).map (·.name), n ∉ m.inputs.map (·.name) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have := (List.mem_filter.mp hp).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    simpa [List.contains_eq_mem] using this.2
  have hXdM : ∀ n ∈ (openIns m).map (·.name), n ∉ drivesOf m.body := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have := (List.mem_filter.mp hp).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    simpa [List.contains_eq_mem] using this.1.2
  have hXdO : ∀ n ∈ (openIns m).map (·.name), n ∉ drivesOf o.body := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have := List.all_eq_true.mp hXdOB p hp
    simpa [List.contains_eq_mem] using this
  have hconn : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ c ∈ conns, ∀ w,
      c.2 = .ref w → w ∈ (m.outputs ++ (openOuts m)).map (·.name) ∨
        (w ∉ drivesOf m.body ∧ w ∉ drivesOf o.body) := by
    intro mn iname conns hmem c hc w hw
    have h1 := List.all_eq_true.mp hconnB _ hmem
    have h2 := List.all_eq_true.mp h1 c hc
    rw [hw] at h2
    have h3 : (((m.outputs ++ (openOuts m)).map (·.name)).contains w ||
        (!(drivesOf m.body).contains w && !(drivesOf o.body).contains w)) = true := h2
    rcases Bool.or_eq_true_iff.mp h3 with h | h
    · exact Or.inl (by simpa [List.contains_eq_mem] using h)
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      exact Or.inr ⟨by simpa [List.contains_eq_mem] using h.1, by simpa [List.contains_eq_mem] using h.2⟩
  have hOutO : ∀ w ∈ bodyInstOuts children o.body, w ∈ (openIns m).map (·.name) := by
    intro w hw
    obtain ⟨mn, iname, conns, child, cwe, hmem, hc, hwo⟩ := bodyInstOuts_mem hw
    exact hOutM w (instOut_body hc hwo (hOM _ _ _ hmem))
  -- the ports
  obtain ⟨hinP, houtP⟩ := Tools.ShippingRefineSoundness.refineCheck_ports hrc
  have hin : o.inputs = m.inputs := by
    simpa [openFlat] using hinP
  have hout : o.outputs = m.outputs := by
    simpa [openFlat] using houtP
  refine ⟨hin, hout, ?_⟩
  -- 1. the linked run of `m` as an open run of the extracted module
  have hlen := runModuleTG_length KS _ children m.body _ T s envs hrun
  let E : Nat → Env := fun k => (envs[T - 1 - k]?).getD (fun _ => 0)
  have hE : ∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j) := by
    intro j hj
    simp only [E]
    rw [show T - 1 - (T - 1 - j) = j by omega]
    simp [hj]
  have hopen := linked_open_run KS (declWidth m) children m (openIns m) (openOuts m) ins E hwfM hOutM hXin hXdM
    T s envs hrun hE
  -- 2. the extracted pair's check
  have hinsFit' : ∀ t x, x ∈ (openFlat m (openIns m) (openOuts m)).inputs.map (·.name) →
      insOf ((openIns m).map (·.name)) E ins t x < 2 ^ declWidth (openFlat m (openIns m) (openOuts m)) x := by
    intro t x hx
    show insOf ((openIns m).map (·.name)) E ins t x < 2 ^ declWidth m x
    simp only [insOf]
    split
    · rename_i hX
      have hX' : x ∈ (openIns m).map (·.name) := by simpa [List.contains_eq_mem] using hX
      simp only [E]
      cases hj : envs[T - 1 - t]? with
      | none => simp only [Option.getD_none]; exact Nat.two_pow_pos _
      | some e =>
        obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
        simpa using hfitX _ hlt x hX'
    · rename_i hX
      have hX' : x ∉ (openIns m).map (·.name) := by simpa [List.contains_eq_mem] using hX
      simp only [openFlat, List.map_append, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hinsFit t x hx
      · exact absurd hx hX'
  have hopen' : runModule (declWidth (openFlat m (openIns m) (openOuts m)))
      (openFlat m (openIns m) (openOuts m)).body
      (seedIn (openFlat m (openIns m) (openOuts m))
        (insOf ((openIns m).map (·.name)) E ins)) T s.st s.mems = some envs := hopen
  -- (changed) no register: the reset-free transfer (HierOptRunHNoRst:153-157)
  have hnoR' : Sparkle.IR.OptCheck.seqRegs (openFlat m (openIns m) (openOuts m)) = [] := by
    rw [Tools.ShippingHierOptRunHNoRst.seqRegs_openFlat]; exact hnoR
  obtain ⟨envsO, hrunO, hlenO, houtsO⟩ := Tools.ShippingRefineNoRst.refineCheck_transfer_noReg hrc
    hnoR' (insOf ((openIns m).map (·.name)) E ins) hinsFit' (stM := s.st) (stO := s.st)
    (mems := s.mems) hopen'
  -- 3. the open run of the extracted optimized module as a linked run of `o`
  have hlinked := open_linked_run KS hloc (declWidth m) (declWidth o) children m o (openIns m) (openOuts m) ins E
    hwfM hwfO hndM hndO hOM hMO hnofb hOutM hOutO hXin hXdM hXdO hconn T s s.st envs envsO hrun hE
    hrunO
    (fun j hj hj' w hw => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      exact houtsO p hp j hj hj')
    (fun _ _ _ => rfl)
  refine ⟨envsO, hlinked, hlenO, fun p hp j hj hj' => houtsO p (List.mem_append_left _ hp) j hj hj'⟩

/-- **C3** `RunFacts` (GuardsSound:314-322) without `rst` (:321). -/
structure RunFactsNR (C : String → Option (Sparkle.IR.AST.Module × WEnv)) (b : Sparkle.IR.AST.Module) : Prop where
  gate : Sparkle.IR.RefineCheck.hierGate b = true
  wfB : Tools.ShippingHierOpen.linkedWF C b.body = true
  ndB : (Tools.ShippingHierState.instNames b.body).Nodup
  self : Tools.ShippingHierPremisesBase.noSelfRead C b.body = true
  outs : Tools.ShippingHierPremisesBase.outsExtracted C b = true
  wid : Tools.ShippingHierOpen.instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth b) b.body = true

/-- C3's projection from `RunFacts`. -/
theorem RunFacts.toNR {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {b : Sparkle.IR.AST.Module}
    (h : Tools.ShippingGuardsSound.RunFacts C b) : RunFactsNR C b :=
  ⟨h.gate, h.wfB, h.ndB, h.self, h.outs, h.wid⟩

/-- **The `outNameOk` supplier** (rev1.1 note 2): the layout's output names, from the run C4 already takes (`hcore`,
`entry`), by the reader's output-name invariant. -/
theorem outNameOk_of_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
    {declName : Name} {shape : Sparkle.Compiler.Elab.MachineShape} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    ∀ o ∈ shape.layout.outs, outNameOk o.name = true :=
  (Tools.ShippingReaderOutNames.outNames_of_core hcore entry).2.1

/-- A `NoTouchZ` body has no register statement. -/
theorem seqRegsL_nil_of_noTouch {Z : List String} :
    ∀ (body : List Stmt), NoTouchZ Z body → Tools.ShippingSeqOptSoundness.seqRegsL body = []
  | [], _ => rfl
  | .assign _ _ :: rest, hZ => by
    simp only [Tools.ShippingSeqOptSoundness.seqRegsL, List.filterMap_cons]
    exact seqRegsL_nil_of_noTouch rest (noTouchZ_tail hZ)
  | .inst _ _ _ :: rest, hZ => by
    simp only [Tools.ShippingSeqOptSoundness.seqRegsL, List.filterMap_cons]
    exact seqRegsL_nil_of_noTouch rest (noTouchZ_tail hZ)
  | .register .. :: _, hZ => by
    rcases hZ _ List.mem_cons_self with ⟨l', r', heq, -⟩ | ⟨mn', iname', conns', heq, -⟩ <;> cases heq
  | .memory .. :: _, hZ => by
    rcases hZ _ List.mem_cons_self with ⟨l', r', heq, -⟩ | ⟨mn', iname', conns', heq, -⟩ <;> cases heq

set_option maxHeartbeats 4000000 in
/-- **C4** `machine_ships_hierC_run` (FitChain:1073-1232) for a slotless module WITHOUT clock or reset input:
no rst/clk antecedent (FitChain:1145 deleted), no `hinitW`; the run at the zeroed seed moved to `seedIn` by A2. -/
theorem machine_ships_hierC_runNR {n : Nat} (hloc : ∀ D : Design, KSLocal (KSn (childMap D.modules) n))
    (Bnd : CtxBnd)
    (C : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    {declName : Name} (d : MachineData) {kD : Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc srcL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {extL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extBL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design →
      MachineTraceLB declName d m design dom srcL extL extBL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design} {b : Sparkle.IR.AST.Module},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule m ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)) →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      Tools.ShippingGen2Fit.ComposedNWRegsF n declName d kD m design dom src ext extB
        (fun regs => ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r))
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hsl0 : d.shape.layout.slots = [])
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : C mctx mref cctx cref)
    (facts : Bnd mctx mref cctx cref w raw D → RunFactsNR (childMap D.modules) b)
    (hnR : "rst" ∉ raw.inputs.map (·.name))
    (hnC : "clk" ∉ raw.inputs.map (·.name))
    (hZ : NoTouchZ ["rst", "clk"] raw.body) :
        Bnd mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk n raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j := by
  intro hBnd
  -- (new) the output names, from the run (the supplier)
  have houtOk := outNameOk_of_run hcore entry
  have hL := soundL hcore entry closes hBnd
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, hlink, houts, _, _, _, _, _, _, _, hclean, _⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hclean houtTy
  obtain ⟨hgate, hwfB, hndB, hself, hOut, hIW⟩ := facts hBnd
  have hOutM := Tools.ShippingHierPremisesBase.outsExtracted_sound hOut
  have hI : Tools.ShippingMachineShipsHier.hasInst b :=
    Tools.ShippingGuardsSound.hasInst_of_hierGate hgate
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · exact mergeChecked_inst h hI
  have hbB : b.body = raw.body := by rw [hbr]; exact hb
  have hbW : declWidth b = Tools.ShippingEntrySoundness.weOf raw := by rw [hbr]; exact hw
  have hbI : b.inputs = raw.inputs := by rw [hbr]; exact hi
  have hbO : b.outputs = raw.outputs := by rw [hbr]; exact ho
  have hmf : Tools.ConeFold.memFree raw.body := by
    rw [← hbB]; exact memFree_of_linkedWF _ hwfB
  -- (new) the case-(C) discriminant on `b`
  have hnRb : "rst" ∉ b.inputs.map (·.name) := by rw [hbI]; exact hnR
  have hnCb : "clk" ∉ b.inputs.map (·.name) := by rw [hbI]; exact hnC
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, hPw, lets, llen, wired, H⟩ :=
    composed hcore hpost entry closes hBnd hmf
  -- (new) no register: no slot
  have hregs0 : regs = [] := List.eq_nil_of_length_eq_zero (by simp [rlen, hslots, hsl0])
  subst hregs0
  refine ⟨ids, nd, len, cache, [], rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hinit hreset hinsFit hstX
  -- (changed) `H` at the zeroed seed: its reset/clock premises hold there for every state
  obtain ⟨envs, hrun, hlen, hobs, hfitI⟩ := H i bools bits T (slSeedZ b ins) st0 mems kids
    (fun t st ht => hsrc t (fun x => if x = "rst" ∨ x = "clk" then 0 else st x) ht)
    (fun t st r hr => by simp at hr)
    (fun t st => by simp [slSeedZ, seedIn, List.contains_eq_mem, hnRb])
    (fun t st => by simp [slSeedZ, seedIn, List.contains_eq_mem, hnCb])
    (fun k r f hr _ => by simp at hr) hreset
  -- (new) A2 at `Z := ["rst", "clk"]`: from the zeroed seed to `seedIn`
  obtain ⟨envs₂, hrun₂, hlen₂, hpt⟩ :=
    runModuleTG_seed_offZ (KSn (childMap D.modules) n) (hloc D) _ (childMap D.modules) hZ
      (slSeedZ_agree b ins) T _ envs hrun
  have hrunB : runModuleTG (KSn (childMap D.modules) n) (declWidth b) (childMap D.modules) b.body
      (seedIn b ins) T ⟨st0, mems, kids⟩ = some envs₂ := by
    rw [hbW, hbB]; exact hrun₂
  have hobs₂ : ∀ j (hj : j < envs₂.length) (k : Nat) (o : OutField) (f : Nat → Nat),
      d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
      (envs₂[j]'hj) o.name = f j := by
    intro j hj k o f hk hf
    rw [hpt j (by omega) hj o.name (outName_notZ (houtOk o (List.mem_of_getElem? hk)))]
    exact hobs j (by omega) k o f hk hf
  have hfitB : Tools.ShippingGen2Fit.KSBoundedRun (childMap D.modules) b.body envs₂ := by
    unfold Tools.ShippingGen2Fit.KSBoundedRun
    intro j hj mn iname conns hm child cwe hc p hp x hl
    have hm' : Stmt.inst mn iname conns ∈ raw.body := by rw [← hbB]; exact hm
    obtain ⟨c, hcm, -, hce⟩ := Tools.ShippingHierState.lookup_mem conns p.name (.ref x) hl
    have hxZ : x ∉ ["rst", "clk"] := by
      rcases hZ _ hm' with ⟨l, r, heq, -⟩ | ⟨mn', iname', conns', heq, hcz⟩
      · cases heq
      · cases heq
        exact hcz c hcm x hce
    rw [hpt j (by omega) hj x hxZ]
    exact hfitI j (by omega) mn iname conns hm' child cwe hc p hp x hl
  have houtSrc : ∀ (k : Nat) (o : OutField), d.shape.layout.outs[k]? = some o →
      o.name ∈ b.outputs.map (·.name) := by
    intro k o hk
    rw [hbO, houts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩, rfl⟩
  -- (new) no register statement in `b`: `hZ` admits assignments and instances only
  have hnoR : Sparkle.IR.OptCheck.seqRegs b = [] := by
    rw [Tools.ShippingSeqOptSoundness.seqRegs_eq, hbB]
    exact seqRegsL_nil_of_noTouch raw.body hZ
  by_cases hbind : hierBinds b = true
  · -- the optimizer: checked on the extracted interface, or not applied
    have hopt : checkedOptimize b = (if hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b))
        then deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
      unfold checkedOptimize
      simp only [simpleBody_inst hI, not_all_seqOk hI, hbind, Bool.false_eq_true, if_false, if_true]
    by_cases hacc : hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
    · -- accepted: the guards give conjuncts 2 and 4, the instance statements 5
      obtain ⟨hwfO, hndO⟩ := Tools.ShippingGuardsSound.deinline_guards
        (o := Sparkle.IR.Optimize.optimizeModule b) hacc hwfB hndB hOut
      have hselfO : Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules)
          (deinline b (Sparkle.IR.Optimize.optimizeModule b)).body = true :=
        Tools.ShippingChecksDerived2.all_inst_transfer _
          (fun mn iname conns =>
            (Tools.ShippingChecksDerived2.hierRefineCheck_inst_iff hacc mn iname conns).mp)
          (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hself
      have hnofb := Tools.ShippingHierPremisesBase.noSelfRead_sound hselfO
      rw [hopt, if_pos hacc]
      -- (changed) C1 in place of `hierRefineCheck_linked`
      obtain ⟨-, -, envsO, hrunO, hlenO, hcorr⟩ := hierRefineCheck_linked_noRst
        (KSn (childMap D.modules) n) (hloc D) (childMap D.modules) hacc
        hwfB hwfO hndB hndO hnofb hOutM ins hinsFit hrunB
        (Tools.ShippingGen2Fit.fitX_of_runR _ (childMap D.modules) b ins hwfB hIW T _ envs₂ hrunB hfitB hstX)
        hnoR
      refine ⟨envsO, hrunO, by omega, ?_⟩
      intro j hj k o f hk hf
      obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (houtSrc k o hk)
      rw [← hpn, hcorr p hp j hj (by omega), hpn]
      exact hobs₂ j (by omega) k o f hk hf
    · rw [hopt, if_neg hacc]
      exact ⟨envs₂, hrunB, by omega, hobs₂⟩
  · -- the check does not bind: the module is shipped as it is
    have hb0 : hierBinds b = false := by simpa using hbind
    rw [Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate hb0]
    exact ⟨envs₂, hrunB, by omega, hobs₂⟩

end Tools.ShippingGen2SlotlessTop

/-! ## C5a (ambient: OneOutTopO:255-278) -/
namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
open Tools.ShippingChildBndCore (cv dv)

set_option maxHeartbeats 4000000 in
/-- **C5a `oneOutSl_topShipsNC`** — the no-clock branch, published by name (S5's main top result): a one-output
slotless parent without a reset input (case C) ships at the top with NO clock/reset premise. `oneOut_topShipsO`
(OneOutTopO:334-415) with `hsl` → `hsl0`, the case binder `hrst`, conclusion `TopShipsNC`; then C4. -/
theorem oneOutSl_topShipsNC {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module}
    {D : Design}
    (hdata : MemParentDataOk p)
    (hord : ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
      (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hW : ∀ k, OneOutWidth P p k)
    (hrst : "rst" ∉ raw.inputs.map (·.name))
    (n : Nat) :
    TopShipsNC p (n + 1) p.decl b raw D := by
  cases Classical.em (Nonempty ι) with
  | inr hne =>
    -- `ι` empty: `h`'s existing witness; `∀ i` is vacuous (as OneOutTopO:353-357)
    obtain ⟨ids, nd, len, cache, regs, rnd, rlen, _⟩ := h
    unfold TopShipsNC
    exact ⟨ids, nd, len, cache, regs, rnd, rlen, fun i => (hne ⟨i⟩).elim⟩
  | inl hne =>
  obtain ⟨i0⟩ := hne
  obtain ⟨hok, hco, hslots, houtTy, hdomB⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hI := data_hI hdata
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have ranA := Tools.ShippingRanABridge.machineRanA_of_runJQC L.O hA L.T ran
  -- `kidsCombB` of the run, checked by its one-output closing (as `oneOut_composedNW`)
  obtain ⟨_, _, _, _, _, _, _, _, hcl, _⟩ :=
    Tools.ShippingParentDesignA.core_closeInstsA L.O p.d hins hsimple ranA
  have hkc : kidsCombB D.modules raw.body = true := Tools.ShippingChildServe.closeInsts_kidsComb hcl
  -- the trace's witness: `ids`, `cache` and the served evidence (the SAME `h`)
  obtain ⟨ids, _, len, cache, _, _, _, _, _, _, hx, _⟩ := id h
  -- (new) case (C): no clock input either — A1 on the trace's wiring, resolved by `hrst`
  have hnC : "clk" ∉ raw.inputs.map (·.name) := by
    have hLT := (Pkg.trace L.O L.T hA p ran).toLB
    obtain ⟨_, _, lenT, _, _, _, _, _, _, wiredT, _⟩ := id hLT
    rcases (Tools.ShippingGen2SlotlessParent.calls_ports_sl (d := p.d) wiredT lenT hsl0 (ok_outNameOk p.d hok) p.kD hkD
        hIlen hSL hSlen hLlen hNIn).2.1 with ⟨_, hr⟩ | ⟨hc, _⟩
    · exact absurd hr hrst
    · exact hc
  -- (new) B1: no statement touches the reset or the clock
  have hZ := slotlessParent_noTouch_ofRun L p hdata hins hsl0 hA ran hrst
  -- (changed) `RunFactsNR` field by field (no `hsl`; `core_runFactsHO` is not used)
  have factsB : ∀ {b' : Sparkle.IR.AST.Module}, (b' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingGen2SlotlessTop.RunFactsNR (childMap D.modules) b' := fun hpb =>
    { gate := Tools.ShippingParentDesignO.core_hierGate_anyO L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins
        houtTy hpb ranA
      wfB := Tools.ShippingParentTailsO.core_linkedWF_ranO L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins houtTy
        hpb ranA
      ndB := Tools.ShippingParentDesignO.core_instNames₁O L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins hsimple
        houtTy hpb ranA
      self := Tools.ShippingParentDesignO.core_noSelfRead₁O L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins
        hsimple houtTy hpb ranA
      outs := Tools.ShippingParentDesignO.core_outsExtracted₁O L.O p.d hok (Pkg.body_eq p) hco hslots hdomB hins
        hsimple houtTy hpb ranA
      wid := core_instOutWidthsOk_oneO L.O p.d hok (Pkg.body_eq p) (nDecl := p.kD) hco hslots hdomB hins hsimple
        houtTy hpb ranA len cache
        (fun _ hk _ _ _ hargs hst hcs hmod =>
          oneOutWidthAtO L P p hx.2 hsimple hord hW i0 hk hargs hst hcs hmod) }
  -- the run-local fit chain (FitChain): `ComposedHBF` → `ComposedNWF` at height `n + 1`
  have hNWF := Tools.ShippingGen2Fit.composedNWn_of_HBF (n + 1) (R := fun _ _ => True)
    (machine_linked_callsServed1F L P p h hsimple hkD hI hIlen hSL hSlen hLlen hNIn hkc hdec hW)
    (by unfold Tools.ShippingMachineDepthH.BoundH; intros; trivial)
    (Tools.ShippingMachineDepthHR.kidsComb_of_B hkc)
  let Bnd : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx' mref' cctx' cref' w' m' D' =>
    mctx' = mctx ∧ mref' = mref ∧ cctx' = cctx ∧ cref' = cref ∧ w' = w ∧ m' = raw ∧ D' = D
  have key := Tools.ShippingGen2SlotlessTop.machine_ships_hierC_runNR (n := n + 1)
    (fun D' => Tools.ShippingHierStateG.KSn_local _ _) Bnd (fun _ _ _ _ => True)
    p.d (kD := p.kD) (src := p.src) (ext := p.extS) (extB := p.extBS)
    (lsrc := p.lsrc) (srcL := p.src) (extL := p.extS) (extBL := p.extBS)
    (fun {mctx'} {mref'} {cctx'} {cref'} {w'} {w''} {m'} {design'} _ _ _ hB => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hB
      exact (Pkg.trace L.O L.T hA p ran).toLB)
    (fun {mctx'} {mref'} {cctx'} {cref'} {w'} {w''} {m'} {design'} {b'} _ hpb _ _ hB _ => by
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hB
      refine Tools.ShippingGen2Fit.composedNWRegsF_of_composedNWF _ hNWF ?_
      intro _ _ _ _ _ _ hWr
      exact Tools.ShippingSrm32.hWd_of_wired hpb (factsB hpb).gate houtTy hWr)
    houtTy hslots hsl0 hcore hpost entry trivial (fun _ => factsB hpost) hrst hnC hZ
  exact key ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Tools.ShippingGen2
