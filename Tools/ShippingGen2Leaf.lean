import Tools.ShippingGen2MemShips
import Tools.ShippingGen2LeafSeq
import Tools.ShippingC4InitW
import Tools.ShippingMachineShipsS
import Tools.ShippingChecksDerived
import Tools.ShippingLeafEntry
import Tools.ShippingGuardsLeaf
import Tools.ShippingLeafSat
set_option autoImplicit false

/-! # M2-a2: the register leaf ships (`leaf_ships : LeafStmt' L`; scripts/gen2/LEAF_FREEZE.md rev2)

`LeafStmt'` is the frozen `LeafStmt` with three approved changes (review of 1ddb25c6, §3): `DataOk := LeafDataOk`
(decidable), the premise `ExtInS p`, and the case `slots ≠ []`. It does NOT discharge the old all-leaf `LeafStmt`:
the slotless leaf is the mandatory obligation G-SLOTLESS (`sparkle-gen2-step`).

Route: the A-boundary trace `(Pkg.trace L.O L.T hA p ran).toLB` of the run, then pure lemmas only. `TopShips` copies
the run part of `machine_ships` (no SV part) on the trace as given; `ChildShips` moves the trace to the identity
extension (`traceL_of_LB`, from `ExtInS` and `bsIn.take kD = bsIn`) and applies the copied `seqChildRun_of_L` and
`seqChildRunN_of_flat`. `JQC (dv w) w`, `MachineDefines` and the run itself are not used beyond `ran`/`hpost`. -/
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
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildBndCore (cv dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The approved statement (freeze rev2 §3) -/

def LeafDataOkB (p : Pkg ι dom) : Bool :=
  p.d.ok && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)

def LeafDataOk (p : Pkg ι dom) : Prop := LeafDataOkB p = true

/-- **The register-leaf lemma**: `LeafStmt L LeafDataOk` with `ExtInS p` after the data premise and
`slots ≠ []` after `insts = []`. -/
def LeafStmt' {mref cref} (L : Laws mref cref) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    LeafDataOk p → ExtInS p → p.d.shape.insts = [] → p.d.shape.layout.slots ≠ [] →
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    ∀ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D

theorem LeafDataOk.rows {p : Pkg ι dom} (h : LeafDataOk p) :
    p.d.ok = true ∧ p.d.callsOk p.kD = true ∧ p.d.ss.length = p.d.shape.layout.slots.length ∧
      (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width) := by
  unfold LeafDataOk LeafDataOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Without calls, the declared inputs are all below `kD`. -/
theorem leaf_take (d : MachineData) (kD : Nat) (hok : d.ok = true) (hco : d.callsOk kD = true)
    (hnoI : d.shape.insts = []) : d.bsIn.take kD = d.bsIn := by
  have h := data_hIlen d kD hok hco
  rw [hnoI, List.length_drop] at h
  exact List.take_of_length_le (by simp at h; omega)

/-! ## The trace at the identity extension -/

/-- A trace whose extensions are the inputs below the declared arity is a trace at the identity extension. -/
theorem traceL_of_LB {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (h : MachineTraceLB declName d m dsn dom src ext extB lsrc)
    (hb : ∀ i bools bits j, j < d.bsIn.length → extB i bools bits j = bools j)
    (hv : ∀ i bools bits j n, j < d.bsIn.length → ext i bools bits j n = bits j n) :
    MachineTraceL declName d m dsn dom src (fun _ _ bits => bits) lsrc := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems hin hpass hrst hinit
  refine H i bools bits T seed st0 mems (fun t st ht => ?_) hpass hrst hinit
  exact sourceInputs_congr nd (fun j hj => by simp only [hb i bools bits j hj])
    (fun j hj n => by simp only [hv i bools bits j n hj]) (hin t st ht)

/-! ## The module facts of a register leaf -/

/-- The returned module of a register leaf is in the register fragment and not of simple shape. -/
theorem leaf_b_facts {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {raw b : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache raw dsn regs lets)
    (rlen : regs.length = d.ss.length)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    (refineCheck (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b = true ∨
      b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ∧
    b.body.all seqStmtOk = true ∧ simpleBody b = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, _, _, _⟩, _, hregs, _, _, _, _, _, hok⟩ := hclean hnoI houtTy
  generalize Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hpost ⊢
  obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons f _ => exact ⟨f, rfl⟩
  obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
    cases hrs : regs with
    | nil =>
      have : d.shape.layout.slots.length = 0 := by rw [← hSS, ← rlen, hrs]; rfl
      rw [List.length_eq_zero_iff] at this; exact absurd this hsl
    | cons r _ => exact ⟨r, rfl⟩
  obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
  have hnA : r0.body.all isAssign = false := by
    apply List.all_eq_false.mpr
    exact ⟨_, hb ▸ hm0, by simp [isAssign]⟩
  have hr0ok : r0.body.all seqStmtOk = true := by rw [hb]; exact hok
  have hmerge : refineCheck r0 b = true ∨ b = r0 := by
    rcases hpost with rfl | rfl
    · exact Or.inr rfl
    · exact mergeChecked_nonAssign hnA
  refine ⟨hmerge, ?_, ?_⟩
  · rcases hmerge with h | rfl
    · exact Tools.ShippingMachineShipping.refineCheck_stmtOk_o h
    · exact hr0ok
  · apply Tools.ShippingLeafEntry.simpleBody_false_of
    rcases hpost with rfl | rfl
    · exact hnA
    · exact Tools.ShippingGuardsLeaf.mergeChecked_keeps_nonAssign hnA

/-! ## Step 1: `TopShips` of a register leaf (pure; the trace as given, no `ExtInS`) -/

theorem leaf_topShips_of_LB (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (n : Nat) :
    TopShips p n p.decl b raw D := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, _, wired, tr⟩ := id hL
  obtain ⟨hmerge, hbok, hsB⟩ := leaf_b_facts wired rlen hnoI hsl hSS houtTy hpost
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, hevery, _, _, _, _, _⟩ := hclean hnoI houtTy
  have hinitW := Tools.ShippingC4InitW.hinitW_of_ok p.d hok
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hinp hpass hrstG _ hinit _ hinsB _
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost hmerge
  have hbIn : b.inputs = r0.inputs ∧ b.outputs = r0.outputs ∧ declWidth b = declWidth r0 := by
    rcases hpost with rfl | rfl
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨(mergeChecked_ports r0).1, (mergeChecked_ports r0).2.1,
        Tools.ShippingLeafSat.declWidth_mergeChecked r0⟩
  obtain ⟨hbi, hbo, hbw⟩ := hbIn
  have hseed : seedIn b ins = seedIn r0 ins := Tools.ShippingPipelineSoundness.seedIn_of_inputs hbi ins
  have hrstR : "rst" ∈ r0.inputs.map (·.name) := by rw [hi]; exact hrstIn hsl
  -- R-G: the reset premise is required exactly because `"rst"` is an input of `b`
  have hrstZ : ∀ t, ins t "rst" = 0 := hrstG (by rw [hbi]; exact hrstR)
  -- the core module's run
  obtain ⟨envs, hrun, hlen, hobs, _⟩ := tr i bools bits T (seedIn r0 ins) st0 mems
    (fun t st ht => by have := hinp t st ht; rw [htake, hseed] at this; exact this)
    (fun t st r hr => by rw [← hseed]; exact hpass t st r hr)
    (fun t st => by simp [seedIn, List.contains_eq_mem, hrstR, hrstZ])
    hinit
  have hrun0 : runModule (declWidth r0) r0.body (seedIn r0 ins) T st0 mems = some envs := by
    rw [hb, show declWidth r0 = weOf r0 from rfl, hw]; exact hrun
  -- every register of the core module is a slot's, at its reset value
  have hfitR : ∀ r ∈ seqRegs r0, st0 r.1 < 2 ^ declWidth r0 r.1 := by
    intro r hr
    obtain ⟨rn, rc, rrs, rinp, rinit⟩ := r
    have hm : Stmt.register rn rc rrs rinp rinit ∈ raw.body :=
      hb ▸ Tools.ShippingMachineChild.mem_seqRegs.mpr hr
    obtain ⟨k, f, hk, hf, _⟩ := hevery rn rc rrs rinp rinit hm
    obtain ⟨hwid, _⟩ := hregs k rn f hk hf
    show st0 rn < 2 ^ declWidth r0 rn
    rw [hinit k rn f hk hf, show declWidth r0 = weOf r0 from rfl, hw, hwid]
    exact hinitW f (List.mem_of_getElem? hf)
  have hinsR : ∀ t x, x ∈ r0.inputs.map (·.name) → ins t x < 2 ^ declWidth r0 x := by
    intro t x hx; rw [← hbw]; exact hinsB t x (by rw [hbi]; exact hx)
  -- the merge
  have stepB : ∃ envsB, runModule (declWidth b) b.body (seedIn r0 ins) T st0 mems = some envsB ∧
      envsB.length = envs.length ∧
      ∀ q ∈ r0.outputs, ∀ j (hj : j < envsB.length) (hj' : j < envs.length),
        (envsB[j]'hj) q.name = (envs[j]'hj') q.name := by
    rcases hmerge with hchk | rfl
    · exact Tools.ShippingRefineSoundness.refineCheck_transfer hchk ins hinsR hrstR hrstZ (stO := st0)
        (fun _ _ => rfl) hfitR hrun0
    · exact ⟨envs, hrun0, rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨envsB, hrunB, hlenB, hcorrB⟩ := stepB
  -- the optimizer
  have hfitB : ∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1 := by
    rcases hmerge with hchk | rfl
    · intro ro hro
      obtain ⟨rm, hrm, hname, hwidth⟩ := Tools.ShippingMachineShipsS.refineCheck_regWidth hchk ro hro
      rw [← hwidth, ← hname]; exact hfitR rm hrm
    · exact hfitR
  have hrstB : "rst" ∈ b.inputs.map (·.name) := by rw [hbi]; exact hrstR
  have stepO : ∃ envsO, runModule (declWidth (checkedOptimize b)) (checkedOptimize b).body
        (seedIn b ins) T st0 mems = some envsO ∧ envsO.length = envsB.length ∧
      ∀ q ∈ b.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envsB.length),
        (envsO[j]'hj) q.name = (envsB[j]'hj') q.name := by
    rw [← hseed] at hrunB
    rcases checkedOptimize_seqOk hsB hbok with hopt | heq
    · exact Tools.ShippingRefineSoundness.refineCheck_transfer hopt ins hinsB hrstB hrstZ (stO := st0)
        (fun _ _ => rfl) hfitB hrunB
    · rw [heq]; exact ⟨envsB, hrunB, rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨envsO, hrunO, hlenO, hcorrO⟩ := stepO
  refine ⟨envsO, ?_, by omega, ?_⟩
  · rw [runModuleTG_instFree _ _ _ _
      (Tools.ShippingMachineDepthRun.instFree_of_seqOk
        (Tools.ShippingChecksDerived.checkedOptimize_seqOk_all hbok))]
    exact hrunO
  · intro j hj k o f hk hf
    have hq : ({ name := o.name, ty := o.ty } : Port) ∈ r0.outputs := by
      rw [ho, houts]; exact List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩
    have h1 : (envsO[j]'hj) o.name = (envsB[j]'(by omega)) o.name :=
      hcorrO _ (by rw [hbo]; exact hq) j hj (by omega)
    have h2 : (envsB[j]'(by omega)) o.name = (envs[j]'(by omega)) o.name :=
      hcorrB _ hq j (by omega) (by omega)
    rw [h1, h2]
    exact hobs j (by omega) k o f hk hf

/-! ## Step 2: `ChildShips` of a register leaf (pure; `ExtInS` moves the trace to the identity extension) -/

theorem leaf_childShips_of_LB (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) (hext : ExtInS p)
    (hnoI : p.d.shape.insts = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (n : Nat) :
    ChildShips p n b D := by
  have hkD : p.d.bsIn.length ≤ p.kD := by
    have h := congrArg List.length htake
    rw [List.length_take] at h
    omega
  have hLid := traceL_of_LB hL (fun i bools bits j hj => hext.1 i bools bits j (by omega))
    (fun i bools bits j n' hj => hext.2 i bools bits j n' (by omega))
  obtain ⟨_, _, _, _, regs, _, rlen, _, _, wired, _⟩ := id hL
  obtain ⟨_, hbok, _⟩ := leaf_b_facts wired rlen hnoI hsl hSS houtTy hpost
  have hS : ∀ i, p.S i = fun vals => p.src i (boolsOf (D := dom i) p.d.bsIn vals)
      (bitsOf (D := dom i) p.d.bsIn vals) := by
    intro i; funext vals; simp only [Pkg.S, htake]
  intro dsn _ _ i
  rw [hS i, htake]
  exact Or.inl <| seqChildRunN_of_flat (childMap dsn.modules) dsn
    (Tools.ShippingMachineDepthRun.instFree_of_seqOk hbok)
    (Tools.ShippingGen2LeafSeq.seqChildRun_of_L hLid hpost hnoI hsl (data_hSlen p.d hok hSS) hSS
      (data_hLlen p.d hok) houtTy (Tools.ShippingC4InitW.hinitW_of_ok p.d hok) i) n

/-! ## Step 3: the register leaf ships -/

/-- **M2-a2: the register leaf ships** (`LeafStmt'`, approved freeze rev2 §3). -/
theorem leaf_ships (L : Laws mref cref) : LeafStmt' (ι := ι) (dom := dom) L := by
  intro p mctx cctx w w1 raw b D hdata hext hnoI hsl hA _ _ hpost _ ran n
  obtain ⟨hok, hco, hSS, houtTy⟩ := hdata.rows
  have htake := leaf_take p.d p.kD hok hco hnoI
  have hL := (Pkg.trace L.O L.T hA p ran).toLB
  exact ⟨leaf_topShips_of_LB p hL hnoI hsl hok hSS houtTy htake hpost n,
    leaf_childShips_of_LB p hL hext hnoI hsl hok hSS houtTy htake hpost n⟩

end Tools.ShippingGen2
