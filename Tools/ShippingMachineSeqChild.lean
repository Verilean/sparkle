import Tools.ShippingMachineChild

/-! # A sequential child's own theorem, as what its instances do over time

A machine-route child WITH registers (slots) and without calls has a trace
theorem about its core module. Over any number of cycles, from its reset
state, with its argument ports carrying an in-range value stream `vals`
(decoded into the source's input Signals) and reset low, the core module's
run drives its output ports with the source observations of those Signals.
This is the sequential counterpart of `childFn_of_trace`: the input is a
stream, the state a register file. -/
namespace Tools.ShippingMachineChild
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineCompose
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingEntrySoundness (weOf RunsTo)
open Sparkle.Core
open Tools.ShippingMachineDenote (tys)
open Tools.ShippingSeqOptSoundness (seedIn)

/-- The source's Bool inputs decoded from a port-value stream. -/
def boolsOf {D : DomainConfig} (bs : List (Name × MixedGateBinder)) (vals : Nat → List Nat) :
    Nat → Signal D Bool :=
  fun p => ⟨fun τ => decB bs (vals τ) p⟩

/-- The source's bit-vector inputs decoded from a port-value stream. -/
def bitsOf {D : DomainConfig} (bs : List (Name × MixedGateBinder)) (vals : Nat → List Nat) :
    (j : Nat) → (n : Nat) → Signal D (BitVec n) :=
  fun p n => ⟨fun τ => decV bs (vals τ) p n⟩

/-- **Argument ports carrying in-range values are the source inputs they
decode to.** -/
theorem sourceInputs_of_vals {declName : Name} {bsIn : List (Name × MixedGateBinder)}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} (nd : ids.Nodup)
    (hlenIn : bsIn.length ≤ ids.length) {raw : Sparkle.IR.AST.Module}
    (hargs : argPorts raw = machPorts declName ids cache bsIn) (env : Env) (vals : List Nat)
    (hvals : (argPorts raw).map (fun p => env p.name) = vals)
    (hrange : InRange vals (bsIn.filter fun b => b.2 != .domain)) :
    SourceInputs declName bsIn ids cache (fun j => decB bsIn vals j)
      (fun j n => decV bsIn vals j n) env := by
  unfold SourceInputs
  apply admissible_of_portsD
  rw [show inputPorts (boolValues ids fun j => decB bsIn vals j)
      (bitValues ids fun j n => decV bsIn vals j n) (bsIn.zip ids)
      (start (entryCompilerState false cache) declName.toString) =
      machPorts declName ids cache bsIn from inputPorts_congr _ _ _ rfl, ← hargs]
  have hlenP : (argPorts raw).length =
      ((bsIn.zip ids).filter fun b => b.1.2 != .domain).length := by
    rw [hargs, machPorts_length _ hlenIn, ← zip_filter_fst _ _ hlenIn, List.length_map]
  apply Zip₂.of_get hlenP
  intro q p b hp hb
  obtain ⟨pos, hpos, hcnt⟩ := filter_getElem_pos _ _ q b hb
  obtain ⟨⟨nm, kind⟩, id⟩ := b
  obtain ⟨hb1, hb2⟩ := List.getElem?_zip_eq_some.mp hpos
  have hidx : ids.idxOf id = pos := by
    have hlt : pos < ids.length := (List.getElem?_eq_some_iff.mp hb2).1
    have hg : ids[pos]! = id := by simp [List.getElem!_eq_getElem?_getD, hb2]
    rw [← hg]; exact index_fresh ids nd pos hlt
  have hport : portIdx bsIn pos = q := by
    unfold portIdx
    have hpl : pos < bsIn.length := (List.getElem?_eq_some_iff.mp hb1).1
    rw [← hcnt, show (bsIn.zip ids).take pos = (bsIn.take pos).zip (ids.take pos) from
      List.take_zipWith, ← zip_filter_fst (bsIn.take pos) (ids.take pos)
      (by simp only [List.length_take]; omega), List.length_map]
  have hval : vals.getD q 0 = env p.name := by
    rw [← hvals]; simp [List.getD_eq_getElem?_getD, hp]
  have hfq : (bsIn.filter fun b => b.2 != .domain)[q]? = some (nm, kind) := by
    rw [← zip_filter_fst _ _ hlenIn, List.getElem?_map, hb]; rfl
  have hr := inRange_get hrange q (nm, kind) hfq
  rw [hval] at hr
  simp only [binderEnc]
  cases kind with
  | domain =>
    have := (List.mem_filter.mp (List.mem_of_getElem? hb)).2
    simp at this
  | bool =>
    simp only [boolValues, hidx, decB, hport, hval]
    simp only [Tools.ShippingMuxLoweringSoundness.encodeBool]
    simp only at hr
    split <;> simp_all <;> omega
  | bits n =>
    simp only [bitValues, hidx, decV, hport, hval]
    simp only at hr
    simp [Nat.mod_eq_of_lt hr]

/-- **A sequential child's own theorem gives what its core module does over
time.** -/
theorem seqStream_of_trace {declName : Name} {d : MachineData} {raw : Sparkle.IR.AST.Module}
    {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (h : MachineTraceL declName d raw dsn dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width) (i : ι) :
    ∀ (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
      (vals : Nat → List Nat),
      (∀ τ, τ < T → InRange (vals τ) (d.bsIn.filter fun b => b.2 != .domain)) →
      (∀ t, t < T → (argPorts raw).map (fun p => ins t p.name) = vals (T - 1 - t)) →
      (∀ t, ins t "rst" = 0) →
      (∀ r rk inp init, Stmt.register r "clk" ("rst", rk) inp init ∈ raw.body →
        st0 r = init.toNat) →
      ∃ envs, runModule (weOf raw) raw.body (seedIn raw ins) T st0 mems = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o →
          (src i (boolsOf d.bsIn vals) (bitsOf d.bsIn vals))[k]? = some f →
          (envs[j]'hj) o.name = f j := by
  obtain ⟨ids, nd, len, cache, regs, _, rlen, lets, _, wired, trace⟩ := h
  obtain ⟨_, _, regsIn, _, _, _, _, _, hins, _, hclean, _⟩ := wired
  obtain ⟨_, hrstIn, hregs, _⟩ := hclean hnoI houtTy
  intro T ins st0 mems vals hrange hports hrstZ hreset
  -- the argument ports are the declaration's ports
  have hbsIn : d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
      d.shape.layout.lets) = d.bsIn := by
    have hb := d.binders_split
    rw [← hSlen, ← hLlen]
    conv => lhs; rw [hb]
    simp only [List.length_append]
    rw [show d.bsIn.length + d.slotBs.length + d.letBs.length - d.slotBs.length - d.letBs.length =
      d.bsIn.length by omega, List.append_assoc, List.take_left]
  have hargs : argPorts raw = machPorts declName ids cache d.bsIn := by
    unfold argPorts; rw [hins hnoI, hbsIn]
  have hlenIn : d.bsIn.length ≤ ids.length := by
    rw [len]; simp only [MachineData.bsIn, List.length_take]; omega
  have hrst : "rst" ∈ raw.inputs.map (·.name) := hrstIn hsl
  obtain ⟨envs, hrun, hlenE, hobs, _⟩ := trace i (boolsOf d.bsIn vals) (bitsOf d.bsIn vals) T
    (seedIn raw ins) st0 mems
    (fun t st ht => by
      refine sourceInputs_of_vals nd hlenIn hargs (seedIn raw ins t st) (vals (T - 1 - t)) ?_
        (hrange _ (by omega))
      rw [← hports t ht]
      apply List.map_congr_left
      intro p hp
      have hpi : p ∈ raw.inputs := (List.mem_filter.mp hp).1
      simp [seedIn, List.contains_eq_mem, List.mem_map_of_mem hpi])
    (fun t st r hr => by
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
      have hks : k < d.shape.layout.slots.length := by rw [← hSS, ← rlen]; exact hk
      obtain ⟨_, hnot, _⟩ := hregs k _ _ (List.getElem?_eq_getElem hk)
        (List.getElem?_eq_getElem hks)
      simp [seedIn, List.contains_eq_mem, hnot])
    (fun t st => by simp [seedIn, List.contains_eq_mem, hrst, hrstZ])
    (fun k r f hr hf => by
      obtain ⟨_, _, rk, inp, hmem⟩ := hregs k r f hr hf
      rw [hreset r rk inp _ hmem]; rfl)
  exact ⟨envs, hrun, hlenE, hobs⟩

/-! ## The merge's registers -/

open Sparkle.IR.RefineCheck Sparkle.IR.OptCheck in
/-- `refineCheck` pairs every register of the accepted module with the
original's register of the same name and reset value, the original's
register names being distinct. -/
theorem refineCheck_regs {m o : Sparkle.IR.AST.Module} (h : refineCheck m o = true) :
    ((seqRegs m).map (·.1)).Nodup ∧
      ∀ ro ∈ seqRegs o, ∃ rm, regOf (seqRegs m) ro.1 = some rm ∧ rm.2.2.2.2 = ro.2.2.2.2 := by
  simp only [refineCheck] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨h1.1.1.1.1.1.1.1.2, ?_⟩
  intro ro hro
  have h11 := List.all_eq_true.mp h1.1.2 ro hro
  revert h11
  cases hr : regOf (seqRegs m) ro.1 with
  | none => simp
  | some rm =>
    intro h11
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h11
    exact ⟨rm, rfl, h11.1.1.2⟩

open Sparkle.IR.RefineCheck in
/-- In a list with distinct names, the lookup by an element's name finds it. -/
theorem regOf_mem {rs : List (String × String × (String × Sparkle.IR.Type.ResetKind) ×
      Sparkle.IR.AST.Expr × Int)} (hnd : (rs.map (·.1)).Nodup) {r : String × String ×
      (String × Sparkle.IR.Type.ResetKind) × Sparkle.IR.AST.Expr × Int} (hr : r ∈ rs) :
    regOf rs r.1 = some r := by
  unfold regOf
  induction rs with
  | nil => cases hr
  | cons x rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    · have hne : (x.1 == r.1) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        exact hnd.1 (he ▸ List.mem_map_of_mem hr)
      simp only [List.find?_cons, hne]
      exact ih hnd.2 hr

open Sparkle.IR.OptCheck in
theorem mem_seqRegs {m : Sparkle.IR.AST.Module} {r c : String}
    {rs : String × Sparkle.IR.Type.ResetKind} {inp : Sparkle.IR.AST.Expr} {init : Int} :
    Stmt.register r c rs inp init ∈ m.body ↔ (r, c, rs, inp, init) ∈ seqRegs m := by
  unfold seqRegs
  rw [List.mem_filterMap]
  constructor
  · intro h; exact ⟨_, h, rfl⟩
  · rintro ⟨st, hst, he⟩
    cases st <;> simp at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
    exact hst

theorem declWidth_of_wires {a b : Sparkle.IR.AST.Module} (h : a.wires = b.wires) :
    Sparkle.IR.RegDedup.declWidth a = Sparkle.IR.RegDedup.declWidth b := by
  funext x; unfold Sparkle.IR.RegDedup.declWidth; rw [h]

/-- Port types of the hardware binders, alongside the filtered binder list. -/
theorem inputPorts_typesD {bools bits} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      Zip₂ (fun (p : Port) b => p.ty = kindTy b.1.2) (inputPorts bools bits L a)
        (L.filter fun b => b.1.2 != .domain)
  | [], _ => .nil
  | ((name, .domain), id) :: rest, a => by
    simp only [inputPorts, List.filter_cons]
    simpa using inputPorts_typesD rest _
  | ((name, .bool), id) :: rest, a => by
    simp only [inputPorts, List.filter_cons]
    exact .cons rfl (inputPorts_typesD rest _)
  | ((name, .bits n), id) :: rest, a => by
    simp only [inputPorts, List.filter_cons]
    exact .cons rfl (inputPorts_typesD rest _)

/-- An input of a module is an argument port, the clock or the reset. -/
theorem input_cases {mc : Sparkle.IR.AST.Module} {x : String} (hx : x ∈ mc.inputs.map (·.name)) :
    x ∈ (argPorts mc).map (·.name) ∨ x = "clk" ∨ x = "rst" := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  by_cases hc : p.name = "clk"
  · exact Or.inr (Or.inl hc)
  by_cases hr : p.name = "rst"
  · exact Or.inr (Or.inr hr)
  refine Or.inl (List.mem_map.mpr ⟨p, ?_, rfl⟩)
  unfold argPorts
  exact List.mem_filter.mpr ⟨hp, by simp [hc, hr]⟩

/-- A run reads its seeding only below its length. -/
theorem runModule_seed_congr' (we : WEnv) (body : List Stmt) :
    ∀ (k : Nat) (s1 s2 : Nat → (String → Nat) → Env),
    (∀ td, td < k → s1 td = s2 td) →
    ∀ (st : String → Nat) (mems : MEnv),
    runModule we body s1 k st mems = runModule we body s2 k st mems
  | 0, _, _, _, _, _ => rfl
  | k + 1, s1, s2, h, st, mems => by
    simp only [runModule, Option.bind_eq_bind]
    rw [h k (by omega)]
    congr 1
    funext r
    rw [runModule_seed_congr' we body k s1 s2 (fun td htd => h td (by omega))]

open Sparkle.IR.RefineCheck Sparkle.IR.OptCheck in
open Tools.ShippingRefineSoundness (refineCheck_transfer) in
/-- **A sequential child at the full entry.** The module a run of
`synthesizeCombinational` returns for a machine-route child with slots and
without calls: over any number of cycles, from its reset state (every
register at its reset value), with its argument ports carrying an in-range
value stream and reset low, its run drives the output ports with the
source's observations of the decoded input Signals. -/
theorem seqStream_full {declName : Name} {d : MachineData} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (sound : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hinitFit : ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width) (i : ι)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∀ (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
      (vals : Nat → List Nat),
      (∀ τ, τ < T → InRange (vals τ) (d.bsIn.filter fun b => b.2 != .domain)) →
      (∀ t, t < T → (argPorts b).map (fun p => ins t p.name) = vals (T - 1 - t)) →
      (∀ t, ins t "rst" = 0) → (∀ t, ins t "clk" = 0) →
      (∀ r c rs inp init, Stmt.register r c rs inp init ∈ b.body → st0 r = init.toNat) →
      ∃ envs, runModule (Sparkle.IR.RegDedup.declWidth b) b.body (seedIn b ins) T st0 mems =
          some envs ∧ envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o →
          (src i (boolsOf d.bsIn vals) (bitsOf d.bsIn vals))[k]? = some f →
          (envs[j]'hj) o.name = f j := by
  intro T ins st0 mems vals hrange hports hrstZ hclkZ hreset
  obtain ⟨raw, D, w1, hcore, hpost⟩ :=
    Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  have h := sound hcore entry closes
  obtain ⟨ids, nd, len, cache, regs, _, rlen, _, _, wired, _⟩ := id h
  obtain ⟨_, _, _, _, _, _, _, houts, hins, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, hevery, _, _, _, hinW, _⟩ := hclean hnoI houtTy
  -- the argument ports are the declaration's, of its binders' types
  have hbsIn : d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
      d.shape.layout.lets) = d.bsIn := by
    have hb := d.binders_split
    rw [← hSlen, ← hLlen]
    conv => lhs; rw [hb]
    simp only [List.length_append]
    rw [show d.bsIn.length + d.slotBs.length + d.letBs.length - d.slotBs.length - d.letBs.length =
      d.bsIn.length by omega, List.append_assoc, List.take_left]
  have hargs : argPorts raw = machPorts declName ids cache d.bsIn := by
    unfold argPorts; rw [hins hnoI, hbsIn]
  have hlenIn : d.bsIn.length ≤ ids.length := by
    rw [len]; simp only [MachineData.bsIn, List.length_take]; omega
  have hbIn : b.inputs = raw.inputs := by
    rcases hpost with rfl | rfl
    · exact hi
    · exact (Sparkle.IR.RefineCheck.mergeChecked_ports _).1.trans hi
  have hargsB : argPorts b = argPorts raw := by unfold argPorts; rw [hbIn]
  -- an input value below the reset index fits its port
  have fitRaw : ∀ t, t < T → ∀ x, x ∈ raw.inputs.map (·.name) →
      ins t x < 2 ^ weOf raw x := by
    intro t ht x hx
    rcases input_cases hx with ha | hcr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain ⟨q, hq, hpq⟩ := List.getElem_of_mem hp
      have hpq' : (argPorts raw)[q]? = some p := by rw [List.getElem?_eq_getElem hq, hpq]
      have hval : (vals (T - 1 - t)).getD q 0 = ins t p.name := by
        rw [← hports t ht, hargsB]; simp [List.getD_eq_getElem?_getD, hpq']
      -- the port's binder
      have hty := inputPorts_typesD (bools := fun _ => false) (bits := fun _ n => 0#n)
        (d.bsIn.zip ids) (start (entryCompilerState false cache) declName.toString)
      rw [show inputPorts (fun _ => false) (fun _ n => 0#n) (d.bsIn.zip ids)
          (start (entryCompilerState false cache) declName.toString) =
          machPorts declName ids cache d.bsIn from rfl, ← hargs] at hty
      obtain ⟨b, hb'⟩ : ∃ b, ((d.bsIn.zip ids).filter fun b => b.1.2 != .domain)[q]? = some b := by
        have hl := hty.length_eq
        exact ⟨_, List.getElem?_eq_getElem (by rw [← hl]; exact hq)⟩
      have hpt := Zip₂.get hty q p b hpq' hb'
      have hfq : (d.bsIn.filter fun b => b.2 != .domain)[q]? = some b.1 := by
        rw [← zip_filter_fst _ _ hlenIn, List.getElem?_map, hb']; rfl
      have hr := inRange_get (hrange (T - 1 - t) (by omega)) q b.1 hfq
      rw [hval] at hr
      have hpi : p ∈ raw.inputs := (List.mem_filter.mp hp).1
      have hpn := (List.mem_filter.mp hp).2
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpn
      rw [hinW p hpi hpn.1 hpn.2, hpt]
      obtain ⟨⟨nm, kind⟩, id⟩ := b
      cases kind with
      | domain =>
        have := (List.mem_filter.mp (List.mem_of_getElem? hb')).2
        simp at this
      | bool => simpa [kindTy] using hr
      | bits n => simpa [kindTy] using hr
    · rcases hcr with rfl | rfl
      · rw [hclkZ]; exact Nat.two_pow_pos _
      · rw [hrstZ]; exact Nat.two_pow_pos _
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost
  have hargs0 : argPorts r0 = argPorts raw := by unfold argPorts; rw [hi]
  have hseed0 : seedIn r0 ins = seedIn raw ins :=
    Tools.ShippingPipelineSoundness.seedIn_of_inputs hi ins
  have run0 : ∀ st, runModule (weOf raw) raw.body (seedIn raw ins) T st mems =
      runModule (Sparkle.IR.RegDedup.declWidth r0) r0.body (seedIn r0 ins) T st mems := by
    intro st
    rw [hb, hseed0, show Sparkle.IR.RegDedup.declWidth r0 = weOf r0 from rfl, hw]
  -- the run of the core module, from a state with every register at reset
  have core : ∀ st, (∀ r c rs inp init, Stmt.register r c rs inp init ∈ raw.body →
      st r = init.toNat) →
      (∀ t, t < T → (argPorts r0).map (fun p => ins t p.name) = vals (T - 1 - t)) →
      ∃ envs, runModule (Sparkle.IR.RegDedup.declWidth r0) r0.body (seedIn r0 ins) T st mems =
          some envs ∧ envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o →
          (src i (boolsOf d.bsIn vals) (bitsOf d.bsIn vals))[k]? = some f →
          (envs[j]'hj) o.name = f j := by
    intro st hst hp
    obtain ⟨envs, hrun, hlen, hobs⟩ := seqStream_of_trace h hnoI hsl hSlen hSS hLlen houtTy i T ins
      st mems vals hrange (by rw [← hargs0]; exact hp) hrstZ
      (fun r rk inp init hm => hst r _ _ inp init hm)
    exact ⟨envs, (run0 st) ▸ hrun, hlen, hobs⟩
  -- the core module has a register (a slot)
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
  have hnA : r0.body.all Sparkle.IR.RegDedup.isAssign = false := by
    apply List.all_eq_false.mpr
    exact ⟨_, hb ▸ hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
  rcases hpost with rfl | rfl
  · exact core st0 (fun r c rs inp init hm => hreset r c rs inp init (hb ▸ hm)) hports
  · obtain ⟨hinB, houtB, hwB⟩ := mergeChecked_ports r0
    have hargsB : argPorts (mergeChecked r0) = argPorts r0 := by unfold argPorts; rw [hinB]
    rcases mergeChecked_nonAssign hnA with hchk | heq
    · -- the merge accepted by `refineCheck`
      obtain ⟨hnd, hpair⟩ := refineCheck_regs hchk
      let stM : String → Nat := fun x => match regOf (seqRegs r0) x with
        | some rm => rm.2.2.2.2.toNat
        | none => 0
      have hstM : ∀ r c rs inp init, Stmt.register r c rs inp init ∈ raw.body →
          stM r = init.toNat := by
        intro r c rs inp init hm
        have hmem : (r, c, rs, inp, init) ∈ seqRegs r0 := mem_seqRegs.mp (hb ▸ hm)
        simp only [stM, regOf_mem hnd hmem]
      obtain ⟨envsM, hrunM, hlenM, hobsM⟩ := core stM hstM (by rw [← hargsB]; exact hports)
      have hrstIn0 : "rst" ∈ r0.inputs.map (·.name) := by rw [hi]; exact hrstIn hsl
      -- the inputs beyond the run held at zero
      let ins' : Nat → String → Nat := fun t x => if t < T then ins t x else 0
      have hcong : ∀ (m : Sparkle.IR.AST.Module), ∀ td, td < T → seedIn m ins td = seedIn m ins' td := by
        intro m td htd
        funext st x
        simp [seedIn, ins', htd]
      have hinsFit : ∀ t x, x ∈ r0.inputs.map (·.name) →
          ins' t x < 2 ^ Sparkle.IR.RegDedup.declWidth r0 x := by
        intro t x hx
        by_cases ht : t < T
        · simp only [ins', if_pos ht]
          rw [show Sparkle.IR.RegDedup.declWidth r0 = weOf r0 from rfl, hw]
          exact fitRaw t ht x (by rw [← hi]; exact hx)
        · simp only [ins', if_neg ht]; exact Nat.two_pow_pos _
      have hrstZ' : ∀ t, ins' t "rst" = 0 := by
        intro t; by_cases ht : t < T
        · simp only [ins', if_pos ht]; exact hrstZ t
        · simp only [ins', if_neg ht]
      have hcpl : ∀ r ∈ seqRegs (mergeChecked r0), st0 r.1 = stM r.1 := by
        intro r hr
        obtain ⟨rn, rc, rrs, rinp, rinit⟩ := r
        rw [hreset rn rc rrs rinp rinit (mem_seqRegs.mpr hr)]
        obtain ⟨rm, hrm, hinit⟩ := hpair _ hr
        simp only [stM, hrm, hinit]
      have hfitM : ∀ r ∈ seqRegs r0, stM r.1 < 2 ^ Sparkle.IR.RegDedup.declWidth r0 r.1 := by
        intro r hr
        obtain ⟨rn, rc, rrs, rinp, rinit⟩ := r
        have hm : Stmt.register rn rc rrs rinp rinit ∈ raw.body := hb ▸ mem_seqRegs.mpr hr
        obtain ⟨k, f, hk, hf, hinit⟩ := hevery rn rc rrs rinp rinit hm
        obtain ⟨hwid, _⟩ := hregs k rn f hk hf
        simp only [stM, regOf_mem hnd hr]
        rw [show Sparkle.IR.RegDedup.declWidth r0 = weOf r0 from rfl, hw, hwid, hinit]
        exact hinitFit f (List.mem_of_getElem? hf)
      rw [runModule_seed_congr' _ _ T _ _ (hcong r0)] at hrunM
      obtain ⟨envsO, hrunO, hlenO, hcorr⟩ :=
        refineCheck_transfer hchk ins' hinsFit hrstIn0 hrstZ' hcpl hfitM hrunM
      refine ⟨envsO, ?_, by omega, ?_⟩
      · rw [runModule_seed_congr' _ _ T _ _ (hcong _),
          Tools.ShippingPipelineSoundness.seedIn_of_inputs hinB ins']
        exact hrunO
      · intro j hj k o f hk hf
        have hp : ({ name := o.name, ty := o.ty } : Port) ∈ r0.outputs := by
          rw [ho, houts]; exact List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩
        rw [hcorr _ hp j hj (by omega)]
        exact hobsM j (by omega) k o f hk hf
    · rw [heq]
      exact core st0 (fun r c rs inp init hm => hreset r c rs inp init (by rw [heq]; exact hb ▸ hm))
        (by rw [← hargsB]; exact hports)

end Tools.ShippingMachineChild
