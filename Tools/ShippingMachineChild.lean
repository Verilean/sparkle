import Tools.ShippingMachineCompose
import Tools.ShippingMachineShipping
import Tools.ShippingMachineLoop

/-! # A child's own theorem, as what its instances compute

`machine_linked` (ShippingMachineCompose) composes a machine with its
children under the hypothesis that every call's module computes some
function of its argument ports (`ChildFn`). This file derives that
hypothesis from the child's OWN machine theorem: a combinational child on
the machine route (no slots, no calls) has a trace theorem about its core
module; at one cycle, on an environment whose argument ports hold in-range
values, the module drives its output with the source function applied to
those values, decoded. -/
namespace Tools.ShippingMachineChild
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineCompose
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingEntrySoundness (weOf RunsTo)
open Sparkle.Core
open Tools.ShippingMachineDenote (tys)

/-! ## Ports and binder positions -/

/-- The `q`-th element of a filtered list sits at a position before which
`q` elements pass the filter. -/
theorem filter_getElem_pos {α : Type} (P : α → Bool) :
    ∀ (L : List α) (q : Nat) (b : α), (L.filter P)[q]? = some b →
      ∃ p, L[p]? = some b ∧ ((L.take p).filter P).length = q
  | [], _, _, h => by simp at h
  | x :: rest, q, b, h => by
    by_cases hx : P x = true
    · rw [List.filter_cons_of_pos hx] at h
      cases q with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        exact ⟨0, by simp [h], by simp⟩
      | succ q =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨p, hp, hc⟩ := filter_getElem_pos P rest q b h
        exact ⟨p + 1, by simpa using hp, by simp [List.filter_cons_of_pos hx, hc]⟩
    · rw [List.filter_cons_of_neg hx] at h
      obtain ⟨p, hp, hc⟩ := filter_getElem_pos P rest q b h
      exact ⟨p + 1, by simpa using hp, by simp [List.filter_cons_of_neg hx, hc]⟩

/-- The port index of binder position `p`: the hardware binders before it. -/
def portIdx (bs : List (Name × MixedGateBinder)) (p : Nat) : Nat :=
  ((bs.take p).filter (fun b => b.2 != .domain)).length

/-- The Bool a port value decodes to. -/
def decB (bs : List (Name × MixedGateBinder)) (vals : List Nat) (p : Nat) : Bool :=
  vals.getD (portIdx bs p) 0 != 0

/-- The bit vector a port value decodes to. -/
def decV (bs : List (Name × MixedGateBinder)) (vals : List Nat) (p : Nat) (n : Nat) : BitVec n :=
  BitVec.ofNat n (vals.getD (portIdx bs p) 0)

/-- Port values in range of their binders' types. -/
def InRange : List Nat → List (Name × MixedGateBinder) → Prop :=
  Zip₂ fun v b => match b.2 with
    | .bool => v < 2
    | .bits n => v < 2 ^ n
    | .domain => True

theorem inRange_get {vals : List Nat} {L : List (Name × MixedGateBinder)}
    (hz : InRange vals L) : ∀ (q : Nat) (b : Name × MixedGateBinder), L[q]? = some b →
      match b.2 with
      | .bool => vals.getD q 0 < 2
      | .bits n => vals.getD q 0 < 2 ^ n
      | .domain => True := by
  induction hz with
  | nil => intro q b h; simp at h
  | cons hab _ ih =>
    intro q b h
    cases q with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simpa using hab
    | succ q =>
      simp only [List.getElem?_cons_succ] at h
      simpa using ih q b h

/-- Admissibility from the ports, binders without ports included. -/
theorem admissible_of_portsD {bools bits initial} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      Zip₂ (fun (p : Port) b => initial p.name = binderEnc bools bits b)
        (inputPorts bools bits L a) (L.filter fun b => b.1.2 != .domain) →
      Admissible bools bits initial L a
  | [], _, _ => trivial
  | ((name, .domain), id) :: rest, a, hz => by
    simp only [inputPorts, List.filter_cons] at hz
    exact ⟨trivial, admissible_of_portsD rest _ (by simpa using hz)⟩
  | ((name, .bool), id) :: rest, a, hz => by
    simp only [inputPorts, List.filter_cons] at hz
    cases hz with
    | cons h hs => exact ⟨h, admissible_of_portsD rest _ hs⟩
  | ((name, .bits n), id) :: rest, a, hz => by
    simp only [inputPorts, List.filter_cons] at hz
    cases hz with
    | cons h hs => exact ⟨h, admissible_of_portsD rest _ hs⟩

theorem zip_filter_fst (L : List (Name × MixedGateBinder)) (ids : List FVarId)
    (h : L.length ≤ ids.length) :
    ((L.zip ids).filter (fun b => b.1.2 != .domain)).map Prod.fst =
      L.filter (fun b => b.2 != .domain) := by
  induction L generalizing ids with
  | nil => rfl
  | cons b rest ih =>
    cases ids with
    | nil => simp at h
    | cons id ids =>
      simp only [List.zip_cons_cons, List.filter_cons]
      have := ih ids (by simp at h; omega)
      split <;> simp_all

/-- One cycle of an open run is one elaboration. -/
theorem runModule_one {we : WEnv} {body : List Stmt} {seed : Nat → (String → Nat) → Env}
    {st : String → Nat} {mems : MEnv} {envs : List Env}
    (h : runModule we body seed 1 st mems = some envs) :
    ∃ envF, envs = [envF] ∧ evalAssigns we mems body (seed 0 st) = some envF := by
  have h' : (stepModule we body (seed 0 st) mems).bind (fun r =>
      (runModule we body seed 0 (applyNexts st r.2.1) r.2.2).bind
        (fun rest => some (r.1 :: rest))) = some envs := h
  cases hS : stepModule we body (seed 0 st) mems with
  | none => rw [hS] at h'; cases h'
  | some r =>
    obtain ⟨envF, nexts, mems'⟩ := r
    rw [hS] at h'
    simp only [Option.bind_some, runModule, Option.some.injEq] at h'
    refine ⟨envF, h'.symm, ?_⟩
    unfold stepModule at hS
    cases hE : evalAssigns we mems body (seed 0 st) with
    | none => rw [hE] at hS; cases hS
    | some e =>
      rw [hE] at hS
      simp only [Option.bind_some, bind] at hS
      cases hN : regNexts we mems body e with
      | none => rw [hN] at hS; cases hS
      | some ns =>
        rw [hN] at hS
        cases hM : memNexts we body mems e with
        | none => rw [hM] at hS; simp at hS
        | some ms =>
          rw [hM] at hS
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hS
          rw [hS.1]

/-! ## A combinational child at one cycle -/

/-- The source function of a combinational child on decoded port values:
its first observation, at time 0, on constant inputs. -/
def childValue {ι : Type} {dom : ι → DomainConfig}
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (bs : List (Name × MixedGateBinder)) (i : ι) (vals : List Nat) : Nat :=
  ((src i (fun p => Signal.pure (decB bs vals p)) (fun p n => Signal.pure (decV bs vals p n)))[0]?.map
    (· 0)).getD 0

/-- **A child's own theorem gives what its module computes.** A machine
without slots and without calls, whose trace theorem is `h`, computes at
one cycle, on any environment with reset low and in-range argument values,
its source function on those values (`childValue`). -/
theorem childFn_of_trace {declName : Name} {d : MachineData} {raw : Sparkle.IR.AST.Module}
    {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (h : MachineTraceL declName d raw dsn dom src ext lsrc)
    (hext : ∀ i bools bits, ext i bools bits = bits)
    (hnoI : d.shape.insts = []) (hss : d.ss = []) (hsl : d.shape.layout.slots = [])
    (hlets : d.letBs.length = d.shape.layout.lets)
    (o : Sparkle.IR.Machine.OutField) (hout : d.shape.layout.outs = [o])
    (hsrc : ∀ i bools bits, (src i bools bits).length = 1) (i : ι) :
    ChildFn raw (fun vals => InRange vals (d.bsIn.filter fun b => b.2 != .domain))
      (childValue src d.bsIn i) := by
  obtain ⟨ids, nd, len, cache, regs, _, rlen, lets, _, wired, trace⟩ := h
  obtain ⟨_, _, _, _, _, _, _, houts, hins, _⟩ := wired
  refine ⟨⟨o.name, o.ty⟩, by rw [houts, hout]; rfl, ?_⟩
  intro mems env hrst hP
  -- the argument ports are the declaration's ports
  have hbsIn : d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
      d.shape.layout.lets) = d.bsIn := by
    rw [hsl, ← hlets]
    simp only [MachineData.letBs, MachineData.bsIn, hss, List.length_nil, Nat.add_zero,
      List.length_drop, Nat.sub_zero]
    by_cases hle : d.nIn ≤ d.shape.binders.length
    · rw [show d.shape.binders.length - (d.shape.binders.length - d.nIn) = d.nIn by omega]
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  have hargs : argPorts raw = machPorts declName ids cache d.bsIn := by
    unfold argPorts; rw [hins hnoI, hbsIn]
  let vals := (argPorts raw).map fun p => env p.name
  have hregs : regs = [] := List.length_eq_zero_iff.mp (by rw [rlen, hss]; rfl)
  -- the decoded inputs, as constant Signals
  let bools : Nat → Signal (dom i) Bool := fun p => Signal.pure (decB d.bsIn vals p)
  let bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n) :=
    fun p n => Signal.pure (decV d.bsIn vals p n)
  have hlenIn : d.bsIn.length ≤ ids.length := by
    rw [len]; simp only [MachineData.bsIn, List.length_take]; omega
  have hsi : SourceInputs declName d.bsIn ids cache (fun j => (bools j).val (1 - 1 - 0))
      (fun j n => (ext i bools bits j n).val (1 - 1 - 0)) env := by
    rw [hext]
    unfold SourceInputs
    apply admissible_of_portsD
    rw [show inputPorts (boolValues ids fun j => (bools j).val (1 - 1 - 0))
        (bitValues ids fun j n => (bits j n).val (1 - 1 - 0)) (d.bsIn.zip ids)
        (start (entryCompilerState false cache) declName.toString) =
        machPorts declName ids cache d.bsIn from inputPorts_congr _ _ _ rfl, ← hargs]
    have hlenP : (argPorts raw).length =
        ((d.bsIn.zip ids).filter fun b => b.1.2 != .domain).length := by
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
    have hport : portIdx d.bsIn pos = q := by
      unfold portIdx
      have hpl : pos < d.bsIn.length := (List.getElem?_eq_some_iff.mp hb1).1
      rw [← hcnt, show (d.bsIn.zip ids).take pos = (d.bsIn.take pos).zip (ids.take pos) from
        List.take_zipWith, ← zip_filter_fst (d.bsIn.take pos) (ids.take pos)
        (by simp only [List.length_take]; omega), List.length_map]
    have hval : vals.getD q 0 = env p.name := by
      simp [vals, List.getD_eq_getElem?_getD, hp]
    -- the binder's value is in range
    have hfq : (d.bsIn.filter fun b => b.2 != .domain)[q]? = some (nm, kind) := by
      rw [← zip_filter_fst _ _ hlenIn, List.getElem?_map, hb]; rfl
    have hrange : InRange vals (d.bsIn.filter fun b => b.2 != .domain) := hP
    have hqlt : q < vals.length := by
      have := (List.getElem?_eq_some_iff.mp hp).1; simpa [vals] using this
    have hr := inRange_get hrange q (nm, kind) hfq
    rw [hval] at hr
    simp only [binderEnc]
    cases kind with
    | domain =>
      have := (List.mem_filter.mp (List.mem_of_getElem? hb)).2
      simp at this
    | bool =>
      simp only [boolValues, hidx, bools, decB, hport, Signal.pure, hval]
      simp only [Tools.ShippingMuxLoweringSoundness.encodeBool]
      simp only at hr
      split <;> simp_all <;> omega
    | bits n =>
      simp only [bitValues, hidx, bits, decV, hport, Signal.pure, hval]
      simp only at hr
      simp [Nat.mod_eq_of_lt hr]
  obtain ⟨envs, hrun, hlenE, hobs, _⟩ := trace i bools bits 1 (fun _ _ => env) (fun _ => 0) mems
    (fun t st ht => by
      have : t = 0 := by omega
      subst this; exact hsi)
    (by intro t st r hr; rw [hregs] at hr; cases hr)
    (fun _ _ => hrst)
    (by intro k r f hr; rw [hregs] at hr; simp at hr)
  obtain ⟨envF, rfl, hev⟩ := runModule_one hrun
  refine ⟨envF, hev, ?_⟩
  have hs1 := hsrc i bools bits
  obtain ⟨f, hf⟩ : ∃ f, (src i bools bits)[0]? = some f :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have := hobs 0 (by simp) 0 o f (by rw [hout]; rfl) hf
  simp only [List.getElem_cons_zero] at this
  rw [this]
  simp [childValue, bools, bits, vals, hf]

/-! ## The child module the full entry returns -/

/-- The duplicate merge keeps what a module of assignments computes. -/
theorem childFn_merge {raw : Sparkle.IR.AST.Module} {P : List Nat → Prop} {F : List Nat → Nat}
    (h : ChildFn raw P F) (hall : raw.body.all Sparkle.IR.RegDedup.isAssign = true) :
    ChildFn (Sparkle.IR.RegDedup.mergeDuplicates raw) P F := by
  obtain ⟨outP, houts, hf⟩ := h
  have hports := Tools.ShippingPostSoundness.mergeDuplicates_sound raw (fun _ _ => 0)
    (fun _ => 0) (fun _ => 0) hall
  refine ⟨outP, ?_, ?_⟩
  · unfold Sparkle.IR.RegDedup.mergeDuplicates
    simp only [hall, if_true]
    split <;> exact houts
  · intro mems env hrst hP
    have hin : (Sparkle.IR.RegDedup.mergeDuplicates raw).inputs = raw.inputs := by
      unfold Sparkle.IR.RegDedup.mergeDuplicates
      simp only [hall, if_true]
      split <;> rfl
    have hargs : argPorts (Sparkle.IR.RegDedup.mergeDuplicates raw) = argPorts raw := by
      unfold argPorts; rw [hin]
    rw [hargs] at hP ⊢
    obtain ⟨cres, hev, hcres⟩ := hf mems env hrst hP
    obtain ⟨hev', _⟩ := Tools.ShippingPostSoundness.mergeDuplicates_sound raw mems env cres
      hall hev
    exact ⟨cres, hev', hcres⟩

/-- **The child module in the design computes the child's function.** The
full entry returns the zero-width cleanup of the core module, merged or
not (`synthesizeCombinational_checked`); when the cleanup changes nothing
(a decidable fact about the run's module), the module computes what the
core module computes. -/
theorem childFn_full {raw b : Sparkle.IR.AST.Module} {P : List Nat → Prop}
    {F : List Nat → Nat} (h : ChildFn raw P F)
    (hall : raw.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdz : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = raw) :
    ChildFn b P F := by
  rw [hdz] at hpost
  rcases hpost with rfl | rfl
  · exact h
  · rcases Sparkle.IR.RefineCheck.mergeChecked_cases raw with he | he <;> rw [he]
    · exact childFn_merge h hall
    · exact h

/-! ## The child's endpoint, with its wiring -/

/-- `machine_trace_of_comb` with the wiring: the same premises, the
`MachineTraceL` conclusion (no `let` observations). -/
theorem machine_traceL_of_comb {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j))
      d.packed)
    (hinit : d.initOk inits = true)
    (hnext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      inits = Tools.ShippingMachineDenote.evalTerms
        (fun j => (Tools.ShippingMachineDenote.typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t
          inits).b (d.bpos j))
        (fun j w => (Tools.ShippingMachineDenote.typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t
          inits).v (d.vpos j) w)
        d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat),
      (src i bools bits).map (fun g => g t) =
        d.outs.map fun o => Tools.ShippingMachineDenote.enc o.1 (Tools.ShippingUnifiedSource.eval
          (fun k => (Tools.ShippingMachineDenote.typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t
            inits).b (d.bpos k))
          (fun k w => (Tools.ShippingMachineDenote.typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t
            inits).v (d.vpos k) w)
          o.2))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []) :=
  machine_trace_lets_of_stream d dom inits src (fun _ _ _ => []) ok hbody hinit
    (fun _ _ bits => bits)
    (fun i bools bits => ⟨fun _ => inits, rfl, fun t => hnext i bools bits t, hres i bools bits,
      fun _ _ _ _ h => by simp at h⟩) hr entry closes

/-- **A combinational child at the full entry.** From the child's wired
endpoint (`sound`, e.g. `machine_traceL_of_comb` with its kernel checks), a
run of the full entry on the child returns a module that — when the run's
zero-width cleanup changes nothing — computes the child's source function
on its argument ports (`ChildFn`, as `machine_linked` uses it). -/
theorem child_full {declName : Name} {d : MachineData} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (sound : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) (fun _ _ _ => []))
    (hnoI : d.shape.insts = []) (hss : d.ss = []) (hsl : d.shape.layout.slots = [])
    (hlets : d.letBs.length = d.shape.layout.lets)
    (hout : d.shape.layout.outs.length = 1)
    (hsrc : ∀ i bools bits, (src i bools bits).length = 1) (i0 : ι)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = raw →
        ChildFn b (fun vals => InRange vals (d.bsIn.filter fun b => b.2 != .domain))
          (childValue src d.bsIn i0)) := by
  obtain ⟨M, D, w1, hcore, hpost⟩ :=
    Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  have h := sound hcore entry closes
  have hall : M.body.all Sparkle.IR.RegDedup.isAssign = true := by
    obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, _, hall⟩ := wired
    exact hall hnoI hsl
  obtain ⟨o, ho⟩ : ∃ o, d.shape.layout.outs = [o] := by
    match hm : d.shape.layout.outs, hout with
    | [o], _ => exact ⟨o, rfl⟩
  exact ⟨M, hpost, fun hdz => childFn_full
    (childFn_of_trace h (fun _ _ _ => rfl) hnoI hss hsl hlets o ho hsrc i0) hall hpost hdz⟩

/-! ## Assembling a call's equations -/

/-- The argument values a child accepts: in range of its ports' types. -/
def childRange (d : MachineData) (vals : List Nat) : Prop :=
  InRange vals (d.bsIn.filter fun b => b.2 != .domain)

/-- A statement about every entry of a list, entry by entry. -/
theorem forall_getElem?_cons {α : Type} {Q : Nat → α → Prop} {a : α} {l : List α}
    (h0 : Q 0 a) (hs : ∀ k b, l[k]? = some b → Q (k + 1) b) :
    ∀ k b, (a :: l)[k]? = some b → Q k b
  | 0, b, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; exact h ▸ h0
  | k + 1, b, h => hs k b (by simpa using h)

theorem forall_getElem?_nil {α : Type} {Q : Nat → α → Prop} :
    ∀ k b, ([] : List α)[k]? = some b → Q k b := by
  intro k b h; simp at h

theorem encodeBool_lt (b : Bool) : Tools.ShippingMuxLoweringSoundness.encodeBool b < 2 := by
  cases b <;> decide

theorem encodeBool_ne (b : Bool) : (Tools.ShippingMuxLoweringSoundness.encodeBool b != 0) = b := by
  cases b <;> rfl

/-- A call's premise of `machine_linked_calls` from its parts: the argument
values are `obs`, which the child's range predicate accepts and its
function maps to `rhs`. -/
theorem call_of_facts {argsN : List Nat} {lsrcL : List (Nat → Nat)} {lsLen : Nat} {j : Nat}
    {P : List Nat → Prop} {F : List Nat → Nat} (obs : List Nat) {rhs : Nat}
    (hlen : lsrcL.length = lsLen) (hbd : ∀ q ∈ argsN, q < lsLen)
    (hv : argsN.map (fun q => (lsrcL[q]?.map (fun g => g j)).getD 0) = obs)
    (hP : P obs) (hF : F obs = rhs) :
    (∀ q ∈ argsN, q < lsLen ∧ q < lsrcL.length) ∧
      P (argsN.map fun q => (lsrcL[q]?.map (fun g => g j)).getD 0) ∧
      F (argsN.map fun q => (lsrcL[q]?.map (fun g => g j)).getD 0) = rhs := by
  refine ⟨fun q hq => ⟨hbd q hq, hlen ▸ hbd q hq⟩, ?_, ?_⟩
  · rw [hv]; exact hP
  · rw [hv]; exact hF

end Tools.ShippingMachineChild
