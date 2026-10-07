import Tools.ShippingMachineAuto
import Tools.ShippingMachineFuse
import Tools.ShippingMachineChild

/-! # A `circuit do` calling SEQUENTIAL hardware modules

`machine_trace_of_data_ext` (ShippingMachineAuto) asks the calls' values to
be POINTWISE in the state: right for a combinational child, false for a
child with registers of its own (an ECDSA engine's `done` depends on what
it was given cycles ago). What the state recurrence actually needs is that
the calls are CAUSAL — their value at a cycle fixed by the state up to that
cycle — because the loop's step at `t + 1` sees the live state truncated
after `t` (`circuit_state_causal`, ShippingMachineFuse). With causal calls
the source's own state loop is a stream whose step is the next-value terms
with the calls' values on that loop at the cycle; that is the recurrence
`machine_trace_of_streamB` turns into the trace theorem of the module.

Both input families are extended (`ext` for `BitVec` call outputs, `extB`
for `Bool` ones). -/
namespace Tools.ShippingMachineCausal
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness

/-- The typed valuation reads both input families at `t` only. -/
theorem typedVal_congrB {D : DomainConfig} (kIn : Nat) (bpos vpos : Nat → Nat) (ss : List SType)
    (ls : List (Σ s : SType, Term s)) (bools bools' : Nat → Signal D Bool)
    (bits bits' : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys ss))
    (hb : ∀ p, (bools p).val t = (bools' p).val t)
    (hv : ∀ p w, (bits p w).val t = (bits' p w).val t) :
    typedVal kIn bpos vpos ss ls bools bits t x = typedVal kIn bpos vpos ss ls bools' bits' t x := by
  unfold typedVal
  have e1 : (fun p => (bools p).val t) = fun p => (bools' p).val t := by
    funext p; exact hb p
  have e2 : (fun p w => (bits p w).val t) = fun p w => (bits' p w).val t := by
    funext p w; exact hv p w
  rw [e1, e2]

set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a `circuit do` with causal calls, from data.** As
`machine_trace_of_data_ext`, with the calls' values (`ext`, `extB`, over
the state signal) CAUSAL in the state instead of pointwise: equal at `t` on
state signals that agree up to `t`. -/
theorem machine_trace_of_data_causal {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst)
    (hcausal : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S S' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (∀ c, c ≤ t → S.val c = S'.val c) →
      (∀ p w, (ext i bools bits S p w).val t = (ext i bools bits S' p w).val t) ∧
      (∀ p, (extB i bools bits S p).val t = (extB i bools bits S' p).val t))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceWithB declName d m dom src
      (fun i bools bits => ext i bools bits (stateLoop inits (body i bools bits)))
      (fun i bools bits => extB i bools bits (stateLoop inits (body i bools bits))) := by
  refine machine_trace_of_streamB d dom inits src ok hbody hinit _ _ ?_ hr entry closes
  intro i bools bits
  -- the writes are causal in the state: the calls are, the rest is pointwise
  have hW : ∀ (l l' : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (∀ c, c ≤ t → l.val c = l'.val c) →
      valsAt (tys d.ss) (writesOn (body i bools bits) l) t =
        valsAt (tys d.ss) (writesOn (body i bools bits) l') t := by
    intro l l' t h
    show valsAt (tys d.ss) (body i bools bits (mkRegList l (tys d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys d.ss) l)).snd t =
      valsAt (tys d.ss) (body i bools bits (mkRegList l' (tys d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys d.ss) l')).snd t
    obtain ⟨hv, hb⟩ := hcausal i bools bits l l' t h
    rw [writes i bools bits l t, writes i bools bits l' t, h t (Nat.le_refl t),
      typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l) (extB i bools bits l')
        (ext i bools bits l) (ext i bools bits l') t (l'.val t) hb hv]
  obtain ⟨h0, hs⟩ := circuit_state_causal inits (body i bools bits) hW
  refine ⟨fun t => (stateLoop inits (body i bools bits)).val t, h0, ?_, ?_⟩
  · intro t
    show (stateLoop inits (body i bools bits)).val (t + 1) = _
    rw [hs t]
    exact writes i bools bits _ t
  · intro j
    rw [hsrc i bools bits]
    exact hres i bools bits (stateLoop inits (body i bools bits)) j

/-- `machine_trace_of_data` with the wiring and the `let` wires (its twin
`machine_traceL_of_data_ext` with the inputs as they are), for a child whose
causality `src_causal_of_trace` derives. Same arguments. -/
theorem machine_traceL_of_data {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).v
            (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src
      (fun i bools bits => (fun _ _ bits _ => bits : (i : ι) → (Nat → Signal (dom i) Bool) →
        ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
        Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        i bools bits (stateLoop inits (body i bools bits)))
      (letObs d dom inits body (fun _ _ bits _ => bits)) :=
  machine_traceL_of_data_ext d dom inits body obsR (fun _ _ bits _ => bits) src ok hbody
    hinit writes hres hsrc (fun _ _ _ _ _ _ _ => rfl) hr entry closes

/-! ## A machine's source is causal in its inputs

From its trace theorem: on inputs that agree up to `t`, one seed serves both
runs (the seed of cycle `τ < t + 1` holds the inputs of cycle `t - τ`), so
the two runs are the same run, and the observations at `t` agree. -/

section Causal
open Tools.ShippingMachineCompose Tools.ShippingMachineChild
open Tools.ShippingMachineClose (Zip₂)

/-- The encoded input values of the hardware binders at cycle `c`. -/
def portVals {D : DomainConfig} (ids : List FVarId) (bs : List (Name × MixedGateBinder))
    (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (c : Nat) : List Nat :=
  ((bs.zip ids).filter fun b => b.1.2 != .domain).map
    (binderEnc (boolValues ids fun j => (bools j).val c) (bitValues ids fun j n => (bits j n).val c))

theorem lookup_zip_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (ks : List α) (vs : List Nat) (q : Nat) (hq : q < ks.length), ks.Nodup → q < vs.length →
      (ks.zip vs).lookup ks[q] = vs[q]?
  | [], _, _, hq, _, _ => by simp at hq
  | _ :: _, [], _, _, _, hv => by simp at hv
  | k :: ks, v :: vs, 0, _, _, _ => by simp [List.lookup]
  | k :: ks, v :: vs, q + 1, hq, nd, hv => by
    obtain ⟨hk, nd⟩ := List.nodup_cons.mp nd
    have hne : (ks[q]'(by simp at hq; omega) == k) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact hk (h ▸ List.getElem_mem _)
    simp only [List.zip_cons_cons, List.lookup, List.getElem_cons_succ, hne,
      List.getElem?_cons_succ]
    exact lookup_zip_nodup ks vs q (by simp at hq; omega) nd (by simp at hv; omega)

theorem lookup_zip_not_mem {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (ks : List α) (vs : List Nat) (x : α), x ∉ ks → (ks.zip vs).lookup x = none
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, v :: vs, x, hx => by
    have hne : (x == k) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact hx (h ▸ List.mem_cons_self)
    simp only [List.zip_cons_cons, List.lookup, hne]
    exact lookup_zip_not_mem ks vs x (fun h => hx (List.mem_cons_of_mem _ h))

/-- **A machine's source is causal in its inputs.** -/
theorem src_causal_of_trace {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module}
    {dsn : Sparkle.IR.AST.Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (h : MachineTraceLB declName d m dsn dom src ext extB lsrc) (ok : d.ok = true)
    (hext : ∀ i bools bits, ext i bools bits = bits)
    (hextB : ∀ i bools bits, extB i bools bits = bools)
    (i : ι) (bools bools' : Nat → Signal (dom i) Bool)
    (bits bits' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat)
    (hb : ∀ p c, c ≤ t → (bools p).val c = (bools' p).val c)
    (hv : ∀ p n c, c ≤ t → (bits p n).val c = (bits' p n).val c)
    (k : Nat) (hk : k < d.shape.layout.outs.length)
    (f f' : Nat → Nat) (hf : (src i bools bits)[k]? = some f)
    (hf' : (src i bools' bits')[k]? = some f') : f t = f' t := by
  have ho : d.shape.layout.outs[k]? = some (d.shape.layout.outs[k]'hk) := List.getElem?_eq_getElem hk
  generalize d.shape.layout.outs[k]'hk = o at ho
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨hlen, hlets, _, slotsND, letsND, layB, -⟩ := ok
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, _, wired, trace⟩ := h
  obtain ⟨namesNd, alloc, hregs, -⟩ := wired
  -- the binders' ports: the inputs' first, then one per slot and `let`
  have hsplit : d.shape.binders = d.bsIn ++ (d.slotBs ++ d.letBs) := by
    rw [d.binders_split, List.append_assoc]
  have hlenB : d.bsIn.length + (d.slotBs ++ d.letBs).length ≤ ids.length := by
    have := congrArg List.length hsplit
    simp only [List.length_append] at this ⊢
    omega
  obtain ⟨R, hR⟩ := machPorts_append (declName := declName) (cache := cache) d.bsIn
    (d.slotBs ++ d.letBs) hlenB
  have hRlen : R.length = d.ss.length + d.shape.layout.lets := by
    have h1 := machPorts_length (declName := declName) (cache := cache) (d.bsIn ++ (d.slotBs ++ d.letBs))
      (by rw [List.length_append]; exact hlenB)
    rw [hR, List.length_append, List.filter_append, List.length_append] at h1
    have h2 : (machPorts declName ids cache d.bsIn).length =
        (d.bsIn.filter fun b => b.2 != .domain).length :=
      machPorts_length _ (by omega)
    have h3 : ((d.slotBs ++ d.letBs).filter fun b => b.2 != .domain) = d.slotBs ++ d.letBs := by
      rw [List.filter_eq_self]
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · simpa using slotsND b hb
      · simpa using letsND b hb
    have h4 : d.slotBs.length = d.ss.length := by
      simp only [MachineData.slotBs, List.length_take, List.length_drop]; omega
    rw [h3, List.length_append, h4] at h1
    have h5 : d.letBs.length = d.shape.layout.lets := hlets.symm
    omega
  -- the input ports' names, and the registers' (among the slot and `let` ports)
  have hnames : (machPorts declName ids cache d.shape.binders).map (·.name) =
      (machPorts declName ids cache d.bsIn).map (·.name) ++ R.map (·.name) := by
    rw [hsplit, hR, List.map_append]
  have namesNd' : ((machPorts declName ids cache d.bsIn).map (·.name) ++ R.map (·.name)).Nodup :=
    hnames ▸ namesNd
  have hPnd := (List.nodup_append.mp namesNd').1
  have hslotsLen : d.shape.layout.slots.length = d.ss.length := by
    have hz := (zip_of_all (R := fun (f : SlotField) (b : Name × MixedGateBinder) =>
      (decide (f.width = machWidth b.2) && (decide (b.2 ≠ .domain) &&
        decide (f.init < 2 ^ f.width))) = true) (fun _ _ h => h) layB).length_eq
    rw [hz]; simp only [MachineData.slotBs, List.length_take, List.length_drop]; omega
  have hregR : ∀ r ∈ regs, r ∈ R.map (·.name) := by
    intro r hr
    have h1 := hregs r hr
    rw [hnames] at h1
    have e : ((machPorts declName ids cache d.bsIn).map (·.name) ++ R.map (·.name)).length -
        d.shape.layout.lets - d.shape.layout.slots.length =
        ((machPorts declName ids cache d.bsIn).map (·.name)).length := by
      simp only [List.length_append, List.length_map]; rw [hRlen, hslotsLen]; omega
    rw [e, List.drop_left] at h1
    exact h1
  have hregP : ∀ r ∈ regs, r ∉ (machPorts declName ids cache d.bsIn).map (·.name) := by
    intro r hr hp
    exact (List.nodup_append.mp namesNd').2.2 r hp r (hregR r hr) rfl
  have hall : ∀ x ∈ (machPorts declName ids cache d.shape.binders).map (·.name), x ≠ "rst" := by
    intro x hx hx'
    exact Tools.ShippingRegisterSoundness.not_allocated_rst (hx' ▸ alloc x hx)
  have hPrst : ∀ x ∈ (machPorts declName ids cache d.bsIn).map (·.name), x ≠ "rst" :=
    fun x hx => hall x (hnames ▸ List.mem_append_left _ hx)
  have hRrst : ∀ r ∈ regs, r ≠ "rst" :=
    fun r hr => hall r (hnames ▸ List.mem_append_right _ (hregR r hr))
  -- one seed for both runs: the ports hold the inputs of cycle `t - τ`
  let Pn := (machPorts declName ids cache d.bsIn).map (·.name)
  let seed : Nat → (String → Nat) → Env := fun τ st x =>
    if x = "rst" then 0 else ((Pn.zip (portVals ids d.bsIn bools bits (t + 1 - 1 - τ))).lookup x).getD (st x)
  have hlenIn : d.bsIn.length ≤ ids.length := by omega
  have hPlen : (machPorts declName ids cache d.bsIn).length =
      ((d.bsIn.zip ids).filter fun b => b.1.2 != .domain).length := by
    rw [machPorts_length _ hlenIn, ← zip_filter_fst _ _ hlenIn, List.length_map]
  -- the seed is admissible for any inputs with the same values up to `t`
  have hsi : ∀ (B : Nat → Signal (dom i) Bool) (V : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (∀ c, c ≤ t → portVals ids d.bsIn B V c = portVals ids d.bsIn bools bits c) →
      ∀ τ st, τ < t + 1 → SourceInputs declName d.bsIn ids cache
        (fun j => (B j).val (t + 1 - 1 - τ)) (fun j n => (V j n).val (t + 1 - 1 - τ)) (seed τ st) := by
    intro B V hBV τ st _
    unfold SourceInputs
    apply admissible_of_portsD
    rw [show inputPorts (boolValues ids fun j => (B j).val (t + 1 - 1 - τ))
        (bitValues ids fun j n => (V j n).val (t + 1 - 1 - τ)) (d.bsIn.zip ids)
        (start (entryCompilerState false cache) declName.toString) =
        machPorts declName ids cache d.bsIn from inputPorts_congr _ _ _ rfl]
    apply Zip₂.of_get hPlen
    intro q p b hp hb
    have hq : q < (machPorts declName ids cache d.bsIn).length := (List.getElem?_eq_some_iff.mp hp).1
    have hpn : Pn[q]'(by simp [Pn, hq]) = p.name := by
      simp only [Pn, List.getElem_map]; rw [(List.getElem?_eq_some_iff.mp hp).2]
    have hvlen : q < (portVals ids d.bsIn bools bits (t + 1 - 1 - τ)).length := by
      simp only [portVals, List.length_map]; rw [← hPlen]; exact hq
    show (if p.name = "rst" then 0 else _) = _
    rw [if_neg (hPrst _ (List.mem_map.mpr ⟨p, List.mem_of_getElem? hp, rfl⟩)), ← hpn,
      lookup_zip_nodup Pn _ q (by simp [Pn, hq]) hPnd hvlen,
      ← hBV (t + 1 - 1 - τ) (by omega)]
    simp only [portVals, List.getElem?_map, hb, Option.map_some, Option.getD_some]
  -- the reset values
  let st0 : String → Nat := fun x =>
    ((regs.zip (d.shape.layout.slots.map (·.init))).lookup x).getD 0
  have hinit : ∀ (k : Nat) (r : String) (fl : SlotField), regs[k]? = some r →
      d.shape.layout.slots[k]? = some fl → st0 r = fl.init := by
    intro k r fl hr hfl
    have hk : k < regs.length := (List.getElem?_eq_some_iff.mp hr).1
    have hk2 : k < (d.shape.layout.slots.map (·.init)).length := by
      simp only [List.length_map]; exact (List.getElem?_eq_some_iff.mp hfl).1
    have hrk : regs[k] = r := (List.getElem?_eq_some_iff.mp hr).2
    show ((regs.zip _).lookup r).getD 0 = _
    rw [← hrk, lookup_zip_nodup regs _ k hk rnd hk2]
    simp [List.getElem?_map, hfl]
  have hpass : ∀ τ st r, r ∈ regs → seed τ st r = st r := by
    intro τ st r hr
    show (if r = "rst" then 0 else _) = _
    rw [if_neg (hRrst r hr)]
    have : (Pn.zip (portVals ids d.bsIn bools bits (t + 1 - 1 - τ))).lookup r = none :=
      lookup_zip_not_mem Pn _ r (hregP r hr)
    rw [this]; rfl
  have hrst : ∀ τ st, seed τ st "rst" = 0 := fun _ _ => if_pos rfl
  let mems : MEnv := fun _ _ => 0
  -- the two runs are one run
  obtain ⟨envs, hrun, hlenE, hobs, -⟩ := trace i bools bits (t + 1) seed st0 mems
    (by rw [hext, hextB]; exact hsi bools bits (fun _ _ => rfl)) hpass hrst hinit
  obtain ⟨envs', hrun', _, hobs', -⟩ := trace i bools' bits' (t + 1) seed st0 mems
    (by
      rw [hext, hextB]
      refine hsi bools' bits' ?_
      intro c hc
      unfold portVals
      congr 1
      funext b
      have e1 : (boolValues ids fun j => (bools' j).val c) = boolValues ids fun j => (bools j).val c := by
        funext id; exact (hb _ c hc).symm
      have e2 : (bitValues ids fun j n => (bits' j n).val c) = bitValues ids fun j n => (bits j n).val c := by
        funext id n; exact (hv _ n c hc).symm
      rw [e1, e2]) hpass hrst hinit
  rw [hrun] at hrun'
  cases hrun'
  have ht : t < envs.length := by omega
  rw [← hobs t ht k o f ho hf, hobs' t ht k o f' ho hf']

end Causal

/-- **A `circuit do`'s source is causal in its inputs, from its endpoint's
facts** (the arguments of `machine_trace_of_data`, no run): its state loop
steps by the next-value terms on the inputs of the cycle, so on inputs that
agree up to `t` the loops agree up to `t`, and so do the observations at
`t`. -/
theorem src_causal_of_data {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).v
            (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t (S.val t)).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst)
    (i : ι) (B B' : Nat → Signal (dom i) Bool)
    (V V' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat)
    (hb : ∀ p c, c ≤ t → (B p).val c = (B' p).val c)
    (hv : ∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) :
    ∀ (k : Nat) (f f' : Nat → Nat), (src i B V)[k]? = some f → (src i B' V')[k]? = some f' →
      f t = f' t := by
  -- each state loop steps by the next-value terms on its inputs of the cycle
  have step : ∀ (Bx : Nat → Signal (dom i) Bool)
      (Vx : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (stateLoop inits (body i Bx Vx)).val 0 = inits ∧
      ∀ c, (stateLoop inits (body i Bx Vx)).val (c + 1) = evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls Bx Vx c
          ((stateLoop inits (body i Bx Vx)).val c)).b (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls Bx Vx c
          ((stateLoop inits (body i Bx Vx)).val c)).v (d.vpos j) w) d.nexts := by
    intro Bx Vx
    obtain ⟨h0, hs⟩ := circuit_state inits (body i Bx Vx) (by
      intro l l' c h
      rw [writes i Bx Vx l c, writes i Bx Vx l' c, h])
    exact ⟨h0, fun c => (hs c).trans (writes i Bx Vx _ c)⟩
  -- the two loops agree up to `t`
  have hstate : ∀ c, c ≤ t →
      (stateLoop inits (body i B V)).val c = (stateLoop inits (body i B' V')).val c := by
    intro c
    induction c with
    | zero => intro _; rw [(step B V).1, (step B' V').1]
    | succ c ih =>
      intro hc
      rw [(step B V).2 c, (step B' V').2 c, ih (by omega),
        typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls B B' V V' c _
          (fun p => hb p c (by omega)) (fun p n => hv p n c (by omega))]
  -- the observations at `t`
  intro k f f' hf hf'
  rw [hsrc i B V] at hf
  rw [hsrc i B' V'] at hf'
  have e1 := congrArg (fun l => l[k]?) (hres i B V (stateLoop inits (body i B V)) t)
  have e2 := congrArg (fun l => l[k]?) (hres i B' V' (stateLoop inits (body i B' V')) t)
  simp only [List.getElem?_map, hf, hf', Option.map_some] at e1 e2
  rw [hstate t (Nat.le_refl t),
    typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls B B' V V' t _
      (fun p => hb p t (Nat.le_refl t)) (fun p n => hv p n t (Nat.le_refl t))] at e1
  exact Option.some.inj (e1.trans e2.symm)

/-- `src_causal_of_data` for a `circuit do` WITH combinational calls (the
arguments of `machine_trace_of_data_ext`): the calls' extension `ext` is
pointwise in the inputs and the state (`hpt`, a `rfl` for a declaration), so
it agrees whenever they agree at the cycle. -/
theorem src_causal_of_data_ext {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (_ok : d.ok = true)
    (_hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (_hinit : d.initOk inits = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S) t
            (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S) t
            (S.val t)).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S) t
            (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S) t
            (S.val t)).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst)
    (_hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t p w : Nat),
      (ext i bools bits S p w).val t = (ext i bools bits ⟨fun _ => S.val t⟩ p w).val t)
    (hpt : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t p w : Nat),
      (ext i bools bits S p w).val t =
        (ext i (fun q => ⟨fun _ => (bools q).val t⟩) (fun q n => ⟨fun _ => (bits q n).val t⟩)
          ⟨fun _ => S.val t⟩ p w).val t)
    (i : ι) (B B' : Nat → Signal (dom i) Bool)
    (V V' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (t : Nat)
    (hb : ∀ p c, c ≤ t → (B p).val c = (B' p).val c)
    (hv : ∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) :
    ∀ (k : Nat) (f f' : Nat → Nat), (src i B V)[k]? = some f → (src i B' V')[k]? = some f' →
      f t = f' t := by
  -- the extension agrees where its inputs and state agree at the cycle
  have agree : ∀ (Bx Bx' : Nat → Signal (dom i) Bool)
      (Vx Vx' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S S' : Signal (dom i) (HList (tys d.ss))) (c : Nat),
      (∀ p, (Bx p).val c = (Bx' p).val c) → (∀ p n, (Vx p n).val c = (Vx' p n).val c) →
      S.val c = S'.val c → ∀ p w, (ext i Bx Vx S p w).val c = (ext i Bx' Vx' S' p w).val c := by
    intro Bx Bx' Vx Vx' S S' c hB hV hS p w
    rw [hpt i Bx Vx S c p w, hpt i Bx' Vx' S' c p w]
    have eB : (fun q => (⟨fun _ => (Bx q).val c⟩ : Signal (dom i) Bool)) =
        fun q => ⟨fun _ => (Bx' q).val c⟩ := by
      funext q; rw [hB q]
    have eV : (fun q n => (⟨fun _ => (Vx q n).val c⟩ : Signal (dom i) (BitVec n))) =
        fun q n => ⟨fun _ => (Vx' q n).val c⟩ := by
      funext q n; rw [hV q n]
    rw [eB, eV, hS]
  -- each state loop steps by the next-value terms on its inputs of the cycle
  have step : ∀ (Bx : Nat → Signal (dom i) Bool)
      (Vx : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (stateLoop inits (body i Bx Vx)).val 0 = inits ∧
      ∀ c, (stateLoop inits (body i Bx Vx)).val (c + 1) = evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls Bx
          (ext i Bx Vx (stateLoop inits (body i Bx Vx))) c
          ((stateLoop inits (body i Bx Vx)).val c)).b (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls Bx
          (ext i Bx Vx (stateLoop inits (body i Bx Vx))) c
          ((stateLoop inits (body i Bx Vx)).val c)).v (d.vpos j) w) d.nexts := by
    intro Bx Vx
    obtain ⟨h0, hs⟩ := circuit_state inits (body i Bx Vx) (by
      intro l l' c h
      rw [writes i Bx Vx l c, writes i Bx Vx l' c, h,
        typedVal_congr d.nIn d.bpos d.vpos d.ss d.ls Bx (ext i Bx Vx l) (ext i Bx Vx l') c _
          (agree Bx Bx Vx Vx l l' c (fun _ => rfl) (fun _ _ => rfl) h)])
    exact ⟨h0, fun c => (hs c).trans (writes i Bx Vx _ c)⟩
  -- the two loops agree up to `t`
  have hstate : ∀ c, c ≤ t →
      (stateLoop inits (body i B V)).val c = (stateLoop inits (body i B' V')).val c := by
    intro c
    induction c with
    | zero => intro _; rw [(step B V).1, (step B' V').1]
    | succ c ih =>
      intro hc
      have hS := ih (by omega)
      rw [(step B V).2 c, (step B' V').2 c, hS,
        typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls B B' _ _ c _
          (fun p => hb p c (by omega))
          (agree B B' V V' _ _ c (fun p => hb p c (by omega)) (fun p n => hv p n c (by omega)) hS)]
  -- the observations at `t`
  intro k f f' hf hf'
  rw [hsrc i B V] at hf
  rw [hsrc i B' V'] at hf'
  have e1 := congrArg (fun l => l[k]?) (hres i B V (stateLoop inits (body i B V)) t)
  have e2 := congrArg (fun l => l[k]?) (hres i B' V' (stateLoop inits (body i B' V')) t)
  simp only [List.getElem?_map, hf, hf', Option.map_some] at e1 e2
  have hS := hstate t (Nat.le_refl t)
  rw [hS, typedVal_congrB d.nIn d.bpos d.vpos d.ss d.ls B B' _ _ t _
      (fun p => hb p t (Nat.le_refl t))
      (agree B B' V V' _ _ t (fun p => hb p t (Nat.le_refl t)) (fun p n => hv p n t (Nat.le_refl t)) hS)]
    at e1
  exact Option.some.inj (e1.trans e2.symm)

/-! ## The calls' values, causal in the state -/

/-- The Bool inputs with `sig` at position `pos`. -/
def extendBools {D : DomainConfig} (bools : Nat → Signal D Bool) (pos : Nat)
    (sig : Signal D Bool) : Nat → Signal D Bool :=
  fun j => if j = pos then sig else bools j

theorem extendBools_val {D : DomainConfig} {bools bools' : Nat → Signal D Bool} {pos : Nat}
    {sig sig' : Signal D Bool} {t : Nat}
    (hb : ∀ j, (bools j).val t = (bools' j).val t) (hsig : sig.val t = sig'.val t) :
    ∀ j, (extendBools bools pos sig j).val t = (extendBools bools' pos sig' j).val t := by
  intro j
  unfold extendBools
  by_cases h : j = pos
  · rw [if_pos h, if_pos h]; exact hsig
  · rw [if_neg h, if_neg h]; exact hb j

/-- A child's source, causal in its inputs (`src_causal_of_trace`), read on
input families that are causal functions of a state signal: the field it
observes at `k` is causal in the state. -/
theorem field_causal {D : DomainConfig} {σ : Type}
    (srcF : (Nat → Signal D Bool) → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) → List (Nat → Nat))
    (hsrc : ∀ (B B' : Nat → Signal D Bool) (V V' : (j : Nat) → (n : Nat) → Signal D (BitVec n))
      (t : Nat), (∀ p c, c ≤ t → (B p).val c = (B' p).val c) →
      (∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) →
      ∀ (k : Nat) (f f' : Nat → Nat), (srcF B V)[k]? = some f → (srcF B' V')[k]? = some f' →
        f t = f' t)
    (famB : Signal D σ → Nat → Signal D Bool)
    (famV : Signal D σ → (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (hfB : ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      ∀ p c, c ≤ t → (famB S p).val c = (famB S' p).val c)
    (hfV : ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      ∀ p n c, c ≤ t → (famV S p n).val c = (famV S' p n).val c)
    (k : Nat) {w : Nat} (field : Signal D σ → Signal D (BitVec w))
    (hobs : ∀ S, (srcF (famB S) (famV S))[k]? = some (fun t => ((field S).val t).toNat)) :
    ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      (field S).val t = (field S').val t := by
  intro S S' t h
  have := hsrc (famB S) (famB S') (famV S) (famV S') t (hfB S S' t h) (hfV S S' t h) k _ _
    (hobs S) (hobs S')
  exact BitVec.eq_of_toNat_eq this

/-- `field_causal` for a Bool field (observed as `encodeBool`). -/
theorem field_causalB {D : DomainConfig} {σ : Type}
    (srcF : (Nat → Signal D Bool) → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) → List (Nat → Nat))
    (hsrc : ∀ (B B' : Nat → Signal D Bool) (V V' : (j : Nat) → (n : Nat) → Signal D (BitVec n))
      (t : Nat), (∀ p c, c ≤ t → (B p).val c = (B' p).val c) →
      (∀ p n c, c ≤ t → (V p n).val c = (V' p n).val c) →
      ∀ (k : Nat) (f f' : Nat → Nat), (srcF B V)[k]? = some f → (srcF B' V')[k]? = some f' →
        f t = f' t)
    (famB : Signal D σ → Nat → Signal D Bool)
    (famV : Signal D σ → (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (hfB : ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      ∀ p c, c ≤ t → (famB S p).val c = (famB S' p).val c)
    (hfV : ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      ∀ p n c, c ≤ t → (famV S p n).val c = (famV S' p n).val c)
    (k : Nat) (field : Signal D σ → Signal D Bool)
    (hobs : ∀ S, (srcF (famB S) (famV S))[k]? =
      some (fun t => Tools.ShippingMuxLoweringSoundness.encodeBool ((field S).val t))) :
    ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      (field S).val t = (field S').val t := by
  intro S S' t h
  have := hsrc (famB S) (famB S') (famV S) (famV S') t (hfB S S' t h) (hfV S S' t h) k _ _
    (hobs S) (hobs S')
  have hh : Tools.ShippingMuxLoweringSoundness.encodeBool ((field S).val t) =
      Tools.ShippingMuxLoweringSoundness.encodeBool ((field S').val t) := this
  have e1 := Tools.ShippingMachineChild.encodeBool_ne ((field S).val t)
  have e2 := Tools.ShippingMachineChild.encodeBool_ne ((field S').val t)
  rw [← e1, ← e2, hh]

/-- `field_causal` from the call's causality (`hcall`: the child's source
read on causal input families, proved once per call and shared by its
fields). -/
theorem field_causal_call {D : DomainConfig} {σ : Type}
    (srcF : (Nat → Signal D Bool) → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) → List (Nat → Nat))
    (famB : Signal D σ → Nat → Signal D Bool)
    (famV : Signal D σ → (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (hcall : ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      ∀ (k : Nat) (f f' : Nat → Nat), (srcF (famB S) (famV S))[k]? = some f →
        (srcF (famB S') (famV S'))[k]? = some f' → f t = f' t)
    (k : Nat) {w : Nat} (field : Signal D σ → Signal D (BitVec w))
    (hobs : ∀ S, (srcF (famB S) (famV S))[k]? = some (fun t => ((field S).val t).toNat)) :
    ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      (field S).val t = (field S').val t := by
  intro S S' t h
  exact BitVec.eq_of_toNat_eq (hcall S S' t h k _ _ (hobs S) (hobs S'))

/-- `field_causal_call` for a Bool field. -/
theorem field_causalB_call {D : DomainConfig} {σ : Type}
    (srcF : (Nat → Signal D Bool) → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) → List (Nat → Nat))
    (famB : Signal D σ → Nat → Signal D Bool)
    (famV : Signal D σ → (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (hcall : ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      ∀ (k : Nat) (f f' : Nat → Nat), (srcF (famB S) (famV S))[k]? = some f →
        (srcF (famB S') (famV S'))[k]? = some f' → f t = f' t)
    (k : Nat) (field : Signal D σ → Signal D Bool)
    (hobs : ∀ S, (srcF (famB S) (famV S))[k]? =
      some (fun t => Tools.ShippingMuxLoweringSoundness.encodeBool ((field S).val t))) :
    ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      (field S).val t = (field S').val t := by
  intro S S' t h
  have hh : Tools.ShippingMuxLoweringSoundness.encodeBool ((field S).val t) =
      Tools.ShippingMuxLoweringSoundness.encodeBool ((field S').val t) :=
    hcall S S' t h k _ _ (hobs S) (hobs S')
  have e1 := Tools.ShippingMachineChild.encodeBool_ne ((field S).val t)
  have e2 := Tools.ShippingMachineChild.encodeBool_ne ((field S').val t)
  rw [← e1, ← e2, hh]

/-- A pointwise value is causal. -/
theorem causal_of_pointwise {D : DomainConfig} {σ α : Type} (g : Signal D σ → Signal D α)
    (hpt : ∀ (S : Signal D σ) (t : Nat), (g S).val t = (g ⟨fun _ => S.val t⟩).val t) :
    ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      (g S).val t = (g S').val t := by
  intro S S' t h
  rw [hpt S t, hpt S' t, h t (Nat.le_refl t)]

/-- A value pointwise in the state and in input families that are themselves
causal in the state (the earlier calls' values) is causal. -/
theorem causal_of_pointwise_fam {D : DomainConfig} {σ α : Type}
    (g : Signal D σ → (Nat → Signal D Bool) → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) →
      Signal D α)
    (FB : Signal D σ → Nat → Signal D Bool)
    (FV : Signal D σ → (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (hpt : ∀ (S : Signal D σ) (B : Nat → Signal D Bool)
      (V : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (t : Nat),
      (g S B V).val t = (g ⟨fun _ => S.val t⟩ (fun p => ⟨fun _ => (B p).val t⟩)
        (fun p n => ⟨fun _ => (V p n).val t⟩)).val t)
    (hFB : ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      ∀ p, (FB S p).val t = (FB S' p).val t)
    (hFV : ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      ∀ p n, (FV S p n).val t = (FV S' p n).val t) :
    ∀ (S S' : Signal D σ) (t : Nat), (∀ c, c ≤ t → S.val c = S'.val c) →
      (g S (FB S) (FV S)).val t = (g S' (FB S') (FV S')).val t := by
  intro S S' t h
  rw [hpt S (FB S) (FV S) t, hpt S' (FB S') (FV S') t, h t (Nat.le_refl t)]
  have e1 : (fun p => (⟨fun _ => (FB S p).val t⟩ : Signal D Bool)) =
      fun p => ⟨fun _ => (FB S' p).val t⟩ := by
    funext p; rw [hFB S S' t h p]
  have e2 : (fun p n => (⟨fun _ => (FV S p n).val t⟩ : Signal D (BitVec n))) =
      fun p n => ⟨fun _ => (FV S' p n).val t⟩ := by
    funext p n; rw [hFV S S' t h p n]
  rw [e1, e2]

/-! ## Reading an extension back

The generator states a call entry with the earlier entries read from the
extended families; these give the equation back to the entry as written. -/

theorem ne_of_beq {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; simp [Nat.beq_refl] at h

theorem extendBits_self (D : DomainConfig) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (pos w : Nat) (sig : Signal D (BitVec w)) : extendBits bits pos w sig pos w = sig := by
  simp [extendBits]

theorem extendBits_ne (D : DomainConfig) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (pos w : Nat) (sig : Signal D (BitVec w)) (j n : Nat) (h : j ≠ pos) :
    extendBits bits pos w sig j n = bits j n := by
  simp [extendBits, h]

theorem extendBools_self (D : DomainConfig) (bools : Nat → Signal D Bool) (pos : Nat)
    (sig : Signal D Bool) : extendBools bools pos sig pos = sig := by
  simp [extendBools]

theorem extendBools_ne (D : DomainConfig) (bools : Nat → Signal D Bool) (pos : Nat)
    (sig : Signal D Bool) (j : Nat) (h : j ≠ pos) : extendBools bools pos sig j = bools j := by
  simp [extendBools, h]

/-- Causality moves along an equation at every state. -/
theorem causal_congr {D : DomainConfig} {σ α : Type} (f g : Signal D σ → Signal D α) (he : ∀ S, f S = g S)
    (hg : ∀ S S' t, (∀ c, c ≤ t → S.val c = S'.val c) → (g S).val t = (g S').val t) :
    ∀ S S' t, (∀ c, c ≤ t → S.val c = S'.val c) → (f S).val t = (f S').val t := by
  intro S S' t h; rw [he S, he S']; exact hg S S' t h

end Tools.ShippingMachineCausal
