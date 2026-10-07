import Tools.ShippingMachineSeqChild
import Tools.ShippingMachineLinkedT

/-! # A sequential child's instance inside the composed machine

`machine_linkedT` asks of every instance its child's own run on the
parent's values (`connEnvS` of the instance's input connections). For a
sequential machine child, `SeqChildRun` packages what its module does over
time (`seqStream_full`) together with its port facts; here that run is
stated on the call group's connections (`connsG`): the connection-fed
seeding is the module's input seeding `seedIn` of the connected values. -/
namespace Tools.ShippingMachineSeqInst
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierState
open Tools.ShippingMachineLinkedT
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.IR.Machine (OutField)
open Tools.ShippingMachineChild (input_cases)

/-- What a sequential child's module does, with its port facts: its outputs
are the layout's, its inputs distinct and include the clock and reset, no
output is an input; over any number of cycles from reset, with argument
ports carrying the value stream `vals`, its run shows `S vals`. -/
def SeqChildRun (mc : Module) (bsC : List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (outsC : List OutField) (S : (Nat → List Nat) → List (Nat → Nat)) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧ "clk" ∈ mc.inputs.map (·.name) ∧
  "rst" ∈ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  ∀ (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
    (vals : Nat → List Nat),
    (∀ τ, τ < T → Tools.ShippingMachineChild.InRange (vals τ)
      (bsC.filter fun b => b.2 != .domain)) →
    (∀ t, t < T → (argPorts mc).map (fun p => ins t p.name) = vals (T - 1 - t)) →
    (∀ t, ins t "rst" = 0) → (∀ t, ins t "clk" = 0) →
    (∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body → st0 r = init.toNat) →
    ∃ envs, runModule (Sparkle.IR.RegDedup.declWidth mc) mc.body (seedIn mc ins) T st0 mems =
        some envs ∧ envs.length = T ∧
      ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
        outsC[k]? = some o → (S vals)[k]? = some f → (envs[j]'hj) o.name = f j

/-- The connection list's keys: the argument ports', the clock and reset,
the read fields. -/
theorem connsG_keys {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} {x : String} {e : Expr}
    (h : (x, e) ∈ connsG mc argWs outs outWs) :
    x ∈ (argPorts mc).map (·.name) ∨ x = "clk" ∨ x = "rst" ∨ x ∈ outs.map (·.2) := by
  unfold connsG at h
  simp only [List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨⟨p, w⟩, hpw, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact Or.inl (List.mem_map.mpr ⟨p, (List.of_mem_zip hpw).1, rfl⟩)
  · split at h
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · cases h
  · obtain ⟨⟨f, w⟩, hfw, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact Or.inr (Or.inr (Or.inr (List.of_mem_zip hfw).1))

theorem lookup_some_mem {L : List (String × Expr)} {x : String} {e : Expr}
    (h : L.lookup x = some e) : (x, e) ∈ L := by
  induction L with
  | nil => simp at h
  | cons c rest ih =>
    obtain ⟨k, v⟩ := c
    simp only [List.lookup] at h
    by_cases hk : x = k
    · subst hk; simp at h; subst h; exact List.mem_cons_self
    · have : (x == k) = false := beq_eq_false_iff_ne.mpr hk
      rw [this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookup_filter_none {L : List (String × Expr)} {P : String × Expr → Bool} {x : String}
    (h : ∀ e, (x, e) ∈ L → P (x, e) = false) : (L.filter P).lookup x = none := by
  cases hl : (L.filter P).lookup x with
  | none => rfl
  | some e =>
    have hm := lookup_some_mem hl
    have := (List.mem_filter.mp hm)
    rw [h e this.1] at this
    cases this.2

theorem lookup_filter_keep {L : List (String × Expr)} {P : String × Expr → Bool} {x : String}
    (h : ∀ e, P (x, e) = true) : (L.filter P).lookup x = L.lookup x := by
  induction L with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨k, v⟩ := c
    by_cases hk : x = k
    · subst hk
      simp only [List.filter_cons, h v, if_true, List.lookup, beq_self_eq_true]
    · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr hk
      by_cases hp : P (k, v) = true
      · simp only [List.filter_cons, hp, if_true, List.lookup, hb]; exact ih
      · simp only [List.filter_cons, hp, List.lookup, hb]
        simp only [Bool.false_eq_true, if_false]
        exact ih

/-- The connection of an argument port: its argument wire. -/
theorem connsG_arg {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} (hnd : ((argPorts mc).map (·.name)).Nodup) {q : Nat} {p : Port}
    {w : String} (hp : (argPorts mc)[q]? = some p) (hw : argWs[q]? = some w) :
    (connsG mc argWs outs outWs).lookup p.name = some (.ref w) := by
  unfold connsG
  rw [List.append_assoc]
  have hpair : (p, w) ∈ (argPorts mc).zip argWs :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hp, hw⟩)
  have key : ∀ (ps : List Port) (ws : List String), (ps.map (·.name)).Nodup →
      (p, w) ∈ ps.zip ws → ∀ rest : List (String × Expr),
      (((ps.zip ws).map fun (x : Port × String) => (x.1.name, Expr.ref x.2)) ++ rest).lookup p.name =
        some (.ref w) := by
    intro ps
    induction ps with
    | nil => intro ws _ h; simp at h
    | cons a ps ih =>
      intro ws hnd h rest
      cases ws with
      | nil => simp at h
      | cons b ws =>
        simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
        simp only [List.zip_cons_cons, List.map_cons, List.cons_append, List.lookup]
        rcases h with ⟨rfl, rfl⟩ | h
        · simp
        · have hne : p.name ≠ a.name := by
            intro he
            rw [List.map_cons, List.nodup_cons] at hnd
            exact hnd.1 (he ▸ List.mem_map_of_mem (List.of_mem_zip h).1)
          rw [beq_eq_false_iff_ne.mpr hne]
          exact ih ws (List.nodup_cons.mp (by simpa using hnd)).2 h rest
  exact key _ _ hnd hpair _

/-- The clock and reset connections. -/
theorem connsG_clkrst {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} (hclk : "clk" ∈ mc.inputs.map (·.name)) {x : String}
    (hx : x = "clk" ∨ x = "rst") :
    (connsG mc argWs outs outWs).lookup x = some (.ref x) := by
  unfold connsG
  rw [List.append_assoc, lookup_append_skip]
  · have hany : mc.inputs.any (fun p => p.name == "clk" || p.name == "rst") = true := by
      obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hclk
      exact List.any_eq_true.mpr ⟨p, hp, by simp [hpn]⟩
    rw [if_pos hany]
    rcases hx with rfl | rfl <;> simp [List.lookup]
  · intro c hc
    obtain ⟨⟨p, w⟩, hpw, rfl⟩ := List.mem_map.mp hc
    have hp := (List.of_mem_zip hpw).1
    unfold argPorts at hp
    have := (List.mem_filter.mp hp).2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    rcases hx with rfl | rfl
    · exact this.1
    · exact this.2

/-- A non-input key of the connections is a read field, connected to its
output wire. -/
theorem connsG_field {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} (hclk : "clk" ∈ mc.inputs.map (·.name))
    (hrst : "rst" ∈ mc.inputs.map (·.name)) {x : String} {e : Expr}
    (h : (x, e) ∈ connsG mc argWs outs outWs) (hx : x ∉ mc.inputs.map (·.name)) :
    ∃ w, e = .ref w ∧ (x, w) ∈ (outs.map (·.2)).zip outWs := by
  unfold connsG at h
  simp only [List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨⟨p, w⟩, hpw, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    have hp := (List.of_mem_zip hpw).1
    exact absurd (List.mem_map_of_mem (List.mem_filter.mp hp).1) hx
  · split at h
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact absurd hclk hx
      · exact absurd hrst hx
    · cases h
  · obtain ⟨⟨f, w⟩, hfw, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨w, rfl, hfw⟩

/-- **A sequential call's instance runs as its child.** -/
theorem seq_inst_run {mc : Module} {bsC : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List OutField} {S : (Nat → List Nat) → List (Nat → Nat)}
    (hrun : SeqChildRun mc bsC outsC S) (argWs : List String) (outs : List (Nat × String))
    (outWs : List String) (Pw : Nat → Env) (T : Nat) (kid : KidState) (vals : Nat → List Nat)
    (hlen : argWs.length = (argPorts mc).length)
    (hfields : ∀ f ∈ outs.map (·.2), f ∈ mc.outputs.map (·.name))
    (hrange : ∀ τ, τ < T → Tools.ShippingMachineChild.InRange (vals τ)
      (bsC.filter fun b => b.2 != .domain))
    (hargs : ∀ t, t < T → argWs.map (Pw t) = vals (T - 1 - t))
    (hrstP : ∀ t, Pw t "rst" = 0) (hclkP : ∀ t, Pw t "clk" = 0)
    (hreset : ∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body → kid.st r = init.toNat)
    (hout : ∀ t, t < T → ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e →
      outWs[idx]? = some w → ∃ (k : Nat) (o : OutField) (f : Nat → Nat), outsC[k]? = some o ∧
        o.name = e.2 ∧ (S vals)[k]? = some f ∧ Pw t w = f (T - 1 - t)) :
    ∃ cenvs, runModule (Sparkle.IR.RegDedup.declWidth mc) mc.body
        (fun t cst => connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw t) cst)
        T kid.st kid.mems = some cenvs ∧
      ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
        (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
        (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w) := by
  obtain ⟨hO, hnd, hclk, hrst, hdisj, hS⟩ := hrun
  have hndA : ((argPorts mc).map (·.name)).Nodup :=
    hnd.sublist (List.Sublist.map _ List.filter_sublist)
  let C := inConns mc.outputs (connsG mc argWs outs outWs)
  -- an input keeps its connection
  have hkeep : ∀ x, x ∈ mc.inputs.map (·.name) →
      C.lookup x = (connsG mc argWs outs outWs).lookup x := by
    intro x hx
    apply lookup_filter_keep
    intro e
    show (!(mc.outputs.map (·.name)).contains x) = true
    rw [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
    exact fun ho => hdisj x ho hx
  -- every input is connected
  have hconn : ∀ x, x ∈ mc.inputs.map (·.name) → ∃ w, C.lookup x = some (.ref w) ∧
      (∀ t, x = "clk" ∨ x = "rst" → Pw t w = 0) ∧
      ∀ (q : Nat) (p : Port), (argPorts mc)[q]? = some p → p.name = x → argWs[q]? = some w := by
    intro x hx
    rw [hkeep x hx]
    rcases input_cases hx with ha | hcr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain ⟨q, hq, hpq⟩ := List.getElem_of_mem hp
      have hqw : q < argWs.length := by rw [hlen]; exact hq
      refine ⟨argWs[q], connsG_arg hndA (by rw [List.getElem?_eq_getElem hq, hpq])
        (List.getElem?_eq_getElem hqw), ?_, ?_⟩
      · intro t hcr
        have := (List.mem_filter.mp hp).2
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
        rcases hcr with h | h
        · exact absurd h this.1
        · exact absurd h this.2
      · intro q' p' hp' hn
        have : q' = q := by
          have h1 : ((argPorts mc).map (·.name))[q']? = some p.name := by
            rw [List.getElem?_map, hp', Option.map_some, hn]
          have h2 : ((argPorts mc).map (·.name))[q]? = some p.name := by
            rw [List.getElem?_map, List.getElem?_eq_getElem hq, hpq]; rfl
          have hl1 := (List.getElem?_eq_some_iff.mp h1).1
          exact (List.getElem?_inj hl1 hndA).mp (h1.trans h2.symm)
        subst this; exact List.getElem?_eq_getElem hqw
    · refine ⟨x, connsG_clkrst hclk hcr, ?_, ?_⟩
      · intro t _
        rcases hcr with rfl | rfl
        · exact hclkP t
        · exact hrstP t
      · intro q p hp hn
        have := (List.mem_filter.mp (List.mem_of_getElem? hp)).2
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
        rcases hcr with rfl | rfl
        · exact absurd hn this.1
        · exact absurd hn this.2
  let ins : Nat → String → Nat := fun t x => connEnvS C (Pw t) (fun _ => 0) x
  have hseed : (fun t cst => connEnvS C (Pw t) cst) = seedIn mc ins := by
    funext t cst x
    unfold seedIn
    by_cases hx : x ∈ mc.inputs.map (·.name)
    · obtain ⟨w, hw, _, _⟩ := hconn x hx
      simp only [ins, List.contains_eq_mem, hx, decide_true, if_true, connEnvS, hw]
    · have hnone : C.lookup x = none := by
        apply lookup_filter_none
        intro e he
        rcases connsG_keys he with ha | hc | hr | hf
        · exact absurd (List.mem_map.mpr (by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
            exact ⟨p, (List.mem_filter.mp hp).1, rfl⟩)) hx
        · exact absurd (hc ▸ hclk) hx
        · exact absurd (hr ▸ hrst) hx
        · simp [List.contains_eq_mem, hfields x hf]
      simp only [connEnvS, hnone, List.contains_eq_mem, hx, decide_false]
      rfl
  -- the argument ports carry the value stream
  have hins_arg : ∀ (t q : Nat) (p : Port) (w : String), (argPorts mc)[q]? = some p →
      argWs[q]? = some w →
      ins t p.name = Pw t w := by
    intro t q p w hp hw
    have hpi : p.name ∈ mc.inputs.map (·.name) :=
      List.mem_map_of_mem (List.mem_filter.mp (List.mem_of_getElem? hp)).1
    obtain ⟨w', hw', _, hidx⟩ := hconn _ hpi
    have := hidx q p hp rfl
    rw [hw] at this; cases this
    simp only [ins, connEnvS, hw']
  have hports : ∀ t, t < T → (argPorts mc).map (fun p => ins t p.name) = vals (T - 1 - t) := by
    intro t ht
    rw [← hargs t ht]
    apply List.ext_getElem (by simp [hlen])
    intro n h1 h2
    simp only [List.getElem_map]
    exact hins_arg t n _ _ (List.getElem?_eq_getElem (by simpa using h1))
      (List.getElem?_eq_getElem (by simpa using h2))
  have hrstI : ∀ t, ins t "rst" = 0 := by
    intro t
    obtain ⟨w, hw, hcr, _⟩ := hconn "rst" hrst
    simp only [ins, connEnvS, hw]
    exact hcr t (Or.inr rfl)
  have hclkI : ∀ t, ins t "clk" = 0 := by
    intro t
    obtain ⟨w, hw, hcr, _⟩ := hconn "clk" hclk
    simp only [ins, connEnvS, hw]
    exact hcr t (Or.inl rfl)
  obtain ⟨envs, hrunE, hlenE, hobs⟩ := hS T ins kid.st kid.mems vals hrange hports hrstI hclkI
    hreset
  refine ⟨envs, ?_, ?_⟩
  · rw [hseed]; exact hrunE
  · intro j hj p hp w hlk
    have hj' : j < envs.length := by rw [hlenE]; exact hj
    have hpo : p.name ∈ mc.outputs.map (·.name) := List.mem_map_of_mem hp
    obtain ⟨w', hw', hzip⟩ := connsG_field hclk hrst (lookup_some_mem hlk) (hdisj _ hpo)
    cases hw'
    obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hzip
    obtain ⟨hf, hwo⟩ := List.getElem?_zip_eq_some.mp hidx
    rw [List.getElem?_map] at hf
    cases he : outs[idx]? with
    | none => rw [he] at hf; cases hf
    | some e =>
      rw [he] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      obtain ⟨k, o, f, hk, hon, hf', hPw⟩ := hout (T - 1 - j) (by omega) idx e w he hwo
      rw [List.getElem?_eq_getElem hj', Option.map_some, hPw,
        show T - 1 - (T - 1 - j) = j by omega]
      rw [hf] at hon
      rw [← hon]
      exact congrArg some (hobs j hj' k o f hk hf')

open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineChild in
open Sparkle.Compiler.Elab Sparkle.IR.RefineCheck in
open Tools.ShippingEntrySoundness (RunsTo) in
/-- **A sequential child at the full entry is a `SeqChildRun`.** -/
theorem seqChildRun_full {declName : Name} {d : MachineData} {ι : Type} {dom : ι → DomainConfig}
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
    SeqChildRun b d.bsIn d.shape.layout.outs
      (fun vals => src i (boolsOf d.bsIn vals) (bitsOf d.bsIn vals)) := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ :=
    Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  have h := sound hcore entry closes
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id h
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨_, _, hi, ho⟩, hrstIn, _, _, hnd, hclk, hdisj, _⟩ := hclean hnoI houtTy
  have hports : b.inputs = raw.inputs ∧ b.outputs = raw.outputs := by
    rcases hpost with rfl | rfl
    · exact ⟨hi, ho⟩
    · obtain ⟨h1, h2, _⟩ := mergeChecked_ports (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
      exact ⟨h1.trans hi, h2.trans ho⟩
  obtain ⟨hbi, hbo⟩ := hports
  refine ⟨by rw [hbo, houts], by rw [hbi]; exact hnd, by rw [hbi]; exact hclk hsl,
    by rw [hbi]; exact hrstIn hsl, by rw [hbi, hbo]; exact hdisj, ?_⟩
  exact seqStream_full sound hnoI hsl hSlen hSS hLlen houtTy hinitFit i hr entry closes

end Tools.ShippingMachineSeqInst
