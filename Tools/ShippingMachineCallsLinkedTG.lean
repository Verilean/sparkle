import Tools.ShippingMachineCallsLinkedTR
import Tools.ShippingGateKid
import Tools.ShippingGateDesign
-- WRITTEN, NOT BUILT (round par/o-gdes, unit "1").

/-! # Memory, sequential AND gate-route children composed, the run boundary derived

`machine_linkedT_callsR` composes a parent whose calls are memory reads and
calls of SEQUENTIAL machine children (`SeqFactsR`, boundary `MachineRun`).
A call of a COMBINATIONAL `@[hardware_module]` the certified unified gate
compiles has no `machine_sound` and its module is not a `SeqChildRun` (it
has no clock and no reset port). Here a third kind of call is added:

* `GateKidRun mc P F n` — what an instance needs of a gate child's module: it
  computes `F` of its argument ports on every environment whose argument
  values are in `P` (`ChildFnR`), its body is assignments only, its inputs
  are distinct, none is `clk`, `rst` or `out`, its one output is `out`, and it
  has `n` argument ports. `gateKidRun_of_gateRun`: every module of a run of
  the full entry on a declaration the unified gate accepts is one (from
  `gate_child_fullFacts` / `gate_child_fnR`; boundary `GateRun`).
* `gate_inst_run` (pure): such a module, instantiated with the call group's
  connections (`connsG`), runs for `T` cycles (`runModule_assigns_total`) and
  drives its output wire with the value each entry's facts give.
* `GateFactsR` / `calls_hchildRG` / `machine_linkedT_callsRG`: the three-way
  per-call premise (memory by ORIGIN; otherwise sequential or gate by the
  callee's kind `gk`, a property of the callee's declaration), the gate
  call's boundary DERIVED from `ServedReal` and the callee's reflection
  `EntryDefines c (vC c)` (moved to the child's run contexts by
  `EntryDefines.ctx`). A sequential and a gate entry cannot share an
  instance (`clk` is an input of the one, not of the other); two gate
  entries of one instance give the same output (one evaluation). -/
namespace Tools.ShippingMachineCallsLinkedTG
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierState
open Tools.ShippingMachineLinkedT Tools.ShippingMachineMemLinked Tools.ShippingMachineSeqInst
open Tools.ShippingMachineCallsLinkedT Tools.ShippingMachineCallsLinkedTR
open Sparkle.IR.Machine (moduleByName OutField)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingFirstGateChild (ChildFnR)

/-- What an instance needs of a gate child's module. -/
structure GateKidRun (mc : Module) (P : List Nat → Prop) (F : List Nat → Nat) (n : Nat) : Prop where
  fn : ChildFnR mc P F
  assigns : mc.body.all Sparkle.IR.RegDedup.isAssign = true
  inputNames : (mc.inputs.map (·.name)).Nodup
  output : ∃ ty, mc.outputs = [{ name := "out", ty := ty }]
  inputs : ∀ p ∈ mc.inputs, p.name ≠ "clk" ∧ p.name ≠ "rst" ∧ p.name ≠ "out"
  argLen : (argPorts mc).length = n

open Sparkle.Compiler.Elab Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge in
open Tools.ShippingMachineChild (InRange decB decV) in
open Tools.ShippingUnifiedMeaning (pack) in
/-- **A module of a run of the full entry on a gate declaration is a
`GateKidRun`** (from the declaration's reflection carried by `GateRun` and
the gate's reading of it: what `#gate_child` generates). -/
theorem gateKidRun_of_gateRun {c : Name} {value dom : Lean.Expr}
    {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    {F : List Nat → Nat}
    (hF : ∀ vs, InRange vs (bs.filter fun b => b.2 != .domain) →
      F vs = (pack srt (eval (fun j => decB bs vs (bpos j)) (fun j w => decV bs vs (vpos j) w) e)).toNat)
    {mc : Module} (h : Tools.ShippingGateChild.GateRun c value mc) :
    GateKidRun mc (fun vs => InRange vs (bs.filter fun b => b.2 != .domain)) F
      (bs.filter fun b => b.2 != .domain).length := by
  obtain ⟨mctx, mref, cctx, cref, w, w', design, hr, entry⟩ := h
  have full := Tools.ShippingGateChildComb.gate_child_fullFacts hr entry old peel he hb hv
  have fn := Tools.ShippingGateKid.gate_child_fnR hr entry old peel he hb hv hF
  have hin : ∀ p ∈ mc.inputs, p.name ≠ "clk" ∧ p.name ≠ "rst" ∧ p.name ≠ "out" := by
    intro p hp
    have alloc := full.comb.inputAlloc p hp
    refine ⟨fun e => Tools.ShippingFirstGateChild.nAlloc_clk (by rw [← e]; exact alloc),
      fun e => Tools.ShippingFirstGateChild.nAlloc_rst (by rw [← e]; exact alloc),
      fun e => Tools.ShippingFirstGateChild.nAlloc_out (by rw [← e]; exact alloc)⟩
  have hargs : argPorts mc = mc.inputs := by
    unfold argPorts
    apply List.filter_eq_self.mpr
    intro p hp
    have hc := (hin p hp).1
    have hr' := (hin p hp).2.1
    simp [hc, hr']
  refine ⟨fn, full.comb.assigns, full.comb.inputNames, full.comb.output, hin, ?_⟩
  have hl := congrArg List.length full.tys
  simp only [List.length_map] at hl
  rw [hargs]
  exact hl

/-- A connection of a non-input, non-clock, non-reset name is a read field. -/
theorem connsG_out_gate {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} {x : String} {e : Expr}
    (h : (x, e) ∈ connsG mc argWs outs outWs) (hx : x ∉ mc.inputs.map (·.name))
    (hc : x ≠ "clk") (hr : x ≠ "rst") :
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
      · exact absurd rfl hc
      · exact absurd rfl hr
    · cases h
  · obtain ⟨⟨f, w⟩, hfw, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨w, rfl, hfw⟩

/-- **A gate call's instance runs.** A `GateKidRun` module instantiated with
the call group's connections, its argument wires carrying the value stream
`vals` (in `P`), runs for `T` cycles; every output entry whose facts give a
function `F'` the module computes (`ChildFnR`, the entry's own callee) and
whose wire carries `F'` of the values, is driven with that wire's value. -/
theorem gate_inst_run {mc : Module} {P : List Nat → Prop} {F : List Nat → Nat} {n : Nat}
    (hrun : GateKidRun mc P F n) (argWs : List String) (outs : List (Nat × String))
    (outWs : List String) (Pw : Nat → Env) (T : Nat) (kid : KidState) (vals : Nat → List Nat)
    (hlen : argWs.length = (argPorts mc).length)
    (hP : ∀ τ, τ < T → P (vals τ))
    (hargs : ∀ t, t < T → argWs.map (Pw t) = vals (T - 1 - t))
    (hout : ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e →
      outWs[idx]? = some w →
      ∃ (P' : List Nat → Prop) (F' : List Nat → Nat), ChildFnR mc P' F' ∧
        (∀ τ, τ < T → P' (vals τ)) ∧ ∀ t, t < T → Pw t w = F' (vals (T - 1 - t))) :
    ∃ cenvs, runModule (Sparkle.IR.RegDedup.declWidth mc) mc.body
        (fun t cst => connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw t) cst)
        T kid.st kid.mems = some cenvs ∧
      ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
        (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
        (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w) := by
  obtain ⟨⟨outP, hO, hf⟩, hall, hnd, ⟨ty, hOut⟩, hin, _⟩ := hrun
  have hndA : ((argPorts mc).map (·.name)).Nodup :=
    hnd.sublist (List.Sublist.map _ List.filter_sublist)
  -- no output is an input
  have hdisj : ∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name) := by
    intro x hx hxi
    rw [hOut] at hx
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hxi
    exact (hin p hp).2.2 (hpn.trans hx)
  -- an input keeps its connection
  have hkeep : ∀ x, x ∈ mc.inputs.map (·.name) →
      (inConns mc.outputs (connsG mc argWs outs outWs)).lookup x =
        (connsG mc argWs outs outWs).lookup x := by
    intro x hx
    apply lookup_filter_keep
    intro e
    show (!(mc.outputs.map (·.name)).contains x) = true
    rw [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
    exact fun ho => hdisj x ho hx
  -- the argument ports carry the value stream
  have hav : ∀ k st, k < T →
      (argPorts mc).map (fun p => connEnvS (inConns mc.outputs (connsG mc argWs outs outWs))
        (Pw k) st p.name) = vals (T - 1 - k) := by
    intro k st hk
    rw [← hargs k hk]
    apply List.ext_getElem (by simp [hlen])
    intro q h1 h2
    simp only [List.getElem_map]
    have hq : q < (argPorts mc).length := by simpa using h1
    have hqw : q < argWs.length := by rw [hlen]; exact hq
    have hpi : (argPorts mc)[q].name ∈ mc.inputs.map (·.name) :=
      List.mem_map_of_mem (List.mem_filter.mp (List.getElem_mem hq)).1
    have hl : (inConns mc.outputs (connsG mc argWs outs outWs)).lookup (argPorts mc)[q].name =
        some (.ref argWs[q]) := by
      rw [hkeep _ hpi]
      exact connsG_arg hndA (List.getElem?_eq_getElem hq) (List.getElem?_eq_getElem hqw)
    simp only [connEnvS, hl]
  -- one cycle: the evaluation exists, and every function the module computes is its output
  have hstep : ∀ (k : Nat) (st : String → Nat) (mems : MEnv), k < T →
      ∃ e, evalAssigns (Sparkle.IR.RegDedup.declWidth mc) mems mc.body
        (connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw k) st) = some e ∧
        ∀ (P' : List Nat → Prop) (F' : List Nat → Nat), ChildFnR mc P' F' →
          P' (vals (T - 1 - k)) → ∀ q ∈ mc.outputs, e q.name = F' (vals (T - 1 - k)) := by
    intro k st mems hk
    have hv := hav k st hk
    obtain ⟨cres, hev, _⟩ := hf mems
      (connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw k) st)
      (by rw [hv]; exact hP _ (by omega))
    refine ⟨cres, hev, ?_⟩
    intro P' F' hfn' hP' q hq
    obtain ⟨outP', hO', hf'⟩ := hfn'
    obtain ⟨cres', hev', hval'⟩ := hf' mems
      (connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw k) st)
      (by rw [hv]; exact hP')
    have heq : cres' = cres := Option.some.inj (hev'.symm.trans hev)
    subst heq
    rw [hO'] at hq
    simp only [List.mem_singleton] at hq
    subst hq
    rw [hval', hv]
  obtain ⟨envs, hrunE, hlenE, hRB⟩ :=
    Tools.ShippingGateDesign.runModule_assigns_total hall
      (seed := fun t cst => connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw t) cst)
      (R := fun k e => ∀ (P' : List Nat → Prop) (F' : List Nat → Nat), ChildFnR mc P' F' →
          P' (vals (T - 1 - k)) → ∀ q ∈ mc.outputs, e q.name = F' (vals (T - 1 - k)))
      (N := T) hstep T kid.st kid.mems (Nat.le_refl T)
  refine ⟨envs, hrunE, ?_⟩
  intro j hj p hp w hlk
  have hj' : j < envs.length := by rw [hlenE]; exact hj
  have hpo : p.name ∈ mc.outputs.map (·.name) := List.mem_map_of_mem hp
  have hpout : p.name = "out" := by
    rw [hOut] at hp
    simp only [List.mem_singleton] at hp
    rw [hp]
  obtain ⟨w', hw', hzip⟩ := connsG_out_gate (lookup_some_mem hlk) (hdisj _ hpo)
    (by rw [hpout]; decide) (by rw [hpout]; decide)
  cases hw'
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hzip
  obtain ⟨hf0, hwo⟩ := List.getElem?_zip_eq_some.mp hidx
  rw [List.getElem?_map] at hf0
  cases he : outs[idx]? with
  | none => rw [he] at hf0; cases hf0
  | some e =>
    obtain ⟨P', F', hfn', hP', hPw⟩ := hout idx e w he hwo
    have hR := hRB j hj' (T - 1 - j) (by omega)
    rw [List.getElem?_eq_getElem hj', Option.map_some, hPw (T - 1 - j) (by omega)]
    exact congrArg some (hR P' F' hfn' (hP' _ (by omega)) p hp)

/-- A gate call's facts with the boundary at the CHILD: every module that is a
run of the callee's full entry with its reflection (`GateRun`) is a
`GateKidRun` of the callee's range and function; the call's arguments are
`let`s whose values are in range, and the call's value at its port is the
callee's function of them. -/
def GateFactsR {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape)
    (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (kD : Nat)
    (extB : Nat → Signal D Bool) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (bsC : Name → List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (vC : Name → Lean.Expr) (FC : Name → List Nat → Nat) (k : Nat) (c : Name) : Prop :=
  (shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args : List Nat, (shape.insts.map (·.2.1))[k]? = some args ∧
    (∀ mc : Module, Tools.ShippingGateChild.GateRun c (vC c) mc →
      ∃ n, GateKidRun mc (fun vs => Tools.ShippingMachineChild.InRange vs
        ((bsC c).filter fun b => b.2 != .domain)) (FC c) n ∧ n = args.length) ∧
    (∀ (q : Nat) (hq : q < args.length), args[q] < nL ∧ ∃ g, lsrc[args[q]]? = some g) ∧
    (∀ τ, Tools.ShippingMachineChild.InRange (valsOf lsrc args τ)
      ((bsC c).filter fun b => b.2 != .domain)) ∧
    ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => (extB p).val τ) (fun p n => (ext p n).val τ)
      (kD + k) ((bsI[k]?.map (·.2)).getD .domain) = FC c (valsOf lsrc args τ)

/-- **Memory, sequential and gate children satisfy the composition's
premise**, each non-memory instance being a run of its call's child entry
(`hsv` for sequential callees, `hsvG` for gate callees: stated for the
instance whose output wires are the call's ports). -/
theorem calls_hchildRG {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape)
    (dsn : Design) (body : List Stmt) (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (kD : Nat)
    (extB : Nat → Signal D Bool) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (bsC : Name → List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (outsC : Name → List OutField) (S : Name → (Nat → List Nat) → List (Nat → Nat))
    (names : List String) (offA offO : Nat) (T : Nat) (kids : String → KidState)
    (hm0 : ∀ iname n a, (kids iname).mems n a = 0)
    (hst0 : ∀ iname, (kids iname).st "out_rdata" = 0)
    (hreg : ∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ body) →
      moduleByName dsn.modules mc.name = some mc →
      ∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body → (kids iname).st r = init.toNat)
    (shC : Name → Sparkle.Compiler.Elab.MachineShape)
    (gk : Name → Bool) (vC : Name → Lean.Expr) (FC : Name → List Nat → Nat)
    (hsv : ∀ k c (mc : Module) (iname : String) (argWs : List String) (outs : List (Nat × String))
      (outWs : List String), (shape.insts.map (·.1))[k]? = some c →
      (shape.instOrigins.getD k .ord).child? = none → gk c = false →
      Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ body →
      outs.mapM (fun (k, _) => names[offO + k]?) = some outWs → (∃ e ∈ outs, e.1 = k) →
      moduleByName dsn.modules mc.name = some mc → Tools.ShippingGateChild.MachineRun c (shC c) mc)
    (hsvG : ∀ k c (mc : Module) (iname : String) (argWs : List String) (outs : List (Nat × String))
      (outWs : List String), (shape.insts.map (·.1))[k]? = some c →
      (shape.instOrigins.getD k .ord).child? = none → gk c = true →
      Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ body →
      outs.mapM (fun (k, _) => names[offO + k]?) = some outWs → (∃ e ∈ outs, e.1 = k) →
      moduleByName dsn.modules mc.name = some mc → Tools.ShippingGateChild.GateRun c (vC c) mc)
    (hcalls : ∀ k c, (shape.insts.map (·.1))[k]? = some c →
      MemFacts shape lsrc nL bsI kD ext k c ∨
      (gk c = false ∧ SeqFactsR shape dsn body lsrc nL bsI kD extB ext bsC outsC S shC k c) ∨
      (gk c = true ∧ GateFactsR shape lsrc nL bsI kD extB ext bsC vC FC k c)) :
    ∀ (args : List Nat) (outs : List (Nat × String)) (mc : Module) (iname : String)
      (argWs outWs : List String),
      args.mapM (fun j => names[offA + j]?) = some argWs →
      outs.mapM (fun (k, _) => names[offO + k]?) = some outWs →
      moduleByName dsn.modules mc.name = some mc →
      Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ body →
      outs ≠ [] → (outs.map (·.2)).Nodup →
      (outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true →
      (∀ e ∈ outs, (shape.insts.map (·.2.1))[e.1]? = some args ∧
        shape.instFields.getD e.1 "" = e.2 ∧
        ∀ c md, (shape.insts.map (·.1))[e.1]? = some c →
          (shape.instOrigins.getD e.1 .ord).child? = some md → mc = md.1) →
      ∀ Pw : Nat → Env,
        (∀ t, Pw t "rst" = 0) → (∀ t, Pw t "clk" = 0) →
        (∀ t, t < T → ∀ (q : Nat) (hq : q < args.length) (w : String) (g : Nat → Nat),
          argWs[q]? = some w → lsrc[args[q]]? = some g → args[q] < nL →
          Pw t w = g (T - 1 - t)) →
        (∀ t, t < T → ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e →
          outWs[idx]? = some w →
          Pw t w = Tools.ShippingMachineEntry.posEnc (fun p => (extB p).val (T - 1 - t))
            (fun p n => (ext p n).val (T - 1 - t)) (kD + e.1)
            ((bsI[e.1]?.map (·.2)).getD .domain)) →
        ∃ cenvs, runModule (Sparkle.IR.RegDedup.declWidth mc) mc.body
            (fun t cst => connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw t) cst)
            T (kids iname).st (kids iname).mems = some cenvs ∧
          ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
            (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
            (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w) := by
  intro args outs mc iname argWs outWs hargsW hout hmc hinst hne hfnd hfields hall Pw hrstP hclkP
    hPa hPo
  obtain ⟨e0, he0⟩ : ∃ e, e ∈ outs := by
    cases outs with
    | nil => exact absurd rfl hne
    | cons e _ => exact ⟨e, List.mem_cons_self⟩
  -- the call of an entry
  have callOf : ∀ e ∈ outs, ∃ c, (shape.insts.map (·.1))[e.1]? = some c := by
    intro e he
    have hk : e.1 < (shape.insts.map (·.2.1)).length :=
      (List.getElem?_eq_some_iff.mp (hall e he).1).1
    exact ⟨_, List.getElem?_eq_getElem (by simpa using hk)⟩
  -- a memory entry's instance has one entry
  have memOne : ∀ e ∈ outs, ∀ c, (shape.insts.map (·.1))[e.1]? = some c →
      MemFacts shape lsrc nL bsI kD ext e.1 c → ∀ e' ∈ outs, e' = e := by
    intro e he c hc hm e' he'
    obtain ⟨cb, aw, dw, _, _, _, _, _, _, _, _, hmc', _⟩ := hm
    have hmm := (hall e he).2.2 c _ hc hmc'
    subst hmm
    have hfo : outs.map (·.2) = ["out"] := by
      apply fields_out (by simpa using hne) hfnd
      intro f hf
      have := List.all_eq_true.mp hfields f hf
      simp only [Sparkle.Compiler.MachMemory.memModule, List.any_cons, List.any_nil, Bool.or_false,
        beq_iff_eq] at this
      exact this.symm
    have hlen : outs.length = 1 := by simpa using congrArg List.length hfo
    match outs, hlen, he, he' with
    | [x], _, he, he' => simp at he he'; rw [he, he']
  -- a memory entry next to a non-memory entry is absurd
  have memNot : ∀ e ∈ outs, ∀ c, (shape.insts.map (·.1))[e.1]? = some c →
      MemFacts shape lsrc nL bsI kD ext e.1 c →
      (shape.instOrigins.getD e0.1 .ord).child? = none → ∀ c0,
      (shape.insts.map (·.1))[e0.1]? = some c0 → False := by
    intro e hem c hc hm hnone0 c0 hc0
    have := memOne e hem c hc hm e0 he0
    subst this
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hmc', _⟩ := hm
    rw [hnone0] at hmc'; cases hmc'
  -- the argument wires carry the call's argument values
  have argStream : ∀ (args0 : List Nat), args0 = args →
      (∀ (q : Nat) (hq : q < args0.length), args0[q] < nL ∧ ∃ g, lsrc[args0[q]]? = some g) →
      ∀ t, t < T → argWs.map (Pw t) = valsOf lsrc args0 (T - 1 - t) := by
    intro args0 hargsEq hlsrc0 t ht
    subst hargsEq
    obtain ⟨hlW, hgetW⟩ := Tools.ShippingMachineInst.mapM_some _ args0 argWs hargsW
    apply List.ext_getElem (by simp [hlW, valsOf])
    intro q h1 h2
    have hq : q < args0.length := by rw [← hlW]; simpa using h1
    obtain ⟨hlt, g, hg⟩ := hlsrc0 q hq
    obtain ⟨w, hw, hwq⟩ := hgetW q hq
    simp only [List.getElem_map, valsOf]
    have hwq' : argWs[q] = w := by
      have := List.getElem?_eq_getElem (l := argWs) (by simpa using h1)
      rw [hwq] at this; exact (Option.some.inj this).symm
    rw [hwq', hPa t ht q hq w g hwq hg hlt, hg]
    rfl
  obtain ⟨c0, hc0⟩ := callOf e0 he0
  rcases hcalls e0.1 c0 hc0 with hmem | ⟨hgk0, hseq⟩ | ⟨hgk0, hgate⟩
  · -- a memory read
    apply mem_hchild shape dsn body lsrc nL bsI kD extB ext names offA offO T kids hm0 hst0 args outs
      mc iname argWs outWs hargsW hout hmc hinst hne hfnd hfields hall _ Pw hrstP hclkP hPa hPo
    intro e he c hc
    have := memOne e0 he0 c0 hc0 hmem e he
    subst this
    rw [hc0] at hc; cases hc
    exact hmem
  · -- a sequential call
    obtain ⟨hnone0, args0, hargs0, hbound0, hlsrc0, hrange0, _⟩ := hseq
    have hargsEq : args0 = args := by
      rw [(hall e0 he0).1] at hargs0; exact (Option.some.inj hargs0).symm
    obtain ⟨hrun, hlenA⟩ := hbound0 mc
      (hsv e0.1 c0 mc iname argWs outs outWs hc0 hnone0 hgk0 hinst hout ⟨e0, he0, rfl⟩ hmc)
    have hclk : "clk" ∈ mc.inputs.map (·.name) := hrun.2.2.1
    have hstream := argStream args0 hargsEq hlsrc0
    subst hargsEq
    obtain ⟨hlW, _⟩ := Tools.ShippingMachineInst.mapM_some _ args0 argWs hargsW
    refine seq_inst_run hrun argWs outs outWs Pw T (kids iname) (valsOf lsrc args0)
      (by rw [hlW, hlenA]) ?_ (fun τ _ => hrange0 τ) hstream hrstP hclkP
      (hreg iname mc ⟨_, hinst⟩ hmc) ?_
    · intro f hf
      have := List.all_eq_true.mp hfields f hf
      obtain ⟨p, hp, hpf⟩ := List.any_eq_true.mp this
      exact List.mem_map.mpr ⟨p, hp, by simpa using hpf⟩
    · intro idx e w he hw
      have hem : e ∈ outs := List.mem_of_getElem? he
      obtain ⟨c, hc⟩ := callOf e hem
      rcases hcalls e.1 c hc with hm | ⟨hgk1, hs⟩ | ⟨hgk, hg⟩
      · exact (memNot e hem c hc hm hnone0 c0 hc0).elim
      · obtain ⟨hnone1, args1, hargs1, hbound1, _, hrange1, k', o, f, hk', hon, hf, hpos⟩ := hs
        have hargsEq : args1 = args0 := by
          rw [(hall e hem).1] at hargs1; exact (Option.some.inj hargs1).symm
        subst hargsEq
        obtain ⟨hrun1, _⟩ := hbound1 mc
          (hsv e.1 c mc iname argWs outs outWs hc hnone1 hgk1 hinst hout ⟨e, hem, rfl⟩ hmc)
        refine ⟨bsC c, outsC c, S c, hrun1, fun τ _ => hrange1 τ, k', o, f, hk',
          by rw [hon, (hall e hem).2.1], hf, ?_⟩
        intro t ht
        rw [hPo t ht idx e w he hw]
        exact hpos (T - 1 - t)
      · -- a gate entry on a sequential instance: the clock is not a gate input
        exfalso
        obtain ⟨hnone1, _, _, hbound1, _⟩ := hg
        obtain ⟨_, hgr, _⟩ := hbound1 mc
          (hsvG e.1 c mc iname argWs outs outWs hc hnone1 hgk hinst hout ⟨e, hem, rfl⟩ hmc)
        obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hclk
        exact (hgr.inputs p hp).1 hpn
  · -- a gate call
    obtain ⟨hnone0, args0, hargs0, hbound0, hlsrc0, hrange0, _⟩ := hgate
    have hargsEq : args0 = args := by
      rw [(hall e0 he0).1] at hargs0; exact (Option.some.inj hargs0).symm
    obtain ⟨n0, hgr0, hn0⟩ := hbound0 mc
      (hsvG e0.1 c0 mc iname argWs outs outWs hc0 hnone0 hgk0 hinst hout ⟨e0, he0, rfl⟩ hmc)
    have hstream := argStream args0 hargsEq hlsrc0
    subst hargsEq
    obtain ⟨hlW, _⟩ := Tools.ShippingMachineInst.mapM_some _ args0 argWs hargsW
    refine gate_inst_run hgr0 argWs outs outWs Pw T (kids iname) (valsOf lsrc args0)
      (by rw [hlW, hgr0.argLen, hn0]) (fun τ _ => hrange0 τ) hstream ?_
    intro idx e w he hw
    have hem : e ∈ outs := List.mem_of_getElem? he
    obtain ⟨c, hc⟩ := callOf e hem
    rcases hcalls e.1 c hc with hm | ⟨hgk, hs⟩ | ⟨hgk, hg⟩
    · exact (memNot e hem c hc hm hnone0 c0 hc0).elim
    · -- a sequential entry on a gate instance: the clock would be an input
      exfalso
      obtain ⟨hnone1, _, _, hbound1, _⟩ := hs
      obtain ⟨hrun1, _⟩ := hbound1 mc
        (hsv e.1 c mc iname argWs outs outWs hc hnone1 hgk hinst hout ⟨e, hem, rfl⟩ hmc)
      obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hrun1.2.2.1
      exact (hgr0.inputs p hp).1 hpn
    · obtain ⟨hnone1, args1, hargs1, hbound1, _, hrange1, hpos⟩ := hg
      have hargsEq : args1 = args0 := by
        rw [(hall e hem).1] at hargs1; exact (Option.some.inj hargs1).symm
      subst hargsEq
      obtain ⟨_, hgr1, _⟩ := hbound1 mc
        (hsvG e.1 c mc iname argWs outs outWs hc hnone1 hgk hinst hout ⟨e, hem, rfl⟩ hmc)
      refine ⟨_, FC c, hgr1.fn, fun τ _ => hrange1 τ, ?_⟩
      intro t ht
      rw [hPo t ht idx e w he hw]
      exact hpos (T - 1 - t)

open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge in
open Sparkle.IR.Machine Sparkle.Compiler.Elab in
/-- **A machine whose calls are memory reads, sequential machine children and
gate-route combinational children, composed with its children — the
child-run boundary derived.** As `machine_linkedT_callsR`, with a third kind
of call (`GateFactsR`, callee kind `gk c = true`); a gate callee's boundary
(`GateRun`) is derived from `ServedReal` and its reflection in the parent's
contexts (`hreflG`: `EntryDefines c (vC c)`). -/
theorem machine_linkedT_callsRG {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX
      (Tools.ShippingMachineTraceX.ServedReal mctx mref cctx cref declName d.shape m dsn)
      declName d m dsn dom src ext extB lsrc)
    (hfe : d.shape.instFields ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (bsC : Name → List (Name × MixedGateBinder)) (outsC : Name → List OutField)
    (S : ι → Name → (Nat → List Nat) → List (Nat → Nat))
    (shC : Name → Sparkle.Compiler.Elab.MachineShape)
    (gk : Name → Bool) (vC : Name → Lean.Expr) (FC : Name → List Nat → Nat)
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
      (d.shape.insts.map (·.1))[k]? = some c →
      MemFacts d.shape (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD (ext i bools bits) k c ∨
      (gk c = false ∧ SeqFactsR d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
        (extB i bools bits) (ext i bools bits) bsC outsC (S i) shC k c) ∨
      (gk c = true ∧ GateFactsR d.shape (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
        (extB i bools bits) (ext i bools bits) bsC vC FC k c))
    -- the sequential children's reflection facts (as `machine_linkedT_callsR`)
    (hrefl : ∀ (k : Nat) (c : Name), (d.shape.insts.map (·.1))[k]? = some c →
      (d.shape.instOrigins.getD k .ord).child? = none → gk c = false →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c (shC c) ∧
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
        Tools.ShippingChildInv.ChildRanIn mref cref c mctx' cctx' →
        Tools.ShippingMachineEntry.MachineCloses mctx' mref cctx' cref c (shC c))
    -- the gate children's reflection: the constant the entry hands on (in the
    -- parent's contexts; it does not depend on them)
    (hreflG : ∀ (k : Nat) (c : Name), (d.shape.insts.map (·.1))[k]? = some c →
      (d.shape.instOrigins.getD k .ord).child? = none → gk c = true →
      Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c (vC c)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
        (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KidState),
        (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
          (fun j => (extB i bools bits j).val (T - 1 - t))
          (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        (∀ iname n a, (kids iname).mems n a = 0) → (∀ iname, (kids iname).st "out_rdata" = 0) →
        (∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
          moduleByName dsn.modules mc.name = some mc →
          ∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body →
            (kids iname).st r = init.toNat) →
        ∃ envs, runModuleT (Tools.ShippingEntrySoundness.weOf m) (childMap dsn.modules) m.body
            seed T st0 mems kids = some envs ∧
          envs.length = T ∧
          ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit hm0 hst0 hreg
  exact machine_linkedT_of nd len rnd rlen llen wired trace hfe kD hkD hI hIlen hSL hSlen hLlen hNIn
    i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit
    (calls_hchildRG d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
      (extB i bools bits) (ext i bools bits) bsC outsC (S i) _ _ _ T kids hm0 hst0 hreg shC
      gk vC FC
      (fun k c mc iname argWs outs outWs hc hnone hgk hst hout hke hmod => by
        have hk : k < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
        have hck : (d.shape.insts[k]).1 = c := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc; simpa using hc
        rcases hx.1 hfe k hk mc iname argWs outs outWs hst hout hke hmod with ⟨md, hmd, _⟩ | ⟨Dc, hrc, hcons⟩
        · rw [hnone] at hmd; cases hmd
        · rw [hck] at hrc
          obtain ⟨mctx', cctx', w, w', hw, hrun⟩ := hrc.inv
          obtain ⟨hdef, hcl⟩ := hrefl k c hc hnone hgk
          exact ⟨mctx', mref, cctx', cref, w, w', Dc, hrun,
            Tools.ShippingReflectCtx.MachineDefines.ctx hdef,
            hcl mctx' cctx' (Tools.ShippingChildInv.ChildRanIn.of_run hw hrun)⟩)
      (fun k c mc iname argWs outs outWs hc hnone hgk hst hout hke hmod => by
        have hk : k < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
        have hck : (d.shape.insts[k]).1 = c := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc; simpa using hc
        rcases hx.1 hfe k hk mc iname argWs outs outWs hst hout hke hmod with ⟨md, hmd, _⟩ | ⟨Dc, hrc, hcons⟩
        · rw [hnone] at hmd; cases hmd
        · rw [hck] at hrc
          obtain ⟨mctx', cctx', w, w', _, hrun⟩ := hrc.inv
          exact ⟨mctx', mref, cctx', cref, w, w', Dc, hrun,
            Tools.ShippingReflectCtx.EntryDefines.ctx (hreflG k c hc hnone hgk)⟩)
      (hcalls i bools bits))

end Tools.ShippingMachineCallsLinkedTG
