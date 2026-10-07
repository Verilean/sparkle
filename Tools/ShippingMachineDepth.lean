import Tools.ShippingHierStateG
import Tools.ShippingMachineSeqInst
import Tools.ShippingHierMem

/-! # Children at any depth

At depth `n` every instance's state is a `KT n` and its child steps by
`KSn children n` (`ShippingHierStateG`). A child module's own run at depth
`n` (`RunOn`) is flat at depth `0` and a stateful run one level down
otherwise; `ResetN` is its reset state (registers at their reset values,
memories and read latches zero, every instance of it reset one level down).
`SeqChildRunN` is `SeqChildRun` at depth `n`; an instance-free child's
`SeqChildRun` is one at every depth. -/
namespace Tools.ShippingMachineDepth
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingMachineSeqInst
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.IR.Machine (OutField moduleByName)

variable (children : String → Option (Module × WEnv))

/-- A module's own run at depth `n`, its instances' states one level down. -/
def RunOn : (n : Nat) → Module → (Nat → (String → Nat) → Env) → Nat → KT n → Option (List Env)
  | 0, mc, seed, T, s => runModule (Sparkle.IR.RegDedup.declWidth mc) mc.body seed T
      (stOf 0 s) (memsOf 0 s)
  | n + 1, mc, seed, T, s => runModuleTG (KSn children n) (Sparkle.IR.RegDedup.declWidth mc)
      children mc.body seed T s

/-- An instance's run under the depth-`n` step is its module's own run. -/
theorem runKS_RunOn (mc : Module) (cin : List (String × Expr)) (P : Nat → Env) :
    ∀ (n T : Nat) (s : KT n),
      runKS (KSn children n) mc (Sparkle.IR.RegDedup.declWidth mc) cin P T s =
        RunOn children n mc (fun t cst => connEnvS cin (P t) cst) T s
  | 0, T, s => runKS_flat mc _ cin P T s
  | n + 1, T, s => runKS_succ (KSn children n) children mc _ cin P T s

/-- An instance-free module's own run at any depth is its flat run. -/
theorem RunOn_instFree (mc : Module) (hf : instFree mc.body) (seed : Nat → (String → Nat) → Env) :
    ∀ (n T : Nat) (s : KT n),
      RunOn children n mc seed T s =
        runModule (Sparkle.IR.RegDedup.declWidth mc) mc.body seed T (stOf n s) (memsOf n s)
  | 0, _, _ => rfl
  | n + 1, T, s => runModuleTG_instFree (KSn children n) _ children mc.body hf seed T s

/-- A module's reset state at depth `n`: registers at their reset values,
memories zero, sync-read latches zero, and (above depth `0`) every instance's
state its child's reset state. -/
def ResetN (dsn : Design) : (n : Nat) → Module → KT n → Prop
  | n, mc, s =>
    (∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body → stOf n s r = init.toNat) ∧
    (∀ nm i, memsOf n s nm i = 0) ∧
    (∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ mc.body → stOf n s rd = 0) ∧
    match n, s with
    | 0, _ => True
    | k + 1, s => ∀ mn iname conns mc', Stmt.inst mn iname conns ∈ mc.body →
        moduleByName dsn.modules mn = some mc' → ResetN dsn k mc' (KState.kids s iname)

/-- `SeqChildRun` at depth `n`: the module's own run at depth `n` from reset. -/
def SeqChildRunN (dsn : Design) (n : Nat) (mc : Module)
    (bsC : List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (outsC : List OutField) (S : (Nat → List Nat) → List (Nat → Nat)) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧ "clk" ∈ mc.inputs.map (·.name) ∧
  "rst" ∈ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (argPorts mc).length = (bsC.filter fun b => b.2 != .domain).length ∧
  ∀ (T : Nat) (ins : Nat → String → Nat) (s : KT n) (vals : Nat → List Nat),
    (∀ τ, τ < T → Tools.ShippingMachineChild.InRange (vals τ)
      (bsC.filter fun b => b.2 != .domain)) →
    (∀ t, t < T → (argPorts mc).map (fun p => ins t p.name) = vals (T - 1 - t)) →
    (∀ t, ins t "rst" = 0) → (∀ t, ins t "clk" = 0) →
    ResetN dsn n mc s →
    ∃ envs, RunOn children n mc (seedIn mc ins) T s = some envs ∧ envs.length = T ∧
      ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
        outsC[k]? = some o → (S vals)[k]? = some f → (envs[j]'hj) o.name = f j

/-- **An instance-free child's flat description holds at every depth.** -/
theorem seqChildRunN_of_flat (dsn : Design) {mc : Module}
    {bsC : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)} (hf : instFree mc.body)
    (h : SeqChildRun mc bsC outsC S) (n : Nat) : SeqChildRunN children dsn n mc bsC outsC S := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hS⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  intro T ins s vals hrange hports hrst hclk hreset
  unfold ResetN at hreset
  obtain ⟨hregs, _, _, _⟩ := hreset
  rw [RunOn_instFree children mc hf]
  exact hS T ins (stOf n s) (memsOf n s) vals hrange hports hrst hclk hregs

open Tools.ShippingMachineLinkedT in
open Tools.ShippingMachineChild (input_cases) in
/-- **A sequential call's instance runs as its child, at depth `n`.** -/
theorem seq_inst_runN (dsn : Design) (n : Nat) {mc : Module} {bsC : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List OutField} {S : (Nat → List Nat) → List (Nat → Nat)}
    (hrun : SeqChildRunN children dsn n mc bsC outsC S) (argWs : List String) (outs : List (Nat × String))
    (outWs : List String) (Pw : Nat → Env) (T : Nat) (kid : KT n) (vals : Nat → List Nat)
    (hlen : argWs.length = (argPorts mc).length)
    (hfields : ∀ f ∈ outs.map (·.2), f ∈ mc.outputs.map (·.name))
    (hrange : ∀ τ, τ < T → Tools.ShippingMachineChild.InRange (vals τ)
      (bsC.filter fun b => b.2 != .domain))
    (hargs : ∀ t, t < T → argWs.map (Pw t) = vals (T - 1 - t))
    (hrstP : ∀ t, Pw t "rst" = 0) (hclkP : ∀ t, Pw t "clk" = 0)
    (hreset : ResetN dsn n mc kid)
    (hout : ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e →
      outWs[idx]? = some w →
      ∃ (bsC' : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (outsC' : List OutField)
        (S' : (Nat → List Nat) → List (Nat → Nat)),
        SeqChildRunN children dsn n mc bsC' outsC' S' ∧
        (∀ τ, τ < T → Tools.ShippingMachineChild.InRange (vals τ)
          (bsC'.filter fun b => b.2 != .domain)) ∧
        ∃ (k : Nat) (o : OutField) (f : Nat → Nat), outsC'[k]? = some o ∧ o.name = e.2 ∧
          (S' vals)[k]? = some f ∧ ∀ t, t < T → Pw t w = f (T - 1 - t)) :
    ∃ cenvs, runKS (KSn children n) mc (Sparkle.IR.RegDedup.declWidth mc)
        (inConns mc.outputs (connsG mc argWs outs outWs)) Pw T kid = some cenvs ∧
      ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
        (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
        (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w) := by
  obtain ⟨hO, hnd, hclk, hrst, hdisj, _, hS⟩ := hrun
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
  obtain ⟨envs, hrunE, hlenE, hobs⟩ := hS T ins kid vals hrange hports hrstI hclkI
    hreset
  refine ⟨envs, ?_, ?_⟩
  · rw [runKS_RunOn, hseed]; exact hrunE
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
      obtain ⟨bsC', outsC', S', hrun', hrange', k, o, f, hk, hon, hf', hPw⟩ := hout idx e w he hwo
      obtain ⟨_, _, _, _, _, _, hS'⟩ := hrun'
      obtain ⟨envs', hrun'', hlen', hobs'⟩ := hS' T ins kid vals hrange' hports hrstI
        hclkI hreset
      -- the module's run is one run
      have heq : envs' = envs := Option.some.inj (hrun''.symm.trans hrunE)
      subst heq
      rw [List.getElem?_eq_getElem hj', Option.map_some, hPw (T - 1 - j) (by omega),
        show T - 1 - (T - 1 - j) = j by omega]
      rw [hf] at hon
      rw [← hon]
      exact congrArg some (hobs' j hj' k o f hk hf')

end Tools.ShippingMachineDepth
