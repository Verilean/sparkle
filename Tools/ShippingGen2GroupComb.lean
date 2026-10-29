import Tools.ShippingGen2OneOut
import Tools.ShippingMachineCallsLinkedTNR
import Tools.ShippingInstStmtG
set_option autoImplicit false
-- WRITTEN, NOT BUILT (S3 stage A, scripts/gen2/S3_GROUP_FREEZE.md rev1 §3).

/-! # S3 stage A: the general combinational child of a group parent (`instFields ≠ []`, `closeInstsG`)
(scripts/gen2/S3_GROUP_FREEZE.md rev1 §3, approved D1(a)-D5)

* A1 `connsG_keys_comb`, A2 `connsG_field_comb`: `connsG_keys`/`connsG_field` (SeqInst:48-68, :166-190) for a child
  without `"clk"`/`"rst"` inputs (the `if` of `connsG`, LinkedT:31, is false).
* A3 `comb_inst_runN`: `seq_inst_runN` (Depth:98-250) with `SeqChildRunN ↦ CombChildRunN` in `hrun` and `hout`,
  `hrstP`/`hclkP` DELETED (D3). Proof: Depth:123-250 minus its clock/reset parts.
* A4 `seqPC`/`combPC` (the branch predicates, D2) and the agreement with `isSeqChild` (InstStmtG:20-21).
* A5 `CombFactsRN`: `SeqFactsRN` (TNR:23-41) with `SeqChildRunN ↦ CombChildRunN`.
* A6 `calls_hchildRNC`: `calls_hchildRN` (TNR:46-191) with ONLY `hcalls` changed to
  `MemFacts ∨ (SeqFactsRN (seqPC PC) ∧ CombFactsRN (combPC PC))` (D1(a)); the branch is taken per INSTANCE, on the
  instance's module, after `intro … mc …` (AUDIT 3).
* A7 `hcallsC_of_seq` (old per-call premise ⇒ new) and `calls_hchildRN_viaC` (the accepted `calls_hchildRN` statement,
  verbatim, proved by A6 ∘ A7).

No new semantic premise; `rst`-absence of a combinational child comes from `CombChildRunN`'s own conjunct (inside
`comb_inst_runN`), never from a premise. No `hseq`-shaped binder (`∀ mc, ServedPC … c mc → "clk" ∈ …`) anywhere. -/
namespace Tools.ShippingGen2
-- TNR:9-17 verbatim (they contain Depth:15-22 except `seedIn`)
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingMachineLinkedT Tools.ShippingMachineMemLinked Tools.ShippingMachineSeqInst
open Tools.ShippingMachineCallsLinkedT Tools.ShippingMachineDepth Tools.ShippingMachineCallsLinkedTN
open Sparkle.IR.Machine (moduleByName OutField)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCompose (argPorts)
-- Depth:21
open Tools.ShippingSeqOptSoundness (seedIn)
-- freeze §3 ambient
open Tools.ShippingMachineSeqInst (lookup_filter_keep lookup_filter_none lookup_some_mem connsG_arg)
-- names used unqualified in the frozen texts
open Sparkle.Compiler.Elab (MixedGateBinder)
open Tools.ShippingMachineCallsLinkedTNR (SeqFactsRN calls_hchildRN)

/-! ## A1, A2: the connections of a child without clock/reset -/

/-- Without `"clk"`/`"rst"` inputs, `connsG`'s clock/reset condition is false. -/
theorem any_clkrst_false {mc : Module} (hclk : "clk" ∉ mc.inputs.map (·.name))
    (hrst : "rst" ∉ mc.inputs.map (·.name)) :
    mc.inputs.any (fun p => p.name == "clk" || p.name == "rst") = false := by
  cases h : mc.inputs.any (fun p => p.name == "clk" || p.name == "rst") with
  | false => rfl
  | true =>
    obtain ⟨p, hp, hpn⟩ := List.any_eq_true.mp h
    simp only [Bool.or_eq_true, beq_iff_eq] at hpn
    rcases hpn with hc | hr
    · exact absurd (List.mem_map.mpr ⟨p, hp, hc⟩) hclk
    · exact absurd (List.mem_map.mpr ⟨p, hp, hr⟩) hrst

/-- **A1**: the connection list's keys of a child without clock/reset: the argument ports', the read fields. -/
theorem connsG_keys_comb {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} {x : String} {e : Expr}
    (hclk : "clk" ∉ mc.inputs.map (·.name)) (hrst : "rst" ∉ mc.inputs.map (·.name))
    (h : (x, e) ∈ connsG mc argWs outs outWs) :
    x ∈ (argPorts mc).map (·.name) ∨ x ∈ outs.map (·.2) := by
  unfold connsG at h
  simp only [List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨⟨p, w⟩, hpw, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact Or.inl (List.mem_map.mpr ⟨p, (List.of_mem_zip hpw).1, rfl⟩)
  · split at h
    · rename_i hany
      rw [any_clkrst_false hclk hrst] at hany
      cases hany
    · cases h
  · obtain ⟨⟨f, w⟩, hfw, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact Or.inr (List.of_mem_zip hfw).1

/-- **A2**: a non-input key of the connections is a read field, connected to its output wire (no clock/reset). -/
theorem connsG_field_comb {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} (hclk : "clk" ∉ mc.inputs.map (·.name))
    (hrst : "rst" ∉ mc.inputs.map (·.name)) {x : String} {e : Expr}
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
    · rename_i hany
      rw [any_clkrst_false hclk hrst] at hany
      cases hany
    · cases h
  · obtain ⟨⟨f, w⟩, hfw, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨w, rfl, hfw⟩

section
variable (children : String → Option (Module × WEnv))

open Tools.ShippingMachineChild (input_cases) in
/-- **A3: a combinational call's instance runs as its child, at depth `n`.** `seq_inst_runN` (Depth:98) with
`CombChildRunN` for `SeqChildRunN` and no clock/reset premise on `Pw`. -/
theorem comb_inst_runN (dsn : Design) (n : Nat) {mc : Module} {bsC : List (Name × MixedGateBinder)}
    {outsC : List OutField} {S : (Nat → List Nat) → List (Nat → Nat)}
    (hrun : CombChildRunN children dsn n mc bsC outsC S) (argWs : List String) (outs : List (Nat × String))
    (outWs : List String) (Pw : Nat → Env) (T : Nat) (kid : KT n) (vals : Nat → List Nat)
    (hlen : argWs.length = (argPorts mc).length)
    (hfields : ∀ f ∈ outs.map (·.2), f ∈ mc.outputs.map (·.name))
    (hrange : ∀ τ, τ < T → Tools.ShippingMachineChild.InRange (vals τ)
      (bsC.filter fun b => b.2 != .domain))
    (hargs : ∀ t, t < T → argWs.map (Pw t) = vals (T - 1 - t))
    (hreset : ResetN dsn n mc kid)
    (hout : ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e →
      outWs[idx]? = some w →
      ∃ (bsC' : List (Name × MixedGateBinder)) (outsC' : List OutField)
        (S' : (Nat → List Nat) → List (Nat → Nat)),
        CombChildRunN children dsn n mc bsC' outsC' S' ∧
        (∀ τ, τ < T → Tools.ShippingMachineChild.InRange (vals τ)
          (bsC'.filter fun b => b.2 != .domain)) ∧
        ∃ (k : Nat) (o : OutField) (f : Nat → Nat), outsC'[k]? = some o ∧ o.name = e.2 ∧
          (S' vals)[k]? = some f ∧ ∀ t, t < T → Pw t w = f (T - 1 - t)) :
    ∃ cenvs, runKS (KSn children n) mc (Sparkle.IR.RegDedup.declWidth mc)
        (inConns mc.outputs (connsG mc argWs outs outWs)) Pw T kid = some cenvs ∧
      ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
        (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
        (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w) := by
  -- the clock/reset absence is `CombChildRunN`'s own (Defs:66), not a premise
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
  -- every input is connected (an argument port: there is no clock/reset input)
  have hconn : ∀ x, x ∈ mc.inputs.map (·.name) → ∃ w, C.lookup x = some (.ref w) ∧
      ∀ (q : Nat) (p : Port), (argPorts mc)[q]? = some p → p.name = x → argWs[q]? = some w := by
    intro x hx
    rw [hkeep x hx]
    rcases input_cases hx with ha | hcr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain ⟨q, hq, hpq⟩ := List.getElem_of_mem hp
      have hqw : q < argWs.length := by rw [hlen]; exact hq
      refine ⟨argWs[q], connsG_arg hndA (by rw [List.getElem?_eq_getElem hq, hpq])
        (List.getElem?_eq_getElem hqw), ?_⟩
      intro q' p' hp' hn
      have : q' = q := by
        have h1 : ((argPorts mc).map (·.name))[q']? = some p.name := by
          rw [List.getElem?_map, hp', Option.map_some, hn]
        have h2 : ((argPorts mc).map (·.name))[q]? = some p.name := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hq, hpq]; rfl
        have hl1 := (List.getElem?_eq_some_iff.mp h1).1
        exact (List.getElem?_inj hl1 hndA).mp (h1.trans h2.symm)
      subst this; exact List.getElem?_eq_getElem hqw
    · rcases hcr with rfl | rfl
      · exact absurd hx hclk
      · exact absurd hx hrst
  let ins : Nat → String → Nat := fun t x => connEnvS C (Pw t) (fun _ => 0) x
  have hseed : (fun t cst => connEnvS C (Pw t) cst) = seedIn mc ins := by
    funext t cst x
    unfold seedIn
    by_cases hx : x ∈ mc.inputs.map (·.name)
    · obtain ⟨w, hw, _⟩ := hconn x hx
      simp only [ins, List.contains_eq_mem, hx, decide_true, if_true, connEnvS, hw]
    · have hnone : C.lookup x = none := by
        apply lookup_filter_none
        intro e he
        rcases connsG_keys_comb hclk hrst he with ha | hf
        · exact absurd (List.mem_map.mpr (by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
            exact ⟨p, (List.mem_filter.mp hp).1, rfl⟩)) hx
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
    obtain ⟨w', hw', hidx⟩ := hconn _ hpi
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
  obtain ⟨envs, hrunE, hlenE, hobs⟩ := hS T ins kid vals hrange hports hreset
  refine ⟨envs, ?_, ?_⟩
  · rw [runKS_RunOn, hseed]; exact hrunE
  · intro j hj p hp w hlk
    have hj' : j < envs.length := by rw [hlenE]; exact hj
    have hpo : p.name ∈ mc.outputs.map (·.name) := List.mem_map_of_mem hp
    obtain ⟨w', hw', hzip⟩ := connsG_field_comb hclk hrst (lookup_some_mem hlk) (hdisj _ hpo)
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
      obtain ⟨envs', hrun'', hlen', hobs'⟩ := hS' T ins kid vals hrange' hports hreset
      -- the module's run is one run
      have heq : envs' = envs := Option.some.inj (hrun''.symm.trans hrunE)
      subst heq
      rw [List.getElem?_eq_getElem hj', Option.map_some, hPw (T - 1 - j) (by omega),
        show T - 1 - (T - 1 - j) = j by omega]
      rw [hf] at hon
      rw [← hon]
      exact congrArg some (hobs' j hj' k o f hk hf')

/-! ## A4: the branch predicates (D2) and `isSeqChild` -/

/-- **A4** (D2): with the clock input, the sequential branch of `PC`. -/
def seqPC (PC : Name → Module → Prop) : Name → Module → Prop :=
  fun c mc => PC c mc ∧ "clk" ∈ mc.inputs.map (·.name)

/-- **A4** (D2): without the clock input, the combinational branch of `PC`. -/
def combPC (PC : Name → Module → Prop) : Name → Module → Prop :=
  fun c mc => PC c mc ∧ "clk" ∉ mc.inputs.map (·.name)

/-- **A4**: a sequential child run's module is a sequential child for the compiler's `instStmtG` (`seq := true`). -/
theorem isSeqChild_of_seqRunN {dsn : Design} {n : Nat} {mc : Module} {bsC : List (Name × MixedGateBinder)}
    {outsC : List OutField} {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : SeqChildRunN children dsn n mc bsC outsC S) :
    Tools.ShippingInstStmtG.isSeqChild mc = true := by
  obtain ⟨_, _, hclk, _⟩ := h
  obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hclk
  unfold Tools.ShippingInstStmtG.isSeqChild
  exact List.any_eq_true.mpr ⟨p, hp, by simp [hpn]⟩

/-- **A4**: a combinational child run's module is not (`seq := false`: no clock/reset connected). -/
theorem isSeqChild_of_combRunN {dsn : Design} {n : Nat} {mc : Module} {bsC : List (Name × MixedGateBinder)}
    {outsC : List OutField} {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : CombChildRunN children dsn n mc bsC outsC S) :
    Tools.ShippingInstStmtG.isSeqChild mc = false := by
  obtain ⟨_, _, hclk, hrst, _⟩ := h
  unfold Tools.ShippingInstStmtG.isSeqChild
  exact any_clkrst_false hclk hrst

end

/-! ## A5: `CombFactsRN` -/

/-- **A5**: `SeqFactsRN` (TNR:23-41) with `CombChildRunN` for `SeqChildRunN` (TNR:34); otherwise verbatim. -/
def CombFactsRN (children : String → Option (Module × WEnv)) (n : Nat) {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape) (dsn : Design)
    (body : List Stmt) (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (kD : Nat)
    (extB : Nat → Signal D Bool) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (bsC : Name → List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (outsC : Name → List OutField) (S : Name → (Nat → List Nat) → List (Nat → Nat))
    (PC : Name → Module → Prop)
    (k : Nat) (c : Name) : Prop :=
  (shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args : List Nat, (shape.insts.map (·.2.1))[k]? = some args ∧
    (∀ mc : Module, PC c mc →
      CombChildRunN children dsn n mc (bsC c) (outsC c) (S c) ∧ (argPorts mc).length = args.length) ∧
    (∀ (q : Nat) (hq : q < args.length), args[q] < nL ∧ ∃ g, lsrc[args[q]]? = some g) ∧
    (∀ τ, Tools.ShippingMachineChild.InRange (valsOf lsrc args τ)
      ((bsC c).filter fun b => b.2 != .domain)) ∧
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat), (outsC c)[k']? = some o ∧
      o.name = shape.instFields.getD k "" ∧ (S c (valsOf lsrc args))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => (extB p).val τ) (fun p n => (ext p n).val τ)
        (kD + k) ((bsI[k]?.map (·.2)).getD .domain) = f τ

/-! ## A6: the consumer, branching per instance -/

/-- **A6: memory, sequential and combinational children satisfy the composition's premise, at depth `n`.**
`calls_hchildRN` (TNR:46) with ONLY `hcalls` changed (D1(a)). The branch is decided on the INSTANCE's module `mc`
(after `intro`), so every entry of the instance uses the same branch. -/
theorem calls_hchildRNC (children : String → Option (Module × WEnv)) (n : Nat) {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape)
    (dsn : Design) (body : List Stmt) (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (kD : Nat)
    (extB : Nat → Signal D Bool) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (bsC : Name → List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (outsC : Name → List OutField) (S : Name → (Nat → List Nat) → List (Nat → Nat))
    (names : List String) (offA offO : Nat) (T : Nat) (kids : String → KT n)
    (hreset : ∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ body) →
      moduleByName dsn.modules mc.name = some mc → ResetN dsn n mc (kids iname))
    (PC : Name → Module → Prop)
    (hsv : ∀ k c (mc : Module) (iname : String) (argWs : List String) (outs : List (Nat × String))
      (outWs : List String), (shape.insts.map (·.1))[k]? = some c →
      (shape.instOrigins.getD k .ord).child? = none →
      Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ body →
      outs.mapM (fun (k, _) => names[offO + k]?) = some outWs → (∃ e ∈ outs, e.1 = k) →
      moduleByName dsn.modules mc.name = some mc → PC c mc)
    (hcalls : ∀ k c, (shape.insts.map (·.1))[k]? = some c →
      MemFacts shape lsrc nL bsI kD ext k c ∨
      (SeqFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S (seqPC PC) k c ∧
       CombFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S (combPC PC) k c)) :
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
        ∃ cenvs, runKS (KSn children n) mc (Sparkle.IR.RegDedup.declWidth mc)
            (inConns mc.outputs (connsG mc argWs outs outWs)) Pw T (kids iname) = some cenvs ∧
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
  obtain ⟨c0, hc0⟩ := callOf e0 he0
  rcases hcalls e0.1 c0 hc0 with hmem | ⟨hsF0, hcF0⟩
  · -- a memory read: an instance-free child, run flat (TNR:123-146 verbatim)
    obtain ⟨cb, aw, dw, _, _, _, _, _, _, _, _, hmc', _⟩ := id hmem
    have hmm := (hall e0 he0).2.2 c0 _ hc0 hmc'
    subst hmm
    have hf : instFree (Sparkle.Compiler.MachMemory.memModule cb aw dw).1.body := by
      intro st hst
      simp only [Sparkle.Compiler.MachMemory.memModule, List.mem_cons, List.not_mem_nil,
        or_false] at hst
      rcases hst with rfl | rfl <;> rfl
    have hR := hreset iname _ ⟨_, hinst⟩ hmc
    unfold ResetN at hR
    obtain ⟨_, hR0, hRl, _⟩ := hR
    rw [runKS_instFree children _ _ hf]
    exact mem_hchild shape dsn body lsrc nL bsI kD extB ext names offA offO T
      (fun _ => ⟨stOf n (kids iname), memsOf n (kids iname)⟩) (fun _ nm a => hR0 nm a)
      (fun _ => hRl "mem" aw dw "clk" (.ref "wa") (.ref "wd") (.ref "we") (.ref "ra") "out_rdata" cb
        [] [] (by simp [Sparkle.Compiler.MachMemory.memModule]))
      args outs _ iname argWs outWs hargsW hout hmc hinst hne hfnd hfields hall
      (by
        intro e he c hc
        have := memOne e0 he0 c0 hc0 hmem e he
        subst this
        rw [hc0] at hc; cases hc
        exact hmem) Pw hrstP hclkP hPa hPo
  · -- an ordinary call: the branch of THE instance's module (AUDIT 3: after `intro … mc …`)
    by_cases hclk : "clk" ∈ mc.inputs.map (·.name)
    · -- sequential (TNR:147-191, the served module in `seqPC PC`)
      obtain ⟨hnone0, args0, hargs0, hbound0, hlsrc0, hrange0, _⟩ := hsF0
      have hargsEq : args0 = args := by
        rw [(hall e0 he0).1] at hargs0; exact (Option.some.inj hargs0).symm
      subst hargsEq
      obtain ⟨hrun, hlenA⟩ := hbound0 mc
        (And.intro (hsv e0.1 c0 mc iname argWs outs outWs hc0 hnone0 hinst hout ⟨e0, he0, rfl⟩ hmc) hclk)
      obtain ⟨hlW, hgetW⟩ := Tools.ShippingMachineInst.mapM_some _ args0 argWs hargsW
      refine seq_inst_runN children dsn n hrun argWs outs outWs Pw T (kids iname) (valsOf lsrc args0)
        (by rw [hlW, hlenA]) ?_ (fun τ _ => hrange0 τ) ?_ hrstP hclkP
        (hreset iname mc ⟨_, hinst⟩ hmc) ?_
      · intro f hf
        have := List.all_eq_true.mp hfields f hf
        obtain ⟨p, hp, hpf⟩ := List.any_eq_true.mp this
        exact List.mem_map.mpr ⟨p, hp, by simpa using hpf⟩
      · intro t ht
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
      · intro idx e w he hw
        have hem : e ∈ outs := List.mem_of_getElem? he
        obtain ⟨c, hc⟩ := callOf e hem
        rcases hcalls e.1 c hc with hm | ⟨hs, _⟩
        · -- a memory entry would be the only one, the sequential call itself
          have := memOne e hem c hc hm e0 he0
          subst this
          rw [hc0] at hc; cases hc
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hmc', _⟩ := hm
          rw [hnone0] at hmc'; cases hmc'
        · obtain ⟨hnone1, args1, hargs1, hbound1, _, hrange1, k', o, f, hk', hon, hf, hpos⟩ := hs
          have hargsEq : args1 = args0 := by
            rw [(hall e hem).1] at hargs1; exact (Option.some.inj hargs1).symm
          subst hargsEq
          obtain ⟨hrun1, _⟩ := hbound1 mc
            (And.intro (hsv e.1 c mc iname argWs outs outWs hc hnone1 hinst hout ⟨e, hem, rfl⟩ hmc) hclk)
          refine ⟨bsC c, outsC c, S c, hrun1, fun τ _ => hrange1 τ, k', o, f, hk',
            by rw [hon, (hall e hem).2.1], hf, ?_⟩
          intro t ht
          rw [hPo t ht idx e w he hw]
          exact hpos (T - 1 - t)
    · -- combinational (the same text, `comb_inst_runN`, no clock/reset premise; the served module in `combPC PC`)
      obtain ⟨hnone0, args0, hargs0, hbound0, hlsrc0, hrange0, _⟩ := hcF0
      have hargsEq : args0 = args := by
        rw [(hall e0 he0).1] at hargs0; exact (Option.some.inj hargs0).symm
      subst hargsEq
      obtain ⟨hrun, hlenA⟩ := hbound0 mc
        (And.intro (hsv e0.1 c0 mc iname argWs outs outWs hc0 hnone0 hinst hout ⟨e0, he0, rfl⟩ hmc) hclk)
      obtain ⟨hlW, hgetW⟩ := Tools.ShippingMachineInst.mapM_some _ args0 argWs hargsW
      refine comb_inst_runN children dsn n hrun argWs outs outWs Pw T (kids iname) (valsOf lsrc args0)
        (by rw [hlW, hlenA]) ?_ (fun τ _ => hrange0 τ) ?_
        (hreset iname mc ⟨_, hinst⟩ hmc) ?_
      · intro f hf
        have := List.all_eq_true.mp hfields f hf
        obtain ⟨p, hp, hpf⟩ := List.any_eq_true.mp this
        exact List.mem_map.mpr ⟨p, hp, by simpa using hpf⟩
      · intro t ht
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
      · intro idx e w he hw
        have hem : e ∈ outs := List.mem_of_getElem? he
        obtain ⟨c, hc⟩ := callOf e hem
        rcases hcalls e.1 c hc with hm | ⟨_, hs⟩
        · -- a memory entry would be the only one, the combinational call itself
          have := memOne e hem c hc hm e0 he0
          subst this
          rw [hc0] at hc; cases hc
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hmc', _⟩ := hm
          rw [hnone0] at hmc'; cases hmc'
        · obtain ⟨hnone1, args1, hargs1, hbound1, _, hrange1, k', o, f, hk', hon, hf, hpos⟩ := hs
          have hargsEq : args1 = args0 := by
            rw [(hall e hem).1] at hargs1; exact (Option.some.inj hargs1).symm
          subst hargsEq
          obtain ⟨hrun1, _⟩ := hbound1 mc
            (And.intro (hsv e.1 c mc iname argWs outs outWs hc hnone1 hinst hout ⟨e, hem, rfl⟩ hmc) hclk)
          refine ⟨bsC c, outsC c, S c, hrun1, fun τ _ => hrange1 τ, k', o, f, hk',
            by rw [hon, (hall e hem).2.1], hf, ?_⟩
          intro t ht
          rw [hPo t ht idx e w he hw]
          exact hpos (T - 1 - t)

/-! ## A7: compatibility with the accepted consumer -/

/-- **A7**: the accepted per-call premise implies the new one (seq part: `seqPC PC ⊆ PC`; comb part: `SeqChildRunN`'s
`"clk" ∈` against `combPC`'s `∉`, ex falso). -/
theorem hcallsC_of_seq {children : String → Option (Module × WEnv)} {n : Nat} {D : DomainConfig}
    {shape : Sparkle.Compiler.Elab.MachineShape} {dsn : Design} {body : List Stmt} {lsrc : List (Nat → Nat)}
    {nL : Nat} {bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)} {kD : Nat}
    {extB : Nat → Signal D Bool} {ext : (j : Nat) → (n : Nat) → Signal D (BitVec n)}
    {bsC : Name → List (Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : Name → List OutField} {S : Name → (Nat → List Nat) → List (Nat → Nat)}
    (PC : Name → Module → Prop) (k : Nat) (c : Name) :
    MemFacts shape lsrc nL bsI kD ext k c ∨ SeqFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S PC k c →
    MemFacts shape lsrc nL bsI kD ext k c ∨
      (SeqFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S (seqPC PC) k c ∧
       CombFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S (combPC PC) k c) := by
  intro h
  rcases h with hm | hs
  · exact Or.inl hm
  · obtain ⟨h1, args, h2, h3, h4⟩ := hs
    refine Or.inr ⟨⟨h1, args, h2, fun mc hmc => h3 mc (And.left hmc), h4⟩,
      ⟨h1, args, h2, fun mc hmc => absurd (h3 mc (And.left hmc)).1.2.2.1 (And.right hmc), h4⟩⟩

/-- **A7 / N2**: the ACCEPTED `calls_hchildRN` statement (TNR:46-91, restated verbatim), proved by A6 ∘ A7: A6 is no
stronger than the accepted consumer on sequential-only data. -/
theorem calls_hchildRN_viaC (children : String → Option (Module × WEnv)) (n : Nat) {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape)
    (dsn : Design) (body : List Stmt) (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (kD : Nat)
    (extB : Nat → Signal D Bool) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (bsC : Name → List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (outsC : Name → List OutField) (S : Name → (Nat → List Nat) → List (Nat → Nat))
    (names : List String) (offA offO : Nat) (T : Nat) (kids : String → KT n)
    (hreset : ∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ body) →
      moduleByName dsn.modules mc.name = some mc → ResetN dsn n mc (kids iname))
    (PC : Name → Module → Prop)
    (hsv : ∀ k c (mc : Module) (iname : String) (argWs : List String) (outs : List (Nat × String))
      (outWs : List String), (shape.insts.map (·.1))[k]? = some c →
      (shape.instOrigins.getD k .ord).child? = none →
      Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ body →
      outs.mapM (fun (k, _) => names[offO + k]?) = some outWs → (∃ e ∈ outs, e.1 = k) →
      moduleByName dsn.modules mc.name = some mc → PC c mc)
    (hcalls : ∀ k c, (shape.insts.map (·.1))[k]? = some c →
      MemFacts shape lsrc nL bsI kD ext k c ∨
      SeqFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S PC k c) :
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
        ∃ cenvs, runKS (KSn children n) mc (Sparkle.IR.RegDedup.declWidth mc)
            (inConns mc.outputs (connsG mc argWs outs outWs)) Pw T (kids iname) = some cenvs ∧
          ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
            (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
            (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w) :=
  calls_hchildRNC children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S names offA offO T kids hreset
    PC hsv (fun k c hc => hcallsC_of_seq PC k c (hcalls k c hc))

end Tools.ShippingGen2
