import Tools.ShippingGen2AComb
import Tools.ShippingGen2Comb
import Tools.ShippingCallsGateA
import Tools.ShippingGateChildIfaceP
import Tools.ShippingEntryReadsLinked
import Tools.ShippingGateDesign
set_option autoImplicit false
-- NOT BUILT. U-GC0 (scripts/gen2/GATE_GC0_FREEZE.md): transfer of kjob/g4gate-g6 to base 15cd9d1f. No sorry / axiom / native_decide.

/-! # Route unit: a gate leaf child gives `CombChildRunN` (scripts/gen2/ROUTE_CENSUS.md rev2 §5, APPROVED 35e6d4a7)

Run level; no `Pkg` change.

* `gateS` and `gate_combChildRunN`: the §5 types, verbatim. From a `RealChildA` of a declaration the unified
  gate compiles (premises exactly those of `childFull_of_realA` / `#gate_child`), the child's module has no
  descendant, one output `out`, and runs combinationally (`CombChildRunN`) at every depth `n` in every design,
  showing at list index `j` the gate term's value on that cycle's argument values `vals j`.
  Suppliers: `childFull_of_realA` (CallsGateA:48) for the module facts; `not_alloc_clk/rst/out` and
  `inPortsOf_of_alloc` (GateChildIfaceP:78-98) for the clock/reset/output names and `argPorts = inputs`;
  `ChildFull.tys` for the `argPorts` length; `RealChildA.run` + `gate_child_fullG` (EntryReadsLinked:345) with
  `EntryDefinesRunG.of_entry` (:214) for `ChildFn` (one evaluation with `env "rst" = 0`);
  `runModule_assigns_total` (GateDesign:92) for a run of `T` cycles under `seedR` (reset held low);
  S1 `runModule_seed_local` (Gen2Comb) to move it to `seedIn` (`"rst"` is not an input and the body is closed
  over its inputs, `ChildComb.closed`); `RunOn_instFree` (MachineDepth:42) for every depth.
  The `ResetN` antecedent of `CombChildRunN` is not used: the run exists from every state.
* The round trip `gate_childFn_roundTrip`: from the `CombChildRunN` above, S4-b (`childFn_of_combRun`) recovers
  `ChildFn` with the function `fun v => ((gateS … (fun _ => v))[0]?.map (· 0)).getD 0`, and that function IS
  the gate's `F` (`pack`/`eval`, the `F` of `gate_child_fullG`) at every argument list. S4-b
  (Tools/ShippingGen2CombKid.lean, BUILT on par/gen2-spec 1df67a82) is NOT in this base; its proof and the small
  lemmas it uses are COPIED below under `g4_` names (statements and proofs unchanged up to the renaming; the
  definitions they use — `CombChildRunN`, `RunOn_instFree`, `ResetN`, `runModule` — are unchanged between
  1fdbc18d and 1df67a82).

NOT covered (as §5): a `Pkg` constructor, `ChildShips`/`CallDec` re-keying, a route-indexed `T1Hyp`,
`ShipsRes`/`CacheShips` for gate names, route-1 children, gate tops, gate parents with instances, repeated
callees, routes 4-7. `RealChildA` is a hypothesis (a past run): no run existence is claimed. -/
namespace Tools.ShippingGen2

/-! ## Copies of the S4 pure lemmas (Tools/ShippingGen2CombKid.lean on par/gen2-spec, not in this base) -/
section copies
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.RegDedup (isAssign)
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingMachineDepth Tools.ShippingMachineLinked
open Tools.ShippingMachineChild (InRange)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineShipsComb (regNexts_assigns memNexts_assigns applyNexts_nil)

/-- Copy of S4-a `evalAssigns_mems_irrel`: an assignment-only body does not read the memories. -/
theorem g4_evalAssigns_mems_irrel {we : WEnv} : ∀ {body : List Stmt}, body.all isAssign = true →
    ∀ (mems mems' : MEnv) (env : Env), evalAssigns we mems body env = evalAssigns we mems' body env
  | [], _, _, _, _ => rfl
  | st :: rest, h, mems, mems', env => by
    have h2 : rest.all isAssign = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2
    have ih := g4_evalAssigns_mems_irrel (we := we) (body := rest) h2
    cases st with
    | assign l e =>
      simp only [evalAssigns]
      cases hv : evalExpr we env e with
      | none => rfl
      | some v => simp only [Option.bind_eq_bind, Option.bind_some]; exact ih mems mems' _
    | _ => simp [isAssign] at h

/-- Copy of `kstAt`: a depth-`n` state with the given flat state, zero memories and every kid at the zero
state. -/
def g4_kstAt : (n : Nat) → (String → Nat) → KT n
  | 0, st => show KidState from { st := st, mems := fun _ _ => 0 }
  | n + 1, st => show KState (KT n) from { st := st, mems := fun _ _ => 0, kids := fun _ => g4_kstAt n (fun _ => 0) }

theorem g4_stOf_kstAt : ∀ (n : Nat) (st : String → Nat), stOf n (g4_kstAt n st) = st
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem g4_memsOf_kstAt : ∀ (n : Nat) (st : String → Nat), memsOf n (g4_kstAt n st) = fun _ _ => 0
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem g4_instFree_of_assigns {body : List Stmt} (hA : body.all isAssign = true) : instFree body := by
  intro st hst
  have := List.all_eq_true.mp hA st hst
  cases st <;> simp_all [isAssign, Sparkle.IR.Machine.isInst]

/-- Copy of `resetN_kstAt`: an assignment-only module is at reset in every `g4_kstAt` state. -/
theorem g4_resetN_kstAt (dsn : Design) {mc : Module} (hA : mc.body.all isAssign = true) :
    ∀ (n : Nat) (st : String → Nat), ResetN dsn n mc (g4_kstAt n st) := by
  have hno : ∀ s ∈ mc.body, isAssign s = true := fun s hs => List.all_eq_true.mp hA s hs
  intro n st
  unfold ResetN
  refine ⟨fun r c rs inp init hm => absurd (hno _ hm) (by simp [isAssign]),
    fun nm i => by rw [g4_memsOf_kstAt],
    fun nm aw dw c wa wd we ra rd cr ew er hm => absurd (hno _ hm) (by simp [isAssign]), ?_⟩
  cases n with
  | zero => trivial
  | succ k => exact fun mn iname conns mc' hm => absurd (hno _ hm) (by simp [isAssign])

/-- Copy of `runModule_assigns_get`: every cycle of an assignment-only run is one evaluation of the body on
that cycle's seed. -/
theorem g4_runModule_assigns_get {we : WEnv} {body : List Stmt} {seed : Nat → (String → Nat) → Env}
    (hA : body.all isAssign = true) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModule we body seed T st mems = some envs →
      envs.length = T ∧ ∀ j (hj : j < envs.length),
        evalAssigns we mems body (seed (T - 1 - j) st) = some (envs[j]'hj)
  | 0, _, _, envs, h => by
    simp only [runModule, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun j hj => by simp at hj⟩
  | k + 1, st, mems, envs, h => by
    simp only [runModule, stepModule] at h
    cases he : evalAssigns we mems body (seed k st) with
    | none => simp [he] at h
    | some e =>
      simp only [he, regNexts_assigns hA, memNexts_assigns hA, Option.bind_eq_bind, Option.bind_some,
        applyNexts_nil] at h
      cases hr : runModule we body seed k st mems with
      | none => simp [hr] at h
      | some rest =>
        simp only [hr, Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨hl, hg⟩ := g4_runModule_assigns_get hA k st mems rest hr
        refine ⟨by simp [hl], fun j hj => ?_⟩
        cases j with
        | zero => simpa using he
        | succ j =>
          have := hg j (by simpa using hj)
          rw [show k + 1 - 1 - (j + 1) = k - 1 - j by omega]
          simpa using this

theorem g4_seedIn_self (mc : Module) (env : Env) : seedIn mc (fun _ => env) 0 env = env := by
  funext x; simp only [seedIn]; split <;> rfl

/-- **Copy of S4-b `childFn_of_combRun`** (STEP_IFACE_FREEZE.md rev3 §4 S4, frozen type, with R1's `hS`). -/
theorem g4_childFn_of_combRun {dsn : Design} {n : Nat} {mc : Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {o : OutField} {outP : Port}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : CombChildRunN (childMap dsn.modules) dsn n mc bsC [o] S)
    (hA : mc.body.all isAssign = true) (hout : mc.outputs = [outP])
    (hS : ∀ v, InRange v (bsC.filter fun b => b.2 != .domain) → ∃ f, (S (fun _ => v))[0]? = some f) :
    Tools.ShippingMachineCompose.ChildFn mc (fun v => InRange v (bsC.filter fun b => b.2 != .domain))
      (fun v => ((S (fun _ => v))[0]?.map (· 0)).getD 0) := by
  obtain ⟨houts, _, _, _, _, _, hrun⟩ := h
  refine ⟨outP, hout, ?_⟩
  intro mems env _ hP
  let v := (Tools.ShippingMachineCompose.argPorts mc).map fun p => env p.name
  obtain ⟨f, hf⟩ := hS v hP
  obtain ⟨envs, hrunE, hlen, hobs⟩ := hrun 1 (fun _ => env) (g4_kstAt n env) (fun _ => v)
    (fun _ _ => hP) (fun _ _ => rfl) (g4_resetN_kstAt dsn hA n env)
  rw [RunOn_instFree (childMap dsn.modules) mc (g4_instFree_of_assigns hA), g4_stOf_kstAt,
    g4_memsOf_kstAt] at hrunE
  obtain ⟨hl, hg⟩ := g4_runModule_assigns_get hA 1 env _ envs hrunE
  have h0 : 0 < envs.length := by omega
  have he := hg 0 h0
  rw [show 1 - 1 - 0 = 0 from rfl, g4_seedIn_self, g4_evalAssigns_mems_irrel hA _ mems] at he
  refine ⟨envs[0], he, ?_⟩
  have hon : outP.name = o.name := by
    rw [hout] at houts
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at houts
    rw [houts.1]
  rw [hon, hobs 0 h0 0 o f rfl hf]
  show f 0 = ((S (fun _ => v))[0]?.map (· 0)).getD 0
  rw [hf]; rfl

end copies

/-! ## The gate leaf route unit -/
section gate
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.RegDedup (isAssign)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineChild (InRange decB decV)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineShipsComb (seedR)
open Tools.ShippingMachineCompose (ChildFn argPorts)
open Sparkle.Compiler.Elab (MixedGateBinder mixedGatePeel certifiedShape?)
open Tools.ShippingUnifiedMeaning (pack)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInvA (RefLawsAOps)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingChildInv (Res)
open Tools.ShippingGateChildComb (ChildFull)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **The gate leaf's source streams** (§5, verbatim): one stream, at cycle `τ` the gate term's value on the
argument values `vals τ` decoded. -/
noncomputable def gateS (bs : List (Lean.Name × MixedGateBinder)) {srt : Tools.ShippingUnifiedSource.SType}
    (e : Tools.ShippingUnifiedSource.Term srt)
    (bpos vpos : Nat → Nat) : (Nat → List Nat) → List (Nat → Nat) :=
  fun vals => [fun τ => (pack srt (Tools.ShippingUnifiedSource.eval (fun j => decB bs (vals τ) (bpos j))
                                    (fun j w => decV bs (vals τ) (vpos j) w) e)).toNat]

/-- The gate's function on one argument list: the `F` of `gate_child_fullG`. -/
noncomputable def g4_gateVal (bs : List (Lean.Name × MixedGateBinder)) {srt : Tools.ShippingUnifiedSource.SType}
    (e : Tools.ShippingUnifiedSource.Term srt) (bpos vpos : Nat → Nat) (vs : List Nat) : Nat :=
  (pack srt (Tools.ShippingUnifiedSource.eval (fun j => decB bs vs (bpos j))
    (fun j w => decV bs vs (vpos j) w) e)).toNat

theorem g4_gateS_eq (bs : List (Lean.Name × MixedGateBinder)) {srt : Tools.ShippingUnifiedSource.SType}
    (e : Tools.ShippingUnifiedSource.Term srt) (bpos vpos : Nat → Nat) (vals : Nat → List Nat) :
    gateS bs e bpos vpos vals = [fun τ => g4_gateVal bs e bpos vpos (vals τ)] := rfl

theorem gateS_get0 (bs : List (Lean.Name × MixedGateBinder)) {srt : Tools.ShippingUnifiedSource.SType}
    (e : Tools.ShippingUnifiedSource.Term srt) (bpos vpos : Nat → Nat) (vals : Nat → List Nat) :
    (gateS bs e bpos vpos vals)[0]? = some (fun τ => g4_gateVal bs e bpos vpos (vals τ)) := by
  rw [g4_gateS_eq]
  all_goals first
    | rfl
    | simp only [List.getElem?_cons_zero]

/-- `gateS` is never empty (at every argument stream). Not run-level non-vacuity. -/
theorem gateS_ne_nil (bs : List (Lean.Name × MixedGateBinder)) {srt : Tools.ShippingUnifiedSource.SType}
    (e : Tools.ShippingUnifiedSource.Term srt) (bpos vpos : Nat → Nat) (vals : Nat → List Nat) :
    gateS bs e bpos vpos vals ≠ [] := by
  rw [g4_gateS_eq]
  exact List.cons_ne_nil _ _

/-- **A gate leaf child runs combinationally** (§5, verbatim type). -/
theorem gate_combChildRunN (O : RefLawsAOps MkRefd mref cref) {c : Lean.Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Lean.Name × MixedGateBinder)} {kb kv : Nat} {vw bpos vpos : Nat → Nat}
    {srt : Tools.ShippingUnifiedSource.SType} {e : Tools.ShippingUnifiedSource.Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : Lean.DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      Tools.ShippingUnifiedSource.quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChildA O c y) :
    y.2.modules = [] ∧ ∃ o : OutField, o.name = "out" ∧ y.1.outputs = [{ name := o.name, ty := o.ty }] ∧
      ∀ (dsn : Design) (n : Nat),
        CombChildRunN (childMap dsn.modules) dsn n y.1 bs [o] (gateS bs e bpos vpos) := by
  -- the module facts (CallsGateA:48)
  have hfull : ChildFull c bs y.1 y.2 :=
    Tools.ShippingCallsGateA.childFull_of_realA O entry old peel he hb hv h
  -- one evaluation, reset low (EntryReadsLinked:345, at the run of `RealChildA.run`)
  have hfn : ChildFn y.1 (fun vs => InRange vs (bs.filter fun b => b.2 != .domain))
      (g4_gateVal bs e bpos vpos) := by
    cases h with
    | run mctx' cctx' w w' adm cache synth quiet hr =>
      exact Tools.ShippingEntryReadsLinked.gate_child_fullG hr
        (Tools.ShippingEntryReadsLinked.EntryDefinesRunG.of_entry
          (Tools.ShippingReflectCtx.EntryDefines.ctx entry))
        old peel he hb hv (F := g4_gateVal bs e bpos vpos) (fun _ _ => rfl)
  obtain ⟨ty, hout⟩ := hfull.comb.output
  have hA : y.1.body.all isAssign = true := hfull.comb.assigns
  have halloc := hfull.comb.inputAlloc
  have hnotin : ∀ x, ¬ Sparkle.IR.NameHints.Allocated x → x ∉ y.1.inputs.map (·.name) := by
    intro x hx hm
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hm
    apply hx
    rw [← hpx]
    exact halloc p hp
  have hrst : "rst" ∉ y.1.inputs.map (·.name) := hnotin "rst" Tools.ShippingGateChildIfaceP.not_alloc_rst
  have harg : argPorts y.1 = y.1.inputs := by
    have h0 := Tools.ShippingGateChildIfaceP.inPortsOf_of_alloc halloc
    first
      | exact h0
      | (unfold argPorts; unfold Tools.ShippingInstStmtG.inPortsOf at h0; exact h0)
  obtain ⟨outP, houtP, hF⟩ := hfn
  have hon : outP.name = "out" := by
    rw [hout] at houtP
    injection houtP with h1 h2
    first
      | (rw [← h1]; done)
      | (rw [h1]; done)
      | simp [← h1]
  refine ⟨hfull.design, ⟨"out", 0, 0, ty⟩, rfl, hout, ?_⟩
  intro dsn n
  refine ⟨?_, hfull.comb.inputNames, hnotin "clk" Tools.ShippingGateChildIfaceP.not_alloc_clk, hrst,
    ?_, ?_, ?_⟩
  · first
      | (rw [hout]; done)
      | (rw [hout]; rfl)
      | simp [hout]
  · intro x hx
    rw [hout] at hx
    have hx' : x = "out" := by
      first
        | simpa using hx
        | (simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx; exact hx)
    subst hx'
    exact hnotin "out" Tools.ShippingGateChildIfaceP.not_alloc_out
  · rw [harg]
    have hl := congrArg List.length hfull.tys
    simpa only [List.length_map] using hl
  · intro T ins s vals hrange hports _hreset
    rw [Tools.ShippingMachineDepth.RunOn_instFree (childMap dsn.modules) y.1 (g4_instFree_of_assigns hA)]
    -- each cycle `k < T` under `seedR` (reset low): the body evaluates, `out` = the gate on `vals (T-1-k)`
    have hstep : ∀ (k : Nat) (st : String → Nat) (mems : MEnv), k < T →
        ∃ env', evalAssigns (Sparkle.IR.RegDedup.declWidth y.1) mems y.1.body (seedR y.1 ins k st) = some env' ∧
          env' "out" = g4_gateVal bs e bpos vpos (vals (T - 1 - k)) := by
      intro k st mems hk
      have hargs : (argPorts y.1).map (fun p => seedR y.1 ins k st p.name) = vals (T - 1 - k) := by
        rw [Tools.ShippingGateDesign.seedR_args]
        exact hports k hk
      have hP : InRange ((argPorts y.1).map fun p => seedR y.1 ins k st p.name)
          (bs.filter fun b => b.2 != .domain) := by
        rw [hargs]
        exact hrange (T - 1 - k) (by omega)
      obtain ⟨cres, hev, hval⟩ := hF mems (seedR y.1 ins k st)
        (Tools.ShippingGateDesign.seedR_rst y.1 ins k st) hP
      refine ⟨cres, hev, ?_⟩
      have hv' := hval
      rw [hon, hargs] at hv'
      exact hv'
    obtain ⟨envs₁, hr₁, hl₁, hR₁⟩ := Tools.ShippingGateDesign.runModule_assigns_total
      (we := Sparkle.IR.RegDedup.declWidth y.1) (seed := seedR y.1 ins)
      (R := fun k env => env "out" = g4_gateVal bs e bpos vpos (vals (T - 1 - k))) (N := T)
      hA hstep T (Tools.ShippingHierStateG.stOf n s) (Tools.ShippingHierStateG.memsOf n s) (Nat.le_refl T)
    -- S1: the same run under `seedIn` (`"rst"` is not an input; the body is closed over the inputs)
    have hagree : ∀ (t : Nat) (st : String → Nat), ∀ x ∈ y.1.inputs.map (·.name),
        seedR y.1 ins t st x = seedIn y.1 ins t st x := by
      intro t st x hx
      have hne : x ≠ "rst" := fun h' => by subst h'; exact hrst hx
      show (if x = "rst" then 0
        else if (y.1.inputs.map (·.name)).contains x then ins t x else st x) =
          (if (y.1.inputs.map (·.name)).contains x then ins t x else st x)
      rw [if_neg hne]
    obtain ⟨envs₂, hr₂, hl₂, hc₂⟩ := Tools.ShippingGen2Comb.runModule_seed_local
      (seed₁ := seedR y.1 ins) (seed₂ := seedIn y.1 ins) hA hfull.comb.closed hagree
      T (Tools.ShippingHierStateG.stOf n s) (Tools.ShippingHierStateG.memsOf n s) envs₁ hr₁
    refine ⟨envs₂, hr₂, hl₂.trans hl₁, ?_⟩
    intro j hj k o' f ho' hf'
    cases k with
    | succ k => simp at ho'
    | zero =>
      have eo : (⟨"out", 0, 0, ty⟩ : OutField) = o' := by
        first
          | exact Option.some.inj ho'
          | (simp only [List.getElem?_cons_zero, Option.some.injEq] at ho'; exact ho')
      subst eo
      rw [gateS_get0] at hf'
      have ef := Option.some.inj hf'
      subst ef
      have hj₁ : j < envs₁.length := by omega
      show (envs₂[j]'hj) "out" = g4_gateVal bs e bpos vpos (vals j)
      rw [hc₂ j hj₁ hj "out" (List.mem_append.mpr (Or.inr hfull.comb.outDriven))]
      have hRj : (envs₁[j]'hj₁) "out" = g4_gateVal bs e bpos vpos (vals (T - 1 - (T - 1 - j))) :=
        hR₁ j hj₁ (T - 1 - j) (by omega)
      rw [hRj, show T - 1 - (T - 1 - j) = j by omega]

/-- **The round trip** (§5 acceptance, with S4-b): the `CombChildRunN` of `gate_combChildRunN` gives back, through
`childFn_of_combRun` (copied as `g4_childFn_of_combRun`), `ChildFn` with the function read off `gateS` at a
constant stream, and that function is the gate's `F` (`pack`/`eval` of the term on the decoded arguments — the
`F` of `gate_child_fullG`) at EVERY argument list (in particular on the admissible ones). -/
theorem gate_childFn_roundTrip (O : RefLawsAOps MkRefd mref cref) {c : Lean.Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Lean.Name × MixedGateBinder)} {kb kv : Nat} {vw bpos vpos : Nat → Nat}
    {srt : Tools.ShippingUnifiedSource.SType} {e : Tools.ShippingUnifiedSource.Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : Lean.DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      Tools.ShippingUnifiedSource.quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChildA O c y) :
    ∃ o : OutField, o.name = "out" ∧ ∀ (dsn : Design) (n : Nat),
      CombChildRunN (childMap dsn.modules) dsn n y.1 bs [o] (gateS bs e bpos vpos) ∧
      ChildFn y.1 (fun v => InRange v (bs.filter fun b => b.2 != .domain))
        (fun v => ((gateS bs e bpos vpos (fun _ => v))[0]?.map (· 0)).getD 0) ∧
      ∀ v : List Nat, ((gateS bs e bpos vpos (fun _ => v))[0]?.map (· 0)).getD 0 =
        (pack srt (Tools.ShippingUnifiedSource.eval (fun j => decB bs v (bpos j))
          (fun j w => decV bs v (vpos j) w) e)).toNat := by
  have hfull : ChildFull c bs y.1 y.2 :=
    Tools.ShippingCallsGateA.childFull_of_realA O entry old peel he hb hv h
  obtain ⟨_, o, ho, hout, hrun⟩ := gate_combChildRunN O entry old peel he hb hv h
  refine ⟨o, ho, fun dsn n => ⟨hrun dsn n, ?_, ?_⟩⟩
  · exact g4_childFn_of_combRun (hrun dsn n) hfull.comb.assigns hout
      (fun v _ => ⟨_, gateS_get0 bs e bpos vpos (fun _ => v)⟩)
  · intro v
    rw [gateS_get0]
    all_goals rfl

end gate

end Tools.ShippingGen2
