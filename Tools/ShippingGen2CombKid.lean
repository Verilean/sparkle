import Tools.ShippingGen2AComb
import Tools.ShippingGen2Comb
set_option autoImplicit false

/-! # M2-step S4 (G-ONEOUT) pure lemmas, part 1 (scripts/gen2/STEP_IFACE_FREEZE.md rev3 §4 S4)

* S4-a `evalAssigns_mems_irrel`: an assignment-only body does not read the memories.
* `Pkg.src_get`: the supplier of S4-b's `hS` and S4-c's `g` (R1 on b7f85204) — every layout output has a source
  observation, for every input. `.gen`: `GenFacts.source`/`result` give `src`'s length `d.outs.length`; `.loop`: the
  same from `LoopFacts.hsrc`/`hres`; `outsFitB` in `d.ok` gives `layout.outs.length ≤ d.outs.length`. -/
namespace Tools.ShippingGen2
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.RegDedup (isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingMachineDepth Tools.ShippingMachineLinked
open Tools.ShippingMachineChild (InRange)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineShipsComb (regNexts_assigns memNexts_assigns applyNexts_nil)

variable {ι : Type} {dom : ι → DomainConfig}

/-- **S4-a** (frozen type). -/
theorem evalAssigns_mems_irrel {we : WEnv} : ∀ {body : List Stmt}, body.all isAssign = true →
    ∀ (mems mems' : MEnv) (env : Env), evalAssigns we mems body env = evalAssigns we mems' body env
  | [], _, _, _, _ => rfl
  | st :: rest, h, mems, mems', env => by
    have h2 : rest.all isAssign = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2
    have ih := evalAssigns_mems_irrel (we := we) (body := rest) h2
    cases st with
    | assign l e =>
      simp only [evalAssigns]
      cases hv : evalExpr we env e with
      | none => rfl
      | some v => simp only [Option.bind_eq_bind, Option.bind_some]; exact ih mems mems' _
    | _ => simp [isAssign] at h

/-- `outsFitB` makes every port have an output term. -/
theorem outsFitB_length {kb kv : Nat} {vw : Nat → Nat}
    {fields : List (Σ w : Nat, Tools.ShippingUnifiedSource.Term (.bits w))} {ports : List OutField}
    {outs : List (Σ s : Tools.ShippingUnifiedSource.SType, Tools.ShippingUnifiedSource.Term s)}
    (h : outsFitB kb kv vw fields ports outs = true) : ports.length ≤ outs.length := by
  rcases Nat.lt_or_ge outs.length ports.length with hlt | hge
  · have hall := List.all_eq_true.mp h outs.length (List.mem_range.mpr hlt)
    simp [List.getElem?_eq_getElem hlt] at hall
  · exact hge

/-- The layout outputs are at most the data's output terms. -/
theorem ok_outs_length (d : MachineData) (ok : d.ok = true) : d.shape.layout.outs.length ≤ d.outs.length := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, houts, _⟩ := ok
  exact outsFitB_length houts

/-- A package's source has one observation per data output term. -/
theorem Pkg.src_length (q : Pkg ι dom) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    (q.src i bools bits).length = q.d.outs.length := by
  cases q with
  | gen p =>
    letI := p.inh
    have hr := congrArg List.length
      (p.gen.result i bools bits (stateLoop p.inits (p.body i bools bits)) 0)
    simp only [List.length_map] at hr
    show (p.src i bools bits).length = p.d.outs.length
    rw [p.gen.source i bools bits]
    exact hr
  | loop p =>
    letI := p.inh
    have hr := congrArg List.length
      (p.facts.hres i bools bits (Signal.loop (p.f i bools bits)) 0)
    simp only [List.length_map] at hr
    show (p.src i bools bits).length = p.d.outs.length
    rw [p.facts.hsrc i bools bits]
    exact hr

/-- **The supplier of `hS` / `g`** (STEP_IFACE_FREEZE.md rev3 §4 S4, frozen type). -/
theorem Pkg.src_get (q : Pkg ι dom) : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k : Nat) (o : OutField),
    q.d.shape.layout.outs[k]? = some o → ∃ f, (q.src i bools bits)[k]? = some f := by
  intro i bools bits k o ho
  have hk : k < q.d.shape.layout.outs.length := (List.getElem?_eq_some_iff.mp ho).1
  have h1 := ok_outs_length q.d q.ok
  have h2 := q.src_length i bools bits
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-! ## S4-b / S4-c: a flat combinational child run, per cycle -/

/-- A depth-`n` state with the given flat state, zero memories and every kid at the zero state. -/
def kstAt : (n : Nat) → (String → Nat) → KT n
  | 0, st => show KidState from { st := st, mems := fun _ _ => 0 }
  | n + 1, st => show KState (KT n) from { st := st, mems := fun _ _ => 0, kids := fun _ => kstAt n (fun _ => 0) }

theorem stOf_kstAt : ∀ (n : Nat) (st : String → Nat), stOf n (kstAt n st) = st
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem memsOf_kstAt : ∀ (n : Nat) (st : String → Nat), memsOf n (kstAt n st) = fun _ _ => 0
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem instFree_of_assigns {body : List Stmt} (hA : body.all isAssign = true) : instFree body := by
  intro st hst
  have := List.all_eq_true.mp hA st hst
  cases st <;> simp_all [isAssign, Sparkle.IR.Machine.isInst]

/-- An assignment-only module is at reset in every `kstAt` state. -/
theorem resetN_kstAt (dsn : Design) {mc : Module} (hA : mc.body.all isAssign = true) :
    ∀ (n : Nat) (st : String → Nat), ResetN dsn n mc (kstAt n st) := by
  have hno : ∀ s ∈ mc.body, isAssign s = true := fun s hs => List.all_eq_true.mp hA s hs
  intro n st
  unfold ResetN
  refine ⟨fun r c rs inp init hm => absurd (hno _ hm) (by simp [isAssign]),
    fun nm i => by rw [memsOf_kstAt],
    fun nm aw dw c wa wd we ra rd cr ew er hm => absurd (hno _ hm) (by simp [isAssign]), ?_⟩
  cases n with
  | zero => trivial
  | succ k => exact fun mn iname conns mc' hm => absurd (hno _ hm) (by simp [isAssign])

/-- Every cycle of an assignment-only run is one evaluation of the body on that cycle's seed. -/
theorem runModule_assigns_get {we : WEnv} {body : List Stmt} {seed : Nat → (String → Nat) → Env}
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
        obtain ⟨hl, hg⟩ := runModule_assigns_get hA k st mems rest hr
        refine ⟨by simp [hl], fun j hj => ?_⟩
        cases j with
        | zero => simpa using he
        | succ j =>
          have := hg j (by simpa using hj)
          rw [show k + 1 - 1 - (j + 1) = k - 1 - j by omega]
          simpa using this

/-- Looking up each name of a distinct list in its zip with values gives the values. -/
theorem map_lookup_zip : ∀ (xs : List String) (vs : List Nat), xs.Nodup → xs.length = vs.length →
    xs.map (fun x => ((xs.zip vs).lookup x).getD 0) = vs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | x :: xs, v :: vs, hnd, hl => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.zip_cons_cons]
    congr 1
    · simp [List.lookup]
    · conv => rhs; rw [← map_lookup_zip xs vs hnd.2 (by simpa using hl)]
      apply List.map_congr_left
      intro y hy
      have hne : y ≠ x := fun h => hnd.1 (h ▸ hy)
      simp [List.lookup, hne]

theorem seedIn_self (mc : Module) (env : Env) : seedIn mc (fun _ => env) 0 env = env := by
  funext x; simp only [seedIn]; split <;> rfl

/-- **S4-b** (frozen type, STEP_IFACE_FREEZE.md rev3 §4 S4, with R1's `hS`). -/
theorem childFn_of_combRun {dsn : Design} {n : Nat} {mc : Module}
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
  obtain ⟨envs, hrunE, hlen, hobs⟩ := hrun 1 (fun _ => env) (kstAt n env) (fun _ => v)
    (fun _ _ => hP) (fun _ _ => rfl) (resetN_kstAt dsn hA n env)
  rw [RunOn_instFree (childMap dsn.modules) mc (instFree_of_assigns hA), stOf_kstAt, memsOf_kstAt] at hrunE
  obtain ⟨hl, hg⟩ := runModule_assigns_get hA 1 env _ envs hrunE
  have h0 : 0 < envs.length := by omega
  have he := hg 0 h0
  rw [show 1 - 1 - 0 = 0 from rfl, seedIn_self, evalAssigns_mems_irrel hA _ mems] at he
  refine ⟨envs[0], he, ?_⟩
  have hon : outP.name = o.name := by
    rw [hout] at houts
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at houts
    rw [houts.1]
  rw [hon, hobs 0 h0 0 o f rfl hf]
  show f 0 = ((S (fun _ => v))[0]?.map (· 0)).getD 0
  rw [hf]; rfl

/-- **S4-c** (frozen type): the source stream of a flat combinational child is pointwise in its argument
stream. -/
theorem combS_pointwise {dsn : Design} {n : Nat} {mc : Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : CombChildRunN (childMap dsn.modules) dsn n mc bsC outsC S) (hA : mc.body.all isAssign = true) :
    ∀ (vals : Nat → List Nat) (τ : Nat) (k : Nat) (o : OutField) (f g : Nat → Nat),
      (∀ τ', τ' ≤ τ → InRange (vals τ') (bsC.filter fun b => b.2 != .domain)) →
      outsC[k]? = some o → (S vals)[k]? = some f → (S (fun _ => vals τ))[k]? = some g → f τ = g 0 := by
  obtain ⟨_, hnd, _, _, _, hlenP, hrun⟩ := h
  intro vals τ k o f g hrange ho hf hg
  let names := (Tools.ShippingMachineCompose.argPorts mc).map (·.name)
  have hndN : names.Nodup :=
    List.Nodup.sublist (List.Sublist.map _ (List.filter_sublist)) hnd
  let insA : Nat → String → Nat := fun t x => ((names.zip (vals (τ + 1 - 1 - t))).lookup x).getD 0
  have hportsA : ∀ t, t < τ + 1 →
      (Tools.ShippingMachineCompose.argPorts mc).map (fun p => insA t p.name) = vals (τ + 1 - 1 - t) := by
    intro t ht
    have hlv : names.length = (vals (τ + 1 - 1 - t)).length := by
      have := (hrange (τ + 1 - 1 - t) (by omega)).length_eq
      simp only [names, List.length_map]; omega
    have := map_lookup_zip names (vals (τ + 1 - 1 - t)) hndN hlv
    simpa only [names, List.map_map, Function.comp_def] using this
  have hreset := resetN_kstAt dsn hA n (fun _ => 0)
  obtain ⟨envsA, hrunA, hlenA, hobsA⟩ := hrun (τ + 1) insA (kstAt n (fun _ => 0)) vals
    (fun τ' h' => hrange τ' (by omega)) hportsA hreset
  obtain ⟨envsB, hrunB, hlenB, hobsB⟩ := hrun 1 (fun _ => insA 0) (kstAt n (fun _ => 0)) (fun _ => vals τ)
    (fun _ _ => hrange τ (Nat.le_refl _)) (fun t ht => by
      have := hportsA 0 (by omega)
      rw [show τ + 1 - 1 - 0 = τ by omega] at this
      exact this) hreset
  rw [RunOn_instFree (childMap dsn.modules) mc (instFree_of_assigns hA), stOf_kstAt, memsOf_kstAt] at hrunA hrunB
  obtain ⟨_, hgA⟩ := runModule_assigns_get hA _ _ _ envsA hrunA
  obtain ⟨_, hgB⟩ := runModule_assigns_get hA _ _ _ envsB hrunB
  have hA' := hgA τ (by omega)
  have hB' := hgB 0 (by omega)
  rw [show τ + 1 - 1 - τ = 0 by omega] at hA'
  have heq : envsA[τ]'(by omega) = envsB[0]'(by omega) := Option.some.inj (hA'.symm.trans hB')
  rw [← hobsA τ (by omega) k o f ho hf, ← hobsB 0 (by omega) k o g ho hg, heq]

end Tools.ShippingGen2
