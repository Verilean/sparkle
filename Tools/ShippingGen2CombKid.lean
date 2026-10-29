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

end Tools.ShippingGen2
