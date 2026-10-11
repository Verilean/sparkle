import Tools.ShippingCallsRank
import Tools.ShippingTransitionFields

/-! # From the per-field facts of a run to the rank's hypotheses

`Facts` (what `letOperands_facts` gives about each `let`'s operand, from the
per-field facts `LP` of a harness run) as the list of body PREFIXES the rank
`rho` is defined from, with what `rank_closed` asks of each: the prefix is a
prefix of the transition's statements, its statements read protected names
only as the field's rule allows, and the operand is driven in it or is a
protected name the rule allows. -/
namespace Tools.ShippingRankRun
open Lean Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingUnifiedSpine Tools.ShippingMachineCloses
open Tools.ShippingSettledSoundness (Acyclic)

/-- **The prefixes of the fields.** -/
theorem facts_pres {P : String → Prop} {bnd : FVarId → Option String} {Vk : Nat → String → Prop}
    {wires : List Port} {body bodyB : List Stmt} :
    ∀ (al : List (Port × String)) (es : List Lean.Expr) (ws : List Nat) (i : Nat),
      Facts P bnd Vk wires body bodyB i al es ws →
      ∃ pres : List (List Stmt), pres.length = al.length ∧
        ∀ (k : Nat) (pa : Port × String), al[k]? = some pa →
          ∃ pre, pres[k]? = some pre ∧ pre <+: bodyB.reverse ∧
            (∀ l r, Stmt.assign l r ∈ pre → ReadsOK P (Vk (i + k)) r) ∧
            ((∃ rhs, Stmt.assign pa.2 rhs ∈ pre) ∨ P pa.2) ∧ (P pa.2 → Vk (i + k) pa.2) ∧
            ∃ x b, concatParts? body x = some (pa.2, b)
  | [], [], [], _, _ => ⟨[], rfl, fun k pa h => by simp at h⟩
  | pa0 :: al, e :: es, m :: ws, i, hf => by
    obtain ⟨_, hcp, ⟨pre, hsuf, hsrc, hrd⟩, hv, hrest⟩ := hf
    obtain ⟨pres, hlen, hall⟩ := facts_pres al es ws (i + 1) hrest
    refine ⟨pre.reverse :: pres, by simp [hlen], ?_⟩
    intro k pa hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      refine ⟨pre.reverse, rfl, List.reverse_prefix.mpr hsuf,
        fun l r hm => hrd l r (List.mem_reverse.mp hm), ?_, hv, hcp⟩
      rcases hsrc with ⟨_, rhs, hm⟩ | ⟨id, _, _, hp⟩
      · exact Or.inl ⟨rhs, List.mem_reverse.mpr hm⟩
      · exact Or.inr hp
    | succ k =>
      obtain ⟨pre', h1, h2, h3, h4, h5, h6⟩ := hall k pa (by simpa using hk)
      refine ⟨pre', by simpa using h1, h2, ?_, h4, ?_, h6⟩
      · rw [show i + (k + 1) = i + 1 + k by omega]
        exact h3
      · rw [show i + (k + 1) = i + 1 + k by omega]
        exact h5
  | [], _ :: _, _, _, hf => by cases hf
  | [], [], _ :: _, _, hf => by cases hf
  | _ :: _, [], _, _, hf => by cases hf
  | _ :: _, _ :: _, [], _, hf => by cases hf

end Tools.ShippingRankRun
