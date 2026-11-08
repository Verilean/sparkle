import Tools.ShippingFGCircuitS3tComb
set_option autoImplicit false
-- FG circuit pilot S3w, step 2 (fix): the validator `checkCombN`, `checkComb` with ONE proved normalisation of the MODULE's translation before the comparison with the source term: the compiler's Bool-to-bit conversion `mux c (lit 1 1) (lit 1 0)` with a one-bit `c` is `c` (`normB`).  The source term is compared as is (no normalisation on the source side, no relaxed equality).  `checkCombN_sound` has the statement of `checkComb_sound`.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §72.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3wComb
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingFGCircuitS3tComb

/-- the normalisation: a one-bit-condition `mux c (lit 1 1) (lit 1 0)` (the compiler's Bool-to-bit conversion) is `c`; everywhere else the term is rebuilt with its children normalised -/
def normB : CTerm → CTerm
  | .var p w => .var p w
  | .lit w v => .lit w v
  | .eq a b => .eq (normB a) (normB b)
  | .mux c a b =>
    if a = .lit 1 1 ∧ b = .lit 1 0 ∧ c.width = 1 then normB c else .mux (normB c) (normB a) (normB b)
  | .slice a hi lo => .slice (normB a) hi lo
  | .cat a b => .cat (normB a) (normB b)

/-- `normB` keeps the width, the well-formedness and the value of a well-formed term -/
theorem normB_sound (V : Nat → Nat) : ∀ c : CTerm, c.wf = true →
    (normB c).width = c.width ∧ (normB c).wf = true ∧ (normB c).den V = c.den V
  | .var p w, _ => ⟨rfl, rfl, rfl⟩
  | .lit w v, _ => ⟨rfl, rfl, rfl⟩
  | .eq a b, h => by
    simp only [CTerm.wf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨ha, hb⟩, hw⟩ := h
    obtain ⟨wa, fa, da⟩ := normB_sound V a ha
    obtain ⟨wb, fb, db⟩ := normB_sound V b hb
    refine ⟨rfl, ?_, ?_⟩
    · simp [normB, CTerm.wf, fa, fb, wa, wb, hw]
    · simp [normB, CTerm.den, da, db]
  | .mux c a b, h => by
    simp only [CTerm.wf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hc, ha⟩, hb⟩, hc1⟩, hw⟩ := h
    obtain ⟨wc, fc, dc⟩ := normB_sound V c hc
    obtain ⟨wa, fa, da⟩ := normB_sound V a ha
    obtain ⟨wb, fb, db⟩ := normB_sound V b hb
    unfold normB
    split
    · rename_i hcase
      obtain ⟨rfl, rfl, h1⟩ := hcase
      refine ⟨by simp [CTerm.width, wc, h1], fc, ?_⟩
      have hlt := CTerm.den_lt V c hc
      rw [h1] at hlt
      simp only [CTerm.den, dc]
      split <;> omega
    · refine ⟨by simp [CTerm.width, wa], ?_, ?_⟩
      · simp [CTerm.wf, fc, fa, fb, wc, wa, wb, hc1, hw]
      · simp [CTerm.den, dc, da, db]
  | .slice a hi lo, h => by
    simp only [CTerm.wf, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ha, h1⟩, h2⟩ := h
    obtain ⟨wa, fa, da⟩ := normB_sound V a ha
    refine ⟨rfl, ?_, ?_⟩
    · simp [normB, CTerm.wf, fa, wa, h1, h2]
    · simp [normB, CTerm.den, da]
  | .cat a b, h => by
    simp only [CTerm.wf, Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨wa, fa, da⟩ := normB_sound V a ha
    obtain ⟨wb, fb, db⟩ := normB_sound V b hb
    refine ⟨by simp [normB, CTerm.width, wa, wb], by simp [normB, CTerm.wf, fa, fb], ?_⟩
    simp [normB, CTerm.den, da, db, wb]

/-- **the validator with the normalisation**: `checkComb`, except that each output port's translation is normalised (`normB`) before it is compared with the source term, which is compared as is -/
def checkCombN (s : CSrc) (m : Module) : Bool :=
  decide (m.inputs.map (·.name)).Nodup &&
  (m.inputs.length == s.inPos.length) && (m.outputs.length == s.outs.length) &&
  (m.inputs.all fun p => declWidth m p.name == portW p) &&
  (match stepT m ((m.inputs.zip s.inPos).map (fun (p, q) => (p.name, CTerm.var q (portW p)))) m.body with
   | some T => (m.outputs.zip s.outs).all (fun (p, c) => ((look T p.name).map normB == some c) && (portW p == c.width))
   | none => false)

/-- **soundness**: the statement of `checkComb_sound`, for `checkCombN` -/
theorem checkCombN_sound (s : CSrc) (m : Module) (h : checkCombN s m = true) (V : Nat → Nat) (mems : MEnv) (env : Env)
    (hin : ∀ (i : Nat) (p : Port) (q : Nat), m.inputs[i]? = some p → s.inPos[i]? = some q → env p.name = V q % 2 ^ portW p) :
    ∃ env', evalAssigns (declWidth m) mems m.body env = some env' ∧
      ∀ (i : Nat) (p : Port) (c : CTerm), m.outputs[i]? = some p → s.outs[i]? = some c → env' p.name = c.den V := by
  unfold checkCombN at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h⟩ := h
  split at h
  · rename_i T' hT'
    have hT0 : ∀ n c, look ((m.inputs.zip s.inPos).map (fun (p, q) => (p.name, CTerm.var q (portW p)))) n = some c →
        env n = c.den V ∧ c.wf = true := by
      intro n c hn
      obtain ⟨i, p, q, h1, h2, rfl, rfl⟩ := look_inputs m s n c hn
      exact ⟨by simpa [CTerm.den] using hin i p q h1 h2, rfl⟩
    obtain ⟨env', he, hT⟩ := stepT_sound m mems V m.body _ T' env hT0 hT'
    refine ⟨env', he, ?_⟩
    intro i p c hp hc
    have hz : (m.outputs.zip s.outs)[i]? = some (p, c) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hp, hc⟩
    have hmem := List.all_eq_true.mp h (p, c) (List.mem_of_getElem? hz)
    simp only [Bool.and_eq_true, beq_iff_eq] at hmem
    obtain ⟨hl, -⟩ := hmem
    cases hlk : look T' p.name with
    | none => simp [hlk] at hl
    | some t =>
      rw [hlk] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      obtain ⟨he1, hwf⟩ := hT p.name t hlk
      rw [he1, ← hl]
      exact ((normB_sound V t hwf).2.2).symm
  · cases h

end Tools.ShippingFGCircuitS3wComb
