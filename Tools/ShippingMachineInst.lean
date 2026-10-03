import Sparkle.IR.Machine
import Sparkle.IR.ReorderInvariance

/-! # `closeInsts` keeps the flat semantics

`Sparkle.IR.Machine.closeInsts` ties the `@[hardware_module]` calls of a
machine module to instances: it appends the instance statements, stops the
output ports being inputs and puts the combinational statements in
dependency order. In the flat (open-module) semantics an instance is a
no-op and a wire keeps the value it is seeded with, so the module steps
exactly as before — provided the re-ordering is one the reorder-invariance
theorem allows. `closeInsts` CHECKS what that theorem needs (both bodies
well-ordered, a permutation, the register and memory statements in the same
order, their names distinct), and this file turns the checks into the
equality of `stepModule` and `runModule`. -/
namespace Tools.ShippingMachineInst
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.IR.Reorder

/-- Instance statements do nothing to the environment. -/
theorem evalAssigns_insts (we : WEnv) (mems : MEnv) :
    ∀ (L : List Stmt) (env : Env), L.all isInst = true → evalAssigns we mems L env = some env
  | [], _, _ => rfl
  | st :: rest, env, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases st with
    | inst mn i conns => exact evalAssigns_insts we mems rest env h.2
    | _ => simp [isInst] at h

/-- Appending instance statements does not change the combinational fold. -/
theorem evalAssigns_append_insts (we : WEnv) (mems : MEnv) :
    ∀ (b L : List Stmt) (env : Env), L.all isInst = true →
      evalAssigns we mems (b ++ L) env = evalAssigns we mems b env
  | [], L, env, h => by
    rw [List.nil_append, evalAssigns_insts we mems L env h]
    rfl
  | .assign l r :: rest, L, env, h => by
    simp only [List.cons_append, evalAssigns]
    cases evalExpr we env r with
    | none => rfl
    | some v =>
      try simp only [Option.bind_eq_bind, Option.bind_some]
      exact evalAssigns_append_insts we mems rest L _ h
  | .register o c rk i iv :: rest, L, env, h => by
    simp only [List.cons_append, evalAssigns]
    exact evalAssigns_append_insts we mems rest L env h
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, L, env, h => by
    simp only [List.cons_append, evalAssigns]
    split
    · cases comboReads we mems nm aw dw ((ra, rd) :: er) env with
      | none => rfl
      | some env' =>
        try simp only [Option.bind_eq_bind, Option.bind_some]
        exact evalAssigns_append_insts we mems rest L env' h
    · exact evalAssigns_append_insts we mems rest L env h
  | .inst mn i conns :: rest, L, env, h => by
    simp only [List.cons_append, evalAssigns]
    exact evalAssigns_append_insts we mems rest L env h

/-- The register phase reads the register and memory statements only. -/
theorem regNexts_seqOf (we : WEnv) (mems : MEnv) (env : Env) :
    ∀ body : List Stmt, regNexts we mems body env = regNexts we mems (seqOf body) env
  | [] => rfl
  | .assign l r :: rest => by
    simp only [regNexts, seqOf, List.filter]
    exact regNexts_seqOf we mems env rest
  | .inst mn i conns :: rest => by
    simp only [regNexts, seqOf, List.filter]
    exact regNexts_seqOf we mems env rest
  | .register o c rk i iv :: rest => by
    have ih := regNexts_seqOf we mems env rest
    simp only [seqOf, List.filter_cons_of_pos] at ih ⊢
    simp only [regNexts]
    rw [ih]
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest => by
    have ih := regNexts_seqOf we mems env rest
    simp only [seqOf, List.filter_cons_of_pos] at ih ⊢
    simp only [regNexts]
    rw [ih]

/-- The memory phase reads the register and memory statements only. -/
theorem memNexts_seqOf (we : WEnv) (env : Env) :
    ∀ (body : List Stmt) (mems : MEnv), memNexts we body mems env = memNexts we (seqOf body) mems env
  | [], _ => rfl
  | .assign l r :: rest, mems => by
    simp only [memNexts, seqOf, List.filter]
    exact memNexts_seqOf we env rest mems
  | .inst mn i conns :: rest, mems => by
    simp only [memNexts, seqOf, List.filter]
    exact memNexts_seqOf we env rest mems
  | .register o c rk i iv :: rest, mems => by
    have ih := memNexts_seqOf we env rest mems
    simp only [seqOf, List.filter_cons_of_pos] at ih ⊢
    simp only [memNexts]
    rw [ih]
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, mems => by
    simp only [seqOf, List.filter_cons_of_pos]
    simp only [memNexts]
    cases memWritePorts we mems env nm aw dw ((wa, wd, wen) :: ew) mems with
    | none => rfl
    | some mems' =>
      try simp only [Option.bind_eq_bind, Option.bind_some]
      have ih := memNexts_seqOf we env rest mems'
      simp only [seqOf] at ih
      exact ih

theorem seqOf_append (a b : List Stmt) : seqOf (a ++ b) = seqOf a ++ seqOf b := by
  simp [seqOf, List.filter_append]

theorem seqOf_insts : ∀ L : List Stmt, L.all isInst = true → seqOf L = []
  | [], _ => rfl
  | st :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases st with
    | inst mn i conns =>
      simp only [seqOf, List.filter]
      exact seqOf_insts rest h.2
    | _ => simp [isInst] at h

/-- **One cycle of the re-ordered module is one cycle of the original.** -/
theorem stepModule_closeInsts (we : WEnv) {b L body : List Stmt}
    (hL : L.all isInst = true) (hperm : (b ++ L).Perm body)
    (hwo : WO [] (b ++ L)) (hwo' : WO [] body) (hseq : seqOf (b ++ L) = seqOf body)
    (hmem : ((b ++ L).filterMap stmtMemName).Nodup) (env0 : Env) (mems : MEnv) :
    stepModule we body env0 mems = stepModule we b env0 mems := by
  have e1 : evalAssigns we mems body env0 = evalAssigns we mems b env0 := by
    rw [← evalAssigns_perm we mems hperm hwo hwo' env0, evalAssigns_append_insts we mems b L env0 hL]
  have hseq' : seqOf body = seqOf b := by
    rw [← hseq, seqOf_append, seqOf_insts L hL, List.append_nil]
  unfold stepModule
  rw [e1]
  cases evalAssigns we mems b env0 with
  | none => rfl
  | some envF =>
    try simp only [Option.bind_eq_bind, Option.bind_some]
    rw [regNexts_seqOf we mems envF body, hseq', ← regNexts_seqOf we mems envF b]
    cases regNexts we mems b envF with
    | none => rfl
    | some nexts =>
      try simp only [Option.bind_eq_bind, Option.bind_some]
      rw [memNexts_seqOf we envF body mems, hseq', ← memNexts_seqOf we envF b mems]

/-- The facts `closeInsts` establishes about its result. -/
theorem closeInsts_some {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    m.wires = m₀.wires ∧ m.outputs = m₀.outputs ∧ m.name = m₀.name ∧
    ∃ L : List Stmt, L.all isInst = true ∧ (m₀.body ++ L).Perm m.body ∧
      WO [] (m₀.body ++ L) ∧ WO [] m.body ∧ seqOf (m₀.body ++ L) = seqOf m.body ∧
      ((m₀.body ++ L).filterMap stmtMemName).Nodup ∧ (nextKeys (m₀.body ++ L)).Nodup := by
  unfold closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨stmts, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outWs, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body, hb, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hinst, hwo⟩, hwo'⟩, hperm⟩, hseq⟩, hkeys⟩, hmem⟩ := hc
    cases h
    refine ⟨rfl, rfl, rfl, stmts, hinst, isPermOf_sound hperm, woCheck_sound _ _ hwo,
      woCheck_sound _ _ hwo', hseq, hmem, hkeys⟩
  · cases h

/-- **`closeInsts` keeps every cycle.** -/
theorem stepModule_of_closeInsts {nIn kI n : Nat} {portNames : List String}
    {insts : List (List Nat)} {children : List (Module × Design)} {m₀ : Module} {d₀ : Design}
    {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d))
    (we : WEnv) (env0 : Env) (mems : MEnv) :
    stepModule we m.body env0 mems = stepModule we m₀.body env0 mems := by
  obtain ⟨_, _, _, L, hL, hperm, hwo, hwo', hseq, hmem, _⟩ := closeInsts_some h
  exact stepModule_closeInsts we hL hperm hwo hwo' hseq hmem env0 mems

/-- **`closeInsts` keeps every run.** -/
theorem runModule_of_closeInsts {nIn kI n : Nat} {portNames : List String}
    {insts : List (List Nat)} {children : List (Module × Design)} {m₀ : Module} {d₀ : Design}
    {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d))
    (we : WEnv) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
      runModule we m.body seed k st mems = runModule we m₀.body seed k st mems := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro st mems
    simp only [runModule]
    rw [stepModule_of_closeInsts h we (seed k st) mems]
    cases stepModule we m₀.body (seed k st) mems with
    | none => rfl
    | some r =>
      obtain ⟨envF, nexts, mems'⟩ := r
      try simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ih]

end Tools.ShippingMachineInst
