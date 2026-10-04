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
      ((m₀.body ++ L).filterMap stmtMemName).Nodup ∧ (nextKeys (m₀.body ++ L)).Nodup ∧
      d = designWith children d₀ ∧ linkedOk (moduleByName d.modules) m.body = true := by
  unfold closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨stmts, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outWs, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body, hb, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hinst, _⟩, hwo⟩, hwo'⟩, hperm⟩, hseq⟩, hkeys⟩, hmem⟩, hlink⟩ := hc
    cases h
    refine ⟨rfl, rfl, rfl, stmts, hinst, isPermOf_sound hperm, woCheck_sound _ _ hwo,
      woCheck_sound _ _ hwo', hseq, hmem, hkeys, rfl, hlink⟩
  · cases h

/-- An `Option` `mapM` that succeeds succeeds at every element. -/
theorem mapM_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r →
      r.length = l.length ∧ ∀ i (hi : i < l.length), ∃ y, f l[i] = some y ∧ r[i]? = some y
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | x :: xs, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_bind] at h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, hys, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure, Option.some.injEq] at h
    subst h
    obtain ⟨hl, hget⟩ := mapM_some f xs ys hys
    refine ⟨by simp [hl], fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨y, hy, rfl⟩
    | succ i =>
      obtain ⟨z, hz, hzr⟩ := hget i (by simpa using hi)
      exact ⟨z, hz, by simpa using hzr⟩

/-- The instance statement of call `k`: an instance of the call's child,
its input ports connected to the call's argument wires, its output port to
the transition's input port `portNames[nIn + k]`. -/
def CallStmt (nIn kI n : Nat) (portNames : List String) (k : Nat) (args : List Nat)
    (mc : Module) (st : Stmt) : Prop :=
  ∃ outW argWs outP iname, portNames[nIn + k]? = some outW ∧
    args.mapM (fun j => portNames[nIn + kI + n + j]?) = some argWs ∧
    mc.outputs = [outP] ∧
    (mc.inputs.any (fun p => p.name == "clk" || p.name == "rst")) = false ∧
    (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").length = argWs.length ∧
    ((mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").map (·.name)).Nodup ∧
    outW ∉ argWs ∧
    outP.name ∉ (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").map (·.name) ∧
    st = .inst mc.name iname
      (((mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").zip argWs).map
        (fun (p, w) => (p.name, Expr.ref w)) ++ [(outP.name, Expr.ref outW)])

theorem instStmt_some {nIn kI n : Nat} {portNames : List String} {k : Nat} {args : List Nat}
    {mc m : Module} {st : Stmt} (h : instStmt nIn kI n portNames k args mc m = some st) :
    CallStmt nIn kI n portNames k args mc st := by
  unfold instStmt at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨outW, hout, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨argWs, hargs, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i hclk
  split at h
  · cases h
  rename_i hnd
  split at h
  · rename_i outP houts
    split at h
    · cases h
    rename_i hon
    split at h
    · cases h
    split at h
    · cases h
    cases h
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_or,
      Bool.not_eq_true, List.contains_iff_mem] at hnd
    refine ⟨outW, argWs, outP, _, hout, hargs, houts, by simpa using hclk, ?_, ?_, ?_, ?_, rfl⟩
    · simpa using hlen
    · simpa using hnd.1
    · simpa using hnd.2
    · simpa using hon
  · cases h

/-- **Every call is an instance statement of the closed module.** -/
theorem closeInsts_calls {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    ∀ k, k < insts.length → ∃ args child mc, insts[k]? = some args ∧ children[k]? = some child ∧
      moduleByName d.modules child.1.name = some mc ∧
      ∃ st ∈ m.body, CallStmt nIn kI n portNames k args mc st := by
  intro k hk
  unfold closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨stmts, hstmts, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outWs, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hperm⟩, _⟩, _⟩, _⟩, _⟩ := hc
    cases h
    -- the `k`-th statement of `stmts`
    obtain ⟨_, hget⟩ := mapM_some _ _ stmts hstmts
    obtain ⟨st, hst, hstk⟩ := hget k (by simpa using hk)
    simp only [List.getElem_range, Option.bind_eq_bind] at hst
    obtain ⟨args, hargs, hst⟩ := Option.bind_eq_some_iff.mp hst
    obtain ⟨child, hchild, hst⟩ := Option.bind_eq_some_iff.mp hst
    obtain ⟨mc, hmc, hst⟩ := Option.bind_eq_some_iff.mp hst
    refine ⟨args, child, mc, hargs, hchild, hmc, st, ?_, instStmt_some hst⟩
    -- `st` is in the appended statements, hence in the permuted body
    have hmem : st ∈ m₀.body ++ stmts := List.mem_append_right _ (List.mem_of_getElem? hstk)
    exact (isPermOf_sound hperm).mem_iff.mp hmem
  · cases h

/-- **Every instance statement of the closed module is a call** (or was in
the module before). -/
theorem closeInsts_insts {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    ∀ st ∈ m.body, isInst st = true → st ∈ m₀.body ∨
      ∃ k args child mc, insts[k]? = some args ∧ children[k]? = some child ∧
        moduleByName d.modules child.1.name = some mc ∧ CallStmt nIn kI n portNames k args mc st := by
  intro st hst hinst
  unfold closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨stmts, hstmts, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outWs, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hperm⟩, _⟩, _⟩, _⟩, _⟩ := hc
    cases h
    have hmem : st ∈ m₀.body ++ stmts := (isPermOf_sound hperm).mem_iff.mpr hst
    rcases List.mem_append.mp hmem with h0 | hs
    · exact Or.inl h0
    · right
      obtain ⟨hlen, hget⟩ := mapM_some _ _ stmts hstmts
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
      obtain ⟨st', hst', hstk⟩ := hget k (by rw [← hlen]; exact hk)
      rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hstk
      subst hstk
      simp only [List.getElem_range, Option.bind_eq_bind] at hst'
      obtain ⟨args, hargs, hst'⟩ := Option.bind_eq_some_iff.mp hst'
      obtain ⟨child, hchild, hst'⟩ := Option.bind_eq_some_iff.mp hst'
      obtain ⟨mc, hmc, hst'⟩ := Option.bind_eq_some_iff.mp hst'
      exact ⟨k, args, child, mc, hargs, hchild, hmc, instStmt_some hst'⟩
  · cases h

theorem moduleByName_name {ms : List Module} {nm : String} {mc : Module}
    (h : moduleByName ms nm = some mc) : mc.name = nm := by
  unfold moduleByName at h
  simpa using List.find?_some h

/-! ### Bodies without instances -/

/-- An assignment or a register. -/
def plainStmt : Stmt → Bool
  | .assign .. => true
  | .register .. => true
  | _ => false

theorem bodyOuts_plain (f : String → Option Module) :
    ∀ body : List Stmt, body.all plainStmt = true → bodyOuts f body = []
  | [], _ => rfl
  | st :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [bodyOuts, bodyOuts_plain f rest h.2, List.append_nil]
    cases st <;> simp_all [plainStmt, stmtOuts]

/-- A body of assignments and registers is in the linked order. -/
theorem linkedOk_plain (f : String → Option Module) :
    ∀ body : List Stmt, body.all plainStmt = true → linkedOk f body = true
  | [], _ => rfl
  | st :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := linkedOk_plain f rest h.2
    cases st with
    | assign l r => simp [linkedOk, bodyOuts_plain f rest h.2, ih]
    | register o c rk i iv => simp [linkedOk, ih]
    | _ => simp [plainStmt] at h

theorem nextAssigns_plain (w : String) :
    ∀ (ps : List Port) (fs : List SlotField), (nextAssigns w ps fs).all plainStmt = true
  | p :: ps, f :: fs => by simp [nextAssigns, plainStmt, nextAssigns_plain w ps fs]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem registers_plain (rk : Sparkle.IR.Type.ResetKind) :
    ∀ (ps : List Port) (fs : List SlotField), (registers rk ps fs).all plainStmt = true
  | p :: ps, f :: fs => by simp [registers, plainStmt, registers_plain rk ps fs]
  | [], _ => rfl
  | _ :: _, [] => rfl

/-- Closing a body of assignments gives a body of assignments and registers. -/
theorem closeMachine_plain (lay : Layout) (t : Module) (h : t.body.all Sparkle.IR.RegDedup.isAssign = true) :
    (closeMachine lay t).body.all plainStmt = true := by
  have ha : ∀ st ∈ t.body, plainStmt st = true := by
    intro st hs
    have := List.all_eq_true.mp h st hs
    cases st <;> simp_all [Sparkle.IR.RegDedup.isAssign, plainStmt]
  unfold closeMachine
  split
  · exact List.all_eq_true.mpr ha
  · simp only [List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨List.all_eq_true.mpr fun st hs => ha st (List.dropLast_subset _ hs),
      nextAssigns_plain _ _ _⟩, registers_plain _ _ _⟩, ?_⟩
    simp [outAssigns, plainStmt]

/-- **`closeInsts` keeps every cycle.** -/
theorem stepModule_of_closeInsts {nIn kI n : Nat} {portNames : List String}
    {insts : List (List Nat)} {children : List (Module × Design)} {m₀ : Module} {d₀ : Design}
    {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d))
    (we : WEnv) (env0 : Env) (mems : MEnv) :
    stepModule we m.body env0 mems = stepModule we m₀.body env0 mems := by
  obtain ⟨_, _, _, L, hL, hperm, hwo, hwo', hseq, hmem, _, _⟩ := closeInsts_some h
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
