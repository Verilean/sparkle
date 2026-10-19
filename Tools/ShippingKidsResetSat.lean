import Tools.ShippingKidsTyped
import Tools.ShippingGuardsSound
import Tools.ShippingGatePorts
import Tools.ShippingMachineShipsHier
import Tools.ShippingDesignSVBounds
-- BUILT as written: ks1 (exit 0, 657 jobs; round par/kids). Writing-time guesses are marked `-- (writing-time guess, accepted by build ks1: …)`.

/-! # The children's reset and the depth-0 children bound are satisfiable TOGETHER (round par/kids)

The head `Tools.ShippingNoPortsTyped.machine_design_noPortsTB` (and its generated instances
`<p>_designClosedB`) take, among the conclusion's run hypotheses, with `Reset := Reset1`:

* `Reset1 raw D kids` (`Tools.ShippingMachineShipsHier.Reset1`): memories zero, `out_rdata` zero,
  each instance's registers (of the module `moduleByName D.modules` gives for the instance's module
  name in `raw.body`) at their reset values `init.toNat`;
* `∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
  childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname)`, at depth
  `0` the bound `Bounded (weS gc) (kids iname).st`.

This file shows the two are satisfied by ONE explicit `kids`.

## 1. Generic, from explicit facts (no run)

`kidsInit raw D` — `kids iname` has, at a name `r`, the reset value of the FIRST register `r` of the
module of the FIRST instance named `iname` in `raw.body`, else `0`; memories `0`.
`kidsInit_sat` needs exactly:

* `hInst` — an instance name determines its module name in `raw.body` (from
  `(instNames raw.body).Nodup`, `instAgree_of_nodup`; the run gives `RunFacts.ndB` on `b.body`, and
  `b.body = raw.body` is `core_kids_factsMT`'s second conjunct);
* `hRegAg` — in each instantiated child, registers of the same name have the same `init.toNat`;
* `hRd` — in each instantiated child, a register named `out_rdata` has `init.toNat = 0`;
* `hW` — in each instantiated child, a register's `init.toNat < 2 ^ weS mc r` (its EMITTED width);
* `hO` — the instance statements of the shipped module `o` are statements of `raw.body`
  (`inst_checkedOptimize_sub` with `b.body = raw.body`, for `o = checkedOptimize b`).

None of `hRegAg`, `hRd`, `hW` can be dropped in general (counterexamples, each with ONE child
instantiated once): a child with `register "x" … 0` and `register "x" … 1` (Reset1 forces both
values); a child with `register "out_rdata" … 1` (Reset1 forces `0` and `1`); a child with
`register "x" … 5` and `x` declared 1 bit wide (`weS = 1`: Reset1 forces `5`, the bound `< 2`).
`hInst` cannot be dropped either: two instances named `i` of modules with a register `x` of
reset values `0` and `1`.

## 2. Register-free children (the collision parents)

`kidsZero` (every state `0`) satisfies both whenever every instantiated child has NO register
statement (`kidsZero_sat`, premise `hNR`). The four collision parents' children are the built
memory module (`memModule_noRegs`, its body is one memory and one assignment) and a gate child
(`noRegs_of_gate`, `GateChildPorts.typed`: every statement is an assignment). At run level,
`core_kidsSatMT` derives `hNR` from the core run (`core_callStmtMT`: each instance's module is the
first component of a `KidT` kid; `core_kids_factsMT`: `b.body = raw.body`) and ONE fact per call
entry, `NoRegs y.1` for every `KidT` kid `y`.

No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingKidsResetSat
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.AST (Module)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingDesignSV (weS)
open Tools.ShippingDesignSVBounds (InvN)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineShipsHier (Reset1)

/-! ## Small list facts -/

/-- The reset value of the first register named `r` of a body (`0` if none). -/
def regInitOf : List Stmt → String → Nat
  | [], _ => 0
  | .register o _ _ _ init :: rest, r => if o = r then init.toNat else regInitOf rest r
  | _ :: rest, r => regInitOf rest r

/-- The module name of the first instance named `n` of a body. -/
def instModOf : List Stmt → String → Option String
  | [], _ => none
  | .inst mn i _ :: rest, n => if i = n then some mn else instModOf rest n
  | _ :: rest, n => instModOf rest n

theorem mem_of_mem_cons_ne {x st : Stmt} {rest : List Stmt} (h : x ∈ st :: rest) (hne : x ≠ st) :
    x ∈ rest := by
  rcases List.mem_cons.mp h with e | e
  · exact absurd e hne
  · exact e

theorem regInitOf_cons_other (st : Stmt) (rest : List Stmt) (r : String)
    (h : ∀ o c rs inp init, st ≠ Stmt.register o c rs inp init) :
    regInitOf (st :: rest) r = regInitOf rest r := by
  cases st with
  | register o c rs inp init => exact absurd rfl (h o c rs inp init)
  -- (writing-time guess, accepted by build ks1: the wildcard equation holds by `rfl` on a non-register head)
  | assign => first | rfl | simp [regInitOf]
  | memory => first | rfl | simp [regInitOf]
  | inst => first | rfl | simp [regInitOf]

theorem instModOf_cons_other (st : Stmt) (rest : List Stmt) (n : String)
    (h : ∀ mn i c, st ≠ Stmt.inst mn i c) :
    instModOf (st :: rest) n = instModOf rest n := by
  cases st with
  | inst mn i c => exact absurd rfl (h mn i c)
  -- (writing-time guess, accepted by build ks1: the wildcard equation holds by `rfl` on a non-instance head)
  | assign => first | rfl | simp [instModOf]
  | register => first | rfl | simp [instModOf]
  | memory => first | rfl | simp [instModOf]

/-- If every register named `r` has the reset value `init` (as a `Nat`) and one exists,
`regInitOf` reads it. -/
theorem regInitOf_of_mem (r : String) (init : Int) : ∀ (body : List Stmt),
    (∀ c' rs' inp' (init' : Int), Stmt.register r c' rs' inp' init' ∈ body →
      init'.toNat = init.toNat) →
    (∃ c rs inp, Stmt.register r c rs inp init ∈ body) → regInitOf body r = init.toNat := by
  intro body
  induction body with
  | nil =>
    intro _ h
    obtain ⟨_, _, _, h⟩ := h
    cases h
  | cons st rest ih =>
    intro hag hex
    obtain ⟨c, rs, inp, h⟩ := hex
    have hag' : ∀ c' rs' inp' (init' : Int), Stmt.register r c' rs' inp' init' ∈ rest →
        init'.toNat = init.toNat :=
      fun c' rs' inp' init' hm => hag c' rs' inp' init' (List.mem_cons_of_mem _ hm)
    cases st with
    | register o c0 rs0 inp0 init0 =>
      by_cases ho : o = r
      · have e : regInitOf (Stmt.register o c0 rs0 inp0 init0 :: rest) r = init0.toNat := by
          simp [regInitOf, ho]
        rw [e]
        have hm : Stmt.register r c0 rs0 inp0 init0 ∈ Stmt.register o c0 rs0 inp0 init0 :: rest := by
          rw [ho]
          exact List.mem_cons_self
        exact hag c0 rs0 inp0 init0 hm
      · have e : regInitOf (Stmt.register o c0 rs0 inp0 init0 :: rest) r = regInitOf rest r := by
          simp [regInitOf, ho]
        rw [e]
        refine ih hag' ⟨c, rs, inp, ?_⟩
        rcases List.mem_cons.mp h with e1 | e1
        · exact absurd (Stmt.register.inj e1).1.symm ho
        · exact e1
    | assign a b =>
      rw [regInitOf_cons_other _ rest r (by intro _ _ _ _ _ e; cases e)]
      exact ih hag' ⟨c, rs, inp, mem_of_mem_cons_ne h (by intro e; cases e)⟩
    | memory nm aw dw cl wa wd wen ra rd cr ew er =>
      rw [regInitOf_cons_other _ rest r (by intro _ _ _ _ _ e; cases e)]
      exact ih hag' ⟨c, rs, inp, mem_of_mem_cons_ne h (by intro e; cases e)⟩
    | inst mn i cs =>
      rw [regInitOf_cons_other _ rest r (by intro _ _ _ _ _ e; cases e)]
      exact ih hag' ⟨c, rs, inp, mem_of_mem_cons_ne h (by intro e; cases e)⟩

/-- `regInitOf` is `0` or the reset value of a register of that name. -/
theorem regInitOf_cases (r : String) : ∀ (body : List Stmt),
    regInitOf body r = 0 ∨ ∃ c rs inp init, Stmt.register r c rs inp init ∈ body ∧
      regInitOf body r = init.toNat := by
  intro body
  induction body with
  | nil => exact Or.inl rfl
  | cons st rest ih =>
    cases st with
    | register o c0 rs0 inp0 init0 =>
      by_cases ho : o = r
      · have e : regInitOf (Stmt.register o c0 rs0 inp0 init0 :: rest) r = init0.toNat := by
          simp [regInitOf, ho]
        have hm : Stmt.register r c0 rs0 inp0 init0 ∈ Stmt.register o c0 rs0 inp0 init0 :: rest := by
          rw [ho]
          exact List.mem_cons_self
        exact Or.inr ⟨c0, rs0, inp0, init0, hm, e⟩
      · have e : regInitOf (Stmt.register o c0 rs0 inp0 init0 :: rest) r = regInitOf rest r := by
          simp [regInitOf, ho]
        rw [e]
        rcases ih with h | ⟨c, rs, inp, init, hm, he⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, rs, inp, init, List.mem_cons_of_mem _ hm, he⟩
    | assign a b =>
      rw [regInitOf_cons_other _ rest r (by intro _ _ _ _ _ e; cases e)]
      rcases ih with h | ⟨c, rs, inp, init, hm, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, rs, inp, init, List.mem_cons_of_mem _ hm, he⟩
    | memory nm aw dw cl wa wd wen ra rd cr ew er =>
      rw [regInitOf_cons_other _ rest r (by intro _ _ _ _ _ e; cases e)]
      rcases ih with h | ⟨c, rs, inp, init, hm, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, rs, inp, init, List.mem_cons_of_mem _ hm, he⟩
    | inst mn i cs =>
      rw [regInitOf_cons_other _ rest r (by intro _ _ _ _ _ e; cases e)]
      rcases ih with h | ⟨c, rs, inp, init, hm, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, rs, inp, init, List.mem_cons_of_mem _ hm, he⟩

/-- If every instance named `n` has module name `mn` and one exists, `instModOf` reads it. -/
theorem instModOf_of_mem (n mn : String) : ∀ (body : List Stmt),
    (∀ mn' c', Stmt.inst mn' n c' ∈ body → mn' = mn) →
    (∃ c, Stmt.inst mn n c ∈ body) → instModOf body n = some mn := by
  intro body
  induction body with
  | nil =>
    intro _ h
    obtain ⟨_, h⟩ := h
    cases h
  | cons st rest ih =>
    intro hag hex
    obtain ⟨c, h⟩ := hex
    have hag' : ∀ mn' c', Stmt.inst mn' n c' ∈ rest → mn' = mn :=
      fun mn' c' hm => hag mn' c' (List.mem_cons_of_mem _ hm)
    cases st with
    | inst m0 i0 c0 =>
      by_cases hi : i0 = n
      · have e : instModOf (Stmt.inst m0 i0 c0 :: rest) n = some m0 := by
          simp [instModOf, hi]
        have hm : Stmt.inst m0 n c0 ∈ Stmt.inst m0 i0 c0 :: rest := by
          rw [hi]
          exact List.mem_cons_self
        rw [e, hag m0 c0 hm]
      · have e : instModOf (Stmt.inst m0 i0 c0 :: rest) n = instModOf rest n := by
          simp [instModOf, hi]
        rw [e]
        refine ih hag' ⟨c, ?_⟩
        rcases List.mem_cons.mp h with e1 | e1
        · exact absurd (Stmt.inst.inj e1).2.1.symm hi
        · exact e1
    | assign a b =>
      rw [instModOf_cons_other _ rest n (by intro _ _ _ e; cases e)]
      exact ih hag' ⟨c, mem_of_mem_cons_ne h (by intro e; cases e)⟩
    | register o cl rs inp init =>
      rw [instModOf_cons_other _ rest n (by intro _ _ _ e; cases e)]
      exact ih hag' ⟨c, mem_of_mem_cons_ne h (by intro e; cases e)⟩
    | memory nm aw dw cl wa wd wen ra rd cr ew er =>
      rw [instModOf_cons_other _ rest n (by intro _ _ _ e; cases e)]
      exact ih hag' ⟨c, mem_of_mem_cons_ne h (by intro e; cases e)⟩

/-- What `instModOf` reads is an instance of the body. -/
theorem instModOf_mem (n mn : String) : ∀ (body : List Stmt),
    instModOf body n = some mn → ∃ c, Stmt.inst mn n c ∈ body := by
  intro body
  induction body with
  | nil =>
    intro h
    -- (writing-time guess, accepted by build ks1: `instModOf [] n` reduces to `none`)
    first | cases h | simp [instModOf] at h
  | cons st rest ih =>
    intro h
    cases st with
    | inst m0 i0 c0 =>
      by_cases hi : i0 = n
      · have e : instModOf (Stmt.inst m0 i0 c0 :: rest) n = some m0 := by
          simp [instModOf, hi]
        rw [e] at h
        have hm : m0 = mn := Option.some.inj h
        refine ⟨c0, ?_⟩
        rw [← hm, ← hi]
        exact List.mem_cons_self
      · have e : instModOf (Stmt.inst m0 i0 c0 :: rest) n = instModOf rest n := by
          simp [instModOf, hi]
        rw [e] at h
        obtain ⟨c, hc⟩ := ih h
        exact ⟨c, List.mem_cons_of_mem _ hc⟩
    | assign a b =>
      rw [instModOf_cons_other _ rest n (by intro _ _ _ e; cases e)] at h
      obtain ⟨c, hc⟩ := ih h
      exact ⟨c, List.mem_cons_of_mem _ hc⟩
    | register o cl rs inp init =>
      rw [instModOf_cons_other _ rest n (by intro _ _ _ e; cases e)] at h
      obtain ⟨c, hc⟩ := ih h
      exact ⟨c, List.mem_cons_of_mem _ hc⟩
    | memory nm aw dw cl wa wd wen ra rd cr ew er =>
      rw [instModOf_cons_other _ rest n (by intro _ _ _ e; cases e)] at h
      obtain ⟨c, hc⟩ := ih h
      exact ⟨c, List.mem_cons_of_mem _ hc⟩

/-- **Distinct instance names: an instance name determines its module name.** -/
theorem instAgree_of_nodup : ∀ (body : List Stmt), (instNames body).Nodup →
    ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ body → Stmt.inst mn' i c' ∈ body → mn = mn' := by
  intro body
  induction body with
  | nil => intro _ _ _ _ _ _ h; cases h
  | cons st rest ih =>
    intro hnd mn i c mn' c' h1 h2
    cases st with
    | inst m0 i0 c0 =>
      simp only [instNames, List.nodup_cons] at hnd
      obtain ⟨hni, hnd'⟩ := hnd
      rcases List.mem_cons.mp h1 with e1 | e1 <;> rcases List.mem_cons.mp h2 with e2 | e2
      · exact (Stmt.inst.inj e1).1.trans (Stmt.inst.inj e2).1.symm
      · have hi : i = i0 := (Stmt.inst.inj e1).2.1
        rw [hi] at e2
        exact absurd (Tools.ShippingHierState.mem_instNames rest mn' i0 c' e2) hni
      · have hi : i = i0 := (Stmt.inst.inj e2).2.1
        rw [hi] at e1
        exact absurd (Tools.ShippingHierState.mem_instNames rest mn i0 c e1) hni
      · exact ih hnd' mn i c mn' c' e1 e2
    -- (writing-time guess, accepted by build ks1: `instNames (st :: rest)` unfolds to `instNames rest` by `exact` for a non-instance head)
    | assign a b =>
      exact ih hnd mn i c mn' c' (mem_of_mem_cons_ne h1 (by intro e; cases e))
        (mem_of_mem_cons_ne h2 (by intro e; cases e))
    | register o cl rs inp init =>
      exact ih hnd mn i c mn' c' (mem_of_mem_cons_ne h1 (by intro e; cases e))
        (mem_of_mem_cons_ne h2 (by intro e; cases e))
    | memory nm aw dw cl wa wd wen ra rd cr ew er =>
      exact ih hnd mn i c mn' c' (mem_of_mem_cons_ne h1 (by intro e; cases e))
        (mem_of_mem_cons_ne h2 (by intro e; cases e))

/-- `childMap` reads `moduleByName`. -/
theorem moduleByName_of_childMap {ms : List Module} {mn : String} {gc : Module} {gcwe : WEnv}
    (h : childMap ms mn = some (gc, gcwe)) : Sparkle.IR.Machine.moduleByName ms mn = some gc := by
  cases hm : Sparkle.IR.Machine.moduleByName ms mn with
  | none =>
    -- (writing-time guess, accepted by build ks1: as in `core_typedRunMT`, `childMap` is the `Option.map` of `moduleByName` by defeq)
    have hC : childMap ms mn = none :=
      congrArg (fun o : Option Module => o.map fun g => (g, declWidth g)) hm
    rw [hC] at h
    cases h
  | some g =>
    have hC : childMap ms mn = some (g, declWidth g) :=
      congrArg (fun o : Option Module => o.map fun g => (g, declWidth g)) hm
    rw [hC] at h
    have e : (g, declWidth g) = (gc, gcwe) := Option.some.inj h
    exact congrArg some (Prod.mk.inj e).1

/-- **The shipped module's instance statements are the full entry's** (all three branches of
`checkedOptimize`, as in `machine_design_noPortsTB`'s proof). -/
theorem inst_checkedOptimize_sub {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
      Stmt.inst mn iname conns ∈ b.body := by
  intro mn iname conns h
  by_cases hbind : Sparkle.IR.RefineCheck.hierBinds b = true
  · rw [Tools.ShippingGuardsSound.checkedOptimize_binding hbind] at h
    by_cases hacc : Sparkle.IR.RefineCheck.hierRefineCheck b
        (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
    · rw [if_pos hacc] at h
      exact (Tools.ShippingChecksDerived2.hierRefineCheck_inst_iff hacc mn iname conns).mp h
    · rw [if_neg hacc] at h
      exact h
  · have hb0 : Sparkle.IR.RefineCheck.hierBinds b = false := by simpa using hbind
    rw [Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate hb0] at h
    exact h

/-! ## 1. The generic statement: `kids` from the children's reset values -/

/-- The module of the first instance named `n` of `raw.body`, as `D` defines it. -/
def instModule (raw : Module) (D : Design) (n : String) : Option Module :=
  (instModOf raw.body n).bind (Sparkle.IR.Machine.moduleByName D.modules)

/-- A state from a module's reset values (`0` without a module). -/
def resetStOf : Option Module → String → Nat
  | some mc, r => regInitOf mc.body r
  | none, _ => 0

/-- **The explicit children's states**: each instance's registers at their reset values, every
other name `0`, memories `0`. -/
def kidsInit (raw : Module) (D : Design) : String → KidState :=
  fun n => ⟨resetStOf (instModule raw D n), fun _ _ => 0⟩

theorem instModule_some {raw : Module} {D : Design} {n : String} {mc : Module}
    (h : instModule raw D n = some mc) :
    ∃ mn, instModOf raw.body n = some mn ∧ Sparkle.IR.Machine.moduleByName D.modules mn = some mc := by
  unfold instModule at h
  cases h1 : instModOf raw.body n with
  | none =>
    rw [h1] at h
    -- (writing-time guess, accepted by build ks1: `Option.bind none _` reduces to `none`)
    first | cases h | simp at h
  | some mn =>
    rw [h1] at h
    exact ⟨mn, rfl, h⟩

set_option maxHeartbeats 1000000 in
/-- **Generic: the reset and the depth-0 children bound hold together** for `kidsInit raw D`, from
explicit facts about `raw` and `D` (no run). `o` is the shipped module (`checkedOptimize b`). -/
theorem kidsInit_sat {raw : Module} {D : Design} {o : Module}
    (hInst : ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ raw.body → Stmt.inst mn' i c' ∈ raw.body → mn = mn')
    (hRegAg : ∀ mn i conns mc, Stmt.inst mn i conns ∈ raw.body →
      Sparkle.IR.Machine.moduleByName D.modules mn = some mc →
      ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
        Stmt.register r c rs inp init ∈ mc.body → Stmt.register r c' rs' inp' init' ∈ mc.body →
        init.toNat = init'.toNat)
    (hRd : ∀ mn i conns mc, Stmt.inst mn i conns ∈ raw.body →
      Sparkle.IR.Machine.moduleByName D.modules mn = some mc →
      ∀ c rs inp (init : Int), Stmt.register "out_rdata" c rs inp init ∈ mc.body → init.toNat = 0)
    (hW : ∀ mn i conns mc, Stmt.inst mn i conns ∈ raw.body →
      Sparkle.IR.Machine.moduleByName D.modules mn = some mc →
      ∀ r c rs inp (init : Int), Stmt.register r c rs inp init ∈ mc.body → init.toNat < 2 ^ weS mc r)
    (hO : ∀ mn i conns, Stmt.inst mn i conns ∈ o.body → Stmt.inst mn i conns ∈ raw.body) :
    Reset1 raw D (kidsInit raw D) ∧
      ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
        childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kidsInit raw D iname) := by
  have key : ∀ mn i conns mc, Stmt.inst mn i conns ∈ raw.body →
      Sparkle.IR.Machine.moduleByName D.modules mn = some mc →
      ∀ r, (kidsInit raw D i).st r = regInitOf mc.body r := by
    intro mn i conns mc hm hmc r
    have h1 : instModOf raw.body i = some mn :=
      instModOf_of_mem i mn raw.body (fun mn' c' hm' => hInst mn' i c' mn conns hm' hm) ⟨conns, hm⟩
    have h2 : instModule raw D i = some mc := by
      unfold instModule
      rw [h1]
      exact hmc
    show resetStOf (instModule raw D i) r = regInitOf mc.body r
    rw [h2]
    rfl
  refine ⟨?_, ?_⟩
  · unfold Reset1
    refine ⟨fun _ _ _ => rfl, ?_, ?_⟩
    · -- `out_rdata`
      intro i
      show resetStOf (instModule raw D i) "out_rdata" = 0
      cases hI : instModule raw D i with
      | none => rfl
      | some mc =>
        obtain ⟨mn, h1, hmc⟩ := instModule_some hI
        obtain ⟨conns, hm⟩ := instModOf_mem i mn raw.body h1
        show regInitOf mc.body "out_rdata" = 0
        rcases regInitOf_cases "out_rdata" mc.body with h0 | ⟨c, rs, inp, init, hr, he⟩
        · exact h0
        · rw [he]
          exact hRd mn i conns mc hm hmc c rs inp init hr
    · -- the registers at their reset values
      rintro i mc ⟨conns, hm⟩ hmc r c rs inp init hr
      rw [key mc.name i conns mc hm hmc r]
      exact regInitOf_of_mem r init mc.body
        (fun c' rs' inp' init' hm' => hRegAg mc.name i conns mc hm hmc r c' rs' inp' init' c rs inp init
          hm' hr)
        ⟨c, rs, inp, hr⟩
  · -- the depth-0 bound
    intro mn iname conns gc gcwe hm hc
    have hmr := hO mn iname conns hm
    have hmc := moduleByName_of_childMap hc
    -- (writing-time guess, accepted by build ks1: `InvN _ 0 gc ks` unfolds to `Bounded (weS gc) ks.st` by `show`, as in TB)
    show Bounded (weS gc) (kidsInit raw D iname).st
    intro x
    show (kidsInit raw D iname).st x < 2 ^ weS gc x
    rw [key mn iname conns gc hmr hmc x]
    rcases regInitOf_cases x gc.body with h0 | ⟨c, rs, inp, init, hr, he⟩
    · rw [h0]
      exact Nat.two_pow_pos _
    · rw [he]
      exact hW mn iname conns gc hmr hmc x c rs inp init hr

/-! ## 2. Register-free children -/

/-- A module with no register statement. -/
def NoRegs (m : Module) : Prop :=
  ∀ r c rs inp (init : Int), Stmt.register r c rs inp init ∉ m.body

/-- Every state `0`, every memory `0`. -/
def kidsZero : String → KidState := fun _ => ⟨fun _ => 0, fun _ _ => 0⟩

/-- **Register-free children: the reset and the depth-0 bound hold together** for `kidsZero`. The
bound needs nothing (`0 < 2 ^ w`); the reset's register clause is vacuous. -/
theorem kidsZero_sat {raw : Module} {D : Design} {o : Module}
    (hNR : ∀ mn iname conns, Stmt.inst mn iname conns ∈ raw.body →
      ∀ mc, Sparkle.IR.Machine.moduleByName D.modules mn = some mc → NoRegs mc) :
    Reset1 raw D kidsZero ∧
      ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
        childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kidsZero iname) := by
  refine ⟨?_, ?_⟩
  · unfold Reset1
    refine ⟨fun _ _ _ => rfl, fun _ => rfl, ?_⟩
    rintro iname mc ⟨conns, hm⟩ hmc r c rs inp init hr
    exact absurd hr (hNR mc.name iname conns hm mc hmc r c rs inp init)
  · intro mn iname conns gc gcwe _ _
    -- (writing-time guess, accepted by build ks1: `InvN _ 0 gc ks` unfolds to `Bounded (weS gc) ks.st` by `show`)
    show Bounded (weS gc) (kidsZero iname).st
    intro x
    have h0 : (kidsZero iname).st x = 0 := rfl
    show (kidsZero iname).st x < 2 ^ weS gc x
    rw [h0]
    exact Nat.two_pow_pos _

/-- The built memory module has no register. -/
theorem memModule_noRegs (cb : Bool) (aw dw : Nat) :
    NoRegs (Sparkle.Compiler.MachMemory.memModule cb aw dw).1 := by
  intro r c rs inp init h
  have hb : (Sparkle.Compiler.MachMemory.memModule cb aw dw).1.body =
      [.memory "mem" aw dw "clk" (.ref "wa") (.ref "wd") (.ref "we") (.ref "ra") "out_rdata" cb [] [],
        .assign "out" (.ref "out_rdata")] := rfl
  rw [hb] at h
  rcases List.mem_cons.mp h with e | h
  · cases e
  · rcases List.mem_cons.mp h with e | h
    · cases e
    · cases h

/-- A gate child has no register: every statement is an assignment (`GateChildPorts.typed`). -/
theorem noRegs_of_gate {c bs w} {m : Module} (h : Tools.ShippingGatePorts.GateChildPorts c bs w m) : NoRegs m := by
  intro r cl rs inp init hr
  -- (writing-time guess, accepted by build ks1: `TypedStmts` applies to a statement and its membership directly)
  obtain ⟨l, e, n, he, -⟩ := h.typed _ hr
  cases he

/-! ## The run: `NoRegs` of every instantiated child from the core run and one fact per kid -/

section Core
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Compiler.Elab Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto
open Tools.ShippingChildInv
open Sparkle.IR.RefineCheck (mergeChecked)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

set_option maxHeartbeats 4000000 in
/-- **From the core run: every child an instance of the full entry's module names is the first
component of a `KidT` kid.** With `NoRegs` per kid, `hNR` of `kidsZero_sat` on `raw`. -/
theorem core_noRegsMT {c : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 y → NoRegs y.1)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ M.body →
      ∀ mc, Sparkle.IR.Machine.moduleByName D.modules mn = some mc → NoRegs mc := by
  have hbB : b.body = M.body :=
    (Tools.ShippingMemKid.core_kids_factsMT d ok hbody hC hslots hdomB hins outTy hfne hB
      hcore hpost entry closes).2.1
  have hstm := Tools.ShippingMemKid.core_callStmtMT d ok hbody hC hslots hdomB hins hfne outTy
    hB hcore hpost entry closes
  intro mn iname conns hm mc hmc
  obtain ⟨mc', hmc', ⟨k, hk, y, hre, hmcy⟩, -⟩ := hstm mn iname conns (by rw [hbB]; exact hm)
  have e : mc = mc' := Option.some.inj (hmc.symm.trans hmc')
  rw [e, hmcy]
  exact hkidR k hk y hre

set_option maxHeartbeats 4000000 in
/-- **The run-level statement**: from the core run (any `raw`/`M`, `D` it returns, as
`core_typedRunMT`) and `NoRegs` per `KidT` kid, ONE `kids` satisfies the head's `Reset1` and its
depth-0 children bound. -/
theorem core_kidsSatMT {c : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 y → NoRegs y.1)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∃ kids : String → KT 0, Reset1 M D kids ∧
      ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body →
        childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname) :=
  -- (writing-time guess, accepted by build ks1: `String → KidState` is accepted at `String → KT 0`, `KT 0` unfolding to
  -- `KidState`, as the head's `Reset := Reset1` instance is)
  ⟨kidsZero, kidsZero_sat (o := Sparkle.IR.OptCheck.checkedOptimize b)
    (core_noRegsMT d ok hbody hC hslots hdomB hins hfne outTy hkidR hB hcore hpost entry closes)⟩

end Core

end Tools.ShippingKidsResetSat
