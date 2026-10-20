import Tools.ShippingSettledSoundness

/-! Zero-delay two-state operational semantics for the emitted combinational
fragment. A delta round reads every RHS in the old environment and commits
all targets simultaneously. Undriven values are fixed. Delta rounds are not
Signal clock cycles and do not model a particular simulator's event queue.
-/
namespace Tools.ShippingDeltaSemantics
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.SVParser.SVSemantics Tools.ShippingSettledSoundness

/-- Every RHS reads `old`, including assignments appearing later in the list.
There are no intermediate writes visible within a round. -/
def DeltaStep (wof : String → Option Nat) (pairs : List CombStep) (old next : Env) : Prop :=
  (∀ step ∈ pairs, match step with
    | .assign l rhs => ∃ width value, wof l = some width ∧
        evalSV wof old width rhs = some value ∧ next l = mask width value
    | .reads .. => False) ∧
  ∀ x, x ∉ svTargets pairs → next x = old x

def DeltaTrace (wof : String → Option Nat) (pairs : List CombStep)
    (seed : Env) (trace : Nat → Env) : Prop :=
  trace 0 = seed ∧ ∀ k, DeltaStep wof pairs (trace k) (trace (k + 1))

/-- Stable operational states are exactly simultaneous-equation solutions.
No acyclicity or convergence premise is needed for this equivalence. -/
theorem delta_fixed_iff {wof pairs env} :
    DeltaStep wof pairs env env ↔ SVEquations wof pairs env := by
  exact ⟨And.left, fun h => ⟨h, fun _ _ => rfl⟩⟩

/-- The round semantics is insensitive to textual assignment order. -/
theorem delta_perm {wof pairs pairs' old next} (hp : pairs.Perm pairs') :
    DeltaStep wof pairs old next ↔ DeltaStep wof pairs' old next := by
  have ht : (svTargets pairs).Perm (svTargets pairs') := hp.flatMap_right _
  constructor
  · rintro ⟨he, hf⟩
    exact ⟨fun st hm => he st (hp.mem_iff.mpr hm),
      fun x hx => hf x (fun hm => hx (ht.mem_iff.mp hm))⟩
  · rintro ⟨he, hf⟩
    exact ⟨fun st hm => he st (hp.mem_iff.mp hm),
      fun x hx => hf x (fun hm => hx (ht.mem_iff.mpr hm))⟩

/-- Proof-side IR counterpart; the public operational relation above uses
only the emitted SV assignments and their declared widths. -/
def IRStep (we : WEnv) (body : List Stmt) (old next : Env) : Prop :=
  (∀ l r, .assign l r ∈ body → evalExpr we old r = some (next l)) ∧
  ExternalValues body old next

/-- A total witness function. The checker proof below discharges every
`getD` fallback: no failed evaluation is admitted as an operational step. -/
def irRound (we : WEnv) (old : Env) : List Stmt → Env
  | [] => old
  | .assign l r :: rest => fun x =>
      if x = l then (evalExpr we old r).getD 0 else irRound we old rest x
  | _ :: rest => irRound we old rest

private theorem written_assignment {body x} (ha : Acyclic body) (hx : x ∈ writesOf body) :
    ∃ r, .assign x r ∈ body := by
  induction ha with
  | nil => cases hx
  | @cons l r rest ht hr ha ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨r, by simp⟩
    · obtain ⟨r', hm⟩ := ih hx
      exact ⟨r', by simp [hm]⟩

private theorem assignment_written {body l r} (ha : Acyclic body)
    (hm : .assign l r ∈ body) : l ∈ writesOf body := by
  induction ha with
  | nil => cases hm
  | cons _ _ _ ih =>
    rcases List.mem_cons.mp hm with he | hm
    · cases he; simp [writes_cons]
    · exact List.mem_cons_of_mem _ (ih hm)

theorem irStep_unique {we body old a b} (ha : Acyclic body)
    (h₁ : IRStep we body old a) (h₂ : IRStep we body old b) : a = b := by
  funext x
  by_cases hx : x ∈ writesOf body
  · obtain ⟨r, hm⟩ := written_assignment ha hx
    exact Option.some.inj ((h₁.1 x r hm).symm.trans (h₂.1 x r hm))
  · exact (h₁.2 x hx).trans (h₂.2 x hx).symm

theorem irRound_spec {we wof body old} (ha : Acyclic body)
    (hc : assignsCheck wof we body = true) (hb : Bounded we old) :
    IRStep we body old (irRound we old body) ∧ Bounded we (irRound we old body) := by
  induction ha with
  | nil => exact ⟨⟨by simp, fun _ _ => rfl⟩, hb⟩
  | @cons l r rest ht hr ha ih =>
    simp only [assignsCheck, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨_, _⟩, hw⟩, hs⟩, hc⟩ := hc
    have hf := sf4Check_sound hs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (sf4_eval_isSome hf old)
    have hvb : v < 2 ^ we l := by simpa [hw] using sf4_bounded hf hb v hv
    obtain ⟨hir, hbound⟩ := ih hc
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro l' r' hm
      rcases List.mem_cons.mp hm with he | hm
      · cases he; simp [irRound, hv]
      · have hne : l' ≠ l := by
          intro he; subst l'; exact ht (assignment_written ha hm)
        simpa [irRound, hne] using hir.1 l' r' hm
    · intro x hx
      have hx' : x ≠ l ∧ x ∉ writesOf rest := by simpa [writes_cons] using hx
      simpa [irRound, hx'.1] using hir.2 x hx'.2
    · intro x
      by_cases hx : x = l
      · simpa [irRound, hx, hv] using hvb
      · simpa [irRound, hx] using hbound x

/-- Direct connection between one parallel IR round and one parallel SV
round. The old environment is bounded; no bound on `next` is assumed. -/
theorem step_emitted_iff {wof we body pairs old next}
    (ha : Acyclic body) (hc : assignsCheck wof we body = true)
    (he : emitAssigns wof body = some pairs) (hb : Bounded we old)
    (hw : ∀ x width, wof x = some width → old x < 2 ^ width) :
    DeltaStep wof pairs old next ↔ IRStep we body old next := by
  have heq : (∀ step ∈ pairs, match step with
      | .assign l rhs => ∃ width value, wof l = some width ∧
          evalSV wof old width rhs = some value ∧ next l = mask width value
      | .reads .. => False) ↔
      (∀ l r, .assign l r ∈ body → evalExpr we old r = some (next l)) := by
    induction ha generalizing pairs with
    | nil => simp [emitAssigns] at he; subst pairs; simp
    | @cons l r rest ht hr ha ih =>
      simp only [assignsCheck, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨_, hl⟩, hwidth⟩, hsf⟩, hc⟩ := hc
      simp only [emitAssigns, bind, Option.bind_eq_some_iff] at he
      obtain ⟨sv, hsv, tail, htail, heq⟩ := he
      cases heq
      have hf := sf4Check_sound hsf
      have hv := emit_sem_evalSV hf hb hw hsv
      rw [hwidth] at hv
      have ih := ih hc htail
      constructor
      · intro hs l' r' hm
        rcases List.mem_cons.mp hm with heq | hm
        · cases heq
          obtain ⟨width, value, hw', heval, heq⟩ := hs (.assign l sv) (by simp)
          rw [hl] at hw'; cases hw'
          rw [hv] at heval
          have hvb : value < 2 ^ we l := by simpa [hwidth] using sf4_bounded hf hb value heval
          have hn : next l = value := by simpa [mask, Nat.mod_eq_of_lt hvb] using heq
          simpa [hn] using heval
        · exact ih.mp (fun st hm => hs st (by simp [hm])) l' r' hm
      · intro hs st hm
        rcases List.mem_cons.mp hm with heq | hm
        · cases heq
          have hvb : next l < 2 ^ we l := by
            simpa [hwidth] using sf4_bounded hf hb (next l) (hs l r (by simp))
          exact ⟨we l, next l, hl, hv.trans (hs l r (by simp)),
            by simp [mask, Nat.mod_eq_of_lt hvb]⟩
        · exact ih.mpr (fun l r hm => hs l r (by simp [hm])) st hm
  exact and_congr heq (by simp only [emitted_targets ha he, ExternalValues])

/-- Structural convergence: each round fixes at least the next dependency
level. This is independent of widths, of the chosen initial internal values,
and of any particular expression operator semantics beyond read congruence. -/
theorem ir_converges {we body stable} {trace : Nat → Env}
    (ha : Acyclic body) (hs : IREquations we body stable)
    (step : ∀ k l r, .assign l r ∈ body →
      evalExpr we (trace k) r = some (trace (k + 1) l))
    (external : ∀ k x, x ∉ writesOf body → trace k x = stable x) :
    ∀ k, body.length ≤ k → trace k = stable := by
  induction ha generalizing trace with
  | nil => intro k _; exact funext (fun x => external k x (by simp [writesOf]))
  | @cons l r rest ht hr ha ih =>
    have head : ∀ k, trace (k + 1) l = stable l := by
      intro k
      have hv : evalExpr we (trace k) r = evalExpr we stable r :=
        evalExpr_congr _ _ _ _ (fun x hx => external k x (by
          have := hr x hx; simpa [writes_cons] using this))
      exact Option.some.inj ((step k l r (by simp)).symm.trans (hv.trans (hs l r (by simp))))
    have tail := ih (trace := fun k => trace (k + 1))
      (fun l r hm => hs l r (by simp [hm]))
      (fun k l r hm => step (k + 1) l r (by simp [hm]))
      (by
        intro k x hx
        by_cases he : x = l
        · subst x; exact head k
        · exact external (k + 1) x (by simp [writes_cons, he, hx]))
    intro k hk
    cases k with
    | zero => simp at hk
    | succ k => exact tail k (by simpa using hk)


/-- A constructive infinite trace witness, including rounds after settling. -/
def irTrace (we : WEnv) (body : List Stmt) (seed : Env) : Nat → Env
  | 0 => seed
  | k + 1 => irRound we (irTrace we body seed k) body

private theorem widthBound {wof : String → Option Nat} {we env} (hb : Bounded we env)
    (hw : ∀ x width, wof x = some width → we x = width) :
    ∀ x width, wof x = some width → env x < 2 ^ width := by
  intro x width hx
  simpa [hw x width hx] using hb x

theorem deltaTrace_exists {wof we body pairs seed}
    (ha : Acyclic body) (hc : assignsCheck wof we body = true)
    (he : emitAssigns wof body = some pairs)
    (hw : ∀ x width, wof x = some width → we x = width)
    (hb : Bounded we seed) :
    ∃ trace, DeltaTrace wof pairs seed trace := by
  have bound : ∀ k, Bounded we (irTrace we body seed k) := by
    intro k; induction k with
    | zero => exact hb
    | succ k ih => exact (irRound_spec ha hc ih).2
  refine ⟨irTrace we body seed, rfl, fun k => ?_⟩
  exact (step_emitted_iff ha hc he (bound k) (widthBound (bound k) hw)).mpr
    (irRound_spec ha hc (bound k)).1

theorem deltaTrace_bounded {wof we body pairs seed trace}
    (ha : Acyclic body) (hc : assignsCheck wof we body = true)
    (he : emitAssigns wof body = some pairs)
    (hw : ∀ x width, wof x = some width → we x = width)
    (hb : Bounded we seed) (ht : DeltaTrace wof pairs seed trace) :
    ∀ k, Bounded we (trace k) := by
  intro k; induction k with
  | zero => simpa [ht.1] using hb
  | succ k ih =>
    have hir := (step_emitted_iff ha hc he ih (widthBound ih hw)).mp (ht.2 k)
    have hs := irRound_spec ha hc ih
    rw [irStep_unique ha hir hs.1]
    exact hs.2

theorem deltaTrace_external {wof pairs seed trace}
    (ht : DeltaTrace wof pairs seed trace) :
    ∀ k x, x ∉ svTargets pairs → trace k x = seed x := by
  intro k; induction k with
  | zero => intro x _; rw [ht.1]
  | succ k ih => intro x hx; exact ((ht.2 k).2 x hx).trans (ih x hx)

theorem emitted_length {wof body pairs} (ha : Acyclic body)
    (he : emitAssigns wof body = some pairs) : pairs.length = body.length := by
  induction ha generalizing pairs with
  | nil => simp [emitAssigns] at he; subst pairs; rfl
  | cons ht hr ha ih =>
    simp only [emitAssigns, bind, Option.bind_eq_some_iff] at he
    obtain ⟨sv, _, tail, ht, he⟩ := he
    cases he
    simpa using ih ht

/-- Every legal delta trace converges in at most one round per assignment,
from any bounded internal initialization sharing the fixed external values.
The conclusion holds at ALL later rounds, not merely at one selected time. -/
theorem deltaTrace_converges {wof we body pairs initial stable seed trace}
    (ha : Acyclic body) (hc : assignsCheck wof we body = true)
    (he : emitAssigns wof body = some pairs)
    (hw : ∀ x width, wof x = some width → we x = width)
    (hs : SVSolution wof pairs initial stable) (hbs : Bounded we stable)
    (hb : Bounded we seed)
    (hseed : ∀ x, x ∉ svTargets pairs → seed x = initial x)
    (ht : DeltaTrace wof pairs seed trace) :
    ∀ k, pairs.length ≤ k → trace k = stable := by
  have bounds := deltaTrace_bounded ha hc he hw hb ht
  have hq := (equations_emitted_iff ha hc he hbs (widthBound hbs hw)).mp hs.1
  have step : ∀ k, IRStep we body (trace k) (trace (k + 1)) := fun k =>
    (step_emitted_iff ha hc he (bounds k) (widthBound (bounds k) hw)).mp (ht.2 k)
  have external : ∀ k x, x ∉ writesOf body → trace k x = stable x := by
    intro k x hx
    have hxp : x ∉ svTargets pairs := by simpa [emitted_targets ha he] using hx
    exact (deltaTrace_external ht k x hxp).trans ((hseed x hxp).trans (hs.2 x hxp).symm)
  intro k hk
  exact ir_converges ha hq (fun k => (step k).1) external k (by
    simpa [emitted_length ha he] using hk)


/-- The mask in every driven equation and the frame on every undriven name
bound the entire stable environment, not merely the observed output. -/
theorem solution_bounded {wof we pairs initial stable}
    (hw : ∀ x width, wof x = some width → we x = width)
    (hb : Bounded we initial) (hs : SVSolution wof pairs initial stable) :
    Bounded we stable := by
  intro x
  by_cases hx : x ∈ svTargets pairs
  · obtain ⟨st, hm, hx⟩ := List.mem_flatMap.mp hx
    cases st with
    | assign l rhs =>
      have he : x = l := by simpa using hx
      subst x
      obtain ⟨width, value, hl, _, hv⟩ := hs.1 _ hm
      rw [hw _ _ hl, hv]
      exact Nat.mod_lt _ (Nat.two_pow_pos width)
    | reads => exact False.elim (hs.1 _ hm)
  · rw [hs.2 x hx]; exact hb x

/-- Observation after settling, for all bounded internal initializations.
The stable state is shared by all traces. Existence is explicit, so universal
claims about traces cannot be vacuous because a round is stuck. -/
def SettlesTo (sv : SVModule) (pairs : List CombStep) (initial : Env) (value : Nat) : Prop :=
  ∃ stable,
    Bounded (fun x => (Tools.ShippingDeclWidths.astWidths sv x).getD 0) stable ∧
    SVSolution (Tools.ShippingDeclWidths.astWidths sv) pairs initial stable ∧
    Tools.ShippingModulePrintSoundness.observeUnsignedOutput sv stable "out" = some value ∧
    ∀ seed, Bounded (fun x => (Tools.ShippingDeclWidths.astWidths sv x).getD 0) seed →
      (∀ x, x ∉ svTargets pairs → seed x = initial x) →
      (∃ trace, DeltaTrace (Tools.ShippingDeclWidths.astWidths sv) pairs seed trace) ∧
      ∀ trace, DeltaTrace (Tools.ShippingDeclWidths.astWidths sv) pairs seed trace →
        ∀ k, pairs.length ≤ k → trace k = stable ∧
          Tools.ShippingModulePrintSoundness.observeUnsignedOutput sv (trace k) "out" = some value

end Tools.ShippingDeltaSemantics
