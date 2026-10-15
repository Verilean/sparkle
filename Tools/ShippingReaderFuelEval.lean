import Tools.ShippingReaderFuelKleene

/-! # Adequacy of the fuel reader w.r.t. FINITE executions

WRITTEN, NOT BUILT (worker E, branch `par/r-8`; record
`docs/parallel/R-reader-coverage.md` §7). No `sorry`, no axiom, no
`native_decide`. Imports only the BUILT `Defs` / `Kleene` files.

Ruling 2026-10-15 (reviewer): `fixpoint_not_complete` stands (the source
EQUATION alone does not give coverage), but "a FINITE execution derivation
gives some fuel with the same answer" is a separate, provable statement. It is
proved here, in both directions, for the machine-reader block (`readF`) and
for `machNorm` (`machNormF`).

## The finite-execution relation

`EvalG Φ c r` (generic in the body `Φ`): call `c` executes to `r` if there is
a FINITE list `L` of sub-calls with answers, each with its own (smaller)
derivation, such that the body of `c` returns `r` against EVERY call table that
answers at least those sub-calls with those answers (`Ext h L`). A derivation
is therefore a well-founded, finitely branching tree of calls: a finite call
tree. `r : R c`; for the block `R c = Option c.Res`, so `r = some v` is a
success and `r = none` an ORDINARY REFUSAL (the old `none`) — both are
executions; fuel exhaustion (OUT) is not a value of `r` at all.

`Runs Φ m a` is the same notion for an arbitrary computation `m` (a
sub-term of a body); `runs_pure`, `runs_call`, `runs_bind`, `runs_bindO`,
`runs_foldO_*` (the old `foldlM`), `runs_findSomeO_*` (the old `findSome?`)
are its rules, and `runs_bind_inv`, `runs_foldO_cons_inv`,
`runs_findSomeO_inv` their inversions.

## What is proved

* `eval_fuel`  : `Eval senv c r → ∃ n, readF senv n c = some r`
  (no hypothesis; success AND refusal; the fuel is the tree's height bound);
* `fuel_eval`  : `readF senv n c = some r → Eval senv c r`;
* `eval_det`, `eval_iff`, `eval_agree` (every derivation's answer is the value
  of every step-level solution: `Eval` is the LEAST one);
* the same for `machNorm`: `evalN_fuel`, `fuel_evalN`, `evalN_det`,
  `evalN_iff`.

The converse direction needs that each body inspects only finitely many
answers (`Compact`, a compactness / continuity property). `FM` alone does not
give it (an `FM` value is any monotone function of the table), so it is
proved for the actual bodies: `compact_step`, `compact_normStep`, by
induction over the combinators (`pure`/`bind`/`call`/`optK`/`domGuard`/
`foldO`/`findSomeO`) and a case split of every arm.

## What is NOT proved here (kept apart)

* **O1 (outside the model)**: that the old COMPILED `partial` implementation,
  when it returns, produced such a finite derivation. That is a fact about the
  runtime, not the kernel.
* **The opaque helpers** called by the bodies — `rootFloat`, `zetaAll` (in
  `machReserve`), `rawNode` and `machNormNode` (and their `partial` callees
  `packTupleInputs`, `machLiftScalarN`, `machBoolMap`), and the `opaque`
  `Expr` primitives `instantiate1`, `liftLooseBVars`, `lowerLooseBVars` /
  `beta` / `instantiate`, `Expr.eqv` (`==` / `!=`), `hasLooseBVars` — are
  PARAMETERS of the relation: a derivation consumes each of their results as a
  single value (one discriminant of one step), whatever that value is. The
  proofs never inspect them (`Compact` is proved by splitting on their results
  as opaque discriminants). Their own termination and their agreement with
  the runtime (O3/O4) are NOT claimed. -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

/-! ## Finite tables, compactness -/

section Generic
variable {κ : Type} {R : κ → Type} {α β σ : Type}

/-- The table `h` answers (at least) the listed calls with the listed answers. -/
def Ext (h : (c : κ) → Option (R c)) (L : List (Sigma R)) : Prop :=
  ∀ p, p ∈ L → h p.1 = some p.2

theorem ext_nil (h : (c : κ) → Option (R c)) : Ext h ([] : List (Sigma R)) := by
  intro p hp
  cases hp

theorem ext_append {h : (c : κ) → Option (R c)} {L₁ L₂ : List (Sigma R)}
    (h₁ : Ext h L₁) (h₂ : Ext h L₂) : Ext h (L₁ ++ L₂) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

theorem ext_left {h : (c : κ) → Option (R c)} {L₁ L₂ : List (Sigma R)}
    (hx : Ext h (L₁ ++ L₂)) : Ext h L₁ :=
  fun p hp => hx p (List.mem_append.mpr (Or.inl hp))

theorem ext_right {h : (c : κ) → Option (R c)} {L₁ L₂ : List (Sigma R)}
    (hx : Ext h (L₁ ++ L₂)) : Ext h L₂ :=
  fun p hp => hx p (List.mem_append.mpr (Or.inr hp))

/-- **Compactness** of a computation: a result obtained against a table is
determined by FINITELY many of the table's answers. (A structure, so that
`intro` never unfolds it.) -/
structure Compact (m : FM κ R α) : Prop where
  ok : ∀ (h : (c : κ) → Option (R c)) (a : α), m.run h = some a →
    ∃ L : List (Sigma R), Ext h L ∧
      ∀ h' : (c : κ) → Option (R c), Ext h' L → m.run h' = some a

theorem compact_pure (a : α) : Compact (FM.pure (κ := κ) (R := R) a) :=
  ⟨fun h b hb => ⟨[], ext_nil h, fun _ _ => hb⟩⟩

theorem compact_call (c : κ) : Compact (FM.call (R := R) c) := by
  constructor
  intro h r hr
  refine ⟨[⟨c, r⟩], ?_, fun h' e' => e' ⟨c, r⟩ (List.mem_cons.mpr (Or.inl rfl))⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hr
  · cases hp

theorem compact_bind {x : FM κ R α} {f : α → FM κ R β} (hx : Compact x)
    (hf : ∀ a, Compact (f a)) : Compact (FM.bind x f) := by
  constructor
  intro h b hb
  have hb' : (x.run h).bind (fun a => (f a).run h) = some b := hb
  obtain ⟨a, ha, hfa⟩ := Option.bind_eq_some_iff.mp hb'
  obtain ⟨L₁, e₁, k₁⟩ := hx.ok h a ha
  obtain ⟨L₂, e₂, k₂⟩ := (hf a).ok h b hfa
  refine ⟨L₁ ++ L₂, ext_append e₁ e₂, fun h' e' => ?_⟩
  show (x.run h').bind (fun a => (f a).run h') = some b
  exact Option.bind_eq_some_iff.mpr ⟨a, k₁ h' (ext_left e'), k₂ h' (ext_right e')⟩

theorem compact_okO (a : α) : Compact (okO (κ := κ) (R := R) a) := compact_pure _

theorem compact_failO : Compact (failO (κ := κ) (R := R) (α := α)) := compact_pure _

theorem compact_optK (o : Option α) {f : α → FM κ R (Option β)} (hf : ∀ a, Compact (f a)) :
    Compact (optK o f) := by
  cases o with
  | some a => exact hf a
  | none => exact compact_pure _

theorem compact_bindO {x : FM κ R (Option α)} {f : α → FM κ R (Option β)} (hx : Compact x)
    (hf : ∀ a, Compact (f a)) : Compact (bindO x f) :=
  compact_bind hx (fun o => compact_optK o hf)

theorem compact_domGuard (o : Option Lean.Expr) (dom' : Lean.Expr) {k : FM κ R (Option β)}
    (hk : Compact k) : Compact (domGuard o dom' k) := by
  unfold domGuard
  repeat' (first | exact hk | exact compact_pure _ | split)

theorem compact_foldO {f : σ → α → FM κ R (Option σ)} (hf : ∀ s a, Compact (f s a)) :
    ∀ (s : σ) (l : List α), Compact (foldO f s l) := by
  intro s l
  induction l generalizing s with
  | nil => exact compact_pure _
  | cons a as ih => exact compact_bindO (hf s a) (fun s' => ih s')

theorem compact_findSomeO {f : α → FM κ R (Option β)} (hf : ∀ a, Compact (f a)) :
    ∀ l : List α, Compact (findSomeO f l) := by
  intro l
  induction l with
  | nil => exact compact_pure _
  | cons a as ih =>
    refine compact_bind (hf a) (fun o => ?_)
    cases o with
    | some b => exact compact_pure _
    | none => exact ih

/-! ## The finite-execution relation -/

/-- **Finite execution** of call `c` with answer `r`: finitely many sub-calls
`L`, each executed (a sub-derivation), and the body of `c` returns `r` against
every table answering at least those. A derivation is a finite call tree. -/
inductive EvalG (Φ : (c : κ) → FM κ R (R c)) : (c : κ) → R c → Prop
  | node {c : κ} {r : R c} (L : List (Sigma R))
      (sub : ∀ p, p ∈ L → EvalG Φ p.1 p.2)
      (hrun : ∀ h : (c' : κ) → Option (R c'), Ext h L → (Φ c).run h = some r) :
      EvalG Φ c r

/-- A table that answers finitely many calls, each at some fuel, is below a
single fuel. -/
theorem ext_fuel_of (Φ : (c : κ) → FM κ R (R c)) :
    ∀ L : List (Sigma R), (∀ p, p ∈ L → ∃ n, fuel Φ n p.1 = some p.2) →
      ∃ N, Ext (fuel Φ N) L := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, ext_nil _⟩
  | cons q L ih =>
    intro hL
    obtain ⟨n, hn⟩ := hL q (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨N, hN⟩ := ih (fun p hp => hL p (List.mem_cons.mpr (Or.inr hp)))
    refine ⟨n + N, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact fuel_stable Φ hn (Nat.le_add_right n N)
    · exact fuel_stable Φ (hN p hp) (Nat.le_add_left N n)

/-- **Adequacy, derivation ⟹ fuel** (no hypothesis on the body). -/
theorem evalG_fuel {Φ : (c : κ) → FM κ R (R c)} {c : κ} {r : R c} (hev : EvalG Φ c r) :
    ∃ n, fuel Φ n c = some r := by
  induction hev with
  | node L _ hrun ih =>
    obtain ⟨N, hN⟩ := ext_fuel_of Φ L ih
    exact ⟨N + 1, hrun (fuel Φ N) hN⟩

/-- **Adequacy, fuel ⟹ derivation**, for a compact body. -/
theorem fuel_evalG {Φ : (c : κ) → FM κ R (R c)} (hΦ : ∀ c, Compact (Φ c)) :
    ∀ (n : Nat) (c : κ) (r : R c), fuel Φ n c = some r → EvalG Φ c r := by
  intro n
  induction n with
  | zero =>
    intro c r h
    rw [fuel_zero] at h
    cases h
  | succ n ih =>
    intro c r h
    obtain ⟨L, e, k⟩ := (hΦ c).ok (fuel Φ n) r h
    exact EvalG.node L (fun p hp => ih p.1 p.2 (e p hp)) k

theorem evalG_det {Φ : (c : κ) → FM κ R (R c)} {c : κ} {r r' : R c}
    (h₁ : EvalG Φ c r) (h₂ : EvalG Φ c r') : r = r' := by
  obtain ⟨n, hn⟩ := evalG_fuel h₁
  obtain ⟨m, hm⟩ := evalG_fuel h₂
  exact fuel_det Φ hn hm

/-- A derivation's answer is the value of every step-level solution: the
finite-execution relation is contained in every fixpoint. -/
theorem evalG_agree {Φ : (c : κ) → FM κ R (R c)} (g : (c : κ) → R c) (hg : IsSol Φ g)
    {c : κ} {r : R c} (h : EvalG Φ c r) : g c = r := by
  obtain ⟨n, hn⟩ := evalG_fuel h
  exact fuel_agree Φ g hg hn

/-! ## Finite executions of sub-computations: the rules of `bind` / `fold` / `findSome` -/

/-- `m` runs to `a` using finitely many executed calls. (`abbrev`: anonymous
constructors see the `∃`.) -/
abbrev Runs (Φ : (c : κ) → FM κ R (R c)) (m : FM κ R α) (a : α) : Prop :=
  ∃ L : List (Sigma R), (∀ p, p ∈ L → EvalG Φ p.1 p.2) ∧
    ∀ h : (c : κ) → Option (R c), Ext h L → m.run h = some a

section Rules
variable {Φ : (c : κ) → FM κ R (R c)}

theorem evalG_iff_runs {c : κ} {r : R c} : EvalG Φ c r ↔ Runs Φ (Φ c) r := by
  constructor
  · intro h
    cases h with
    | node L sub hrun => exact ⟨L, sub, hrun⟩
  · intro h
    obtain ⟨L, sub, hrun⟩ := h
    exact EvalG.node L sub hrun

theorem runs_pure (a : α) : Runs Φ (FM.pure a) a :=
  ⟨[], (fun p hp => by cases hp), fun _ _ => rfl⟩

theorem runs_call {c : κ} {r : R c} (hev : EvalG Φ c r) : Runs Φ (FM.call c) r := by
  refine ⟨[⟨c, r⟩], ?_, fun h' e' => e' ⟨c, r⟩ (List.mem_cons.mpr (Or.inl rfl))⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hev
  · cases hp

theorem runs_bind {x : FM κ R α} {f : α → FM κ R β} {a : α} {b : β}
    (hx : Runs Φ x a) (hf : Runs Φ (f a) b) : Runs Φ (FM.bind x f) b := by
  obtain ⟨L₁, s₁, k₁⟩ := hx
  obtain ⟨L₂, s₂, k₂⟩ := hf
  refine ⟨L₁ ++ L₂, ?_, fun h e => ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact s₁ p hp
    · exact s₂ p hp
  · show (x.run h).bind (fun a => (f a).run h) = some b
    exact Option.bind_eq_some_iff.mpr ⟨a, k₁ h (ext_left e), k₂ h (ext_right e)⟩

theorem runs_okO (a : α) : Runs Φ (okO a) (some a) := runs_pure _

theorem runs_failO : Runs Φ (failO (α := α)) none := runs_pure _

theorem runs_bindO {x : FM κ R (Option α)} {f : α → FM κ R (Option β)} {a : α} {b : Option β}
    (hx : Runs Φ x (some a)) (hf : Runs Φ (f a) b) : Runs Φ (bindO x f) b :=
  runs_bind hx hf

theorem runs_bindO_fail {x : FM κ R (Option α)} {f : α → FM κ R (Option β)}
    (hx : Runs Φ x none) : Runs Φ (bindO x f) none :=
  runs_bind hx (runs_pure none)

/-- `foldlM`, empty list. -/
theorem runs_foldO_nil {f : σ → α → FM κ R (Option σ)} (s : σ) :
    Runs Φ (foldO f s []) (some s) :=
  runs_pure _

/-- `foldlM`, a step that succeeds. -/
theorem runs_foldO_cons {f : σ → α → FM κ R (Option σ)} {s s' : σ} {a : α} {as : List α}
    {r : Option σ} (h1 : Runs Φ (f s a) (some s')) (h2 : Runs Φ (foldO f s' as) r) :
    Runs Φ (foldO f s (a :: as)) r :=
  runs_bindO h1 h2

/-- `foldlM`, a step that refuses: the whole fold refuses. -/
theorem runs_foldO_cons_fail {f : σ → α → FM κ R (Option σ)} {s : σ} {a : α} {as : List α}
    (h1 : Runs Φ (f s a) none) : Runs Φ (foldO f s (a :: as)) none :=
  runs_bindO_fail h1

/-- `findSome?`, empty list. -/
theorem runs_findSomeO_nil {f : α → FM κ R (Option β)} : Runs Φ (findSomeO f []) none :=
  runs_pure _

/-- `findSome?`, a hit. -/
theorem runs_findSomeO_hit {f : α → FM κ R (Option β)} {a : α} {as : List α} {b : β}
    (h1 : Runs Φ (f a) (some b)) : Runs Φ (findSomeO f (a :: as)) (some b) := by
  refine runs_bind h1 ?_
  exact runs_pure _

/-- `findSome?`, "not this one" (an ordinary refusal of the probe). -/
theorem runs_findSomeO_miss {f : α → FM κ R (Option β)} {a : α} {as : List α} {r : Option β}
    (h1 : Runs Φ (f a) none) (h2 : Runs Φ (findSomeO f as) r) :
    Runs Φ (findSomeO f (a :: as)) r :=
  runs_bind h1 h2

/-- A run of a sub-computation has a finite fuel. -/
theorem runs_fuel {m : FM κ R α} {a : α} (hr : Runs Φ m a) :
    ∃ n, m.run (fuel Φ n) = some a := by
  obtain ⟨L, s, k⟩ := hr
  obtain ⟨N, hN⟩ := ext_fuel_of Φ L (fun p hp => evalG_fuel (s p hp))
  exact ⟨N, k _ hN⟩

/-- A fuel run of a compact sub-computation of a compact body is a finite run. -/
theorem fuel_runs (hΦ : ∀ c, Compact (Φ c)) {m : FM κ R α} (hm : Compact m) {n : Nat} {a : α}
    (h : m.run (fuel Φ n) = some a) : Runs Φ m a := by
  obtain ⟨L, e, k⟩ := hm.ok _ a h
  exact ⟨L, fun p hp => fuel_evalG hΦ n p.1 p.2 (e p hp), k⟩

theorem runs_pure_inv {a b : α} (h : Runs Φ (FM.pure a) b) : a = b := by
  obtain ⟨n, hn⟩ := runs_fuel h
  exact Option.some.inj hn

/-- Inversion of `bind`: a finite run of `x >>= f` is a finite run of `x`
followed by one of the continuation. -/
theorem runs_bind_inv (hΦ : ∀ c, Compact (Φ c)) {x : FM κ R α} {f : α → FM κ R β} {b : β}
    (hx : Compact x) (hf : ∀ a, Compact (f a)) (h : Runs Φ (FM.bind x f) b) :
    ∃ a, Runs Φ x a ∧ Runs Φ (f a) b := by
  obtain ⟨n, hn⟩ := runs_fuel h
  have hn' : (x.run (fuel Φ n)).bind (fun a => (f a).run (fuel Φ n)) = some b := hn
  obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hn'
  exact ⟨a, fuel_runs hΦ hx ha, fuel_runs hΦ (hf a) hb⟩

/-- Inversion of `foldlM` on a non-empty list. -/
theorem runs_foldO_cons_inv (hΦ : ∀ c, Compact (Φ c)) {f : σ → α → FM κ R (Option σ)}
    (hf : ∀ s a, Compact (f s a)) {s : σ} {a : α} {as : List α} {r : Option σ}
    (h : Runs Φ (foldO f s (a :: as)) r) :
    (r = none ∧ Runs Φ (f s a) none) ∨
      (∃ s', Runs Φ (f s a) (some s') ∧ Runs Φ (foldO f s' as) r) := by
  obtain ⟨o, h1, h2⟩ := runs_bind_inv hΦ (hf s a)
    (fun o => by exact compact_optK o (fun s' => compact_foldO hf s' as)) h
  cases o with
  | none => exact Or.inl ⟨(runs_pure_inv h2).symm, h1⟩
  | some s' => exact Or.inr ⟨s', h1, h2⟩

/-- Inversion of `findSome?` on a non-empty list. -/
theorem runs_findSomeO_inv (hΦ : ∀ c, Compact (Φ c)) {f : α → FM κ R (Option β)}
    (hf : ∀ a, Compact (f a)) {a : α} {as : List α} {r : Option β}
    (h : Runs Φ (findSomeO f (a :: as)) r) :
    (∃ b, r = some b ∧ Runs Φ (f a) (some b)) ∨
      (Runs Φ (f a) none ∧ Runs Φ (findSomeO f as) r) := by
  obtain ⟨o, h1, h2⟩ := runs_bind_inv hΦ (hf a)
    (fun o => by
      cases o with
      | some b => exact compact_pure _
      | none => exact compact_findSomeO hf as) h
  cases o with
  | some b => exact Or.inl ⟨b, (runs_pure_inv h2).symm, h1⟩
  | none => exact Or.inr ⟨h1, h2⟩

end Rules

end Generic

/-! ## Compactness of the block's bodies -/

theorem compact_cConv {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead} :
    Compact (cConv env d e st) := compact_call (Call.conv env d e st)

theorem compact_cNested {env : List MachVal} {dom αs initsE body : Lean.Expr} {st : MachRead} :
    Compact (cNested env dom αs initsE body st) :=
  compact_call (Call.nested env dom αs initsE body st)

theorem compact_cInst {env : List MachVal} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} {st : MachRead} :
    Compact (cInst env c kinds res args st) := compact_call (Call.inst env c kinds res args st)

theorem compact_cInstS {env : List MachVal} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead} :
    Compact (cInstS env c kinds ty args st) := compact_call (Call.instS env c kinds ty args st)

theorem compact_cChain {env : List MachVal} {e : Lean.Expr} {st : MachRead} :
    Compact (cChain env e st) := compact_call (Call.chain env e st)

theorem compact_cLoopBody {base : Nat} {env : List MachVal} {e : Lean.Expr} {st : MachRead} :
    Compact (cLoopBody base env e st) := compact_call (Call.loopBody base env e st)

theorem compact_cLoopRoot {env : List MachVal} {e : Lean.Expr} {st : MachRead} :
    Compact (cLoopRoot env e st) := compact_call (Call.loopRoot env e st)

/-- One crunch step: a combinator lemma (syntactic, reducible transparency),
an `intro`, a case split, or a beta/zeta/iota clean-up. -/
macro "compact_base" : tactic => `(tactic| first
  | with_reducible exact compact_cConv
  | with_reducible exact compact_cNested
  | with_reducible exact compact_cInst
  | with_reducible exact compact_cInstS
  | with_reducible exact compact_cChain
  | with_reducible exact compact_cLoopBody
  | with_reducible exact compact_cLoopRoot
  | with_reducible exact compact_okO _
  | with_reducible exact compact_failO
  | with_reducible exact compact_pure _
  | with_reducible exact compact_call _
  | with_reducible apply compact_bindO
  | with_reducible apply compact_bind
  | with_reducible apply compact_optK
  | with_reducible apply compact_domGuard
  | with_reducible apply compact_foldO
  | with_reducible apply compact_findSomeO
  | intro _
  | split
  | dsimp only)

theorem compact_nestedProbe (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) (p : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr) :
    Compact (nestedProbe env dom' αs initsE body st p) := by
  unfold nestedProbe
  repeat' compact_base

theorem compact_instArg (env : List MachVal) (k : Nat) (s : List Nat × MachRead)
    (a : MixedGateBinder × Lean.Expr) : Compact (instArg env k s a) := by
  unfold instArg
  repeat' compact_base

theorem compact_instSArg (env : List MachVal) (s : List Nat × MachRead)
    (a : MixedGateBinder × Lean.Expr) : Compact (instSArg env s a) := by
  unfold instSArg
  repeat' compact_base

theorem compact_instSParam (env : List MachVal) (s : List Lean.Expr × MachRead)
    (p : Lean.Expr) : Compact (instSParam env s p) := by
  unfold instSParam
  repeat' compact_base

theorem compact_loopNext (env : List MachVal) (base : Nat)
    (s : List (Nat × Lean.Expr) × MachRead) (t : Lean.Expr × Lean.Expr × Lean.Expr) :
    Compact (loopNext env base s t) := by
  unfold loopNext
  repeat' compact_base

theorem compact_loopProbe (env : List MachVal) (body : Lean.Expr) (n : Nat) (st : MachRead)
    (p : Nat × Nat × List (Nat × Lean.Expr)) : Compact (loopProbe env body n st p) := by
  unfold loopProbe
  repeat' compact_base

/-- The crunch with the per-helper lemmas. -/
macro "compact_all" : tactic => `(tactic| repeat' (first
  | with_reducible exact compact_nestedProbe _ _ _ _ _ _ _
  | with_reducible exact compact_instArg _ _ _ _
  | with_reducible exact compact_instSArg _ _ _
  | with_reducible exact compact_instSParam _ _ _
  | with_reducible exact compact_loopNext _ _ _ _
  | with_reducible exact compact_loopProbe _ _ _ _ _
  | compact_base))

set_option maxHeartbeats 1000000 in
theorem compact_convStep (senv : StructEnv) (env : List MachVal) (d : Nat) (e : Lean.Expr)
    (st : MachRead) : Compact (convStep senv env d e st) := by
  unfold convStep
  compact_all

theorem compact_nestedStep (senv : StructEnv) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) :
    Compact (nestedStep senv env dom αs initsE body st) := by
  unfold nestedStep
  compact_all

theorem compact_instStep (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) :
    Compact (instStep env c kinds res args st) := by
  unfold instStep
  compact_all

theorem compact_instSStep (senv : StructEnv) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead) :
    Compact (instSStep senv env c kinds ty args st) := by
  unfold instSStep
  compact_all

set_option maxHeartbeats 1000000 in
theorem compact_chainStep (senv : StructEnv) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Compact (chainStep senv env e st) := by
  unfold chainStep
  compact_all

theorem compact_loopBodyStep (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    Compact (loopBodyStep base env e st) := by
  unfold loopBodyStep
  compact_all

set_option maxHeartbeats 1000000 in
theorem compact_loopRootStep (senv : StructEnv) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Compact (loopRootStep senv env e st) := by
  unfold loopRootStep
  compact_all

/-- **Every arm of the block inspects finitely many answers.** -/
theorem compact_step (senv : StructEnv) : ∀ c : Call, Compact (step senv c) := by
  intro c
  cases c with
  | conv env d e st => exact compact_convStep senv env d e st
  | nested env dom αs initsE body st => exact compact_nestedStep senv env dom αs initsE body st
  | inst env c kinds res args st => exact compact_instStep env c kinds res args st
  | instS env c kinds ty args st => exact compact_instSStep senv env c kinds ty args st
  | chain env e st => exact compact_chainStep senv env e st
  | loopBody base env e st => exact compact_loopBodyStep base env e st
  | loopRoot env e st => exact compact_loopRootStep senv env e st

/-! ## The block: finite executions = finished fuel runs -/

/-- **Finite execution of the machine-reader block.** `r = some v`: success;
`r = none`: ordinary refusal (the old `none`). -/
abbrev Eval (senv : StructEnv) : (c : Call) → RB c → Prop := EvalG (step senv)

/-- **Sufficient fuel**: a finite execution (success or refusal) is reached at
some fuel. No hypothesis. -/
theorem eval_fuel {senv : StructEnv} {c : Call} {r : RB c} (h : Eval senv c r) :
    ∃ n, readF senv n c = some r :=
  evalG_fuel h

/-- **Converse**: a finished fuel answer is a finite execution. -/
theorem fuel_eval {senv : StructEnv} {n : Nat} {c : Call} {r : RB c}
    (h : readF senv n c = some r) : Eval senv c r :=
  fuel_evalG (compact_step senv) n c r h

theorem eval_iff {senv : StructEnv} {c : Call} {r : RB c} :
    Eval senv c r ↔ ∃ n, readF senv n c = some r :=
  ⟨eval_fuel, fun ⟨_, h⟩ => fuel_eval h⟩

theorem eval_det {senv : StructEnv} {c : Call} {r r' : RB c}
    (h₁ : Eval senv c r) (h₂ : Eval senv c r') : r = r' :=
  evalG_det h₁ h₂

/-- Success: a sufficient fuel. -/
theorem eval_fuel_ok {senv : StructEnv} {c : Call} {v : c.Res} (h : Eval senv c (some v)) :
    ∃ n, readF senv n c = some (some v) :=
  eval_fuel h

/-- Ordinary refusal: a sufficient fuel (never confused with OUT). -/
theorem eval_fuel_fail {senv : StructEnv} {c : Call} (h : Eval senv c none) :
    ∃ n, readF senv n c = some none :=
  eval_fuel h

/-- A finite execution's answer is the value of every step-level solution. -/
theorem eval_agree {senv : StructEnv} (g : (c : Call) → RB c) (hg : IsSol (step senv) g)
    {c : Call} {r : RB c} (h : Eval senv c r) : g c = r :=
  evalG_agree g hg h

theorem machConvF_iff_eval {senv : StructEnv} {env : List MachVal} {d : Nat} {e : Lean.Expr}
    {st : MachRead} {r : Option (Lean.Expr × MachRead)} :
    (∃ n, machConvF n senv env d e st = some r) ↔ Eval senv (Call.conv env d e st) r :=
  eval_iff.symm

theorem machChainF_iff_eval {senv : StructEnv} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {r : Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead)} :
    (∃ n, machChainF n senv env e st = some r) ↔ Eval senv (Call.chain env e st) r :=
  eval_iff.symm

theorem machLoopRootF_iff_eval {senv : StructEnv} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {r : Option (MachVal × MachRead)} :
    (∃ n, machLoopRootF n senv env e st = some r) ↔ Eval senv (Call.loopRoot env e st) r :=
  eval_iff.symm

/-! ## `machNorm` -/

set_option maxHeartbeats 1000000 in
theorem compact_normStep (senv : StructEnv) (e : Lean.Expr) : Compact (normStep senv e) := by
  unfold normStep
  repeat' compact_base

/-- **Finite execution of `machNorm`** (it never refuses: every execution is a
result). -/
abbrev EvalN (senv : StructEnv) : Lean.Expr → Lean.Expr → Prop :=
  @EvalG Lean.Expr (fun _ => Lean.Expr) (normStep senv)

theorem evalN_fuel {senv : StructEnv} {e r : Lean.Expr} (h : EvalN senv e r) :
    ∃ n, machNormF n senv e = some r :=
  evalG_fuel h

theorem fuel_evalN {senv : StructEnv} {n : Nat} {e r : Lean.Expr}
    (h : machNormF n senv e = some r) : EvalN senv e r :=
  @fuel_evalG Lean.Expr (fun _ => Lean.Expr) (normStep senv) (compact_normStep senv) n e r h

theorem evalN_iff {senv : StructEnv} {e r : Lean.Expr} :
    EvalN senv e r ↔ ∃ n, machNormF n senv e = some r :=
  ⟨evalN_fuel, fun ⟨_, h⟩ => fuel_evalN h⟩

theorem evalN_det {senv : StructEnv} {e r r' : Lean.Expr}
    (h₁ : EvalN senv e r) (h₂ : EvalN senv e r') : r = r' :=
  evalG_det h₁ h₂

end Tools.ShippingReaderFuel
