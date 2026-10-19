import Tools.ShippingCallWidthsStructRes

/-! # `InstSubst` from a proved substitution model + an explicit runtime boundary

BUILT (worker O-SUBST, from poc 5934ac32; run sm1 failed at one existential
packing (line 366, `⟨us, …⟩` added by the integrator), run sm2 exit 0). Axioms of
`instSubstM`, `instSubst_of_agree`: [propext, Classical.choice, Quot.sound]. No
`sorry`, no new axiom, no `native_decide`.

`InstAgree` is an OPEN runtime-agreement boundary (the extern
`Expr.instantiate1` agrees with the proved model `inst1M`), NOT a trusted binder
and not established. Evidence only: `Tests/Compiler/InstAgreeShadowProbe.lean`
(run sh3: 4260 comparisons — every telescope step of the hardware modules and
`Sparkle.Core.Signal` constants in scope, six argument shapes including loose
bvars and a lambda — 0 mismatches). Premise change: `InstSubst` (a semantic
statement about the extern) is now DERIVED from `InstAgree` (`instSubst_of_agree`).

## What this does

`Tools.ShippingCallWidthsStructRes.InstSubst` is a NEW semantic premise about
`Lean.Expr.instantiate1`, an `@[extern "lean_expr_instantiate1"] opaque`
(v4.32.1 `src/lean/Lean/Expr.lean:1446`): the kernel/logic knows NOTHING about
its value, so no proof can inspect it. This file splits that premise into

1. a pure, structurally recursive de Bruijn substitution model `inst1M`
   (with its own loose-bvar lift `liftM`; `Expr.liftLooseBVars` is extern as
   well), covering every `Expr` constructor, and
2. `instSubstM : InstSubstM` — BOTH clauses of `InstSubst` PROVED for the
   model (`head`: head constant of the `∀`-body kept; `outs`: a `machOuts?`
   reading kept when `senv.fields Signal = none`), via lemmas generalised
   over the binder depth `j` (`head_inst`, `outs_inst`), with no isolated
   hypothesis, and
3. the BOUNDARY `InstAgree : Prop` — the runtime agreement of the extern with
   the model — and `instSubst_of_agree : InstAgree → InstSubst`.

## Premise accounting

`InstSubst` (NEW semantic premise, an arbitrary-looking statement about an
opaque function) is REPLACED by `InstAgree` (runtime agreement of an extern
with a proved model). `InstAgree` is an explicit boundary: it is NOT
established, NOT trusted and NOT in any allowed-premise list. It is,
however, a precise, model-checkable claim: `Expr` equality is structural
(the cached `data` field is computed from the children), so it can be
SHADOW-CHECKED by `#eval` comparing `b.instantiate1 a` with `inst1M b 0 a`
on sample terms (e.g. the forall-telescope bodies of the corpus `instS`
types). It cannot be checked by `decide`/`rfl`: `instantiate1` is opaque.
Such a shadow check is evidence about the C implementation, not a proof.

The C implementation (`instantiate` in `src/kernel/instantiate.cpp`) is
expected to match the model: loose `bvar k` at depth `k` becomes `a` lifted
by `k` (`lift_loose_bvars`), higher loose bvars are decremented, everything
else is rebuilt unchanged. That expectation is documentation only.

`InstAgree` is stated for ALL `b a`; only the bodies `instRes` actually
substitutes are needed (`instSignatureS?` types), so a restricted
`InstAgreeOn` would be weaker — not introduced here, because the
restriction would have to be threaded through `instRes_outs`/`instRes_head`
(StructRes) and the single global statement is the simplest testable form.
-/
namespace Tools.ShippingInstSubstModel
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingCallWidthsStructRes (resBody machOuts?_forall outs_nonprod InstSubst)
open Tools.ShippingReaderResultKind (outsOfKind)

/-! ## The model -/

/-- Lift the loose bound variables `≥ d` of `e` by `n` (model of
`Expr.liftLooseBVars e d n`). -/
def liftM : Lean.Expr → Nat → Nat → Lean.Expr
  | .bvar i, n, d => if i < d then .bvar i else .bvar (i + n)
  | .fvar x, _, _ => .fvar x
  | .mvar m, _, _ => .mvar m
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app f x, n, d => .app (liftM f n d) (liftM x n d)
  | .lam nm t b bi, n, d => .lam nm (liftM t n d) (liftM b n (d + 1)) bi
  | .forallE nm t b bi, n, d => .forallE nm (liftM t n d) (liftM b n (d + 1)) bi
  | .letE nm t v b nd, n, d =>
    .letE nm (liftM t n d) (liftM v n d) (liftM b n (d + 1)) nd
  | .lit l, _, _ => .lit l
  | .mdata m e, n, d => .mdata m (liftM e n d)
  | .proj s i e, n, d => .proj s i (liftM e n d)

/-- Substitute `a` for the loose bound variable `k` (at binder depth `k`),
decrementing the higher loose bound variables (model of
`Expr.instantiate1 e a = inst1M e 0 a`). -/
def inst1M : Lean.Expr → Nat → Lean.Expr → Lean.Expr
  | .bvar i, k, a =>
    if i < k then .bvar i else if i = k then liftM a k 0 else .bvar (i - 1)
  | .fvar x, _, _ => .fvar x
  | .mvar m, _, _ => .mvar m
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app f x, k, a => .app (inst1M f k a) (inst1M x k a)
  | .lam nm t b bi, k, a => .lam nm (inst1M t k a) (inst1M b (k + 1) a) bi
  | .forallE nm t b bi, k, a => .forallE nm (inst1M t k a) (inst1M b (k + 1) a) bi
  | .letE nm t v b nd, k, a =>
    .letE nm (inst1M t k a) (inst1M v k a) (inst1M b (k + 1) a) nd
  | .lit l, _, _ => .lit l
  | .mdata m e, k, a => .mdata m (inst1M e k a)
  | .proj s i e, k, a => .proj s i (inst1M e k a)

theorem inst1M_app (f x : Lean.Expr) (j : Nat) (a : Lean.Expr) :
    inst1M (.app f x) j a = .app (inst1M f j a) (inst1M x j a) := by
  first | rfl | simp [inst1M]

theorem inst1M_const (c : Name) (us : List Lean.Level) (j : Nat) (a : Lean.Expr) :
    inst1M (.const c us) j a = .const c us := by
  first | rfl | simp [inst1M]

theorem inst1M_lit (l : Literal) (j : Nat) (a : Lean.Expr) :
    inst1M (.lit l) j a = .lit l := by
  first | rfl | simp [inst1M]

theorem inst1M_forallE (n : Name) (d b : Lean.Expr) (bi : BinderInfo) (j : Nat)
    (a : Lean.Expr) :
    inst1M (.forallE n d b bi) j a = .forallE n (inst1M d j a) (inst1M b (j + 1) a) bi := by
  first | rfl | simp [inst1M]

/-! ## Head constants are kept -/

theorem inst_getAppFn (j : Nat) (a : Lean.Expr) (s : Name) (ls : List Lean.Level) :
    ∀ e : Lean.Expr, e.getAppFn = .const s ls → (inst1M e j a).getAppFn = .const s ls := by
  intro e
  induction e with
  | app f x ihf _ =>
    intro h
    rw [inst1M_app]
    exact ihf h
  | const c us =>
    intro h
    rw [inst1M_const]
    exact h
  | _ =>
    intro h
    first
      | cases h
      | simp [Lean.Expr.getAppFn] at h

/-- **`head`, generalised over the binder depth.** -/
theorem head_inst (a : Lean.Expr) (s : Name) (ls : List Lean.Level) :
    ∀ (b : Lean.Expr) (j : Nat), (resBody b).getAppFn = .const s ls →
      (resBody (inst1M b j a)).getAppFn = .const s ls := by
  intro b
  induction b with
  | forallE n d body bi _ ih =>
    intro j h
    rw [inst1M_forallE]
    exact ih (j + 1) h
  | app f x _ _ =>
    intro j h
    have h1 : (Lean.Expr.app f x).getAppFn = .const s ls := h
    have h2 := inst_getAppFn j a s ls (.app f x) h1
    rw [inst1M_app] at h2 ⊢
    exact h2
  | const c us =>
    intro j h
    rw [inst1M_const]
    exact h
  | _ =>
    intro j h
    first
      | cases h
      | simp [resBody, Lean.Expr.getAppFn] at h

/-- A `Prod`-shaped substitution result of a constant-headed term comes from a
`Prod`-shaped term (same head, same arity). -/
theorem inst_prod_inv (j : Nat) (a : Lean.Expr) {us : List Lean.Level} {x' y' : Lean.Expr} :
    ∀ (e : Lean.Expr) {s : Name} {ls : List Lean.Level}, e.getAppFn = .const s ls →
      inst1M e j a = .app (.app (.const ``Prod us) x') y' →
      ∃ x y, e = .app (.app (.const ``Prod us) x) y := by
  intro e s ls he h
  cases e with
  | app f y =>
    rw [inst1M_app] at h
    injection h with h1 h1b
    cases f with
    | app g x =>
      rw [inst1M_app] at h1
      injection h1 with h2 h2b
      cases g with
      | const c ls' =>
        rw [inst1M_const] at h2
        injection h2 with h3 h4
        subst h3
        subst h4
        exact ⟨x, y, rfl⟩
      | app g1 g2 =>
        rw [inst1M_app] at h2
        cases h2
      | _ =>
        first
          | cases he
          | simp [Lean.Expr.getAppFn] at he
    | const c ls' =>
      rw [inst1M_const] at h1
      cases h1
    | _ =>
      first
        | cases he
        | simp [Lean.Expr.getAppFn] at he
  | const c ls' =>
    rw [inst1M_const] at h
    cases h
  | _ =>
    first
      | cases he
      | simp [Lean.Expr.getAppFn] at he

/-! ## Binder kinds are kept -/

theorem natLit_inst (j : Nat) (a : Lean.Expr) {wE : Lean.Expr} {n : Nat}
    (h : canonicalNatLitValue? wE = some n) : inst1M wE j a = wE := by
  unfold canonicalNatLitValue? at h
  split at h
  all_goals first
    | rfl
    | (simp only [inst1M_app, inst1M_const, inst1M_lit])
    | (subst_vars; rfl)
    | (subst_vars; simp only [inst1M_app, inst1M_const, inst1M_lit])
    | cases h
    | simp at h

theorem kind_bool_eq (us : List Lean.Level) (dom : Lean.Expr) (us' : List Lean.Level) :
    mixedGateBinderKind?
      (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom) (.const ``Bool us')) =
      some .bool := by
  first | rfl | simp [mixedGateBinderKind?, Lean.Expr.isConstOf]

theorem kind_bits_eq (us : List Lean.Level) (dom : Lean.Expr) (us' : List Lean.Level)
    (wE : Lean.Expr) :
    mixedGateBinderKind?
      (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom) (.app (.const ``BitVec us') wE)) =
      (canonicalNatLitValue? wE).bind (fun n => if 0 < n then some (.bits n) else none) := by
  first | rfl | simp [mixedGateBinderKind?, Lean.Expr.isConstOf]

/-- A non-domain binder kind survives substitution (the width literal is
closed; the domain argument may change). -/
theorem kind_inst (j : Nat) (a : Lean.Expr) {e : Lean.Expr} {kd : MixedGateBinder}
    (h : mixedGateBinderKind? e = some kd) (hk : kd ≠ .domain) :
    mixedGateBinderKind? (inst1M e j a) = some kd := by
  rcases Tools.ShippingReaderResultKind.kind_inv h hk with
    ⟨us, dom, us', rfl, rfl⟩ | ⟨us, dom, us', wE, n, rfl, rfl⟩
  · simp only [inst1M_app, inst1M_const]
    exact kind_bool_eq us (inst1M dom j a) us'
  · simp only [inst1M_app, inst1M_const]
    rw [kind_bits_eq] at h
    rw [kind_bits_eq]
    obtain ⟨m, hm, _⟩ := Option.bind_eq_some_iff.mp h
    rw [natLit_inst j a hm]
    exact h

theorem kind_head {e : Lean.Expr} {kd : MixedGateBinder}
    (h : mixedGateBinderKind? e = some kd) (hk : kd ≠ .domain) :
    ∃ us, e.getAppFn = .const ``Sparkle.Core.Signal.Signal us := by
  rcases Tools.ShippingReaderResultKind.kind_inv h hk with
    ⟨us, dom, us', rfl, _⟩ | ⟨us, dom, us', wE, n, rfl, _⟩
  · exact ⟨us, rfl⟩
  · exact ⟨us, rfl⟩

/-! ## `machOuts?` readings are kept -/

/-- The `Prod` arm of `machOuts?` (same text) as a function of the two kinds. -/
def prodOuts (kx ky : Option MixedGateBinder) :
    Option (Option Name × List (String × MixedGateBinder)) :=
  match kx, ky with
  | some ka, some kb =>
    if ka == .domain || kb == .domain then none
    else some (some ``Prod.mk, [("out_0", ka), ("out_1", kb)])
  | _, _ => none

theorem outs_prod (senv : StructEnv) (us : List Lean.Level) (x y : Lean.Expr) :
    machOuts? senv (.app (.app (.const ``Prod us) x) y) =
      prodOuts (mixedGateBinderKind? x) (mixedGateBinderKind? y) := by
  first
    | rfl
    | simp only [machOuts?, prodOuts]
    | simp [machOuts?, prodOuts]
    | (unfold machOuts? prodOuts; rfl)

theorem prod_inv {senv : StructEnv} {us : List Lean.Level} {x y : Lean.Expr}
    {o : Option Name × List (String × MixedGateBinder)}
    (h : machOuts? senv (.app (.app (.const ``Prod us) x) y) = some o) :
    ∃ ka kb, mixedGateBinderKind? x = some ka ∧ mixedGateBinderKind? y = some kb ∧
      ka ≠ .domain ∧ kb ≠ .domain := by
  rw [outs_prod] at h
  revert h
  cases mixedGateBinderKind? x <;> cases mixedGateBinderKind? y <;> intro h
  all_goals first
    | (simp [prodOuts] at h; done)
    | (refine ⟨_, _, rfl, rfl, ?_, ?_⟩ <;> intro hh <;> subst hh <;> simp [prodOuts] at h)

theorem outsOfKind_head_inv {senv : StructEnv} {e : Lean.Expr}
    {o : Option Name × List (String × MixedGateBinder)}
    (hk : mixedGateBinderKind? e = none ∨ mixedGateBinderKind? e = some .domain)
    (h : outsOfKind senv e = some o) :
    ∃ s ls, e.getAppFn = .const s ls ∧ senv.fields s ≠ none := by
  cases hg : e.getAppFn with
  | const s ls =>
    refine ⟨s, ls, rfl, ?_⟩
    intro hn
    rcases hk with hk | hk <;> simp [outsOfKind, hk, hg, hn] at h
  | _ => rcases hk with hk | hk <;> simp [outsOfKind, hk, hg] at h

theorem outsOfKind_eq (senv : StructEnv) {e e' : Lean.Expr}
    (hk : mixedGateBinderKind? e = none ∨ mixedGateBinderKind? e = some .domain)
    (hk' : mixedGateBinderKind? e' = none ∨ mixedGateBinderKind? e' = some .domain)
    (hg : e'.getAppFn = e.getAppFn) :
    outsOfKind senv e' = outsOfKind senv e := by
  rcases hk with hk | hk <;> rcases hk' with hk' | hk' <;> simp [outsOfKind, hk, hk', hg]

/-- **`outs` off the `∀` spine.** -/
theorem outs_inst_nf (senv : StructEnv)
    (NS : senv.fields ``Sparkle.Core.Signal.Signal = none) (a : Lean.Expr) (j : Nat)
    {e : Lean.Expr} {o : Option Name × List (String × MixedGateBinder)}
    (hnf : ∀ (n : Name) (d b : Lean.Expr) (bi : BinderInfo), e ≠ .forallE n d b bi)
    (h : machOuts? senv e = some o) : machOuts? senv (inst1M e j a) = some o := by
  by_cases hkd : ∃ kd, mixedGateBinderKind? e = some kd ∧ kd ≠ .domain
  · -- a Bool / BitVec Signal: the one port `out`, kept by `kind_inst`
    obtain ⟨kd, hk, hd⟩ := hkd
    rw [(Tools.ShippingReaderResultKind.outs_of_kind senv (kind_inst j a hk hd) hd).2]
    exact (Tools.ShippingReaderResultKind.outs_of_kind senv hk hd).2.symm.trans h
  · by_cases hp : ∃ (us : List Lean.Level) (x y : Lean.Expr),
        e = .app (.app (.const ``Prod us) x) y
    · -- the pair arm: both kinds kept
      obtain ⟨us, x, y, rfl⟩ := hp
      obtain ⟨ka, kb, hx, hy, hka, hkb⟩ := prod_inv h
      rw [inst1M_app, inst1M_app, inst1M_const, outs_prod,
        kind_inst j a hx hka, kind_inst j a hy hkb]
      rw [outs_prod, hx, hy] at h
      exact h
    · -- a structure head `s` (≠ `Signal` by `NS`): head and arity kept
      rw [outs_nonprod senv hnf hp] at h
      have hk : mixedGateBinderKind? e = none ∨ mixedGateBinderKind? e = some .domain := by
        cases hk0 : mixedGateBinderKind? e with
        | none => exact Or.inl rfl
        | some kd =>
          by_cases hd : kd = .domain
          · subst hd
            exact Or.inr rfl
          · exact (hkd ⟨kd, hk0, hd⟩).elim
      obtain ⟨s, ls, he, hf⟩ := outsOfKind_head_inv hk h
      have hs : s ≠ ``Sparkle.Core.Signal.Signal := by
        intro hh
        subst hh
        exact hf NS
      have he' := inst_getAppFn j a s ls e he
      have hk' : mixedGateBinderKind? (inst1M e j a) = none ∨
          mixedGateBinderKind? (inst1M e j a) = some .domain := by
        cases hk0 : mixedGateBinderKind? (inst1M e j a) with
        | none => exact Or.inl rfl
        | some kd =>
          cases kd with
          | domain => exact Or.inr rfl
          | bool =>
            obtain ⟨us, hh⟩ := kind_head hk0 (by intro hh; cases hh)
            rw [hh] at he'
            injection he' with h1 h1b
            exact absurd h1.symm hs
          | bits w =>
            obtain ⟨us, hh⟩ := kind_head hk0 (by intro hh; cases hh)
            rw [hh] at he'
            injection he' with h1 h1b
            exact absurd h1.symm hs
      have hnf' : ∀ (n : Name) (d b : Lean.Expr) (bi : BinderInfo),
          inst1M e j a ≠ .forallE n d b bi := by
        intro n d b bi hh
        rw [hh] at he'
        first
          | cases he'
          | simp [Lean.Expr.getAppFn] at he'
      have hnp' : ¬ ∃ (us : List Lean.Level) (x y : Lean.Expr),
          inst1M e j a = .app (.app (.const ``Prod us) x) y := by
        rintro ⟨us, x, y, hh⟩
        exact hp ⟨us, inst_prod_inv j a e he hh⟩
      rw [outs_nonprod senv hnf' hnp', outsOfKind_eq senv hk hk' (he'.trans he.symm)]
      exact h

/-- **`outs`, generalised over the binder depth.** -/
theorem outs_inst (senv : StructEnv) (NS : senv.fields ``Sparkle.Core.Signal.Signal = none)
    (a : Lean.Expr) :
    ∀ (b : Lean.Expr) (j : Nat) (o : Option Name × List (String × MixedGateBinder)),
      machOuts? senv b = some o → machOuts? senv (inst1M b j a) = some o := by
  intro b
  induction b with
  | forallE n d body bi _ ih =>
    intro j o h
    rw [machOuts?_forall] at h
    rw [inst1M_forallE, machOuts?_forall]
    exact ih (j + 1) o h
  | _ =>
    intro j o h
    exact outs_inst_nf senv NS a j (by intro n d b bi hh; cases hh) h

/-! ## `InstSubst` for the model, and the boundary -/

/-- `InstSubst` with `Expr.instantiate1` replaced by the model. -/
structure InstSubstM : Prop where
  outs : ∀ (senv : StructEnv), senv.fields ``Sparkle.Core.Signal.Signal = none →
    ∀ (b a : Lean.Expr) (o : Option Name × List (String × MixedGateBinder)),
      machOuts? senv b = some o → machOuts? senv (inst1M b 0 a) = some o
  head : ∀ (b a : Lean.Expr) (s : Name) (ls : List Lean.Level),
    (resBody b).getAppFn = .const s ls → (resBody (inst1M b 0 a)).getAppFn = .const s ls

/-- **PROVED**: both clauses hold for the model (no hypothesis). -/
theorem instSubstM : InstSubstM :=
  ⟨fun senv NS b a o h => outs_inst senv NS a b 0 o h,
   fun b a s ls h => head_inst a s ls b 0 h⟩

/-- **The runtime-agreement boundary** (explicit, NOT established, NOT
trusted): the extern `Expr.instantiate1` computes the model. Testable by
shadow `#eval` on sample terms (structural `Expr` equality); not decidable
in the logic, since `instantiate1` is opaque. -/
def InstAgree : Prop := ∀ b a : Lean.Expr, b.instantiate1 a = inst1M b 0 a

/-- `InstSubst` from the boundary and the proved model. -/
theorem instSubst_of_agree (A : InstAgree) : InstSubst :=
  ⟨fun senv NS b a o h => by
      rw [A]
      exact instSubstM.outs senv NS b a o h,
   fun b a s ls h => by
      rw [A]
      exact instSubstM.head b a s ls h⟩

end Tools.ShippingInstSubstModel
