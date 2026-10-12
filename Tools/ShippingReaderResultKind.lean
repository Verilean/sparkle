import Sparkle.Compiler.Elab

/-! # P2 — the one-Signal result reader agrees with the structure reader

`docs/parallel/B-callkinds.md` §7, invariant P2, proved in full (no
restriction to literal shapes was needed): both `machResultKind?` and
`machOuts?` are structural recursions on `Lean.Expr` (NOT `partial`), so
they have equations.

    machResultKind? ty = some k  →
      machTupleKinds? ty = none ∧ machOuts? senv ty = some (none, [("out", k)])

i.e. when the parent's reader takes the one-Signal path for a callee
(`instSignature?`, whose result kind is `machResultKind? ci.type`), the
child's own reader — `machineShape?`, which reads its outputs by
`machTupleKinds?` first and `machOuts?` otherwise — finds ONE output named
`out` of the SAME kind, whatever the structure environment `senv` is.

What this is not: nothing here speaks of `Expr.instantiate1` (P3), of
`userInliner` (P5) or of the `partial` readers (R1–R4).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingReaderResultKind
open Lean
open Sparkle.Compiler.Elab

/-- A hardware binder type that is not the domain is syntactically
`Signal dom Bool` or `Signal dom (BitVec w)`. -/
theorem kind_inv {ty : Lean.Expr} {k : MixedGateBinder}
    (h : mixedGateBinderKind? ty = some k) (hk : k ≠ .domain) :
    (∃ us dom us', ty = Lean.Expr.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom)
        (.const ``Bool us') ∧ k = .bool) ∨
    (∃ us dom us' wE n, ty = Lean.Expr.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom)
        (.app (.const ``BitVec us') wE) ∧ k = .bits n) := by
  unfold mixedGateBinderKind? at h
  split at h
  · cases h; exact absurd rfl hk
  · split at h
    · cases h
      first
        | exact Or.inl ⟨_, _, _, rfl, rfl⟩
        | (subst_vars; exact Or.inl ⟨_, _, _, rfl, rfl⟩)
        | exact Or.inl ⟨_, _, _, by assumption, rfl⟩
    · obtain ⟨m, _, hm⟩ := Option.bind_eq_some_iff.mp h
      split at hm
      · cases hm
        first
          | exact Or.inr ⟨_, _, _, _, _, rfl, rfl⟩
          | (subst_vars; exact Or.inr ⟨_, _, _, _, _, rfl, rfl⟩)
          | exact Or.inr ⟨_, _, _, _, _, by assumption, rfl⟩
      · cases hm
    · cases h

/-- The last alternative of `machOuts?` (same text), as a function of its
own: what `machOuts?` is on a type that is neither a `∀` nor a `Prod`. -/
def outsOfKind (senv : StructEnv) (e : Lean.Expr) :
    Option (Option Name × List (String × MixedGateBinder)) :=
  match mixedGateBinderKind? e with
  | some .bool => some (none, [("out", .bool)])
  | some (.bits n) => some (none, [("out", .bits n)])
  | _ =>
    match e.getAppFn with
    | .const s _ => (senv.fields s).map fun (ctor, fs) => (some ctor, fs)
    | _ => none

/-- On a `Signal dom α` type `machOuts?` takes its last alternative (the
type is not a `∀`, and its head constant is `Signal`, not `Prod`). -/
theorem machOuts?_signal (senv : StructEnv) (us : List Level) (dom α : Lean.Expr) :
    machOuts? senv (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom) α) =
      outsOfKind senv (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom) α) := by
  first
    | rfl
    | (unfold outsOfKind; rfl)
    | simp [machOuts?, outsOfKind]

theorem machTupleKinds?_bool (us : List Level) (dom : Lean.Expr) (us' : List Level) :
    machTupleKinds? (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom)
      (.const ``Bool us')) = none := by
  first | rfl | simp [machTupleKinds?]

theorem machTupleKinds?_bits (us : List Level) (dom : Lean.Expr) (us' : List Level)
    (wE : Lean.Expr) :
    machTupleKinds? (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom)
      (.app (.const ``BitVec us') wE)) = none := by
  first | rfl | simp [machTupleKinds?]

/-- A type with a non-domain hardware kind: not a tuple result, and the
structure reader returns the one port `out` of that kind. -/
theorem outs_of_kind (senv : StructEnv) {ty : Lean.Expr} {k : MixedGateBinder}
    (h : mixedGateBinderKind? ty = some k) (hk : k ≠ .domain) :
    machTupleKinds? ty = none ∧ machOuts? senv ty = some (none, [("out", k)]) := by
  rcases kind_inv h hk with ⟨us, dom, us', rfl, rfl⟩ | ⟨us, dom, us', wE, n, rfl, rfl⟩
  · exact ⟨machTupleKinds?_bool us dom us', by simp only [machOuts?_signal, outsOfKind, h]⟩
  · exact ⟨machTupleKinds?_bits us dom us' wE, by simp only [machOuts?_signal, outsOfKind, h]⟩

/-- `machResultKind?` on a type that is not a `∀`: the kind of the type
itself, and it is not the domain. -/
theorem machResultKind?_inv {ty : Lean.Expr} {k : MixedGateBinder}
    (h : machResultKind? ty = some k)
    (hnf : ∀ n d b bi, ty ≠ Lean.Expr.forallE n d b bi) :
    mixedGateBinderKind? ty = some k ∧ k ≠ .domain := by
  unfold machResultKind? at h
  split at h
  · exact absurd rfl (hnf _ _ _ _)
  · split at h
    · cases h; exact ⟨by assumption, by intro hh; cases hh⟩
    · cases h; exact ⟨by assumption, by intro hh; cases hh⟩
    · cases h

/-- **P2.** The one-Signal reader agrees with the structure reader, under
any telescope and for any structure environment. -/
theorem machOuts?_of_resultKind (senv : StructEnv) (ty : Lean.Expr) :
    ∀ k, machResultKind? ty = some k →
      machTupleKinds? ty = none ∧ machOuts? senv ty = some (none, [("out", k)]) := by
  induction ty with
  | forallE n d b bi _ ih =>
    intro k h
    first
      | exact ih k h
      | (simp only [machResultKind?] at h
         simp only [machTupleKinds?, machOuts?]
         exact ih k h)
  | _ =>
    intro k h
    obtain ⟨hk, hd⟩ := machResultKind?_inv h (by intro n d b bi hh; cases hh)
    exact outs_of_kind senv hk hd

/-- The kind a one-Signal result has is never the domain. -/
theorem machResultKind?_ne_domain (ty : Lean.Expr) :
    ∀ k, machResultKind? ty = some k → k ≠ .domain := by
  induction ty with
  | forallE n d b bi _ ih =>
    intro k h
    first
      | exact ih k h
      | (simp only [machResultKind?] at h; exact ih k h)
  | _ =>
    intro k h
    exact (machResultKind?_inv h (by intro n d b bi hh; cases hh)).2

/-- The layout output list of ONE port. -/
theorem machOutFields_single (W : Nat) (nm : String) (k : MixedGateBinder) :
    machOutFields W [(nm, k)] =
      [{ name := nm, lo := W, width := machWidth k, ty := machHWType k }] := by
  first | rfl | simp [machOutFields]

end Tools.ShippingReaderResultKind
