import Tools.ShippingInlTypeFacts
import Tools.ShippingReaderResultKind

/-! # L2: the candidate inliner keeps the one-Signal result kind of a `∀` type (unit U4, L2 only)

BUILT by the integrator: ic5 exit 0 (the four candidate files; fixes after ic1/ic4 recorded in
`docs/parallel/O-origin-integration.md`), committed in 2cbe8c45, axioms audited in
`Tests.Compiler.InlCandAuditTest` (ic6). Written by worker O-INLC (branch par/o-inlc, base a230f9d1) without
running Lean; writing-time guesses decided by the build. No `sorry`, no axiom, no `native_decide`. Nothing added to
`RefLaws` or any trust / allowed-premise list. Production unchanged.

    resKind_userInlinerC :
      ReadConstsPlain env → ty.isForall = true → machResultKind? ty = some k →
      machResultKind? (userInlinerC env ty) = some k

This is the FORWARD direction, the one `P5At` (Tools/ShippingCallWidthsChildReal.lean 147) needs
(the declared kind is `ResDeclAt`; P5 asks for the same kind after the inliner).

Premise accounting for L2 (candidate inliner only):

| ingredient | status |
|---|---|
| `relevantClosure` (`partial`) | not needed: Bool case split (`split`), both branches handled |
| `passM` (`partial`) | not reached: `passF (999999+1)` takes its trivial `∀` arm (`passT_forallE`) |
| `Expr.eqv` (opaque `==`) in `roundsC` / `inlAbbrevsC` | not needed: case split on the Bool |
| `Expr.replace` (extern) | not reached on `∀` inputs (`abbrevStep` uses `replaceNoCache`) |
| `Expr.headBeta` / `betaRev` (`partial`) | not reached: `headBeta` of a `∀` is itself |
| library constants not user abbreviations | LOCALISED: explicit premise `ReadConstsPlain env` (six `userAbbrev? env c = none` facts) |
| `ty.isForall = true` | premise (callees with at least one binder; zero-binder callees are NOT covered) |

What this is NOT: a statement about production `userInliner` (that needs the switch, plus the OPEN
agreement of `replaceNoCache` with the extern `replace`, and the runtime-only compatibility
`passF ≈ passM`); nor L1 (`declOuts?`, structure results). -/
namespace Tools.ShippingInlTypeReads
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingInlCand Tools.ShippingInlTypeFacts
open Tools.ShippingReaderResultKind (kind_inv machResultKind?_inv)

/-! ## The structural replace keeps the result kind -/

/-- At the end of the telescope (`Signal dom Bool` / `Signal dom (BitVec w)` with `w` a canonical
literal): the replace only touches the domain, which the kind does not read. -/
theorem resKind_rnc_base (env : Environment) (hR : ReadConstsPlain env) {ty : Lean.Expr}
    {k : MixedGateBinder}
    (hnf : ∀ n d b bi, ty ≠ Lean.Expr.forallE n d b bi) (h : machResultKind? ty = some k) :
    machResultKind? (Lean.Expr.replaceNoCache (abbrevFn env) ty) = some k := by
  obtain ⟨hk, hd⟩ := machResultKind?_inv h hnf
  rcases kind_inv hk hd with ⟨us, dom, us', rfl, rfl⟩ | ⟨us, dom, us', wE, n, rfl, rfl⟩
  · rw [rnc_app, rnc_app, rnc_const env hR.signal, rnc_const env hR.bool]
    exact (resKind_sig_bool_dom us dom _ us').symm.trans h
  · rw [kind_bits_eq] at hk
    obtain ⟨m, hm, -⟩ := Option.bind_eq_some_iff.mp hk
    rw [rnc_app, rnc_app, rnc_app, rnc_const env hR.signal, rnc_const env hR.bitVec,
      rnc_canon env hR hm]
    exact (resKind_sig_bits_dom us dom _ us' wE).symm.trans h

/-- The structural replace keeps `machResultKind?` under any telescope. -/
theorem resKind_rnc (env : Environment) (hR : ReadConstsPlain env) (ty : Lean.Expr) :
    ∀ k, machResultKind? ty = some k →
      machResultKind? (Lean.Expr.replaceNoCache (abbrevFn env) ty) = some k := by
  induction ty with
  | forallE n d b bi _ ih =>
    intro k h
    rw [rnc_forallE]
    first
      | exact ih k h
      | (simp only [machResultKind?] at h ⊢; exact ih k h)
  | _ =>
    intro k h
    exact resKind_rnc_base env hR (by intro n d b bi hh; cases hh) h

/-! ## `inlFoldNat` keeps the result kind -/

theorem resKind_fold_base {ty : Lean.Expr} {k : MixedGateBinder}
    (hnf : ∀ n d b bi, ty ≠ Lean.Expr.forallE n d b bi) (h : machResultKind? ty = some k) :
    machResultKind? (inlFoldNat ty) = some k := by
  obtain ⟨hk, hd⟩ := machResultKind?_inv h hnf
  rcases kind_inv hk hd with ⟨us, dom, us', rfl, rfl⟩ | ⟨us, dom, us', wE, n, rfl, rfl⟩
  · rw [fold_sig, fold_const]
    exact (resKind_sig_bool_dom us dom _ us').symm.trans h
  · rw [kind_bits_eq] at hk
    obtain ⟨m, hm, -⟩ := Option.bind_eq_some_iff.mp hk
    rw [fold_sig, fold_bitVec, fold_canon hm]
    exact (resKind_sig_bits_dom us dom _ us' wE).symm.trans h

/-- `inlFoldNat` keeps `machResultKind?` under any telescope (no premise). -/
theorem resKind_fold (ty : Lean.Expr) :
    ∀ k, machResultKind? ty = some k → machResultKind? (inlFoldNat ty) = some k := by
  induction ty with
  | forallE n d b bi _ ih =>
    intro k h
    rw [fold_forallE]
    first
      | exact ih k h
      | (simp only [machResultKind?] at h ⊢; exact ih k h)
  | _ =>
    intro k h
    exact resKind_fold_base (by intro n d b bi hh; cases hh) h

/-! ## `inlAbbrevsC` on a `∀` -/

/-- Every round of `inlAbbrevsC` on a `∀` either stops (opaque `==` true) or continues on a `∀`
with the same result kind (`abbrevStep_forallE`, `headBeta_forallE`, `resKind_rnc`). -/
theorem inlAbbrevsC_forallE (env : Environment) (hR : ReadConstsPlain env) {k : MixedGateBinder}
    (m : Nat) :
    ∀ (n : Name) (d b : Lean.Expr) (bi : BinderInfo), machResultKind? b = some k →
      machResultKind? (inlAbbrevsC env m (.forallE n d b bi)) = some k := by
  induction m with
  | zero =>
    intro n d b bi h
    first
      | exact h
      | (show machResultKind? (Lean.Expr.forallE n d b bi) = some k
         first | exact h | (simp only [machResultKind?]; exact h))
  | succ m ih =>
    intro n d b bi h
    have hu : inlAbbrevsC env (m + 1) (.forallE n d b bi) =
        (if abbrevStep env (.forallE n d b bi) == Lean.Expr.forallE n d b bi then
            Lean.Expr.forallE n d b bi
          else inlAbbrevsC env m (abbrevStep env (.forallE n d b bi)).headBeta) := by
      first
        | rfl
        | (rw [inlAbbrevsC])
        | (simp only [inlAbbrevsC])
    rw [hu, abbrevStep_forallE]
    split
    · first | exact h | (simp only [machResultKind?]; exact h)
    · rw [headBeta_forallE]
      exact ih n _ _ bi (resKind_rnc env hR b k h)

/-! ## L2 -/

/-- **L2 on an explicit `∀`.** The candidate inliner keeps the declared one-Signal result kind.
Localised premise: `ReadConstsPlain env`. -/
theorem resKind_userInlinerC_forallE (env : Environment) (hR : ReadConstsPlain env)
    (n : Name) (d b : Lean.Expr) (bi : BinderInfo) {k : MixedGateBinder}
    (h : machResultKind? (.forallE n d b bi) = some k) :
    machResultKind? (userInlinerC env (.forallE n d b bi)) = some k := by
  have hb : machResultKind? b = some k := by
    first | exact h | (simp only [machResultKind?] at h; exact h)
  have hF : machResultKind? (inlFoldNat (inlAbbrevsC env 4 (.forallE n d b bi))) = some k :=
    resKind_fold _ k (inlAbbrevsC_forallE env hR 4 n d b bi hb)
  have hu : userInlinerC env (.forallE n d b bi) =
      (if Sparkle.Compiler.MachRecUnfold.relevantClosure (userDefinition? env) (isRecC env) (.forallE n d b bi) then
          inlFoldNat (inlAbbrevsC env 4 (roundsC env 64 (inlC env (.forallE n d b bi))))
        else inlFoldNat (inlAbbrevsC env 4 (inlC env (.forallE n d b bi)))) := by
    first
      | rfl
      | (unfold userInlinerC; rfl)
      | (simp only [userInlinerC])
  rw [hu, inlC_forallE, roundsC_forallE]
  split <;> exact hF

/-- **L2** (`isForall` form, the one `P5At` consumers have). -/
theorem resKind_userInlinerC (env : Environment) (hR : ReadConstsPlain env) (ty : Lean.Expr)
    (hf : ty.isForall = true) {k : MixedGateBinder} (h : machResultKind? ty = some k) :
    machResultKind? (userInlinerC env ty) = some k := by
  cases ty with
  | forallE n d b bi => exact resKind_userInlinerC_forallE env hR n d b bi h
  | _ =>
    first
      | cases hf
      | (simp [Lean.Expr.isForall] at hf)
      | exact absurd hf (by decide)

end Tools.ShippingInlTypeReads
