import Tools.ShippingInlCand

/-! # Expr facts for the candidate inliner on `∀` types (unit U3, scope: what L2 needs)

UNBUILT at the time of writing (worker O-INLC, branch par/o-inlc, base a230f9d1; written without
running Lean; spots marked `-- UNSURE` are guesses about elaboration that the integrator's build
decides, most with `first | …` fallbacks). No `sorry`, no axiom, no `native_decide`. Nothing is added
to `RefLaws` or any trust / allowed-premise list. Production is unchanged.

Contents (all about the CANDIDATE definitions of `Tools.ShippingInlCand` and total production `def`s):

* `Expr.replaceNoCache` (structural core `def`) with the candidate replacement `abbrevFn env`:
  `rnc_forallE`, `rnc_app`, `rnc_lit`, `rnc_const` (the last under `userAbbrev? env c = none`);
* `Expr.headBeta` on a `∀`: `headBeta_forallE`;
* `inlineDefs` / `inlC` on a `∀`: `inlineDefs_forall_succ`, `inlineDefs_forallE_depth`, `inlC_forallE`;
* `passF` / `passT` on a `∀` (the trivial arm after an empty-memo miss): `passF_succ_forallE`,
  `passT_forallE`;
* `roundsC` fixes a `∀` WHATEVER the opaque `Expr.eqv` answers: `roundsC_forallE`;
* `abbrevStep` on a `∀` is the structural replace: `abbrevStep_forallE`;
* `inlFoldNat` on the reading skeleton: `fold_forallE`, `fold_sig`, `fold_const`, `fold_bitVec`;
* the canonical `Nat` literal (`canonicalNatLitValue?`): `canon_inv`, and that both
  `replaceNoCache (abbrevFn env)` (under `ReadConstsPlain env`) and `inlFoldNat` fix it.

Nothing here is about `Expr.replace` (extern `replaceImpl`) or about `passM` (opaque `partial`):
those are never reached on a `∀` input of the candidate. -/
namespace Tools.ShippingInlTypeFacts
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingInlCand

/-! ## `replaceNoCache` -/

/-- One step of `replaceNoCache` at a `∀` node the replacement skips. -/
theorem rnc_forallE' (f : Lean.Expr → Option Lean.Expr) (n : Name) (d b : Lean.Expr)
    (bi : BinderInfo) (hf : f (.forallE n d b bi) = none) :
    Lean.Expr.replaceNoCache f (.forallE n d b bi) =
      .forallE n (Lean.Expr.replaceNoCache f d) (Lean.Expr.replaceNoCache f b) bi := by
  -- UNSURE: shape of the equation lemma of the core `def` (single unfold equation expected)
  first
    | (rw [Lean.Expr.replaceNoCache.eq_def, hf]; rfl)
    | (rw [Lean.Expr.replaceNoCache.eq_def, hf])
    | (rw [Lean.Expr.replaceNoCache, hf]; rfl)
    | (rw [Lean.Expr.replaceNoCache, hf])

/-- One step of `replaceNoCache` at an application node the replacement skips. -/
theorem rnc_app' (f : Lean.Expr → Option Lean.Expr) (a b : Lean.Expr)
    (hf : f (.app a b) = none) :
    Lean.Expr.replaceNoCache f (.app a b) =
      .app (Lean.Expr.replaceNoCache f a) (Lean.Expr.replaceNoCache f b) := by
  first
    | (rw [Lean.Expr.replaceNoCache.eq_def, hf]; rfl)
    | (rw [Lean.Expr.replaceNoCache.eq_def, hf])
    | (rw [Lean.Expr.replaceNoCache, hf]; rfl)
    | (rw [Lean.Expr.replaceNoCache, hf])

/-- A leaf the replacement skips is kept (`| e => e` arm). Stated for constants. -/
theorem rnc_const' (f : Lean.Expr → Option Lean.Expr) (c : Name) (ls : List Level)
    (hf : f (.const c ls) = none) :
    Lean.Expr.replaceNoCache f (.const c ls) = .const c ls := by
  first
    | (rw [Lean.Expr.replaceNoCache.eq_def, hf]; rfl)
    | (rw [Lean.Expr.replaceNoCache.eq_def, hf])
    | (rw [Lean.Expr.replaceNoCache, hf]; rfl)
    | (rw [Lean.Expr.replaceNoCache, hf])

section AbbrevFn
variable (env : Environment)

theorem rnc_forallE (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    Lean.Expr.replaceNoCache (abbrevFn env) (.forallE n d b bi) =
      .forallE n (Lean.Expr.replaceNoCache (abbrevFn env) d)
        (Lean.Expr.replaceNoCache (abbrevFn env) b) bi :=
  rnc_forallE' (abbrevFn env) n d b bi rfl

theorem rnc_app (a b : Lean.Expr) :
    Lean.Expr.replaceNoCache (abbrevFn env) (.app a b) =
      .app (Lean.Expr.replaceNoCache (abbrevFn env) a) (Lean.Expr.replaceNoCache (abbrevFn env) b) :=
  rnc_app' (abbrevFn env) a b rfl

theorem rnc_lit (l : Literal) :
    Lean.Expr.replaceNoCache (abbrevFn env) (.lit l) = .lit l := by
  first
    | rfl
    | (rw [Lean.Expr.replaceNoCache.eq_def]; rfl)
    | (rw [Lean.Expr.replaceNoCache.eq_def])

/-- `abbrevFn env` skips a constant that is not a user abbreviation (any universe list:
a non-empty one is skipped by the pattern `.const c []` already). -/
theorem abbrevFn_const {c : Name} (hc : userAbbrev? env c = none) (ls : List Level) :
    abbrevFn env (.const c ls) = none := by
  cases ls with
  | nil =>
    first
      | exact hc
      | (simp only [abbrevFn]; exact hc)
      | simpa [abbrevFn] using hc
  | cons _ _ => rfl

theorem rnc_const {c : Name} (hc : userAbbrev? env c = none) (ls : List Level) :
    Lean.Expr.replaceNoCache (abbrevFn env) (.const c ls) = .const c ls :=
  rnc_const' (abbrevFn env) c ls (abbrevFn_const env hc ls)

end AbbrevFn

/-! ## `headBeta` -/

/-- `headBeta` leaves a `∀` alone (`isHeadBetaTargetFn false (.forallE ..) = false`; the
`partial` `betaRev` is not reached). -/
theorem headBeta_forallE (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    (Lean.Expr.forallE n d b bi).headBeta = .forallE n d b bi := by
  first
    | rfl
    | simp [Lean.Expr.headBeta, Lean.Expr.getAppFn, Lean.Expr.isHeadBetaTargetFn]

/-! ## `inlineDefs` / `inlC` -/

/-- `inlineDefs` never descends into a `∀`: last arm, empty spine. (It spends one unit of
budget.) -/
theorem inlineDefs_forall_succ (defs : Name → Option Lean.Expr)
    (projs : Name → Option (Name × Nat × Nat)) (fuel bud : Nat)
    (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    inlineDefs defs projs (fuel + 1) (.forallE n d b bi) (bud + 1) =
      some (.forallE n d b bi, bud) := by
  first
    | rfl
    | (unfold inlineDefs; rfl)
    | (simp only [inlineDefs, inlSpine, inlMap, List.foldl])
    | (rw [inlineDefs]; rfl)

theorem inlineDefs_forallE_depth (defs : Name → Option Lean.Expr)
    (projs : Name → Option (Name × Nat × Nat))
    (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    inlineDefs defs projs inlineDepth (.forallE n d b bi) inlineBudget =
      some (.forallE n d b bi, 15999999) :=
  -- `inlineDepth = 4095 + 1`, `inlineBudget = 15999999 + 1` by `Nat` literal defeq
  inlineDefs_forall_succ defs projs 4095 15999999 n d b bi

theorem inlC_forallE (env : Environment) (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    inlC env (.forallE n d b bi) = .forallE n d b bi := by
  unfold inlC
  rw [inlineDefs_forallE_depth]
  try rfl

/-! ## `passF` / `passT` -/

/-- `passF (k+1)` on a `∀` that misses the memo: the trivial arm `| e => pure e`, then the memo
write. -/
theorem passF_succ_forallE (env : Environment) (nl : Lean.Expr → Option Nat) (iu : Name → Bool)
    (k : Nat) (n : Name) (d b : Lean.Expr) (bi : BinderInfo)
    (s : Std.HashMap Lean.Expr Lean.Expr)
    (hs : s.get? (Lean.Expr.forallE n d b bi) = none) :
    (passF env nl iu (k + 1) (.forallE n d b bi)).run s =
      (Lean.Expr.forallE n d b bi, s.insert (.forallE n d b bi) (.forallE n d b bi)) := by
  -- `passF (k+1)` unfolds to the memo lookup (`get`, then a match on `get?`), the trivial arm and
  -- the memo write; the StateT `run` lemmas reduce it in `Id`
  unfold passF
  first
    | (simp only [StateT.run_bind, StateT.run_get, pure_bind, hs, StateT.run_pure, StateT.run_modify,
        bind_pure_comp, map_pure]; rfl)
    | (simp only [StateT.run_bind, StateT.run_get, pure_bind, hs, StateT.run_pure, StateT.run_modify,
        bind_pure_comp, map_pure])
    | (simp [hs]; rfl)
    | simp [hs]

/-- **`passT` fixes a `∀`.** No `partial` value is used: fuel `passDepth = 999999 + 1`, empty
memo (`Std.HashMap.getElem?_empty`, which needs only `BEq` / `Hashable`, so the opaque
`Expr.eqv` is irrelevant). -/
theorem passT_forallE (env : Environment) (nl : Lean.Expr → Option Nat) (iu : Name → Bool)
    (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    passT env nl iu (.forallE n d b bi) = .forallE n d b bi := by
  have hs : (∅ : Std.HashMap Lean.Expr Lean.Expr).get? (Lean.Expr.forallE n d b bi) = none := by
    first
      | exact Std.HashMap.getElem?_empty
      | (rw [Std.HashMap.get?_eq_getElem?]; exact Std.HashMap.getElem?_empty)
      | simp
  have h := passF_succ_forallE env nl iu 999999 n d b bi ∅ hs
  have e1 : passT env nl iu (.forallE n d b bi) =
      Prod.fst ((passF env nl iu (999999 + 1) (.forallE n d b bi)).run ∅) := by
    -- UNSURE: `StateT.run'` in `Id` is `Prod.fst` of `run` by defeq; `passDepth = 999999 + 1`
    first
      | rfl
      | (unfold passT passDepth; rfl)
      | (simp only [passT, passDepth, StateT.run'_eq]; rfl)
  rw [e1, h]
  try rfl

/-! ## `roundsC` -/

/-- **`roundsC` fixes a `∀`**, whatever the opaque `==` answers: `passT` returns the input; if
`==` says equal the input is returned, otherwise `roundsC k (inlC e)` with `inlC e = e`. -/
theorem roundsC_forallE (env : Environment) (k : Nat) (n : Name) (d b : Lean.Expr)
    (bi : BinderInfo) :
    roundsC env k (.forallE n d b bi) = .forallE n d b bi := by
  induction k with
  | zero => first | rfl | simp only [roundsC]
  | succ k ih =>
    have hu : roundsC env (k + 1) (.forallE n d b bi) =
        (if passT env canonicalNatLitValue? (isRecC env) (.forallE n d b bi) ==
            Lean.Expr.forallE n d b bi then Lean.Expr.forallE n d b bi
          else roundsC env k
            (inlC env (passT env canonicalNatLitValue? (isRecC env) (.forallE n d b bi)))) := by
      first
        | rfl
        | (rw [roundsC])
        | (simp only [roundsC])
    rw [hu, passT_forallE]
    split
    · rfl
    · rw [inlC_forallE]; exact ih

/-! ## `abbrevStep` -/

/-- On a `∀` the candidate abbreviation step is the STRUCTURAL replace. -/
theorem abbrevStep_forallE (env : Environment) (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    abbrevStep env (.forallE n d b bi) =
      .forallE n (Lean.Expr.replaceNoCache (abbrevFn env) d)
        (Lean.Expr.replaceNoCache (abbrevFn env) b) bi := by
  have h : abbrevStep env (.forallE n d b bi) =
      Lean.Expr.replaceNoCache (abbrevFn env) (.forallE n d b bi) := by
    first
      | rfl
      | (simp only [abbrevStep, Lean.Expr.isForall, if_true, ite_true])
      | (unfold abbrevStep; simp [Lean.Expr.isForall])
  rw [h, rnc_forallE]

/-! ## `inlFoldNat` on the reading skeleton -/

theorem fold_forallE (n : Name) (d b : Lean.Expr) (bi : BinderInfo) :
    inlFoldNat (.forallE n d b bi) = .forallE n (inlFoldNat d) (inlFoldNat b) bi := by
  first | rfl | simp only [inlFoldNat]

theorem fold_const (c : Name) (ls : List Level) : inlFoldNat (.const c ls) = .const c ls := by
  first | rfl | simp only [inlFoldNat]

theorem fold_lit (l : Literal) : inlFoldNat (.lit l) = .lit l := by
  first | rfl | simp only [inlFoldNat]

/-- `Signal dom X`: no foldable sum at the two application nodes (`inlNatSum?` needs six). -/
theorem fold_sig (us : List Level) (dom X : Lean.Expr) :
    inlFoldNat (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom) X) =
      .app (.app (.const ``Sparkle.Core.Signal.Signal us) (inlFoldNat dom)) (inlFoldNat X) := by
  -- UNSURE: `rfl` must reduce `inlNatSum?` on a two-node spine with a constant head
  first
    | rfl
    | simp [inlFoldNat, inlNatSum?]

theorem fold_bitVec (us : List Level) (w : Lean.Expr) :
    inlFoldNat (.app (.const ``BitVec us) w) = .app (.const ``BitVec us) (inlFoldNat w) := by
  first
    | rfl
    | simp [inlFoldNat, inlNatSum?]

/-! ## The canonical `Nat` literal -/

/-- The two shapes `canonicalNatLitValue?` accepts, with the names written as in
`ReadConstsPlain`. -/
theorem canon_inv {w : Lean.Expr} {m : Nat} (h : canonicalNatLitValue? w = some m) :
    w = .lit (.natVal m) ∨
      ∃ l1 l2 l3, w = .app (.app (.app (.const ``OfNat.ofNat l1) (.const ``Nat l2))
        (.lit (.natVal m))) (.app (.const ``instOfNatNat l3) (.lit (.natVal m))) := by
  unfold canonicalNatLitValue? at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h
      -- UNSURE: the `if` condition hypothesis is inaccessible; `simp … at *` reaches it
      first
        | (simp only [beq_iff_eq] at *; subst_vars; exact Or.inr ⟨_, _, _, rfl⟩)
        | (simp at *; subst_vars; exact Or.inr ⟨_, _, _, rfl⟩)
        | (rename_i hc; have hk := Nat.eq_of_beq_eq_true hc; subst hk; exact Or.inr ⟨_, _, _, rfl⟩)
    · cases h
  · cases h

/-- The structural replace fixes a canonical `Nat` literal (localised premise:
`ReadConstsPlain env`). -/
theorem rnc_canon (env : Environment) (hR : ReadConstsPlain env) {w : Lean.Expr} {m : Nat}
    (h : canonicalNatLitValue? w = some m) :
    Lean.Expr.replaceNoCache (abbrevFn env) w = w := by
  rcases canon_inv h with rfl | ⟨l1, l2, l3, rfl⟩
  · exact rnc_lit env _
  · simp only [rnc_app, rnc_lit, rnc_const env hR.ofNat, rnc_const env hR.nat,
      rnc_const env hR.instOfNatNat]

/-- `inlFoldNat` fixes a canonical `Nat` literal (no premise). -/
theorem fold_canon {w : Lean.Expr} {m : Nat} (h : canonicalNatLitValue? w = some m) :
    inlFoldNat w = w := by
  rcases canon_inv h with rfl | ⟨l1, l2, l3, rfl⟩
  · exact fold_lit _
  · -- UNSURE: `rfl` reduces `inlNatSum?` on the four application nodes (it needs six)
    first
      | rfl
      | simp [inlFoldNat, inlNatSum?]

/-! ## `mixedGateBinderKind?` / `machResultKind?` on the reading skeleton -/

/-- The bits kind is decided by the width literal alone. -/
theorem kind_bits_eq (us : List Level) (dom : Lean.Expr) (us' : List Level) (wE : Lean.Expr) :
    mixedGateBinderKind? (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom)
        (.app (.const ``BitVec us') wE)) =
      (canonicalNatLitValue? wE).bind fun n => if 0 < n then some (MixedGateBinder.bits n) else none := by
  first
    | rfl
    | simp [mixedGateBinderKind?, Lean.Expr.isConstOf]

/-- `machResultKind?` of a Bool Signal does not read the domain argument. -/
theorem resKind_sig_bool_dom (us : List Level) (dom dom' : Lean.Expr) (us' : List Level) :
    machResultKind? (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom) (.const ``Bool us')) =
      machResultKind? (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom')
        (.const ``Bool us')) := by
  first
    | rfl
    | simp [machResultKind?, mixedGateBinderKind?, Lean.Expr.isConstOf]

/-- `machResultKind?` of a BitVec Signal does not read the domain argument. -/
theorem resKind_sig_bits_dom (us : List Level) (dom dom' : Lean.Expr) (us' : List Level)
    (wE : Lean.Expr) :
    machResultKind? (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom)
        (.app (.const ``BitVec us') wE)) =
      machResultKind? (.app (.app (.const ``Sparkle.Core.Signal.Signal us) dom')
        (.app (.const ``BitVec us') wE)) := by
  -- UNSURE: `rfl` must see both sides reduce to the same term stuck on `canonicalNatLitValue? wE`
  first
    | rfl
    | simp [machResultKind?, mixedGateBinderKind?, Lean.Expr.isConstOf]

end Tools.ShippingInlTypeFacts
