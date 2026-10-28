import Tools.Prototype.ReaderFixpointSpec

/-! # Unit LC13: `LetOk` preservation of the TOTAL preprocessing defs, connected to `ShapeInOk`

BUILT: runs l1–l3 exit 1 (syntax), l4 exit 0 (four lemmas), l5 exit 1, l6 exit 0 (final). No sorry / axiom / native_decide.

One lemma per def of the wrapper's preprocessing (`shapeMid`): `inlFoldNat`, `zeroLit`, `machLoopAsLet`, `machRoot`.
`zeroLit` is a TOTAL def but its body is the `@[extern]` `Expr.replace`, whose compiled behaviour is not visible to proofs; its
`LetOk` preservation is therefore PROVED for the structural `replaceNoCache` and the link
`zeroLit … = replaceNoCache …` is the named PREMISE `ZeroLitAgrees` (NOT proved).  No counterexample was found.
PROVED without premises for `inlFoldNat`, `machLoopAsLet`, `machRoot`; for the shipped `zeroLit` the preservation is
CONDITIONAL on the unproved `ZeroLitAgrees` (correspondence NOT proved), so "every def preserves `LetOk`" is NOT claimed. -/
namespace Tools.Prototype.PreprocLetOk
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel Tools.ShippingLetsAliasInv

/-! ## `inlFoldNat` -/

theorem inlNatSum?_ok (n : Nat) (e r : Lean.Expr) (h : inlNatSum? e = some r) : LetOk n r = true := by
  unfold inlNatSum? at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (injection h with h; subst h; exact letOk_natLit _ _)

theorem inlFoldNat_ok (n : Nat) : ∀ e : Lean.Expr, LetOk n e = true → LetOk n (inlFoldNat e) = true
  | .app f a, he => by
    simp only [LetOk, Bool.and_eq_true] at he
    have h1 := inlFoldNat_ok n f he.1
    have h2 := inlFoldNat_ok n a he.2
    unfold inlFoldNat
    cases hs : inlNatSum? (Lean.Expr.app (inlFoldNat f) (inlFoldNat a)) with
    | some r => simpa [hs] using inlNatSum?_ok n _ r hs
    | none => simp only [hs, Option.getD_none, LetOk, Bool.and_eq_true]; exact ⟨h1, h2⟩
  | .lam _ t b _, he => by
    simp only [LetOk, Bool.and_eq_true, inlFoldNat] at he ⊢
    exact ⟨inlFoldNat_ok n t he.1, inlFoldNat_ok n b he.2⟩
  | .forallE _ t b _, he => by
    simp only [LetOk, Bool.and_eq_true, inlFoldNat] at he ⊢
    exact ⟨inlFoldNat_ok n t he.1, inlFoldNat_ok n b he.2⟩
  | .letE _ t v b _, he => by
    simp only [LetOk, Bool.and_eq_true, inlFoldNat] at he ⊢
    exact ⟨⟨inlFoldNat_ok n t he.1.1, inlFoldNat_ok n v he.1.2⟩, inlFoldNat_ok n b he.2⟩
  | .mdata _ e, he => by
    simp only [LetOk, inlFoldNat] at he ⊢
    exact inlFoldNat_ok n e he
  | .proj _ _ e, he => by
    simp only [LetOk, inlFoldNat] at he ⊢
    exact inlFoldNat_ok n e he
  | .bvar _, he => he
  | .fvar _, he => he
  | .mvar _, he => he
  | .sort _, he => he
  | .const _ _, he => he
  | .lit _, he => he

/-! ## `zeroLit` (through the structural `replaceNoCache`) -/

theorem replaceNoCache_ok (n : Nat) (f : Lean.Expr → Option Lean.Expr)
    (hf : ∀ x r, f x = some r → LetOk n r = true) :
    ∀ e : Lean.Expr, LetOk n e = true → LetOk n (e.replaceNoCache f) = true
  | .forallE nm t b bi, he => by
    cases hfe : f (.forallE nm t b bi) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact hf _ r hfe
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [LetOk, Bool.and_eq_true, Lean.Expr.updateForallE!, Lean.Expr.updateForall!, Lean.mkForall] at he ⊢
      exact ⟨replaceNoCache_ok n f hf t he.1, replaceNoCache_ok n f hf b he.2⟩
  | .lam nm t b bi, he => by
    cases hfe : f (.lam nm t b bi) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact hf _ r hfe
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [LetOk, Bool.and_eq_true, Lean.Expr.updateLambdaE!, Lean.Expr.updateLambda!, Lean.mkLambda] at he ⊢
      exact ⟨replaceNoCache_ok n f hf t he.1, replaceNoCache_ok n f hf b he.2⟩
  | .mdata d b, he => by
    cases hfe : f (.mdata d b) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact hf _ r hfe
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [LetOk, Lean.Expr.updateMData!, Lean.mkMData] at he ⊢
      exact replaceNoCache_ok n f hf b he
  | .letE nm t v b nd, he => by
    cases hfe : f (.letE nm t v b nd) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact hf _ r hfe
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [LetOk, Bool.and_eq_true, Lean.Expr.updateLetE!, Lean.Expr.updateLet!] at he ⊢
      exact ⟨⟨replaceNoCache_ok n f hf t he.1.1, replaceNoCache_ok n f hf v he.1.2⟩,
        replaceNoCache_ok n f hf b he.2⟩
  | .app g a, he => by
    cases hfe : f (.app g a) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact hf _ r hfe
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [LetOk, Bool.and_eq_true, Lean.Expr.updateApp!, Lean.mkApp] at he ⊢
      exact ⟨replaceNoCache_ok n f hf g he.1, replaceNoCache_ok n f hf a he.2⟩
  | .proj s i b, he => by
    cases hfe : f (.proj s i b) with
    | some r => rw [Lean.Expr.replaceNoCache, hfe]; exact hf _ r hfe
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe]
      simp only [LetOk, Lean.Expr.updateProj!, Lean.mkProj] at he ⊢
      exact replaceNoCache_ok n f hf b he
  | .bvar i, he => by
    cases hfe : f (.bvar i) with
    | some r =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact hf _ r hfe | (intros; rename_i h; cases h)
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact he | (intros; rename_i h; cases h)
  | .fvar i, he => by
    cases hfe : f (.fvar i) with
    | some r =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact hf _ r hfe | (intros; rename_i h; cases h)
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact he | (intros; rename_i h; cases h)
  | .mvar i, he => by
    cases hfe : f (.mvar i) with
    | some r =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact hf _ r hfe | (intros; rename_i h; cases h)
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact he | (intros; rename_i h; cases h)
  | .sort u, he => by
    cases hfe : f (.sort u) with
    | some r =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact hf _ r hfe | (intros; rename_i h; cases h)
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact he | (intros; rename_i h; cases h)
  | .const c us, he => by
    cases hfe : f (.const c us) with
    | some r =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact hf _ r hfe | (intros; rename_i h; cases h)
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact he | (intros; rename_i h; cases h)
  | .lit l, he => by
    cases hfe : f (.lit l) with
    | some r =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact hf _ r hfe | (intros; rename_i h; cases h)
    | none =>
      rw [Lean.Expr.replaceNoCache, hfe] <;> first | exact he | (intros; rename_i h; cases h)

/-- The `Expr.replace` of `zeroLit` is an `@[extern]` (compiled behaviour not visible to proofs): the link to the structural
`replaceNoCache` is a PREMISE (NOT proved), for this particular `f`. -/
def ZeroLitAgrees : Prop :=
  ∀ e : Lean.Expr, Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e =
    e.replaceNoCache fun x =>
      match x with
      | .app (.const ``BitVec.zero _) w =>
        (canonicalNatLitValue? w).map fun n => mkApp2 (.const ``BitVec.ofNat []) (inlNatLit n) (inlNatLit 0)
      | _ => none

theorem zeroLit_ok (hz : ZeroLitAgrees) (n : Nat) (e : Lean.Expr) (he : LetOk n e = true) :
    LetOk n (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true := by
  rw [hz e]
  refine replaceNoCache_ok n _ ?_ e he
  intro x r hx
  split at hx
  · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp hx
    simp only [mkApp2, LetOk, Bool.and_eq_true, Bool.true_and]
    exact ⟨letOk_natLit _ _, letOk_natLit _ _⟩
  · simp at hx

/-! ## `machLoopAsLet` -/

theorem machLoopAsLet_ok (n : Nat) (e : Lean.Expr) : LetOk n e = true → LetOk n (machLoopAsLet e) = true := by
  induction e with
  | letE nm t v b nd iht ihv ihb =>
    intro he
    simp only [LetOk, Bool.and_eq_true, machLoopAsLet] at he ⊢
    exact ⟨he.1, ihb he.2⟩
  | _ =>
    intro he
    unfold machLoopAsLet
    first
      | exact he
      | (split <;> first | exact he | simp_all [LetOk, mkApp2])

/-! ## `machRoot` -/

theorem machRootLets_ok (n : Nat) : ∀ (e : Lean.Expr) (acc : List (Name × Lean.Expr × Lean.Expr)),
    LetOk n e = true → (∀ x ∈ acc, LetOk n x.2.2 = true) →
    (∀ x ∈ (machRootLets e acc).1, LetOk n x.2.2 = true) ∧ LetOk n (machRootLets e acc).2 = true
  | .letE nm ty v b nd, acc, he, hacc => by
    simp only [LetOk, Bool.and_eq_true] at he
    rw [machRootLets]
    refine machRootLets_ok n b _ he.2 ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he.1.2
    · exact hacc x hx
  | .bvar _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .fvar _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .mvar _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .sort _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .const _ _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .lit _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .app _ _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .lam _ _ _ _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .forallE _ _ _ _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .mdata _ _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)
  | .proj _ _ _, acc, he, hacc => by
    rw [machRootLets]
    · exact ⟨hacc, he⟩
    all_goals (intros; rename_i h; cases h)

/-- The shape of `machRoot`'s answer that `ShapeInOk` needs: the `let` values, the root and the enclosing run. -/
def RootOk (n : Nat) (r : List (Name × Lean.Expr × Lean.Expr) × Option (Name × Nat × Nat) × Option Lean.Expr ×
    Lean.Expr) : Prop :=
  (∀ x ∈ r.1, LetOk n x.2.2 = true) ∧ LetOk n r.2.2.2 = true ∧ ∀ q, r.2.2.1 = some q → LetOk n q = true

theorem machRoot_ok (n : Nat) (projs : Name → Option (Name × Nat × Nat)) (e : Lean.Expr)
    (acc : List (Name × Lean.Expr × Lean.Expr)) (he : LetOk n e = true)
    (hacc : ∀ x ∈ acc, LetOk n x.2.2 = true) : RootOk n (machRoot projs e acc) := by
  induction e generalizing acc with
  | letE nm t v b nd iht ihv ihb =>
    simp only [LetOk, Bool.and_eq_true] at he
    rw [machRoot]
    refine ihb _ he.2 ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he.1.2
    · exact hacc x hx
  | _ =>
    simp only [machRoot]
    have hrev : ∀ l : List (Name × Lean.Expr × Lean.Expr), (∀ x ∈ l, LetOk n x.2.2 = true) →
        ∀ x ∈ l.reverse, LetOk n x.2.2 = true := fun l h x hx => h x (List.mem_reverse.mp hx)
    obtain ⟨hfn, hargs⟩ := ok_spine n _ [] he (by simp)
    split
    · exact ⟨hrev acc hacc, he, fun q hq => by cases hq; exact he⟩
    · rcases hsp : inlSpine _ [] with ⟨fn, args⟩
      simp only [hsp] at hfn hargs ⊢
      split
      · rename_i p ls args' heq
        have ha : args' = args := by
          first | exact (Prod.mk.inj heq).2 | exact (Prod.mk.inj heq).2.symm
        subst ha
        split
        · rename_i ctor np idx r hproj hlast
          have hr : LetOk n r = true := hargs r (List.mem_of_getLast? hlast)
          have hq := machRootLets_ok n r acc hr hacc
          generalize machRootLets r acc = q at hq ⊢
          obtain ⟨acc', r'⟩ := q
          dsimp only at hq ⊢
          split
          · exact ⟨hrev acc' hq.1, he, fun q hq' => by cases hq'; exact hq.2⟩
          · exact ⟨hrev acc hacc, he, fun q hq => by cases hq⟩
        · exact ⟨hrev acc hacc, he, fun q hq => by cases hq⟩
      · exact ⟨hrev acc hacc, he, fun q hq => by cases hq⟩

/-! ## Connection to `ShapeInOk` -/

/-- **PROVED** from `LetOk 0` of the normalised body `en` and the premises `RootFloatRange` (`rootFloat`, a `partial
def`) and `ZeroLitAgrees` (`zeroLit`, an `@[extern]` `Expr.replace`): the three input fields `rootLets`, `root`,
`runBody` of `ShapeInOk`.  (`startDom` is NOT included.) -/
theorem shapeMid_ok (hroot : RootFloatRange) (hz : ZeroLitAgrees) (senv : StructEnv) (p : ShapePre)
    (en : Lean.Expr) (hen : LetOk 0 en = true) :
    (∀ x ∈ (shapeMid senv p en).rootLets, LetOk 0 x.2.2 = true) ∧ LetOk 0 (shapeMid senv p en).root = true ∧
      ∀ dom αs initsE body, (shapeMid senv p en).run? = some (dom, αs, initsE, body) → LetOk 0 body = true := by
  have he := machLoopAsLet_ok 0 _ (hroot _ (zeroLit_ok hz 0 _ (inlFoldNat_ok 0 _ hen)))
  have hr := machRoot_ok 0 senv.proj _ [] he (by simp)
  unfold shapeMid
  dsimp only
  generalize machRoot senv.proj
    (machLoopAsLet (Sparkle.Compiler.MachRawSurface.rootFloat
      (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? (inlFoldNat en)))) [] = r at hr ⊢
  obtain ⟨rl, sel, run?, root⟩ := r
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨h1, h2, ?_⟩
  intro dom αs initsE body h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, hm⟩ := h
  have hqok : LetOk 0 q = true := by
    split at hq
    · exact ok_getAppArgs h2 q (Array.mem_of_back? hq)
    · exact h3 q hq
  exact (runApp_ok 0 q dom αs initsE body hqok hm).2

/-- The ONE input field of `ShapeInOk` that is not derived here (`startDom`, studied by unit SDOM). -/
def StartDomOk (senv : StructEnv) (m : ShapeMid) : Prop :=
  ∀ n dom αs initsE body dom' stc, m.run? = some (dom, αs, initsE, body) →
    machConvF n senv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead) =
      some (some (dom', stc)) → LetOk 0 dom' = true

/-- `ShapeInOk` from `startDom` alone plus `LetOk 0 en`. -/
theorem shapeInOk_of (hroot : RootFloatRange) (hz : ZeroLitAgrees) (senv : StructEnv) (p : ShapePre)
    (en : Lean.Expr) (hen : LetOk 0 en = true) (hs : StartDomOk senv (shapeMid senv p en)) :
    ShapeInOk senv (shapeMid senv p en) :=
  let h := shapeMid_ok hroot hz senv p en hen
  ⟨h.1, h.2.1, h.2.2, hs⟩

/-- The exact requirement on the normaliser's output: the `LetOk 0` property of `execNorm`'s result, given the
declaration body `p.e` (PREMISE shape; NOT proved — `execNorm` is a `partial_fixpoint`). -/
def NormRange (senv : StructEnv) : Prop :=
  ∀ e en, LetOk 0 e = true → execNorm senv e = some en → LetOk 0 en = true

/-- `machineShapeN_lets'` with the fields `rootLets`, `root`, `runBody` of `ShapeInOk` DERIVED (from `NormRange`,
`ZeroLitAgrees`, `RootFloatRange` and the declaration condition `LetOk 0 p.e`); the premise list now has the
INPUT `hpe` (`LetOk 0 p.e`), `NormRange senv`, `ZeroLitAgrees` and the one remaining field `StartDomOk`. -/
theorem machineShapeN_lets'' {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv) (hz : ZeroLitAgrees) (hnorm : NormRange senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (hstart : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → StartDomOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp :=
  machineShapeN_lets hroot hlift hinst1 hsig Tools.ShippingLetsReaderInv.bundleIotaRange
    (fun p en hp hn => shapeInOk_of hroot hz senv p en (hnorm _ _ (hpe p hp) hn) (hstart p en hp hn)) h

#print axioms shapeMid_ok
#print axioms machineShapeN_lets''

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_lets''
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "NormRange", "Eq", "StartDomOk", "Eq"])
#print axioms inlFoldNat_ok
#print axioms zeroLit_ok
#print axioms machLoopAsLet_ok
#print axioms machRoot_ok

end Tools.Prototype.PreprocLetOk
