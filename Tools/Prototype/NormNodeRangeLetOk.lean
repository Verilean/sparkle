import Tools.Prototype.NormRangeLetOk

/-! # Unit LC15: `NormNodeRange senv` decomposed along the branches of `machNormNode`

BUILT (unit LC15): a1-a26 exit 1/0 while developing (a1, a3-a7, a9, a12-a13, a15, a21, a23 exit 1 = my own proof errors/timeouts), a27 and a28 (final, after header edit) exit 0. No sorry / axiom / native_decide.

**`NormNodeRange` is REPLACED by two premises, NOT unconditionally discharged.**
PROVED (this file): every branch of `machNormNode` keeps `LetOk 0`: `machNormPure_ok`, `machNormMixed_ok`, `machNormAp_ok`,
`machNormApLift_ok` (via `machApSpine_ok`, `machLamBody_ok`, `mapM_vars`, `letOk_mkAppN`), `machNormMap_ok` (incl. `machNormLift_ok`),
the `~~~`/`-` Signal arms, `Signal.lit`, `Functor.map`; hence `machNormNode_ok`, `normNodeRange_of`, `normRange_of'`,
`machineShapeN_lets''_noNode` (old theorems unchanged; binder audit exact).
PREMISES (not proved; each names ONE call; both are `partial def`, i.e. opaque to the kernel, no unfolding equation):
* `LiftScalarRange senv`: `machLiftScalarN senv dom vars e = some (w, r)` keeps `LetOk 0` (given `dom`, `vars`, `e` do).
* `BoolMapRange senv`: `machBoolMap senv dom a wa body = some r` keeps `LetOk 0`.
The existing `Inst1Range`/`LiftRange` do not cover them (they are not `instantiate1`/lift-by-1 calls). `senv.natOf` and
`canonicalNatLitValue?` return `Nat`s that are re-embedded through `inlNatLit`, so they need no premise.
No branch producing a value outside `LetOk 0` was found (none creates an `fvar`); the two premises are a replacement for the
single `NormNodeRange`, narrower (two `partial` helpers), not a discharge. -/
namespace Tools.Prototype.NormNodeRangeLetOk
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk

theorem machBVLit_ok (w v : Nat) : LetOk 0 (machBVLit w v) = true := by
  simp [machBVLit, mkApp2, mkApp, LetOk, letOk_natLit]

theorem machPureE_ok {dom c : Lean.Expr} (w : Nat) (hd : LetOk 0 dom = true) (hc : LetOk 0 c = true) :
    LetOk 0 (machPureE dom w c) = true := by
  simp [machPureE, mkApp3, mkApp2, mkApp, LetOk, letOk_natLit, hd, hc]

theorem machConcatE_ok {dom a b : Lean.Expr} (m n : Nat) (hd : LetOk 0 dom = true)
    (ha : LetOk 0 a = true) (hb : LetOk 0 b = true) : LetOk 0 (machConcatE dom m n a b) = true := by
  simp [machConcatE, machSigT, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, LetOk, letOk_natLit, hd, ha, hb]

theorem machLitOf_ok {senv : StructEnv} {w : Nat} {c l : Lean.Expr} (hc : LetOk 0 c = true)
    (h : machLitOf senv w c = some l) : LetOk 0 l = true := by
  unfold machLitOf at h
  split at h
  · split at h
    · cases h; exact hc
    · cases h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨v, _, rfl⟩ := h
    exact machBVLit_ok _ _

theorem machNormPure_ok (senv : StructEnv) {e : Lean.Expr} (he : LetOk 0 e = true) :
    LetOk 0 (machNormPure senv e) = true := by
  unfold machNormPure
  split
  · rename_i ls dom ty c
    have he0 := he
    simp only [LetOk, Bool.and_eq_true] at he
    obtain ⟨⟨⟨-, hd⟩, hty⟩, hc⟩ := he
    split
    · split
      · exact he0
      · exact he0
      · split
        · simp [mkApp3, mkApp, LetOk, hd]
        · simp [mkApp3, mkApp, LetOk, hd]
        · exact he0
    · split
      · split
        · exact he0
        · split
          · rename_i l hl
            exact machPureE_ok _ hd (machLitOf_ok hc hl)
          · exact he0
      · exact he0
  · exact he

theorem machSigBits_ok {γ dom : Lean.Expr} {w : Nat} (h : LetOk 0 γ = true)
    (hs : machSigBits? γ = some (dom, w)) : LetOk 0 dom = true := by
  unfold machSigBits? at hs
  split at hs
  · simp only [LetOk, Bool.and_eq_true] at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hs
    obtain ⟨_, _, rfl, _⟩ := hs
    exact h.1.2
  · cases hs

theorem machNormMixed_ok (senv : StructEnv) {e : Lean.Expr} (he : LetOk 0 e = true) :
    LetOk 0 (machNormMixed senv e) = true := by
  have he0 := he
  unfold machNormMixed
  split
  · rename_i m ls α β γ inst a b
    simp only [LetOk, Bool.and_eq_true] at he
    obtain ⟨⟨⟨⟨⟨⟨-, hα⟩, hβ⟩, hγ⟩, hi⟩, ha⟩, hb⟩ := he
    split
    · split
      · split
        · split
          · exact he0
          · split
            · rename_i l hl
              have := machLitOf_ok hb hl
              simp [mkApp6, LetOk, hα, hβ, hγ, hi, ha, this]
            · exact he0
        · exact he0
      · split
        · rename_i dom w si hs _
          split
          · rename_i l hl
            have := machLitOf_ok hb hl
            have hd := machSigBits_ok hγ hs
            simp [machSigBin, machSigT, machPureE, mkApp6, mkApp3, mkApp2, mkApp, LetOk, letOk_natLit, ha, this, hd]
          · exact he0
        · exact he0
    · split
      · split
        · split
          · exact he0
          · split
            · rename_i l hl
              have := machLitOf_ok ha hl
              simp [mkApp6, LetOk, hα, hβ, hγ, hi, hb, this]
            · exact he0
        · exact he0
      · split
        · rename_i dom w si hs _
          split
          · rename_i l hl
            have := machLitOf_ok ha hl
            have hd := machSigBits_ok hγ hs
            simp [machSigBin, machSigT, machPureE, mkApp6, mkApp3, mkApp2, mkApp, LetOk, letOk_natLit, hb, this, hd]
          · exact he0
        · exact he0
    · exact he0
  · exact he0

theorem machNormAp_ok {e : Lean.Expr} (he : LetOk 0 e = true) : LetOk 0 (machNormAp e) = true := by
  have he0 := he
  unfold machNormAp
  split
  · simp only [LetOk, Bool.and_eq_true] at he
    repeat' split
    all_goals first
      | exact he0
      | simp_all [machSigBin, machSigT, mkApp6, mkApp2, LetOk, letOk_natLit]
  · exact he0

/-- PREMISE (not proved; replaces the `machLiftScalarN` part of `NormNodeRange`): `machLiftScalarN` is a `partial def`
(opaque to the kernel: no unfolding equation), so its range cannot be derived here. -/
def LiftScalarRange (senv : StructEnv) : Prop :=
  ∀ (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) (w : Nat) (r : Lean.Expr),
    LetOk 0 dom = true → (∀ p ∈ vars, LetOk 0 p.2 = true) → LetOk 0 e = true →
    machLiftScalarN senv dom vars e = some (w, r) → LetOk 0 r = true

/-- PREMISE (not proved; replaces the `machBoolMap` part of `NormNodeRange`): `machBoolMap` is a `partial def`. -/
def BoolMapRange (senv : StructEnv) : Prop :=
  ∀ (dom a : Lean.Expr) (wa : Nat) (body r : Lean.Expr),
    LetOk 0 dom = true → LetOk 0 a = true → LetOk 0 body = true →
    machBoolMap senv dom a wa body = some r → LetOk 0 r = true

theorem getD_ok {o : Option Lean.Expr} {d : Lean.Expr} (hd : LetOk 0 d = true)
    (ho : ∀ r, o = some r → LetOk 0 r = true) : LetOk 0 (o.getD d) = true := by
  cases h : o with
  | none => exact hd
  | some r => exact ho r h

theorem machNormLift_ok {senv : StructEnv} (hl : LiftScalarRange senv) {dom tyA tyB a body e : Lean.Expr}
    (hd : LetOk 0 dom = true) (ha : LetOk 0 a = true) (hb : LetOk 0 body = true) (he : LetOk 0 e = true) :
    LetOk 0 (machNormMap.machNormLift senv dom tyA tyB a body e) = true := by
  unfold machNormMap.machNormLift
  split
  · split
    · rename_i r hr
      split
      · exact hl dom _ body _ r hd (by simpa using ha) hb hr
      · exact he
    · exact he
  · exact he

theorem machScalarBin_ok {w : Nat} {body x y : Lean.Expr} {mm : Name} (hb : LetOk 0 body = true)
    (h : machScalarBin? w body = some (mm, x, y)) : LetOk 0 x = true ∧ LetOk 0 y = true := by
  unfold machScalarBin? at h
  split at h
  · rename_i m t1 t2 t3 inst x' y'
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      simp only [LetOk, Bool.and_eq_true] at hb
      exact ⟨hb.1.2, hb.2⟩
    · cases h
  · cases h

theorem machNormMap_ok {senv : StructEnv} (hl : LiftScalarRange senv) (hbm : BoolMapRange senv)
    {dom tyA tyB f a e : Lean.Expr} {mk : Lean.Expr → Lean.Expr}
    (hmk : ∀ f', LetOk 0 f' = true → LetOk 0 (mk f') = true)
    (hd : LetOk 0 dom = true) (hf : LetOk 0 f = true) (ha : LetOk 0 a = true) (he : LetOk 0 e = true) :
    LetOk 0 (machNormMap senv dom tyA tyB f a mk e) = true := by
  unfold machNormMap
  split
  · rename_i nm t ls wsE startE lenE bi
    simp only [LetOk, Bool.and_eq_true] at hf
    repeat' split
    all_goals first
      | exact he
      | exact machConcatE_ok _ _ hd (machPureE_ok _ hd (machBVLit_ok _ _)) ha
      | (apply hmk; simp [mkApp4, LetOk, letOk_natLit, hf])
  · repeat' split
    all_goals first
      | exact he
      | exact machSigBin_ok hd _ _ _ (machPureE_ok _ hd (machBVLit_ok _ _)) ha
  · repeat' split
    all_goals first
      | exact he
      | exact machSigBin_ok hd _ _ _ (machPureE_ok _ hd (machBVLit_ok _ _)) ha
  · rename_i nm t body bi
    simp only [LetOk, Bool.and_eq_true] at hf
    have hbody := hf.2
    repeat' split
    all_goals first
      | exact he
      | exact machNormLift_ok hl hd ha hbody he
      | exact getD_ok he (fun r hr => hbm dom a _ _ r hd ha hbody hr)
      | (obtain ⟨hx, hy⟩ := machScalarBin_ok hbody ‹machScalarBin? _ _ = some _›
         exact machSigBin_ok hd _ _ _ ha (machPureE_ok _ hd (machLitOf_ok hy ‹machLitOf _ _ _ = some _›)))
      | (obtain ⟨hx, hy⟩ := machScalarBin_ok hbody ‹machScalarBin? _ _ = some _›
         exact machSigBin_ok hd _ _ _ (machPureE_ok _ hd (machLitOf_ok hx ‹machLitOf _ _ _ = some _›)) ha)
  · exact he

theorem machLamBody_ok : ∀ (n : Nat) {e b : Lean.Expr}, LetOk 0 e = true → machLamBody n e = some b →
    LetOk 0 b = true
  | 0, e, b, he, h => by
    simp only [machLamBody, Option.some.injEq] at h; subst h; exact he
  | n + 1, e, b, he, h => by
    cases e with
    | lam nm t bd bi =>
      simp only [machLamBody] at h
      simp only [LetOk, Bool.and_eq_true] at he
      exact machLamBody_ok n he.2 h
    | _ => simp [machLamBody] at h

theorem machApSpine_ok (e : Lean.Expr) (acc : List (Lean.Expr × Lean.Expr)) {dom f : Lean.Expr}
    {args : List (Lean.Expr × Lean.Expr)} (he : LetOk 0 e = true)
    (hacc : ∀ p ∈ acc, LetOk 0 p.1 = true ∧ LetOk 0 p.2 = true)
    (h : machApSpine e acc = some (dom, f, args)) :
    LetOk 0 dom = true ∧ LetOk 0 f = true ∧ ∀ p ∈ args, LetOk 0 p.1 = true ∧ LetOk 0 p.2 = true := by
  induction e, acc using machApSpine.induct generalizing dom f args with
  | case1 ls dom' α β f' x acc ih =>
    simp only [machApSpine] at h
    simp only [LetOk, Bool.and_eq_true] at he
    exact ih he.1.2 (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨he.1.1.1.2, he.2⟩
      · exact hacc p hp) h
  | case2 ls dom' α β f' a acc =>
    simp only [machApSpine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [LetOk, Bool.and_eq_true] at he
    refine ⟨he.1.1.1.1.2, he.1.2, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨he.1.1.1.2, he.2⟩
    · exact hacc p hp
  | case3 e acc h1 h2 => simp [machApSpine, h1, h2] at h

theorem letOk_foldl_app {f : Lean.Expr} (hf : LetOk 0 f = true) :
    ∀ (l : List Lean.Expr), (∀ a ∈ l, LetOk 0 a = true) → ∀ {f : Lean.Expr}, LetOk 0 f = true →
      LetOk 0 (l.foldl Lean.mkApp f) = true
  | [], _, _, hf => hf
  | a :: l, h, f, hf => by
    apply letOk_foldl_app hf l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [Lean.mkApp, LetOk, Bool.and_eq_true]
    exact ⟨hf, h a (List.mem_cons_self ..)⟩

theorem mapM_vars (l : List (Lean.Expr × Lean.Expr)) :
    ∀ (vs : List (Nat × Lean.Expr)),
      l.mapM (fun p => Option.map (fun w => (w, p.snd)) (machBits? p.fst)) = some vs →
      ∀ v ∈ vs, ∃ p ∈ l, v.2 = p.2 := by
  induction l with
  | nil => intro vs h v hv; simp at h; subst h; simp at hv
  | cons p l ih =>
    intro vs h v hv
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, ⟨w, hw, rfl⟩, rest, hrest, hvs⟩ := h
    have hvs' : vs = (w, p.snd) :: rest := (Option.some.inj hvs).symm
    subst hvs'
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨p, List.mem_cons_self .., rfl⟩
    · obtain ⟨q, hq, hqq⟩ := ih rest hrest v hv
      exact ⟨q, List.mem_cons_of_mem _ hq, hqq⟩

theorem letOk_mkAppN {f : Lean.Expr} (hf : LetOk 0 f = true) (l : List Lean.Expr)
    (h : ∀ a ∈ l, LetOk 0 a = true) : LetOk 0 (Lean.mkAppN f l.toArray) = true := by
  unfold Lean.mkAppN
  rw [← Array.foldl_toList]
  simp only [List.toList_toArray]
  exact letOk_foldl_app hf l h hf

theorem machNormApLift_ok {senv : StructEnv} (hl : LiftScalarRange senv) {e : Lean.Expr}
    (he : LetOk 0 e = true) : LetOk 0 (machNormApLift senv e) = true := by
  have he0 := he
  unfold machNormApLift
  split
  · apply getD_ok he0
    intro r hr
    simp only [bind, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨dom, f, args⟩, hsp, hr⟩ := hr
    obtain ⟨hd, hf, hargs⟩ := machApSpine_ok _ [] he0 (by simp) hsp
    simp only at hr
    split at hr
    · cases hr
    rw [Option.bind_eq_some_iff] at hr
    obtain ⟨body, hbody, hr⟩ := hr
    have hbodyok : LetOk 0 body = true := by
      cases h : machLamBody args.length f with
      | some b =>
        simp [h] at hbody
        subst hbody
        exact machLamBody_ok _ hf h
      | none =>
        simp [h] at hbody
        obtain ⟨-, rfl⟩ := hbody
        apply letOk_mkAppN hf
        intro a ha
        rw [List.mem_reverse] at ha
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
        rfl
    rw [Option.bind_eq_some_iff] at hr
    obtain ⟨vars, hvars, hr⟩ := hr
    have hvok : ∀ p ∈ vars, LetOk 0 p.2 = true := by
      intro p hp
      obtain ⟨q, hq, hqq⟩ := mapM_vars _ _ hvars p hp
      rw [hqq]
      exact (hargs q (List.mem_reverse.mp hq)).2
    split at hr
    · rw [Option.bind_eq_some_iff] at hr
      obtain ⟨⟨w0, r0⟩, hlift, hr⟩ := hr
      split at hr
      · have := Option.some.inj hr
        subst this
        exact hl dom vars body w0 r0 hd hvok hbodyok hlift
      · cases hr
    · split at hr
      · cases hr
      · split at hr
        · rename_i c lsC wE x y
          split at hr
          · cases hr
          · simp only [Option.bind_eq_some_iff] at hr
            obtain ⟨w, hw, ⟨wx, x'⟩, hx, ⟨wy, y'⟩, hy, hr⟩ := hr
            split at hr
            · cases hr
            · have := Option.some.inj hr
              subst this
              simp only [LetOk, Bool.and_eq_true] at hbodyok
              have h1 := hl dom vars x wx x' hd hvok hbodyok.1.2 hx
              have h2 := hl dom vars y wy y' hd hvok hbodyok.2 hy
              simp [mkApp5, mkApp4, mkApp3, mkApp2, mkApp, LetOk, letOk_natLit, hd, h1, h2]
        · cases hr
  · exact he0

theorem machNormNode_ok {senv : StructEnv} (hl : LiftScalarRange senv) (hbm : BoolMapRange senv)
    {e : Lean.Expr} (he : LetOk 0 e = true) : LetOk 0 (machNormNode senv e) = true := by
  have he0 := he
  unfold machNormNode
  split
  · rename_i ls ty dom x
    simp only [LetOk, Bool.and_eq_true] at he
    obtain ⟨⟨⟨-, hty⟩, hdom⟩, hx⟩ := he
    apply machNormPure_ok
    simp [mkApp3, mkApp2, mkApp, LetOk, hty, hdom, hx]
  · exact machNormPure_ok senv he0
  · rename_i sigTy _ _ a
    simp only [LetOk, Bool.and_eq_true] at he
    split
    · rename_i dom w hs
      exact machSigBin_ok (machSigBits_ok he.1.1.2 hs) _ _ _
        (machPureE_ok _ (machSigBits_ok he.1.1.2 hs) (machBVLit_ok _ _)) he.2
    · exact he0
  · rename_i sigTy _ _ a
    simp only [LetOk, Bool.and_eq_true] at he
    split
    · rename_i dom w hs
      exact machSigBin_ok (machSigBits_ok he.1.1.2 hs) _ _ _
        (machPureE_ok _ (machSigBits_ok he.1.1.2 hs) (machBVLit_ok _ _)) he.2
    · exact he0
  · have h1 := machNormAp_ok he0
    simp only
    split
    · exact machNormApLift_ok hl he0
    · exact h1
  · rename_i ls dom tyA tyB f a
    simp only [LetOk, Bool.and_eq_true] at he
    obtain ⟨⟨⟨⟨⟨-, hdom⟩, htyA⟩, htyB⟩, hf⟩, ha⟩ := he
    refine machNormMap_ok hl hbm ?_ hdom hf ha he0
    intro f' hf'
    simp [mkApp5, mkApp4, mkApp3, mkApp2, mkApp, LetOk, hdom, htyA, htyB, hf', ha]
  · rename_i ls us dom is dom' tyA tyB f a
    simp only [LetOk, Bool.and_eq_true] at he
    obtain ⟨⟨⟨⟨⟨⟨-, -, hdom⟩, -, hdom'⟩, htyA⟩, htyB⟩, hf⟩, ha⟩ := he
    refine machNormMap_ok hl hbm ?_ hdom hf ha he0
    intro f' hf'
    simp [mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, LetOk, hdom, hdom', htyA, htyB, hf', ha]
  · exact machNormMixed_ok senv he0
  · exact he0

/-- `NormNodeRange senv` from the two `partial def` range premises (`machLiftScalarN`, `machBoolMap`); every other branch
of `machNormNode` is proved above. -/
theorem normNodeRange_of {senv : StructEnv} (hl : LiftScalarRange senv) (hbm : BoolMapRange senv) :
    NormNodeRange senv := fun _ he => machNormNode_ok hl hbm he

/-- `normRange_of` with `NormNodeRange` replaced by `LiftScalarRange` + `BoolMapRange`. -/
theorem normRange_of' {senv : StructEnv} (hraw : RawNodeRange senv) (hl : LiftScalarRange senv)
    (hbm : BoolMapRange senv) (hinst : Inst1Range) : NormRange senv :=
  normRange_of hraw (normNodeRange_of hl hbm) hinst

/-- `machineShapeN_lets''_noNorm` with `NormNodeRange` replaced by `LiftScalarRange` + `BoolMapRange`. -/
theorem machineShapeN_lets''_noNode {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv) (hz : ZeroLitAgrees)
    (hraw : RawNodeRange senv) (hls : LiftScalarRange senv) (hbm : BoolMapRange senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (hstart : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → StartDomOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp :=
  machineShapeN_lets''_noNorm hroot hlift hinst1 hsig hz hraw (normNodeRange_of hls hbm) hpe hstart h

#print axioms machNormNode_ok
#print axioms normNodeRange_of
#print axioms machineShapeN_lets''_noNode

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_lets''_noNode
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "RawNodeRange", "LiftScalarRange",
    "BoolMapRange", "Eq", "StartDomOk", "Eq"])

end Tools.Prototype.NormNodeRangeLetOk
