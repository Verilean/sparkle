import Tools.ShippingGen5PTCorpus
import Tools.ShippingGen5DepRows
set_option autoImplicit false
/-! # Spec supply for `PTcorpus` (issue sparkle-ledger-dd4-deprows, Q-C; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Spec)

No TRUSTED, axiom, `sorry`, `native_decide`. Existing files are unchanged. A Spec being STATED does not pay a row: a row is counted only when a theorem `RowTypedAtV PTcorpus env c ls` / `RowTeleEvAt PTcorpus env c ls` exists
(its env facts stay hypotheses, evaluated in the real environment by the Check).

* §1 The result type former applied to the first `m` binders (`D x₁ … x_m`, any `m`): `instForallS_spine` (a generalisation of `instForallS_depFirst`, which is `m = 1`) and `rowTypedAtV_spine`.
* §2 `PTcorpus` supplies the Spec per key.
* §3 The 26 keys of `DepRows` have no row in `PTcorpus` (`notImportable`): `FirstArgSpec` / `DomFieldsSpec` cannot be supplied, proved. -/
namespace Tools.ShippingGen5PTCorpusSpec
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
  Tools.ShippingGen5ConstValueESL Tools.ShippingGen5ConstValueEVL Tools.ShippingGen5RowTypedV Tools.ShippingGen5PTCorpus

/-- The first `m` of `n` binders as loose bound variables: `bvar (n-1), …, bvar (n-m)` (meaningful for `m ≤ n`). -/
def spine : Nat → Nat → List Expr
  | _, 0 => []
  | 0, _ + 1 => []
  | n + 1, m + 1 => .bvar n :: spine n m

theorem spine_lt : ∀ (n m : Nat), m ≤ n → ∀ e ∈ spine n m, ∃ j, j < n ∧ e = .bvar j
  | _, 0, _, e, he => by simp [spine] at he
  | 0, m + 1, h, _, _ => by omega
  | n + 1, m + 1, h, e, he => by
    simp only [spine, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨n, by omega, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := spine_lt n m (by omega) e he
      exact ⟨j, by omega, rfl⟩

theorem substS_spine (n m : Nat) (h : m ≤ n) (x : Expr) : (spine n m).map (fun e => substS e n x) = spine n m := by
  refine (List.map_congr_left (g := fun e => e) fun e he => ?_).trans (List.map_id _)
  obtain ⟨j, hj, rfl⟩ := spine_lt n m h e he
  simp [substS, hj]

/-- `instForallS` of `n` binders whose result is `D` applied to `pre` (already substituted, lifted) and then to the first `m` binders: `D (pre ++ args.take m)`. -/
theorem instForallS_spine (D : Name) (Ls : List Level) :
    ∀ (n m : Nat) (T : Expr) (pre args : List Expr), m ≤ n →
      PiN T n (mkAppN (.const D Ls) (pre.map (fun e => liftS e 0 n) ++ spine n m).toArray) → args.length = n →
      instForallS T args = mkAppN (.const D Ls) (pre ++ args.take m).toArray
  | 0, m, T, pre, args, hm, h, hl => by
    have : args = [] := List.length_eq_zero_iff.mp hl
    subst this
    have hm0 : m = 0 := by omega
    subst hm0
    have h' : T = mkAppN (.const D Ls) (pre.map (fun e => liftS e 0 0) ++ spine 0 0).toArray := h
    rw [instForallS_nil, h']
    simp [spine, liftS_zero]
  | n + 1, m, T, pre, args, hm, ⟨y, A, B, bi, hT, hB⟩, hl => by
    subst hT
    match args, hl with
    | b :: xs, hl =>
      have hl' : xs.length = n := by simpa using hl
      show instForallS (substS B 0 b) xs = _
      have h1 := piN_substS n B _ 0 b hB
      rw [Nat.zero_add, substS_mkAppN] at h1
      have hc : substS (.const D Ls) n b = .const D Ls := rfl
      rw [hc] at h1
      have hpre : (pre.map (fun e => liftS e 0 (n + 1))).map (fun e => substS e n b) = pre.map (fun e => liftS e 0 n) := by
        rw [List.map_map]
        exact List.map_congr_left fun e _ => substS_liftS_in e 0 (n + 1) n b (by omega) (by omega)
      cases m with
      | zero =>
        rw [List.map_append, hpre] at h1
        have := instForallS_spine D Ls n 0 _ pre xs (by omega) (by simpa [spine] using h1) hl'
        simpa using this
      | succ m =>
        have h2 : (pre.map (fun e => liftS e 0 (n + 1)) ++ spine (n + 1) (m + 1)).map (fun e => substS e n b) =
            (pre ++ [b]).map (fun e => liftS e 0 n) ++ spine n m := by
          rw [List.map_append, hpre]
          simp only [spine, List.map_cons, substS, Nat.lt_irrefl, if_false, if_true, List.map_append, List.map_nil]
          rw [substS_spine n m (by omega) b]
          simp
        rw [h2] at h1
        have := instForallS_spine D Ls n m _ (pre ++ [b]) xs (by omega) h1 hl'
        simpa using this

theorem argsDenV_take {PT : PrimTableK} {env : Environment} {ρ : Val} :
    ∀ (kp kq : List Bool) {args : List Expr} {xs : List Arg}, ArgsDenV PT env ρ (kp ++ kq) args xs →
      ArgsDenV PT env ρ kp (args.take kp.length) (xs.take kp.length)
  | [], _, _, _, _ => .nil
  | false :: kp, kq, _, _, .ty hT hs => .ty hT (argsDenV_take kp kq hs)
  | true :: kp, kq, _, _, .tm hv hs => .tm hv (argsDenV_take kp kq hs)

/-- ENV FACT: the instantiated declared type of `c` is `n` binders and then `D Ls` applied to the first `m` of them. -/
def EnvDepSpine (env : Environment) (c : Name) (ls : List Level) (n m : Nat) (D : Name) (Ls : List Level) : Prop :=
  ∀ ci : ConstantInfo, env.find? c = some ci →
    PiN (instantiateLevelParamsS ci.levelParams ls ci.type) n (mkAppN (.const D Ls) (spine n m).toArray)

/-- Spec of a row (about `PT`): the argument kinds are `kp ++ kq`, and the value type it produces is the denotation of the type former `D` at the first `kp.length` arguments. `FirstArgSpec` is `kp = [k0]`. -/
def SpineSpec (PT : PrimTableK) (c : Name) (ls : List Level) (kp kq : List Bool) (D : Name) (Ls : List Level) : Prop :=
  ∃ (row : TmRow) (trow : TyRow), PT.tms c ls = some row ∧ row.kinds = kp ++ kq ∧ PT.tys D Ls = some trow ∧ trow.kinds = kp ∧
    ∀ (ys : List Arg) (d : Dyn), row.den ys = some d → trow.den (ys.take kp.length) = some d.ty

/-- `RowTypedAtV` of a row whose result is a type former applied to the first `m` arguments. NO `OblDenSubstS`: the first `m` arguments' own derivations type the result. -/
theorem rowTypedAtV_spine (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (kp kq : List Bool) (D : Name) (Ls : List Level)
    (hs : SpineSpec PT c ls kp kq D Ls) (hnd : ¬ IsDefn env D) (hT : EnvDepSpine env c ls (kp ++ kq).length kp.length D Ls) :
    RowTypedAtV PT env c ls := by
  obtain ⟨row, trow, hrow, hk, htrow, htk, hden⟩ := hs
  intro ci row' ρ args ys d hci hrow' hargs hd
  rw [hrow] at hrow'; cases hrow'
  rw [hk] at hargs
  have hl : args.length = (kp ++ kq).length := by have := (argsdenv_length hargs).1; simpa using this
  have hm : kp.length ≤ (kp ++ kq).length := by simp
  have hT' := hT ci hci
  have hT'' : PiN (instantiateLevelParamsS ci.levelParams ls ci.type) (kp ++ kq).length
      (mkAppN (.const D Ls) (([] : List Expr).map (fun e => liftS e 0 (kp ++ kq).length) ++ spine (kp ++ kq).length kp.length).toArray) := by
    simpa using hT'
  rw [instForallS_spine D Ls _ _ _ [] args hm hT'' hl]
  have hargs' : ArgsDenV PT env ρ trow.kinds (args.take kp.length) (ys.take kp.length) := by rw [htk]; exact argsDenV_take kp kq hargs
  exact .tcon htrow hnd hargs' (hden ys d hd) (by simp)

/-! ## §2 `SpineSpec` of a `PTcorpus` row by construction

`Refines kp kq t u`: the value telescope `t` (kinds `kp ++ kq`) and the type telescope `u` (kinds `kp`) take the same arguments in the first `kp.length` places, and `t` produces a value of the type that `u` produces. -/
open Classical in
def Refines : (kp kq : List Bool) → TmTele (kp ++ kq) → TyTele kp → Prop
  | [], _, t, .done T => t.ResTy T
  | true :: kp, kq, .tm A k, .tm A' k' => ∃ h : A = A', ∀ a, Refines kp kq (k a) (k' (cast h a))
  | false :: kp, kq, .ty k, .ty k' => ∀ X, Refines kp kq (k X) (k' X)

theorem refines_run : ∀ (kp kq : List Bool) (t : TmTele (kp ++ kq)) (u : TyTele kp), Refines kp kq t u →
    ∀ (ys : List Arg) (d : Dyn), t.run ys = some d → u.run (ys.take kp.length) = some d.ty
  | [], _, t, .done T, h, ys, d, hd => by
    simp only [List.length_nil, List.take_zero, TyTele.run]
    rw [TmTele.run_ty t T h ys d hd]
  | true :: kp, kq, .tm A k, .tm A' k', ⟨hA, h⟩, ys, d, hd => by
    cases hA
    cases ys with
    | nil => simp [TmTele.run] at hd
    | cons y ys =>
      cases y with
      | ty _ => simp [TmTele.run] at hd
      | tm p =>
        obtain ⟨α, a⟩ := p
        simp only [TmTele.run] at hd
        by_cases hα : α = A
        · subst hα
          simp only [dif_pos] at hd
          have := refines_run kp kq _ _ (h (cast rfl a)) ys d hd
          simpa [TyTele.run] using this
        · simp [hα] at hd
  | false :: kp, kq, .ty k, .ty k', h, ys, d, hd => by
    cases ys with
    | nil => simp [TmTele.run] at hd
    | cons y ys =>
      cases y with
      | tm _ => simp [TmTele.run] at hd
      | ty T =>
        simp only [TmTele.run] at hd
        simpa [TyTele.run] using refines_run kp kq _ _ (h T) ys d hd

theorem spineSpec_of_refines {PT : PrimTableK} {c : Name} {ls : List Level} {kp kq : List Bool} {D : Name} {Ls : List Level}
    {t : TmTele (kp ++ kq)} {u : TyTele kp} (hr : Refines kp kq t u)
    (h1 : PT.tms c ls = some t.row) (h2 : PT.tys D Ls = some u.row) : SpineSpec PT c ls kp kq D Ls :=
  ⟨_, _, h1, rfl, h2, rfl, fun ys d hd => refines_run kp kq t u hr ys d hd⟩

macro "refines_tac" : tactic => `(tactic| (repeat (first | refine ⟨rfl, ?_⟩ | intro _); try rfl))

/-- `RowTypedAtV PTcorpus` of the 19 rows that the first-argument theorems do not reach (type former applied to the first `m` arguments), one pair of theorems per key: the `SpineSpec` of the row, and the row theorem with the env fact as hypothesis. -/
theorem spec_BitVec_ofFin : SpineSpec PTcorpus `BitVec.ofFin [] [true] [true] `BitVec [] :=
  spineSpec_of_refines (t := tm_4) (u := ty_4) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_BitVec_ofFin (env : Environment) (hnd : ¬ IsDefn env `BitVec)
    (hT : EnvDepSpine env `BitVec.ofFin [] 2 1 `BitVec []) : RowTypedAtV PTcorpus env `BitVec.ofFin [] :=
  rowTypedAtV_spine PTcorpus env _ _ [true] [true] _ _ spec_BitVec_ofFin hnd hT

theorem spec_HAdd_mk : SpineSpec PTcorpus `HAdd.mk [.zero, .zero, .zero] [false, false, false] [true] `HAdd [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_9) (u := ty_10) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HAdd_mk (env : Environment) (hnd : ¬ IsDefn env `HAdd)
    (hT : EnvDepSpine env `HAdd.mk [.zero, .zero, .zero] 4 3 `HAdd [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HAdd.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HAdd_mk hnd hT

theorem spec_HAnd_mk : SpineSpec PTcorpus `HAnd.mk [.zero, .zero, .zero] [false, false, false] [true] `HAnd [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_10) (u := ty_11) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HAnd_mk (env : Environment) (hnd : ¬ IsDefn env `HAnd)
    (hT : EnvDepSpine env `HAnd.mk [.zero, .zero, .zero] 4 3 `HAnd [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HAnd.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HAnd_mk hnd hT

theorem spec_HAppend_mk : SpineSpec PTcorpus `HAppend.mk [.zero, .zero, .zero] [false, false, false] [true] `HAppend [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_11) (u := ty_12) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HAppend_mk (env : Environment) (hnd : ¬ IsDefn env `HAppend)
    (hT : EnvDepSpine env `HAppend.mk [.zero, .zero, .zero] 4 3 `HAppend [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HAppend.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HAppend_mk hnd hT

theorem spec_HDiv_mk : SpineSpec PTcorpus `HDiv.mk [.zero, .zero, .zero] [false, false, false] [true] `HDiv [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_12) (u := ty_13) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HDiv_mk (env : Environment) (hnd : ¬ IsDefn env `HDiv)
    (hT : EnvDepSpine env `HDiv.mk [.zero, .zero, .zero] 4 3 `HDiv [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HDiv.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HDiv_mk hnd hT

theorem spec_HMod_mk : SpineSpec PTcorpus `HMod.mk [.zero, .zero, .zero] [false, false, false] [true] `HMod [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_13) (u := ty_14) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HMod_mk (env : Environment) (hnd : ¬ IsDefn env `HMod)
    (hT : EnvDepSpine env `HMod.mk [.zero, .zero, .zero] 4 3 `HMod [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HMod.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HMod_mk hnd hT

theorem spec_HMul_mk : SpineSpec PTcorpus `HMul.mk [.zero, .zero, .zero] [false, false, false] [true] `HMul [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_14) (u := ty_15) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HMul_mk (env : Environment) (hnd : ¬ IsDefn env `HMul)
    (hT : EnvDepSpine env `HMul.mk [.zero, .zero, .zero] 4 3 `HMul [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HMul.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HMul_mk hnd hT

theorem spec_HOr_mk : SpineSpec PTcorpus `HOr.mk [.zero, .zero, .zero] [false, false, false] [true] `HOr [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_15) (u := ty_16) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HOr_mk (env : Environment) (hnd : ¬ IsDefn env `HOr)
    (hT : EnvDepSpine env `HOr.mk [.zero, .zero, .zero] 4 3 `HOr [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HOr.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HOr_mk hnd hT

theorem spec_HPow_mk : SpineSpec PTcorpus `HPow.mk [.zero, .zero, .zero] [false, false, false] [true] `HPow [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_16) (u := ty_17) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HPow_mk (env : Environment) (hnd : ¬ IsDefn env `HPow)
    (hT : EnvDepSpine env `HPow.mk [.zero, .zero, .zero] 4 3 `HPow [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HPow.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HPow_mk hnd hT

theorem spec_HShiftLeft_mk : SpineSpec PTcorpus `HShiftLeft.mk [.zero, .zero, .zero] [false, false, false] [true] `HShiftLeft [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_17) (u := ty_18) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HShiftLeft_mk (env : Environment) (hnd : ¬ IsDefn env `HShiftLeft)
    (hT : EnvDepSpine env `HShiftLeft.mk [.zero, .zero, .zero] 4 3 `HShiftLeft [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HShiftLeft.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HShiftLeft_mk hnd hT

theorem spec_HShiftRight_mk : SpineSpec PTcorpus `HShiftRight.mk [.zero, .zero, .zero] [false, false, false] [true] `HShiftRight [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_18) (u := ty_19) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HShiftRight_mk (env : Environment) (hnd : ¬ IsDefn env `HShiftRight)
    (hT : EnvDepSpine env `HShiftRight.mk [.zero, .zero, .zero] 4 3 `HShiftRight [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HShiftRight.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HShiftRight_mk hnd hT

theorem spec_HSub_mk : SpineSpec PTcorpus `HSub.mk [.zero, .zero, .zero] [false, false, false] [true] `HSub [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_19) (u := ty_20) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HSub_mk (env : Environment) (hnd : ¬ IsDefn env `HSub)
    (hT : EnvDepSpine env `HSub.mk [.zero, .zero, .zero] 4 3 `HSub [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HSub.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HSub_mk hnd hT

theorem spec_HXor_mk : SpineSpec PTcorpus `HXor.mk [.zero, .zero, .zero] [false, false, false] [true] `HXor [.zero, .zero, .zero] :=
  spineSpec_of_refines (t := tm_20) (u := ty_21) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_HXor_mk (env : Environment) (hnd : ¬ IsDefn env `HXor)
    (hT : EnvDepSpine env `HXor.mk [.zero, .zero, .zero] 4 3 `HXor [.zero, .zero, .zero]) : RowTypedAtV PTcorpus env `HXor.mk [.zero, .zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false, false] [true] _ _ spec_HXor_mk hnd hT

theorem spec_OfNat_mk : SpineSpec PTcorpus `OfNat.mk [.zero] [false, true] [true] `OfNat [.zero] :=
  spineSpec_of_refines (t := tm_35) (u := ty_33) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_OfNat_mk (env : Environment) (hnd : ¬ IsDefn env `OfNat)
    (hT : EnvDepSpine env `OfNat.mk [.zero] 3 2 `OfNat [.zero]) : RowTypedAtV PTcorpus env `OfNat.mk [.zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, true] [true] _ _ spec_OfNat_mk hnd hT

theorem spec_PProd_mk : SpineSpec PTcorpus `PProd.mk [.succ .zero, .succ .zero] [false, false] [true, true] `PProd [.succ .zero, .succ .zero] :=
  spineSpec_of_refines (t := tm_37) (u := ty_35) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_PProd_mk (env : Environment) (hnd : ¬ IsDefn env `PProd)
    (hT : EnvDepSpine env `PProd.mk [.succ .zero, .succ .zero] 4 2 `PProd [.succ .zero, .succ .zero]) : RowTypedAtV PTcorpus env `PProd.mk [.succ .zero, .succ .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false] [true, true] _ _ spec_PProd_mk hnd hT

theorem spec_Pow_mk : SpineSpec PTcorpus `Pow.mk [.zero, .zero] [false, false] [true] `Pow [.zero, .zero] :=
  spineSpec_of_refines (t := tm_39) (u := ty_37) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_Pow_mk (env : Environment) (hnd : ¬ IsDefn env `Pow)
    (hT : EnvDepSpine env `Pow.mk [.zero, .zero] 3 2 `Pow [.zero, .zero]) : RowTypedAtV PTcorpus env `Pow.mk [.zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false] [true] _ _ spec_Pow_mk hnd hT

theorem spec_Prod_mk : SpineSpec PTcorpus `Prod.mk [.zero, .zero] [false, false] [true, true] `Prod [.zero, .zero] :=
  spineSpec_of_refines (t := tm_40) (u := ty_38) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_Prod_mk (env : Environment) (hnd : ¬ IsDefn env `Prod)
    (hT : EnvDepSpine env `Prod.mk [.zero, .zero] 4 2 `Prod [.zero, .zero]) : RowTypedAtV PTcorpus env `Prod.mk [.zero, .zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, false] [true, true] _ _ spec_Prod_mk hnd hT

theorem spec_Sparkle_Core_HasDomain_mk : SpineSpec PTcorpus `Sparkle.Core.HasDomain.mk [] [false, true] [] `Sparkle.Core.HasDomain [] :=
  spineSpec_of_refines (t := tm_45) (u := ty_42) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_Sparkle_Core_HasDomain_mk (env : Environment) (hnd : ¬ IsDefn env `Sparkle.Core.HasDomain)
    (hT : EnvDepSpine env `Sparkle.Core.HasDomain.mk [] 2 2 `Sparkle.Core.HasDomain []) : RowTypedAtV PTcorpus env `Sparkle.Core.HasDomain.mk [] :=
  rowTypedAtV_spine PTcorpus env _ _ [false, true] [] _ _ spec_Sparkle_Core_HasDomain_mk hnd hT

theorem spec_Sparkle_Core_Signal_Signal_mk : SpineSpec PTcorpus `Sparkle.Core.Signal.Signal.mk [.zero] [true, false] [true] `Sparkle.Core.Signal.Signal [.zero] :=
  spineSpec_of_refines (t := tm_46) (u := ty_43) (by refines_tac) rfl rfl

theorem ptc_spine_rowTypedV_Sparkle_Core_Signal_Signal_mk (env : Environment) (hnd : ¬ IsDefn env `Sparkle.Core.Signal.Signal)
    (hT : EnvDepSpine env `Sparkle.Core.Signal.Signal.mk [.zero] 3 2 `Sparkle.Core.Signal.Signal [.zero]) : RowTypedAtV PTcorpus env `Sparkle.Core.Signal.Signal.mk [.zero] :=
  rowTypedAtV_spine PTcorpus env _ _ [true, false] [true] _ _ spec_Sparkle_Core_Signal_Signal_mk hnd hT

end Tools.ShippingGen5PTCorpusSpec
