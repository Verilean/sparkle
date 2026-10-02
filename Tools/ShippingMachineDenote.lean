import Tools.ShippingMachineRef
import Tools.ShippingMachineSource

/-! # A `circuit do` is its reference machine

`machine_ref_trace` says the emitted module implements the reference
machine of the terms. This file proves, ONCE, that a `circuit do` whose
pending writes and result are — by `rfl`, per declaration — the typed
evaluation of those terms, has the reference machine's state and outputs:

* `TVal`: a typed valuation of the binders, built from the state tuple of
  the `circuit do` (`slotVal`) and its hardware `let`s in order (`letVal`).
  The casts in it are `dite`s on width equalities, which reduce on concrete
  widths, so a declaration identifies its own writes with
  `evalTerms nexts (typed valuation)` by `rfl`.
* `agree`: the typed valuation and the reference machine's store valuation
  give every term the same value.
* `packList_field`: the fields of the packed core.
* `denote_state`: the state tuple of the `circuit do`, encoded, IS the
  reference machine's state at every time; `denote_out`: a typed term that
  is a field of the core has the reference machine's output there. -/
namespace Tools.ShippingMachineDenote
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource

/-! ## Typed terms and values -/

/-- A list of terms, one per sort. -/
inductive Terms : List SType → Type
  | nil : Terms []
  | cons {s : SType} {ss : List SType} : Term s → Terms ss → Terms (s :: ss)

/-- The Lean types of a list of sorts. -/
abbrev tys (ss : List SType) : List Type := ss.map SType.Type

/-- The encoding of a typed value: a Bool as one bit, a BitVec as itself. -/
def enc : (s : SType) → s.Type → Nat
  | .bool, b => encodeBool b
  | .bits _, v => v.toNat

/-- The encoded state tuple, slot by slot (0 beyond the last slot). -/
def encState : (ss : List SType) → HList (tys ss) → Nat → Nat
  | [], _, _ => 0
  | s :: _, x, 0 => enc s x.1
  | _ :: ss, x, i + 1 => encState ss x.2 i

theorem encState_ge : ∀ (ss : List SType) (x : HList (tys ss)) (i : Nat), ss.length ≤ i →
    encState ss x i = 0
  | [], _, _, _ => rfl
  | _ :: _, _, 0, h => by simp at h
  | _ :: ss, x, i + 1, h => encState_ge ss x.2 i (by simpa using h)

/-- A typed valuation of the binders, by position. -/
structure TVal where
  b : Nat → Bool
  v : (p : Nat) → (w : Nat) → BitVec w

/-- Give position `p` a typed value. (The cast is a `dite` on the width.) -/
def TVal.set (V : TVal) (p : Nat) : (s : SType) → s.Type → TVal
  | .bool, x => ⟨fun q => if q = p then x else V.b q, V.v⟩
  | .bits w, x =>
    ⟨V.b, fun q n => if q = p then (if h : w = n then h ▸ x else 0#n) else V.v q n⟩

/-- The slots: position `kIn + i` holds component `i` of the state tuple. -/
def slotVal (kIn : Nat) : (ss : List SType) → HList (tys ss) → Nat → TVal → TVal
  | [], _, _, V => V
  | s :: ss, x, i, V => slotVal kIn ss x.2 (i + 1) (V.set (kIn + i) s x.1)

/-- The hardware `let`s, in order: each gets the value of its term under the
valuation so far. -/
def letVal (bpos vpos : Nat → Nat) : List (Σ s : SType, Term s) → Nat → TVal → TVal
  | [], _, V => V
  | l :: ls, p, V =>
    letVal bpos vpos ls (p + 1)
      (V.set p l.1 (eval (fun j => V.b (bpos j)) (fun j w => V.v (vpos j) w) l.2))

/-- The typed values of a list of terms. -/
def evalTerms (b : Nat → Bool) (v : (j : Nat) → (w : Nat) → BitVec w) :
    {ss : List SType} → Terms ss → HList (tys ss)
  | _, .nil => ()
  | _, .cons t ts => (eval b v t, evalTerms b v ts)

/-- The packed field of a typed term: a Bool as `mux b 1#1 0#1`. -/
def toField : (s : SType) → Term s → Σ w : Nat, Term (.bits w)
  | .bool, t => ⟨1, .mux t (.bitsLit 1 1) (.bitsLit 1 0)⟩
  | .bits w, t => ⟨w, t⟩

theorem eval_toField (b : Nat → Bool) (v : (j : Nat) → (w : Nat) → BitVec w) :
    ∀ (s : SType) (t : Term s),
      (eval b v (toField s t).2 : BitVec (toField s t).1).toNat = enc s (eval b v t)
  | .bool, t => by
    show (if eval b v t then BitVec.ofNat 1 1 else BitVec.ofNat 1 0).toNat = encodeBool _
    cases eval b v t <;> rfl
  | .bits _, _ => rfl

/-- The fields of a list of typed terms. -/
def Terms.fields : {ss : List SType} → Terms ss → List (Σ w : Nat, Term (.bits w))
  | _, .nil => []
  | _, .cons (s := s) t ts => toField s t :: ts.fields

theorem encState_evalTerms (b : Nat → Bool) (v : (j : Nat) → (w : Nat) → BitVec w) :
    ∀ {ss : List SType} (ts : Terms ss) (i : Nat) (g : Σ w : Nat, Term (.bits w)),
      ts.fields[i]? = some g →
      encState ss (evalTerms b v ts) i = (eval b v g.2 : BitVec g.1).toNat
  | _, .nil, _, _, h => by simp [Terms.fields] at h
  | _, .cons (s := s) t ts, 0, g, h => by
    simp only [Terms.fields, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact (eval_toField b v s t).symm
  | _, .cons t ts, i + 1, g, h => by
    simp only [Terms.fields, List.getElem?_cons_succ] at h
    exact encState_evalTerms b v ts i g h

/-! ## The packed core -/

/-- Fields concatenated, the first in the high bits. -/
def packList : (Σ w : Nat, Term (.bits w)) → List (Σ w : Nat, Term (.bits w)) →
    Σ W : Nat, Term (.bits W)
  | f, [] => f
  | f, g :: gs => ⟨f.1 + (packList g gs).1, .concat f.2 (packList g gs).2⟩

theorem packList_width : ∀ (f : Σ w : Nat, Term (.bits w)) (gs : List (Σ w : Nat, Term (.bits w))),
    (packList f gs).1 = ((f :: gs).map (·.1)).sum
  | f, [] => by simp [packList]
  | f, g :: gs => by
    simp only [packList, List.map_cons, List.sum_cons, packList_width g gs]

theorem drop_sum_le {α : Type} (wd : α → Nat) : ∀ (l : List α) (k : Nat) (g : α),
    l[k]? = some g → ((l.drop (k + 1)).map wd).sum + wd g ≤ (l.map wd).sum
  | [], _, _, h => by simp at h
  | a :: l, 0, g, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [Nat.add_comm]
  | a :: l, k + 1, g, h => by
    simp only [List.getElem?_cons_succ] at h
    have := drop_sum_le wd l k g h
    simp only [List.drop_succ_cons, List.map_cons, List.sum_cons]
    omega

/-- **The fields of a packed value**: field `k` sits above the fields after
it. -/
theorem packList_field (b : Nat → Bool) (v : (j : Nat) → (w : Nat) → BitVec w) :
    ∀ (gs : List (Σ w : Nat, Term (.bits w))) (f : Σ w : Nat, Term (.bits w)) (k : Nat)
      (g : Σ w : Nat, Term (.bits w)), (f :: gs)[k]? = some g →
      mask g.1 ((eval b v (packList f gs).2 : BitVec (packList f gs).1).toNat >>>
          (((f :: gs).drop (k + 1)).map (·.1)).sum) =
        (eval b v g.2 : BitVec g.1).toNat
  | [], f, 0, g, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simpa [packList] using field_all (eval b v f.2 : BitVec f.1)
  | [], f, k + 1, g, h => by simp at h
  | g0 :: gs, f, 0, g, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    show mask f.1 ((eval b v f.2 ++ eval b v (packList g0 gs).2 :
      BitVec (f.1 + (packList g0 gs).1)).toNat >>> _) = _
    rw [show (((f :: g0 :: gs).drop (0 + 1)).map (·.1)).sum = (packList g0 gs).1 by
      rw [packList_width]; rfl]
    rw [field_hi _ _ (Nat.le_refl _), Nat.sub_self]
    exact field_all _
  | g0 :: gs, f, k + 1, g, h => by
    simp only [List.getElem?_cons_succ] at h
    show mask g.1 ((eval b v f.2 ++ eval b v (packList g0 gs).2 :
      BitVec (f.1 + (packList g0 gs).1)).toNat >>> _) = _
    have hle := drop_sum_le (fun q : Σ w : Nat, Term (.bits w) => q.1) (g0 :: gs) k g h
    rw [show (((f :: g0 :: gs).drop (k + 1 + 1)).map (·.1)).sum =
      (((g0 :: gs).drop (k + 1)).map (·.1)).sum by rfl]
    rw [field_lo _ _ (by rw [packList_width]; exact hle)]
    exact packList_field b v gs g0 k g h

/-! ## Congruence at declared widths -/

theorem reads_true : ∀ {s : SType} (e : Term s),
    reads (fun _ => true) (fun _ => true) e = true := by
  intro s e
  induction e <;> simp_all [reads]

/-- A term's value depends on the inputs it reads, each at its declared
width. -/
theorem eval_congr_wf {kb kv : Nat} {vw : Nat → Nat} {okB okV : Nat → Bool}
    {b b' : Nat → Bool} {v v' : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → okB j = true → b j = b' j)
    (hv : ∀ j, j < kv → okV j = true → v j (vw j) = v' j (vw j)) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → reads okB okV e = true →
      eval b v e = eval b' v' e := by
  intro s e
  induction e with
  | boolInput j => intro hw hr; exact hb j hw hr
  | bitsInput w j =>
    intro hw hr
    obtain ⟨hj, hwj, _⟩ := hw
    subst hwj
    exact hv j hj hr
  | boolLit _ => intro _ _; rfl
  | bitsLit _ _ => intro _ _; rfl
  | bitsNum _ _ => intro _ _; rfl
  | binary op a b iha ihb =>
    intro hw hr; simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, iha hw.1 hr.1, ihb hw.2 hr.2]
  | compare op a b iha ihb =>
    intro hw hr; simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, iha hw.1 hr.1, ihb hw.2 hr.2]
  | boolBinary op a b iha ihb =>
    intro hw hr; simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, iha hw.1 hr.1, ihb hw.2 hr.2]
  | boolNot a iha => intro hw hr; simp only [reads] at hr; simp only [eval, iha hw hr]
  | boolEq a b iha ihb =>
    intro hw hr; simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, iha hw.1 hr.1, ihb hw.2 hr.2]
  | mux c a b ihc iha ihb =>
    intro hw hr; simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, ihc hw.1 hr.1.1, iha hw.2.1 hr.1.2, ihb hw.2.2 hr.2]
  | setw w' a iha => intro hw hr; simp only [reads] at hr; simp only [eval, iha hw.1 hr]
  | appCompare op a b iha ihb =>
    intro hw hr; simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, iha hw.1 hr.1, ihb hw.2 hr.2]
  | appBool op a b iha ihb =>
    intro hw hr; simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, iha hw.1 hr.1, ihb hw.2 hr.2]
  | appBool2 f a b iha ihb =>
    intro hw hr; simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, iha hw.1 hr.1, ihb hw.2 hr.2]
  | slice nm start len a iha =>
    intro hw hr; simp only [reads] at hr; simp only [eval, iha hw.1 hr]
  | concat a b iha ihb =>
    intro hw hr; simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, iha hw.1 hr.1, ihb hw.2 hr.2]
  | concatLitHi k v b ihb =>
    intro hw hr; simp only [reads] at hr; simp only [eval, ihb hw.1 hr]
  | concatLitLo a k v iha =>
    intro hw hr; simp only [reads] at hr; simp only [eval, iha hw.1 hr]
  | zextMap nm k a iha =>
    intro hw hr; simp only [reads] at hr; simp only [eval, iha hw.1 hr]
  | sliceF nm start len a iha =>
    intro hw hr; simp only [reads] at hr; simp only [eval, iha hw.1 hr]

/-! ## The typed valuation and the store agree -/

theorem set_b_ne {V : TVal} {p q : Nat} {s : SType} {x : s.Type} (h : q ≠ p) :
    (V.set p s x).b q = V.b q := by
  cases s <;> simp [TVal.set, h]

theorem set_v_ne {V : TVal} {p q : Nat} {s : SType} {x : s.Type} (h : q ≠ p) (n : Nat) :
    (V.set p s x).v q n = V.v q n := by
  cases s <;> simp [TVal.set, h]

theorem set_b_eq (V : TVal) (p : Nat) (x : Bool) : (V.set p .bool x).b p = x := by
  simp [TVal.set]

theorem set_v_eq (V : TVal) (p w : Nat) (x : BitVec w) : (V.set p (.bits w) x).v p w = x := by
  simp [TVal.set]

theorem slotVal_lt (kIn : Nat) : ∀ (ss : List SType) (x : HList (tys ss)) (i0 : Nat) (V : TVal)
    (q : Nat), q < kIn + i0 →
    (slotVal kIn ss x i0 V).b q = V.b q ∧ ∀ n, (slotVal kIn ss x i0 V).v q n = V.v q n
  | [], _, _, _, _, _ => ⟨rfl, fun _ => rfl⟩
  | s :: ss, x, i0, V, q, h => by
    obtain ⟨hb, hv⟩ := slotVal_lt kIn ss x.2 (i0 + 1) (V.set (kIn + i0) s x.1) q (by omega)
    exact ⟨hb.trans (set_b_ne (by omega)), fun n => (hv n).trans (set_v_ne (by omega) n)⟩

/-- A slot position of the typed valuation holds the state's component. -/
theorem slotVal_at (kIn : Nat) : ∀ (ss : List SType) (x : HList (tys ss)) (i0 : Nat) (V : TVal)
    (i : Nat) (s : SType), ss[i]? = some s →
    (s = .bool → encodeBool ((slotVal kIn ss x i0 V).b (kIn + i0 + i)) = encState ss x i) ∧
    (∀ w, s = .bits w → ((slotVal kIn ss x i0 V).v (kIn + i0 + i) w).toNat = encState ss x i)
  | [], _, _, _, _, _, h => by simp at h
  | s0 :: ss, x, i0, V, 0, s, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    obtain ⟨hb, hv⟩ := slotVal_lt kIn ss x.2 (i0 + 1) (V.set (kIn + i0) s0 x.1) (kIn + i0)
      (by omega)
    refine ⟨fun hs => ?_, fun w hs => ?_⟩
    · subst hs
      exact congrArg encodeBool (hb.trans (set_b_eq _ _ _))
    · subst hs
      exact congrArg BitVec.toNat ((hv w).trans (set_v_eq _ _ _ _))
  | s0 :: ss, x, i0, V, i + 1, s, h => by
    simp only [List.getElem?_cons_succ] at h
    have := slotVal_at kIn ss x.2 (i0 + 1) (V.set (kIn + i0) s0 x.1) i s h
    rw [show kIn + i0 + (i + 1) = kIn + (i0 + 1) + i by omega]
    exact this

/-- The typed valuation and a store valuation agree below a position, at
every binder's declared sort. -/
def Agree (K : Nat → Option SType) (below : Nat) (T : TVal) (B : Nat → Bool)
    (V : (p : Nat) → (w : Nat) → BitVec w) : Prop :=
  ∀ p, p < below →
    (K p = some .bool → T.b p = B p) ∧ (∀ w, K p = some (.bits w) → T.v p w = V p w)

theorem bool_of_enc (b : Bool) : (encodeBool b == 1) = b := by cases b <;> rfl

/-- The slots: the typed valuation of the state tuple agrees with the store
of the encoded state. -/
theorem agree_slots {kIn : Nat} {K : Nat → Option SType} (inB : Nat → Bool)
    (inV : (j : Nat) → (n : Nat) → BitVec n) (ss : List SType) (x : HList (tys ss))
    (slotK : ∀ i s, ss[i]? = some s → K (kIn + i) = some s) :
    Agree K (kIn + ss.length) (slotVal kIn ss x 0 ⟨inB, inV⟩)
      (valB kIn inB (fun p => encState ss x (p - kIn)))
      (valV kIn inV (fun p => encState ss x (p - kIn))) := by
  intro p hp
  by_cases hk : p < kIn
  · obtain ⟨hb, hv⟩ := slotVal_lt kIn ss x 0 ⟨inB, inV⟩ p (by omega)
    exact ⟨fun _ => by simp [hb, valB, hk], fun w _ => by simp [hv w, valV, hk]⟩
  · have hi : p - kIn < ss.length := by omega
    have hs := slotK (p - kIn) ss[p - kIn] (List.getElem?_eq_getElem hi)
    rw [show kIn + (p - kIn) = p by omega] at hs
    obtain ⟨hb, hv⟩ := slotVal_at kIn ss x 0 ⟨inB, inV⟩ (p - kIn) ss[p - kIn]
      (List.getElem?_eq_getElem hi)
    rw [show kIn + 0 + (p - kIn) = p by omega] at hb hv
    refine ⟨fun hK => ?_, fun w hK => ?_⟩
    · have hsort : ss[p - kIn] = .bool := Option.some.inj (hs.symm.trans hK)
      simp only [valB, hk, if_false, ← hb hsort, bool_of_enc]
    · have hsort : ss[p - kIn] = .bits w := Option.some.inj (hs.symm.trans hK)
      simp only [valV, hk, if_false, ← hv w hsort, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The typed `let`s: each term well formed, reading earlier positions only,
at a position of its own sort. -/
def LetsTyped (bpos vpos : Nat → Nat) (kb kv : Nat) (vw : Nat → Nat) (K : Nat → Option SType) :
    Nat → List (Σ s : SType, Term s) → Prop
  | _, [] => True
  | p, l :: ls =>
    l.2.WF kb kv vw ∧
      reads (fun j => decide (bpos j < p)) (fun j => decide (vpos j < p)) l.2 = true ∧
      K p = some l.1 ∧ LetsTyped bpos vpos kb kv vw K (p + 1) ls

theorem valB_set {kIn : Nat} {inB : Nat → Bool} {σ : Nat → Nat} {p q n : Nat} (h : q ≠ p) :
    valB kIn inB (fun r => if r = p then n else σ r) q = valB kIn inB σ q := by
  simp [valB, h]

theorem valV_set {kIn : Nat} {inV : (j : Nat) → (n : Nat) → BitVec n} {σ : Nat → Nat}
    {p q n : Nat} (h : q ≠ p) (w : Nat) :
    valV kIn inV (fun r => if r = p then n else σ r) q w = valV kIn inV σ q w := by
  simp [valV, h]

/-- The `let`s: computing them typed and computing them in the store keep
the two valuations in agreement. -/
theorem agree_lets {kIn kb kv : Nat} {vw bpos vpos : Nat → Nat} {K : Nat → Option SType}
    {inB : Nat → Bool} {inV : (j : Nat) → (n : Nat) → BitVec n}
    (hbk : ∀ j, j < kb → K (bpos j) = some .bool)
    (hvk : ∀ j, j < kv → K (vpos j) = some (.bits (vw j))) :
    ∀ (ls : List (Σ s : SType, Term s)) (p : Nat) (T : TVal) (σ : Nat → Nat), kIn ≤ p →
      Agree K p T (valB kIn inB σ) (valV kIn inV σ) →
      LetsTyped bpos vpos kb kv vw K p ls →
      Agree K (p + ls.length) (letVal bpos vpos ls p T)
        (valB kIn inB (letStore bpos vpos kIn inB inV (ls.map fun l => toField l.1 l.2) p σ))
        (valV kIn inV (letStore bpos vpos kIn inB inV (ls.map fun l => toField l.1 l.2) p σ))
  | [], p, T, σ, _, h, _ => h
  | l :: ls, p, T, σ, hp, hagree, ⟨hwf, hreads, hK, hrest⟩ => by
    have hnot : ¬ p < kIn := by omega
    -- the `let`'s term has the same value under both valuations
    have hev : eval (fun j => T.b (bpos j)) (fun j w => T.v (vpos j) w) l.2 =
        eval (fun j => valB kIn inB σ (bpos j)) (fun j w => valV kIn inV σ (vpos j) w) l.2 := by
      apply eval_congr_wf (okB := fun j => decide (bpos j < p))
        (okV := fun j => decide (vpos j < p)) _ _ l.2 hwf hreads
      · intro j hj hlt
        exact (hagree (bpos j) (by simpa using hlt)).1 (hbk j hj)
      · intro j hj hlt
        exact (hagree (vpos j) (by simpa using hlt)).2 (vw j) (hvk j hj)
    have hstore : (eval (fun j => valB kIn inB σ (bpos j)) (fun j w => valV kIn inV σ (vpos j) w)
        (toField l.1 l.2).2 : BitVec (toField l.1 l.2).1).toNat =
        enc l.1 (eval (fun j => T.b (bpos j)) (fun j w => T.v (vpos j) w) l.2) := by
      rw [eval_toField, hev]
    have step : Agree K (p + 1)
        (T.set p l.1 (eval (fun j => T.b (bpos j)) (fun j w => T.v (vpos j) w) l.2))
        (valB kIn inB (fun q => if q = p then
          (eval (fun j => valB kIn inB σ (bpos j)) (fun j w => valV kIn inV σ (vpos j) w)
            (toField l.1 l.2).2 : BitVec (toField l.1 l.2).1).toNat else σ q))
        (valV kIn inV (fun q => if q = p then
          (eval (fun j => valB kIn inB σ (bpos j)) (fun j w => valV kIn inV σ (vpos j) w)
            (toField l.1 l.2).2 : BitVec (toField l.1 l.2).1).toNat else σ q)) := by
      intro q hq
      by_cases hqp : q = p
      · subst hqp
        rw [hstore]
        obtain ⟨s, t⟩ := l
        cases s with
        | bool =>
          refine ⟨fun _ => ?_, fun w hw => ?_⟩
          · simp only [valB, hnot, if_false, if_true, set_b_eq, enc, bool_of_enc]
          · rw [hK] at hw; cases hw
        | bits w0 =>
          refine ⟨fun hb => ?_, fun w hw => ?_⟩
          · rw [hK] at hb; cases hb
          · rw [hK] at hw
            cases hw
            simp only [valV, hnot, if_false, if_true, set_v_eq, enc, BitVec.ofNat_toNat,
              BitVec.setWidth_eq]
      · have hlt : q < p := by omega
        obtain ⟨hb, hv⟩ := hagree q hlt
        exact ⟨fun hk => by rw [set_b_ne hqp, valB_set hqp]; exact hb hk,
          fun w hk => by rw [set_v_ne hqp, valV_set hqp]; exact hv w hk⟩
    have := agree_lets hbk hvk ls (p + 1) _ _ (by omega) step hrest
    rw [show p + (l :: ls).length = p + 1 + ls.length by simp; omega]
    exact this

/-- Agreement on every position gives every term the same value. -/
theorem eval_agree {kb kv N : Nat} {vw bpos vpos : Nat → Nat} {K : Nat → Option SType}
    {T : TVal} {B : Nat → Bool} {V : (p : Nat) → (w : Nat) → BitVec w}
    (hbk : ∀ j, j < kb → K (bpos j) = some .bool ∧ bpos j < N)
    (hvk : ∀ j, j < kv → K (vpos j) = some (.bits (vw j)) ∧ vpos j < N)
    (h : Agree K N T B V) {s : SType} (e : Term s) (hwf : e.WF kb kv vw) :
    eval (fun j => T.b (bpos j)) (fun j w => T.v (vpos j) w) e =
      eval (fun j => B (bpos j)) (fun j w => V (vpos j) w) e :=
  eval_congr_wf (okB := fun _ => true) (okV := fun _ => true)
    (fun j hj _ => (h (bpos j) (hbk j hj).2).1 (hbk j hj).1)
    (fun j hj _ => (h (vpos j) (hvk j hj).2).2 (vw j) (hvk j hj).1) e hwf (reads_true e)

theorem toField_wf {kb kv : Nat} {vw : Nat → Nat} : ∀ (s : SType) (t : Term s),
    t.WF kb kv vw → (toField s t).2.WF kb kv vw
  | .bool, _, h => ⟨h, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  | .bits _, _, h => h

/-! ## A `circuit do` is its reference machine -/

/-- The typed valuation of a cycle: the inputs' Signals at time `t`, the
state tuple `x`, the `let`s. -/
def typedVal {D : DomainConfig} (kIn : Nat) (bpos vpos : Nat → Nat) (ss : List SType)
    (ls : List (Σ s : SType, Term s)) (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys ss)) : TVal :=
  letVal bpos vpos ls (kIn + ss.length)
    (slotVal kIn ss x 0 ⟨fun p => (bools p).val t, fun p w => (bits p w).val t⟩)

/-- What the terms of a machine must satisfy, as facts about data. -/
structure TermFacts (kIn kb kv : Nat) (vw bpos vpos : Nat → Nat) (K : Nat → Option SType)
    (ss : List SType) (ls : List (Σ s : SType, Term s)) : Prop where
  bools : ∀ j, j < kb → K (bpos j) = some .bool ∧ bpos j < kIn + ss.length + ls.length
  bits : ∀ j, j < kv →
    K (vpos j) = some (.bits (vw j)) ∧ vpos j < kIn + ss.length + ls.length
  slots : ∀ i s, ss[i]? = some s → K (kIn + i) = some s
  lets : LetsTyped bpos vpos kb kv vw K (kIn + ss.length) ls

/-- The typed valuation of a cycle gives every well-formed term the value
the reference machine's store valuation gives it. -/
theorem eval_typed {D : DomainConfig} {kIn kb kv : Nat} {vw bpos vpos : Nat → Nat}
    {K : Nat → Option SType} {ss : List SType} {ls : List (Σ s : SType, Term s)}
    (facts : TermFacts kIn kb kv vw bpos vpos K ss ls)
    (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (t : Nat) (x : HList (tys ss)) {s : SType} (e : Term s) (hwf : e.WF kb kv vw) :
    eval (fun j => (typedVal kIn bpos vpos ss ls bools bits t x).b (bpos j))
        (fun j w => (typedVal kIn bpos vpos ss ls bools bits t x).v (vpos j) w) e =
      eval
        (fun j => valB kIn (fun p => (bools p).val t)
          (letStore bpos vpos kIn (fun p => (bools p).val t) (fun p w => (bits p w).val t)
            (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
            (fun p => encState ss x (p - kIn))) (bpos j))
        (fun j w => valV kIn (fun p w => (bits p w).val t)
          (letStore bpos vpos kIn (fun p => (bools p).val t) (fun p w => (bits p w).val t)
            (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
            (fun p => encState ss x (p - kIn))) (vpos j) w) e :=
  eval_agree facts.bools facts.bits
    (agree_lets (fun j hj => (facts.bools j hj).1) (fun j hj => (facts.bits j hj).1) ls
      (kIn + ss.length) _ _ (by omega)
      (agree_slots _ _ ss x facts.slots) facts.lets) e hwf

/-- The fit of a slot layout with the fields of the packed core: slot `i`
is field `nOuts + i`. -/
def SlotsFit (fields : List (Σ w : Nat, Term (.bits w))) (nOuts : Nat)
    (slots : List SlotField) : Prop :=
  ∀ i f, slots[i]? = some f → ∃ g, fields[nOuts + i]? = some g ∧ f.width = g.1 ∧
    f.lo = ((fields.drop (nOuts + i + 1)).map (·.1)).sum

set_option maxHeartbeats 1000000 in
/-- **The state of a `circuit do` is the state of its reference machine.**
Let the body's pending writes be, at every cycle and for every state
signal, the typed values of the terms `nexts` (`H2` — `rfl` for a
declaration). Then the state tuple of `runCircuitH inits body`, encoded, is
the reference machine's state at every time. -/
theorem denote_state {D : DomainConfig} {ss : List SType} [Inhabited (HList (tys ss))]
    {ρ : Type} (inits : HList (tys ss))
    (body : RegList D (HList (tys ss)) (Circuit.SigList D (tys ss)) (tys ss) →
      Circuit D (Circuit.SigList D (tys ss)) ρ)
    (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    {kIn kb kv : Nat} {vw bpos vpos : Nat → Nat} {K : Nat → Option SType}
    (ls : List (Σ s : SType, Term s)) (nexts : Terms ss)
    (f0 : Σ w : Nat, Term (.bits w)) (rest : List (Σ w : Nat, Term (.bits w)))
    {c : Nat} (core : Term (.bits c)) (slots : List SlotField) (nOuts : Nat)
    (hcore : (⟨c, core⟩ : Σ W : Nat, Term (.bits W)) = packList f0 rest)
    (hnexts : (f0 :: rest).drop nOuts = nexts.fields)
    (hslots : SlotsFit (f0 :: rest) nOuts slots)
    (hslotsLen : slots.length = ss.length)
    (hinit : ∀ i, encState ss inits i = (slots[i]?.map (·.init)).getD 0)
    (facts : TermFacts kIn kb kv vw bpos vpos K ss ls)
    (nextsWF : ∀ g ∈ nexts.fields, g.2.WF kb kv vw)
    (H2 : ∀ (S : Signal D (HList (tys ss))) (t : Nat),
      valsAt (tys ss) (body (mkRegList S (tys ss) (fun s => s) (fun f => f))
          (mkHolds (tys ss) S)).snd t =
        evalTerms (fun j => (typedVal kIn bpos vpos ss ls bools bits t (S.val t)).b (bpos j))
          (fun j w => (typedVal kIn bpos vpos ss ls bools bits t (S.val t)).v (vpos j) w)
          nexts) :
    ∀ τ, encState ss ((stateLoop inits body).val τ) =
      RefMachine.state (RefMachine.mk kIn ss.length bpos vpos (ls.map fun l => toField l.1 l.2)
        c core slots) (fun τ p => (bools p).val τ) (fun τ p w => (bits p w).val τ) τ := by
  have hW : ∀ (l l' : Signal D (HList (tys ss))) (t : Nat), l.val t = l'.val t →
      valsAt (tys ss) (body (mkRegList l (tys ss) (fun s => s) (fun f => f))
          (mkHolds (tys ss) l)).snd t =
        valsAt (tys ss) (body (mkRegList l' (tys ss) (fun s => s) (fun f => f))
          (mkHolds (tys ss) l')).snd t := by
    intro l l' t h
    rw [H2 l t, H2 l' t, h]
  obtain ⟨h0, hs⟩ := circuit_state inits body hW
  intro τ
  induction τ with
  | zero =>
    funext i
    rw [h0, hinit i]
    rfl
  | succ τ ih =>
    funext i
    rw [hs τ, H2 _ τ]
    show _ = RefMachine.next _ _ _ _ i
    simp only [RefMachine.next]
    cases hf : slots[i]? with
    | none =>
      have hi : ss.length ≤ i := by
        have := List.getElem?_eq_none_iff.mp hf; omega
      simp only [hf]
      exact encState_ge ss _ i hi
    | some f =>
      obtain ⟨g, hg, hwid, hlo⟩ := hslots i f hf
      have hgn : nexts.fields[i]? = some g := by
        rw [← hnexts, List.getElem?_drop]; exact hg
      simp only [hf]
      rw [encState_evalTerms _ _ nexts i g hgn,
        eval_typed facts bools bits τ _ g.2 (nextsWF g (List.mem_of_getElem? hgn))]
      -- the field of the packed core
      have hpack := packList_field
        (fun j => valB kIn (fun p => (bools p).val τ)
          (letStore bpos vpos kIn (fun p => (bools p).val τ) (fun p w => (bits p w).val τ)
            (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
            (fun p => encState ss ((stateLoop inits body).val τ) (p - kIn))) (bpos j))
        (fun j w => valV kIn (fun p w => (bits p w).val τ)
          (letStore bpos vpos kIn (fun p => (bools p).val τ) (fun p w => (bits p w).val τ)
            (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
            (fun p => encState ss ((stateLoop inits body).val τ) (p - kIn))) (vpos j) w)
        rest f0 (nOuts + i) g hg
      rw [← hpack, hwid, hlo]
      have hc := congrArg (fun q : Σ W : Nat, Term (.bits W) =>
        (eval
          (fun j => valB kIn (fun p => (bools p).val τ)
            (letStore bpos vpos kIn (fun p => (bools p).val τ) (fun p w => (bits p w).val τ)
              (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
              (fun p => encState ss ((stateLoop inits body).val τ) (p - kIn))) (bpos j))
          (fun j w => valV kIn (fun p w => (bits p w).val τ)
            (letStore bpos vpos kIn (fun p => (bools p).val τ) (fun p w => (bits p w).val τ)
              (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
              (fun p => encState ss ((stateLoop inits body).val τ) (p - kIn))) (vpos j) w)
          q.2 : BitVec q.1).toNat) hcore
      simp only at hc
      rw [← hc, ih]
      rfl

set_option maxHeartbeats 1000000 in
/-- **An output of a `circuit do` is an output of its reference machine.**
A typed term that is field `k` of the packed core has, under the typed
valuation of the `circuit do` state at time `τ`, the reference machine's
output on that field. -/
theorem denote_out {D : DomainConfig} {ss : List SType} [Inhabited (HList (tys ss))]
    {ρ : Type} (inits : HList (tys ss))
    (body : RegList D (HList (tys ss)) (Circuit.SigList D (tys ss)) (tys ss) →
      Circuit D (Circuit.SigList D (tys ss)) ρ)
    (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    {kIn kb kv : Nat} {vw bpos vpos : Nat → Nat} {K : Nat → Option SType}
    (ls : List (Σ s : SType, Term s))
    (f0 : Σ w : Nat, Term (.bits w)) (rest : List (Σ w : Nat, Term (.bits w)))
    {c : Nat} (core : Term (.bits c)) (slots : List SlotField)
    (hcore : (⟨c, core⟩ : Σ W : Nat, Term (.bits W)) = packList f0 rest)
    (facts : TermFacts kIn kb kv vw bpos vpos K ss ls)
    (hstate : ∀ τ, encState ss ((stateLoop inits body).val τ) =
      RefMachine.state (RefMachine.mk kIn ss.length bpos vpos (ls.map fun l => toField l.1 l.2)
        c core slots) (fun τ p => (bools p).val τ) (fun τ p w => (bits p w).val τ) τ)
    {s : SType} (ot : Term s) (hwf : ot.WF kb kv vw) (k : Nat)
    (hk : (f0 :: rest)[k]? = some (toField s ot)) (τ : Nat) :
    enc s (eval
        (fun j => (typedVal kIn bpos vpos ss ls bools bits τ
          ((stateLoop inits body).val τ)).b (bpos j))
        (fun j w => (typedVal kIn bpos vpos ss ls bools bits τ
          ((stateLoop inits body).val τ)).v (vpos j) w) ot) =
      RefMachine.out (RefMachine.mk kIn ss.length bpos vpos (ls.map fun l => toField l.1 l.2)
        c core slots) (fun τ p => (bools p).val τ) (fun τ p w => (bits p w).val τ) τ
        ((((f0 :: rest).drop (k + 1)).map (·.1)).sum) (toField s ot).1 := by
  rw [← eval_toField, eval_typed facts bools bits τ _ _ (toField_wf s ot hwf)]
  have hpack := packList_field
    (fun j => valB kIn (fun p => (bools p).val τ)
      (letStore bpos vpos kIn (fun p => (bools p).val τ) (fun p w => (bits p w).val τ)
        (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
        (fun p => encState ss ((stateLoop inits body).val τ) (p - kIn))) (bpos j))
    (fun j w => valV kIn (fun p w => (bits p w).val τ)
      (letStore bpos vpos kIn (fun p => (bools p).val τ) (fun p w => (bits p w).val τ)
        (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
        (fun p => encState ss ((stateLoop inits body).val τ) (p - kIn))) (vpos j) w)
    rest f0 k (toField s ot) hk
  rw [← hpack]
  have hc := congrArg (fun q : Σ W : Nat, Term (.bits W) =>
    (eval
      (fun j => valB kIn (fun p => (bools p).val τ)
        (letStore bpos vpos kIn (fun p => (bools p).val τ) (fun p w => (bits p w).val τ)
          (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
          (fun p => encState ss ((stateLoop inits body).val τ) (p - kIn))) (bpos j))
      (fun j w => valV kIn (fun p w => (bits p w).val τ)
        (letStore bpos vpos kIn (fun p => (bools p).val τ) (fun p w => (bits p w).val τ)
          (ls.map fun l => toField l.1 l.2) (kIn + ss.length)
          (fun p => encState ss ((stateLoop inits body).val τ) (p - kIn))) (vpos j) w)
      q.2 : BitVec q.1).toNat) hcore
  simp only at hc
  rw [← hc, hstate τ]
  rfl

end Tools.ShippingMachineDenote
