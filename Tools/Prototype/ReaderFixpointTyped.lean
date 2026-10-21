import Tools.Prototype.ReaderFixpointSpec
import Tools.ShippingMachineClosesData

/-! # Unit LCQ prototype: the Expr → typed `letFields` / `quote` bridge (draft part 1)

UNBUILT. -/
namespace Tools.Prototype.ReaderTyped
open Lean Sparkle.Compiler.Elab Tools.ShippingUnifiedSource Tools.ShippingMachineDenote
open Tools.ShippingMachineEntry

theorem canon_machConcatE (dom : Lean.Expr) (m n : Nat) (a b : Lean.Expr) :
    ∃ K, machCanonAp (machConcatE dom m n a b) = .app (.app K (machCanonAp a)) (machCanonAp b) := by
  refine ⟨machCanonAp (mkApp4 (.const ``HAppend.hAppend [.zero, .zero, .zero]) (machSigT dom m)
    (machSigT dom n) (machSigT dom (m + n))
    (mkApp3 (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat []) dom (inlNatLit m)
      (inlNatLit n))), ?_⟩
  unfold machConcatE
  simp [mkApp6, machCanonAp, machCanonApNode]

theorem canon_eq_bvar {e : Lean.Expr} {b : Nat} (h : machCanonAp e = .bvar b) : e = .bvar b := by
  cases e <;> simp only [machCanonAp] at h <;> first | exact h | skip
  all_goals
    exfalso
    unfold machCanonApNode at h
    split at h <;> simp_all [mkApp, mkApp4, mkApp5]


theorem machPack_cons_ne {dom : Lean.Expr} {f g : Nat × Lean.Expr} {t : List (Nat × Lean.Expr)}
    {r : Nat × Lean.Expr} (h : machPack dom (f :: g :: t) = some r) :
    ∃ n b, machPack dom (g :: t) = some (n, b) ∧ r = (f.1 + n, machConcatE dom f.1 n f.2 b) := by
  conv at h => lhs; unfold machPack
  cases hp : machPack dom (g :: t) with
  | none => simp [hp] at h
  | some nb =>
    obtain ⟨n, b⟩ := nb
    simp only [hp, Option.some.injEq] at h
    exact ⟨n, b, rfl, h.symm⟩

/-- The `quote` of a `packLets` spine is the `concatE` spine; matched against the `machPack` of the
`machCanonAp`-canonicalised packed value, the fields line up one by one. -/
theorem peel (dom dom2 : Lean.Expr) (bB bV : Nat → Lean.Expr) :
    ∀ (Ls : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c))
      (lfs rest : List (Nat × Lean.Expr)), lfs.length = Ls.length → rest ≠ [] →
      ∀ (w : Nat) (P : Lean.Expr), machPack dom (lfs ++ rest) = some (w, P) →
      machCanonAp P = quote dom2 bB bV (packLets Ls core).2 →
      ∀ (i : Nat) (x : Nat × Lean.Expr) (y : Σ w : Nat, Term (.bits w)), lfs[i]? = some x →
        Ls[i]? = some y → machCanonAp x.2 = quote dom2 bB bV y.2
  | [], _, _, _, _, _, _, _, _, _, _, i, x, y, _, hy => by simp at hy
  | L :: Ls, c, core, lfs, rest, hlen, hne, w, P, hP, hq, i, x, y, hx, hy => by
    cases lfs with
    | nil => simp at hlen
    | cons f lfs' =>
      have hlen' : lfs'.length = Ls.length := by simpa using hlen
      cases hr : (lfs' ++ rest) with
      | nil => exact absurd (by simpa using (by simpa using hr : lfs' = [] ∧ rest = []).2) hne
      | cons g t =>
        rw [List.cons_append, hr] at hP
        obtain ⟨n, b, hb, hPe⟩ := machPack_cons_ne hP
        have hP' : P = machConcatE dom f.1 n f.2 b := by
          have := congrArg Prod.snd hPe; simpa using this
        subst hP'
        obtain ⟨K, hK⟩ := canon_machConcatE dom f.1 n f.2 b
        rw [hK] at hq
        have hq' : (Lean.Expr.app (Lean.Expr.app K (machCanonAp f.2)) (machCanonAp b)) =
            concatE dom2 _ _ (quote dom2 bB bV L.2) (quote dom2 bB bV (packLets Ls core).2) := hq
        unfold concatE mkApp6 at hq'
        injection hq' with h1 hb'
        injection h1 with _ ha'
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst hx; subst hy; exact ha'
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx hy
          exact peel dom dom2 bB bV Ls core lfs' rest hlen' hne n b (by rw [hr]; exact hb) hb' i x y hx hy


theorem mapM_get {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r →
      r.length = l.length ∧ ∀ (i : Nat) (y : β), r[i]? = some y → ∃ x, l[i]? = some x ∧ f x = some y
  | [], r, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hb : f a with
    | none => simp [hb] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hb, hl] at h
      | some bs =>
        simp [hb, hl] at h
        subst h
        obtain ⟨hl', hg⟩ := mapM_get f l bs hl
        refine ⟨by simp [hl'], ?_⟩
        intro i y hy
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hy; subst hy
          exact ⟨a, rfl, hb⟩
        | succ i => simp only [List.getElem?_cons_succ] at hy ⊢; exact hg i y hy

open Tools.ShippingReaderFuel in
/-- What the `body` of a `shapePost` success is: `machCanonAp` of the `machPack` of the closed `let`
fields, then the results and slots (the results are non-empty when `p.outs` is). -/
theorem shapePost_pack {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (hne : p.outs ≠ []) (h : shapePost ai p m st v = some sp) :
    ∃ (dom' : Lean.Expr) (lfs outF slotF : List (Nat × Lean.Expr)) (w : Nat) (P : Lean.Expr),
      st.lets.toList.mapM (fun x => machField dom' x.2.1
        (machClose st.insts.size st.kinds.size (Array.size st.lets) 0 x.2.2)) = some lfs ∧
      outF ≠ [] ∧ machPack dom' (lfs ++ outF ++ slotF) = some (w, P) ∧
      sp.body = machCanonAp P ∧ sp.layout.lets = st.lets.size := by
  unfold shapePost at h
  dsimp only at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h

  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨domE, _, dm, _, lfs, hlfs, h⟩ := h
  cases ht : p.tup? with
  | some ks =>
    simp only [ht, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨parts, _, fs, _, packed, _, outF, hoF, slotF, _, pk, hpk, h⟩ := h
    subst hoF
    split at h
    · cases h
      exact ⟨dm.1, lfs, [packed], slotF, pk.1, pk.2, hlfs, by simp, hpk, rfl, rfl⟩
    · simp at h
  | none =>
    simp only [ht, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨outEs, _, h⟩ := h
    by_cases hl : (outEs.length != p.outs.length) = true
    · simp [hl] at h
    · rw [if_neg hl] at h
      have hl' : outEs.length = p.outs.length := by simpa using hl
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨outF, hout, slotF, _, pk, hpk, h⟩ := h
      split at h
      · cases h
        refine ⟨dm.1, lfs, outF, slotF, pk.1, pk.2, hlfs, ?_, hpk, rfl, rfl⟩
        intro hnil
        subst hnil
        have := (mapM_get _ _ _ hout).1
        simp only [List.length_nil, List.length_zip, hl', Nat.min_self] at this
        exact hne (List.length_eq_zero_iff.mp this.symm)
      · simp at h

end Tools.Prototype.ReaderTyped
