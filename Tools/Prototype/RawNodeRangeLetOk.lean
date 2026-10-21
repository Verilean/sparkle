import Tools.Prototype.ReaderComposed
import Tools.Prototype.BoolMapModelLetOk
import Tools.ShippingSparseCasesTac

/-! # Unit LC18: `RawNodeRange` from the three extern calls inside `rawNode`

BUILT (unit LC18): a1-a5 exit 1 (my proof errors: `tauto`/`beta_reduce` are Mathlib, missing opens, matcher leaves), a6 exit 0.  No sorry / axiom / native_decide.

`Sparkle.Compiler.MachRawSurface.rawNode` is a TOTAL `def` (structural local `peel`/`build`; `projChain` and `listElems`
are total).  So `RawNodeRange senv` is proved here by reading its branches, with the following exact residue.
The only things `rawNode` calls that are `@[extern]` / `partial` (so not unfoldable by the kernel) are:

* `Expr.liftLooseBVars` with arbitrary offsets (`regs.liftLooseBVars 0 j`, `f.liftLooseBVars 0 i`, ...);
* `Expr.lowerLooseBVars` (the component types `t.lowerLooseBVars i i` in the pair arm);
* `Expr.beta` (`partial def betaRev`), always with ONE argument here.

Each is a REPLACEMENT PREMISE of `RawNodeRange` (NOT proved in this change), one per call:
* `LiftLooseRange`  : `LetOk 0 e → LetOk 0 (e.liftLooseBVars s d)`   (general; the existing `LiftRange` is the `d = 1`, `s ∈ {0,1}` case);
* `LowerLooseRange` : `LetOk 0 e → LetOk 0 (e.lowerLooseBVars s d)`;
* `BetaRange`       : `LetOk 0 f → LetOk 0 a → LetOk 0 (f.beta #[a])`.

PROVED (conditional on those): `rawNode_ok`, `rawNodeRange_of`, corollary `machineShapeN_typed_all_rawNode`
(`machineShapeN_typed_all` with `RawNodeRange` replaced by the three premises; the old theorems are unchanged), pinned by
`auditPropBinders`.  Everything else in `rawNode` (the `Circuit.read`/`bind`/`pure` arms, the `forM` arms with their
`foldr`, the `peel` / `build` loop with `projChain`, `tailTy`, `listElems`) is proved by structure.
No executed agreement example is claimed.

Matchers: Lean v4.32.1 cannot generate the equation lemmas of `rawNode.match_15`, `match_7`, `match_1`, `match_3` (name-literal and
array-literal patterns), so `split` is not usable on them.  `match15_elim`, `match7_elim`, `match1_elim`, `match3_elim` are
eliminators proved on the matchers' own definitions (case split of the name components and the `dite`s, as in `ashrView_args`).

Review note (REVIEW-LC18): the existing `LiftRange` is `∀ e, LetOk 0 e → LetOk 0 (e.liftLooseBVars 0 1) ∧ LetOk 0 (e.liftLooseBVars 1 1)`
(offset 1 only), and `Inst1Range` is `instantiate1`; neither states `liftLooseBVars 0 n` for arbitrary `n` nor `lowerLooseBVars` nor
`Expr.beta`, so they are NOT reused here; each call gets its own premise. -/
namespace Tools.Prototype.RawNodeRangeLetOk
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk Tools.ShippingCloInv
open Tools.Prototype.ReaderTyped Tools.Prototype.StartDomOk Tools.Prototype.ReaderClosed
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge
open Sparkle.Compiler.MachRawSurface (rawNode projChain listElems)

/-- PREMISE (not proved): `Expr.liftLooseBVars` (extern), arbitrary offsets, invents no `_machLet j` placeholder. -/
def LiftLooseRange : Prop :=
  ∀ (e : Lean.Expr) (s d : Nat), LetOk 0 e = true → LetOk 0 (e.liftLooseBVars s d) = true

/-- PREMISE (not proved): `Expr.lowerLooseBVars` (extern) invents no `_machLet j` placeholder. -/
def LowerLooseRange : Prop :=
  ∀ (e : Lean.Expr) (s d : Nat), LetOk 0 e = true → LetOk 0 (e.lowerLooseBVars s d) = true

/-- PREMISE (not proved): `Expr.beta` with one argument (`partial def betaRev`) invents no `_machLet j` placeholder. -/
def BetaRange : Prop :=
  ∀ (f a : Lean.Expr), LetOk 0 f = true → LetOk 0 a = true → LetOk 0 (f.beta #[a]) = true

theorem ok_mkAppN_list {n : Nat} {f : Lean.Expr} {l : List Lean.Expr} (hf : LetOk n f = true)
    (hl : ∀ a ∈ l, LetOk n a = true) : LetOk n (mkAppN f l.toArray) = true :=
  ok_mkAppN hf (fun a ha => hl a (List.mem_toArray.mp ha))

theorem ok_foldr {n : Nat} {g : Lean.Expr × Nat → Lean.Expr → Lean.Expr} :
    ∀ (l : List (Lean.Expr × Nat)) (init : Lean.Expr), LetOk n init = true →
      (∀ p ∈ l, ∀ r, LetOk n r = true → LetOk n (g p r) = true) → LetOk n (l.foldr g init) = true
  | [], init, hi, _ => by simpa using hi
  | p :: l, init, hi, hg => by
    simp only [List.foldr_cons]
    exact hg p List.mem_cons_self _
      (ok_foldr l init hi (fun q hq => hg q (List.mem_cons_of_mem _ hq)))

theorem of_mem_zipIdx {α : Type} : ∀ (l : List α) (k : Nat) (x : α) (i : Nat), (x, i) ∈ l.zipIdx k → x ∈ l
  | [], k, x, i, h => by simp at h
  | a :: l, k, x, i, h => by
    rw [List.zipIdx_cons, List.mem_cons] at h
    rcases h with h | h
    · have := (Prod.mk.inj h).1
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (of_mem_zipIdx l (k + 1) x i h)

/-! ## `listElems` -/

theorem listElems_ok {n : Nat} : ∀ (e : Lean.Expr) (xs : List Lean.Expr), listElems e = some xs →
    LetOk n e = true → ∀ a ∈ xs, LetOk n a = true := by
  intro e
  induction e with
  | app f r ihf ihr =>
    intro xs h he
    unfold listElems at h
    split at h
    · rename_i us t a rest heq
      obtain ⟨rfl, rfl⟩ := Expr.app.inj heq
      cases hl : listElems r with
      | none => simp [hl] at h
      | some ys =>
        simp [hl] at h
        subst h
        simp only [LetOk, Bool.and_eq_true] at he
        have h1 : LetOk n a = true := he.1.2
        have h2 : LetOk n r = true := he.2
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h1
        · exact ihr ys hl h2 y hy
    · simp at h
      subst h
      simp
    · cases h
  | _ => intro xs h he; simp [listElems] at h

/-! ## `projChain` -/

theorem tailTy_ok : ∀ (l : List Lean.Expr) (b : Lean.Expr), (∀ t ∈ l, LetOk 0 t = true) →
    Sparkle.Compiler.MachProjChain.tailTy l = some b → LetOk 0 b = true
  | [], b, _, h => by simp [Sparkle.Compiler.MachProjChain.tailTy] at h
  | [a], b, hl, h => by
    have h' : some a = some b := h
    have := Option.some.inj h'
    subst this
    exact hl a List.mem_cons_self
  | a :: c :: rest, b, hl, h => by
    have h' : (Sparkle.Compiler.MachProjChain.tailTy (c :: rest)).map
        (Sparkle.Compiler.MachProjChain.prodE a) = some b := h
    cases hc : Sparkle.Compiler.MachProjChain.tailTy (c :: rest) with
    | none => rw [hc] at h'; cases h'
    | some d =>
      rw [hc] at h'
      have := Option.some.inj h'
      subst this
      have hd := tailTy_ok (c :: rest) d (fun t ht => hl t (List.mem_cons_of_mem _ ht)) hc
      have ha := hl a List.mem_cons_self
      simp [Sparkle.Compiler.MachProjChain.prodE, mkApp2, mkApp, LetOk, hd, ha]

theorem tailAt_ok {tys : List Lean.Expr} (ht : ∀ t ∈ tys, LetOk 0 t = true) {i : Nat} {b : Lean.Expr}
    (h : Sparkle.Compiler.MachProjChain.tailAt tys i = some b) : LetOk 0 b = true :=
  tailTy_ok _ b (fun t hm => ht t (List.mem_of_mem_drop hm)) h

theorem forIn_inv {α : Type} (P : Lean.Expr → Prop) (f : α → Lean.Expr → Option (ForInStep Lean.Expr))
    (hf : ∀ a b, P b → ∀ s, f a b = some s → P s.value) :
    ∀ (l : List α) (init r : Lean.Expr), P init → forIn l init f = some r → P r
  | [], init, r, hi, h => by
    rw [List.forIn_nil] at h
    have := Option.some.inj h
    subst this
    exact hi
  | a :: l, init, r, hi, h => by
    rw [List.forIn_cons] at h
    cases hfa : f a init with
    | none => simp [hfa] at h
    | some s =>
      cases s with
      | done b =>
        simp [hfa] at h
        subst h
        exact hf a init hi _ hfa
      | yield b =>
        simp [hfa] at h
        exact forIn_inv P f hf l b r (hf a init hi _ hfa) h

theorem projChain_ok {regs : Lean.Expr} {tys : List Lean.Expr} {j : Nat} {last : Bool} {v : Lean.Expr}
    (hr : LetOk 0 regs = true) (ht : ∀ t ∈ tys, LetOk 0 t = true)
    (h : projChain regs tys j last = some v) : LetOk 0 v = true := by
  unfold projChain at h
  obtain ⟨cur, hforin, hg⟩ := Option.bind_eq_some_iff.mp h
  have hcur : LetOk 0 cur = true := by
    have hf2 := hforin
    first
      | rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hf2
      | simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', forIn'_eq_forIn] at hf2
    refine forIn_inv (fun e => LetOk 0 e = true) _ ?_ _ regs cur hr hf2
    intro i b hb s hs
    dsimp only at hs
    cases ha : tys[i]? with
    | none => simp [ha] at hs
    | some a =>
      cases hb2 : Sparkle.Compiler.MachProjChain.tailAt tys i with
      | none => simp [ha, hb2] at hs
      | some c =>
        simp [ha, hb2] at hs
        subst hs
        have h1 : LetOk 0 a = true := ht a (List.mem_of_getElem? ha)
        have h2 := tailAt_ok ht hb2
        simp [ForInStep.value, LetOk, mkApp3, mkApp2, mkApp, h1, h2, hb]
  by_cases hlast : last = true
  · simp [hlast] at hg
    subst hg
    exact hcur
  · cases ha : tys[j]? with
    | none => simp [hlast, ha] at hg
    | some a =>
      cases hb2 : Sparkle.Compiler.MachProjChain.tailAt tys j with
      | none => simp [hlast, ha, hb2] at hg
      | some c =>
        simp [hlast, ha, hb2] at hg
        subst hg
        have h1 : LetOk 0 a = true := ht a (List.mem_of_getElem? ha)
        have h2 := tailAt_ok ht hb2
        simp [LetOk, mkApp3, mkApp2, mkApp, h1, h2, hcur]

/-! ## `peel` and `build` -/

theorem peel_ok : ∀ (i : Nat) (b : Lean.Expr) (acc bs : List (Name × Lean.Expr)) (body : Lean.Expr),
    rawNode.peel i b acc = some (bs, body) → LetOk 0 b = true → (∀ x ∈ acc, LetOk 0 x.2 = true) →
    LetOk 0 body = true ∧ ∀ x ∈ bs, LetOk 0 x.2 = true
  | 0, b, acc, bs, body, h, hb, ha => by
    have h' : some (acc.reverse, b) = some (bs, body) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h')
    subst h1
    subst h2
    exact ⟨hb, fun x hx => ha x (List.mem_reverse.mp hx)⟩
  | i + 1, b, acc, bs, body, h, hb, ha => by
    cases b with
    | lam nm t b' bi =>
      have h' : rawNode.peel i b' ((nm, t) :: acc) = some (bs, body) := h
      simp only [LetOk, Bool.and_eq_true] at hb
      refine peel_ok i b' ((nm, t) :: acc) bs body h' hb.2 ?_
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb.1
      · exact ha x hx
    | _ =>
      exfalso
      have h' : (none : Option (List (Name × Lean.Expr) × Lean.Expr)) = some (bs, body) := h
      cases h'

theorem build_nil (k : Nat) (regs body : Lean.Expr) (tys : List Lean.Expr) :
    rawNode.build k regs body tys [] = some body := rfl

theorem build_cons (k : Nat) (regs body : Lean.Expr) (tys : List Lean.Expr) (j : Nat) (nm : Name) (t : Lean.Expr)
    (rest : List (Nat × Name × Lean.Expr)) :
    rawNode.build k regs body tys ((j, nm, t) :: rest) =
      (do
        let v ← projChain (regs.liftLooseBVars 0 j) (tys.map (·.liftLooseBVars 0 j)) j (j + 1 == k)
        let r ← rawNode.build k regs body tys rest
        some (Lean.Expr.letE nm t v r false)) := rfl

theorem build_ok (hl : LiftLooseRange) {k : Nat} {regs body : Lean.Expr} {tys : List Lean.Expr}
    (hr : LetOk 0 regs = true) (hbody : LetOk 0 body = true) (ht : ∀ t ∈ tys, LetOk 0 t = true) :
    ∀ (l : List (Nat × Name × Lean.Expr)), (∀ x ∈ l, LetOk 0 x.2.2 = true) → ∀ r : Lean.Expr,
      rawNode.build k regs body tys l = some r → LetOk 0 r = true
  | [], _, r, h => by
    rw [build_nil] at h
    have := Option.some.inj h
    subst this
    exact hbody
  | (j, nm, t) :: rest, hlist, r, h => by
    rw [build_cons] at h
    obtain ⟨v, hv, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr', h3⟩ := Option.bind_eq_some_iff.mp h2
    have h4 := Option.some.inj h3
    subst h4
    have hv' : LetOk 0 v = true := by
      refine projChain_ok (hl regs 0 j hr) ?_ hv
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hl y 0 j (ht y hy)
    have hrest := build_ok hl hr hbody ht rest (fun x hx => hlist x (List.mem_cons_of_mem _ hx)) r' hr'
    have htt : LetOk 0 t = true := hlist (j, nm, t) List.mem_cons_self
    simp [LetOk, htt, hv', hrest]

theorem tys_ok {binders : List (Name × Lean.Expr)} (F : (Name × Lean.Expr) × Nat → Lean.Expr)
    (hb : ∀ x ∈ binders, LetOk 0 x.2 = true)
    (hF : ∀ nm t i, LetOk 0 t = true → LetOk 0 (F ((nm, t), i)) = true) :
    ∀ t ∈ binders.zipIdx.map F, LetOk 0 t = true := by
  intro t ht
  obtain ⟨⟨⟨nm, ty⟩, i⟩, hq, rfl⟩ := List.mem_map.mp ht
  exact hF nm ty i (hb (nm, ty) (of_mem_zipIdx binders 0 (nm, ty) i hq))

theorem list_ok {binders : List (Name × Lean.Expr)} {ks : List Nat}
    (G : Nat × (Name × Lean.Expr) → Nat × Name × Lean.Expr)
    (hb : ∀ x ∈ binders, LetOk 0 x.2 = true)
    (hG : ∀ j nm t, (G (j, (nm, t))).2.2 = t) :
    ∀ x ∈ (ks.zip binders).map G, LetOk 0 x.2.2 = true := by
  intro x hx
  obtain ⟨⟨j, ⟨nm, t⟩⟩, hq, rfl⟩ := List.mem_map.mp hx
  rw [hG]
  exact hb (nm, t) (List.of_mem_zip hq).2

/-! ## The outer matcher of `rawNode`

Lean v4.32.1 does not generate the equation lemmas of `rawNode.match_15` (name-literal and array-literal patterns), so
`split` cannot be used.  `match15_elim` is the eliminator we need, proved on the matcher's own definition (technique of
`Tools.Prototype.NormRangeLetOk.ashrView_args`): a property `Q` of the result holds when it holds for each arm that could
have been selected. -/
set_option maxHeartbeats 16000000 in
theorem match15_elim (Q : Option Lean.Expr → Prop) (F : Lean.Expr) (A : Array Lean.Expr)
    (h1 : (us : List Level) → (dom S τ W r : Lean.Expr) → Option Lean.Expr)
    (h2 : (us : List Level) → (m inst α β x k : Lean.Expr) → Option Lean.Expr)
    (h3 : (us : List Level) → (m inst α a : Lean.Expr) → Option Lean.Expr)
    (h4 : (us : List Level) → (dom S head β x k : Lean.Expr) → Option Lean.Expr)
    (h5 : (us : List Level) → (m inst head as f : Lean.Expr) → Option Lean.Expr)
    (h6 : (n : Name) → (us : List Level) → (args : Array Lean.Expr) → Option Lean.Expr)
    (h7 : (x : Lean.Expr) → (x_1 : Array Lean.Expr) → Option Lean.Expr)
    (c1 : ∀ us dom S τ W r, F = .const `Sparkle.Core.Circuit.read us → A = #[dom, S, τ, W, r] →
      Q (h1 us dom S τ W r))
    (c2 : ∀ us m inst α β x k, F = .const `Bind.bind us → A = #[m, inst, α, β, x, k] → Q (h2 us m inst α β x k))
    (c3 : ∀ us m inst α a, F = .const `Pure.pure us → A = #[m, inst, α, a] → Q (h3 us m inst α a))
    (c4 : ∀ us dom S head β x k, F = .const `Sparkle.Core.Circuit.bind us → A = #[dom, S, head, β, x, k] →
      Q (h4 us dom S head β x k))
    (c5 : ∀ us m inst head as f, F = .const `List.forM us → A = #[m, inst, head, as, f] →
      Q (h5 us m inst head as f))
    (c6 : ∀ n us, F = .const n us → Q (h6 n us A))
    (c7 : Q (h7 F A)) :
    Q (Sparkle.Compiler.MachRawSurface.rawNode.match_15 (fun _ _ => Option Lean.Expr) F A h1 h2 h3 h4 h5 h6 h7) := by
  rcases A with ⟨L⟩
  cases F with
  | const n us =>
    unfold Sparkle.Compiler.MachRawSurface.rawNode.match_15
    rcases n with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals first
      | exact c6 _ _ rfl
      | (subst_vars; exact c6 _ _ rfl)
      | (rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, L'⟩⟩⟩⟩⟩⟩⟩ <;>
          first
            | exact c6 _ _ rfl
            | (subst_vars; exact c6 _ _ rfl)
            | (subst_vars; exact c1 _ _ _ _ _ _ rfl rfl)
            | (subst_vars; exact c2 _ _ _ _ _ _ _ rfl rfl)
            | (subst_vars; exact c3 _ _ _ _ _ rfl rfl)
            | (subst_vars; exact c4 _ _ _ _ _ _ _ rfl rfl)
            | (subst_vars; exact c5 _ _ _ _ _ _ rfl rfl)
            | (exfalso; simp at *; done)
            | (exfalso; simp_all; done)
            | (trace_state; fail "LEAF"))
  | _ =>
    unfold Sparkle.Compiler.MachRawSurface.rawNode.match_15
    all_goals first | exact c7 | (dsimp_sparse_aux; exact c7) | (repeat' split; exact c7)

set_option maxHeartbeats 16000000 in
theorem match7_elim (Q : Option Lean.Expr → Prop) (F : Lean.Expr) (A : Array Lean.Expr)
    (h1 : (us : List Level) → (head head_1 head_2 as f : Lean.Expr) → Option Lean.Expr)
    (h2 : (x : Lean.Expr) → (x_1 : Array Lean.Expr) → Option Lean.Expr)
    (c1 : ∀ us a b c as f, F = .const `List.forM us → A = #[a, b, c, as, f] → Q (h1 us a b c as f))
    (c2 : Q (h2 F A)) :
    Q (Sparkle.Compiler.MachRawSurface.rawNode.match_7 (fun _ _ => Option Lean.Expr) F A h1 h2) := by
  rcases A with ⟨L⟩
  cases F with
  | const n us =>
    unfold Sparkle.Compiler.MachRawSurface.rawNode.match_7
    rcases n with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals first
      | exact c2
      | (subst_vars; exact c2)
      | (rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, L'⟩⟩⟩⟩⟩⟩⟩ <;>
          first
            | exact c2
            | (subst_vars; exact c2)
            | (subst_vars; exact c1 _ _ _ _ _ _ rfl rfl)
            | (exfalso; simp at *; done)
            | (exfalso; simp_all; done)
            | (trace_state; fail "LEAF7"))
  | _ =>
    unfold Sparkle.Compiler.MachRawSurface.rawNode.match_7
    all_goals first | exact c2 | (dsimp_sparse_aux; exact c2) | (repeat' split; exact c2)

set_option maxHeartbeats 16000000 in
theorem match1_elim (Q : Option Lean.Expr → Prop) (F : Lean.Expr) (A : Array Lean.Expr) (G : Lean.Expr)
    (h1 : (us : List Level) → (dom S : Lean.Expr) → (us_1 : List Level) → Option Lean.Expr)
    (h2 : (x : Lean.Expr) → (x_1 : Array Lean.Expr) → (x_2 : Lean.Expr) → Option Lean.Expr)
    (c1 : ∀ us dom S us1, F = .const `Sparkle.Core.Circuit us → A = #[dom, S] → G = .const `Monad.toBind us1 →
      Q (h1 us dom S us1))
    (c2 : Q (h2 F A G)) :
    Q (Sparkle.Compiler.MachRawSurface.rawNode.match_1 (fun _ _ _ => Option Lean.Expr) F A G h1 h2) := by
  rcases A with ⟨L⟩
  unfold Sparkle.Compiler.MachRawSurface.rawNode.match_1
  cases F with
  | const n us =>
    rcases n with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (rcases G with _ | _ | _ | _ |
      ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p3, s3⟩ | ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩, us2⟩ |
      _ | _ | _ | _ | _ | _ | _)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals first
      | exact c2
      | (subst_vars; exact c2)
      | (rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, L'⟩⟩⟩ <;>
          first
            | exact c2
            | (subst_vars; exact c2)
            | (subst_vars; exact c1 _ _ _ _ rfl rfl rfl)
            | (exfalso; simp at *; done)
            | (exfalso; simp_all; done)
            | (trace_state; fail "LEAF1"))
  | _ =>
    all_goals first | exact c2 | (dsimp_sparse_aux; exact c2) | (repeat' split; exact c2)

set_option maxHeartbeats 16000000 in
theorem match3_elim (Q : Option Lean.Expr → Prop) (F : Lean.Expr) (A : Array Lean.Expr) (G : Lean.Expr)
    (h1 : (us : List Level) → (dom S : Lean.Expr) → (us_1 : List Level) → Option Lean.Expr)
    (h2 : (x : Lean.Expr) → (x_1 : Array Lean.Expr) → (x_2 : Lean.Expr) → Option Lean.Expr)
    (c1 : ∀ us dom S us1, F = .const `Sparkle.Core.Circuit us → A = #[dom, S] → G = .const `Applicative.toPure us1 →
      Q (h1 us dom S us1))
    (c2 : Q (h2 F A G)) :
    Q (Sparkle.Compiler.MachRawSurface.rawNode.match_3 (fun _ _ _ => Option Lean.Expr) F A G h1 h2) := by
  rcases A with ⟨L⟩
  unfold Sparkle.Compiler.MachRawSurface.rawNode.match_3
  cases F with
  | const n us =>
    rcases n with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (rcases G with _ | _ | _ | _ |
      ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p3, s3⟩ | ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩, us2⟩ |
      _ | _ | _ | _ | _ | _ | _)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals first
      | exact c2
      | (subst_vars; exact c2)
      | (rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, L'⟩⟩⟩ <;>
          first
            | exact c2
            | (subst_vars; exact c2)
            | (subst_vars; exact c1 _ _ _ _ rfl rfl rfl)
            | (exfalso; simp at *; done)
            | (exfalso; simp_all; done)
            | (trace_state; fail "LEAF3"))
  | _ =>
    all_goals first | exact c2 | (dsimp_sparse_aux; exact c2) | (repeat' split; exact c2)

/-! ## The whole of `rawNode` -/

theorem rawNode_ok (hl : LiftLooseRange) (hlo : LowerLooseRange) (hb : BetaRange) (pm : Name → Option Nat) :
    ∀ e e', LetOk 0 e = true → rawNode pm e = some e' → LetOk 0 e' = true := by
  intro e e' he h
  have hF := ok_getAppFn he
  have hA := ok_getAppArgs he
  have hA2 : ∀ x ∈ e.getAppArgs, ∀ y ∈ x.getAppArgs, LetOk 0 y = true :=
    fun x hx => ok_getAppArgs (hA x hx)
  clear he
  revert h
  first
    | unfold rawNode
    | delta rawNode
    | simp only [rawNode]
  generalize e.getAppFn = F at hF ⊢
  generalize e.getAppArgs = A at hA hA2 ⊢
  refine match15_elim (fun o => o = some e' → LetOk 0 e' = true) F A _ _ _ _ _ _ _ ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7
  case c7 => intro h; cases h
  case c1 =>
    intro us dom S τ W r hFe hAe h
    subst hAe
    cases h
    simp_all [LetOk, mkApp3, mkApp2, mkApp4, mkApp]
  case c2 =>
    intro us m inst α β x k hFe hAe h
    subst hAe
    try dsimp only at h
    revert h
    refine match1_elim (fun o => o = some e' → LetOk 0 e' = true) _ _ _ _ _ ?d1 ?d2
    case d2 => intro h; cases h
    case d1 =>
      intro us' dom S us1 hF' hA' hG' h
      try dsimp only at h
      cases h
      apply ok_mkAppN_list (by simp [LetOk])
      simp_all
  case c3 =>
    intro us m inst α a hFe hAe h
    subst hAe
    try dsimp only at h
    revert h
    refine match3_elim (fun o => o = some e' → LetOk 0 e' = true) _ _ _ _ _ ?d1 ?d2
    case d2 => intro h; cases h
    case d1 =>
      intro us' dom S us1 hF' hA' hG' h
      try dsimp only at h
      cases h
      apply ok_mkAppN_list (by simp [LetOk])
      simp_all
  case c4 =>
    intro us dom S head β x k hFe hAe h
    subst hAe
    try dsimp only at h
    revert h
    refine match7_elim (fun o => o = some e' → LetOk 0 e' = true) _ _ _ _ ?d1 ?d2
    case d2 => intro h; cases h
    case d1 =>
      intro us' a b c as f hFe' hAe' h
      try dsimp only at h
      split at h
      · cases h
      · rename_i xs hxs
        try dsimp only at h
        cases h
        try dsimp only
        have has : ∀ a ∈ xs, LetOk 0 a = true := by
          refine listElems_ok (n := 0) _ _ ‹listElems _ = some _› ?_
          simp_all
        refine ok_foldr _ _ ?_ ?_
        · exact hb _ _ (hl _ _ _ (by simp_all)) (by simp [LetOk])
        · intro p hp r hr
          obtain ⟨⟨a, i0⟩, hq, rfl⟩ := List.mem_map.mp hp
          dsimp only
          apply ok_mkAppN_list (by simp [LetOk])
          intro y hy
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hl _ _ _ (by simp_all)
          · exact hl _ _ _ (by simp_all)
          · simp [LetOk]
          · exact hl _ _ _ (by simp_all)
          · exact hb _ _ (hl _ _ _ (by simp_all)) (hl _ _ _ (has a (of_mem_zipIdx xs 0 a i0 hq)))
          · simp [LetOk, hr]
  case c5 =>
    intro us m inst head as f hFe hAe h
    subst hAe
    try dsimp only at h
    split at h
    · cases h
    · rename_i xs hxs
      try dsimp only at h
      cases h
      try dsimp only
      have has : ∀ a ∈ xs, LetOk 0 a = true := by
        refine listElems_ok (n := 0) _ _ ‹listElems _ = some _› ?_
        simp_all
      refine ok_foldr _ _ ?_ ?_
      · refine hl _ _ _ ?_
        apply ok_mkAppN_list (by simp [LetOk])
        simp_all [LetOk, mkApp2, mkApp]
      · intro p hp r hr
        obtain ⟨⟨a, i0⟩, hq, rfl⟩ := List.mem_map.mp hp
        dsimp only
        apply ok_mkAppN_list (by simp [LetOk])
        intro y hy
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hl _ _ _ (by simp_all)
        · simp only [LetOk, mkApp2, mkApp, Bool.and_eq_true]
          exact ⟨⟨by simp [LetOk], hl _ _ _ (by simp_all)⟩, hl _ _ _ (by simp_all)⟩
        · simp [LetOk]
        · simp [LetOk]
        · exact hb _ _ (hl _ _ _ (by simp_all)) (hl _ _ _ (has a (of_mem_zipIdx xs 0 a i0 hq)))
        · simp [LetOk, hr]
  case c6 =>
    intro n us hFe h
    try dsimp only at h
    split at h
    · split at h
      · cases h
      · try dsimp only at h
        split at h
        · cases h
        · try dsimp only at h
          have hpeel := peel_ok _ _ _ _ _ ‹rawNode.peel _ _ _ = some _› (ok_getElem! hA 2) (by simp)
          refine build_ok hl (ok_getElem! hA 1) hpeel.1 ?_ _ ?_ _ h
          · exact tys_ok _ hpeel.2 (fun nm t i ht => hlo t i i ht)
          · exact list_ok _ hpeel.2 (fun _ _ _ => rfl)
    · cases h

theorem rawNodeRange_of {senv : StructEnv} (hl : LiftLooseRange) (hlo : LowerLooseRange) (hb : BetaRange) :
    RawNodeRange senv :=
  fun e e' he h => rawNode_ok hl hlo hb senv.prodMatch e e' he h

#print axioms rawNode_ok
#print axioms rawNodeRange_of

/-- `machineShapeN_typed_all` with `RawNodeRange` replaced by the three extern-call premises. -/
theorem machineShapeN_typed_all_rawNode {senv : StructEnv}
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hsig : SigTyRange senv)
    (hz : ZeroLitAgrees) (hll : LiftLooseRange) (hlo : LowerLooseRange) (hbeta : BetaRange)
    (hnode : NormNodeRange senv) (hE : EqvLetOk0)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      (∀ (d : MachineData), d.shape = sp → d.ok = true →
        d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) :=
  Tools.Prototype.ReaderComposed.machineShapeN_typed_all hroot hlift hinst1 hsig hz
    (rawNodeRange_of hll hlo hbeta) hnode hE hpe h

#print axioms machineShapeN_typed_all_rawNode

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_typed_all_rawNode
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "LiftLooseRange", "LowerLooseRange",
    "BetaRange", "NormNodeRange", "EqvLetOk0", "Eq", "Eq"])

end Tools.Prototype.RawNodeRangeLetOk
