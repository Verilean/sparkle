import Tools.Prototype.ExtReaderDefs

/-! # Unit EXT2 (5/N): the `LetOk 0` range of the raw-surface node rewriter `rawNodeX O`, from `OpsOk O` (copy of LC18)

STATUS: see REPORT-EXT2.md for the build log. LC18's proof of `rawNode_ok` with `rawNode` ↦ `rawNodeX O`; the three extern premises
(`LiftLooseRange`, `LowerLooseRange`, `BetaRange`) are the fields `lift`, `lower`, `beta` of `OpsOk O` (HYPOTHESES for an arbitrary `O`,
PROVED for `modelOps`). `rawNodeX.peel` is the shipped, operation-free `rawNode.peel` (LC18's `peel_ok` is reused); `build` is
`rawBuildX`. The four matcher eliminators are LC18's, restated on `rawNodeX.match_15/7/1/3`. No sorry / axiom / native_decide. -/

namespace Tools.Prototype.ExtReader
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk Tools.ShippingCloInv
open Tools.Prototype.ReaderTyped Tools.Prototype.StartDomOk Tools.Prototype.ReaderClosed
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge
open Tools.Prototype.RawNodeRangeLetOk
open Sparkle.Compiler.MachRawSurface (rawNode projChain listElems)
open Tools.Prototype.ExtModelLetOk

theorem rawBuildX_nil (O : ExtOps) (k : Nat) (regs body : Lean.Expr) (tys : List Lean.Expr) :
    rawBuildX O k regs body tys [] = some body := rfl

theorem rawBuildX_cons (O : ExtOps) (k : Nat) (regs body : Lean.Expr) (tys : List Lean.Expr) (j : Nat) (nm : Name)
    (t : Lean.Expr) (rest : List (Nat × Name × Lean.Expr)) :
    rawBuildX O k regs body tys ((j, nm, t) :: rest) =
      (do
        let v ← projChain (O.lift regs 0 j) (tys.map (fun t => O.lift t 0 j)) j (j + 1 == k)
        let r ← rawBuildX O k regs body tys rest
        some (Lean.Expr.letE nm t v r false)) := rfl

theorem rawBuildX_ok (O : ExtOps) (hl : ∀ e s d, LetOk 0 e = true → LetOk 0 (O.lift e s d) = true)
    {k : Nat} {regs body : Lean.Expr} {tys : List Lean.Expr}
    (hr : LetOk 0 regs = true) (hbody : LetOk 0 body = true) (ht : ∀ t ∈ tys, LetOk 0 t = true) :
    ∀ (l : List (Nat × Name × Lean.Expr)), (∀ x ∈ l, LetOk 0 x.2.2 = true) → ∀ r : Lean.Expr,
      rawBuildX O k regs body tys l = some r → LetOk 0 r = true
  | [], _, r, h => by
    rw [rawBuildX_nil] at h
    have := Option.some.inj h
    subst this
    exact hbody
  | (j, nm, t) :: rest, hlist, r, h => by
    rw [rawBuildX_cons] at h
    obtain ⟨v, hv, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr', h3⟩ := Option.bind_eq_some_iff.mp h2
    have h4 := Option.some.inj h3
    subst h4
    have hv' : LetOk 0 v = true := by
      refine projChain_ok (hl regs 0 j hr) ?_ hv
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hl y 0 j (ht y hy)
    have hrest := rawBuildX_ok O hl hr hbody ht rest (fun x hx => hlist x (List.mem_cons_of_mem _ hx)) r' hr'
    have htt : LetOk 0 t = true := hlist (j, nm, t) List.mem_cons_self
    simp [LetOk, htt, hv', hrest]


/-! ## The outer matcher of `rawNode`

Lean v4.32.1 does not generate the equation lemmas of `rawNodeX.match_15` (name-literal and array-literal patterns), so
`split` cannot be used.  `matchX15_elim` is the eliminator we need, proved on the matcher's own definition (technique of
`Tools.Prototype.NormRangeLetOk.ashrView_args`): a property `Q` of the result holds when it holds for each arm that could
have been selected. -/
set_option maxHeartbeats 16000000 in
theorem matchX15_elim (Q : Option Lean.Expr → Prop) (F : Lean.Expr) (A : Array Lean.Expr)
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
    Q (Tools.Prototype.ExtReader.rawNodeX.match_15 (fun _ _ => Option Lean.Expr) F A h1 h2 h3 h4 h5 h6 h7) := by
  rcases A with ⟨L⟩
  cases F with
  | const n us =>
    unfold Tools.Prototype.ExtReader.rawNodeX.match_15
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
    unfold Tools.Prototype.ExtReader.rawNodeX.match_15
    all_goals first | exact c7 | (dsimp_sparse_aux; exact c7) | (repeat' split; exact c7)

set_option maxHeartbeats 16000000 in
theorem matchX7_elim (Q : Option Lean.Expr → Prop) (F : Lean.Expr) (A : Array Lean.Expr)
    (h1 : (us : List Level) → (head head_1 head_2 as f : Lean.Expr) → Option Lean.Expr)
    (h2 : (x : Lean.Expr) → (x_1 : Array Lean.Expr) → Option Lean.Expr)
    (c1 : ∀ us a b c as f, F = .const `List.forM us → A = #[a, b, c, as, f] → Q (h1 us a b c as f))
    (c2 : Q (h2 F A)) :
    Q (Tools.Prototype.ExtReader.rawNodeX.match_7 (fun _ _ => Option Lean.Expr) F A h1 h2) := by
  rcases A with ⟨L⟩
  cases F with
  | const n us =>
    unfold Tools.Prototype.ExtReader.rawNodeX.match_7
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
    unfold Tools.Prototype.ExtReader.rawNodeX.match_7
    all_goals first | exact c2 | (dsimp_sparse_aux; exact c2) | (repeat' split; exact c2)

set_option maxHeartbeats 16000000 in
theorem matchX1_elim (Q : Option Lean.Expr → Prop) (F : Lean.Expr) (A : Array Lean.Expr) (G : Lean.Expr)
    (h1 : (us : List Level) → (dom S : Lean.Expr) → (us_1 : List Level) → Option Lean.Expr)
    (h2 : (x : Lean.Expr) → (x_1 : Array Lean.Expr) → (x_2 : Lean.Expr) → Option Lean.Expr)
    (c1 : ∀ us dom S us1, F = .const `Sparkle.Core.Circuit us → A = #[dom, S] → G = .const `Monad.toBind us1 →
      Q (h1 us dom S us1))
    (c2 : Q (h2 F A G)) :
    Q (Tools.Prototype.ExtReader.rawNodeX.match_1 (fun _ _ _ => Option Lean.Expr) F A G h1 h2) := by
  rcases A with ⟨L⟩
  unfold Tools.Prototype.ExtReader.rawNodeX.match_1
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
theorem matchX3_elim (Q : Option Lean.Expr → Prop) (F : Lean.Expr) (A : Array Lean.Expr) (G : Lean.Expr)
    (h1 : (us : List Level) → (dom S : Lean.Expr) → (us_1 : List Level) → Option Lean.Expr)
    (h2 : (x : Lean.Expr) → (x_1 : Array Lean.Expr) → (x_2 : Lean.Expr) → Option Lean.Expr)
    (c1 : ∀ us dom S us1, F = .const `Sparkle.Core.Circuit us → A = #[dom, S] → G = .const `Applicative.toPure us1 →
      Q (h1 us dom S us1))
    (c2 : Q (h2 F A G)) :
    Q (Tools.Prototype.ExtReader.rawNodeX.match_3 (fun _ _ _ => Option Lean.Expr) F A G h1 h2) := by
  rcases A with ⟨L⟩
  unfold Tools.Prototype.ExtReader.rawNodeX.match_3
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


theorem rawNodeX_ok (O : ExtOps) (hO : OpsOk O) (pm : Name → Option Nat) :
    ∀ e e', LetOk 0 e = true → rawNodeX O pm e = some e' → LetOk 0 e' = true := by
  have hl := hO.lift
  have hlo := hO.lower
  have hb := hO.beta
  intro e e' he h
  have hF := ok_getAppFn he
  have hA := ok_getAppArgs he
  have hA2 : ∀ x ∈ e.getAppArgs, ∀ y ∈ x.getAppArgs, LetOk 0 y = true :=
    fun x hx => ok_getAppArgs (hA x hx)
  clear he
  revert h
  first
    | unfold rawNodeX
    | delta rawNodeX
    | simp only [rawNodeX]
  generalize e.getAppFn = F at hF ⊢
  generalize e.getAppArgs = A at hA hA2 ⊢
  refine matchX15_elim (fun o => o = some e' → LetOk 0 e' = true) F A _ _ _ _ _ _ _ ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7
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
    refine matchX1_elim (fun o => o = some e' → LetOk 0 e' = true) _ _ _ _ _ ?d1 ?d2
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
    refine matchX3_elim (fun o => o = some e' → LetOk 0 e' = true) _ _ _ _ _ ?d1 ?d2
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
    refine matchX7_elim (fun o => o = some e' → LetOk 0 e' = true) _ _ _ _ ?d1 ?d2
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
          refine rawBuildX_ok O hl (ok_getElem! hA 1) hpeel.1 ?_ _ ?_ _ h
          · exact tys_ok _ hpeel.2 (fun nm t i ht => hlo t i i ht)
          · exact list_ok _ hpeel.2 (fun _ _ _ => rfl)
    · cases h

/-- `RawNodeRange` for the node rewriter of the reader with the operations `O`. -/
def RawNodeRangeX (O : ExtOps) (senv : StructEnv) : Prop :=
  ∀ e e', LetOk 0 e = true → rawNodeX O senv.prodMatch e = some e' → LetOk 0 e' = true

theorem rawNodeRangeX_of {O : ExtOps} (hO : OpsOk O) {senv : StructEnv} : RawNodeRangeX O senv :=
  fun e e' he h => rawNodeX_ok O hO senv.prodMatch e e' he h

#print axioms rawNodeX_ok

end Tools.Prototype.ExtReader
