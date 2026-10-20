import Tools.ShippingReaderLenOk

/-! # The length invariant — (ii) `machReserve`, and the list lengths of the two `++` sites

`machReserve` (`Sparkle/Compiler/Elab.lean` 3696–3710) is a plain `def`:
an `Option` program. What it appends to a state `st`:

| array | appended | length |
|---|---|---|
| `kinds` | `kinds`, read by `machSlotKinds` (3439) | `kinds.length` |
| `inits` | `inits`, read by `machInits natOf kinds` (3468) | `kinds.length` — `machInits_length` |
| `names` | `machSlotNames st.runs.size body kinds base` (3685) | `kinds.length` — `machSlotNames_length` |

so the returned state is `reserved st dom' body kinds inits`
(`machReserve_some`) and it satisfies the invariant when `st` does
(`machReserve_lenOk`).

How the `do` block is handled: NOT by walking its elaborated form. A
second function `machReserveSpec` is written here with `Option.bind` and
`if` only, `machReserve_eq_spec` proves the two EQUAL by deciding every
discriminant and closing each leaf by reduction, and the inversion is then
done on the text of this file.

Also here: the length fact of `machLoopRoot`'s two `mapM`s (4199–4200),
which is the premise of `lenOk_loopRoot`.

A separate file, so that a failure here does not take
`Tools/ShippingReaderLenOk.lean` (the invariant, the initial state, the
update lemmas) with it. UNVERIFIED: written, not built. -/
namespace Tools.ShippingReaderLenOk
open Lean
open Sparkle.Compiler.Elab

/-! ## List lengths -/

/-- `mapM` in `Option` keeps the length. -/
theorem mapM_option_length {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro r h
    rw [List.mapM_nil] at h
    cases h
    rfl
  | cons a l ih =>
    intro r h
    rw [List.mapM_cons] at h
    try simp only [Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨b, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    have hl := ih bs hbs
    first
      | exact congrArg (· + 1) hl
      | simp [hl]

/-- **4199–4200**: the kinds and reset values `machLoopRoot` reads off the
registers of a loop have one length (for any two readers `f`, `g`). -/
theorem loopRoot_inits_length {ρ : Type} {f : ρ → Option MixedGateBinder}
    {g : MixedGateBinder × ρ → Option Nat} {regs : List ρ}
    {kinds : List MixedGateBinder} {inits : List Nat}
    (hk : regs.mapM f = some kinds) (hi : (kinds.zip regs).mapM g = some inits) :
    inits.length = kinds.length := by
  have h1 := mapM_option_length f regs kinds hk
  have h2 := mapM_option_length g (kinds.zip regs) inits hi
  rw [List.length_zip] at h2
  omega

/-- The reset values `machInits` reads are as many as the kinds. -/
theorem machInits_length (natOf : Lean.Expr → Option Nat) :
    ∀ (kinds : List MixedGateBinder) (e : Lean.Expr) (inits : List Nat),
      machInits natOf kinds e = some inits → inits.length = kinds.length := by
  intro kinds
  induction kinds with
  | nil =>
    intro e inits h
    unfold machInits at h
    split at h
    -- the `[]` alternative; the other two carry an absurd equation
    -- (`[] = _ :: _` from the split, or `none = some _`)
    all_goals first
      | contradiction
      | (cases h; rfl)
      | (simp_all; done)
  | cons k ks ih =>
    intro e inits h
    unfold machInits at h
    split at h
    -- `[]` alternative: the split's equation `k :: ks = []`; wildcard: `none = some _`;
    -- the `_ :: _` alternative: name the split's equation by its type, make its
    -- tail the induction's `ks`, then split the inner match
    all_goals first
      | contradiction
      | (have hc : k :: ks = _ :: _ := ‹_›
         injection hc with hk hks
         subst hks
         split at h
         all_goals first
           | contradiction
           | (cases h
              have hl := ih _ _ (by assumption)
              first
                | simp [hl]
                | exact congrArg (· + 1) hl))

theorem length_ite_map {α : Type} (c : Prop) [Decidable c] (l : List α) (f : α → α) :
    (if c then l else l.map f).length = l.length := by
  by_cases h : c
  · rw [if_pos h]
  · rw [if_neg h, List.length_map]

theorem length_take_or_range {α : Type} (n : Nat) (l : List α) (f : Nat → α) :
    (if n ≤ l.length then l.take n else (List.range n).map f).length = n := by
  by_cases h : n ≤ l.length
  · rw [if_pos h, List.length_take]
    exact Nat.min_eq_left h
  · rw [if_neg h, List.length_map, List.length_range]

/-- The handle names `machSlotNames` gives are as many as the kinds. -/
theorem machSlotNames_length (ordinal : Nat) (body : Lean.Expr) (kinds : List MixedGateBinder)
    (base : Nat) : (machSlotNames ordinal body kinds base).length = kinds.length := by
  unfold machSlotNames
  first
    | exact (length_ite_map (ordinal = 0) _ _).trans
        (length_take_or_range kinds.length (machLetNames body) _)
    | (by_cases h0 : ordinal = 0 <;>
        by_cases hc : kinds.length ≤ (machLetNames body).length <;>
        first
          | (simp [h0, hc]; done)
          | (simp [h0, hc]; omega))

/-! ## (ii) `machReserve` -/

/-- `machReserve`, written with `Option.bind` and `if` only. -/
def machReserveSpec (natOf : Lean.Expr → Option Nat) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) : Option (Nat × MachRead) :=
  (machSlotKinds (Sparkle.Compiler.MachRawSurface.zetaAll αs)).bind fun kinds =>
    if kinds.isEmpty then none else
    (machInits natOf kinds (Sparkle.Compiler.MachRawSurface.zetaAll initsE)).bind fun inits =>
      if st.dom.any (fun d => d != dom') then none else
      some (st.kinds.size, reserved st dom' body kinds inits)

/-- The compiler's `machReserve` IS that function. Every discriminant is
decided (`cases` / `by_cases`); each leaf closes by reduction. -/
theorem machReserve_eq_spec (natOf : Lean.Expr → Option Nat) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) :
    machReserve natOf dom' αs initsE body st = machReserveSpec natOf dom' αs initsE body st := by
  unfold machReserve machReserveSpec
  cases machSlotKinds (Sparkle.Compiler.MachRawSurface.zetaAll αs) with
  | none => first | rfl | simp
  | some kinds =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    by_cases hc : kinds.isEmpty = true
    · first
        | (simp only [if_pos hc]; done)
        | (simp [hc]; done)
    · simp only [if_neg hc]
      cases machInits natOf kinds (Sparkle.Compiler.MachRawSurface.zetaAll initsE) with
      | none => first | rfl | simp
      | some inits =>
        cases st.dom with
        | none =>
          first
            | rfl
            | (simp [reserved]; done)
        | some d0 =>
          by_cases hd : (d0 != dom') = true
          · first
              | (simp only [Option.bind_some, Option.bind_none, Option.any_some, if_pos hd]; done)
              | (simp [hd, reserved]; done)
              | rfl
          · first
              | (simp only [Option.bind_some, Option.any_some, if_neg hd]; rfl)
              | (simp only [Option.bind_some, Option.any_some, if_neg hd]; done)
              | (simp [hd, reserved]; done)
              | rfl

theorem ite_none_some {α : Type} {c : Prop} [Decidable c] {x : Option α} {b : α}
    (h : (if c then none else x) = some b) : x = some b := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h; exact h

/-- **What `machReserve` returns**: the state `reserved st dom' body kinds
inits`, for kinds and reset values it read. -/
theorem machReserve_some {natOf : Lean.Expr → Option Nat} {dom' αs initsE body : Lean.Expr}
    {st : MachRead} {base : Nat} {st' : MachRead}
    (hr : machReserve natOf dom' αs initsE body st = some (base, st')) :
    ∃ (kinds : List MixedGateBinder) (inits : List Nat),
      machSlotKinds (Sparkle.Compiler.MachRawSurface.zetaAll αs) = some kinds ∧
      machInits natOf kinds (Sparkle.Compiler.MachRawSurface.zetaAll initsE) = some inits ∧
      base = st.kinds.size ∧ st' = reserved st dom' body kinds inits := by
  rw [machReserve_eq_spec] at hr
  unfold machReserveSpec at hr
  obtain ⟨kinds, hks, hr⟩ := Option.bind_eq_some_iff.mp hr
  replace hr := ite_none_some hr
  obtain ⟨inits, hin, hr⟩ := Option.bind_eq_some_iff.mp hr
  replace hr := ite_none_some hr
  have hp := Prod.mk.inj (Option.some.inj hr)
  exact ⟨kinds, inits, hks, hin, hp.1.symm, hp.2.symm⟩

/-- **(ii)** `machReserve` preserves the length invariant. -/
theorem machReserve_lenOk {natOf : Lean.Expr → Option Nat} {dom' αs initsE body : Lean.Expr}
    {st : MachRead} {base : Nat} {st' : MachRead} (h : st.LenOk)
    (hr : machReserve natOf dom' αs initsE body st = some (base, st')) : st'.LenOk := by
  obtain ⟨kinds, inits, _, hin, _, hst⟩ := machReserve_some hr
  rw [hst]
  exact lenOk_reserved h dom' body (machInits_length natOf kinds _ inits hin)
    (machSlotNames_length _ body kinds _)

/-- `machReserve` applied to the initial state `{}` itself. NOT the
wrapper's situation as it stands: at 5098–5099 the state `machReserve`
receives is the one `machConv` returned for the domain expression, and that
it satisfies the invariant (or is `{}`) is a fact about a `partial`
function. This lemma is (i) + (ii) composed, nothing more. -/
theorem machReserve_lenOk_init {natOf : Lean.Expr → Option Nat}
    {dom' αs initsE body : Lean.Expr} {base : Nat} {st' : MachRead}
    (hr : machReserve natOf dom' αs initsE body ({} : MachRead) = some (base, st')) :
    st'.LenOk :=
  machReserve_lenOk lenOk_init hr

end Tools.ShippingReaderLenOk
