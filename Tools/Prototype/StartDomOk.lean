import Tools.Prototype.PreprocLetOk

/-! # Unit SDOM3: the domain a SUCCESSFUL run keeps (`machDom?` success ⇒ `LetOk 0` of the start domain)

BUILT: sd1 exit 1 (base `run_meta` syntax), sd2 exit 1, sd3 exit 1, sd4 exit 0 (final). No sorry / axiom / native_decide.

Fact used: every site of the reader that writes `st.dom` either writes it when it is `none`, or writes `dom'` after the guard
`d0 != dom'` (`BEq Expr` = the extern `Expr.eqv`, alpha-equivalence) has passed.  So along any run the kept domain is a CHAIN
`D = d₀ ~ d₁ ~ … ~ d_k` of `==`-steps.  `DK D st` : `st.dom = some d` with `DChain D d`.  This file proves, for every fuel and
without a premise, that the fuel reader keeps `DK D` (`dreadF_good`).  The ONLY premise (`ExprEqvAtom`: `Expr.eqv` answers `true` against an atom only for that atom; a statement about the
extern `Expr.eqv`, NOT proved) enters at the very end, in the BACKWARD direction from the final `machDom?`-accepted domain. -/
namespace Tools.Prototype.StartDomOk
open Lean Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingReaderLenOk
open Tools.Prototype.ReaderExec Tools.Prototype.PreprocLetOk
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.ShippingReaderFuelShapeProv

/-- the kept domain is `==`-linked to `D` by a chain of guard passes -/
inductive DChain (D : Lean.Expr) : Lean.Expr → Prop
  | refl : DChain D D
  | step {d d' : Lean.Expr} : DChain D d → (d == d') = true → DChain D d'

abbrev DK (D : Lean.Expr) (st : MachRead) : Prop := ∃ d, st.dom = some d ∧ DChain D d

/-- A call table that keeps `LenOk`: every answered call whose input state
is `LenOk` returns a `LenOk` state. -/
def DGoodH (D : Lean.Expr) (h : Hs) : Prop :=
  ∀ c, DK D (Call.inSt c) → ∀ v, h c = some (some v) → DK D (Call.outSt c v)

variable {D : Lean.Expr}

/-! ## The state of a result -/

class DHasSt (α : Type) where
  st : α → MachRead

instance dhasStRead : DHasSt MachRead := ⟨id⟩

instance dhasStProd {α β : Type} [DHasSt β] : DHasSt (α × β) := ⟨fun p => DHasSt.st p.2⟩

/-- The result's state is `LenOk`. -/
abbrev DStOk (D : Lean.Expr) {α : Type} [DHasSt α] (a : α) : Prop := DK D (DHasSt.st a)

theorem stOk_pair {α β : Type} [DHasSt β] (a : α) (b : β) : DStOk D (a, b) = DStOk D b := rfl

theorem stOk_read (st : MachRead) : DStOk D st = (DK D st) := rfl

/-- Every OK result of `x` (against `h`) has a `LenOk` state. -/
abbrev DSat (D : Lean.Expr) {α : Type} [DHasSt α] (h : Hs) (x : BM (Option α)) : Prop :=
  ∀ a, x.run h = some (some a) → DStOk D a

/-! ## Combinators (Hoare-style; each proof is a few lines, no case crunch) -/

section Comb
variable {h : Hs} {α β : Type} [DHasSt α]

theorem dsat_pure {o : Option α} (ho : ∀ a, o = some a → DStOk D a) : DSat D h (FM.pure o) := by
  intro a ha
  rw [run_pure] at ha
  exact ho a (Option.some.inj ha)

theorem dsat_okO {a : α} (ha : DStOk D a) : DSat D h (okO a) :=
  dsat_pure fun b hb => by
    injection hb with hb1
    subst hb1
    exact ha

theorem dsat_failO : DSat D h (failO : BM (Option α)) :=
  dsat_pure fun b hb => by cases hb

theorem dsat_optK {o : Option β} {f : β → BM (Option α)} (hf : ∀ b, o = some b → DSat D h (f b)) :
    DSat D h (optK o f) := by
  cases o with
  | none => exact dsat_failO
  | some b => exact hf b rfl

theorem dsat_bindO [DHasSt β] {x : BM (Option β)} {f : β → BM (Option α)} (hx : DSat D h x)
    (hf : ∀ b, DStOk D b → DSat D h (f b)) : DSat D h (bindO x f) := by
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b => exact hf b (hx b ho) a ha

theorem dsat_bind {x : BM β} {f : β → BM (Option α)}
    (hf : ∀ r, x.run h = some r → DSat D h (f r)) : DSat D h (FM.bind x f) := by
  intro a ha
  rw [run_bind] at ha
  obtain ⟨r, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  exact hf r hr a ha

theorem dsat_ite {c : Prop} [Decidable c] {x y : BM (Option α)} (hx : DSat D h x) (hy : DSat D h y) :
    DSat D h (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx
  · rw [if_neg hc]
    exact hy

theorem dsat_domGuard {o : Option Lean.Expr} {dom' : Lean.Expr} {k : BM (Option α)}
    (ho : ∃ d0, o = some d0 ∧ DChain D d0)
    (hk : ∀ d0, o = some d0 → DChain D d0 → (d0 == dom') = true → DSat D h k) :
    DSat D h (domGuard o dom' k) := by
  obtain ⟨d0, hd0, hc⟩ := ho
  subst hd0
  simp only [domGuard]
  by_cases hb : (d0 != dom') = true
  · rw [if_pos hb]; exact dsat_failO
  · rw [if_neg hb]
    refine hk d0 rfl hc ?_
    simpa [bne] using hb

theorem dsat_pure_ite {c : Prop} [Decidable c] {a : α} (ha : DStOk D a) :
    DSat D h (FM.pure (if c then some a else none)) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact dsat_okO ha
  · rw [if_neg hc]
    exact dsat_failO

end Comb

/-! ## `foldO` / `findSomeO` -/

theorem dsat_foldO {σ α : Type} [DHasSt σ] {h : Hs} {f : σ → α → BM (Option σ)}
    (hf : ∀ s a, DStOk D s → DSat D h (f s a)) :
    ∀ (l : List α) (s : σ), DStOk D s → DSat D h (foldO f s l)
  | [], _, hs => dsat_okO hs
  | a :: l, s, hs => dsat_bindO (hf s a hs) (fun s' hs' => dsat_foldO hf l s' hs')

theorem dsat_findSomeO {α β : Type} [DHasSt β] {h : Hs} {f : α → BM (Option β)}
    (hf : ∀ a, DSat D h (f a)) : ∀ (l : List α), DSat D h (findSomeO f l)
  | [] => dsat_failO
  | a :: l => by
    refine dsat_bind ?_
    intro r hr
    cases r with
    | none => exact dsat_findSomeO hf l
    | some b => exact dsat_okO (hf a b hr)

theorem dfoldO_ok {σ α : Type} [DHasSt σ] {h : Hs} {f : σ → α → BM (Option σ)}
    (hf : ∀ s a, DStOk D s → DSat D h (f s a)) :
    ∀ (l : List α) (s s' : σ), DStOk D s → (foldO f s l).run h = some (some s') → DStOk D s' :=
  fun l s s' hs hr => dsat_foldO hf l s hs s' hr

theorem dfindSomeO_ok {α β : Type} [DHasSt β] {h : Hs} {f : α → BM (Option β)}
    (hf : ∀ a, DSat D h (f a)) :
    ∀ (l : List α) (b : β), (findSomeO f l).run h = some (some b) → DStOk D b :=
  fun l b hr => dsat_findSomeO hf l b hr

/-! ## The answers of the calls -/

section Out
variable {h : Hs}

theorem dout_conv (hG : DGoodH D h) {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    {v : Lean.Expr} {st' : MachRead} (hc : h (Call.conv env d e st) = some (some (v, st')))
    (hst : (DK D st)) : (DK D st') :=
  hG (Call.conv env d e st) hst (v, st') hc

theorem dout_nested (hG : DGoodH D h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} {v : Lean.Expr} {st' : MachRead}
    (hc : h (Call.nested env dom αs initsE body st) = some (some (v, st'))) (hst : (DK D st)) :
    (DK D st') :=
  hG (Call.nested env dom αs initsE body st) hst (v, st') hc

theorem dout_inst (hG : DGoodH D h) {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} {st : MachRead} {v : Lean.Expr}
    {st' : MachRead} (hc : h (Call.inst env c org kinds res args st) = some (some (v, st')))
    (hst : (DK D st)) : (DK D st') :=
  hG (Call.inst env c org kinds res args st) hst (v, st') hc

theorem dout_instS (hG : DGoodH D h) {env : List MachVal} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead} {v : Lean.Expr} {st' : MachRead}
    (hc : h (Call.instS env c kinds ty args st) = some (some (v, st'))) (hst : (DK D st)) :
    (DK D st') :=
  hG (Call.instS env c kinds ty args st) hst (v, st') hc

theorem dout_chain (hG : DGoodH D h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} {st' : MachRead}
    (hc : h (Call.chain env e st) = some (some (ws, v, st'))) (hst : (DK D st)) : (DK D st') :=
  hG (Call.chain env e st) hst (ws, v, st') hc

theorem dout_loopBody (hG : DGoodH D h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} (hc : h (Call.loopBody base env e st) = some (some st'))
    (hst : (DK D st)) : (DK D st') :=
  hG (Call.loopBody base env e st) hst st' hc

theorem dout_loopRoot (hG : DGoodH D h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {mv : MachVal} {st' : MachRead} (hc : h (Call.loopRoot env e st) = some (some (mv, st')))
    (hst : (DK D st)) : (DK D st') :=
  hG (Call.loopRoot env e st) hst (mv, st') hc

/-! The same, as `DSat` facts of the call combinators. -/

theorem dsat_cConv (hG : DGoodH D h) {env : List MachVal} {d : Nat} {e : Lean.Expr}
    {st : MachRead} (hst : (DK D st)) : DSat D h (cConv env d e st) :=
  fun p hp => hG (Call.conv env d e st) hst p hp

theorem dsat_cNested (hG : DGoodH D h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} (hst : (DK D st)) : DSat D h (cNested env dom αs initsE body st) :=
  fun p hp => hG (Call.nested env dom αs initsE body st) hst p hp

theorem dsat_cInst (hG : DGoodH D h) {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} {st : MachRead} (hst : (DK D st)) :
    DSat D h (cInst env c org kinds res args st) :=
  fun p hp => hG (Call.inst env c org kinds res args st) hst p hp

theorem dsat_cInstS (hG : DGoodH D h) {env : List MachVal} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead}
    (hst : (DK D st)) : DSat D h (cInstS env c kinds ty args st) :=
  fun p hp => hG (Call.instS env c kinds ty args st) hst p hp

theorem dsat_cChain (hG : DGoodH D h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hst : (DK D st)) : DSat D h (cChain env e st) :=
  fun p hp => hG (Call.chain env e st) hst p hp

theorem dsat_cLoopBody (hG : DGoodH D h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} (hst : (DK D st)) : DSat D h (cLoopBody base env e st) :=
  fun p hp => hG (Call.loopBody base env e st) hst p hp

theorem dsat_cLoopRoot (hG : DGoodH D h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hst : (DK D st)) : DSat D h (cLoopRoot env e st) :=
  fun p hp => hG (Call.loopRoot env e st) hst p hp

end Out

/-! ## Leaf tactics (small; names prefixed so that no keyword leaks) -/

/-- Close `DStOk D r` of an updated state from a hypothesis (the updates that do not write `dom` are `rfl`-defeq). -/
macro "d5close" : tactic => `(tactic| assumption)

/-- A leaf `hr : o = some r` of a pure `Option` value: `none = some r` is
absurd; `some x = some r` gives `r = x`, closed by `d5close`. -/
macro "d5leaf " hr:ident : tactic => `(tactic| first
  | (cases $hr:ident; done)
  | (injection $hr:ident with hq; subst hq; d5close)
  | (cases $hr:ident; d5close))

/-- A `let (x, y) := p; k` continuation: `t` directly (structure eta of the
pair `match`), or after splitting the pair `match` (≤ 3 goals). -/
macro "d5pair " t:tactic : tactic => `(tactic| first
  | $t:tactic
  | (split <;> $t:tactic)
  | ((try dsimp only); split <;> $t:tactic)
  | ((try dsimp only); (repeat' split) <;> $t:tactic))

/-! ## Pure fragments -/

/-- `machConv`'s `.bvar` arm returns its input state. Goals: `if` (2), then
the 5-arm `match` on `env[j - d]?` (5 leaves; the `.state b n` leaf is a
3-bind `do` block). -/
theorem dconvBvar_ok {env : List MachVal} {d j : Nat} {st : MachRead}
    {r : Lean.Expr × MachRead} (hr : convBvar env d j st = some r) (hst : (DK D st)) : DStOk D r := by
  unfold convBvar at hr
  split at hr
  · injection hr with hr1
    subst hr1
    exact hst
  · split at hr
    all_goals first
      | (cases hr; done)
      | (injection hr with hr1; subst hr1; exact hst)
      | (try simp only [Option.bind_eq_bind] at hr
         obtain ⟨_, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         obtain ⟨_, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         obtain ⟨⟨_, _⟩, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         injection hr with hr1
         subst hr1
         exact hst)

/-- `machInstance`'s entry step (3 constructors, one leaf each). -/
theorem dinstEntry_ok {res : MixedGateBinder} {st st' : MachRead}
    (hr : instEntry res st = some st') (hst : (DK D st)) : (DK D st') := by
  cases res with
  | bits w =>
    have hr' : some st = some st' := hr
    injection hr' with hr1
    subst hr1
    exact hst
  | bool =>
    have hr' : some { st with instStruct := true } = some st' := hr
    injection hr' with hr1
    subst hr1
    exact (by assumption)
  | domain =>
    have hr' : (none : Option MachRead) = some st' := hr
    cases hr'

/-! ## The `foldlM` / `findSome?` functions -/

section Helpers
variable {h : Hs}

/-- Goals after the call: `match kind` (2) → `match st.dom` / pair (2 + 1)
→ `if` (2): 4 leaves. -/
theorem instArg_dsat (hG : DGoodH D h) (env : List MachVal) (k : Nat) :
    ∀ s a, DStOk D s → DSat D h (instArg env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hst : (DK D st))
  refine dsat_bindO (dsat_cConv hG hst) ?_
  rintro ⟨v', st1⟩ (h1 : (DK D st1))
  have h1' := h1
  obtain ⟨d0, hd0, -⟩ := h1
  refine dsat_pure ?_
  intro r hr
  repeat' split at hr
  all_goals first | d5leaf hr | (exfalso; simp_all)

theorem instSArg_dsat (hG : DGoodH D h) (env : List MachVal) :
    ∀ s a, DStOk D s → DSat D h (instSArg env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hst : (DK D st))
  refine dsat_bindO (dsat_cConv hG hst) ?_
  rintro ⟨v', st1⟩ (h1 : (DK D st1))
  have h1' := h1
  obtain ⟨d0, hd0, -⟩ := h1
  refine dsat_pure ?_
  intro r hr
  repeat' split at hr
  all_goals first | d5leaf hr | (exfalso; simp_all)

theorem instSParam_dsat (hG : DGoodH D h) (env : List MachVal) :
    ∀ s a, DStOk D s → DSat D h (instSParam env s a) := by
  rintro ⟨ps, st⟩ p (hst : (DK D st))
  refine dsat_bindO (dsat_cConv hG hst) ?_
  rintro ⟨p', st1⟩ (h1 : (DK D st1))
  refine dsat_okO ?_
  exact h1

theorem loopNext_dsat (hG : DGoodH D h) (env : List MachVal) (base : Nat) :
    ∀ s a, DStOk D s → DSat D h (loopNext env base s a) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩ (hst : (DK D st))
  refine dsat_bindO (dsat_cConv hG hst) ?_
  rintro ⟨nx', st1⟩ (h1 : (DK D st1))
  refine dsat_okO ?_
  exact h1

theorem nestedProbe_dsat (hG : DGoodH D h) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) (hst : (DK D st)) : ∀ a, DSat D h (nestedProbe env dom' αs initsE body st a) := by
  rintro ⟨base, d, a, ini, ws, v⟩
  refine dsat_ite ?_ dsat_failO
  refine dsat_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact dsat_failO
  · have h' : (DK D st') := dsat_cChain hG hst (ws', v', st') hr
    refine dsat_pure_ite ?_
    exact h'

theorem loopProbe_dsat (hG : DGoodH D h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st : MachRead) (hst : (DK D st)) : ∀ a, DSat D h (loopProbe env body n st a) := by
  rintro ⟨b0, n0, ws0⟩
  refine dsat_ite dsat_failO ?_
  refine dsat_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact dsat_failO
  · have h' : (DK D st') := dsat_cLoopBody hG ((by assumption)) st' hr
    refine dsat_pure_ite ?_
    exact (by assumption)

theorem dinstArgFold_ok (hG : DGoodH D h) {env : List MachVal} {k : Nat}
    {l : List (MixedGateBinder × Lean.Expr)} {js js' : List Nat} {st st' : MachRead}
    (hr : (foldO (instArg env k) (js, st) l).run h = some (some (js', st'))) (hst : (DK D st)) :
    (DK D st') :=
  dfoldO_ok (instArg_dsat hG env k) l (js, st) (js', st') hst hr

theorem dinstSArgFold_ok (hG : DGoodH D h) {env : List MachVal}
    {l : List (MixedGateBinder × Lean.Expr)} {js js' : List Nat} {st st' : MachRead}
    (hr : (foldO (instSArg env) (js, st) l).run h = some (some (js', st'))) (hst : (DK D st)) :
    (DK D st') :=
  dfoldO_ok (instSArg_dsat hG env) l (js, st) (js', st') hst hr

theorem dinstSParamFold_ok (hG : DGoodH D h) {env : List MachVal} {l : List Lean.Expr}
    {ps ps' : List Lean.Expr} {st st' : MachRead}
    (hr : (foldO (instSParam env) (ps, st) l).run h = some (some (ps', st'))) (hst : (DK D st)) :
    (DK D st') :=
  dfoldO_ok (instSParam_dsat hG env) l (ps, st) (ps', st') hst hr

theorem dloopNextFold_ok (hG : DGoodH D h) {env : List MachVal} {base : Nat}
    {l : List (Lean.Expr × Lean.Expr × Lean.Expr)} {ws ws' : List (Nat × Lean.Expr)}
    {st st' : MachRead}
    (hr : (foldO (loopNext env base) (ws, st) l).run h = some (some (ws', st'))) (hst : (DK D st)) :
    (DK D st') :=
  dfoldO_ok (loopNext_dsat hG env base) l (ws, st) (ws', st') hst hr

theorem dnestedFind_ok (hG : DGoodH D h) {env : List MachVal} {dom' αs initsE body : Lean.Expr}
    {st : MachRead}
    {l : List (Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr)}
    {r : Lean.Expr × MachRead}
    (hr : (findSomeO (nestedProbe env dom' αs initsE body st) l).run h = some (some r))
    (hst : (DK D st)) : DStOk D r :=
  dfindSomeO_ok (nestedProbe_dsat hG env dom' αs initsE body st hst) l r hr

theorem dloopFind_ok (hG : DGoodH D h) {env : List MachVal} {body : Lean.Expr} {n : Nat}
    {st : MachRead} {l : List (Nat × Nat × List (Nat × Lean.Expr))} {b0 : Nat} {st' : MachRead}
    (hr : (findSomeO (loopProbe env body n st) l).run h = some (some (b0, st')))
    (hst : (DK D st)) : (DK D st') :=
  dfindSomeO_ok (loopProbe_dsat hG env body n st hst) l (b0, st') hr

end Helpers

/-! ## The seven bodies -/

section Arms
variable {h : Hs}

/-- `machConv`'s `.app` arm. One `split` per view, in source order:
`regView?` (2) → [`if` → `bareRegs.find?` (2) → 2 `optK` → call → `domGuard`
→ call → `okO`] / `machLoopRead?` (2) → `machRunApp?` (2) → `machInstCall?`
(2) → `machInstCallS?` (2) → `memCall?` (2) → `machReadV` (2): at most 2 open
goals at any time, 9 leaves. -/
theorem conv_app_sat (senv : StructEnv) (hG : DGoodH D h) (env : List MachVal) (d : Nat)
    (f a : Lean.Expr) (st : MachRead) (hst : (DK D st)) :
    DSat D h (convStep senv env d (.app f a) st) := by
  first
    | simp only [convStep]
    | (unfold convStep; dsimp only)
  split
  · -- a bare `Signal.register`
    refine dsat_ite dsat_failO ?_
    split
    · refine dsat_okO ?_
      exact hst
    · refine dsat_optK ?_
      intro kind _
      refine dsat_optK ?_
      intro initN _
      refine dsat_bindO (dsat_cConv hG hst) ?_
      rintro ⟨dom', st1⟩ (h1 : (DK D st1))
      refine dsat_domGuard h1 ?_
      intro d0 _ hc0 hb
      refine dsat_bindO (dsat_cConv hG (by exact ⟨dom', rfl, DChain.step hc0 hb⟩)) ?_
      rintro ⟨x', st2⟩ (h2 : (DK D st2))
      refine dsat_okO ?_
      exact (by assumption)
  · split
    · -- a loop read
      refine dsat_pure_ite ?_
      exact hst
    · split
      · -- a nested machine
        exact dsat_ite dsat_failO (dsat_cNested hG hst)
      · split
        · -- an instance
          exact dsat_ite dsat_failO (dsat_cInst hG hst)
        · split
          · -- a structure instance
            exact dsat_ite dsat_failO (dsat_cInstS hG hst)
          · split
            · -- a memory
              refine dsat_ite dsat_failO (dsat_bindO (dsat_cInst hG hst) ?_)
              rintro ⟨v, st1⟩ (h1 : (DK D st1))
              refine dsat_okO ?_
              exact (by assumption)
            · split
              · -- a state read
                refine dsat_pure_ite ?_
                exact hst
              · -- an application
                refine dsat_bindO (dsat_cConv hG hst) ?_
                rintro ⟨f', st1⟩ (h1 : (DK D st1))
                refine dsat_bindO (dsat_cConv hG h1) ?_
                rintro ⟨a', st2⟩ (h2 : (DK D st2))
                refine dsat_okO ?_
                exact h2

/-- `machConv`'s `.letE` arm: `if` → `rootFloat` (2) → `if` (2) →
`machTailV` (2) → `machHandleV` (2): 5 leaves. -/
theorem conv_letE_sat (senv : StructEnv) (hG : DGoodH D h) (env : List MachVal) (d : Nat)
    (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead) (hst : (DK D st)) :
    DSat D h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine dsat_ite dsat_failO ?_
  split
  · exact dsat_cConv hG hst
  · refine dsat_ite ?_ ?_
    · refine dsat_bindO (dsat_cLoopRoot hG hst) ?_
      rintro ⟨mv, st1⟩ (h1 : (DK D st1))
      exact dsat_cConv hG h1
    · split
      · exact dsat_cConv hG hst
      · split
        · exact dsat_cConv hG hst
        · refine dsat_bindO (dsat_cConv hG hst) ?_
          rintro ⟨v', st1⟩ (h1 : (DK D st1))
          d5pair (exact dsat_cConv hG ((by assumption)))

/-- `machConv`: `cases e` (12 constructors); `.bvar` by `dconvBvar_ok`,
`.app` / `.letE` by their lemmas, `.lam` / `.forallE` two calls, the rest one
leaf each (`okO (e, st)` or `failO`). -/
theorem conv_dsat (senv : StructEnv) (hG : DGoodH D h) (env : List MachVal) (d : Nat)
    (e : Lean.Expr) (st : MachRead) (hst : (DK D st)) : DSat D h (convStep senv env d e st) := by
  cases e
  case bvar j =>
    refine dsat_pure ?_
    intro r hr
    exact dconvBvar_ok hr hst
  case app f a => exact conv_app_sat senv hG env d f a st hst
  case letE nm ty v b nd => exact conv_letE_sat senv hG env d nm ty v b nd st hst
  case lam nm t b bi =>
    refine dsat_bindO (dsat_cConv hG hst) ?_
    rintro ⟨t', st1⟩ (h1 : (DK D st1))
    refine dsat_bindO (dsat_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : (DK D st2))
    refine dsat_okO ?_
    exact h2
  case forallE nm t b bi =>
    refine dsat_bindO (dsat_cConv hG hst) ?_
    rintro ⟨t', st1⟩ (h1 : (DK D st1))
    refine dsat_bindO (dsat_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : (DK D st2))
    refine dsat_okO ?_
    exact h2
  all_goals first
    | (refine dsat_okO ?_; exact hst)
    | exact dsat_failO

/-- `machReserve` keeps the domain chain: it writes `dom := some dom'` only after the guard `d != dom'` has passed. -/
theorem machReserve_dk {natOf : Lean.Expr → Option Nat} {dom' αs initsE body : Lean.Expr}
    {st : MachRead} {base : Nat} {st' : MachRead} (hst : DK D st)
    (hr : machReserve natOf dom' αs initsE body st = some (base, st')) : DK D st' := by
  obtain ⟨d0, hd0, hc⟩ := hst
  rw [machReserve_eq_spec] at hr
  unfold machReserveSpec at hr
  obtain ⟨kinds, hks, hr⟩ := Option.bind_eq_some_iff.mp hr
  replace hr := ite_none_some hr
  obtain ⟨inits, hin, hr⟩ := Option.bind_eq_some_iff.mp hr
  by_cases hb : (st.dom.any fun d => d != dom') = true
  · rw [if_pos hb] at hr
    cases hr
  · rw [if_neg hb] at hr
    have hp := Prod.mk.inj (Option.some.inj hr)
    have hst' : st' = reserved st dom' body kinds inits := hp.2.symm
    subst hst'
    refine ⟨dom', rfl, ?_⟩
    have hb' : (d0 != dom') = false := by
      cases hh : (d0 != dom')
      · rfl
      · exfalso
        apply hb
        rw [hd0, Option.any_some, hh]
    have he : (d0 == dom') = true := by
      cases e : (d0 == dom')
      · simp [bne, e] at hb'
      · rfl
    exact DChain.step hc he

/-- `machNested`: `if` → call → `findSomeO` → `match shared` (2) →
`machReserve` → call → `okO`. -/
theorem nested_dsat (senv : StructEnv) (hG : DGoodH D h) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) (hst : (DK D st)) :
    DSat D h (nestedStep senv env dom αs initsE body st) := by
  refine dsat_ite dsat_failO ?_
  refine dsat_bindO (dsat_cConv hG hst) ?_
  rintro ⟨dom', st1⟩ (h1 : (DK D st1))
  refine dsat_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · refine dsat_optK ?_
    rintro ⟨base, st2⟩ hres
    have h2 : (DK D st2) := machReserve_dk h1 hres
    refine dsat_bindO (dsat_cChain hG ((by assumption))) ?_
    rintro ⟨ws, v, st3⟩ (h3 : (DK D st3))
    refine dsat_okO ?_
    exact (by assumption)
  · refine dsat_okO ?_
    exact dsat_findSomeO (nestedProbe_dsat hG _ _ _ _ _ _ h1) _ r hsh

/-- `machInstance`: `instEntry` → `foldO` → `match findIdx?` (2 leaves). -/
theorem inst_dsat (hG : DGoodH D h) (env : List MachVal) (c : Name)
    (org : Sparkle.Compiler.MachInstOrigin.InstOrigin) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) (hst : (DK D st)) :
    DSat D h (instStep env c org kinds res args st) := by
  refine dsat_optK ?_
  intro st1 hst1
  have h1 : (DK D st1) := dinstEntry_ok hst1 hst
  refine dsat_bindO (dsat_foldO (instArg_dsat hG env _) _ _ ?_) ?_
  · exact h1
  rintro ⟨js, st2⟩ (h2 : (DK D st2))
  refine dsat_pure ?_
  intro r hr
  split at hr
  all_goals d5leaf hr

/-- `machInstanceS`: `if` → 2 `optK` → `match (ctor?, fields)` (2) → `if` →
2 `foldO` → `match findIdx?` (2 leaves). -/
theorem instS_dsat (senv : StructEnv) (hG : DGoodH D h) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hst : (DK D st)) : DSat D h (instSStep senv env c kinds ty args st) := by
  refine dsat_ite dsat_failO ?_
  refine dsat_optK ?_
  intro resTy _
  refine dsat_optK ?_
  intro r _
  obtain ⟨oc, fields⟩ := r
  cases oc with
  | none => exact dsat_failO
  | some ctor =>
    refine dsat_ite dsat_failO ?_
    refine dsat_bindO (dsat_foldO (instSArg_dsat hG env) _ _ ?_) ?_
    · exact hst
    rintro ⟨js, st1⟩ (h1 : (DK D st1))
    refine dsat_bindO (dsat_foldO (instSParam_dsat hG env) _ _ ?_) ?_
    · exact h1
    rintro ⟨params, st2⟩ (h2 : (DK D st2))
    try dsimp only
    split
    · refine dsat_okO ?_
      exact h2
    · refine dsat_okO ?_
      exact (by assumption)

/-- `machChain`: the 4-arm source `match` split ONCE (the input state's
`LenOk` reverted so that it follows the split): `pure'` (1 leaf), `bind
(next h rhs)` (inner `match` 2), `letE` (as `machConv`'s, 5 leaves),
wildcard (`failO`). -/
theorem chain_dsat (senv : StructEnv) (hG : DGoodH D h) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) (hst : (DK D st)) : DSat D h (chainStep senv env e st) := by
  revert hst
  unfold chainStep
  split
  · intro hst
    refine dsat_bindO (dsat_cConv hG hst) ?_
    rintro ⟨v', st1⟩ (h1 : (DK D st1))
    refine dsat_okO ?_
    exact h1
  · intro hst
    refine dsat_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → (DK D b) := by
      intro a b he
      subst he
      exact dsat_cConv hG hst (a, b) hr
    revert hr'
    split
    · intro hr'
      have h1 := hr' _ _ rfl
      refine dsat_ite ?_ dsat_failO
      refine dsat_bindO (dsat_cChain hG h1) ?_
      rintro ⟨ws, v, st2⟩ (h2 : (DK D st2))
      refine dsat_okO ?_
      exact h2
    · intro _
      exact dsat_failO
  · intro hst
    split
    · exact dsat_cChain hG hst
    · refine dsat_ite ?_ ?_
      · refine dsat_bindO (dsat_cLoopRoot hG hst) ?_
        rintro ⟨mv, st1⟩ (h1 : (DK D st1))
        exact dsat_cChain hG h1
      · split
        · exact dsat_cChain hG hst
        · split
          · exact dsat_cChain hG hst
          · refine dsat_bindO (dsat_cConv hG hst) ?_
            rintro ⟨v', st1⟩ (h1 : (DK D st1))
            d5pair (exact dsat_cChain hG ((by assumption)))
  · intro _
    exact dsat_failO

/-- `machLoopBody`: `cases e` (12); `.letE` one call then a recursive call,
the other 11 the wildcard arm (`optK` → `foldO` → `okO`). -/
theorem loopBody_dsat (hG : DGoodH D h) (base : Nat) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) (hst : (DK D st)) : DSat D h (loopBodyStep base env e st) := by
  cases e
  case letE nm ty v b nd =>
    refine dsat_bindO (dsat_cConv hG hst) ?_
    rintro ⟨v', st1⟩ (h1 : (DK D st1))
    d5pair (exact dsat_cLoopBody hG ((by assumption)))
  all_goals
    unfold loopBodyStep
    try dsimp only
    refine dsat_optK ?_
    intro regs _
    refine dsat_bindO (dsat_foldO (loopNext_dsat hG _ _) _ _ ?_) ?_
    · exact hst
    rintro ⟨ws, st1⟩ (h1 : (DK D st1))
    refine dsat_okO ?_
    exact (by assumption)

/-- `machLoopRoot`: `loopView?` (2) → `if` → `optK` → `if` → 2 `optK` → call
→ `domGuard` → `findSomeO` → `match shared` (2) → call → `okO`. -/
theorem loopRoot_dsat (senv : StructEnv) (hG : DGoodH D h) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) (hst : (DK D st)) : DSat D h (loopRootStep senv env e st) := by
  unfold loopRootStep
  split
  · refine dsat_ite dsat_failO ?_
    refine dsat_optK ?_
    intro regs _
    refine dsat_ite dsat_failO ?_
    refine dsat_optK ?_
    intro kinds hk
    refine dsat_optK ?_
    intro inits hi
    refine dsat_bindO (dsat_cConv hG hst) ?_
    rintro ⟨dom', st1⟩ (h1 : (DK D st1))
    refine dsat_domGuard h1 ?_
    intro d0 _ hc0 hb
    refine dsat_bind ?_
    intro shared hsh
    rcases shared with _ | ⟨b0, st2⟩
    · refine dsat_bindO (dsat_cLoopBody hG (by exact ⟨dom', rfl, DChain.step hc0 hb⟩)) ?_
      rintro st3 (h3 : (DK D st3))
      refine dsat_okO ?_
      exact (by assumption)
    · refine dsat_okO ?_
      exact dsat_findSomeO (loopProbe_dsat hG _ _ _ _ h1) _ (b0, st2) hsh
  · exact dsat_failO

end Arms

/-- **One step keeps `LenOk`**: if the table keeps it, the body run against
the table keeps it. -/
theorem dstep_good (senv : StructEnv) {h : Hs} (hG : DGoodH D h) :
    DGoodH D (fun c => (step senv c).run h) := by
  intro c hin v hv
  cases c with
  | conv env d e st => exact conv_dsat senv hG env d e st hin v hv
  | nested env dom αs initsE body st => exact nested_dsat senv hG env dom αs initsE body st hin v hv
  | inst env c org kinds res args st => exact inst_dsat hG env c org kinds res args st hin v hv
  | instS env c kinds ty args st => exact instS_dsat senv hG env c kinds ty args st hin v hv
  | chain env e st => exact chain_dsat senv hG env e st hin v hv
  | loopBody base env e st => exact loopBody_dsat hG base env e st hin v hv
  | loopRoot env e st => exact loopRoot_dsat senv hG env e st hin v hv

/-- **R5 of the fuel reader, for ALL fuels**: every fuel's table keeps
`LenOk` (induction on the fuel). -/
theorem dreadF_good (senv : StructEnv) : ∀ n, DGoodH D (readF senv n)
  | 0 => fun c _ v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => dstep_good senv (dreadF_good senv n)

theorem machConvF_dk {n : Nat} {senv : StructEnv} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machConvF n senv env d e st = some (some (r, st'))) (hst : (DK D st)) : (DK D st') :=
  dreadF_good senv n (Call.conv env d e st) hst (r, st') h

theorem machNestedF_dk {n : Nat} {senv : StructEnv} {env : List MachVal}
    {dom αs initsE body : Lean.Expr} {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machNestedF n senv env dom αs initsE body st = some (some (r, st'))) (hst : (DK D st)) :
    (DK D st') :=
  dreadF_good senv n (Call.nested env dom αs initsE body st) hst (r, st') h

theorem machInstanceF_dk {n : Nat} {senv : StructEnv} {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin}
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr}
    {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machInstanceF n senv env c org kinds res args st = some (some (r, st')))
    (hst : (DK D st)) : (DK D st') :=
  dreadF_good senv n (Call.inst env c org kinds res args st) hst (r, st') h

theorem machInstanceSF_dk {n : Nat} {senv : StructEnv} {env : List MachVal} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machInstanceSF n senv env c kinds ty args st = some (some (r, st'))) (hst : (DK D st)) :
    (DK D st') :=
  dreadF_good senv n (Call.instS env c kinds ty args st) hst (r, st') h

theorem machChainF_dk {n : Nat} {senv : StructEnv} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} {st' : MachRead}
    (h : machChainF n senv env e st = some (some (ws, v, st'))) (hst : (DK D st)) : (DK D st') :=
  dreadF_good senv n (Call.chain env e st) hst (ws, v, st') h

theorem machLoopBodyF_dk {n : Nat} {senv : StructEnv} {base : Nat} {env : List MachVal}
    {e : Lean.Expr} {st st' : MachRead}
    (h : machLoopBodyF n senv base env e st = some (some st')) (hst : (DK D st)) : (DK D st') :=
  dreadF_good senv n (Call.loopBody base env e st) hst st' h

theorem machLoopRootF_dk {n : Nat} {senv : StructEnv} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {mv : MachVal} {st' : MachRead}
    (h : machLoopRootF n senv env e st = some (some (mv, st'))) (hst : (DK D st)) : (DK D st') :=
  dreadF_good senv n (Call.loopRoot env e st) hst (mv, st') h

/-! ## The wrapper: the domain of a successful run -/

/-- **PREMISE (NOT proved)**, narrowed to what the final `machDom?` acceptance needs: the extern `Expr.eqv` (the `BEq Expr`
behind the guard `d0 != dom'`) can only answer `true` against an ATOM (an `fvar` or a `const`, the only shapes `machDom?`
accepts) for an expression that is that atom.  It is NOT a statement about `Expr.eqv` on general Exprs. -/
def ExprEqvAtom : Prop := ∀ a b : Lean.Expr, (a == b) = true →
  ((∃ id, b = Lean.Expr.fvar id) ∨ (∃ n ls, b = Lean.Expr.const n ls)) → a = b

/-- BACKWARD direction along the guard chain: if the domain the run ends with is an atom, every domain in the chain equals it. -/
theorem dchain_eq (hE : ExprEqvAtom) {D d : Lean.Expr} (hc : DChain D d)
    (hat : (∃ id, d = Lean.Expr.fvar id) ∨ (∃ n ls, d = Lean.Expr.const n ls)) : D = d := by
  induction hc with
  | refl => rfl
  | step _ hb ih =>
    have e := hE _ _ hb hat
    subst e
    exact ih hat

/-- STEP 1: what `machDom?` accepts is a `_machIn` variable or `defaultDomain` (an atom), in range at every table size. -/
theorem machDom_accept {n : Nat} {d : Lean.Expr} {r : Lean.Expr × Sparkle.IR.Type.ResetKind}
    (h : machDom? n d = some r) :
    ((∃ id, d = Lean.Expr.fvar id) ∨ (∃ n ls, d = Lean.Expr.const n ls)) ∧ ∀ k, LetOk k d = true := by
  unfold machDom? at h
  split at h
  · exact ⟨Or.inl ⟨_, rfl⟩, fun k => by simp [LetOk, letFv]⟩
  · exact ⟨Or.inr ⟨_, _, rfl⟩, fun k => by simp [LetOk]⟩
  · cases h

theorem shapePost_dom {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (h : shapePost ai p m st v = some sp) :
    ∃ (domE : Lean.Expr) (dm : Lean.Expr × Sparkle.IR.Type.ResetKind),
      (st.dom <|> machTypeDom? p.d.type) = some domE ∧
      machDom? (st.insts.size + st.kinds.size + st.lets.size) domE = some dm := by
  unfold shapePost at h
  dsimp only at h
  split at h; · simp at h
  split at h; · simp at h
  split at h; · simp at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨domE, hd, dm, hm, -⟩ := h
  exact ⟨domE, dm, hd, hm⟩

theorem shapeRootLet_dk {n : Nat} {senv : StructEnv} (s : List MachVal × MachRead)
    (a : Name × Lean.Expr × Lean.Expr) (s' : List MachVal × MachRead) (hs : DK D s.2)
    (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s')) : DK D s'.2 := by
  obtain ⟨env, st⟩ := s
  obtain ⟨nm, ty, v⟩ := a
  first
    | (simp only [shapeRootLet] at hr)
    | (unfold shapeRootLet at hr; try dsimp only at hr)
  split at hr
  · obtain ⟨⟨mv, st2⟩, hl2, hr⟩ := bindO_some_inv hr
    have hp := machLoopRootF_dk hl2 hs
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact hp
  · split at hr
    · obtain ⟨⟨v', st2⟩, hc, hr⟩ := bindO_some_inv hr
      have hp := machConvF_dk hc hs
      try dsimp only at hr
      have e := okO_run_inv hr
      subst e
      generalize (if (!st2.loops.isEmpty && machIsSlot v') = true then machBindLetNamed nm ty v' st2.lets
        else machBindLet nm ty v' st2.lets) = bl
      obtain ⟨x, lets'⟩ := bl
      exact hp
    · exact (failO_run_inv hr).elim

theorem rootLets_dk {n : Nat} {senv : StructEnv} {l : List (Name × Lean.Expr × Lean.Expr)}
    {env env' : List MachVal} {st0 st1 : MachRead} (h0 : DK D st0)
    (hr : (foldO (shapeRootLet senv) (env, st0) l).run (wtab senv n) = some (some (env', st1))) :
    DK D st1 :=
  foldO_inv_mem (h := wtab senv n) (fun s : List MachVal × MachRead => DK D s.2)
    (fun _ : Name × Lean.Expr × Lean.Expr => True) (f := shapeRootLet senv)
    (fun s a s' _ hs hr => shapeRootLet_dk s a s' hs hr) l (env, st0) (env', st1)
    (fun _ _ => trivial) h0 hr

theorem shapeBody_dk {n : Nat} {senv : StructEnv} {m : ShapeMid} {env : List MachVal}
    {st1 st : MachRead} {v : Lean.Expr} (hs : DK D st1)
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v))) : DK D st := by
  unfold shapeBody at hr
  rcases hm : m.run? with _ | ⟨dom, αs, initsE, body⟩
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    subst e1
    exact machConvF_dk hc hs
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨ws, v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    have hp := machChainF_dk hc hs
    subst e1
    exact hp

/-- **SUCCESS-RESTRICTED `startDom`** (PROVED from the premise `ExprEqvAtom` only).  If the wrapper succeeds at fuel `n`
with the phases `machineShapeN_steps` gives, then the start-domain fact `ShapeInOk.startDom` holds AT THAT FUEL `n`.  It is
NOT the all-fuel `StartDomOk` (see the report: the missing lemma is fuel monotonicity/determinism of `machConvF`). -/
theorem startDom_succ (hE : ExprEqvAtom) {senv : StructEnv} {n : Nat} {m : ShapeMid}
    {ai : Bool} {p : ShapePre} {st0 st1 st : MachRead} {env : List MachVal} {v : Lean.Expr} {sp : MachineShape}
    (h0 : (shapeStart senv m).run (wtab senv n) = some (some st0))
    (h1 : (foldO (shapeRootLet senv) (([] : List MachVal), st0) m.rootLets).run (wtab senv n) =
      some (some (env, st1)))
    (h2 : (shapeBody m env st1).run (wtab senv n) = some (some (st, v)))
    (h3 : shapePost ai p m st v = some sp) :
    ∀ dom αs initsE body dom' stc, m.run? = some (dom, αs, initsE, body) →
      machConvF n senv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead) =
        some (some (dom', stc)) → LetOk 0 dom' = true := by
  intro dom αs initsE body dom' stc hm hc
  rcases shapeStart_inv h0 with ⟨hm0, _⟩ | ⟨dom2, αs2, i2, b2, dom2', stc2, base, hm2, hc2, hres⟩
  · rw [hm0] at hm; cases hm
  · rw [hm2] at hm
    have e1 : dom2 = dom := (Prod.mk.inj (Option.some.inj hm)).1
    subst e1
    have e2 : dom2' = dom' := by
      rw [hc2] at hc
      exact (Prod.mk.inj (Option.some.inj (Option.some.inj hc))).1
    rw [← e2]
    obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hres
    have k0 : DK dom2' st0 := ⟨dom2', by rw [hst]; rfl, DChain.refl⟩
    have k1 := rootLets_dk k0 h1
    have k2 := shapeBody_dk k1 h2
    obtain ⟨d, hdk, hch⟩ := k2
    obtain ⟨domE, dm, hd, hdm⟩ := shapePost_dom h3
    rw [hdk] at hd
    have hde : domE = d := by
      simp at hd
      first | exact hd.symm | exact hd
    subst hde
    have hac := machDom_accept hdm
    rw [dchain_eq hE hch hac.1]
    exact hac.2 0

/-- **`machineShapeN_lets'''`** (new; `machineShapeN_lets''` is unchanged): the field `StartDomOk` of `machineShapeN_lets''`
is REPLACED by the success-fuel fact `startDom_succ`, which is DERIVED (no `hstart` hypothesis) from the premise
`ExprEqvAtom` (an unproved statement about the extern `Expr.eqv` on atoms).  Premises: `RootFloatRange`, `LiftRange`,
`Inst1Range`, `SigTyRange senv`, `ZeroLitAgrees`, `NormRange senv`, `ExprEqvAtom`, and the input `hpe`.  The all-fuel
`StartDomOk` is NOT claimed. -/
theorem machineShapeN_lets''' {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv) (hz : ZeroLitAgrees) (hnorm : NormRange senv)
    (hE : ExprEqvAtom)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp := by
  obtain ⟨n, p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3⟩ := machineShapeN_steps h
  have hex : execNorm senv p.e = some en := (execNorm_iff senv).mpr ⟨n, hen⟩
  obtain ⟨hrl, hrt, hrb⟩ := shapeMid_ok hroot hz senv p en (hnorm _ _ (hpe p hp) hex)
  have r0 : RdOk st0 := shapeStart_ok (n := n) (startDom_succ hE h0 h1 h2 h3) h0
  have r1 := rootLets_ok hroot hlift hinst1 hsig Tools.ShippingLetsReaderInv.bundleIotaRange hrl r0 h1
    (fun v hv => by cases hv)
  have r2 := shapeBody_ok hroot hlift hinst1 hsig Tools.ShippingLetsReaderInv.bundleIotaRange r1.1 r1.2 hrt hrb
    (shapeMid_wrap_ok senv p en hrt) h2
  exact ⟨p, en, st, v, hp, hex, r2.1, r2.1.1, r2.2.2, h3⟩

#print axioms machineShapeN_lets'''
run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_lets'''
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "NormRange", "ExprEqvAtom", "Eq", "Eq"])
#print axioms startDom_succ
#print axioms dreadF_good

end Tools.Prototype.StartDomOk
