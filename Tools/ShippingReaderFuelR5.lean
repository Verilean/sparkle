import Tools.ShippingReaderFuelRun
import Tools.ShippingReaderLenOkReserve

/-! # R5 for the fuel candidate: every returned reader state keeps `LenOk`

STATUS 2026-10-19 (worker O, branch `par/o-cand`): WRITTEN, NOT BUILT against
the patched compiler (explicit call-entry origin, `MachRead.instOrigins`).
`LenOk` has a third part (`origins : instOrigins.size = insts.size`); the
leaf lemmas `lenOk_instPush` / `lenOk_instS` are the patched push / append;
`Call.inst` takes `org`. New: `machConvF_origins`, `machChainF_origins`,
`machLoopRootF_origins`, `machInstanceF_origins` (alignment at every fuel).

BUILT on poc after 65eaccbb (run `r5`, cgrun -j 1; integrator fixes: `$t:tactic` in the r5pair macro, `unfold loopBodyStep` in its wildcard arms) (worker R5, branch `par/r-7`, from poc `22908c5f`). No
`sorry`, no axiom, no `native_decide`, no Mathlib tactic. No hypothesis beyond
the input state's `LenOk`.

Imports ONLY: `Tools/ShippingReaderFuelDefs.lean` and
`Tools/ShippingReaderFuelKleene.lean` (BUILT on poc), the small
`Tools/ShippingReaderFuelRun.lean` (three `rfl` lemmas `run_pure`, `run_bind`,
`run_bindO`), and the BUILT `LenOk` update lemmas
(`Tools/ShippingReaderLenOk.lean`, `Tools/ShippingReaderLenOkReserve.lean`:
`lenOk_*`, `machReserve_lenOk`, `loopRoot_inits_length`). It does NOT import
`ShippingReaderFuelOldEq` (reviewer ruling 2026-10-15).

SCOPE. This is a property of the NEW fuel functions (`readF`, `machConvF`, …)
by themselves: induction on the fuel, one step at a time. It says nothing
about the old `partial` readers (`machConv`, …); it is NOT connected to them
(that needs `OldEq → IsSol`, the separate OldEq file, which does not build
yet), and it does not discharge `ReadersKeepLenOk` of the old readers.

* `step_good` — if a call table keeps `LenOk` (`GoodH`), the body run against
  it keeps `LenOk`;
* `readF_good` — every fuel's table keeps `LenOk` (induction on the fuel);
* `machConvF_lenOk`, `machNestedF_lenOk`, `machInstanceF_lenOk`,
  `machInstanceSF_lenOk`, `machChainF_lenOk`, `machLoopBodyF_lenOk`,
  `machLoopRootF_lenOk`, `readersKeepLenOkF`, `machConvF_lenOk_init`.

PROOF STYLE (after the integrator's notes on the previous draft, see
docs/parallel/R-reader-fuel.md, R5 section): no `repeat' split` over whole
bodies. Each body is taken apart in its own order with Hoare-style
combinator lemmas (`sat_bindO`, `sat_optK`, `sat_ite`, `sat_bind`, …), each
`match` split once on the goal where its arm is reached, each leaf closed by
one named update lemma. Expected goal counts are recorded per arm. -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderLenOk

/-! ## Input and output states of a call -/

def Call.inSt : Call → MachRead
  | Call.conv _ _ _ st => st
  | Call.nested _ _ _ _ _ st => st
  | Call.inst _ _ _ _ _ _ st => st
  | Call.instS _ _ _ _ _ st => st
  | Call.chain _ _ st => st
  | Call.loopBody _ _ _ st => st
  | Call.loopRoot _ _ st => st

def Call.outSt : (c : Call) → c.Res → MachRead
  | Call.conv .., p => Prod.snd (p : Lean.Expr × MachRead)
  | Call.nested .., p => Prod.snd (p : Lean.Expr × MachRead)
  | Call.inst .., p => Prod.snd (p : Lean.Expr × MachRead)
  | Call.instS .., p => Prod.snd (p : Lean.Expr × MachRead)
  | Call.chain .., p => Prod.snd (Prod.snd (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead))
  | Call.loopBody .., s => (s : MachRead)
  | Call.loopRoot .., p => Prod.snd (p : MachVal × MachRead)

/-- A call table that keeps `LenOk`: every answered call whose input state
is `LenOk` returns a `LenOk` state. -/
def GoodH (h : Hs) : Prop :=
  ∀ c, (Call.inSt c).LenOk → ∀ v, h c = some (some v) → (Call.outSt c v).LenOk

/-! ## The state of a result -/

class HasSt (α : Type) where
  st : α → MachRead

instance hasStRead : HasSt MachRead := ⟨id⟩

instance hasStProd {α β : Type} [HasSt β] : HasSt (α × β) := ⟨fun p => HasSt.st p.2⟩

/-- The result's state is `LenOk`. -/
abbrev StOk {α : Type} [HasSt α] (a : α) : Prop := (HasSt.st a).LenOk

theorem stOk_pair {α β : Type} [HasSt β] (a : α) (b : β) : StOk (a, b) = StOk b := rfl

theorem stOk_read (st : MachRead) : StOk st = st.LenOk := rfl

/-- Every OK result of `x` (against `h`) has a `LenOk` state. -/
abbrev Sat {α : Type} [HasSt α] (h : Hs) (x : BM (Option α)) : Prop :=
  ∀ a, x.run h = some (some a) → StOk a

/-! ## Combinators (Hoare-style; each proof is a few lines, no case crunch) -/

section Comb
variable {h : Hs} {α β : Type} [HasSt α]

theorem sat_pure {o : Option α} (ho : ∀ a, o = some a → StOk a) : Sat h (FM.pure o) := by
  intro a ha
  rw [run_pure] at ha
  exact ho a (Option.some.inj ha)

theorem sat_okO {a : α} (ha : StOk a) : Sat h (okO a) :=
  sat_pure fun b hb => by
    injection hb with hb1
    subst hb1
    exact ha

theorem sat_failO : Sat h (failO : BM (Option α)) :=
  sat_pure fun b hb => by cases hb

theorem sat_optK {o : Option β} {f : β → BM (Option α)} (hf : ∀ b, o = some b → Sat h (f b)) :
    Sat h (optK o f) := by
  cases o with
  | none => exact sat_failO
  | some b => exact hf b rfl

theorem sat_bindO [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} (hx : Sat h x)
    (hf : ∀ b, StOk b → Sat h (f b)) : Sat h (bindO x f) := by
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b => exact hf b (hx b ho) a ha

theorem sat_bind {x : BM β} {f : β → BM (Option α)}
    (hf : ∀ r, x.run h = some r → Sat h (f r)) : Sat h (FM.bind x f) := by
  intro a ha
  rw [run_bind] at ha
  obtain ⟨r, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  exact hf r hr a ha

theorem sat_ite {c : Prop} [Decidable c] {x y : BM (Option α)} (hx : Sat h x) (hy : Sat h y) :
    Sat h (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx
  · rw [if_neg hc]
    exact hy

theorem sat_domGuard {o : Option Lean.Expr} {dom' : Lean.Expr} {k : BM (Option α)}
    (hk : Sat h k) : Sat h (domGuard o dom' k) := by
  cases o with
  | none => exact hk
  | some d0 =>
    first
      | exact sat_ite sat_failO hk
      | (simp only [domGuard]; exact sat_ite sat_failO hk)

theorem sat_pure_ite {c : Prop} [Decidable c] {a : α} (ha : StOk a) :
    Sat h (FM.pure (if c then some a else none)) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact sat_okO ha
  · rw [if_neg hc]
    exact sat_failO

end Comb

/-! ## `foldO` / `findSomeO` -/

theorem sat_foldO {σ α : Type} [HasSt σ] {h : Hs} {f : σ → α → BM (Option σ)}
    (hf : ∀ s a, StOk s → Sat h (f s a)) :
    ∀ (l : List α) (s : σ), StOk s → Sat h (foldO f s l)
  | [], _, hs => sat_okO hs
  | a :: l, s, hs => sat_bindO (hf s a hs) (fun s' hs' => sat_foldO hf l s' hs')

theorem sat_findSomeO {α β : Type} [HasSt β] {h : Hs} {f : α → BM (Option β)}
    (hf : ∀ a, Sat h (f a)) : ∀ (l : List α), Sat h (findSomeO f l)
  | [] => sat_failO
  | a :: l => by
    refine sat_bind ?_
    intro r hr
    cases r with
    | none => exact sat_findSomeO hf l
    | some b => exact sat_okO (hf a b hr)

theorem foldO_ok {σ α : Type} [HasSt σ] {h : Hs} {f : σ → α → BM (Option σ)}
    (hf : ∀ s a, StOk s → Sat h (f s a)) :
    ∀ (l : List α) (s s' : σ), StOk s → (foldO f s l).run h = some (some s') → StOk s' :=
  fun l s s' hs hr => sat_foldO hf l s hs s' hr

theorem findSomeO_ok {α β : Type} [HasSt β] {h : Hs} {f : α → BM (Option β)}
    (hf : ∀ a, Sat h (f a)) :
    ∀ (l : List α) (b : β), (findSomeO f l).run h = some (some b) → StOk b :=
  fun l b hr => sat_findSomeO hf l b hr

/-! ## The answers of the calls -/

section Out
variable {h : Hs}

theorem out_conv (hG : GoodH h) {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    {v : Lean.Expr} {st' : MachRead} (hc : h (Call.conv env d e st) = some (some (v, st')))
    (hst : st.LenOk) : st'.LenOk :=
  hG (Call.conv env d e st) hst (v, st') hc

theorem out_nested (hG : GoodH h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} {v : Lean.Expr} {st' : MachRead}
    (hc : h (Call.nested env dom αs initsE body st) = some (some (v, st'))) (hst : st.LenOk) :
    st'.LenOk :=
  hG (Call.nested env dom αs initsE body st) hst (v, st') hc

theorem out_inst (hG : GoodH h) {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} {st : MachRead} {v : Lean.Expr}
    {st' : MachRead} (hc : h (Call.inst env c org kinds res args st) = some (some (v, st')))
    (hst : st.LenOk) : st'.LenOk :=
  hG (Call.inst env c org kinds res args st) hst (v, st') hc

theorem out_instS (hG : GoodH h) {env : List MachVal} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead} {v : Lean.Expr} {st' : MachRead}
    (hc : h (Call.instS env c kinds ty args st) = some (some (v, st'))) (hst : st.LenOk) :
    st'.LenOk :=
  hG (Call.instS env c kinds ty args st) hst (v, st') hc

theorem out_chain (hG : GoodH h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} {st' : MachRead}
    (hc : h (Call.chain env e st) = some (some (ws, v, st'))) (hst : st.LenOk) : st'.LenOk :=
  hG (Call.chain env e st) hst (ws, v, st') hc

theorem out_loopBody (hG : GoodH h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} (hc : h (Call.loopBody base env e st) = some (some st'))
    (hst : st.LenOk) : st'.LenOk :=
  hG (Call.loopBody base env e st) hst st' hc

theorem out_loopRoot (hG : GoodH h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {mv : MachVal} {st' : MachRead} (hc : h (Call.loopRoot env e st) = some (some (mv, st')))
    (hst : st.LenOk) : st'.LenOk :=
  hG (Call.loopRoot env e st) hst (mv, st') hc

/-! The same, as `Sat` facts of the call combinators. -/

theorem sat_cConv (hG : GoodH h) {env : List MachVal} {d : Nat} {e : Lean.Expr}
    {st : MachRead} (hst : st.LenOk) : Sat h (cConv env d e st) :=
  fun p hp => hG (Call.conv env d e st) hst p hp

theorem sat_cNested (hG : GoodH h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} (hst : st.LenOk) : Sat h (cNested env dom αs initsE body st) :=
  fun p hp => hG (Call.nested env dom αs initsE body st) hst p hp

theorem sat_cInst (hG : GoodH h) {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} {st : MachRead} (hst : st.LenOk) :
    Sat h (cInst env c org kinds res args st) :=
  fun p hp => hG (Call.inst env c org kinds res args st) hst p hp

theorem sat_cInstS (hG : GoodH h) {env : List MachVal} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead}
    (hst : st.LenOk) : Sat h (cInstS env c kinds ty args st) :=
  fun p hp => hG (Call.instS env c kinds ty args st) hst p hp

theorem sat_cChain (hG : GoodH h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hst : st.LenOk) : Sat h (cChain env e st) :=
  fun p hp => hG (Call.chain env e st) hst p hp

theorem sat_cLoopBody (hG : GoodH h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} (hst : st.LenOk) : Sat h (cLoopBody base env e st) :=
  fun p hp => hG (Call.loopBody base env e st) hst p hp

theorem sat_cLoopRoot (hG : GoodH h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hst : st.LenOk) : Sat h (cLoopRoot env e st) :=
  fun p hp => hG (Call.loopRoot env e st) hst p hp

end Out

/-! ## Leaf tactics (small; names prefixed so that no keyword leaks) -/

/-- Close `StOk r` / `LenOk` of an updated state from a `LenOk` hypothesis. -/
macro "r5close" : tactic => `(tactic| first
  | assumption
  | exact lenOk_ws ‹_› _
  | exact lenOk_lets ‹_› _
  | exact lenOk_dom ‹_› _
  | exact lenOk_instStruct ‹_› _
  | exact lenOk_inInner ‹_› _
  | exact lenOk_instPush ‹_› _ _ _
  | exact lenOk_instS ‹_› _ _ _ _
  | exact lenOk_nestedClose ‹_› _ _ _
  | exact lenOk_loopClose ‹_› _ _)

/-- A leaf `hr : o = some r` of a pure `Option` value: `none = some r` is
absurd; `some x = some r` gives `r = x`, closed by `r5close`. -/
macro "r5leaf " hr:ident : tactic => `(tactic| first
  | (cases $hr:ident; done)
  | (injection $hr:ident with hq; subst hq; r5close)
  | (cases $hr:ident; r5close))

/-- A `let (x, y) := p; k` continuation: `t` directly (structure eta of the
pair `match`), or after splitting the pair `match` (≤ 3 goals). -/
macro "r5pair " t:tactic : tactic => `(tactic| first
  | $t:tactic
  | (split <;> $t:tactic)
  | ((try dsimp only); split <;> $t:tactic)
  | ((try dsimp only); (repeat' split) <;> $t:tactic))

/-! ## Pure fragments -/

/-- `machConv`'s `.bvar` arm returns its input state. Goals: `if` (2), then
the 5-arm `match` on `env[j - d]?` (5 leaves; the `.state b n` leaf is a
3-bind `do` block). -/
theorem convBvar_ok {env : List MachVal} {d j : Nat} {st : MachRead}
    {r : Lean.Expr × MachRead} (hr : convBvar env d j st = some r) (hst : st.LenOk) : StOk r := by
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
theorem instEntry_ok {res : MixedGateBinder} {st st' : MachRead}
    (hr : instEntry res st = some st') (hst : st.LenOk) : st'.LenOk := by
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
    exact lenOk_instStruct hst true
  | domain =>
    have hr' : (none : Option MachRead) = some st' := hr
    cases hr'

/-! ## The `foldlM` / `findSome?` functions -/

section Helpers
variable {h : Hs}

/-- Goals after the call: `match kind` (2) → `match st.dom` / pair (2 + 1)
→ `if` (2): 4 leaves. -/
theorem instArg_sat (hG : GoodH h) (env : List MachVal) (k : Nat) :
    ∀ s a, StOk s → Sat h (instArg env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hst : st.LenOk)
  refine sat_bindO (sat_cConv hG hst) ?_
  rintro ⟨v', st1⟩ (h1 : st1.LenOk)
  refine sat_pure ?_
  intro r hr
  repeat' split at hr
  all_goals r5leaf hr

theorem instSArg_sat (hG : GoodH h) (env : List MachVal) :
    ∀ s a, StOk s → Sat h (instSArg env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hst : st.LenOk)
  refine sat_bindO (sat_cConv hG hst) ?_
  rintro ⟨v', st1⟩ (h1 : st1.LenOk)
  refine sat_pure ?_
  intro r hr
  repeat' split at hr
  all_goals r5leaf hr

theorem instSParam_sat (hG : GoodH h) (env : List MachVal) :
    ∀ s a, StOk s → Sat h (instSParam env s a) := by
  rintro ⟨ps, st⟩ p (hst : st.LenOk)
  refine sat_bindO (sat_cConv hG hst) ?_
  rintro ⟨p', st1⟩ (h1 : st1.LenOk)
  refine sat_okO ?_
  exact h1

theorem loopNext_sat (hG : GoodH h) (env : List MachVal) (base : Nat) :
    ∀ s a, StOk s → Sat h (loopNext env base s a) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩ (hst : st.LenOk)
  refine sat_bindO (sat_cConv hG hst) ?_
  rintro ⟨nx', st1⟩ (h1 : st1.LenOk)
  refine sat_okO ?_
  exact h1

theorem nestedProbe_sat (hG : GoodH h) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) (hst : st.LenOk) : ∀ a, Sat h (nestedProbe env dom' αs initsE body st a) := by
  rintro ⟨base, d, a, ini, ws, v⟩
  refine sat_ite ?_ sat_failO
  refine sat_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact sat_failO
  · have h' : st'.LenOk := sat_cChain hG hst (ws', v', st') hr
    refine sat_pure_ite ?_
    exact h'

theorem loopProbe_sat (hG : GoodH h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st : MachRead) (hst : st.LenOk) : ∀ a, Sat h (loopProbe env body n st a) := by
  rintro ⟨b0, n0, ws0⟩
  refine sat_ite sat_failO ?_
  refine sat_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact sat_failO
  · have h' : st'.LenOk := sat_cLoopBody hG (lenOk_ws hst _) st' hr
    refine sat_pure_ite ?_
    exact lenOk_ws h' _

theorem instArgFold_ok (hG : GoodH h) {env : List MachVal} {k : Nat}
    {l : List (MixedGateBinder × Lean.Expr)} {js js' : List Nat} {st st' : MachRead}
    (hr : (foldO (instArg env k) (js, st) l).run h = some (some (js', st'))) (hst : st.LenOk) :
    st'.LenOk :=
  foldO_ok (instArg_sat hG env k) l (js, st) (js', st') hst hr

theorem instSArgFold_ok (hG : GoodH h) {env : List MachVal}
    {l : List (MixedGateBinder × Lean.Expr)} {js js' : List Nat} {st st' : MachRead}
    (hr : (foldO (instSArg env) (js, st) l).run h = some (some (js', st'))) (hst : st.LenOk) :
    st'.LenOk :=
  foldO_ok (instSArg_sat hG env) l (js, st) (js', st') hst hr

theorem instSParamFold_ok (hG : GoodH h) {env : List MachVal} {l : List Lean.Expr}
    {ps ps' : List Lean.Expr} {st st' : MachRead}
    (hr : (foldO (instSParam env) (ps, st) l).run h = some (some (ps', st'))) (hst : st.LenOk) :
    st'.LenOk :=
  foldO_ok (instSParam_sat hG env) l (ps, st) (ps', st') hst hr

theorem loopNextFold_ok (hG : GoodH h) {env : List MachVal} {base : Nat}
    {l : List (Lean.Expr × Lean.Expr × Lean.Expr)} {ws ws' : List (Nat × Lean.Expr)}
    {st st' : MachRead}
    (hr : (foldO (loopNext env base) (ws, st) l).run h = some (some (ws', st'))) (hst : st.LenOk) :
    st'.LenOk :=
  foldO_ok (loopNext_sat hG env base) l (ws, st) (ws', st') hst hr

theorem nestedFind_ok (hG : GoodH h) {env : List MachVal} {dom' αs initsE body : Lean.Expr}
    {st : MachRead}
    {l : List (Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr)}
    {r : Lean.Expr × MachRead}
    (hr : (findSomeO (nestedProbe env dom' αs initsE body st) l).run h = some (some r))
    (hst : st.LenOk) : StOk r :=
  findSomeO_ok (nestedProbe_sat hG env dom' αs initsE body st hst) l r hr

theorem loopFind_ok (hG : GoodH h) {env : List MachVal} {body : Lean.Expr} {n : Nat}
    {st : MachRead} {l : List (Nat × Nat × List (Nat × Lean.Expr))} {b0 : Nat} {st' : MachRead}
    (hr : (findSomeO (loopProbe env body n st) l).run h = some (some (b0, st')))
    (hst : st.LenOk) : st'.LenOk :=
  findSomeO_ok (loopProbe_sat hG env body n st hst) l (b0, st') hr

end Helpers

/-! ## The seven bodies -/

section Arms
variable {h : Hs}

/-- `machConv`'s `.app` arm. One `split` per view, in source order:
`regView?` (2) → [`if` → `bareRegs.find?` (2) → 2 `optK` → call → `domGuard`
→ call → `okO`] / `machLoopRead?` (2) → `machRunApp?` (2) → `machInstCall?`
(2) → `machInstCallS?` (2) → `memCall?` (2) → `machReadV` (2): at most 2 open
goals at any time, 9 leaves. -/
theorem conv_app_sat (senv : StructEnv) (hG : GoodH h) (env : List MachVal) (d : Nat)
    (f a : Lean.Expr) (st : MachRead) (hst : st.LenOk) :
    Sat h (convStep senv env d (.app f a) st) := by
  first
    | simp only [convStep]
    | (unfold convStep; dsimp only)
  split
  · -- a bare `Signal.register`
    refine sat_ite sat_failO ?_
    split
    · refine sat_okO ?_
      exact hst
    · refine sat_optK ?_
      intro kind _
      refine sat_optK ?_
      intro initN _
      refine sat_bindO (sat_cConv hG hst) ?_
      rintro ⟨dom', st1⟩ (h1 : st1.LenOk)
      refine sat_domGuard ?_
      refine sat_bindO (sat_cConv hG (lenOk_bareRegister h1 _ _ _ _ _ _)) ?_
      rintro ⟨x', st2⟩ (h2 : st2.LenOk)
      refine sat_okO ?_
      exact lenOk_ws h2 _
  · split
    · -- a loop read
      refine sat_pure_ite ?_
      exact hst
    · split
      · -- a nested machine
        exact sat_ite sat_failO (sat_cNested hG hst)
      · split
        · -- an instance
          exact sat_ite sat_failO (sat_cInst hG hst)
        · split
          · -- a structure instance
            exact sat_ite sat_failO (sat_cInstS hG hst)
          · split
            · -- a memory
              refine sat_ite sat_failO (sat_bindO (sat_cInst hG hst) ?_)
              rintro ⟨v, st1⟩ (h1 : st1.LenOk)
              refine sat_okO ?_
              exact lenOk_instStruct h1 _
            · split
              · -- a state read
                refine sat_pure_ite ?_
                exact hst
              · -- an application
                refine sat_bindO (sat_cConv hG hst) ?_
                rintro ⟨f', st1⟩ (h1 : st1.LenOk)
                refine sat_bindO (sat_cConv hG h1) ?_
                rintro ⟨a', st2⟩ (h2 : st2.LenOk)
                refine sat_okO ?_
                exact h2

/-- `machConv`'s `.letE` arm: `if` → `rootFloat` (2) → `if` (2) →
`machTailV` (2) → `machHandleV` (2): 5 leaves. -/
theorem conv_letE_sat (senv : StructEnv) (hG : GoodH h) (env : List MachVal) (d : Nat)
    (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead) (hst : st.LenOk) :
    Sat h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine sat_ite sat_failO ?_
  split
  · exact sat_cConv hG hst
  · refine sat_ite ?_ ?_
    · refine sat_bindO (sat_cLoopRoot hG hst) ?_
      rintro ⟨mv, st1⟩ (h1 : st1.LenOk)
      exact sat_cConv hG h1
    · split
      · exact sat_cConv hG hst
      · split
        · exact sat_cConv hG hst
        · refine sat_bindO (sat_cConv hG hst) ?_
          rintro ⟨v', st1⟩ (h1 : st1.LenOk)
          r5pair (exact sat_cConv hG (lenOk_lets h1 _))

/-- `machConv`: `cases e` (12 constructors); `.bvar` by `convBvar_ok`,
`.app` / `.letE` by their lemmas, `.lam` / `.forallE` two calls, the rest one
leaf each (`okO (e, st)` or `failO`). -/
theorem conv_sat (senv : StructEnv) (hG : GoodH h) (env : List MachVal) (d : Nat)
    (e : Lean.Expr) (st : MachRead) (hst : st.LenOk) : Sat h (convStep senv env d e st) := by
  cases e
  case bvar j =>
    refine sat_pure ?_
    intro r hr
    exact convBvar_ok hr hst
  case app f a => exact conv_app_sat senv hG env d f a st hst
  case letE nm ty v b nd => exact conv_letE_sat senv hG env d nm ty v b nd st hst
  case lam nm t b bi =>
    refine sat_bindO (sat_cConv hG hst) ?_
    rintro ⟨t', st1⟩ (h1 : st1.LenOk)
    refine sat_bindO (sat_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : st2.LenOk)
    refine sat_okO ?_
    exact h2
  case forallE nm t b bi =>
    refine sat_bindO (sat_cConv hG hst) ?_
    rintro ⟨t', st1⟩ (h1 : st1.LenOk)
    refine sat_bindO (sat_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : st2.LenOk)
    refine sat_okO ?_
    exact h2
  all_goals first
    | (refine sat_okO ?_; exact hst)
    | exact sat_failO

/-- `machNested`: `if` → call → `findSomeO` → `match shared` (2) →
`machReserve` → call → `okO`. -/
theorem nested_sat (senv : StructEnv) (hG : GoodH h) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) (hst : st.LenOk) :
    Sat h (nestedStep senv env dom αs initsE body st) := by
  refine sat_ite sat_failO ?_
  refine sat_bindO (sat_cConv hG hst) ?_
  rintro ⟨dom', st1⟩ (h1 : st1.LenOk)
  refine sat_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · refine sat_optK ?_
    rintro ⟨base, st2⟩ hres
    have h2 : st2.LenOk := machReserve_lenOk h1 hres
    refine sat_bindO (sat_cChain hG (lenOk_inInner h2 _)) ?_
    rintro ⟨ws, v, st3⟩ (h3 : st3.LenOk)
    refine sat_okO ?_
    exact lenOk_nestedClose h3 _ _ _
  · refine sat_okO ?_
    exact sat_findSomeO (nestedProbe_sat hG _ _ _ _ _ _ h1) _ r hsh

/-- `machInstance`: `instEntry` → `foldO` → `match findIdx?` (2 leaves). -/
theorem inst_sat (hG : GoodH h) (env : List MachVal) (c : Name)
    (org : Sparkle.Compiler.MachInstOrigin.InstOrigin) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) (hst : st.LenOk) :
    Sat h (instStep env c org kinds res args st) := by
  refine sat_optK ?_
  intro st1 hst1
  have h1 : st1.LenOk := instEntry_ok hst1 hst
  refine sat_bindO (sat_foldO (instArg_sat hG env _) _ _ ?_) ?_
  · exact h1
  rintro ⟨js, st2⟩ (h2 : st2.LenOk)
  refine sat_pure ?_
  intro r hr
  split at hr
  all_goals r5leaf hr

/-- `machInstanceS`: `if` → 2 `optK` → `match (ctor?, fields)` (2) → `if` →
2 `foldO` → `match findIdx?` (2 leaves). -/
theorem instS_sat (senv : StructEnv) (hG : GoodH h) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hst : st.LenOk) : Sat h (instSStep senv env c kinds ty args st) := by
  refine sat_ite sat_failO ?_
  refine sat_optK ?_
  intro resTy _
  refine sat_optK ?_
  intro r _
  obtain ⟨oc, fields⟩ := r
  cases oc with
  | none => exact sat_failO
  | some ctor =>
    refine sat_ite sat_failO ?_
    refine sat_bindO (sat_foldO (instSArg_sat hG env) _ _ ?_) ?_
    · exact hst
    rintro ⟨js, st1⟩ (h1 : st1.LenOk)
    refine sat_bindO (sat_foldO (instSParam_sat hG env) _ _ ?_) ?_
    · exact h1
    rintro ⟨params, st2⟩ (h2 : st2.LenOk)
    try dsimp only
    split
    · refine sat_okO ?_
      exact h2
    · refine sat_okO ?_
      exact lenOk_instS h2 _ _ _ _

/-- `machChain`: the 4-arm source `match` split ONCE (the input state's
`LenOk` reverted so that it follows the split): `pure'` (1 leaf), `bind
(next h rhs)` (inner `match` 2), `letE` (as `machConv`'s, 5 leaves),
wildcard (`failO`). -/
theorem chain_sat (senv : StructEnv) (hG : GoodH h) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) (hst : st.LenOk) : Sat h (chainStep senv env e st) := by
  revert hst
  unfold chainStep
  split
  · intro hst
    refine sat_bindO (sat_cConv hG hst) ?_
    rintro ⟨v', st1⟩ (h1 : st1.LenOk)
    refine sat_okO ?_
    exact h1
  · intro hst
    refine sat_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → b.LenOk := by
      intro a b he
      subst he
      exact sat_cConv hG hst (a, b) hr
    revert hr'
    split
    · intro hr'
      have h1 := hr' _ _ rfl
      refine sat_ite ?_ sat_failO
      refine sat_bindO (sat_cChain hG h1) ?_
      rintro ⟨ws, v, st2⟩ (h2 : st2.LenOk)
      refine sat_okO ?_
      exact h2
    · intro _
      exact sat_failO
  · intro hst
    split
    · exact sat_cChain hG hst
    · refine sat_ite ?_ ?_
      · refine sat_bindO (sat_cLoopRoot hG hst) ?_
        rintro ⟨mv, st1⟩ (h1 : st1.LenOk)
        exact sat_cChain hG h1
      · split
        · exact sat_cChain hG hst
        · split
          · exact sat_cChain hG hst
          · refine sat_bindO (sat_cConv hG hst) ?_
            rintro ⟨v', st1⟩ (h1 : st1.LenOk)
            r5pair (exact sat_cChain hG (lenOk_lets h1 _))
  · intro _
    exact sat_failO

/-- `machLoopBody`: `cases e` (12); `.letE` one call then a recursive call,
the other 11 the wildcard arm (`optK` → `foldO` → `okO`). -/
theorem loopBody_sat (hG : GoodH h) (base : Nat) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) (hst : st.LenOk) : Sat h (loopBodyStep base env e st) := by
  cases e
  case letE nm ty v b nd =>
    refine sat_bindO (sat_cConv hG hst) ?_
    rintro ⟨v', st1⟩ (h1 : st1.LenOk)
    r5pair (exact sat_cLoopBody hG (lenOk_lets h1 _))
  all_goals
    unfold loopBodyStep
    try dsimp only
    refine sat_optK ?_
    intro regs _
    refine sat_bindO (sat_foldO (loopNext_sat hG _ _) _ _ ?_) ?_
    · exact hst
    rintro ⟨ws, st1⟩ (h1 : st1.LenOk)
    refine sat_okO ?_
    exact lenOk_ws h1 _

/-- `machLoopRoot`: `loopView?` (2) → `if` → `optK` → `if` → 2 `optK` → call
→ `domGuard` → `findSomeO` → `match shared` (2) → call → `okO`. -/
theorem loopRoot_sat (senv : StructEnv) (hG : GoodH h) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) (hst : st.LenOk) : Sat h (loopRootStep senv env e st) := by
  unfold loopRootStep
  split
  · refine sat_ite sat_failO ?_
    refine sat_optK ?_
    intro regs _
    refine sat_ite sat_failO ?_
    refine sat_optK ?_
    intro kinds hk
    refine sat_optK ?_
    intro inits hi
    have hil : inits.length = kinds.length := loopRoot_inits_length hk hi
    refine sat_bindO (sat_cConv hG hst) ?_
    rintro ⟨dom', st1⟩ (h1 : st1.LenOk)
    refine sat_domGuard ?_
    refine sat_bind ?_
    intro shared hsh
    rcases shared with _ | ⟨b0, st2⟩
    · refine sat_bindO (sat_cLoopBody hG (lenOk_loopRoot h1 hil _ _)) ?_
      rintro st3 (h3 : st3.LenOk)
      refine sat_okO ?_
      exact lenOk_loopClose h3 _ _
    · refine sat_okO ?_
      exact sat_findSomeO (loopProbe_sat hG _ _ _ _ h1) _ (b0, st2) hsh
  · exact sat_failO

end Arms

/-- **One step keeps `LenOk`**: if the table keeps it, the body run against
the table keeps it. -/
theorem step_good (senv : StructEnv) {h : Hs} (hG : GoodH h) :
    GoodH (fun c => (step senv c).run h) := by
  intro c hin v hv
  cases c with
  | conv env d e st => exact conv_sat senv hG env d e st hin v hv
  | nested env dom αs initsE body st => exact nested_sat senv hG env dom αs initsE body st hin v hv
  | inst env c org kinds res args st => exact inst_sat hG env c org kinds res args st hin v hv
  | instS env c kinds ty args st => exact instS_sat senv hG env c kinds ty args st hin v hv
  | chain env e st => exact chain_sat senv hG env e st hin v hv
  | loopBody base env e st => exact loopBody_sat hG base env e st hin v hv
  | loopRoot env e st => exact loopRoot_sat senv hG env e st hin v hv

/-- **R5 of the fuel reader, for ALL fuels**: every fuel's table keeps
`LenOk` (induction on the fuel). -/
theorem readF_good (senv : StructEnv) : ∀ n, GoodH (readF senv n)
  | 0 => fun c _ v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => step_good senv (readF_good senv n)

theorem machConvF_lenOk {n : Nat} {senv : StructEnv} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machConvF n senv env d e st = some (some (r, st'))) (hst : st.LenOk) : st'.LenOk :=
  readF_good senv n (Call.conv env d e st) hst (r, st') h

theorem machNestedF_lenOk {n : Nat} {senv : StructEnv} {env : List MachVal}
    {dom αs initsE body : Lean.Expr} {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machNestedF n senv env dom αs initsE body st = some (some (r, st'))) (hst : st.LenOk) :
    st'.LenOk :=
  readF_good senv n (Call.nested env dom αs initsE body st) hst (r, st') h

theorem machInstanceF_lenOk {n : Nat} {senv : StructEnv} {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin}
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr}
    {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machInstanceF n senv env c org kinds res args st = some (some (r, st')))
    (hst : st.LenOk) : st'.LenOk :=
  readF_good senv n (Call.inst env c org kinds res args st) hst (r, st') h

theorem machInstanceSF_lenOk {n : Nat} {senv : StructEnv} {env : List MachVal} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machInstanceSF n senv env c kinds ty args st = some (some (r, st'))) (hst : st.LenOk) :
    st'.LenOk :=
  readF_good senv n (Call.instS env c kinds ty args st) hst (r, st') h

theorem machChainF_lenOk {n : Nat} {senv : StructEnv} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} {st' : MachRead}
    (h : machChainF n senv env e st = some (some (ws, v, st'))) (hst : st.LenOk) : st'.LenOk :=
  readF_good senv n (Call.chain env e st) hst (ws, v, st') h

theorem machLoopBodyF_lenOk {n : Nat} {senv : StructEnv} {base : Nat} {env : List MachVal}
    {e : Lean.Expr} {st st' : MachRead}
    (h : machLoopBodyF n senv base env e st = some (some st')) (hst : st.LenOk) : st'.LenOk :=
  readF_good senv n (Call.loopBody base env e st) hst st' h

theorem machLoopRootF_lenOk {n : Nat} {senv : StructEnv} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {mv : MachVal} {st' : MachRead}
    (h : machLoopRootF n senv env e st = some (some (mv, st'))) (hst : st.LenOk) : st'.LenOk :=
  readF_good senv n (Call.loopRoot env e st) hst (mv, st') h

/-- **`ReadersKeepLenOk` for the fuel candidate, PROVED** (the three readers
the wrapper calls with a state it keeps), at every fuel. A statement about
the fuel functions only; the old `partial` readers are not involved. -/
theorem readersKeepLenOkF (senv : StructEnv) (n : Nat) :
    (∀ (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead) (r : Lean.Expr)
        (st' : MachRead),
        machConvF n senv env d e st = some (some (r, st')) → st.LenOk → st'.LenOk) ∧
    (∀ (env : List MachVal) (e : Lean.Expr) (st : MachRead) (mv : MachVal) (st' : MachRead),
        machLoopRootF n senv env e st = some (some (mv, st')) → st.LenOk → st'.LenOk) ∧
    (∀ (env : List MachVal) (e : Lean.Expr) (st : MachRead) (ws : List (Nat × Lean.Expr))
        (v : Lean.Expr) (st' : MachRead),
        machChainF n senv env e st = some (some (ws, v, st')) → st.LenOk → st'.LenOk) :=
  ⟨fun _ _ _ _ _ _ h hst => machConvF_lenOk h hst,
   fun _ _ _ _ _ h hst => machLoopRootF_lenOk h hst,
   fun _ _ _ _ _ _ h hst => machChainF_lenOk h hst⟩

/-- From the initial state (`lenOk_init`). -/
theorem machConvF_lenOk_init {n : Nat} {senv : StructEnv} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {r : Lean.Expr} {st' : MachRead}
    (h : machConvF n senv env d e ({} : MachRead) = some (some (r, st'))) : st'.LenOk :=
  machConvF_lenOk h lenOk_init

/-! ## Origin alignment (patched compiler, explicit call-entry origin)

`LenOk` now also says `instOrigins.size = insts.size` (`MachRead.LenOk.origins`):
the two call-entry updates push / append one tag per entry. So every
successful run of the candidate readers, at every fuel, keeps one origin tag
per call entry. -/

theorem machConvF_origins {n : Nat} {senv : StructEnv} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machConvF n senv env d e st = some (some (r, st'))) (hst : st.LenOk) :
    st'.instOrigins.size = st'.insts.size :=
  (machConvF_lenOk h hst).origins

theorem machChainF_origins {n : Nat} {senv : StructEnv} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} {st' : MachRead}
    (h : machChainF n senv env e st = some (some (ws, v, st'))) (hst : st.LenOk) :
    st'.instOrigins.size = st'.insts.size :=
  (machChainF_lenOk h hst).origins

theorem machLoopRootF_origins {n : Nat} {senv : StructEnv} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {mv : MachVal} {st' : MachRead}
    (h : machLoopRootF n senv env e st = some (some (mv, st'))) (hst : st.LenOk) :
    st'.instOrigins.size = st'.insts.size :=
  (machLoopRootF_lenOk h hst).origins

theorem machInstanceF_origins {n : Nat} {senv : StructEnv} {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin}
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr}
    {st : MachRead} {r : Lean.Expr} {st' : MachRead}
    (h : machInstanceF n senv env c org kinds res args st = some (some (r, st')))
    (hst : st.LenOk) : st'.instOrigins.size = st'.insts.size :=
  (machInstanceF_lenOk h hst).origins

end Tools.ShippingReaderFuel
