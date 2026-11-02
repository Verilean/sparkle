import Tools.Assume.ExprEqv
import Tools.ShippingGen5ReaderTraceCtl
import Tools.ShippingReaderFuelR5
import Tools.ShippingReaderLenOkReserve
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceDomKeepF, exit 0) on the tree of 237f86d9179ae02cd11f4a9766bcb668fb4bdeab (Lean content identical; this header is comment-only). Clean build is the coder's. No sorry / axiom / native_decide in source.
-- Written against freeze rev21.1 `scripts/gen5/DG_READERTRACE_FREEZE_REV21.md` §1.1, §3, §5 (`DomForm`, `domForm_shape`, `DomKeepF`, `domKeepF_seq`, `domKeepF_write`, `readF_domKeepF`).

/-! # DG-READERTRACE rev21.1: `DomKeepF` and `readF_domKeepF`

`DomKeepF h`: an answered call whose input state has `dom = some d` returns a state with `dom = some d'` where `DomForm d' → d' = d`.
`readF_domKeepF` takes `EqvAtom` (`Tools/Assume/ExprEqv.lean`, an assumption, NOT claimed true) as a hypothesis; it is used only at the three places
that write `dom := some dom'` after the guard `d != dom'` (conv bare register, `machReserve` (nested), `machLoopRoot`), through `domKeepF_write`.
Independent induction on the fuel (same skeleton as `readF_good` in `Tools/ShippingReaderFuelR5.lean`); `TraceGood` is not touched.
Conditional (intermediate) result: it does not show that `EqvAtom` holds. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingReaderLenOk Tools.Assume.ExprEqv

def DomForm (d : Lean.Expr) : Prop := ∃ r, machDom? 0 d = some r

theorem domForm_shape (d : Lean.Expr) : DomForm d → DomShape d := by
  rintro ⟨r, h⟩
  unfold machDom? at h
  split at h
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · cases h

def DomKeepF (h : Hs) : Prop :=
  ∀ (c : Call) (v : c.Res), h c = some (some v) →
    ∀ d : Lean.Expr, (callSt c).dom = some d →
      ∃ d' : Lean.Expr, (callOut c v).dom = some d' ∧ (DomForm d' → d' = d)

theorem domKeepF_seq {d d1 d2 : Lean.Expr}
    (h1 : DomForm d1 → d1 = d) (h2 : DomForm d2 → d2 = d1) : DomForm d2 → d2 = d := by
  intro hf
  have e := h2 hf
  subst e
  exact h1 hf

theorem domKeepF_write (hE : EqvAtom) {d dom' : Lean.Expr} (hb : (d != dom') = false) :
    DomForm dom' → dom' = d := by
  intro hf
  have hb' : (d == dom') = true := by
    cases hh : (d == dom') <;> simp_all [bne]
  exact (hE d dom' (domForm_shape dom' hf) hb').symm

/-! ## The relation on a result, and Hoare-style combinators -/

/-- the result's state has a `dom` that is `d'` with `DomForm d' → d' = d`. -/
abbrev DomRel {α : Type} [HasSt α] (d : Lean.Expr) (a : α) : Prop :=
  ∃ d' : Lean.Expr, (HasSt.st a).dom = some d' ∧ (DomForm d' → d' = d)

/-- every OK result of `x` (against `h`) relates to `d`. -/
abbrev DK {α : Type} [HasSt α] (h : Hs) (d : Lean.Expr) (x : BM (Option α)) : Prop :=
  ∀ a, x.run h = some (some a) → DomRel d a

theorem domRel_of {α : Type} [HasSt α] {d : Lean.Expr} {a : α} (hd : (HasSt.st a).dom = some d) :
    DomRel d a := ⟨d, hd, fun _ => rfl⟩

section Comb
variable {h : Hs} {α β : Type} [HasSt α] {d : Lean.Expr}

theorem dk_pure {o : Option α} (ho : ∀ a, o = some a → DomRel d a) : DK h d (FM.pure o) := by
  intro a ha
  rw [run_pure] at ha
  exact ho a (Option.some.inj ha)

theorem dk_okO {a : α} (ha : DomRel d a) : DK h d (okO a) :=
  dk_pure fun b hb => by
    injection hb with hb1
    subst hb1
    exact ha

theorem dk_failO : DK h d (failO : BM (Option α)) :=
  dk_pure fun b hb => by cases hb

theorem dk_optK {o : Option β} {f : β → BM (Option α)} (hf : ∀ b, o = some b → DK h d (f b)) :
    DK h d (optK o f) := by
  cases o with
  | none => exact dk_failO
  | some b => exact hf b rfl

theorem dk_bindO [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} (hx : DK h d x)
    (hf : ∀ b d1, (HasSt.st b).dom = some d1 → DK h d1 (f b)) : DK h d (bindO x f) := by
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b =>
    obtain ⟨d1, hd1, r1⟩ := hx b ho
    obtain ⟨d2, hd2, r2⟩ := hf b d1 hd1 a ha
    exact ⟨d2, hd2, domKeepF_seq r1 r2⟩

theorem dk_bind {x : BM β} {f : β → BM (Option α)}
    (hf : ∀ r, x.run h = some r → DK h d (f r)) : DK h d (FM.bind x f) := by
  intro a ha
  rw [run_bind] at ha
  obtain ⟨r, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  exact hf r hr a ha

theorem dk_ite {c : Prop} [Decidable c] {x y : BM (Option α)} (hx : DK h d x) (hy : DK h d y) :
    DK h d (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx
  · rw [if_neg hc]
    exact hy

theorem dk_pure_ite {c : Prop} [Decidable c] {a : α} (ha : DomRel d a) :
    DK h d (FM.pure (if c then some a else none)) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact dk_okO ha
  · rw [if_neg hc]
    exact dk_failO

/-- relate through a known relation of the start dom. -/
theorem dk_lift {d1 : Lean.Expr} {k : BM (Option α)} (hrel : DomForm d1 → d1 = d)
    (hk : DK h d1 k) : DK h d k := by
  intro a ha
  obtain ⟨d2, hd2, r⟩ := hk a ha
  exact ⟨d2, hd2, domKeepF_seq hrel r⟩

/-- `domGuard`: the guard `d1 != dom'` is false on the continuation. -/
theorem dk_domGuard {o : Option Lean.Expr} {d1 dom' : Lean.Expr} {k : BM (Option α)}
    (ho : o = some d1) (hk : (d1 != dom') = false → DK h d1 k) : DK h d1 (domGuard o dom' k) := by
  subst ho
  intro a ha
  unfold domGuard at ha
  dsimp only at ha
  by_cases hb : (d1 != dom') = true
  · rw [if_pos hb, run_pure] at ha
    cases ha
  · rw [if_neg hb] at ha
    have hb' : (d1 != dom') = false := by simpa using hb
    exact hk hb' a ha

end Comb

theorem dk_foldO {σ α : Type} [HasSt σ] {h : Hs} {f : σ → α → BM (Option σ)}
    (hf : ∀ s a d1, (HasSt.st s).dom = some d1 → DK h d1 (f s a)) :
    ∀ (l : List α) (s : σ) (d : Lean.Expr), (HasSt.st s).dom = some d → DK h d (foldO f s l)
  | [], s, _, hs => dk_okO (domRel_of hs)
  | a :: l, s, d, hs => dk_bindO (hf s a d hs) (fun s' d1 hs' => dk_foldO hf l s' d1 hs')

theorem dk_findSomeO {α β : Type} [HasSt β] {h : Hs} {d : Lean.Expr} {f : α → BM (Option β)}
    (hf : ∀ a, DK h d (f a)) : ∀ (l : List α), DK h d (findSomeO f l)
  | [] => dk_failO
  | a :: l => by
    refine dk_bind ?_
    intro r hr
    cases r with
    | none => exact dk_findSomeO hf l
    | some b => exact dk_okO (hf a b hr)

/-! ## The calls -/

section Out
variable {h : Hs}

theorem dk_cConv (hG : DomKeepF h) {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    {dm : Lean.Expr} (hd : st.dom = some dm) : DK h dm (cConv env d e st) :=
  fun p hp => hG (Call.conv env d e st) p hp dm hd

theorem dk_cNested (hG : DomKeepF h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} {dm : Lean.Expr} (hd : st.dom = some dm) :
    DK h dm (cNested env dom αs initsE body st) :=
  fun p hp => hG (Call.nested env dom αs initsE body st) p hp dm hd

theorem dk_cInst (hG : DomKeepF h) {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} {st : MachRead} {dm : Lean.Expr}
    (hd : st.dom = some dm) : DK h dm (cInst env c org kinds res args st) :=
  fun p hp => hG (Call.inst env c org kinds res args st) p hp dm hd

theorem dk_cInstS (hG : DomKeepF h) {env : List MachVal} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead}
    {dm : Lean.Expr} (hd : st.dom = some dm) : DK h dm (cInstS env c kinds ty args st) :=
  fun p hp => hG (Call.instS env c kinds ty args st) p hp dm hd

theorem dk_cChain (hG : DomKeepF h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {dm : Lean.Expr} (hd : st.dom = some dm) : DK h dm (cChain env e st) :=
  fun p hp => hG (Call.chain env e st) p hp dm hd

theorem dk_cLoopBody (hG : DomKeepF h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} {dm : Lean.Expr} (hd : st.dom = some dm) : DK h dm (cLoopBody base env e st) :=
  fun p hp => hG (Call.loopBody base env e st) p hp dm hd

theorem dk_cLoopRoot (hG : DomKeepF h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {dm : Lean.Expr} (hd : st.dom = some dm) : DK h dm (cLoopRoot env e st) :=
  fun p hp => hG (Call.loopRoot env e st) p hp dm hd

end Out

/-! ## Pure fragments -/

theorem convBvar_dk {env : List MachVal} {d j : Nat} {st : MachRead} {r : Lean.Expr × MachRead}
    (hr : convBvar env d j st = some r) {dm : Lean.Expr} (hd : st.dom = some dm) : DomRel dm r := by
  unfold convBvar at hr
  split at hr
  · injection hr with hr1
    subst hr1
    exact domRel_of hd
  · split at hr
    all_goals first
      | (cases hr; done)
      | (injection hr with hr1; subst hr1; exact domRel_of hd)
      | (try simp only [Option.bind_eq_bind] at hr
         obtain ⟨_, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         obtain ⟨_, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         obtain ⟨⟨_, _⟩, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         injection hr with hr1
         subst hr1
         exact domRel_of hd)

theorem instEntry_dom {res : MixedGateBinder} {st st' : MachRead}
    (hr : instEntry res st = some st') {dm : Lean.Expr} (hd : st.dom = some dm) : st'.dom = some dm := by
  cases res with
  | bits w =>
    have hr' : some st = some st' := hr
    injection hr' with hr1
    subst hr1
    exact hd
  | bool =>
    have hr' : some { st with instStruct := true } = some st' := hr
    injection hr' with hr1
    subst hr1
    exact hd
  | domain =>
    have hr' : (none : Option MachRead) = some st' := hr
    cases hr'

/-- what `machReserve` does to `dom`: it writes `dom'`, after a guard that the old `dom` (if any) is `== dom'`. -/
theorem machReserve_dom {natOf : Lean.Expr → Option Nat} {dom' αs initsE body : Lean.Expr}
    {st : MachRead} {base : Nat} {st' : MachRead}
    (hr : machReserve natOf dom' αs initsE body st = some (base, st')) {d1 : Lean.Expr}
    (hd : st.dom = some d1) : st'.dom = some dom' ∧ (d1 != dom') = false := by
  obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hr
  refine ⟨by rw [hst]; rfl, ?_⟩
  cases hne' : (d1 != dom')
  · rfl
  · exfalso
    rw [machReserve_eq_spec] at hr
    unfold machReserveSpec at hr
    obtain ⟨kinds', hks, hr⟩ := Option.bind_eq_some_iff.mp hr
    by_cases hk : kinds'.isEmpty = true
    · rw [if_pos hk] at hr
      cases hr
    · rw [if_neg hk] at hr
      obtain ⟨inits', hin, hr⟩ := Option.bind_eq_some_iff.mp hr
      rw [hd] at hr
      simp only [Option.any_some, hne', if_true] at hr
      cases hr

/-! ## The `foldlM` / `findSome?` functions -/

section Helpers
variable {h : Hs}

theorem instArg_dk (hG : DomKeepF h) (env : List MachVal) (k : Nat) :
    ∀ s a d, (HasSt.st s).dom = some d → DK h d (instArg env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ d (hst : st.dom = some d)
  refine dk_bindO (dk_cConv hG hst) ?_
  rintro ⟨v', st1⟩ d1 (h1 : st1.dom = some d1)
  refine dk_pure ?_
  intro r hr
  simp only [h1] at hr
  repeat' split at hr
  all_goals first
    | (cases hr; done)
    | (injection hr with hq; subst hq; first | exact domRel_of h1 | exact domRel_of rfl)
    | (cases hr; first | exact domRel_of h1 | exact domRel_of rfl)

theorem instSArg_dk (hG : DomKeepF h) (env : List MachVal) :
    ∀ s a d, (HasSt.st s).dom = some d → DK h d (instSArg env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ d (hst : st.dom = some d)
  refine dk_bindO (dk_cConv hG hst) ?_
  rintro ⟨v', st1⟩ d1 (h1 : st1.dom = some d1)
  refine dk_pure ?_
  intro r hr
  simp only [h1] at hr
  repeat' split at hr
  all_goals first
    | (cases hr; done)
    | (injection hr with hq; subst hq; first | exact domRel_of h1 | exact domRel_of rfl)
    | (cases hr; first | exact domRel_of h1 | exact domRel_of rfl)

theorem instSParam_dk (hG : DomKeepF h) (env : List MachVal) :
    ∀ s a d, (HasSt.st s).dom = some d → DK h d (instSParam env s a) := by
  rintro ⟨ps, st⟩ p d (hst : st.dom = some d)
  refine dk_bindO (dk_cConv hG hst) ?_
  rintro ⟨p', st1⟩ d1 (h1 : st1.dom = some d1)
  exact dk_okO (domRel_of h1)

theorem loopNext_dk (hG : DomKeepF h) (env : List MachVal) (base : Nat) :
    ∀ s a d, (HasSt.st s).dom = some d → DK h d (loopNext env base s a) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩ d (hst : st.dom = some d)
  refine dk_bindO (dk_cConv hG hst) ?_
  rintro ⟨nx', st1⟩ d1 (h1 : st1.dom = some d1)
  exact dk_okO (domRel_of h1)

theorem nestedProbe_dk (hG : DomKeepF h) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) {d1 : Lean.Expr} (hd : st.dom = some d1) :
    ∀ a, DK h d1 (nestedProbe env dom' αs initsE body st a) := by
  rintro ⟨base, d, a, ini, ws, v⟩
  refine dk_ite ?_ dk_failO
  refine dk_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact dk_failO
  · have h' : DomRel d1 (ws', v', st') := dk_cChain hG hd (ws', v', st') hr
    exact dk_pure_ite h'

theorem loopProbe_dk (hG : DomKeepF h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st : MachRead) {d1 : Lean.Expr} (hd : st.dom = some d1) :
    ∀ a, DK h d1 (loopProbe env body n st a) := by
  rintro ⟨b0, n0, ws0⟩
  refine dk_ite dk_failO ?_
  refine dk_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact dk_failO
  · have h' : DomRel d1 st' := dk_cLoopBody hG (st := { st with ws := #[] }) hd st' hr
    obtain ⟨d2, hd2, r2⟩ := h'
    exact dk_pure_ite ⟨d2, hd2, r2⟩

end Helpers

/-! ## The seven bodies -/

section Arms
variable {h : Hs}

theorem conv_app_dk (hE : EqvAtom) (senv : StructEnv) (hG : DomKeepF h) (env : List MachVal) (d : Nat)
    (f a : Lean.Expr) (st : MachRead) {dm : Lean.Expr} (hd : st.dom = some dm) :
    DK h dm (convStep senv env d (.app f a) st) := by
  first
    | simp only [convStep]
    | (unfold convStep; dsimp only)
  split
  · -- a bare `Signal.register`
    refine dk_ite dk_failO ?_
    split
    · exact dk_okO (domRel_of hd)
    · refine dk_optK ?_
      intro kind _
      refine dk_optK ?_
      intro initN _
      refine dk_bindO (dk_cConv hG hd) ?_
      rintro ⟨dom', st1⟩ d1 (h1 : st1.dom = some d1)
      refine dk_domGuard h1 ?_
      intro hg
      refine dk_lift (domKeepF_write hE hg) ?_
      dsimp only
      refine dk_bindO (dk_cConv hG ?_) ?_
      · rfl
      rintro ⟨x', st2⟩ d2 (h2 : st2.dom = some d2)
      exact dk_okO (domRel_of h2)
  · split
    · -- a loop read
      exact dk_pure_ite (domRel_of hd)
    · split
      · -- a nested machine
        exact dk_ite dk_failO (dk_cNested hG hd)
      · split
        · -- an instance
          exact dk_ite dk_failO (dk_cInst hG hd)
        · split
          · -- a structure instance
            exact dk_ite dk_failO (dk_cInstS hG hd)
          · split
            · -- a memory
              refine dk_ite dk_failO (dk_bindO (dk_cInst hG hd) ?_)
              rintro ⟨v, st1⟩ d1 (h1 : st1.dom = some d1)
              exact dk_okO (domRel_of h1)
            · split
              · -- a state read
                exact dk_pure_ite (domRel_of hd)
              · -- an application
                refine dk_bindO (dk_cConv hG hd) ?_
                rintro ⟨f', st1⟩ d1 (h1 : st1.dom = some d1)
                refine dk_bindO (dk_cConv hG h1) ?_
                rintro ⟨a', st2⟩ d2 (h2 : st2.dom = some d2)
                exact dk_okO (domRel_of h2)

theorem conv_letE_dk (senv : StructEnv) (hG : DomKeepF h) (env : List MachVal) (d : Nat)
    (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead) {dm : Lean.Expr}
    (hd : st.dom = some dm) : DK h dm (convStep senv env d (.letE nm ty v b nd) st) := by
  refine dk_ite dk_failO ?_
  split
  · exact dk_cConv hG hd
  · refine dk_ite ?_ ?_
    · refine dk_bindO (dk_cLoopRoot hG hd) ?_
      rintro ⟨mv, st1⟩ d1 (h1 : st1.dom = some d1)
      exact dk_cConv hG h1
    · split
      · exact dk_cConv hG hd
      · split
        · exact dk_cConv hG hd
        · refine dk_bindO (dk_cConv hG hd) ?_
          rintro ⟨v', st1⟩ d1 (h1 : st1.dom = some d1)
          r5pair (refine dk_cConv hG ?_; exact h1)

theorem conv_dk (hE : EqvAtom) (senv : StructEnv) (hG : DomKeepF h) (env : List MachVal) (d : Nat)
    (e : Lean.Expr) (st : MachRead) {dm : Lean.Expr} (hd : st.dom = some dm) :
    DK h dm (convStep senv env d e st) := by
  cases e
  case bvar j =>
    refine dk_pure ?_
    intro r hr
    exact convBvar_dk hr hd
  case app f a => exact conv_app_dk hE senv hG env d f a st hd
  case letE nm ty v b nd => exact conv_letE_dk senv hG env d nm ty v b nd st hd
  case lam nm t b bi =>
    refine dk_bindO (dk_cConv hG hd) ?_
    rintro ⟨t', st1⟩ d1 (h1 : st1.dom = some d1)
    refine dk_bindO (dk_cConv hG h1) ?_
    rintro ⟨b', st2⟩ d2 (h2 : st2.dom = some d2)
    exact dk_okO (domRel_of h2)
  case forallE nm t b bi =>
    refine dk_bindO (dk_cConv hG hd) ?_
    rintro ⟨t', st1⟩ d1 (h1 : st1.dom = some d1)
    refine dk_bindO (dk_cConv hG h1) ?_
    rintro ⟨b', st2⟩ d2 (h2 : st2.dom = some d2)
    exact dk_okO (domRel_of h2)
  all_goals first
    | (refine dk_okO ?_; exact domRel_of hd)
    | exact dk_failO

theorem nested_dk (hE : EqvAtom) (senv : StructEnv) (hG : DomKeepF h) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) {dm : Lean.Expr} (hd : st.dom = some dm) :
    DK h dm (nestedStep senv env dom αs initsE body st) := by
  refine dk_ite dk_failO ?_
  refine dk_bindO (dk_cConv hG hd) ?_
  rintro ⟨dom', st1⟩ d1 (h1 : st1.dom = some d1)
  refine dk_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · refine dk_optK ?_
    rintro ⟨base, st2⟩ hres
    obtain ⟨h2, hg⟩ := machReserve_dom hres h1
    refine dk_lift (domKeepF_write hE hg) ?_
    refine dk_bindO (dk_cChain hG (st := { st2 with inInner := true }) ?_) ?_
    · exact h2
    rintro ⟨ws, v, st3⟩ d3 (h3 : st3.dom = some d3)
    exact dk_okO (domRel_of h3)
  · exact dk_okO (dk_findSomeO (nestedProbe_dk hG _ _ _ _ _ _ h1) _ r hsh)

theorem inst_dk (hG : DomKeepF h) (env : List MachVal) (c : Name)
    (org : Sparkle.Compiler.MachInstOrigin.InstOrigin) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) {dm : Lean.Expr}
    (hd : st.dom = some dm) : DK h dm (instStep env c org kinds res args st) := by
  refine dk_optK ?_
  intro st1 hst1
  have h1 : st1.dom = some dm := instEntry_dom hst1 hd
  refine dk_bindO (dk_foldO (instArg_dk hG env _) _ _ _ ?_) ?_
  · exact h1
  rintro ⟨js, st2⟩ d2 (h2 : st2.dom = some d2)
  refine dk_pure ?_
  intro r hr
  split at hr
  all_goals first
    | (cases hr; done)
    | (injection hr with hq; subst hq; exact domRel_of h2)

theorem instS_dk (senv : StructEnv) (hG : DomKeepF h) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    {dm : Lean.Expr} (hd : st.dom = some dm) : DK h dm (instSStep senv env c kinds ty args st) := by
  refine dk_ite dk_failO ?_
  refine dk_optK ?_
  intro resTy _
  refine dk_optK ?_
  intro r _
  obtain ⟨oc, fields⟩ := r
  cases oc with
  | none => exact dk_failO
  | some ctor =>
    refine dk_ite dk_failO ?_
    refine dk_bindO (dk_foldO (instSArg_dk hG env) _ _ _ ?_) ?_
    · exact hd
    rintro ⟨js, st1⟩ d1 (h1 : st1.dom = some d1)
    refine dk_bindO (dk_foldO (instSParam_dk hG env) _ _ _ ?_) ?_
    · exact h1
    rintro ⟨params, st2⟩ d2 (h2 : st2.dom = some d2)
    try dsimp only
    split
    · exact dk_okO (domRel_of h2)
    · exact dk_okO (domRel_of h2)

theorem chain_dk (senv : StructEnv) (hG : DomKeepF h) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) {dm : Lean.Expr} (hd : st.dom = some dm) :
    DK h dm (chainStep senv env e st) := by
  revert hd
  unfold chainStep
  split
  · intro hd
    refine dk_bindO (dk_cConv hG hd) ?_
    rintro ⟨v', st1⟩ d1 (h1 : st1.dom = some d1)
    exact dk_okO (domRel_of h1)
  · intro hd
    refine dk_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → DomRel dm b := by
      intro a b he
      subst he
      exact dk_cConv hG hd (a, b) hr
    revert hr'
    split
    · intro hr'
      obtain ⟨d1, hd1, rel1⟩ := hr' _ _ rfl
      refine dk_ite ?_ dk_failO
      refine dk_lift rel1 ?_
      refine dk_bindO (dk_cChain hG hd1) ?_
      rintro ⟨ws, v, st2⟩ d2 (h2 : st2.dom = some d2)
      exact dk_okO (domRel_of h2)
    · intro _
      exact dk_failO
  · intro hd
    split
    · exact dk_cChain hG hd
    · refine dk_ite ?_ ?_
      · refine dk_bindO (dk_cLoopRoot hG hd) ?_
        rintro ⟨mv, st1⟩ d1 (h1 : st1.dom = some d1)
        exact dk_cChain hG h1
      · split
        · exact dk_cChain hG hd
        · split
          · exact dk_cChain hG hd
          · refine dk_bindO (dk_cConv hG hd) ?_
            rintro ⟨v', st1⟩ d1 (h1 : st1.dom = some d1)
            r5pair (refine dk_cChain hG ?_; exact h1)
  · intro _
    exact dk_failO

theorem loopBody_dk (hG : DomKeepF h) (base : Nat) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) {dm : Lean.Expr} (hd : st.dom = some dm) :
    DK h dm (loopBodyStep base env e st) := by
  cases e
  case letE nm ty v b nd =>
    refine dk_bindO (dk_cConv hG hd) ?_
    rintro ⟨v', st1⟩ d1 (h1 : st1.dom = some d1)
    r5pair (refine dk_cLoopBody hG ?_; exact h1)
  all_goals
    unfold loopBodyStep
    try dsimp only
    refine dk_optK ?_
    intro regs _
    refine dk_bindO (dk_foldO (loopNext_dk hG _ _) _ _ _ ?_) ?_
    · exact hd
    rintro ⟨ws, st1⟩ d1 (h1 : st1.dom = some d1)
    exact dk_okO (domRel_of h1)

theorem loopRoot_dk (hE : EqvAtom) (senv : StructEnv) (hG : DomKeepF h) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) {dm : Lean.Expr} (hd : st.dom = some dm) :
    DK h dm (loopRootStep senv env e st) := by
  unfold loopRootStep
  split
  · refine dk_ite dk_failO ?_
    refine dk_optK ?_
    intro regs _
    refine dk_ite dk_failO ?_
    refine dk_optK ?_
    intro kinds hk
    refine dk_optK ?_
    intro inits hi
    refine dk_bindO (dk_cConv hG hd) ?_
    rintro ⟨dom', st1⟩ d1 (h1 : st1.dom = some d1)
    refine dk_domGuard h1 ?_
    intro hg
    refine dk_bind ?_
    intro shared hsh
    rcases shared with _ | ⟨b0, st2⟩
    · refine dk_lift (domKeepF_write hE hg) ?_
      dsimp only
      refine dk_bindO (dk_cLoopBody hG ?_) ?_
      · rfl
      rintro st3 d3 (h3 : st3.dom = some d3)
      exact dk_okO (domRel_of h3)
    · exact dk_okO (dk_findSomeO (loopProbe_dk hG _ _ _ _ h1) _ (b0, st2) hsh)
  · exact dk_failO

end Arms

theorem step_dk (hE : EqvAtom) (senv : StructEnv) {h : Hs} (hG : DomKeepF h) :
    DomKeepF (fun c => (step senv c).run h) := by
  intro c v hv dm hd
  cases c with
  | conv env d e st => exact conv_dk hE senv hG env d e st hd v hv
  | nested env dom αs initsE body st => exact nested_dk hE senv hG env dom αs initsE body st hd v hv
  | inst env c org kinds res args st => exact inst_dk hG env c org kinds res args st hd v hv
  | instS env c kinds ty args st => exact instS_dk senv hG env c kinds ty args st hd v hv
  | chain env e st => exact chain_dk senv hG env e st hd v hv
  | loopBody base env e st => exact loopBody_dk hG base env e st hd v hv
  | loopRoot env e st => exact loopRoot_dk hE senv hG env e st hd v hv

theorem readF_domKeepF (hE : EqvAtom) (senv : StructEnv) (n : Nat) : DomKeepF (readF senv n) := by
  induction n with
  | zero =>
    intro c v hv
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | succ n ih => exact step_dk hE senv ih

end Tools.ShippingGen5ReaderTrace
