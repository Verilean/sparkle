import Tools.ShippingLetsReaderInvBase

/-! # Unit LC3: the joint induction invariant of the reader twin (NoLetAlias + placeholder range)

BUILT: UNBUILT (written, first build pending). No `sorry`, no axiom, no `native_decide`.

SCOPE. A property of the FUEL TWIN (`readF`, `Tools/ShippingReaderFuelDefs.lean`) only, by induction on the
fuel exactly as `Tools/ShippingReaderFuelR1.lean` (arm by arm). It is NOT a theorem about the `partial`
readers `machConv` / `machChain` / `machLoopBody`: that link (the twin's results are the real reader's) is
the named OPEN hypothesis `TwinCover` below (O1 coverage) together with `OldEq` (O2, in
`Tools/ShippingReaderFuelOldEq.lean`).

## The invariant (one simultaneous induction, over the seven mutually recursive bodies)

Input side (`Pre`): the state satisfies `RdOk`; the environment's converted values are in range for the
state's `let` table (`EnvOk`); the expressions handed to the reader mention no `_machLet` placeholder
(`LetOk 0`, `LetFree`).
Output side (`Post`): the output state `Adv`-ances the input (`RdOk` again, the table did not shrink), and the
returned expression (`LetOk` at the OUTPUT table's size) is in range.
`RdOk st` = (i) `NoLetAlias st.lets` AND (ii) the expressions the state keeps (nested machines' results,
the domain) are in range of `st.lets.size`.

The two halves are carried together because they feed each other: the `NoLetAlias` of `machBindLetAlias`
needs the RANGE of the converted value (`alias_premise`), and the range of what a nested probe / the
domain returns needs the state invariant.

PROVED here: `readF_good` (every fuel), the per-call corollaries, and the Alias premise at the
`machLoopBody` call site (`loopBody_alias_premise`).
PREMISES (named hypotheses, not axioms): `PureFacts senv` (`Tools/ShippingLetsReaderInvBase.lean`) — facts
about `rootFloat` (`partial`), `liftLooseBVars`, `instantiate1` (extern) and about total pattern-extractor
functions; `TwinCover` (O1); the input condition `LetOk 0 e`.
OPEN (not proved): the loose-bvar condition on `let` values (`machClose_bvar` only bounds the root bvar);
the Expr → typed `letFields` / `quote` link; fuel → real reader (`TwinCover`, `OldEq`). -/
namespace Tools.ShippingLetsReaderInv
open Lean Sparkle.Compiler.Elab
open Tools.ShippingLetsAliasInv Tools.ShippingReaderFuel Tools.ShippingReaderFuelR1
open Tools.ShippingReaderLenOk

/-! ## Hoare-style combinators with an arbitrary postcondition -/

/-- Every OK result of `x` (against `h`) satisfies `P`. -/
abbrev SatP {α : Type} (h : Hs) (P : α → Prop) (x : BM (Option α)) : Prop :=
  ∀ a, x.run h = some (some a) → P a

section Comb
variable {h : Hs} {α β : Type}

theorem satp_pure {P : α → Prop} {o : Option α} (ho : ∀ a, o = some a → P a) :
    SatP h P (FM.pure o) := by
  intro a ha
  rw [run_pure] at ha
  exact ho a (Option.some.inj ha)

theorem satp_okO {P : α → Prop} {a : α} (ha : P a) : SatP h P (okO a) :=
  satp_pure fun b hb => by
    injection hb with hb1
    subst hb1
    exact ha

theorem satp_failO {P : α → Prop} : SatP h P (failO : BM (Option α)) :=
  satp_pure fun b hb => by cases hb

theorem satp_optK {P : α → Prop} {o : Option β} {f : β → BM (Option α)}
    (hf : ∀ b, o = some b → SatP h P (f b)) : SatP h P (optK o f) := by
  cases o with
  | none => exact satp_failO
  | some b => exact hf b rfl

theorem satp_bindO {P : α → Prop} {Q : β → Prop} {x : BM (Option β)} {f : β → BM (Option α)}
    (hx : SatP h Q x) (hf : ∀ b, Q b → SatP h P (f b)) : SatP h P (bindO x f) := by
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b => exact hf b (hx b ho) a ha

theorem satp_bind {P : α → Prop} {x : BM β} {f : β → BM (Option α)}
    (hf : ∀ r, x.run h = some r → SatP h P (f r)) : SatP h P (FM.bind x f) := by
  intro a ha
  rw [run_bind] at ha
  obtain ⟨r, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  exact hf r hr a ha

theorem satp_ite {P : α → Prop} {c : Prop} [Decidable c] {x y : BM (Option α)}
    (hx : SatP h P x) (hy : SatP h P y) : SatP h P (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx
  · rw [if_neg hc]
    exact hy

theorem satp_domGuard {P : α → Prop} {o : Option Lean.Expr} {dom' : Lean.Expr}
    {k : BM (Option α)} (hk : SatP h P k) : SatP h P (domGuard o dom' k) := by
  cases o with
  | none => exact hk
  | some d0 =>
    first
      | exact satp_ite satp_failO hk
      | (simp only [domGuard]; exact satp_ite satp_failO hk)

theorem satp_pure_ite {P : α → Prop} {c : Prop} [Decidable c] {a : α} (ha : P a) :
    SatP h P (FM.pure (if c then some a else none)) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact satp_okO ha
  · rw [if_neg hc]
    exact satp_failO

theorem satp_mono {P Q : α → Prop} {x : BM (Option α)} (hPQ : ∀ a, P a → Q a)
    (hx : SatP h P x) : SatP h Q x :=
  fun a ha => hPQ a (hx a ha)

end Comb

theorem satp_foldO {h : Hs} {σ α : Type} {P : σ → Prop} {f : σ → α → BM (Option σ)} :
    ∀ (l : List α) (s : σ), (∀ s a, a ∈ l → P s → SatP h P (f s a)) → P s →
      SatP h P (foldO f s l)
  | [], _, _, hs => satp_okO hs
  | a :: l, s, hf, hs =>
    satp_bindO (hf s a List.mem_cons_self hs) fun s' hs' =>
      satp_foldO l s' (fun s a ha => hf s a (List.mem_cons_of_mem _ ha)) hs'

theorem satp_findSomeO {h : Hs} {α β : Type} {P : β → Prop} {f : α → BM (Option β)} :
    ∀ (l : List α), (∀ a ∈ l, SatP h P (f a)) → SatP h P (findSomeO f l)
  | [], _ => satp_failO
  | a :: l, hf => by
    refine satp_bind ?_
    intro r hr
    cases r with
    | none => exact satp_findSomeO l (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    | some b => exact satp_okO (hf a List.mem_cons_self b hr)

/-! ## The invariant of a call table -/

/-- The input condition of a call. -/
def Pre : Call → Prop
  | Call.conv env _ e st => RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 e = true
  | Call.nested env dom _ _ body st =>
    RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 dom = true ∧ LetOk 0 body = true
  | Call.inst env _ _ _ _ args st =>
    RdOk st ∧ EnvOk st.lets.size env ∧ ∀ a ∈ args, LetOk 0 a = true
  | Call.instS env _ _ ty args st =>
    RdOk st ∧ EnvOk st.lets.size env ∧ (∀ a ∈ args, LetOk 0 a = true) ∧ LetOk 0 ty = true
  | Call.chain env e st => RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 e = true
  | Call.loopBody _ env e st => RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 e = true
  | Call.loopRoot env e st => RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 e = true

/-- Result of `machConv` / `machNested` / `machInstance` / `machInstanceS`. -/
abbrev ConvOut (s0 : MachRead) (p : Lean.Expr × MachRead) : Prop :=
  Adv s0 p.2 ∧ LetOk p.2.lets.size p.1 = true

/-- Result of `machChain`. -/
abbrev ChainOut (s0 : MachRead) (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead) : Prop :=
  Adv s0 p.2.2 ∧ LetOk p.2.2.lets.size p.2.1 = true

/-- Result of `machLoopBody`. -/
abbrev BodyOut (s0 : MachRead) (s : MachRead) : Prop := Adv s0 s

/-- Result of `machLoopRoot`. -/
abbrev RootOut (s0 : MachRead) (p : MachVal × MachRead) : Prop :=
  Adv s0 p.2 ∧ MvOk p.2.lets.size p.1

/-- The output condition of a call. -/
def Post : (c : Call) → c.Res → Prop
  | Call.conv _ _ _ st, p => ConvOut st (p : Lean.Expr × MachRead)
  | Call.nested _ _ _ _ _ st, p => ConvOut st (p : Lean.Expr × MachRead)
  | Call.inst _ _ _ _ _ _ st, p => ConvOut st (p : Lean.Expr × MachRead)
  | Call.instS _ _ _ _ _ st, p => ConvOut st (p : Lean.Expr × MachRead)
  | Call.chain _ _ st, p => ChainOut st (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  | Call.loopBody _ _ _ st, s => BodyOut st (s : MachRead)
  | Call.loopRoot _ _ st, p => RootOut st (p : MachVal × MachRead)

/-- A call table that keeps the joint invariant. -/
def Good (h : Hs) : Prop :=
  ∀ c, Pre c → ∀ v, h c = some (some v) → Post c v

theorem convOut_trans {s0 s1 : MachRead} (h : Adv s0 s1) {p : Lean.Expr × MachRead}
    (hp : ConvOut s1 p) : ConvOut s0 p := ⟨adv_trans h hp.1, hp.2⟩

theorem chainOut_trans {s0 s1 : MachRead} (h : Adv s0 s1)
    {p : List (Nat × Lean.Expr) × Lean.Expr × MachRead} (hp : ChainOut s1 p) : ChainOut s0 p :=
  ⟨adv_trans h hp.1, hp.2⟩

section Out
variable {h : Hs}

theorem sat_cConv (hG : Good h) {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    (hr : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true) :
    SatP h (ConvOut st) (cConv env d e st) :=
  fun p hp => hG (Call.conv env d e st)
    (show RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 e = true from ⟨hr, hE, hl⟩) p hp

theorem sat_cNested (hG : Good h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} (hr : RdOk st) (hE : EnvOk st.lets.size env) (hd : LetOk 0 dom = true)
    (hb : LetOk 0 body = true) : SatP h (ConvOut st) (cNested env dom αs initsE body st) :=
  fun p hp => hG (Call.nested env dom αs initsE body st)
    (show RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 dom = true ∧ LetOk 0 body = true from
      ⟨hr, hE, hd, hb⟩) p hp

theorem sat_cInst (hG : Good h) {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} {st : MachRead}
    (hr : RdOk st) (hE : EnvOk st.lets.size env) (ha : ∀ a ∈ args, LetOk 0 a = true) :
    SatP h (ConvOut st) (cInst env c org kinds res args st) :=
  fun p hp => hG (Call.inst env c org kinds res args st)
    (show RdOk st ∧ EnvOk st.lets.size env ∧ ∀ a ∈ args, LetOk 0 a = true from ⟨hr, hE, ha⟩) p hp

theorem sat_cInstS (hG : Good h) {env : List MachVal} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead}
    (hr : RdOk st) (hE : EnvOk st.lets.size env) (ha : ∀ a ∈ args, LetOk 0 a = true)
    (ht : LetOk 0 ty = true) : SatP h (ConvOut st) (cInstS env c kinds ty args st) :=
  fun p hp => hG (Call.instS env c kinds ty args st)
    (show RdOk st ∧ EnvOk st.lets.size env ∧ (∀ a ∈ args, LetOk 0 a = true) ∧ LetOk 0 ty = true from
      ⟨hr, hE, ha, ht⟩) p hp

theorem sat_cChain (hG : Good h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hr : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true) :
    SatP h (ChainOut st) (cChain env e st) :=
  fun p hp => hG (Call.chain env e st)
    (show RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 e = true from ⟨hr, hE, hl⟩) p hp

theorem sat_cLoopBody (hG : Good h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} (hr : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true) :
    SatP h (BodyOut st) (cLoopBody base env e st) :=
  fun p hp => hG (Call.loopBody base env e st)
    (show RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 e = true from ⟨hr, hE, hl⟩) p hp

theorem sat_cLoopRoot (hG : Good h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hr : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true) :
    SatP h (RootOut st) (cLoopRoot env e st) :=
  fun p hp => hG (Call.loopRoot env e st)
    (show RdOk st ∧ EnvOk st.lets.size env ∧ LetOk 0 e = true from ⟨hr, hE, hl⟩) p hp

end Out

/-! ## Pure fragments -/

theorem ok_mapM {α : Type} {n : Nat} {f : α → Option Lean.Expr}
    (hf : ∀ a t, f a = some t → LetOk n t = true) :
    ∀ (l : List α) (ts : List Lean.Expr), l.mapM f = some ts → ∀ t ∈ ts, LetOk n t = true
  | [], ts, h, t, ht => by
    simp [List.mapM_nil] at h
    subst h
    simp at ht
  | a :: l, ts, h, t, ht => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    have h' : b :: bs = ts := Option.some.inj h
    subst h'
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hf a _ hb
    · exact ok_mapM hf l bs hbs t ht

theorem bundleSlots_ok {n : Nat} {dom : Lean.Expr} (hd : LetOk n dom = true) (is : List Nat) :
    ∀ (ts : List Lean.Expr) (r : Lean.Expr × Lean.Expr),
      (∀ t ∈ ts, LetOk n t = true) → bundleSlots dom is ts = some r →
        LetOk n r.1 = true ∧ LetOk n r.2 = true := by
  induction is with
  | nil => intro ts r _ h; simp [bundleSlots] at h
  | cons i is ih =>
    intro ts r ht h
    cases ts with
    | nil => simp [bundleSlots] at h
    | cons t ts =>
      cases is with
      | nil =>
        cases ts with
        | nil =>
          simp [bundleSlots] at h
          subst h
          exact ⟨letOk_slot _ _, ht t (by simp)⟩
        | cons t' ts' => simp [bundleSlots] at h
      | cons j is' =>
        simp only [bundleSlots] at h
        obtain ⟨⟨rest, restT⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
        have ihh := ih ts (rest, restT) (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hb
        injection h with h
        subst h
        have h1 : LetOk n t = true := ht t List.mem_cons_self
        have h2 : LetOk n rest = true := ihh.1
        have h3 : LetOk n restT = true := ihh.2
        refine ⟨?_, ?_⟩ <;>
          simp [LetOk, mkApp5, mkApp4, mkApp2, mkAppB, mkApp, letOk_slot, hd, h1, h2, h3]

theorem convBvar_ok {env : List MachVal} {d j : Nat} {st : MachRead} {r : Lean.Expr × MachRead}
    (hdm : ∀ d, st.dom = some d → LetOk st.lets.size d = true)
    (hE : EnvOk st.lets.size env) (h : convBvar env d j st = some r) :
    r.2 = st ∧ LetOk st.lets.size r.1 = true := by
  unfold convBvar at h
  split at h
  · injection h with h
    subst h
    exact ⟨rfl, rfl⟩
  · split at h
    · rename_i v hv
      injection h with h
      subst h
      exact ⟨rfl, hE v (List.mem_of_getElem? hv)⟩
    · rename_i b hv
      injection h with h
      subst h
      exact ⟨rfl, letOk_slot _ _⟩
    · rename_i b n hn hv
      try simp only [Option.bind_eq_bind] at h
      obtain ⟨dom, hdom, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tys, htys, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨e, t⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
      injection h with h
      subst h
      refine ⟨rfl, ?_⟩
      have htys' := ok_mapM (n := st.lets.size) (f := _) ?_ _ _ htys
      · exact (bundleSlots_ok (hdm dom hdom) _ tys (e, t) htys' hb).1
      · intro i t ht
        obtain ⟨k, hk, ht⟩ := Option.bind_eq_some_iff.mp ht
        cases k with
        | bits w =>
          injection ht with ht
          subst ht
          simp [LetOk, mkApp, letOk_natLit]
        | bool =>
          injection ht with ht
          subst ht
          simp [LetOk]
        | domain => cases ht
    · cases h
    · rename_i hv
      injection h with h
      subst h
      exact ⟨rfl, letOk_in _ _⟩

theorem instRes_ok {senv : StructEnv} (F : PureFacts senv) {n : Nat} :
    ∀ (args : List Lean.Expr) (ty r : Lean.Expr), LetOk n ty = true →
      (∀ a ∈ args, LetOk n a = true) → instRes ty args = some r → LetOk n r = true
  | [], ty, r, ht, _, h => by
    simp only [instRes, Option.some.injEq] at h
    subst h
    exact ht
  | a :: as, ty, r, ht, ha, h => by
    cases ty with
    | forallE nm t b bi =>
      simp only [instRes] at h
      simp only [LetOk, Bool.and_eq_true] at ht
      exact instRes_ok F as _ r (F.inst1 n b a ht.2 (ha a List.mem_cons_self))
        (fun x hx => ha x (List.mem_cons_of_mem _ hx)) h
    | _ => simp [instRes] at h

theorem instEntry_adv {s0 st st' : MachRead} {res : MixedGateBinder} (hs : Adv s0 st)
    (h : instEntry res st = some st') : Adv s0 st' := by
  cases res with
  | bits w =>
    have h' : some st = some st' := h
    injection h' with h1
    subst h1
    exact hs
  | bool =>
    have h' : some { st with instStruct := true } = some st' := h
    injection h' with h1
    subst h1
    exact adv_congr hs (by rfl) (by rfl) (by rfl)
  | domain =>
    have h' : (none : Option MachRead) = some st' := h
    cases h'

theorem letIndex_facts (nm : Name) (k : MixedGateBinder) (v' : Lean.Expr) (lets : MachLets)
    (H : NoLetAlias lets) (j : Nat) (lets' : MachLets) (h : machLetIndex nm k v' lets = (j, lets')) :
    NoLetAlias lets' ∧ lets.size ≤ lets'.size := by
  have h1 := machLetIndex_noAlias (nm := nm) (k := k) (v' := v') H
  have h2 := machLetIndex_size (nm := nm) (k := k) (v' := v') (lets := lets)
  rw [h] at h1 h2
  exact ⟨h1, h2⟩

section Folds
variable {h : Hs}

/-- `machInstance`'s `foldlM` function (one argument). -/
theorem instArg_sat (hG : Good h) (env : List MachVal) (k : Nat) {s0 : MachRead}
    (hE : EnvOk s0.lets.size env) (args : List Lean.Expr)
    (hargs : ∀ x ∈ args, LetOk 0 x = true) (kinds : List MixedGateBinder) :
    ∀ s a, a ∈ kinds.zip args → Adv s0 s.2 →
      SatP h (fun p : List Nat × MachRead => Adv s0 p.2) (instArg env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ hmem (hA : Adv s0 st)
  have harg : LetOk 0 arg = true := hargs arg (List.of_mem_zip hmem).2
  refine satp_bindO (sat_cConv hG hA.1 (envOk_mono hA.2 hE) harg) ?_
  rintro ⟨v', st1⟩ ⟨h1, hv'⟩
  have h1' : Adv st st1 := h1
  have hv'' : LetOk st1.lets.size v' = true := hv'
  have hA1 : Adv s0 st1 := adv_trans hA h1'
  refine satp_pure ?_
  intro r hr
  cases kind with
  | domain =>
    try dsimp only at hr
    split at hr
    · split at hr
      · cases hr
      · injection hr with hr
        subst hr
        exact hA1
    · injection hr with hr
      subst hr
      exact adv_dom hA1 (by rfl) (by rfl) (by rfl) hv''
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact adv_lets hA1 (machLetIndex_noAlias hA1.1.1) machLetIndex_size (by rfl) (by rfl)
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact adv_lets hA1 (machLetIndex_noAlias hA1.1.1) machLetIndex_size (by rfl) (by rfl)

/-- `machInstanceS`'s first `foldlM` function (one argument). -/
theorem instSArg_sat (hG : Good h) (env : List MachVal) {s0 : MachRead}
    (hE : EnvOk s0.lets.size env) (args : List Lean.Expr)
    (hargs : ∀ x ∈ args, LetOk 0 x = true) (kinds : List MixedGateBinder) :
    ∀ s a, a ∈ kinds.zip args → Adv s0 s.2 →
      SatP h (fun p : List Nat × MachRead => Adv s0 p.2) (instSArg env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ hmem (hA : Adv s0 st)
  have harg : LetOk 0 arg = true := hargs arg (List.of_mem_zip hmem).2
  refine satp_bindO (sat_cConv hG hA.1 (envOk_mono hA.2 hE) harg) ?_
  rintro ⟨v', st1⟩ ⟨h1, hv'⟩
  have h1' : Adv st st1 := h1
  have hv'' : LetOk st1.lets.size v' = true := hv'
  have hA1 : Adv s0 st1 := adv_trans hA h1'
  refine satp_pure ?_
  intro r hr
  cases kind with
  | domain =>
    try dsimp only at hr
    split at hr
    · split at hr
      · cases hr
      · injection hr with hr
        subst hr
        exact hA1
    · injection hr with hr
      subst hr
      exact adv_dom hA1 (by rfl) (by rfl) (by rfl) hv''
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact adv_lets hA1 (machLetIndex_noAlias hA1.1.1) machLetIndex_size (by rfl) (by rfl)
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact adv_lets hA1 (machLetIndex_noAlias hA1.1.1) machLetIndex_size (by rfl) (by rfl)

/-- `machInstanceS`'s second `foldlM` function (one structure parameter). -/
theorem instSParam_sat (hG : Good h) (env : List MachVal) {s0 : MachRead}
    (hE : EnvOk s0.lets.size env) (ps0 : List Lean.Expr)
    (hps0 : ∀ q ∈ ps0, LetOk 0 q = true) :
    ∀ s a, a ∈ ps0 → (Adv s0 s.2 ∧ ∀ q ∈ s.1, LetOk s.2.lets.size q = true) →
      SatP h (fun p : List Lean.Expr × MachRead =>
        Adv s0 p.2 ∧ ∀ q ∈ p.1, LetOk p.2.lets.size q = true) (instSParam env s a) := by
  rintro ⟨ps, st⟩ p hmem ⟨(hA : Adv s0 st), (hps : ∀ q ∈ ps, LetOk st.lets.size q = true)⟩
  refine satp_bindO (sat_cConv hG hA.1 (envOk_mono hA.2 hE) (hps0 p hmem)) ?_
  rintro ⟨p', st1⟩ ⟨h1, hp'⟩
  have h1' : Adv st st1 := h1
  have hp'' : LetOk st1.lets.size p' = true := hp'
  refine satp_okO ⟨adv_trans hA h1', ?_⟩
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact letOk_mono h1'.2 _ (hps q hq)
  · rw [List.mem_singleton.mp hq]
    exact hp''

/-- `machLoopBody`'s `foldlM` function (one register's next-value). -/
theorem loopNext_sat (hG : Good h) (env : List MachVal) (base : Nat) {s0 : MachRead}
    (hE : EnvOk s0.lets.size env) (regs : List (Lean.Expr × Lean.Expr × Lean.Expr))
    (hregs : ∀ r ∈ regs, LetOk 0 r.2.2 = true) :
    ∀ s a, a ∈ regs → Adv s0 s.2 →
      SatP h (fun p : List (Nat × Lean.Expr) × MachRead => Adv s0 p.2) (loopNext env base s a) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩ hmem (hA : Adv s0 st)
  refine satp_bindO (sat_cConv hG hA.1 (envOk_mono hA.2 hE) (hregs _ hmem)) ?_
  rintro ⟨nx', st1⟩ ⟨h1, _⟩
  have h1' : Adv st st1 := h1
  exact satp_okO (adv_trans hA h1')

/-- `machNested`'s sharing probe. -/
theorem nestedProbe_sat (hG : Good h) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st1 : MachRead) (hr1 : RdOk st1) (hE : EnvOk st1.lets.size env)
    (hb : LetOk 0 body = true) :
    ∀ a, a ∈ st1.nested.toList →
      SatP h (ConvOut st1) (nestedProbe env dom' αs initsE body st1 a) := by
  rintro ⟨base, d, a, ini, ws, v⟩ hmem
  have hv : LetOk st1.lets.size v = true := hr1.2.1 _ hmem
  refine satp_ite ?_ satp_failO
  refine satp_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact satp_failO
  · have hc : ChainOut st1 (ws', v', st') :=
      sat_cChain hG hr1 (envOk_cons hE (fun w hw => by cases hw)) hb (ws', v', st') hr
    refine satp_pure_ite ?_
    exact ⟨hc.1, letOk_mono hc.1.2 _ hv⟩

/-- `machLoopRoot`'s sharing probe. -/
theorem loopProbe_sat (hG : Good h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st1 : MachRead) (hr1 : RdOk st1) (hE : EnvOk st1.lets.size env)
    (hb : LetOk 0 body = true) :
    ∀ a, SatP h (fun p : Nat × MachRead => Adv st1 p.2) (loopProbe env body n st1 a) := by
  rintro ⟨b0, n0, ws0⟩
  refine satp_ite satp_failO ?_
  refine satp_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact satp_failO
  · have hz : Adv st1 { st1 with ws := #[] } := adv_congr (adv_refl hr1) (by rfl) (by rfl) (by rfl)
    have hc : Adv { st1 with ws := #[] } st' :=
      sat_cLoopBody hG hz.1 (envOk_cons hE (fun w hw => by cases hw)) hb st' hr
    refine satp_pure_ite ?_
    exact adv_congr (adv_trans hz hc) (by rfl) (by rfl) (by rfl)

end Folds

end Tools.ShippingLetsReaderInv
