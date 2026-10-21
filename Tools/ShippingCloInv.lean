import Tools.ShippingCloBundle
import Tools.ShippingLetsReaderInv

/-! # Unit LCQ2: the closedness invariant of the reader twin (`Clo`): no loose `bvar` in any `let` value

BUILT: see the BUILD LOG at the end of this header.  No `sorry`, no axiom, no `native_decide`.

## What is proved

For the FUEL TWIN `readF` (not for the `partial` readers `machConv` / ... themselves: the twin → real link is the
OPEN `TwinCoverAt`), every SUCCESSFUL answer of every call, at every fuel, keeps

* `CloSt st`: every `let` value, every saved nested-machine result and the domain is `Clo 0` (no loose bound variable);
* the returned expression of a `machConv` call at depth `d` is `Clo d`, of every other expression-returning call `Clo 0`,
  and a returned `MachVal.val` is `Clo 0`,

from the entry condition `CloSt st ∧ EnvClo env` (every `MachVal.val` of the environment is `Clo 0`); the empty state
satisfies `CloSt` (`cloSt_init`).

## Why the invariant is `Clo` and not only "the value is not a bare `bvar`"

What the typed bridge needs is `NoLetBvar`: no `let` value is itself `.bvar b`.  That property alone is NOT inductive: the
reader returns `bundleIota (machProjIota … (f' a'))`, which can return a COMPONENT (a constructor argument / a
`getAppArgs` element) of an earlier result, so a bare `bvar` could surface from the inside of a compound result.  The
minimal property that is preserved by all arms is therefore "no loose bound variable at all" (`Clo`).  The converse is
direct: `Clo 0 e → e ≠ .bvar b` (`clo_ne_bvar`), hence `LetsClo lets → NoLetBvar lets`.

## Entry conditions, premises

* NO condition on the INPUT expressions: an input `bvar` is either below the binders crossed (kept), an environment value
  (itself a reader result, `Clo 0` by `EnvClo`), a state/bundle slot, or outside the environment (replaced by the
  `machIn` placeholder, an `fvar`).  Types are read like terms (`.lam` / `.forallE` arms) and are covered by the
  same `Clo d` post-condition.
* The only properties of the non-`partial` helpers used: `bundleIota_clo` and `projIota_clo` (PROVED, copies of LC4a / LC3
  proofs), the let-table helpers (`Tools/ShippingCloBase.lean`, PROVED).  `rootFloat`, `liftLooseBVars`, `instantiate1`
  act only on INPUT subterms that the reader then reads again, so no premise about them is used.
* NOT a statement about the real `partial` readers; see `TwinCoverAt` (OPEN).  Also NOT proved: that the START environment
  of a shipped declaration is `EnvClo` (for the wrapper this is the empty/`unit` environment; see
  `Tools/Prototype/ReaderClosed.lean`).

## BUILD LOG
c1 (Base) exit 1, c2 (Base) exit 0, c3 (Bundle) exit 0, (Inv) see below. -/
namespace Tools.ShippingCloInv
open Lean Sparkle.Compiler.Elab
open Tools.ShippingLetsAliasInv Tools.ShippingReaderFuel Tools.ShippingReaderLenOk
open Tools.ShippingLetsReaderInv (SatP satp_pure satp_okO satp_failO satp_optK satp_bindO satp_bind
  satp_ite satp_domGuard satp_pure_ite satp_mono satp_foldO satp_findSomeO)

theorem clo_ne_bvar {e : Lean.Expr} (h : Clo 0 e = true) (b : Nat) : e ≠ .bvar b := by
  intro he
  subst he
  simp [Clo] at h

/-! ## The invariant of a call table -/

/-- The input condition of a call. -/
def CPre : Call → Prop
  | Call.conv env _ _ st => CloSt st ∧ EnvClo env
  | Call.nested env _ _ _ _ st => CloSt st ∧ EnvClo env
  | Call.inst env _ _ _ _ _ st => CloSt st ∧ EnvClo env
  | Call.instS env _ _ _ _ st => CloSt st ∧ EnvClo env
  | Call.chain env _ st => CloSt st ∧ EnvClo env
  | Call.loopBody _ env _ st => CloSt st ∧ EnvClo env
  | Call.loopRoot env _ st => CloSt st ∧ EnvClo env

/-- Result of `machConv` at depth `d` (and, with `d = 0`, of `machNested` / `machInstance` / `machInstanceS`). -/
abbrev ConvC (d : Nat) (p : Lean.Expr × MachRead) : Prop := CloSt p.2 ∧ Clo d p.1 = true

abbrev ChainC (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead) : Prop :=
  CloSt p.2.2 ∧ Clo 0 p.2.1 = true

abbrev RootC (p : MachVal × MachRead) : Prop := CloSt p.2 ∧ MvClo p.1

/-- The output condition of a call. -/
def CPost : (c : Call) → c.Res → Prop
  | Call.conv _ d _ _, p => ConvC d (p : Lean.Expr × MachRead)
  | Call.nested _ _ _ _ _ _, p => ConvC 0 (p : Lean.Expr × MachRead)
  | Call.inst _ _ _ _ _ _ _, p => ConvC 0 (p : Lean.Expr × MachRead)
  | Call.instS _ _ _ _ _ _, p => ConvC 0 (p : Lean.Expr × MachRead)
  | Call.chain _ _ _, p => ChainC (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  | Call.loopBody _ _ _ _, s => CloSt (s : MachRead)
  | Call.loopRoot _ _ _, p => RootC (p : MachVal × MachRead)

/-- A call table that keeps the invariant. -/
def CGood (h : Hs) : Prop :=
  ∀ c, CPre c → ∀ v, h c = some (some v) → CPost c v

theorem convC_mono {d : Nat} {p : Lean.Expr × MachRead} (h : ConvC 0 p) : ConvC d p :=
  ⟨h.1, clo_zero h.2⟩

section Out
variable {h : Hs}

theorem csat_cConv (hG : CGood h) {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    (hr : CloSt st) (hE : EnvClo env) : SatP h (ConvC d) (cConv env d e st) :=
  fun p hp => hG (Call.conv env d e st) ⟨hr, hE⟩ p hp

theorem csat_cNested (hG : CGood h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} (hr : CloSt st) (hE : EnvClo env) :
    SatP h (ConvC 0) (cNested env dom αs initsE body st) :=
  fun p hp => hG (Call.nested env dom αs initsE body st) ⟨hr, hE⟩ p hp

theorem csat_cInst (hG : CGood h) {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} {st : MachRead}
    (hr : CloSt st) (hE : EnvClo env) : SatP h (ConvC 0) (cInst env c org kinds res args st) :=
  fun p hp => hG (Call.inst env c org kinds res args st) ⟨hr, hE⟩ p hp

theorem csat_cInstS (hG : CGood h) {env : List MachVal} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead}
    (hr : CloSt st) (hE : EnvClo env) : SatP h (ConvC 0) (cInstS env c kinds ty args st) :=
  fun p hp => hG (Call.instS env c kinds ty args st) ⟨hr, hE⟩ p hp

theorem csat_cChain (hG : CGood h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hr : CloSt st) (hE : EnvClo env) : SatP h ChainC (cChain env e st) :=
  fun p hp => hG (Call.chain env e st) ⟨hr, hE⟩ p hp

theorem csat_cLoopBody (hG : CGood h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} (hr : CloSt st) (hE : EnvClo env) :
    SatP h (fun s : MachRead => CloSt s) (cLoopBody base env e st) :=
  fun p hp => hG (Call.loopBody base env e st) ⟨hr, hE⟩ p hp

theorem csat_cLoopRoot (hG : CGood h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hr : CloSt st) (hE : EnvClo env) : SatP h RootC (cLoopRoot env e st) :=
  fun p hp => hG (Call.loopRoot env e st) ⟨hr, hE⟩ p hp

end Out

/-! ## Pure fragments -/

theorem clo_mapM {α : Type} {d : Nat} {f : α → Option Lean.Expr}
    (hf : ∀ a t, f a = some t → Clo d t = true) :
    ∀ (l : List α) (ts : List Lean.Expr), l.mapM f = some ts → ∀ t ∈ ts, Clo d t = true
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
    · exact clo_mapM hf l bs hbs t ht

theorem bundleSlots_clo {d : Nat} {dom : Lean.Expr} (hd : Clo d dom = true) (is : List Nat) :
    ∀ (ts : List Lean.Expr) (r : Lean.Expr × Lean.Expr),
      (∀ t ∈ ts, Clo d t = true) → bundleSlots dom is ts = some r →
        Clo d r.1 = true ∧ Clo d r.2 = true := by
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
          exact ⟨clo_slot _ _, ht t (by simp)⟩
        | cons t' ts' => simp [bundleSlots] at h
      | cons j is' =>
        simp only [bundleSlots] at h
        obtain ⟨⟨rest, restT⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
        have ihh := ih ts (rest, restT) (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hb
        injection h with h
        subst h
        have h1 : Clo d t = true := ht t List.mem_cons_self
        have h2 : Clo d rest = true := ihh.1
        have h3 : Clo d restT = true := ihh.2
        refine ⟨?_, ?_⟩ <;>
          simp [Clo, mkApp5, mkApp4, mkApp2, mkAppB, mkApp, clo_slot, hd, h1, h2, h3]

theorem convBvar_clo {env : List MachVal} {d j : Nat} {st : MachRead} {r : Lean.Expr × MachRead}
    (hdm : ∀ d, st.dom = some d → Clo 0 d = true)
    (hE : EnvClo env) (h : convBvar env d j st = some r) :
    r.2 = st ∧ Clo d r.1 = true := by
  unfold convBvar at h
  by_cases hjd : j < d
  · rw [if_pos hjd] at h
    injection h with h
    subst h
    exact ⟨rfl, by simp [Clo, hjd]⟩
  · rw [if_neg hjd] at h
    split at h
    · rename_i v hv
      injection h with h
      subst h
      exact ⟨rfl, clo_zero (hE v (List.mem_of_getElem? hv))⟩
    · rename_i b hv
      injection h with h
      subst h
      exact ⟨rfl, clo_slot _ _⟩
    · rename_i b n hn hv
      try simp only [Option.bind_eq_bind] at h
      obtain ⟨dom, hdom, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tys, htys, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨e, t⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
      injection h with h
      subst h
      refine ⟨rfl, ?_⟩
      have htys' := clo_mapM (d := d) (f := _) ?_ _ _ htys
      · exact (bundleSlots_clo (clo_zero (hdm dom hdom)) _ tys (e, t) htys' hb).1
      · intro i t ht
        obtain ⟨k, hk, ht⟩ := Option.bind_eq_some_iff.mp ht
        cases k with
        | bits w =>
          injection ht with ht
          subst ht
          simp [Clo, mkApp, clo_natLit]
        | bool =>
          injection ht with ht
          subst ht
          simp [Clo]
        | domain => cases ht
    · cases h
    · rename_i hv
      injection h with h
      subst h
      exact ⟨rfl, clo_in _ _⟩

theorem clo_ctorApp {d : Nat} (ctor : Name) (lvls : List Level) (params : List Lean.Expr)
    (hps : ∀ q ∈ params, Clo d q = true) (k len : Nat) :
    Clo d (mkAppN (.const ctor lvls) (params.toArray ++
      ((List.range len).map fun i => machInstOut (k + i)).toArray)) = true := by
  refine clo_mkAppN rfl ?_
  intro x hx
  rcases Array.mem_append.mp hx with hx | hx
  · exact hps x (Array.mem_toArray.mp hx)
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp (Array.mem_toArray.mp hx)
    exact clo_inst _ _

theorem clo_pair {d : Nat} {a b : Lean.Expr} (ha : Clo d a = true) (hb : Clo d b = true) :
    Clo d (.app a b) = true := by
  simp only [Clo, Bool.and_eq_true]
  exact ⟨ha, hb⟩

theorem instEntry_clo {st st' : MachRead} {res : MixedGateBinder} (hs : CloSt st)
    (h : instEntry res st = some st') : CloSt st' := by
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
    exact cloSt_congr hs (by rfl) (by rfl) (by rfl)
  | domain =>
    have h' : (none : Option MachRead) = some st' := h
    cases h'

/-! ## The folds and probes -/

section Folds
variable {h : Hs}

theorem instArg_sat (hG : CGood h) (env : List MachVal) (k : Nat) (hE : EnvClo env) :
    ∀ (s : List Nat × MachRead) (a : MixedGateBinder × Lean.Expr), CloSt s.2 →
      SatP h (fun p : List Nat × MachRead => CloSt p.2) (instArg env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hA : CloSt st)
  refine satp_bindO (csat_cConv hG hA hE) ?_
  rintro ⟨v', st1⟩ ⟨(h1 : CloSt st1), (hv' : Clo 0 v' = true)⟩
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
        exact h1
    · injection hr with hr
      subst hr
      exact cloSt_dom h1 (by rfl) (by rfl) (by rfl) hv'
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact cloSt_lets h1 (machLetIndex_clo h1.1 hv') (by rfl) (by rfl)
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact cloSt_lets h1 (machLetIndex_clo h1.1 hv') (by rfl) (by rfl)

theorem instSArg_sat (hG : CGood h) (env : List MachVal) (hE : EnvClo env) :
    ∀ (s : List Nat × MachRead) (a : MixedGateBinder × Lean.Expr), CloSt s.2 →
      SatP h (fun p : List Nat × MachRead => CloSt p.2) (instSArg env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hA : CloSt st)
  refine satp_bindO (csat_cConv hG hA hE) ?_
  rintro ⟨v', st1⟩ ⟨(h1 : CloSt st1), (hv' : Clo 0 v' = true)⟩
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
        exact h1
    · injection hr with hr
      subst hr
      exact cloSt_dom h1 (by rfl) (by rfl) (by rfl) hv'
  | bits w =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact cloSt_lets h1 (machLetIndex_clo h1.1 hv') (by rfl) (by rfl)
  | bool =>
    try dsimp only at hr
    injection hr with hr
    subst hr
    exact cloSt_lets h1 (machLetIndex_clo h1.1 hv') (by rfl) (by rfl)

theorem instSParam_sat (hG : CGood h) (env : List MachVal) (hE : EnvClo env) :
    ∀ (s : List Lean.Expr × MachRead) (a : Lean.Expr),
      (CloSt s.2 ∧ ∀ q ∈ s.1, Clo 0 q = true) →
      SatP h (fun p : List Lean.Expr × MachRead => CloSt p.2 ∧ ∀ q ∈ p.1, Clo 0 q = true)
        (instSParam env s a) := by
  rintro ⟨ps, st⟩ p ⟨(hA : CloSt st), (hps : ∀ q ∈ ps, Clo 0 q = true)⟩
  refine satp_bindO (csat_cConv hG hA hE) ?_
  rintro ⟨p', st1⟩ ⟨(h1 : CloSt st1), (hp' : Clo 0 p' = true)⟩
  refine satp_okO ⟨h1, ?_⟩
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hps q hq
  · rw [List.mem_singleton.mp hq]
    exact hp'

theorem loopNext_sat (hG : CGood h) (env : List MachVal) (base : Nat) (hE : EnvClo env) :
    ∀ (s : List (Nat × Lean.Expr) × MachRead) (a : Lean.Expr × Lean.Expr × Lean.Expr), CloSt s.2 →
      SatP h (fun p : List (Nat × Lean.Expr) × MachRead => CloSt p.2) (loopNext env base s a) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩ (hA : CloSt st)
  refine satp_bindO (csat_cConv hG hA hE) ?_
  rintro ⟨nx', st1⟩ ⟨(h1 : CloSt st1), _⟩
  exact satp_okO h1

theorem nestedProbe_sat (hG : CGood h) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st1 : MachRead) (hr1 : CloSt st1) (hE : EnvClo env) :
    ∀ a, a ∈ st1.nested.toList →
      SatP h (ConvC 0) (nestedProbe env dom' αs initsE body st1 a) := by
  rintro ⟨base, d, a, ini, ws, v⟩ hmem
  have hv : Clo 0 v = true := hr1.2.1 _ hmem
  refine satp_ite ?_ satp_failO
  refine satp_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact satp_failO
  · have hc : ChainC (ws', v', st') :=
      csat_cChain hG hr1 (envClo_cons hE (fun w hw => by cases hw)) (ws', v', st') hr
    refine satp_pure_ite ?_
    exact ⟨hc.1, hv⟩

theorem loopProbe_sat (hG : CGood h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st1 : MachRead) (hr1 : CloSt st1) (hE : EnvClo env) :
    ∀ a, SatP h (fun p : Nat × MachRead => CloSt p.2) (loopProbe env body n st1 a) := by
  rintro ⟨b0, n0, ws0⟩
  refine satp_ite satp_failO ?_
  refine satp_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact satp_failO
  · have hz : CloSt { st1 with ws := #[] } := cloSt_congr hr1 (by rfl) (by rfl) (by rfl)
    have hc : CloSt st' :=
      csat_cLoopBody hG hz (envClo_cons hE (fun w hw => by cases hw)) st' hr
    refine satp_pure_ite ?_
    exact cloSt_congr hc (by rfl) (by rfl) (by rfl)

end Folds

/-! ## The seven bodies -/

section Arms
variable {h : Hs}

/-- `machConv`'s `.app` arm. -/
theorem cconv_app_sat (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (d : Nat) (f a : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h (ConvC d) (convStep senv env d (.app f a) st) := by
  first
    | simp only [convStep]
    | (unfold convStep; dsimp only)
  split
  · -- a bare `Signal.register`
    rename_i dom α init x hreg
    refine satp_ite satp_failO ?_
    split
    · exact satp_okO ⟨hst, clo_slot _ _⟩
    · refine satp_optK ?_
      intro kind _
      refine satp_optK ?_
      intro initN _
      refine satp_bindO (csat_cConv hG hst hE) ?_
      rintro ⟨dom', st1⟩ ⟨(h1 : CloSt st1), (hd' : Clo 0 dom' = true)⟩
      refine satp_domGuard ?_
      refine satp_bindO (csat_cConv hG (cloSt_dom h1 (by rfl) (by rfl) (by rfl) hd') hE) ?_
      rintro ⟨x', st2⟩ ⟨(h2 : CloSt st2), hx'⟩
      refine satp_okO ⟨?_, clo_slot _ _⟩
      exact cloSt_congr h2 (by rfl) (by rfl) (by rfl)
  · split
    · -- a loop read
      exact satp_pure_ite ⟨hst, clo_slot _ _⟩
    · split
      · -- a nested machine
        exact satp_ite satp_failO (satp_mono (fun p hp => convC_mono hp) (csat_cNested hG hst hE))
      · split
        · -- an instance
          exact satp_ite satp_failO
            (satp_mono (fun p hp => convC_mono hp) (csat_cInst hG hst hE))
        · split
          · -- a structure instance
            exact satp_ite satp_failO
              (satp_mono (fun p hp => convC_mono hp) (csat_cInstS hG hst hE))
          · split
            · -- a memory
              refine satp_ite satp_failO (satp_bindO (csat_cInst hG hst hE) ?_)
              rintro ⟨v, st1⟩ ⟨(h1 : CloSt st1), (hv : Clo 0 v = true)⟩
              exact satp_okO ⟨cloSt_congr h1 (by rfl) (by rfl) (by rfl), clo_zero hv⟩
            · split
              · -- a state read
                exact satp_pure_ite ⟨hst, clo_slot _ _⟩
              · -- an application
                refine satp_bindO (csat_cConv hG hst hE) ?_
                rintro ⟨f', st1⟩ ⟨(h1 : CloSt st1), (hf' : Clo d f' = true)⟩
                refine satp_bindO (csat_cConv hG h1 hE) ?_
                rintro ⟨a', st2⟩ ⟨(h2 : CloSt st2), (ha' : Clo d a' = true)⟩
                exact satp_okO ⟨h2, bundleIota_clo _ _ (projIota_clo _ _ _ (clo_pair hf' ha'))⟩

/-- `machConv`'s `.letE` arm. -/
theorem cconv_letE_sat (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (d : Nat) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead) (hst : CloSt st)
    (hE : EnvClo env) :
    SatP h (ConvC d) (convStep senv env d (.letE nm ty v b nd) st) := by
  refine satp_ite satp_failO ?_
  split
  · exact satp_mono (fun p hp => convC_mono hp) (csat_cConv hG hst hE)
  · refine satp_ite ?_ ?_
    · refine satp_bindO (csat_cLoopRoot hG hst hE) ?_
      rintro ⟨mv, st1⟩ ⟨(h1 : CloSt st1), (hmv : MvClo mv)⟩
      have hEv : EnvClo (mv :: env) := envClo_cons hE (fun w hw => by subst hw; exact hmv)
      exact satp_mono (fun p hp => convC_mono hp) (csat_cConv hG h1 hEv)
    · split
      · exact satp_mono (fun p hp => convC_mono hp)
          (csat_cConv hG hst (envClo_cons hE (fun w hw => by cases hw)))
      · split
        · exact satp_mono (fun p hp => convC_mono hp)
            (csat_cConv hG hst (envClo_cons hE (fun w hw => by cases hw)))
        · refine satp_bindO (csat_cConv hG hst hE) ?_
          rintro ⟨v', st1⟩ ⟨(h1 : CloSt st1), (hv' : Clo 0 v' = true)⟩
          have hB := machBindLet_clo (nm := nm) (ty := ty) h1.1 hv'
          dsimp only
          generalize machBindLet nm ty v' st1.lets = bl at hB ⊢
          obtain ⟨x, lets'⟩ := bl
          have hA : CloSt { st1 with lets := lets' } := cloSt_lets h1 hB.1 (by rfl) (by rfl)
          have hEv : EnvClo (MachVal.val x :: env) :=
            envClo_cons hE (fun w hw => by injection hw with hw; subst hw; exact hB.2)
          show SatP h (ConvC d) (cConv (MachVal.val x :: env) 0 b { st1 with lets := lets' })
          exact satp_mono (fun p hp => convC_mono hp) (csat_cConv hG hA hEv)

/-- `machConv`. -/
theorem cconv_sat (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (d : Nat) (e : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h (ConvC d) (convStep senv env d e st) := by
  cases e
  case bvar j =>
    refine satp_pure ?_
    intro r hr
    obtain ⟨hs, hv⟩ := convBvar_clo hst.2.2 hE hr
    show CloSt r.2 ∧ Clo d r.1 = true
    rw [hs]
    exact ⟨hst, hv⟩
  case app f a => exact cconv_app_sat senv hG env d f a st hst hE
  case letE nm ty v b nd => exact cconv_letE_sat senv hG env d nm ty v b nd st hst hE
  case lam nm t b bi =>
    refine satp_bindO (csat_cConv hG hst hE) ?_
    rintro ⟨t', st1⟩ ⟨(h1 : CloSt st1), (ht' : Clo d t' = true)⟩
    refine satp_bindO (csat_cConv hG h1 hE) ?_
    rintro ⟨b', st2⟩ ⟨(h2 : CloSt st2), (hb' : Clo (d + 1) b' = true)⟩
    refine satp_okO ⟨h2, ?_⟩
    show Clo d (.lam nm t' b' bi) = true
    simp only [Clo, Bool.and_eq_true]
    exact ⟨ht', hb'⟩
  case forallE nm t b bi =>
    refine satp_bindO (csat_cConv hG hst hE) ?_
    rintro ⟨t', st1⟩ ⟨(h1 : CloSt st1), (ht' : Clo d t' = true)⟩
    refine satp_bindO (csat_cConv hG h1 hE) ?_
    rintro ⟨b', st2⟩ ⟨(h2 : CloSt st2), (hb' : Clo (d + 1) b' = true)⟩
    refine satp_okO ⟨h2, ?_⟩
    show Clo d (.forallE nm t' b' bi) = true
    simp only [Clo, Bool.and_eq_true]
    exact ⟨ht', hb'⟩
  all_goals first
    | (refine satp_okO ⟨hst, ?_⟩; rfl)
    | exact satp_failO

/-- `machNested`. -/
theorem cnested_sat (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h (ConvC 0) (nestedStep senv env dom αs initsE body st) := by
  refine satp_ite satp_failO ?_
  refine satp_bindO (csat_cConv hG hst hE) ?_
  rintro ⟨dom', st1⟩ ⟨(h1 : CloSt st1), (hd' : Clo 0 dom' = true)⟩
  refine satp_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · refine satp_optK ?_
    rintro ⟨base, st2⟩ hres
    obtain ⟨kinds, inits, _, _, _, hst2⟩ := machReserve_some hres
    subst hst2
    have h2 : CloSt (reserved st1 dom' body kinds inits) :=
      cloSt_dom h1 (by rfl) (by rfl) (by rfl) hd'
    refine satp_bindO (csat_cChain hG
      (cloSt_congr h2 (by rfl) (by rfl) (by rfl))
      (envClo_cons hE (fun w hw => by cases hw))) ?_
    rintro ⟨ws, v, st3⟩ ⟨(h3 : CloSt st3), (hv3 : Clo 0 v = true)⟩
    refine satp_okO ⟨?_, hv3⟩
    exact cloSt_nested (e := (base, dom', αs, initsE, ws, v)) h3 (by rfl) (by rfl) (by rfl) hv3
  · have := satp_findSomeO (P := ConvC 0) st1.nested.toList
      (fun a ha => nestedProbe_sat hG env dom' αs initsE body st1 h1 hE a ha) r hsh
    exact satp_okO this

/-- `machInstance`. -/
theorem cinst_sat (hG : CGood h) (env : List MachVal) (c : Name)
    (org : Sparkle.Compiler.MachInstOrigin.InstOrigin) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) (hst : CloSt st)
    (hE : EnvClo env) :
    SatP h (ConvC 0) (instStep env c org kinds res args st) := by
  refine satp_optK ?_
  intro st1 hst1
  have h1 : CloSt st1 := instEntry_clo hst hst1
  refine satp_bindO (satp_foldO (P := fun p : List Nat × MachRead => CloSt p.2)
    (kinds.zip args) ([], st1) ?_ h1) ?_
  · intro s a _ hs
    exact instArg_sat hG env st1.insts.size hE s a hs
  rintro ⟨js, st2⟩ (h2 : CloSt st2)
  refine satp_pure ?_
  intro r hr
  split at hr
  all_goals first
    | (injection hr with hq; subst hq; exact ⟨h2, clo_inst _ _⟩)
    | (injection hr with hq; subst hq
       exact ⟨cloSt_congr h2 (by rfl) (by rfl) (by rfl), clo_inst _ _⟩)

/-- `machInstanceS`. -/
theorem cinstS_sat (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr)
    (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h (ConvC 0) (instSStep senv env c kinds ty args st) := by
  refine satp_ite satp_failO ?_
  refine satp_optK ?_
  intro resTy hres
  refine satp_optK ?_
  intro r _
  obtain ⟨oc, fields⟩ := r
  cases oc with
  | none => exact satp_failO
  | some ctor =>
    refine satp_ite satp_failO ?_
    refine satp_bindO (satp_foldO (P := fun p : List Nat × MachRead => CloSt p.2)
      (kinds.zip args) ([], st) ?_ hst) ?_
    · intro s a _ hs
      exact instSArg_sat hG env hE s a hs
    rintro ⟨js, st1⟩ (h1 : CloSt st1)
    refine satp_bindO (satp_foldO
      (P := fun p : List Lean.Expr × MachRead => CloSt p.2 ∧ ∀ q ∈ p.1, Clo 0 q = true)
      resTy.getAppArgs.toList ([], st1) ?_ ⟨h1, by simp⟩) ?_
    · intro s a _ hs
      exact instSParam_sat hG env hE s a hs
    rintro ⟨params, st2⟩ ⟨(h2 : CloSt st2), (hps : ∀ q ∈ params, Clo 0 q = true)⟩
    try dsimp only
    split
    · exact satp_okO ⟨h2, clo_ctorApp _ _ params hps _ _⟩
    · exact satp_okO ⟨cloSt_congr h2 (by rfl) (by rfl) (by rfl), clo_ctorApp _ _ params hps _ _⟩

/-- `machChain`. -/
theorem cchain_sat (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h ChainC (chainStep senv env e st) := by
  unfold chainStep
  split
  · refine satp_bindO (csat_cConv hG hst hE) ?_
    rintro ⟨v', st1⟩ ⟨h1, hv'⟩
    exact satp_okO ⟨h1, hv'⟩
  · refine satp_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → ConvC 0 (a, b) := by
      intro a b he
      subst he
      exact csat_cConv hG hst hE (a, b) hr
    revert hr'
    split
    · intro hr'
      have h1 := hr' _ _ rfl
      have h1' : CloSt _ := h1.1
      refine satp_ite ?_ satp_failO
      refine satp_bindO (csat_cChain hG h1'
        (envClo_cons hE (fun w hw => by cases hw))) ?_
      rintro ⟨ws, v, st3⟩ ⟨h2, hv⟩
      exact satp_okO ⟨h2, hv⟩
    · intro _
      exact satp_failO
  · rename_i nm ty v b nd
    split
    · exact csat_cChain hG hst hE
    · refine satp_ite ?_ ?_
      · refine satp_bindO (csat_cLoopRoot hG hst hE) ?_
        rintro ⟨mv, st1⟩ ⟨(h1 : CloSt st1), (hmv : MvClo mv)⟩
        exact csat_cChain hG h1 (envClo_cons hE (fun w hw => by subst hw; exact hmv))
      · split
        · exact csat_cChain hG hst (envClo_cons hE (fun w hw => by cases hw))
        · split
          · exact csat_cChain hG hst (envClo_cons hE (fun w hw => by cases hw))
          · refine satp_bindO (csat_cConv hG hst hE) ?_
            rintro ⟨v', st1⟩ ⟨(h1 : CloSt st1), (hv' : Clo 0 v' = true)⟩
            have hB := machBindLet_clo (nm := nm) (ty := ty) h1.1 hv'
            dsimp only
            generalize machBindLet nm ty v' st1.lets = bl at hB ⊢
            obtain ⟨x, lets'⟩ := bl
            have hA : CloSt { st1 with lets := lets' } := cloSt_lets h1 hB.1 (by rfl) (by rfl)
            have hEv : EnvClo (MachVal.val x :: env) :=
              envClo_cons hE (fun w hw => by injection hw with hw; subst hw; exact hB.2)
            show SatP h ChainC (cChain (MachVal.val x :: env) b { st1 with lets := lets' })
            exact csat_cChain hG hA hEv
  · exact satp_failO

/-- `machLoopBody`. -/
theorem cloopBody_sat (senv : StructEnv) (hG : CGood h) (base : Nat)
    (env : List MachVal) (e : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h (fun s : MachRead => CloSt s) (loopBodyStep base env e st) := by
  cases e
  case letE nm ty v b nd =>
    refine satp_bindO (csat_cConv hG hst hE) ?_
    rintro ⟨v', st1⟩ ⟨(h1 : CloSt st1), (hv' : Clo 0 v' = true)⟩
    have hF := loopLet_clo (nm := nm) (ty := ty) h1.1 hv'
    dsimp only
    generalize (if machIsSlot v' then machBindLetNamed nm ty v' st1.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st1.lets
      else machBindLet nm ty v' st1.lets) = bl at hF ⊢
    obtain ⟨x, lets'⟩ := bl
    have hA : CloSt { st1 with lets := lets' } := cloSt_lets h1 hF.1 (by rfl) (by rfl)
    have hEv : EnvClo (MachVal.val x :: env) :=
      envClo_cons hE (fun w hw => by injection hw with hw; subst hw; exact hF.2)
    show SatP h (fun s : MachRead => CloSt s)
      (cLoopBody base (MachVal.val x :: env) b { st1 with lets := lets' })
    exact csat_cLoopBody hG hA hEv
  all_goals
    unfold loopBodyStep
    try dsimp only
    refine satp_optK ?_
    intro regs hregs
    refine satp_bindO (satp_foldO (P := fun p : List (Nat × Lean.Expr) × MachRead => CloSt p.2)
      regs ([], st) ?_ hst) ?_
    · intro s a _ hs
      exact loopNext_sat hG env base hE s a hs
    rintro ⟨ws, st1⟩ (h1 : CloSt st1)
    exact satp_okO (cloSt_congr h1 (by rfl) (by rfl) (by rfl))

/-- `machLoopRoot`. -/
theorem cloopRoot_sat (senv : StructEnv) (hG : CGood h) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : CloSt st) (hE : EnvClo env) :
    SatP h RootC (loopRootStep senv env e st) := by
  unfold loopRootStep
  split
  · rename_i dom body hview
    refine satp_ite satp_failO ?_
    refine satp_optK ?_
    intro regs _
    refine satp_ite satp_failO ?_
    refine satp_optK ?_
    intro kinds _
    refine satp_optK ?_
    intro inits _
    refine satp_bindO (csat_cConv hG hst hE) ?_
    rintro ⟨dom', st1⟩ ⟨(h1 : CloSt st1), (hd' : Clo 0 dom' = true)⟩
    refine satp_domGuard ?_
    refine satp_bind ?_
    intro shared hsh
    rcases shared with _ | ⟨b0, st2⟩
    · refine satp_bindO (csat_cLoopBody hG
        (cloSt_dom h1 (by rfl) (by rfl) (by rfl) hd')
        (envClo_cons hE (fun w hw => by cases hw))) ?_
      rintro st3 (h3 : CloSt st3)
      exact satp_okO ⟨cloSt_congr h3 (by rfl) (by rfl) (by rfl), trivial⟩
    · have := satp_findSomeO (P := fun p : Nat × MachRead => CloSt p.2) st1.loopWs.toList
        (fun a _ => loopProbe_sat hG env body _ st1 h1 hE a)
        (b0, st2) hsh
      exact satp_okO ⟨this, trivial⟩
  · exact satp_failO

end Arms

/-! ## One step, and the fuel induction -/

/-- **One step keeps the closedness invariant.** -/
theorem cstep_good (senv : StructEnv) {h : Hs} (hG : CGood h) :
    CGood (fun c => (step senv c).run h) := by
  intro c hpre v hv
  cases c with
  | conv env d e st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cconv_sat senv hG env d e st pa pb v hv
  | nested env dom αs initsE body st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cnested_sat senv hG env dom αs initsE body st pa pb v hv
  | inst env c org kinds res args st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cinst_sat hG env c org kinds res args st pa pb v hv
  | instS env c kinds ty args st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cinstS_sat senv hG env c kinds ty args st pa pb v hv
  | chain env e st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cchain_sat senv hG env e st pa pb v hv
  | loopBody base env e st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cloopBody_sat senv hG base env e st pa pb v hv
  | loopRoot env e st =>
    obtain ⟨pa, pb⟩ := hpre
    exact cloopRoot_sat senv hG env e st pa pb v hv

/-- **The closedness invariant of the fuel reader, for ALL fuels** (induction on the fuel). -/
theorem readF_clo (senv : StructEnv) : ∀ n, CGood (readF senv n)
  | 0 => fun c _ v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => cstep_good senv (readF_clo senv n)

section Posts
variable {senv : StructEnv}

theorem machConvF_clo {n : Nat} {env : List MachVal} {d : Nat} {e : Lean.Expr} {st st' : MachRead}
    {r : Lean.Expr} (hst : CloSt st) (hE : EnvClo env)
    (h : machConvF n senv env d e st = some (some (r, st'))) : CloSt st' ∧ Clo d r = true :=
  readF_clo senv n (Call.conv env d e st) ⟨hst, hE⟩ (r, st') h

theorem machChainF_clo {n : Nat} {env : List MachVal} {e : Lean.Expr} {st st' : MachRead}
    {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hst : CloSt st) (hE : EnvClo env)
    (h : machChainF n senv env e st = some (some (ws, v, st'))) : CloSt st' ∧ Clo 0 v = true :=
  readF_clo senv n (Call.chain env e st) ⟨hst, hE⟩ (ws, v, st') h

theorem machLoopRootF_clo {n : Nat} {env : List MachVal} {e : Lean.Expr} {st st' : MachRead}
    {mv : MachVal} (hst : CloSt st) (hE : EnvClo env)
    (h : machLoopRootF n senv env e st = some (some (mv, st'))) : CloSt st' ∧ MvClo mv :=
  readF_clo senv n (Call.loopRoot env e st) ⟨hst, hE⟩ (mv, st') h

end Posts

end Tools.ShippingCloInv
