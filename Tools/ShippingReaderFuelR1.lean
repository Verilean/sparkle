import Tools.ShippingReaderFuelR5
import Tools.ShippingInstSignature

/-! # R1 for the fuel CANDIDATE: every call entry's kind is its callee's signature result

BUILT: run `k1` (poc a6573291) exit 0 as written (worker K, branch `par/r-15`, from poc
`20304f50`; reviewer 2026-10-17 item 2(b)). No `sorry`, no axiom, no
`native_decide`. Nothing here is imported by the compiler; no compiler change.

SCOPE. A property of the NEW fuel functions (`readF`, …) only, by induction on
the fuel exactly as `Tools/ShippingReaderFuelR5.lean` (whose proof skeleton is
copied arm by arm; the invariant is different). It says nothing about the old
`partial` readers (needs O1/O2).

## The invariant

`InstR1 senv st`: every entry `(c, js, r)` of `st.insts` whose callee `c` has a
one-Signal signature `senv.inst c = some (kinds, r')` has kind `r = r'`.

It mentions `st.insts` ONLY, so every state update that does not write `insts`
keeps it by `instR1_congr … (by rfl)`. `insts` is written at exactly two
places (grep `insts :=` in `Tools/ShippingReaderFuelDefs.lean`):

* `instStep` (4068): `push (c, js, res)` — the call's `res`;
* `instSStep` (4110–4113): `++ fields.map (c, js, f.2)` — a STRUCTURE callee.

## Where the call parameters come from (`CallPre`)

A call `Call.inst env c kinds res …` is made at two places of `convStep`:

* the `machInstCall?` arm: `(c, kinds, res, args)` IS `senv.inst c`
  (`machInstCall?_inst`) — R1 holds by construction;
* the memory arm: `c = memChildName combo aw dw`, `res = .bits dw` — R1 holds
  iff `senv.inst` gives that placeholder name no signature with another
  result: the hypothesis `MemR1 senv`. The reader does NOT establish it (the
  name is built by the compiler, `MachMemory.memChildName`; whether the
  environment holds a `@[hardware_module]` of that name is a fact about the
  environment).

A call `Call.instS env c …` is made only in the `machInstCallS?` arm, so
`senv.instS c = some _`. Its entries satisfy `InstR1` iff `senv.inst c = none`:
the hypothesis `SigDisj senv` (no name has both signatures). For
`senv = structEnv env` it is PROVED (`sigDisj_structEnv`: `instSignature?`
needs `machResultKind? ci.type = some _`, `instSignatureS?` needs it `none`).

`GoodR1 senv h`: every answered call whose parameters satisfy `CallPre` and
whose input state satisfies `InstR1` returns a state satisfying `InstR1`.

* `step_good1`, `readF_good1` (every fuel, under `MemR1`, `SigDisj`);
* `machConvF_instR1`, `machChainF_instR1`, `machLoopRootF_instR1`.

MEASURED axioms (run `ax18`, poc after 3a1938a3): `readF_good1`: [propext, Quot.sound]. -/
namespace Tools.ShippingReaderFuelR1
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel
open Tools.ShippingReaderLenOk
open Tools.ShippingInstSignature

/-! ## The invariant and its update lemmas -/

/-- **R1 of a reader state.** -/
def InstR1 (senv : StructEnv) (st : MachRead) : Prop :=
  ∀ (c : Name) (js : List Nat) (r : MixedGateBinder), (c, js, r) ∈ st.insts.toList →
    ∀ (kinds : List MixedGateBinder) (r' : MixedGateBinder),
      senv.inst c = some (kinds, r') → r = r'

/-- The memory placeholder names carry no conflicting one-Signal signature. -/
def MemR1 (senv : StructEnv) : Prop :=
  ∀ (combo : Bool) (aw dw : Nat) (kinds : List MixedGateBinder) (r : MixedGateBinder),
    senv.inst (Sparkle.Compiler.MachMemory.memChildName combo aw dw) = some (kinds, r) →
    r = MixedGateBinder.bits dw

/-- No name has both a one-Signal and a structure signature. -/
def SigDisj (senv : StructEnv) : Prop :=
  ∀ (c : Name) (a : List MixedGateBinder × Lean.Expr)
    (b : List MixedGateBinder × MixedGateBinder),
    senv.instS c = some a → senv.inst c = some b → False

/-- **`SigDisj` of the real signature tables** (`structEnv env`). -/
theorem sigDisj_structEnv (env : Environment) : SigDisj (structEnv env) := by
  rintro c ⟨kS, ty⟩ ⟨kI, r⟩ hS hI
  rw [structEnv_instS] at hS
  rw [structEnv_inst] at hI
  obtain ⟨_, ci, hci, _, _, hnone⟩ := instSignatureS?_some hS
  obtain ⟨_, ci', hci', _, hsome⟩ := instSignature?_some hI
  rw [hci] at hci'
  cases hci'
  rw [hnone] at hsome
  cases hsome

/-- `MemR1` when the environment gives the memory placeholder names no
one-Signal signature at all. -/
theorem memR1_of_none {senv : StructEnv}
    (h : ∀ (combo : Bool) (aw dw : Nat),
      senv.inst (Sparkle.Compiler.MachMemory.memChildName combo aw dw) = none) :
    MemR1 senv := by
  intro combo aw dw kinds r hi
  rw [h combo aw dw] at hi
  cases hi

theorem instR1_init {senv : StructEnv} : InstR1 senv ({} : MachRead) := by
  intro c js r hm
  first
    | cases hm
    | (simp at hm)
    | exact absurd hm List.not_mem_nil

/-- Any update that leaves `insts` alone. -/
theorem instR1_congr {senv : StructEnv} {st st' : MachRead} (H : InstR1 senv st)
    (he : st'.insts = st.insts) : InstR1 senv st' := by
  intro c js r hm
  rw [he] at hm
  exact H c js r hm

/-- `instStep`'s push (4068). -/
theorem instR1_push {senv : StructEnv} {st st' : MachRead} {c : Name} {js : List Nat}
    {res : MixedGateBinder} (H : InstR1 senv st)
    (hc : ∀ (kinds : List MixedGateBinder) (r' : MixedGateBinder),
      senv.inst c = some (kinds, r') → res = r')
    (he : st'.insts = st.insts.push (c, js, res)) : InstR1 senv st' := by
  intro c' js' r hm
  rw [he, Array.toList_push] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact H c' js' r hm
  · have e := List.mem_singleton.mp hm
    injection e with e1 e2
    injection e2 with e3 e4
    subst e1
    subst e4
    exact hc

/-- `instSStep`'s append (4110–4113), for a callee with no one-Signal
signature. -/
theorem instR1_appendS {senv : StructEnv} {st st' : MachRead} {c : Name} {js : List Nat}
    {fields : List (String × MixedGateBinder)} (H : InstR1 senv st)
    (hc : senv.inst c = none)
    (he : st'.insts = st.insts ++ (fields.map fun f => (c, js, f.2)).toArray) :
    InstR1 senv st' := by
  intro c' js' r hm kinds r' hi
  rw [he, Array.toList_append] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact H c' js' r hm kinds r' hi
  · have hm' : (c', js', r) ∈ fields.map (fun f => (c, js, f.2)) := hm
    obtain ⟨f, _, e⟩ := List.mem_map.mp hm'
    have e' : (c, js, f.2) = (c', js', r) := e
    injection e' with e1 e2
    subst e1
    rw [hc] at hi
    cases hi

theorem machReserve_instR1 {senv : StructEnv} {natOf : Lean.Expr → Option Nat}
    {dom' αs initsE body : Lean.Expr} {st : MachRead} {base : Nat} {st' : MachRead}
    (H : InstR1 senv st) (hr : machReserve natOf dom' αs initsE body st = some (base, st')) :
    InstR1 senv st' := by
  obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hr
  subst hst
  exact instR1_congr H (by rfl)

/-! ## Where the call parameters come from -/

theorem machInstCall?_inst {senv : StructEnv} {e : Lean.Expr} {c : Name}
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr}
    (h : machInstCall? senv e = some (c, kinds, res, args)) :
    senv.inst c = some (kinds, res) := by
  unfold machInstCall? at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h1
       injection h1 with e1 h2
       injection h2 with e2 h3
       injection h3 with e3 _
       subst e1
       subst e2
       subst e3
       assumption)

theorem machInstCallS?_instS {senv : StructEnv} {e : Lean.Expr} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    (h : machInstCallS? senv e = some (c, kinds, ty, args)) :
    senv.instS c = some (kinds, ty) := by
  unfold machInstCallS? at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h1
       injection h1 with e1 h2
       injection h2 with e2 h3
       injection h3 with e3 _
       subst e1
       subst e2
       subst e3
       assumption)

/-- The parameters of a call, as the block's call sites make them. -/
def CallPre (senv : StructEnv) : Call → Prop
  | Call.conv _ _ _ _ => True
  | Call.nested _ _ _ _ _ _ => True
  | Call.inst _ c _ res _ _ =>
    ∀ (kinds : List MixedGateBinder) (r : MixedGateBinder), senv.inst c = some (kinds, r) → res = r
  | Call.instS _ c _ _ _ _ => senv.inst c = none
  | Call.chain _ _ _ => True
  | Call.loopBody _ _ _ _ => True
  | Call.loopRoot _ _ _ => True

theorem pre_of_instCall {senv : StructEnv} {e : Lean.Expr} {c : Name}
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr}
    {env : List MachVal} {st : MachRead}
    (h : machInstCall? senv e = some (c, kinds, res, args)) :
    CallPre senv (Call.inst env c kinds res args st) := by
  show ∀ (kinds' : List MixedGateBinder) (r : MixedGateBinder),
    senv.inst c = some (kinds', r) → res = r
  intro kinds' r hi
  rw [machInstCall?_inst h] at hi
  exact (Prod.mk.inj (Option.some.inj hi)).2

theorem pre_of_instCallS {senv : StructEnv} (hD : SigDisj senv) {e : Lean.Expr} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    {env : List MachVal} {st : MachRead}
    (h : machInstCallS? senv e = some (c, kinds, ty, args)) :
    CallPre senv (Call.instS env c kinds ty args st) := by
  show senv.inst c = none
  cases hi : senv.inst c with
  | none => rfl
  | some b => exact (hD c (kinds, ty) b (machInstCallS?_instS h) hi).elim

theorem pre_of_mem {senv : StructEnv} (hM : MemR1 senv) {combo : Bool} {aw dw : Nat}
    {kinds : List MixedGateBinder} {args : List Lean.Expr} {env : List MachVal}
    {st : MachRead} :
    CallPre senv (Call.inst env (Sparkle.Compiler.MachMemory.memChildName combo aw dw) kinds
      (MixedGateBinder.bits dw) args st) := by
  show ∀ (kinds' : List MixedGateBinder) (r : MixedGateBinder),
    senv.inst (Sparkle.Compiler.MachMemory.memChildName combo aw dw) = some (kinds', r) →
    MixedGateBinder.bits dw = r
  intro kinds' r hi
  exact (hM combo aw dw kinds' r hi).symm

/-! ## Call tables that keep the invariant -/

/-- A call table that keeps R1. -/
def GoodR1 (senv : StructEnv) (h : Hs) : Prop :=
  ∀ c, CallPre senv c → InstR1 senv (Call.inSt c) → ∀ v, h c = some (some v) →
    InstR1 senv (Call.outSt c v)

/-- The result's state satisfies R1. -/
abbrev StR1 {α : Type} [HasSt α] (senv : StructEnv) (a : α) : Prop := InstR1 senv (HasSt.st a)

/-- Every OK result of `x` (against `h`) has a state satisfying R1. -/
abbrev Sat1 {α : Type} [HasSt α] (senv : StructEnv) (h : Hs) (x : BM (Option α)) : Prop :=
  ∀ a, x.run h = some (some a) → StR1 senv a

/-! ## Combinators (as in the R5 file) -/

section Comb
variable {senv : StructEnv} {h : Hs} {α β : Type} [HasSt α]

theorem sat1_pure {o : Option α} (ho : ∀ a, o = some a → StR1 senv a) :
    Sat1 senv h (FM.pure o) := by
  intro a ha
  rw [run_pure] at ha
  exact ho a (Option.some.inj ha)

theorem sat1_okO {a : α} (ha : StR1 senv a) : Sat1 senv h (okO a) :=
  sat1_pure fun b hb => by
    injection hb with hb1
    subst hb1
    exact ha

theorem sat1_failO : Sat1 senv h (failO : BM (Option α)) :=
  sat1_pure fun b hb => by cases hb

theorem sat1_optK {o : Option β} {f : β → BM (Option α)}
    (hf : ∀ b, o = some b → Sat1 senv h (f b)) : Sat1 senv h (optK o f) := by
  cases o with
  | none => exact sat1_failO
  | some b => exact hf b rfl

theorem sat1_bindO [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} (hx : Sat1 senv h x)
    (hf : ∀ b, StR1 senv b → Sat1 senv h (f b)) : Sat1 senv h (bindO x f) := by
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b => exact hf b (hx b ho) a ha

theorem sat1_bind {x : BM β} {f : β → BM (Option α)}
    (hf : ∀ r, x.run h = some r → Sat1 senv h (f r)) : Sat1 senv h (FM.bind x f) := by
  intro a ha
  rw [run_bind] at ha
  obtain ⟨r, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  exact hf r hr a ha

theorem sat1_ite {c : Prop} [Decidable c] {x y : BM (Option α)} (hx : Sat1 senv h x)
    (hy : Sat1 senv h y) : Sat1 senv h (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx
  · rw [if_neg hc]
    exact hy

theorem sat1_domGuard {o : Option Lean.Expr} {dom' : Lean.Expr} {k : BM (Option α)}
    (hk : Sat1 senv h k) : Sat1 senv h (domGuard o dom' k) := by
  cases o with
  | none => exact hk
  | some d0 =>
    first
      | exact sat1_ite sat1_failO hk
      | (simp only [domGuard]; exact sat1_ite sat1_failO hk)

theorem sat1_pure_ite {c : Prop} [Decidable c] {a : α} (ha : StR1 senv a) :
    Sat1 senv h (FM.pure (if c then some a else none)) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact sat1_okO ha
  · rw [if_neg hc]
    exact sat1_failO

end Comb

theorem sat1_foldO {senv : StructEnv} {σ α : Type} [HasSt σ] {h : Hs}
    {f : σ → α → BM (Option σ)} (hf : ∀ s a, StR1 senv s → Sat1 senv h (f s a)) :
    ∀ (l : List α) (s : σ), StR1 senv s → Sat1 senv h (foldO f s l)
  | [], _, hs => sat1_okO hs
  | a :: l, s, hs => sat1_bindO (hf s a hs) (fun s' hs' => sat1_foldO hf l s' hs')

theorem sat1_findSomeO {senv : StructEnv} {α β : Type} [HasSt β] {h : Hs}
    {f : α → BM (Option β)} (hf : ∀ a, Sat1 senv h (f a)) :
    ∀ (l : List α), Sat1 senv h (findSomeO f l)
  | [] => sat1_failO
  | a :: l => by
    refine sat1_bind ?_
    intro r hr
    cases r with
    | none => exact sat1_findSomeO hf l
    | some b => exact sat1_okO (hf a b hr)

/-! ## The answers of the calls, as `Sat1` facts -/

section Out
variable {senv : StructEnv} {h : Hs}

theorem sat1_cConv (hG : GoodR1 senv h) {env : List MachVal} {d : Nat} {e : Lean.Expr}
    {st : MachRead} (hst : InstR1 senv st) : Sat1 senv h (cConv env d e st) :=
  fun p hp => hG (Call.conv env d e st) True.intro hst p hp

theorem sat1_cNested (hG : GoodR1 senv h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} (hst : InstR1 senv st) : Sat1 senv h (cNested env dom αs initsE body st) :=
  fun p hp => hG (Call.nested env dom αs initsE body st) True.intro hst p hp

theorem sat1_cInst (hG : GoodR1 senv h) {env : List MachVal} {c : Name}
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr}
    {st : MachRead} (hpre : CallPre senv (Call.inst env c kinds res args st))
    (hst : InstR1 senv st) : Sat1 senv h (cInst env c kinds res args st) :=
  fun p hp => hG (Call.inst env c kinds res args st) hpre hst p hp

theorem sat1_cInstS (hG : GoodR1 senv h) {env : List MachVal} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead}
    (hpre : CallPre senv (Call.instS env c kinds ty args st))
    (hst : InstR1 senv st) : Sat1 senv h (cInstS env c kinds ty args st) :=
  fun p hp => hG (Call.instS env c kinds ty args st) hpre hst p hp

theorem sat1_cChain (hG : GoodR1 senv h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hst : InstR1 senv st) : Sat1 senv h (cChain env e st) :=
  fun p hp => hG (Call.chain env e st) True.intro hst p hp

theorem sat1_cLoopBody (hG : GoodR1 senv h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} (hst : InstR1 senv st) : Sat1 senv h (cLoopBody base env e st) :=
  fun p hp => hG (Call.loopBody base env e st) True.intro hst p hp

theorem sat1_cLoopRoot (hG : GoodR1 senv h) {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} (hst : InstR1 senv st) : Sat1 senv h (cLoopRoot env e st) :=
  fun p hp => hG (Call.loopRoot env e st) True.intro hst p hp

end Out

/-! ## Pure fragments -/

/-- `machConv`'s `.bvar` arm returns its input state. -/
theorem convBvar_r1 {senv : StructEnv} {env : List MachVal} {d j : Nat} {st : MachRead}
    {r : Lean.Expr × MachRead} (hr : convBvar env d j st = some r) (hst : InstR1 senv st) :
    StR1 senv r := by
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

theorem instEntry_r1 {senv : StructEnv} {res : MixedGateBinder} {st st' : MachRead}
    (hr : instEntry res st = some st') (hst : InstR1 senv st) : InstR1 senv st' := by
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
    exact instR1_congr hst (by rfl)
  | domain =>
    have hr' : (none : Option MachRead) = some st' := hr
    cases hr'

/-- A leaf `hr : o = some r` whose state is the hypothesis' state or an update
of it that leaves `insts` alone. -/
macro "r1leaf " hr:ident h1:ident : tactic => `(tactic| first
  | (cases $hr:ident; done)
  | (injection $hr:ident with hq; subst hq; exact $h1:ident)
  | (injection $hr:ident with hq; subst hq; exact instR1_congr $h1:ident (by rfl))
  | (cases $hr:ident; exact $h1:ident)
  | (cases $hr:ident; exact instR1_congr $h1:ident (by rfl)))

/-- A `let (x, y) := p; k` continuation (as `r5pair`). -/
macro "r1pair " t:tactic : tactic => `(tactic| first
  | $t:tactic
  | (split <;> $t:tactic)
  | ((try dsimp only); split <;> $t:tactic)
  | ((try dsimp only); (repeat' split) <;> $t:tactic))

/-! ## The `foldlM` / `findSome?` functions -/

section Helpers
variable {senv : StructEnv} {h : Hs}

theorem instArg_sat1 (hG : GoodR1 senv h) (env : List MachVal) (k : Nat) :
    ∀ s a, StR1 senv s → Sat1 senv h (instArg env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hst : InstR1 senv st)
  refine sat1_bindO (sat1_cConv hG hst) ?_
  rintro ⟨v', st1⟩ (h1 : InstR1 senv st1)
  refine sat1_pure ?_
  intro r hr
  repeat' split at hr
  all_goals r1leaf hr h1

theorem instSArg_sat1 (hG : GoodR1 senv h) (env : List MachVal) :
    ∀ s a, StR1 senv s → Sat1 senv h (instSArg env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hst : InstR1 senv st)
  refine sat1_bindO (sat1_cConv hG hst) ?_
  rintro ⟨v', st1⟩ (h1 : InstR1 senv st1)
  refine sat1_pure ?_
  intro r hr
  repeat' split at hr
  all_goals r1leaf hr h1

theorem instSParam_sat1 (hG : GoodR1 senv h) (env : List MachVal) :
    ∀ s a, StR1 senv s → Sat1 senv h (instSParam env s a) := by
  rintro ⟨ps, st⟩ p (hst : InstR1 senv st)
  refine sat1_bindO (sat1_cConv hG hst) ?_
  rintro ⟨p', st1⟩ (h1 : InstR1 senv st1)
  refine sat1_okO ?_
  exact h1

theorem loopNext_sat1 (hG : GoodR1 senv h) (env : List MachVal) (base : Nat) :
    ∀ s a, StR1 senv s → Sat1 senv h (loopNext env base s a) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩ (hst : InstR1 senv st)
  refine sat1_bindO (sat1_cConv hG hst) ?_
  rintro ⟨nx', st1⟩ (h1 : InstR1 senv st1)
  refine sat1_okO ?_
  exact h1

theorem nestedProbe_sat1 (hG : GoodR1 senv h) (env : List MachVal)
    (dom' αs initsE body : Lean.Expr) (st : MachRead) (hst : InstR1 senv st) :
    ∀ a, Sat1 senv h (nestedProbe env dom' αs initsE body st a) := by
  rintro ⟨base, d, a, ini, ws, v⟩
  refine sat1_ite ?_ sat1_failO
  refine sat1_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact sat1_failO
  · have h' : InstR1 senv st' := sat1_cChain hG hst (ws', v', st') hr
    refine sat1_pure_ite ?_
    exact h'

theorem loopProbe_sat1 (hG : GoodR1 senv h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st : MachRead) (hst : InstR1 senv st) : ∀ a, Sat1 senv h (loopProbe env body n st a) := by
  rintro ⟨b0, n0, ws0⟩
  refine sat1_ite sat1_failO ?_
  refine sat1_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact sat1_failO
  · have h' : InstR1 senv st' := sat1_cLoopBody hG (instR1_congr hst (by rfl)) st' hr
    refine sat1_pure_ite ?_
    exact instR1_congr h' (by rfl)

end Helpers

/-! ## The seven bodies -/

section Arms
variable {h : Hs}

/-- `machConv`'s `.app` arm (as `conv_app_sat`; the two instance arms and the
memory arm discharge `CallPre`). -/
theorem conv_app_sat1 (senv : StructEnv) (hM : MemR1 senv) (hD : SigDisj senv)
    (hG : GoodR1 senv h) (env : List MachVal) (d : Nat)
    (f a : Lean.Expr) (st : MachRead) (hst : InstR1 senv st) :
    Sat1 senv h (convStep senv env d (.app f a) st) := by
  first
    | simp only [convStep]
    | (unfold convStep; dsimp only)
  split
  · -- a bare `Signal.register`
    refine sat1_ite sat1_failO ?_
    split
    · refine sat1_okO ?_
      exact hst
    · refine sat1_optK ?_
      intro kind _
      refine sat1_optK ?_
      intro initN _
      refine sat1_bindO (sat1_cConv hG hst) ?_
      rintro ⟨dom', st1⟩ (h1 : InstR1 senv st1)
      refine sat1_domGuard ?_
      refine sat1_bindO (sat1_cConv hG (instR1_congr h1 (by rfl))) ?_
      rintro ⟨x', st2⟩ (h2 : InstR1 senv st2)
      refine sat1_okO ?_
      exact instR1_congr h2 (by rfl)
  · split
    · -- a loop read
      refine sat1_pure_ite ?_
      exact hst
    · split
      · -- a nested machine
        exact sat1_ite sat1_failO (sat1_cNested hG hst)
      · split
        · -- an instance: the parameters ARE the signature (`machInstCall?_inst`)
          refine sat1_ite sat1_failO (sat1_cInst hG ?pre hst)
          case pre => exact pre_of_instCall (by assumption)
        · split
          · -- a structure instance: no one-Signal signature (`SigDisj`)
            refine sat1_ite sat1_failO (sat1_cInstS hG ?pre hst)
            case pre => exact pre_of_instCallS hD (by assumption)
          · split
            · -- a memory: the placeholder name (`MemR1`)
              refine sat1_ite sat1_failO (sat1_bindO (sat1_cInst hG ?pre hst) ?k)
              case pre => exact pre_of_mem hM
              case k =>
                rintro ⟨v, st1⟩ (h1 : InstR1 senv st1)
                refine sat1_okO ?_
                exact instR1_congr h1 (by rfl)
            · split
              · -- a state read
                refine sat1_pure_ite ?_
                exact hst
              · -- an application
                refine sat1_bindO (sat1_cConv hG hst) ?_
                rintro ⟨f', st1⟩ (h1 : InstR1 senv st1)
                refine sat1_bindO (sat1_cConv hG h1) ?_
                rintro ⟨a', st2⟩ (h2 : InstR1 senv st2)
                refine sat1_okO ?_
                exact h2

/-- `machConv`'s `.letE` arm. -/
theorem conv_letE_sat1 (senv : StructEnv) (hG : GoodR1 senv h) (env : List MachVal) (d : Nat)
    (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead) (hst : InstR1 senv st) :
    Sat1 senv h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine sat1_ite sat1_failO ?_
  split
  · exact sat1_cConv hG hst
  · refine sat1_ite ?_ ?_
    · refine sat1_bindO (sat1_cLoopRoot hG hst) ?_
      rintro ⟨mv, st1⟩ (h1 : InstR1 senv st1)
      exact sat1_cConv hG h1
    · split
      · exact sat1_cConv hG hst
      · split
        · exact sat1_cConv hG hst
        · refine sat1_bindO (sat1_cConv hG hst) ?_
          rintro ⟨v', st1⟩ (h1 : InstR1 senv st1)
          r1pair (exact sat1_cConv hG (instR1_congr h1 (by rfl)))

/-- `machConv`. -/
theorem conv_sat1 (senv : StructEnv) (hM : MemR1 senv) (hD : SigDisj senv)
    (hG : GoodR1 senv h) (env : List MachVal) (d : Nat)
    (e : Lean.Expr) (st : MachRead) (hst : InstR1 senv st) :
    Sat1 senv h (convStep senv env d e st) := by
  cases e
  case bvar j =>
    refine sat1_pure ?_
    intro r hr
    exact convBvar_r1 hr hst
  case app f a => exact conv_app_sat1 senv hM hD hG env d f a st hst
  case letE nm ty v b nd => exact conv_letE_sat1 senv hG env d nm ty v b nd st hst
  case lam nm t b bi =>
    refine sat1_bindO (sat1_cConv hG hst) ?_
    rintro ⟨t', st1⟩ (h1 : InstR1 senv st1)
    refine sat1_bindO (sat1_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : InstR1 senv st2)
    refine sat1_okO ?_
    exact h2
  case forallE nm t b bi =>
    refine sat1_bindO (sat1_cConv hG hst) ?_
    rintro ⟨t', st1⟩ (h1 : InstR1 senv st1)
    refine sat1_bindO (sat1_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : InstR1 senv st2)
    refine sat1_okO ?_
    exact h2
  all_goals first
    | (refine sat1_okO ?_; exact hst)
    | exact sat1_failO

/-- `machNested`. -/
theorem nested_sat1 (senv : StructEnv) (hG : GoodR1 senv h) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) (hst : InstR1 senv st) :
    Sat1 senv h (nestedStep senv env dom αs initsE body st) := by
  refine sat1_ite sat1_failO ?_
  refine sat1_bindO (sat1_cConv hG hst) ?_
  rintro ⟨dom', st1⟩ (h1 : InstR1 senv st1)
  refine sat1_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · refine sat1_optK ?_
    rintro ⟨base, st2⟩ hres
    have h2 : InstR1 senv st2 := machReserve_instR1 h1 hres
    refine sat1_bindO (sat1_cChain hG (instR1_congr h2 (by rfl))) ?_
    rintro ⟨ws, v, st3⟩ (h3 : InstR1 senv st3)
    refine sat1_okO ?_
    exact instR1_congr h3 (by rfl)
  · refine sat1_okO ?_
    exact sat1_findSomeO (nestedProbe_sat1 hG _ _ _ _ _ _ h1) _ r hsh

/-- `machInstance`: the push carries the call's `res`, which `CallPre` ties to
the signature. -/
theorem inst_sat1 {senv : StructEnv} (hG : GoodR1 senv h) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr)
    (st : MachRead)
    (hpre : ∀ (kinds' : List MixedGateBinder) (r : MixedGateBinder),
      senv.inst c = some (kinds', r) → res = r)
    (hst : InstR1 senv st) : Sat1 senv h (instStep env c kinds res args st) := by
  refine sat1_optK ?_
  intro st1 hst1
  have h1 : InstR1 senv st1 := instEntry_r1 hst1 hst
  refine sat1_bindO (sat1_foldO (instArg_sat1 hG env _) _ _ ?_) ?_
  · exact h1
  rintro ⟨js, st2⟩ (h2 : InstR1 senv st2)
  refine sat1_pure ?_
  intro r hr
  split at hr
  all_goals first
    | (cases hr; done)
    | (injection hr with hq; subst hq; exact h2)
    | (injection hr with hq; subst hq; exact instR1_push (js := js) h2 hpre (by rfl))
    | (cases hr; exact h2)
    | (cases hr; exact instR1_push (js := js) h2 hpre (by rfl))

/-- `machInstanceS`: the appended entries' callee has no one-Signal signature
(`CallPre`). -/
theorem instS_sat1 (senv : StructEnv) (hG : GoodR1 senv h) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hpre : senv.inst c = none)
    (hst : InstR1 senv st) : Sat1 senv h (instSStep senv env c kinds ty args st) := by
  refine sat1_ite sat1_failO ?_
  refine sat1_optK ?_
  intro resTy _
  refine sat1_optK ?_
  intro r _
  obtain ⟨oc, fields⟩ := r
  cases oc with
  | none => exact sat1_failO
  | some ctor =>
    refine sat1_ite sat1_failO ?_
    refine sat1_bindO (sat1_foldO (instSArg_sat1 hG env) _ _ ?_) ?_
    · exact hst
    rintro ⟨js, st1⟩ (h1 : InstR1 senv st1)
    refine sat1_bindO (sat1_foldO (instSParam_sat1 hG env) _ _ ?_) ?_
    · exact h1
    rintro ⟨params, st2⟩ (h2 : InstR1 senv st2)
    try dsimp only
    split
    · refine sat1_okO ?_
      exact h2
    · refine sat1_okO ?_
      exact instR1_appendS (js := js) (fields := fields) h2 hpre (by rfl)

/-- `machChain`. -/
theorem chain_sat1 (senv : StructEnv) (hG : GoodR1 senv h) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) (hst : InstR1 senv st) : Sat1 senv h (chainStep senv env e st) := by
  revert hst
  unfold chainStep
  split
  · intro hst
    refine sat1_bindO (sat1_cConv hG hst) ?_
    rintro ⟨v', st1⟩ (h1 : InstR1 senv st1)
    refine sat1_okO ?_
    exact h1
  · intro hst
    refine sat1_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → InstR1 senv b := by
      intro a b he
      subst he
      exact sat1_cConv hG hst (a, b) hr
    revert hr'
    split
    · intro hr'
      have h1 := hr' _ _ rfl
      refine sat1_ite ?_ sat1_failO
      refine sat1_bindO (sat1_cChain hG h1) ?_
      rintro ⟨ws, v, st2⟩ (h2 : InstR1 senv st2)
      refine sat1_okO ?_
      exact h2
    · intro _
      exact sat1_failO
  · intro hst
    split
    · exact sat1_cChain hG hst
    · refine sat1_ite ?_ ?_
      · refine sat1_bindO (sat1_cLoopRoot hG hst) ?_
        rintro ⟨mv, st1⟩ (h1 : InstR1 senv st1)
        exact sat1_cChain hG h1
      · split
        · exact sat1_cChain hG hst
        · split
          · exact sat1_cChain hG hst
          · refine sat1_bindO (sat1_cConv hG hst) ?_
            rintro ⟨v', st1⟩ (h1 : InstR1 senv st1)
            r1pair (exact sat1_cChain hG (instR1_congr h1 (by rfl)))
  · intro _
    exact sat1_failO

/-- `machLoopBody`. -/
theorem loopBody_sat1 {senv : StructEnv} (hG : GoodR1 senv h) (base : Nat) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : InstR1 senv st) :
    Sat1 senv h (loopBodyStep base env e st) := by
  cases e
  case letE nm ty v b nd =>
    refine sat1_bindO (sat1_cConv hG hst) ?_
    rintro ⟨v', st1⟩ (h1 : InstR1 senv st1)
    r1pair (exact sat1_cLoopBody hG (instR1_congr h1 (by rfl)))
  all_goals
    unfold loopBodyStep
    try dsimp only
    refine sat1_optK ?_
    intro regs _
    refine sat1_bindO (sat1_foldO (loopNext_sat1 hG _ _) _ _ ?_) ?_
    · exact hst
    rintro ⟨ws, st1⟩ (h1 : InstR1 senv st1)
    refine sat1_okO ?_
    exact instR1_congr h1 (by rfl)

/-- `machLoopRoot`. -/
theorem loopRoot_sat1 (senv : StructEnv) (hG : GoodR1 senv h) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : InstR1 senv st) :
    Sat1 senv h (loopRootStep senv env e st) := by
  unfold loopRootStep
  split
  · refine sat1_ite sat1_failO ?_
    refine sat1_optK ?_
    intro regs _
    refine sat1_ite sat1_failO ?_
    refine sat1_optK ?_
    intro kinds _
    refine sat1_optK ?_
    intro inits _
    refine sat1_bindO (sat1_cConv hG hst) ?_
    rintro ⟨dom', st1⟩ (h1 : InstR1 senv st1)
    refine sat1_domGuard ?_
    refine sat1_bind ?_
    intro shared hsh
    rcases shared with _ | ⟨b0, st2⟩
    · refine sat1_bindO (sat1_cLoopBody hG (instR1_congr h1 (by rfl))) ?_
      rintro st3 (h3 : InstR1 senv st3)
      refine sat1_okO ?_
      exact instR1_congr h3 (by rfl)
    · refine sat1_okO ?_
      exact sat1_findSomeO (loopProbe_sat1 hG _ _ _ _ h1) _ (b0, st2) hsh
  · exact sat1_failO

end Arms

/-- **One step keeps R1**: if the table keeps it, the body run against the
table keeps it (under `MemR1`, `SigDisj`). -/
theorem step_good1 (senv : StructEnv) (hM : MemR1 senv) (hD : SigDisj senv) {h : Hs}
    (hG : GoodR1 senv h) : GoodR1 senv (fun c => (step senv c).run h) := by
  intro c hpre hin v hv
  cases c with
  | conv env d e st => exact conv_sat1 senv hM hD hG env d e st hin v hv
  | nested env dom αs initsE body st =>
    exact nested_sat1 senv hG env dom αs initsE body st hin v hv
  | inst env c kinds res args st => exact inst_sat1 hG env c kinds res args st hpre hin v hv
  | instS env c kinds ty args st => exact instS_sat1 senv hG env c kinds ty args st hpre hin v hv
  | chain env e st => exact chain_sat1 senv hG env e st hin v hv
  | loopBody base env e st => exact loopBody_sat1 hG base env e st hin v hv
  | loopRoot env e st => exact loopRoot_sat1 senv hG env e st hin v hv

/-- **R1 of the fuel reader, for ALL fuels** (induction on the fuel). -/
theorem readF_good1 (senv : StructEnv) (hM : MemR1 senv) (hD : SigDisj senv) :
    ∀ n, GoodR1 senv (readF senv n)
  | 0 => fun c _ _ v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => step_good1 senv hM hD (readF_good1 senv hM hD n)

theorem machConvF_instR1 {n : Nat} {senv : StructEnv} (hM : MemR1 senv) (hD : SigDisj senv)
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead} {r : Lean.Expr}
    {st' : MachRead} (h : machConvF n senv env d e st = some (some (r, st')))
    (hst : InstR1 senv st) : InstR1 senv st' :=
  readF_good1 senv hM hD n (Call.conv env d e st) True.intro hst (r, st') h

theorem machChainF_instR1 {n : Nat} {senv : StructEnv} (hM : MemR1 senv) (hD : SigDisj senv)
    {env : List MachVal} {e : Lean.Expr} {st : MachRead} {ws : List (Nat × Lean.Expr)}
    {v : Lean.Expr} {st' : MachRead} (h : machChainF n senv env e st = some (some (ws, v, st')))
    (hst : InstR1 senv st) : InstR1 senv st' :=
  readF_good1 senv hM hD n (Call.chain env e st) True.intro hst (ws, v, st') h

theorem machLoopRootF_instR1 {n : Nat} {senv : StructEnv} (hM : MemR1 senv)
    (hD : SigDisj senv) {env : List MachVal} {e : Lean.Expr} {st : MachRead} {mv : MachVal}
    {st' : MachRead} (h : machLoopRootF n senv env e st = some (some (mv, st')))
    (hst : InstR1 senv st) : InstR1 senv st' :=
  readF_good1 senv hM hD n (Call.loopRoot env e st) True.intro hst (mv, st') h

end Tools.ShippingReaderFuelR1
