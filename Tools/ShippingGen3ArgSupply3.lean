import Tools.ShippingGen3ArgSupply2   -- batch 2: ReadInv, EnvKindOk, ReadSub, CallPreK, GoodK, PhExt, SatK, closed arms
set_option autoImplicit false
-- Built: g3sf-88858249 (clean snapshot, exit 0, standard axioms). No `sorry`, no `axiom`, no `native_decide`.

/-! # SRC-ARGW batch 3: option (b) of scripts/gen3/SRC_ARGW_SUPPLY_FREEZE.md §3.7 (rev3 at e8a41c70)

CONDITIONAL INTERMEDIATE WORK ONLY. NOT an L-RUN1 discharge, NOT L-FG supply, NOT FG completion (§1.3). Nothing
here is a reader run of a corpus declaration. No shared definition, no compiler file, no FG statement is edited.

* **Definitions (§3.7.3, text of the freeze, binder types annotated):** `EntryKindOk` (per ENV ENTRY, `dom`-free;
  `.state b n` demands `n = 1 ∧ st.kinds[b]? = some k`), `EnvKindOkE`, `CallPreKE` (rev2 `CallPreK` with
  `EnvKindOkE` in all seven rows), `GoodKE`, and the UNCONDITIONAL table invariant `GoodE`.
* **`goodE_readF`** (§2 below): `∀ n, GoodE (readF senv n)`, by fuel induction with NO premise, in the style of
  `readF_good` (Tools/ShippingReaderFuelR5.lean:71-72, :756-761): each of the seven bodies is taken apart in the
  same order as R5 (`step_good`), with the Hoare predicate `SatE st₀` ("every OK result's state extends `st₀` in
  `kinds`/`lets`/`insts`"). Leaves: pushes / appends (`apre_push`, `apre_append`), the four let binders
  (`apre_bindLet`, `apre_bindLetNamed`, `apre_bindLetAlias`, `apre_letIndex`: push or unchanged),
  `machReserve` (append, via `machReserve_some`), `instEntry`, and the probes (`{ st with ws := … }`).
* **E lemmas:** `envKindOk_of_E` (E ⇒ rev2 `EnvKindOk`; ONE direction only — the converse is false, see the
  controls in Tests/Gen3/ArgSupply3Check.lean: a typed non-domain `.state b n` with `n = 0` or `n ≥ 2` satisfies the
  old `EnvKindOk` vacuously when `st.dom = none`, and is EXCLUDED by `EnvKindOkE`), `entryKindOk_ext`,
  `envKindOkE_ext` (from `PhExt`), `envKindOkE_lift`, `envKindOkE_cons`, `satK_bindOE`.
* **Migrated closed arms (E versions of batch 2):** G1 `satKE_conv_bvar`, G15 `satKE_conv_mdata` / `_proj`,
  G10 `satKE_conv_letFloat`, G13 `satKE_conv_letRegs` / `_letHandle`, G16-pure `satKE_chain_pure`,
  G17 float / `.regs` / `.handle` `satKE_chain_letFloat` / `_letRegs` / `_letHandle`.
* **Arms (b) unblocks, CLOSED here (proof written, conditional on `GoodKE ∧ GoodE` of the table):**
  - G9 `satKE_conv_lam`, `satKE_conv_forallE` (second call at `d + 1` under `envKindOkE_lift` + `_ext`);
  - G16 `next` `satKE_chain_next` (second call under the `.unit` entry, `envKindOkE_cons` + `_ext`);
  - G7 `satKE_instSParamFold` (the `instSParam` fold of `instSStep`, every parameter at its own state);
  - G19 `satKE_loopBody_tail` (the `loopNext` fold + `ws` append; `readSub_loopRegs`, `readInv_ws`);
  - G8 `satKE_conv_app_generic` (generic application: both calls; the result-kind item stays NOT AUDITED).
* **OPEN (not closed here):** G2 (bare register: needs a `regView?` argument lemma — matcher not split in v4.32.1),
  G4 (nested: `machRunApp?` argument lemma + reserve state, not written), G5 / G6 (`ConvKind`/`EqvSound`/`uniq` per
  argument), G11 / G17 user-let / G18 (new entry `.val x`: `ConvKind`, D5 `rootFloat` transport, new-let
  `LetKindOk`), G12 / G20 (loop root: `n = 1 ∧ kinds[b] = k` at the created `.state` entry, `LoopSrcKinds` /
  `LoopLetSrcKinds`, the shared probe's `ws` argument), G3 / G14 / G21 (not audited / not attempted). Their
  second-call parts are dischargeable with `envKindOkE_ext` / `_cons` + `goodE_readF` but are NOT written.
* **Not claimed:** LK1's induction (`GoodKE` of `readF`) is not proved; `GoodKE` is a hypothesis of every arm. -/
namespace Tools.ShippingGen3ArgSupply3
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingGen3ArgSupply (phKind PhKinding PhKindingLaws LetKindOk)
open Tools.ShippingReaderFuel
open Tools.ShippingReaderFuelProv (InstProv CallPreP)
open Tools.ShippingReaderLenOk (machReserve_some reserved)
open Tools.ShippingGen3ArgSupply2

/-! ## 1. Array prefixes and the state extension `PhExt` (A2:587-598) -/

/-- `b` keeps every entry of `a` (push / append / unchanged). -/
def APre {α : Type} (a b : Array α) : Prop :=
  ∀ (i : Nat) (y : α), a[i]? = some y → b[i]? = some y

theorem apre_refl {α : Type} (a : Array α) : APre a a := fun _ _ h => h

theorem apre_push {α : Type} (a : Array α) (x : α) : APre a (a.push x) := by
  intro i y h
  obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.mp h
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hi)]
  exact h

theorem apre_append {α : Type} (a b : Array α) : APre a (a ++ b) := by
  intro i y h
  obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.mp h
  rw [Array.getElem?_append_left hi]
  exact h

/-- One update step after an extension. -/
theorem phExt_upd {st₀ st st' : MachRead} (h : PhExt st₀ st) (hk : APre st.kinds st'.kinds)
    (hl : APre st.lets st'.lets) (hi : APre st.insts st'.insts) : PhExt st₀ st' :=
  ⟨fun i k hh => hk i k (h.1 i k hh), fun j l hh => hl j l (h.2.1 j l hh),
    fun k c hh => hi k c (h.2.2 k c hh)⟩

/-! The record updates of the reader (shapes copied from `lenOk_*`, Tools/ShippingReaderLenOk.lean:130-256). -/

theorem phExt_ws {st₀ st : MachRead} (h : PhExt st₀ st) (ws : Array (Nat × Lean.Expr)) :
    PhExt st₀ { st with ws := ws } :=
  phExt_upd h (apre_refl _) (apre_refl _) (apre_refl _)

theorem phExt_dom {st₀ st : MachRead} (h : PhExt st₀ st) (dom : Option Lean.Expr) :
    PhExt st₀ { st with dom := dom } :=
  phExt_upd h (apre_refl _) (apre_refl _) (apre_refl _)

theorem phExt_instStruct {st₀ st : MachRead} (h : PhExt st₀ st) (b : Bool) :
    PhExt st₀ { st with instStruct := b } :=
  phExt_upd h (apre_refl _) (apre_refl _) (apre_refl _)

theorem phExt_inInner {st₀ st : MachRead} (h : PhExt st₀ st) (b : Bool) :
    PhExt st₀ { st with inInner := b } :=
  phExt_upd h (apre_refl _) (apre_refl _) (apre_refl _)

theorem phExt_lets {st₀ st : MachRead} (h : PhExt st₀ st) (lets : MachLets) (hl : APre st.lets lets) :
    PhExt st₀ { st with lets := lets } :=
  phExt_upd h (apre_refl _) hl (apre_refl _)

theorem phExt_nestedClose {st₀ st : MachRead} (h : PhExt st₀ st) (ws : Array (Nat × Lean.Expr))
    (outer : Bool)
    (nested : Array (Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr)) :
    PhExt st₀ { st with ws := ws, inInner := outer, nested := nested } :=
  phExt_upd h (apre_refl _) (apre_refl _) (apre_refl _)

theorem phExt_loopClose {st₀ st : MachRead} (h : PhExt st₀ st)
    (loopWs : Array (Nat × Nat × List (Nat × Lean.Expr))) (depth : Nat) :
    PhExt st₀ { st with loopWs := loopWs, loopDepth := depth } :=
  phExt_upd h (apre_refl _) (apre_refl _) (apre_refl _)

theorem phExt_bareRegister {st₀ st : MachRead} (h : PhExt st₀ st) (kind : MixedGateBinder)
    (initN : Nat) (nm : Name) (dom' e : Lean.Expr) (base : Nat) :
    PhExt st₀ { st with
      kinds := st.kinds.push kind, inits := st.inits.push initN
      names := st.names.push nm, dom := some dom'
      bareRegs := st.bareRegs.push (e, base) } :=
  phExt_upd h (apre_push _ _) (apre_refl _) (apre_refl _)

theorem phExt_instPush {st₀ st : MachRead} (h : PhExt st₀ st)
    (e : Name × List Nat × MixedGateBinder) (instFields : Array String) (org : InstOrigin) :
    PhExt st₀ { st with insts := st.insts.push e, instFields := instFields,
                        instOrigins := st.instOrigins.push org } :=
  phExt_upd h (apre_refl _) (apre_refl _) (apre_push _ _)

theorem phExt_instS {st₀ st : MachRead} (h : PhExt st₀ st) {α : Type}
    (fields : List α) (g : α → Name × List Nat × MixedGateBinder) (instFields : Array String) (b : Bool) :
    PhExt st₀ { st with insts := st.insts ++ (fields.map g).toArray,
                        instFields := instFields, instStruct := b,
                        instOrigins := st.instOrigins ++
                          ((List.range fields.length).map InstOrigin.field).toArray } :=
  phExt_upd h (apre_refl _) (apre_refl _) (apre_append _ _)

theorem phExt_loopRoot {st₀ st : MachRead} (h : PhExt st₀ st) {kinds : List MixedGateBinder}
    {inits : List Nat} (dom' : Lean.Expr) (depth : Nat) :
    PhExt st₀ { st with
      kinds := st.kinds ++ kinds.toArray
      inits := st.inits ++ inits.toArray
      names := st.names ++ ((List.range kinds.length).map fun i =>
        Name.mkSimple s!"loop{st.loops.size}_r{i}").toArray
      dom := some dom'
      loops := st.loops.push (st.kinds.size, kinds.length)
      nestedLoops := if depth ≥ 1 then st.nestedLoops + 1 else st.nestedLoops
      loopDepth := depth + 1 } :=
  phExt_upd h (apre_append _ _) (apre_refl _) (apre_refl _)

/-! ### The let binders push or return the old array (E:3619-3671, :3743-3750) -/

theorem apre_bindLet (nm : Name) (ty v' : Lean.Expr) (lets : MachLets) :
    APre lets (machBindLet nm ty v' lets).2 := by
  unfold machBindLet
  repeat' split
  all_goals first
    | exact apre_refl _
    | exact apre_push _ _

theorem apre_bindLetNamed (nm : Name) (ty v' : Lean.Expr) (lets : MachLets) :
    APre lets (machBindLetNamed nm ty v' lets).2 := by
  unfold machBindLetNamed
  repeat' split
  all_goals first
    | exact apre_refl _
    | exact apre_push _ _

theorem apre_bindLetAlias (nm : Name) (ty v' : Lean.Expr) (lets : MachLets) :
    APre lets (machBindLetAlias nm ty v' lets).2 := by
  unfold machBindLetAlias
  try dsimp only
  repeat' split
  all_goals first
    | exact apre_refl _
    | exact apre_push _ _
    | exact apre_bindLetNamed _ _ _ _

theorem apre_letIndex (nm : Name) (k : MixedGateBinder) (v' : Lean.Expr) (lets : MachLets) :
    APre lets (machLetIndex nm k v' lets).2 := by
  unfold machLetIndex
  repeat' split
  all_goals first
    | exact apre_refl _
    | exact apre_push _ _

/-- `machLoopBody`'s let binder (FD:540-543). -/
theorem apre_loopLet (nm : Name) (ty v' : Lean.Expr) (lets : MachLets) :
    APre lets (if machIsSlot v' then machBindLetNamed nm ty v' lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' lets
      else machBindLet nm ty v' lets).2 := by
  split
  · exact apre_bindLetNamed _ _ _ _
  · split
    · exact apre_bindLetAlias _ _ _ _
    · exact apre_bindLet _ _ _ _

theorem apre_of_bindLet {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} {x : Lean.Expr} {ls : MachLets}
    (heq : machBindLet nm ty v' lets = (x, ls)) : APre lets ls := by
  have h := apre_bindLet nm ty v' lets
  rw [heq] at h
  exact h

theorem apre_of_bindLetNamed {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} {x : Lean.Expr}
    {ls : MachLets} (heq : machBindLetNamed nm ty v' lets = (x, ls)) : APre lets ls := by
  have h := apre_bindLetNamed nm ty v' lets
  rw [heq] at h
  exact h

theorem apre_of_bindLetAlias {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} {x : Lean.Expr}
    {ls : MachLets} (heq : machBindLetAlias nm ty v' lets = (x, ls)) : APre lets ls := by
  have h := apre_bindLetAlias nm ty v' lets
  rw [heq] at h
  exact h

theorem apre_of_letIndex {nm : Name} {k : MixedGateBinder} {v' : Lean.Expr} {lets : MachLets} {j : Nat}
    {ls : MachLets} (heq : machLetIndex nm k v' lets = (j, ls)) : APre lets ls := by
  have h := apre_letIndex nm k v' lets
  rw [heq] at h
  exact h

theorem apre_of_loopLet {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} {x : Lean.Expr} {ls : MachLets}
    (heq : (if machIsSlot v' then machBindLetNamed nm ty v' lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' lets
      else machBindLet nm ty v' lets) = (x, ls)) : APre lets ls := by
  have h := apre_loopLet nm ty v' lets
  rw [heq] at h
  exact h

/-- Closes an `APre old new` goal of a let binder (direct `.2` form or after a `split` with its equation). -/
macro "a3apre" : tactic => `(tactic| first
  | exact apre_bindLet _ _ _ _
  | exact apre_bindLetNamed _ _ _ _
  | exact apre_bindLetAlias _ _ _ _
  | exact apre_loopLet _ _ _ _
  | exact apre_letIndex _ _ _ _
  | exact apre_of_bindLet (by assumption)
  | exact apre_of_bindLetNamed (by assumption)
  | exact apre_of_bindLetAlias (by assumption)
  | exact apre_of_loopLet (by assumption)
  | exact apre_of_letIndex (by assumption)
  | exact apre_refl _)

/-- `machReserve` appends (`machReserve_some`, Tools/ShippingReaderLenOkReserve.lean:187-201). -/
theorem machReserve_ext {natOf : Lean.Expr → Option Nat} {dom' αs initsE body : Lean.Expr}
    {st : MachRead} {base : Nat} {st' : MachRead}
    (hr : machReserve natOf dom' αs initsE body st = some (base, st')) : PhExt st st' := by
  obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hr
  subst hst
  exact phExt_upd (phExt_refl st) (apre_append _ _) (apre_refl _) (apre_refl _)

/-- `machInstance`'s entry step. -/
theorem instEntry_ext {res : MixedGateBinder} {st st' : MachRead}
    (hr : instEntry res st = some st') : PhExt st st' := by
  cases res with
  | bits w =>
    have hr' : some st = some st' := hr
    injection hr' with hr1
    subst hr1
    exact phExt_refl _
  | bool =>
    have hr' : some { st with instStruct := true } = some st' := hr
    injection hr' with hr1
    subst hr1
    exact phExt_instStruct (phExt_refl st) true
  | domain =>
    have hr' : (none : Option MachRead) = some st' := hr
    cases hr'

/-! ## 2. `GoodE` (§3.7.3): UNCONDITIONAL, by fuel induction (pattern of `GoodH`, FuelR5:71-72) -/

/-- Every answered call only extends the three lookups `phKind` reads. -/
def GoodE (h : Hs) : Prop :=
  ∀ (c : Call) (v : c.Res), h c = some (some v) → PhExt (Call.inSt c) (Call.outSt c v)

/-- Every OK result of `x` (against `h`) has a state extending `st₀`. -/
abbrev SatE {α : Type} [HasSt α] (h : Hs) (st₀ : MachRead) (x : BM (Option α)) : Prop :=
  ∀ a, x.run h = some (some a) → PhExt st₀ (HasSt.st a)

section CombE
variable {h : Hs} {st₀ : MachRead} {α β : Type} [HasSt α]

theorem satE_pure {o : Option α} (ho : ∀ a, o = some a → PhExt st₀ (HasSt.st a)) :
    SatE h st₀ (FM.pure o) := by
  intro a ha
  rw [run_pure] at ha
  exact ho a (Option.some.inj ha)

theorem satE_okO {a : α} (ha : PhExt st₀ (HasSt.st a)) : SatE h st₀ (okO a) :=
  satE_pure fun b hb => by
    injection hb with hb1
    subst hb1
    exact ha

theorem satE_failO : SatE h st₀ (failO : BM (Option α)) :=
  satE_pure fun b hb => by cases hb

theorem satE_optK {o : Option β} {f : β → BM (Option α)} (hf : ∀ b, o = some b → SatE h st₀ (f b)) :
    SatE h st₀ (optK o f) := by
  cases o with
  | none => exact satE_failO
  | some b => exact hf b rfl

theorem satE_bindO [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} (hx : SatE h st₀ x)
    (hf : ∀ b, PhExt st₀ (HasSt.st b) → SatE h st₀ (f b)) : SatE h st₀ (bindO x f) := by
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b => exact hf b (hx b ho) a ha

theorem satE_bind {x : BM β} {f : β → BM (Option α)}
    (hf : ∀ r, x.run h = some r → SatE h st₀ (f r)) : SatE h st₀ (FM.bind x f) := by
  intro a ha
  rw [run_bind] at ha
  obtain ⟨r, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  exact hf r hr a ha

theorem satE_ite {c : Prop} [Decidable c] {x y : BM (Option α)} (hx : SatE h st₀ x) (hy : SatE h st₀ y) :
    SatE h st₀ (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx
  · rw [if_neg hc]
    exact hy

theorem satE_domGuard {o : Option Lean.Expr} {dom' : Lean.Expr} {k : BM (Option α)}
    (hk : SatE h st₀ k) : SatE h st₀ (domGuard o dom' k) := by
  cases o with
  | none => exact hk
  | some d0 =>
    first
      | exact satE_ite satE_failO hk
      | (simp only [domGuard]; exact satE_ite satE_failO hk)

theorem satE_pure_ite {c : Prop} [Decidable c] {a : α} (ha : PhExt st₀ (HasSt.st a)) :
    SatE h st₀ (FM.pure (if c then some a else none)) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact satE_okO ha
  · rw [if_neg hc]
    exact satE_failO

end CombE

theorem satE_foldO {σ α : Type} [HasSt σ] {h : Hs} {st₀ : MachRead} {f : σ → α → BM (Option σ)}
    (hf : ∀ s a, PhExt st₀ (HasSt.st s) → SatE h st₀ (f s a)) :
    ∀ (l : List α) (s : σ), PhExt st₀ (HasSt.st s) → SatE h st₀ (foldO f s l)
  | [], _, hs => satE_okO hs
  | a :: l, s, hs => satE_bindO (hf s a hs) (fun s' hs' => satE_foldO hf l s' hs')

theorem satE_findSomeO {α β : Type} [HasSt β] {h : Hs} {st₀ : MachRead} {f : α → BM (Option β)}
    (hf : ∀ a, SatE h st₀ (f a)) : ∀ (l : List α), SatE h st₀ (findSomeO f l)
  | [] => satE_failO
  | a :: l => by
    refine satE_bind ?_
    intro r hr
    cases r with
    | none => exact satE_findSomeO hf l
    | some b => exact satE_okO (hf a b hr)

section OutE
variable {h : Hs} {st₀ : MachRead}

theorem satE_cConv (hG : GoodE h) {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    (hx : PhExt st₀ st) : SatE h st₀ (cConv env d e st) :=
  fun q hq => phExt_trans hx (hG (Call.conv env d e st) q hq)

theorem satE_cNested (hG : GoodE h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} (hx : PhExt st₀ st) : SatE h st₀ (cNested env dom αs initsE body st) :=
  fun q hq => phExt_trans hx (hG (Call.nested env dom αs initsE body st) q hq)

theorem satE_cInst (hG : GoodE h) {env : List MachVal} {c : Name} {org : InstOrigin}
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr} {st : MachRead}
    (hx : PhExt st₀ st) : SatE h st₀ (cInst env c org kinds res args st) :=
  fun q hq => phExt_trans hx (hG (Call.inst env c org kinds res args st) q hq)

theorem satE_cInstS (hG : GoodE h) {env : List MachVal} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead} (hx : PhExt st₀ st) :
    SatE h st₀ (cInstS env c kinds ty args st) :=
  fun q hq => phExt_trans hx (hG (Call.instS env c kinds ty args st) q hq)

theorem satE_cChain (hG : GoodE h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hx : PhExt st₀ st) : SatE h st₀ (cChain env e st) :=
  fun q hq => phExt_trans hx (hG (Call.chain env e st) q hq)

theorem satE_cLoopBody (hG : GoodE h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} (hx : PhExt st₀ st) : SatE h st₀ (cLoopBody base env e st) :=
  fun q hq => phExt_trans hx (hG (Call.loopBody base env e st) q hq)

theorem satE_cLoopRoot (hG : GoodE h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hx : PhExt st₀ st) : SatE h st₀ (cLoopRoot env e st) :=
  fun q hq => phExt_trans hx (hG (Call.loopRoot env e st) q hq)

end OutE

/-- A `let (x, y) := p; k` continuation (as `r5pair`, FuelR5): `t` directly, or after splitting the pair `match`. -/
macro "a3pair " t:tactic : tactic => `(tactic| first
  | $t:tactic
  | (split <;> $t:tactic)
  | ((try dsimp only); split <;> $t:tactic)
  | ((try dsimp only); (repeat' split) <;> $t:tactic))

/-- A leaf `hr : o = some r` of a pure `Option` value, closed from the extension `h1` of the current state. -/
macro "a3leaf " hr:ident h1:ident : tactic => `(tactic| first
  | (cases $hr:ident; done)
  | (injection $hr:ident with hq; subst hq; exact $h1:ident)
  | (injection $hr:ident with hq; subst hq; exact phExt_dom $h1:ident _)
  | (injection $hr:ident with hq; subst hq; exact phExt_lets $h1:ident _ (by a3apre))
  | (injection $hr:ident with hq; subst hq; exact phExt_instPush $h1:ident _ _ _)
  | (cases $hr:ident; exact $h1:ident))

section HelpersE
variable {h : Hs} {st₀ : MachRead}

theorem instArg_satE (hG : GoodE h) (env : List MachVal) (k : Nat) :
    ∀ s a, PhExt st₀ (HasSt.st s) → SatE h st₀ (instArg env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hx : PhExt st₀ st)
  refine satE_bindO (satE_cConv hG hx) ?_
  rintro ⟨v', st1⟩ (h1 : PhExt st₀ st1)
  refine satE_pure ?_
  intro r hr
  repeat' split at hr
  all_goals a3leaf hr h1

theorem instSArg_satE (hG : GoodE h) (env : List MachVal) :
    ∀ s a, PhExt st₀ (HasSt.st s) → SatE h st₀ (instSArg env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hx : PhExt st₀ st)
  refine satE_bindO (satE_cConv hG hx) ?_
  rintro ⟨v', st1⟩ (h1 : PhExt st₀ st1)
  refine satE_pure ?_
  intro r hr
  repeat' split at hr
  all_goals a3leaf hr h1

theorem instSParam_satE (hG : GoodE h) (env : List MachVal) :
    ∀ s a, PhExt st₀ (HasSt.st s) → SatE h st₀ (instSParam env s a) := by
  rintro ⟨ps, st⟩ q (hx : PhExt st₀ st)
  refine satE_bindO (satE_cConv hG hx) ?_
  rintro ⟨q', st1⟩ (h1 : PhExt st₀ st1)
  refine satE_okO ?_
  exact h1

theorem loopNext_satE (hG : GoodE h) (env : List MachVal) (base : Nat) :
    ∀ s a, PhExt st₀ (HasSt.st s) → SatE h st₀ (loopNext env base s a) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩ (hx : PhExt st₀ st)
  refine satE_bindO (satE_cConv hG hx) ?_
  rintro ⟨nx', st1⟩ (h1 : PhExt st₀ st1)
  refine satE_okO ?_
  exact h1

theorem nestedProbe_satE (hG : GoodE h) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) (hx : PhExt st₀ st) : ∀ a, SatE h st₀ (nestedProbe env dom' αs initsE body st a) := by
  rintro ⟨base, d, a, ini, ws, v⟩
  refine satE_ite ?_ satE_failO
  refine satE_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact satE_failO
  · have h' : PhExt st₀ st' := satE_cChain hG hx (ws', v', st') hr
    refine satE_pure_ite ?_
    exact h'

theorem loopProbe_satE (hG : GoodE h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st : MachRead) (hx : PhExt st₀ st) : ∀ a, SatE h st₀ (loopProbe env body n st a) := by
  rintro ⟨b0, n0, ws0⟩
  refine satE_ite satE_failO ?_
  refine satE_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact satE_failO
  · have h' : PhExt st₀ st' := satE_cLoopBody hG (phExt_ws hx _) st' hr
    refine satE_pure_ite ?_
    exact phExt_ws h' _

end HelpersE

/-! ### The seven bodies (same order and splits as FuelR5:384-736) -/

section ArmsE
variable {h : Hs}

theorem conv_app_satE (senv : StructEnv) (hG : GoodE h) (env : List MachVal) (d : Nat)
    (f a : Lean.Expr) (st₀ st : MachRead) (hx : PhExt st₀ st) :
    SatE h st₀ (convStep senv env d (.app f a) st) := by
  first
    | simp only [convStep]
    | (unfold convStep; dsimp only)
  split
  · -- a bare `Signal.register`
    refine satE_ite satE_failO ?_
    split
    · refine satE_okO ?_
      exact hx
    · refine satE_optK ?_
      intro kind _
      refine satE_optK ?_
      intro initN _
      refine satE_bindO (satE_cConv hG hx) ?_
      rintro ⟨dom', st1⟩ (h1 : PhExt st₀ st1)
      refine satE_domGuard ?_
      refine satE_bindO (satE_cConv hG (phExt_bareRegister h1 _ _ _ _ _ _)) ?_
      rintro ⟨x', st2⟩ (h2 : PhExt st₀ st2)
      refine satE_okO ?_
      exact phExt_ws h2 _
  · split
    · -- a loop read
      refine satE_pure_ite ?_
      exact hx
    · split
      · -- a nested machine
        exact satE_ite satE_failO (satE_cNested hG hx)
      · split
        · -- an instance
          exact satE_ite satE_failO (satE_cInst hG hx)
        · split
          · -- a structure instance
            exact satE_ite satE_failO (satE_cInstS hG hx)
          · split
            · -- a memory
              refine satE_ite satE_failO (satE_bindO (satE_cInst hG hx) ?_)
              rintro ⟨v, st1⟩ (h1 : PhExt st₀ st1)
              refine satE_okO ?_
              exact phExt_instStruct h1 _
            · split
              · -- a state read
                refine satE_pure_ite ?_
                exact hx
              · -- an application
                refine satE_bindO (satE_cConv hG hx) ?_
                rintro ⟨f', st1⟩ (h1 : PhExt st₀ st1)
                refine satE_bindO (satE_cConv hG h1) ?_
                rintro ⟨a', st2⟩ (h2 : PhExt st₀ st2)
                refine satE_okO ?_
                exact h2

theorem conv_letE_satE (senv : StructEnv) (hG : GoodE h) (env : List MachVal) (d : Nat)
    (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st₀ st : MachRead) (hx : PhExt st₀ st) :
    SatE h st₀ (convStep senv env d (.letE nm ty v b nd) st) := by
  refine satE_ite satE_failO ?_
  split
  · exact satE_cConv hG hx
  · refine satE_ite ?_ ?_
    · refine satE_bindO (satE_cLoopRoot hG hx) ?_
      rintro ⟨mv, st1⟩ (h1 : PhExt st₀ st1)
      exact satE_cConv hG h1
    · split
      · exact satE_cConv hG hx
      · split
        · exact satE_cConv hG hx
        · refine satE_bindO (satE_cConv hG hx) ?_
          rintro ⟨v', st1⟩ (h1 : PhExt st₀ st1)
          a3pair (exact satE_cConv hG (phExt_lets h1 _ (by a3apre)))

theorem conv_satE (senv : StructEnv) (hG : GoodE h) (env : List MachVal) (d : Nat)
    (e : Lean.Expr) (st₀ st : MachRead) (hx : PhExt st₀ st) : SatE h st₀ (convStep senv env d e st) := by
  cases e
  case bvar j =>
    refine satE_pure ?_
    intro r hr
    show PhExt st₀ r.2
    rw [convBvar_st hr]
    exact hx
  case app f a => exact conv_app_satE senv hG env d f a st₀ st hx
  case letE nm ty v b nd => exact conv_letE_satE senv hG env d nm ty v b nd st₀ st hx
  case lam nm t b bi =>
    refine satE_bindO (satE_cConv hG hx) ?_
    rintro ⟨t', st1⟩ (h1 : PhExt st₀ st1)
    refine satE_bindO (satE_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : PhExt st₀ st2)
    refine satE_okO ?_
    exact h2
  case forallE nm t b bi =>
    refine satE_bindO (satE_cConv hG hx) ?_
    rintro ⟨t', st1⟩ (h1 : PhExt st₀ st1)
    refine satE_bindO (satE_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : PhExt st₀ st2)
    refine satE_okO ?_
    exact h2
  all_goals first
    | (refine satE_okO ?_; exact hx)
    | exact satE_failO

theorem nested_satE (senv : StructEnv) (hG : GoodE h) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st₀ st : MachRead) (hx : PhExt st₀ st) :
    SatE h st₀ (nestedStep senv env dom αs initsE body st) := by
  refine satE_ite satE_failO ?_
  refine satE_bindO (satE_cConv hG hx) ?_
  rintro ⟨dom', st1⟩ (h1 : PhExt st₀ st1)
  refine satE_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · refine satE_optK ?_
    rintro ⟨base, st2⟩ hres
    have h2 : PhExt st₀ st2 := phExt_trans h1 (machReserve_ext hres)
    refine satE_bindO (satE_cChain hG (phExt_inInner h2 _)) ?_
    rintro ⟨ws, v, st3⟩ (h3 : PhExt st₀ st3)
    refine satE_okO ?_
    exact phExt_nestedClose h3 _ _ _
  · refine satE_okO ?_
    exact satE_findSomeO (nestedProbe_satE hG _ _ _ _ _ _ h1) _ r hsh

theorem inst_satE (hG : GoodE h) (env : List MachVal) (c : Name) (org : InstOrigin)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr) (st₀ st : MachRead)
    (hx : PhExt st₀ st) : SatE h st₀ (instStep env c org kinds res args st) := by
  refine satE_optK ?_
  intro st1 hst1
  have h1 : PhExt st₀ st1 := phExt_trans hx (instEntry_ext hst1)
  refine satE_bindO (satE_foldO (instArg_satE hG env _) _ _ ?_) ?_
  · exact h1
  rintro ⟨js, st2⟩ (h2 : PhExt st₀ st2)
  refine satE_pure ?_
  intro r hr
  split at hr
  all_goals a3leaf hr h2

theorem instS_satE (senv : StructEnv) (hG : GoodE h) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st₀ st : MachRead)
    (hx : PhExt st₀ st) : SatE h st₀ (instSStep senv env c kinds ty args st) := by
  refine satE_ite satE_failO ?_
  refine satE_optK ?_
  intro resTy _
  refine satE_optK ?_
  intro r _
  obtain ⟨oc, fields⟩ := r
  cases oc with
  | none => exact satE_failO
  | some ctor =>
    refine satE_ite satE_failO ?_
    refine satE_bindO (satE_foldO (instSArg_satE hG env) _ _ ?_) ?_
    · exact hx
    rintro ⟨js, st1⟩ (h1 : PhExt st₀ st1)
    refine satE_bindO (satE_foldO (instSParam_satE hG env) _ _ ?_) ?_
    · exact h1
    rintro ⟨params, st2⟩ (h2 : PhExt st₀ st2)
    try dsimp only
    split
    · refine satE_okO ?_
      exact h2
    · refine satE_okO ?_
      exact phExt_instS h2 _ _ _ _

theorem chain_satE (senv : StructEnv) (hG : GoodE h) (env : List MachVal) (e : Lean.Expr)
    (st₀ st : MachRead) (hx : PhExt st₀ st) : SatE h st₀ (chainStep senv env e st) := by
  revert hx
  unfold chainStep
  split
  · intro hx
    refine satE_bindO (satE_cConv hG hx) ?_
    rintro ⟨v', st1⟩ (h1 : PhExt st₀ st1)
    refine satE_okO ?_
    exact h1
  · intro hx
    refine satE_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → PhExt st₀ b := by
      intro a b he
      subst he
      exact satE_cConv hG hx (a, b) hr
    revert hr'
    split
    · intro hr'
      have h1 := hr' _ _ rfl
      refine satE_ite ?_ satE_failO
      refine satE_bindO (satE_cChain hG h1) ?_
      rintro ⟨ws, v, st2⟩ (h2 : PhExt st₀ st2)
      refine satE_okO ?_
      exact h2
    · intro _
      exact satE_failO
  · intro hx
    split
    · exact satE_cChain hG hx
    · refine satE_ite ?_ ?_
      · refine satE_bindO (satE_cLoopRoot hG hx) ?_
        rintro ⟨mv, st1⟩ (h1 : PhExt st₀ st1)
        exact satE_cChain hG h1
      · split
        · exact satE_cChain hG hx
        · split
          · exact satE_cChain hG hx
          · refine satE_bindO (satE_cConv hG hx) ?_
            rintro ⟨v', st1⟩ (h1 : PhExt st₀ st1)
            a3pair (exact satE_cChain hG (phExt_lets h1 _ (by a3apre)))
  · intro _
    exact satE_failO

theorem loopBody_satE (hG : GoodE h) (base : Nat) (env : List MachVal) (e : Lean.Expr)
    (st₀ st : MachRead) (hx : PhExt st₀ st) : SatE h st₀ (loopBodyStep base env e st) := by
  cases e
  case letE nm ty v b nd =>
    refine satE_bindO (satE_cConv hG hx) ?_
    rintro ⟨v', st1⟩ (h1 : PhExt st₀ st1)
    a3pair (exact satE_cLoopBody hG (phExt_lets h1 _ (by a3apre)))
  all_goals
    unfold loopBodyStep
    try dsimp only
    refine satE_optK ?_
    intro regs _
    refine satE_bindO (satE_foldO (loopNext_satE hG _ _) _ _ ?_) ?_
    · exact hx
    rintro ⟨ws, st1⟩ (h1 : PhExt st₀ st1)
    refine satE_okO ?_
    exact phExt_ws h1 _

theorem loopRoot_satE (senv : StructEnv) (hG : GoodE h) (env : List MachVal) (e : Lean.Expr)
    (st₀ st : MachRead) (hx : PhExt st₀ st) : SatE h st₀ (loopRootStep senv env e st) := by
  unfold loopRootStep
  split
  · refine satE_ite satE_failO ?_
    refine satE_optK ?_
    intro regs _
    refine satE_ite satE_failO ?_
    refine satE_optK ?_
    intro kinds _
    refine satE_optK ?_
    intro inits _
    refine satE_bindO (satE_cConv hG hx) ?_
    rintro ⟨dom', st1⟩ (h1 : PhExt st₀ st1)
    refine satE_domGuard ?_
    refine satE_bind ?_
    intro shared hsh
    rcases shared with _ | ⟨b0, st2⟩
    · refine satE_bindO (satE_cLoopBody hG (phExt_loopRoot h1 _ _)) ?_
      rintro st3 (h3 : PhExt st₀ st3)
      refine satE_okO ?_
      exact phExt_loopClose h3 _ _
    · refine satE_okO ?_
      exact satE_findSomeO (loopProbe_satE hG _ _ _ _ h1) _ (b0, st2) hsh
  · exact satE_failO

end ArmsE

/-- One step keeps `GoodE`. -/
theorem step_goodE (senv : StructEnv) {h : Hs} (hG : GoodE h) :
    GoodE (fun c => (step senv c).run h) := by
  intro c v hv
  cases c with
  | conv env d e st => exact conv_satE senv hG env d e st st (phExt_refl st) v hv
  | nested env dom αs initsE body st =>
    exact nested_satE senv hG env dom αs initsE body st st (phExt_refl st) v hv
  | inst env c org kinds res args st =>
    exact inst_satE hG env c org kinds res args st st (phExt_refl st) v hv
  | instS env c kinds ty args st => exact instS_satE senv hG env c kinds ty args st st (phExt_refl st) v hv
  | chain env e st => exact chain_satE senv hG env e st st (phExt_refl st) v hv
  | loopBody base env e st => exact loopBody_satE hG base env e st st (phExt_refl st) v hv
  | loopRoot env e st => exact loopRoot_satE senv hG env e st st (phExt_refl st) v hv

/-- **`GoodE` of the fuel reader, for ALL fuels, UNCONDITIONAL** (§3.7.3 `goodE_readF`). -/
theorem goodE_readF (senv : StructEnv) : ∀ n, GoodE (readF senv n)
  | 0 => fun c v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => step_goodE senv (goodE_readF senv n)

/-! ## 3. Option (b) definitions (§3.7.3) -/

/-- What a reader value owes the source kind `k` of its binder. -/
def EntryKindOk (HK : PhKinding) (p : ShapePre) (st : MachRead) (k : MixedGateBinder) (m : MachVal) : Prop :=
  match m with
  | .val v     => HK (phKind p.bs st) v k
  | .state b n => n = 1 ∧ st.kinds[b]? = some k
  | .regs _    => True
  | .handle _  => True
  | .unit      => True

/-- Entry-indexed, `dom`-free environment invariant. -/
def EnvKindOkE (HK : PhKinding) (p : ShapePre) (st : MachRead) (Δ : SrcCtx) (env : List MachVal) (d : Nat) :
    Prop :=
  Δ.length = d + env.length ∧
  ∀ (j : Nat) (k : MixedGateBinder) (m : MachVal), d ≤ j → Δ[j]? = some (some k) → k ≠ .domain →
    env[j - d]? = some m → EntryKindOk HK p st k m

/-- rev3 `CallPreK`: rev2's text (A2:283-295) with `EnvKindOkE` in all seven rows. -/
def CallPreKE (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Call → Prop
  | Call.conv env d e st => ∃ Δ, EnvKindOkE HK p st Δ env d ∧ ReadSub senv (midExpr en) Δ e
  | Call.nested env dom αs initsE body st => ∃ Δ e, EnvKindOkE HK p st Δ env 0 ∧
      ReadSub senv (midExpr en) Δ e ∧ machRunApp? e = some (dom, αs, initsE, body)
  | Call.inst env c org ks res args st => CallPreP senv (Call.inst env c org ks res args st) ∧
      ∃ Δ e, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧ InstSite senv e org c ks res args
  | Call.instS env c ks ty args st => senv.instS c = some (ks, ty) ∧
      ∃ Δ e, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧
        machInstCallS? senv e = some (c, ks, ty, args)
  | Call.chain env e st => ∃ Δ, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopBody _ env e st => ∃ Δ, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopRoot env e st => ∃ Δ, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e

/-- `GoodK`'s rev2 shape (A2:297-299) over `CallPreKE`. -/
def GoodKE (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (h : Hs) : Prop :=
  ∀ c, CallPreKE HK senv p en c → ReadInv HK senv p (Call.inSt c) → ∀ v, h c = some (some v) →
    ReadInv HK senv p (Call.outSt c v)

/-! ## 4. E lemmas -/

/-- **E ⇒ rev2 `EnvKindOk`** (ONE direction; `.state b 1`: `HKL.var` at the slot placeholder + `phKind_slot`). -/
theorem envKindOk_of_E {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx} {env : List MachVal}
    {d : Nat} (HKL : PhKindingLaws HK) :
    EnvKindOkE HK p st Δ env d → EnvKindOk HK p st Δ env d := by
  rintro ⟨hlen, hk⟩
  refine ⟨hlen, ?_⟩
  intro j k x st' hdj hjl hΔ hk0 hc
  have hjd : j - d < env.length := by omega
  have hm : env[j - d]? = some (env[j - d]'hjd) := List.getElem?_eq_getElem hjd
  have hE := hk j k (env[j - d]'hjd) hdj hΔ hk0 hm
  have hlt : ¬ j < d := by omega
  unfold convBvar at hc
  rw [if_neg hlt, hm] at hc
  generalize env[j - d]'hjd = m at hE hc
  cases m with
  | val v =>
    have hc' : some (v, st) = some (x, st') := hc
    obtain ⟨hx, -⟩ := Prod.mk.inj (Option.some.inj hc')
    subst hx
    exact hE
  | state b n =>
    obtain ⟨hn, hkb⟩ := hE
    subst hn
    have hc' : some (machSlot b, st) = some (x, st') := hc
    obtain ⟨hx, -⟩ := Prod.mk.inj (Option.some.inj hc')
    subst hx
    exact (HKL.var (phKind p.bs st) (machSlot b) k (Or.inr ⟨_, rfl⟩)).mpr
      ((phKind_slot p.bs st b).trans hkb)
  | regs q =>
    first
      | (have hc' : (none : Option (Lean.Expr × MachRead)) = some (x, st') := hc
         cases hc')
      | (simp at hc)
  | handle i =>
    first
      | (have hc' : (none : Option (Lean.Expr × MachRead)) = some (x, st') := hc
         cases hc')
      | (simp at hc)
  | unit =>
    first
      | (have hc' : (none : Option (Lean.Expr × MachRead)) = some (x, st') := hc
         cases hc')
      | (simp at hc)

theorem entryKindOk_ext {HK : PhKinding} {p : ShapePre} {st st₁ : MachRead} (HKL : PhKindingLaws HK)
    (hx : PhExt st st₁) (k : MixedGateBinder) :
    ∀ m : MachVal, EntryKindOk HK p st k m → EntryKindOk HK p st₁ k m
  | .val v, hm => HKL.mono (phKind p.bs st) (phKind p.bs st₁) v k (fun _ _ hk => phKind_ext hx hk) hm
  | .state b n, hm => by
    obtain ⟨h1, h2⟩ := hm
    exact ⟨h1, hx.1 b k h2⟩
  | .regs _, _ => trivial
  | .handle _, _ => trivial
  | .unit, _ => trivial

/-- Along a state extension (`HKL.mono` + `phKind_ext`; `PhExt.1` for slots). -/
theorem envKindOkE_ext {HK : PhKinding} {p : ShapePre} {st st₁ : MachRead} {Δ : SrcCtx}
    {env : List MachVal} {d : Nat} (HKL : PhKindingLaws HK) :
    EnvKindOkE HK p st Δ env d → PhExt st st₁ → EnvKindOkE HK p st₁ Δ env d := by
  rintro ⟨hlen, hk⟩ hx
  refine ⟨hlen, ?_⟩
  intro j k m hdj hΔ hk0 hm
  exact entryKindOk_ext HKL hx k m (hk j k m hdj hΔ hk0 hm)

/-- Under a binder (the G9 body at depth `d + 1`). -/
theorem envKindOkE_lift {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx} {env : List MachVal}
    {d : Nat} (o : Option MixedGateBinder) :
    EnvKindOkE HK p st Δ env d → EnvKindOkE HK p st (o :: Δ) env (d + 1) := by
  rintro ⟨hlen, hk⟩
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · intro j k m hdj hΔ hk0 hm
    cases j with
    | zero => exact absurd hdj (by omega)
    | succ j =>
      have hΔ' : Δ[j]? = some (some k) := by simpa using hΔ
      have hm' : env[j - d]? = some m := by simpa using hm
      exact hk j k m (by omega) hΔ' hk0 hm'

/-- A new outermost env entry with its obligation. -/
theorem envKindOkE_cons {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx} {env : List MachVal}
    (o : Option MixedGateBinder) (m : MachVal)
    (hm : ∀ k, o = some k → k ≠ .domain → EntryKindOk HK p st k m) :
    EnvKindOkE HK p st Δ env 0 → EnvKindOkE HK p st (o :: Δ) (m :: env) 0 := by
  rintro ⟨hlen, hk⟩
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · intro j k m' _ hΔ hk0 hm'
    cases j with
    | zero =>
      have ho : o = some k := by simpa using hΔ
      have hmm : m = m' := by simpa using hm'
      subst hmm
      exact hm k ho hk0
    | succ j =>
      have hΔ' : Δ[j]? = some (some k) := by simpa using hΔ
      have hm'' : env[j - 0]? = some m' := by simpa using hm'
      exact hk j k m' (Nat.zero_le j) hΔ' hk0 hm''

/-- Hoare combinator for a second call (replaces `satK_bindO` where the continuation needs `st₁`). Note (review of
88858249): the environment transport is carried by `hxE`; `hE` is currently unused in the proof, so this does NOT say
that `GoodE` alone extends an arbitrary `x`. -/
theorem satK_bindOE {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs} {α β : Type} [HasSt α]
    [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} {st : MachRead} (hE : GoodE h)
    (hx : SatK HK senv p h x) (hxE : ∀ b, x.run h = some (some b) → PhExt st (HasSt.st b))
    (hf : ∀ b, StK HK senv p b → PhExt st (HasSt.st b) → SatK HK senv p h (f b)) :
    SatK HK senv p h (bindO x f) := by
  have _hE := hE
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b => exact hf b (hx b ho) (hxE b ho) a ha

/-! ### Call combinators (E) -/

section CallsE
variable {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}

theorem satK_cConvE (hG : GoodKE HK senv p en h) {env : List MachVal} {d : Nat} {e : Lean.Expr}
    {st : MachRead} (hpre : CallPreKE HK senv p en (Call.conv env d e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (cConv env d e st) :=
  fun a ha => hG (Call.conv env d e st) hpre hst a ha

theorem satK_cChainE (hG : GoodKE HK senv p en h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (cChain env e st) :=
  fun a ha => hG (Call.chain env e st) hpre hst a ha

theorem cConv_phExt (hE : GoodE h) {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead} :
    ∀ b, (cConv env d e st).run h = some (some b) → PhExt st (HasSt.st b) :=
  fun b hb => hE (Call.conv env d e st) b hb

theorem cChain_phExt (hE : GoodE h) {env : List MachVal} {e : Lean.Expr} {st : MachRead} :
    ∀ b, (cChain env e st).run h = some (some b) → PhExt st (HasSt.st b) :=
  fun b hb => hE (Call.chain env e st) b hb

end CallsE

/-! ### `ReadInv` + extension, as one Hoare predicate (for folds) -/

/-- Every OK result keeps `ReadInv` and extends `st₀`. -/
abbrev SatKX {α : Type} [HasSt α] (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (h : Hs)
    (st₀ : MachRead) (x : BM (Option α)) : Prop :=
  ∀ a, x.run h = some (some a) → ReadInv HK senv p (HasSt.st a) ∧ PhExt st₀ (HasSt.st a)

section CombX
variable {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs} {st₀ : MachRead} {α β : Type} [HasSt α]

theorem satK_of_X {x : BM (Option α)} (hx : SatKX HK senv p h st₀ x) : SatK HK senv p h x :=
  fun a ha => (hx a ha).1

theorem satKX_pure {o : Option α}
    (ho : ∀ a, o = some a → ReadInv HK senv p (HasSt.st a) ∧ PhExt st₀ (HasSt.st a)) :
    SatKX HK senv p h st₀ (FM.pure o) := by
  intro a ha
  rw [run_pure] at ha
  exact ho a (Option.some.inj ha)

theorem satKX_okO {a : α} (hs : ReadInv HK senv p (HasSt.st a)) (hx : PhExt st₀ (HasSt.st a)) :
    SatKX HK senv p h st₀ (okO a) :=
  satKX_pure fun b hb => by
    injection hb with hb1
    subst hb1
    exact ⟨hs, hx⟩

theorem satKX_bindO [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)}
    (hx : SatKX HK senv p h st₀ x)
    (hf : ∀ b, ReadInv HK senv p (HasSt.st b) → PhExt st₀ (HasSt.st b) → SatKX HK senv p h st₀ (f b)) :
    SatKX HK senv p h st₀ (bindO x f) := by
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b => exact hf b (hx b ho).1 (hx b ho).2 a ha

theorem satK_optK {o : Option β} {f : β → BM (Option α)} (hf : ∀ b, o = some b → SatK HK senv p h (f b)) :
    SatK HK senv p h (optK o f) := by
  cases o with
  | none => exact satK_failO
  | some b => exact hf b rfl

theorem satK_bind {x : BM β} {f : β → BM (Option α)} (hf : ∀ r, x.run h = some r → SatK HK senv p h (f r)) :
    SatK HK senv p h (FM.bind x f) := by
  intro a ha
  rw [run_bind] at ha
  obtain ⟨r, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  exact hf r hr a ha

end CombX

theorem satKX_foldO {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs} {st₀ : MachRead}
    {σ α : Type} [HasSt σ] {f : σ → α → BM (Option σ)} (P : α → Prop)
    (hf : ∀ s a, P a → ReadInv HK senv p (HasSt.st s) → PhExt st₀ (HasSt.st s) →
      SatKX HK senv p h st₀ (f s a)) :
    ∀ (l : List α), (∀ a ∈ l, P a) → ∀ (s : σ), ReadInv HK senv p (HasSt.st s) → PhExt st₀ (HasSt.st s) →
      SatKX HK senv p h st₀ (foldO f s l)
  | [], _, _, hs, hx => satKX_okO hs hx
  | a :: l, hl, s, hs, hx =>
    satKX_bindO (hf s a (hl a (by simp)) hs hx)
      (fun s' hs' hx' => satKX_foldO P hf l (fun b hb => hl b (by simp [hb])) s' hs' hx')

theorem satKX_cConv {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    {st₀ : MachRead} (hG : GoodKE HK senv p en h) (hE : GoodE h) {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st : MachRead} (hpre : CallPreKE HK senv p en (Call.conv env d e st))
    (hs : ReadInv HK senv p st) (hx : PhExt st₀ st) : SatKX HK senv p h st₀ (cConv env d e st) :=
  fun q hq => ⟨hG (Call.conv env d e st) hpre hs q hq, phExt_trans hx (hE (Call.conv env d e st) q hq)⟩

/-- `ReadInv` of a state with the same lets / call entries / tags and extended lookups. -/
theorem readInv_congr {HK : PhKinding} {senv : StructEnv} {p : ShapePre} (HKL : PhKindingLaws HK)
    {st st' : MachRead} (h : ReadInv HK senv p st) (hx : PhExt st st') (hl : st'.lets = st.lets)
    (hi : st'.insts = st.insts) (hf : st'.instFields = st.instFields)
    (ho : st'.instOrigins = st.instOrigins) (hs : st'.instStruct = st.instStruct) :
    ReadInv HK senv p st' := by
  obtain ⟨hP, hL, hA⟩ := h
  refine ⟨?_, letKindOk_sameLets HKL hL hx hl, ?_⟩
  · unfold InstProv at hP ⊢
    rw [hi, hf, ho, hs]
    exact hP
  · intro k c js r kinds hk hsk
    rw [hi] at hk
    have hsk' : SigKindsSt senv st k c kinds := by
      unfold SigKindsSt at hsk ⊢
      rw [ho] at hsk
      exact hsk
    rw [hl]
    exact hA k c js r kinds hk hsk'

theorem readInv_ws {HK : PhKinding} {senv : StructEnv} {p : ShapePre} (HKL : PhKindingLaws HK)
    {st : MachRead} (h : ReadInv HK senv p st) (ws : Array (Nat × Lean.Expr)) :
    ReadInv HK senv p { st with ws := ws } :=
  readInv_congr HKL h (phExt_ws (phExt_refl st) ws) rfl rfl rfl rfl rfl

/-! ### Loop registers are reader inputs (pattern of `loopRegs_ok`, Tools/ShippingLetsReaderInvPure.lean:35-64) -/

theorem readSub_loopReg {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {a : Lean.Expr}
    {q : Lean.Expr × Lean.Expr × Lean.Expr} (ha : ReadSub senv r Δ a) (h : machLoopReg? a = some q) :
    ReadSub senv r Δ q.2.2 := by
  unfold machLoopReg? at h
  split at h
  · injection h with h
    subst h
    exact ReadSub.appA ha
  · cases h

theorem readSub_loopRegs {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} :
    ∀ (e : Lean.Expr) (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)),
      ReadSub senv r Δ e → machLoopRegs e = some regs → ∀ q ∈ regs, ReadSub senv r Δ q.2.2 := by
  intro e
  induction e with
  | app f b ihf ihb =>
    intro regs he h
    unfold machLoopRegs at h
    split at h
    · rename_i heq
      injection heq with hf hb
      subst hf
      subst hb
      try simp only [Option.bind_eq_bind] at h
      obtain ⟨q0, hq0, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs, hrs, h⟩ := Option.bind_eq_some_iff.mp h
      injection h with h
      subst h
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact readSub_loopReg (ReadSub.appA (ReadSub.appF he)) hq0
      · exact ihb rs (ReadSub.appA he) hrs q hq
    · obtain ⟨q0, hq0, h⟩ := Option.map_eq_some_iff.mp h
      subst h
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact readSub_loopReg he hq0
  | _ =>
    intro regs he h
    simp only [machLoopRegs] at h
    obtain ⟨q0, hq0, h⟩ := Option.map_eq_some_iff.mp h
    subst h
    intro q hq
    rw [List.mem_singleton.mp hq]
    exact readSub_loopReg he hq0

/-! ## 5. Migrated closed arms (batch 2 → E; same proofs) -/

/-- **G1** (unchanged: no call, no env obligation). -/
theorem satKE_conv_bvar {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d j : Nat} {st : MachRead} (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.bvar j) st) :=
  satK_conv_bvar hst

/-- **G15** (`.mdata`, FAIL). -/
theorem satKE_conv_mdata {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {md : MData} {x : Lean.Expr} {st : MachRead} :
    SatK HK senv p h (convStep senv env d (.mdata md x) st) :=
  satK_conv_mdata

/-- **G15** (`.proj`, FAIL). -/
theorem satKE_conv_proj {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {s : Name} {i : Nat} {x : Lean.Expr} {st : MachRead} :
    SatK HK senv p h (convStep senv env d (.proj s i x) st) :=
  satK_conv_proj

theorem callPreKE_conv_float {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead}
    {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st)) (hd : d = 0)
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2) :
    CallPreKE HK senv p en
      (Call.conv env 0 (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st) := by
  subst hd
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨Δ, hE, ReadSub.float hR hf⟩

theorem callPreKE_conv_letRegs {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead} {q : Nat}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st)) (hd : d = 0) :
    CallPreKE HK senv p en (Call.conv (.regs q :: env) 0 b st) := by
  subst hd
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨_, envKindOkE_cons (mixedGateBinderKind? ty) (.regs q) (fun _ _ _ => trivial) hE, ReadSub.letB hR⟩

theorem callPreKE_conv_letHandle {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead} {i : Nat}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st)) (hd : d = 0) :
    CallPreKE HK senv p en (Call.conv (.handle i :: env) 0 b st) := by
  subst hd
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨_, envKindOkE_cons (mixedGateBinderKind? ty) (.handle i) (fun _ _ _ => trivial) hE, ReadSub.letB hR⟩

theorem callPreKE_chain_float {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead}
    {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hpre : CallPreKE HK senv p en (Call.chain env (.letE nm ty v b nd) st))
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2) :
    CallPreKE HK senv p en
      (Call.chain env (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st) := by
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨Δ, hE, ReadSub.float hR hf⟩

theorem callPreKE_chain_letRegs {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead} {q : Nat}
    (hpre : CallPreKE HK senv p en (Call.chain env (.letE nm ty v b nd) st)) :
    CallPreKE HK senv p en (Call.chain (.regs q :: env) b st) := by
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨_, envKindOkE_cons (mixedGateBinderKind? ty) (.regs q) (fun _ _ _ => trivial) hE, ReadSub.letB hR⟩

theorem callPreKE_chain_letHandle {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    {env : List MachVal} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead} {i : Nat}
    (hpre : CallPreKE HK senv p en (Call.chain env (.letE nm ty v b nd) st)) :
    CallPreKE HK senv p en (Call.chain (.handle i :: env) b st) := by
  obtain ⟨Δ, hE, hR⟩ := hpre
  exact ⟨_, envKindOkE_cons (mixedGateBinderKind? ty) (.handle i) (fun _ _ _ => trivial) hE, ReadSub.letB hR⟩

/-- **G10** (E). -/
theorem satKE_conv_letFloat {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h) {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool}
    {st : MachRead} (hpre : CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st))
    (hst : ReadInv HK senv p st) {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2) :
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine satK_ite2 (fun _ => satK_failO) ?_
  intro hd0
  have hd : d = 0 := eq_zero_of_not_bne hd0
  split
  · exact satK_cConvE hG (callPreKE_conv_float hpre hd ‹_›) hst
  · exfalso
    first
      | (rename_i hne; exact hne _ _ _ _ _ hf)
      | simp_all

/-- **G13** (E, `.regs`). -/
theorem satKE_conv_letRegs {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h) {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool}
    {st : MachRead} (hpre : CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st))
    (hst : ReadInv HK senv p st)
    (hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2)
    (hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false)
    {q : Nat} (hq : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some q) :
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine satK_ite2 (fun _ => satK_failO) ?_
  intro hd0
  have hd : d = 0 := eq_zero_of_not_bne hd0
  split
  · exfalso
    first
      | exact hnf _ _ _ _ _ ‹_›
      | simp_all
  · refine satK_ite2 (fun hc => ?_) (fun _ => ?_)
    · exfalso
      first
        | exact bool_false_true hc hnl
        | (rw [hnl] at hc; cases hc)
        | simp_all
    · split
      · exact satK_cConvE hG (callPreKE_conv_letRegs hpre hd) hst
      · exfalso
        first
          | (have hn : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none := ‹_›
             rw [hq] at hn
             cases hn)
          | simp_all

/-- **G13** (E, `.handle`). -/
theorem satKE_conv_letHandle {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h) {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool}
    {st : MachRead} (hpre : CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st))
    (hst : ReadInv HK senv p st)
    (hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2)
    (hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false)
    (hq0 : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none)
    {i : Nat} (hi : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some i) :
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine satK_ite2 (fun _ => satK_failO) ?_
  intro hd0
  have hd : d = 0 := eq_zero_of_not_bne hd0
  split
  · exfalso
    first
      | exact hnf _ _ _ _ _ ‹_›
      | simp_all
  · refine satK_ite2 (fun hc => ?_) (fun _ => ?_)
    · exfalso
      first
        | exact bool_false_true hc hnl
        | (rw [hnl] at hc; cases hc)
        | simp_all
    · split
      · exfalso
        first
          | (have hn : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some _ := ‹_›
             rw [hq0] at hn
             cases hn)
          | simp_all
      · split
        · exact satK_cConvE hG (callPreKE_conv_letHandle hpre hd) hst
        · exfalso
          first
            | (have hn : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none := ‹_›
               rw [hi] at hn
               cases hn)
            | simp_all

/-- **G16, `pure'` sub-arm** (E). -/
theorem satKE_chain_pure {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {us : List Level} {a1 a2 a3 x : Lean.Expr}
    (he : e = .app (.app (.app (.app (.const ``Sparkle.Core.Circuit.pure' us) a1) a2) a3) x)
    (hpre : CallPreKE HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert he hpre
  unfold chainStep
  split
  · intro _ hpre
    obtain ⟨Δ, hE, hR⟩ := hpre
    refine satK_bindO (satK_cConvE hG ⟨Δ, hE, ReadSub.appA hR⟩ hst) ?_
    rintro ⟨v', st1⟩ h1
    exact satK_okO h1
  · intro he
    cases he
  · intro he
    cases he
  · intro _ _
    exact satK_failO

/-- **G17, float sub-arm** (E). -/
theorem satKE_chain_letFloat {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h) {env : List MachVal} {e : Lean.Expr} {nm : Name} {ty v b : Lean.Expr}
    {nd : Bool} {st : MachRead} (he : e = .letE nm ty v b nd)
    (hpre : CallPreKE HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st)
    {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert he hpre
  unfold chainStep
  split
  · intro he
    cases he
  · intro he
    cases he
  · intro he hpre
    injection he with e1 e2 e3 e4 e5
    subst e1
    subst e2
    subst e3
    subst e4
    subst e5
    split
    · exact satK_cChainE hG (callPreKE_chain_float hpre ‹_›) hst
    · exfalso
      first
        | (rename_i hne; exact hne _ _ _ _ _ hf)
        | simp_all
  · intro _ _
    exact satK_failO

/-- **G17, `.regs` sub-arm** (E). -/
theorem satKE_chain_letRegs {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h) {env : List MachVal} {e : Lean.Expr} {nm : Name} {ty v b : Lean.Expr}
    {nd : Bool} {st : MachRead} (he : e = .letE nm ty v b nd)
    (hpre : CallPreKE HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st)
    (hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2)
    (hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false)
    {q : Nat} (hq : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some q) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert he hpre
  unfold chainStep
  split
  · intro he
    cases he
  · intro he
    cases he
  · intro he hpre
    injection he with e1 e2 e3 e4 e5
    subst e1
    subst e2
    subst e3
    subst e4
    subst e5
    split
    · exfalso
      first
        | exact hnf _ _ _ _ _ ‹_›
        | simp_all
    · refine satK_ite2 (fun hc => ?_) (fun _ => ?_)
      · exfalso
        first
          | exact bool_false_true hc hnl
          | (rw [hnl] at hc; cases hc)
          | simp_all
      · split
        · exact satK_cChainE hG (callPreKE_chain_letRegs hpre) hst
        · exfalso
          first
            | (have hn : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat _) = none := ‹_›
               rw [hq] at hn
               cases hn)
            | simp_all
  · intro _ _
    exact satK_failO

/-- **G17, `.handle` sub-arm** (E). -/
theorem satKE_chain_letHandle {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h) {env : List MachVal} {e : Lean.Expr} {nm : Name} {ty v b : Lean.Expr}
    {nd : Bool} {st : MachRead} (he : e = .letE nm ty v b nd)
    (hpre : CallPreKE HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st)
    (hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2)
    (hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false)
    (hq0 : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none)
    {i : Nat} (hi : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some i) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert he hpre
  unfold chainStep
  split
  · intro he
    cases he
  · intro he
    cases he
  · intro he hpre
    injection he with e1 e2 e3 e4 e5
    subst e1
    subst e2
    subst e3
    subst e4
    subst e5
    split
    · exfalso
      first
        | exact hnf _ _ _ _ _ ‹_›
        | simp_all
    · refine satK_ite2 (fun hc => ?_) (fun _ => ?_)
      · exfalso
        first
          | exact bool_false_true hc hnl
          | (rw [hnl] at hc; cases hc)
          | simp_all
      · split
        · exfalso
          first
            | (have hn : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat _) = some _ := ‹_›
               rw [hq0] at hn
               cases hn)
            | simp_all
        · split
          · exact satK_cChainE hG (callPreKE_chain_letHandle hpre) hst
          · exfalso
            first
              | (have hn : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat _) = none := ‹_›
                 rw [hi] at hn
                 cases hn)
              | simp_all
  · intro _ _
    exact satK_failO

/-! ## 6. Arms option (b) unblocks (second call at the state returned by the first) -/

/-- **G9** (conv `.lam`, FD:353-356): second call at `d + 1` under `envKindOkE_lift` + `envKindOkE_ext`. -/
theorem satKE_conv_lam {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.lam nm t b bi) st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.lam nm t b bi) st) := by
  obtain ⟨Δ, hEnv, hR⟩ := hpre
  have hpre1 : CallPreKE HK senv p en (Call.conv env d t st) := ⟨Δ, hEnv, ReadSub.lamT hR⟩
  refine satK_bindOE hE (satK_cConvE hG hpre1 hst) (cConv_phExt hE) ?_
  rintro ⟨t', st1⟩ (h1 : ReadInv HK senv p st1) (hx1 : PhExt st st1)
  have hpre2 : CallPreKE HK senv p en (Call.conv env (d + 1) b st1) :=
    ⟨_, envKindOkE_ext HKL (envKindOkE_lift (mixedGateBinderKind? t) hEnv) hx1, ReadSub.lamB hR⟩
  refine satK_bindO (satK_cConvE hG hpre2 h1) ?_
  rintro ⟨b', st2⟩ h2
  exact satK_okO h2

/-- **G9** (conv `.forallE`, FD:357-360). -/
theorem satKE_conv_forallE {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.forallE nm t b bi) st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.forallE nm t b bi) st) := by
  obtain ⟨Δ, hEnv, hR⟩ := hpre
  have hpre1 : CallPreKE HK senv p en (Call.conv env d t st) := ⟨Δ, hEnv, ReadSub.allT hR⟩
  refine satK_bindOE hE (satK_cConvE hG hpre1 hst) (cConv_phExt hE) ?_
  rintro ⟨t', st1⟩ (h1 : ReadInv HK senv p st1) (hx1 : PhExt st st1)
  have hpre2 : CallPreKE HK senv p en (Call.conv env (d + 1) b st1) :=
    ⟨_, envKindOkE_ext HKL (envKindOkE_lift (mixedGateBinderKind? t) hEnv) hx1, ReadSub.allB hR⟩
  refine satK_bindO (satK_cConvE hG hpre2 h1) ?_
  rintro ⟨b', st2⟩ h2
  exact satK_okO h2

/-- **G8** (conv generic application, FD:349-352): both calls; no push. The six recognisers before it fail. -/
theorem satKE_conv_app_generic {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st)
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none) (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = none) (h5 : machInstCallS? senv (.app f a) = none)
    (h6 : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e)
      (.app f a) = none)
    (h7 : machReadV env d (.app f a) = none) :
    SatK HK senv p h (convStep senv env d (.app f a) st) := by
  obtain ⟨Δ, hEnv, hR⟩ := hpre
  have hpre1 : CallPreKE HK senv p en (Call.conv env d f st) := ⟨Δ, hEnv, ReadSub.appF hR⟩
  first
    | simp only [convStep, h1, h2, h3, h4, h5, h6, h7]
    | (unfold convStep; dsimp only; simp only [h1, h2, h3, h4, h5, h6, h7])
  refine satK_bindOE hE (satK_cConvE hG hpre1 hst) (cConv_phExt hE) ?_
  rintro ⟨f', st1⟩ (hs1 : ReadInv HK senv p st1) (hx1 : PhExt st st1)
  have hpre2 : CallPreKE HK senv p en (Call.conv env d a st1) :=
    ⟨Δ, envKindOkE_ext HKL hEnv hx1, ReadSub.appA hR⟩
  refine satK_bindO (satK_cConvE hG hpre2 hs1) ?_
  rintro ⟨a', st2⟩ hs2
  exact satK_okO hs2

/-- **G16 `next`** (chain, FD:500-510): `rhs` at `st`, then `rest` under the `.unit` entry at the returned state. -/
theorem satKE_chain_next {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {us vs : List Level} {a1 a2 a3 a4 b1 b2 b3 b4 hh rhs t rest : Lean.Expr} {n : Name} {bi : BinderInfo}
    (he : e = .app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.bind us) a1) a2) a3) a4)
      (.app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.next vs) b1) b2) b3) b4) hh) rhs))
      (.lam n t rest bi))
    (hpre : CallPreKE HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert he hpre
  unfold chainStep
  split
  · intro he
    cases he
  · intro _ hpre
    obtain ⟨Δ, hEnv, hR⟩ := hpre
    refine satK_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → ReadInv HK senv p b ∧ PhExt st b := by
      intro a b hrab
      subst hrab
      exact ⟨satK_cConvE hG ⟨Δ, hEnv, ReadSub.appA (ReadSub.appA (ReadSub.appF hR))⟩ hst (a, b) hr,
        cConv_phExt hE (a, b) hr⟩
    revert hr'
    split
    · intro hr'
      obtain ⟨h1, hx1⟩ := hr' _ _ rfl
      refine satK_ite2 (fun _ => ?_) (fun _ => satK_failO)
      refine satK_bindO (satK_cChainE hG ⟨_, envKindOkE_cons _ MachVal.unit (fun _ _ _ => trivial)
        (envKindOkE_ext HKL hEnv hx1), ReadSub.lamB (ReadSub.appA hR)⟩ h1) ?_
      rintro ⟨ws, v, st2⟩ h2
      exact satK_okO h2
    · intro _
      exact satK_failO
  · intro he
    cases he
  · intro _ _
    exact satK_failO

/-- One `instSParam` step (FD:457-460): the parameter at the current state, `envKindOkE_ext`. -/
theorem satKX_instSParam {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {Δ : SrcCtx} {st₀ : MachRead} (hEnv : EnvKindOkE HK p st₀ Δ env 0) :
    ∀ (s : List Lean.Expr × MachRead) (q : Lean.Expr), ReadSub senv (midExpr en) Δ q →
      ReadInv HK senv p (HasSt.st s) → PhExt st₀ (HasSt.st s) →
      SatKX HK senv p h st₀ (instSParam env s q) := by
  rintro ⟨ps, st⟩ q hq (hs : ReadInv HK senv p st) (hx : PhExt st₀ st)
  refine satKX_bindO (satKX_cConv hG hE ⟨Δ, envKindOkE_ext HKL hEnv hx, hq⟩ hs hx) ?_
  rintro ⟨q', st1⟩ hs1 hx1
  exact satKX_okO hs1 hx1

/-- **G7** (`instSParam` fold of `instSStep`, FD:474): every parameter of the CONSTRUCTED `instRes ty args` is a
reader input by `ReadSub.sparam` (the kept call site) and is converted at its own (extended) state. -/
theorem satKE_instSParamFold {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {c : Name} {ks : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    {st₀ : MachRead} {resTy : Lean.Expr}
    (hpre : CallPreKE HK senv p en (Call.instS env c ks ty args st₀)) (hres : instRes ty args = some resTy)
    {ps : List Lean.Expr} {st : MachRead} (hs : ReadInv HK senv p st) (hx : PhExt st₀ st) :
    SatKX HK senv p h st₀ (foldO (instSParam env) (ps, st) resTy.getAppArgs.toList) := by
  obtain ⟨_, Δ, e, hEnv, hR, hS⟩ := hpre
  exact satKX_foldO (fun q => ReadSub senv (midExpr en) Δ q) (satKX_instSParam HKL hG hE hEnv)
    resTy.getAppArgs.toList (fun q hq => ReadSub.sparam hR hS hres hq) (ps, st) hs hx

/-- One `loopNext` step (FD:532-536). -/
theorem satKX_loopNext {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {base : Nat} {Δ : SrcCtx} {st₀ : MachRead} (hEnv : EnvKindOkE HK p st₀ Δ env 0) :
    ∀ (s : List (Nat × Lean.Expr) × MachRead) (r : Lean.Expr × Lean.Expr × Lean.Expr),
      ReadSub senv (midExpr en) Δ r.2.2 → ReadInv HK senv p (HasSt.st s) → PhExt st₀ (HasSt.st s) →
      SatKX HK senv p h st₀ (loopNext env base s r) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩ hq (hs : ReadInv HK senv p st) (hx : PhExt st₀ st)
  refine satKX_bindO (satKX_cConv hG hE ⟨Δ, envKindOkE_ext HKL hEnv hx, hq⟩ hs hx) ?_
  rintro ⟨nx', st1⟩ hs1 hx1
  exact satKX_okO hs1 hx1

/-- **G19** (loopBody tail, FD:546-549): the `loopNext` fold (each `next` at its own state) and the `ws` append. -/
theorem satKE_loopBody_tail {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {base : Nat} {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hne : ∀ (nm : Name) (ty v b : Lean.Expr) (nd : Bool), e ≠ .letE nm ty v b nd)
    (hpre : CallPreKE HK senv p en (Call.loopBody base env e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (loopBodyStep base env e st) := by
  obtain ⟨Δ, hEnv, hR⟩ := hpre
  cases e
  case letE nm ty v b nd => exact absurd rfl (hne nm ty v b nd)
  all_goals
    unfold loopBodyStep
    try dsimp only
    refine satK_optK ?_
    intro regs hregs
    refine satK_of_X (st₀ := st) ?_
    refine satKX_bindO (satKX_foldO (fun r => ReadSub senv (midExpr en) Δ r.2.2)
      (satKX_loopNext HKL hG hE hEnv) regs (readSub_loopRegs _ regs hR hregs)
      (([] : List (Nat × Lean.Expr)), st) hst (phExt_refl st)) ?_
    rintro ⟨ws, st1⟩ (hs1 : ReadInv HK senv p st1) (hx1 : PhExt st st1)
    exact satKX_okO (readInv_ws HKL hs1 _) (phExt_ws hx1 _)

end Tools.ShippingGen3ArgSupply3
