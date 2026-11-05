import Tools.ShippingGen4FKidsDefs
import Tools.ShippingChildWalkA
set_option autoImplicit false
-- F-kids StatePF walk, part 1: the calculus `KCS` (a `CompilerM` action keeps `Keeps`-world invariant `I` AND takes a state
-- with `StatePF` to a state with `StatePF` and the same `module.parameters`). No sorry / axiom / native_decide; no law.

/-! # `KCS`: `KeepsCP` with the circuit state tracked

`KCS I st c`: from every compiler context with provenance (`CtxOk`) and a world satisfying `I`, the run `c ctx st` returns in `I` with
a final state `st'` with `GoodS st st'` (both `StatePF`, and `parameters = []` is kept: the child's separate invariant. `GoodS.design` is the design-only part), and throws in `I` with the exception in the class.
`KeepsCS I c := ∀ st, KCS I st c`. The state is a parameter of `KCS` (pointed), so that `get >>= f` and `set s` relate `s` to the
state of the run (`KCS.bindGet`, `KCS.set`). A lifted `MetaM` action leaves the state: its leaf is a plain `Keeps` goal. -/

namespace Tools.ShippingGen4FKidsCalc
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildTranslateA
open Tools.ShippingGen4FKids
open Sparkle.IR.Builder (CircuitState)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the state relation of the walk: design-only part `StatePF a ∧ StatePF b` (`GoodS.design`; `addParameter` writes `module`, not `design`) plus `module.parameters` is kept EQUAL (fkids7: was an iff `= [] ↔ = []`; the equality is what the obligations (2) names ⊆ θ and (3) Nodup read; `bindInputsLegacy θ` with `θ = []` never reaches `addParameter`; the symbolic top walks its binders with `GoodS.design`) -/
def GoodS (st st' : CircuitState) : Prop :=
  StatePF st ∧ StatePF st' ∧ (st.module.parameters = st'.module.parameters)

theorem GoodS.design {a b : CircuitState} (h : GoodS a b) : StatePF a ∧ StatePF b := ⟨h.1, h.2.1⟩
theorem GoodS.symm {a b : CircuitState} (h : GoodS a b) : GoodS b a := ⟨h.2.1, h.1, h.2.2.symm⟩
theorem GoodS.refl {st : CircuitState} (h : StatePF st) : GoodS st st := ⟨h, h, rfl⟩
theorem GoodS.trans {a b c : CircuitState} (h1 : GoodS a b) (h2 : GoodS b c) : GoodS a c :=
  ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

/-- a state with the same view (design and module parameters) is `GoodS` to a `StatePF` state -/
theorem GoodS.of_view {a b : CircuitState} (h : StatePF a) (hv : View b = View a) : GoodS a b := by
  have h1 : b.design = a.design := congrArg Prod.fst hv
  have h2 : b.module.parameters = a.module.parameters := congrArg Prod.snd hv
  exact ⟨h, by unfold StatePF at *; rw [h1]; exact h, h2.symm⟩

section Defs
variable (mctx mref cctx cref)

/-- the pointed statement -/
def KCS {α : Type} (I : Void IO.RealWorld → Prop) (st : CircuitState) (c : CompilerM α) : Prop :=
  ∀ (ctx : CompilerState), CtxOk ctx → StatePF st →
    Triple mctx mref cctx cref I (c ctx st) (fun p w => I w ∧ GoodS st p.2) (fun e w => I w ∧ OkExc e)

/-- from every `StatePF` state -/
def KeepsCS {α : Type} (I : Void IO.RealWorld → Prop) (c : CompilerM α) : Prop :=
  ∀ st : CircuitState, KCS mctx mref cctx cref I st c

end Defs

section Rules
variable {I : Void IO.RealWorld → Prop} {st : CircuitState}

theorem KeepsCS.at {α : Type} {c : CompilerM α} (h : KeepsCS mctx mref cctx cref I c) (st : CircuitState) :
    KCS mctx mref cctx cref I st c := h st

theorem KCS.pure {α : Type} (a : α) : KCS mctx mref cctx cref I st (Pure.pure a : CompilerM α) :=
  fun _ _ hs => Triple.pure (a := (a, st)) fun _ hw => ⟨hw, GoodS.refl hs⟩

theorem KCS.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : KCS mctx mref cctx cref I st c)
    (h2 : ∀ a st', GoodS st st' → KCS mctx mref cctx cref I st' (f a)) :
    KCS mctx mref cctx cref I st (c >>= f) := by
  intro ctx hc hs
  refine Triple.bind (h1 ctx hc hs) (fun p => ?_)
  obtain ⟨a, s⟩ := p
  intro w hw
  have hg : GoodS st s := hw.2
  exact (Triple.conseq (P' := fun w => I w ∧ GoodS st s) (h2 a s hg ctx hc hg.2.1) (fun w hw => hw.1)
    (fun p w hq => ⟨hq.1, GoodS.trans hg hq.2⟩) (fun e w h => h)) w hw

theorem KCS.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    (ha : c → KCS mctx mref cctx cref I st a) (hb : ¬c → KCS mctx mref cctx cref I st b) :
    KCS mctx mref cctx cref I st (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem KCS.dite {α : Type} {c : Prop} [Decidable c] {a : c → CompilerM α} {b : ¬c → CompilerM α}
    (ha : ∀ h, KCS mctx mref cctx cref I st (a h)) (hb : ∀ h, KCS mctx mref cctx cref I st (b h)) :
    KCS mctx mref cctx cref I st (if h : c then a h else b h) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact ha hc
  · rw [dif_neg hc]; exact hb hc

theorem KCS.throw {α : Type} (e : Exception) (he : OkExc e) :
    KCS mctx mref cctx cref I st (MonadExcept.throw e : CompilerM α) :=
  fun _ _ _ => Triple.throw e fun w hw => ⟨hw, he⟩

/-- `throw e >>= k`: the continuation never runs. -/
theorem KCS.throwBind {α β : Type} (e : Exception) (he : OkExc e) (k : α → CompilerM β) :
    KCS mctx mref cctx cref I st ((MonadExcept.throw e : CompilerM α) >>= k) :=
  fun ctx _ _ => by
    refine Triple.bind (m := (MonadExcept.throw e : MetaM (α × CircuitState))) (f := fun p => k p.1 ctx p.2)
      (Q := fun _ _ => False) ?_ ?_
    · exact Triple.throw e fun w hw => ⟨hw, he⟩
    · intro p w hf
      exact hf.elim

theorem KCS.lift {α : Type} {m : MetaM α} (h : Keeps mctx mref cctx cref I m) :
    KCS mctx mref cctx cref I st (CompilerM.liftMetaM m) :=
  fun _ _ hs => Triple.bind (keeps_iff.mp h) fun a => Triple.pure (a := (a, st)) fun _ hw => ⟨hw, GoodS.refl hs⟩

theorem KCS.liftM {α : Type} {m : MetaM α} (h : Keeps mctx mref cctx cref I m) :
    KCS mctx mref cctx cref I st (_root_.liftM m : CompilerM α) :=
  KCS.lift h

theorem KCS.liftIO {α : Type} {x : IO α} (h : Keeps mctx mref cctx cref I (_root_.liftM x : MetaM α)) :
    KCS mctx mref cctx cref I st (_root_.liftM x : CompilerM α) :=
  KCS.lift h

theorem KCS.liftBaseIO {α : Type} {x : BaseIO α} (h : Keeps mctx mref cctx cref I (_root_.liftM x : MetaM α)) :
    KCS mctx mref cctx cref I st (_root_.liftM x : CompilerM α) :=
  KCS.lift h

theorem KCS.refGet {σ : Type} {r : IO.Ref σ} (h : Keeps mctx mref cctx cref I (ST.Ref.get r : MetaM σ)) :
    KCS mctx mref cctx cref I st (ST.Ref.get r : CompilerM σ) :=
  KCS.lift h

theorem KCS.refSet {σ : Type} {r : IO.Ref σ} {v : σ} (h : Keeps mctx mref cctx cref I (ST.Ref.set r v : MetaM Unit)) :
    KCS mctx mref cctx cref I st (ST.Ref.set r v : CompilerM Unit) :=
  KCS.lift h

theorem KCS.refModify {σ : Type} {r : IO.Ref σ} {f : σ → σ}
    (h : Keeps mctx mref cctx cref I (ST.Ref.modify r f : MetaM Unit)) :
    KCS mctx mref cctx cref I st (ST.Ref.modify r f : CompilerM Unit) :=
  KCS.lift h

/-- `get` followed by the continuation: the continuation is run from the very state read -/
theorem KCS.bindGet {β : Type} {f : CircuitState → CompilerM β} (h : KCS mctx mref cctx cref I st (f st)) :
    KCS mctx mref cctx cref I st ((get : CompilerM CircuitState) >>= f) :=
  fun ctx hc hs => h ctx hc hs

theorem KCS.get : KCS mctx mref cctx cref I st (get : CompilerM CircuitState) :=
  fun _ _ hs => Triple.pure (a := (st, st)) fun _ hw => ⟨hw, GoodS.refl hs⟩

theorem KCS.set (s : CircuitState) (hs : StatePF st → GoodS st s) :
    KCS mctx mref cctx cref I st (set s : CompilerM PUnit) :=
  fun _ _ h => Triple.pure (a := (PUnit.unit, s)) fun _ hw => ⟨hw, hs h⟩

theorem KCS.modify (f : CircuitState → CircuitState) (hs : StatePF st → GoodS st (f st)) :
    KCS mctx mref cctx cref I st (modify f : CompilerM PUnit) :=
  fun _ _ h => Triple.pure (a := (PUnit.unit, f st)) fun _ hw => ⟨hw, hs h⟩

theorem KCS.getCompilerState : KCS mctx mref cctx cref I st CompilerM.getCompilerState :=
  fun ctx _ hs => Triple.pure (a := (ctx, st)) fun _ hw => ⟨hw, GoodS.refl hs⟩

theorem KCS.read : KCS mctx mref cctx cref I st (MonadReader.read : CompilerM CompilerState) :=
  fun ctx _ hs => Triple.pure (a := (ctx, st)) fun _ hw => ⟨hw, GoodS.refl hs⟩

/-- **The read context has provenance**: its continuation is asked only for contexts with `CtxOk`. -/
theorem KCS.bindCtx {β : Type} {f : CompilerState → CompilerM β}
    (h : ∀ cs, CtxOk cs → KCS mctx mref cctx cref I st (f cs)) :
    KCS mctx mref cctx cref I st (CompilerM.getCompilerState >>= f) :=
  fun ctx hc hs => h ctx hc ctx hc hs

theorem KCS.bindRead {β : Type} {f : CompilerState → CompilerM β}
    (h : ∀ cs, CtxOk cs → KCS mctx mref cctx cref I st (f cs)) :
    KCS mctx mref cctx cref I st ((MonadReader.read : CompilerM CompilerState) >>= f) :=
  fun ctx hc hs => h ctx hc ctx hc hs

theorem KCS.withReader {α : Type} {k : CompilerM α} (f : CompilerState → CompilerState)
    (hf : ∀ ctx, CtxOk ctx → CtxOk (f ctx)) (h : KCS mctx mref cctx cref I st k) :
    KCS mctx mref cctx cref I st (withReader f k) :=
  fun ctx hc hs => h (f ctx) (hf ctx hc) hs

theorem KCS.tryCatch {α : Type} {x : CompilerM α} {h : Exception → CompilerM α}
    (hx : KCS mctx mref cctx cref I st x) (hh : ∀ e, OkExc e → KCS mctx mref cctx cref I st (h e)) :
    KCS mctx mref cctx cref I st (MonadExcept.tryCatch x h) :=
  fun ctx hc hs => Triple.tryCatchQ (hx ctx hc hs) fun e he => hh e he ctx hc hs

theorem KCS.map {α β : Type} {c : CompilerM α} (f : α → β) (h : KCS mctx mref cctx cref I st c) :
    KCS mctx mref cctx cref I st (f <$> c) :=
  KCS.bind h fun a _ _ => KCS.pure (f a)


theorem KCS.forIn_list {α β : Type} (f : α → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCS mctx mref cctx cref I (f a b)) :
    ∀ (l : List α) (b : β) (st : CircuitState), KCS mctx mref cctx cref I st (forIn l b f)
  | [], b, st => by
    rw [List.forIn_nil]
    exact KCS.pure b
  | a :: l, b, st => by
    rw [List.forIn_cons]
    refine KCS.bind (hf a b st) (fun r st' _ => ?_)
    cases r with
    | done b' => exact KCS.pure b'
    | yield b' => exact KCS.forIn_list f hf l b' st'

theorem KCS.forIn_array {α β : Type} (f : α → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCS mctx mref cctx cref I (f a b)) (as : Array α) (b : β) (st : CircuitState) :
    KCS mctx mref cctx cref I st (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact KCS.forIn_list f hf _ b st

theorem KCS.forIn_range {β : Type} (f : Nat → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCS mctx mref cctx cref I (f a b)) (r : Std.Legacy.Range) (b : β) (st : CircuitState) :
    KCS mctx mref cctx cref I st (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact KCS.forIn_list f hf _ b st

theorem KCS.pureE {ρ α : Type} (a : α) : KCS mctx mref cctx cref I st (Pure.pure a : ExceptT ρ CompilerM α) :=
  KCS.pure (Except.ok a)

theorem KCS.throwE {ρ α : Type} (r : ρ) : KCS mctx mref cctx cref I st (throwThe ρ r : ExceptT ρ CompilerM α) :=
  KCS.pure (Except.error r)

theorem KCS.bindE {ρ α β : Type} {m : ExceptT ρ CompilerM α} {f : α → ExceptT ρ CompilerM β}
    (h1 : KCS mctx mref cctx cref I st m)
    (h2 : ∀ a st', GoodS st st' → KCS mctx mref cctx cref I st' (f a)) :
    KCS mctx mref cctx cref I st (m >>= f : ExceptT ρ CompilerM β) :=
  KCS.bind (c := (m : CompilerM (Except ρ α))) h1 fun r st' hg => by
    cases r with
    | ok a => exact h2 a st' hg
    | error e => exact KCS.pure (Except.error e)

theorem KCS.liftE {ρ α : Type} {c : CompilerM α} (h : KCS mctx mref cctx cref I st c) :
    KCS mctx mref cctx cref I st (_root_.liftM c : ExceptT ρ CompilerM α) :=
  KCS.bind h fun a _ _ => KCS.pure (Except.ok a)

end Rules

/-! ## The unpointed API: the same names as `KeepsCP` (a copy of a `KeepsCP` proof script ports by renaming) -/

section Unpointed
variable {I : Void IO.RealWorld → Prop}

theorem KeepsCS.pure {α : Type} (a : α) : KeepsCS mctx mref cctx cref I (Pure.pure a : CompilerM α) :=
  fun _ => KCS.pure a

theorem KeepsCS.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : KeepsCS mctx mref cctx cref I c) (h2 : ∀ a, KeepsCS mctx mref cctx cref I (f a)) :
    KeepsCS mctx mref cctx cref I (c >>= f) :=
  fun st => KCS.bind (h1 st) fun a st' _ => h2 a st'

theorem KeepsCS.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    (ha : c → KeepsCS mctx mref cctx cref I a) (hb : ¬c → KeepsCS mctx mref cctx cref I b) :
    KeepsCS mctx mref cctx cref I (if c then a else b) :=
  fun st => KCS.ite (fun h => ha h st) (fun h => hb h st)

theorem KeepsCS.dite {α : Type} {c : Prop} [Decidable c] {a : c → CompilerM α} {b : ¬c → CompilerM α}
    (ha : ∀ h, KeepsCS mctx mref cctx cref I (a h)) (hb : ∀ h, KeepsCS mctx mref cctx cref I (b h)) :
    KeepsCS mctx mref cctx cref I (if h : c then a h else b h) :=
  fun st => KCS.dite (fun h => ha h st) (fun h => hb h st)

theorem KeepsCS.throw {α : Type} (e : Exception) (he : OkExc e) :
    KeepsCS mctx mref cctx cref I (MonadExcept.throw e : CompilerM α) :=
  fun _ => KCS.throw e he

theorem KeepsCS.throwBind {α β : Type} (e : Exception) (he : OkExc e) (k : α → CompilerM β) :
    KeepsCS mctx mref cctx cref I ((MonadExcept.throw e : CompilerM α) >>= k) :=
  fun _ => KCS.throwBind e he k

theorem KeepsCS.lift {α : Type} {m : MetaM α} (h : Keeps mctx mref cctx cref I m) :
    KeepsCS mctx mref cctx cref I (CompilerM.liftMetaM m) :=
  fun _ => KCS.lift h

theorem KeepsCS.liftM {α : Type} {m : MetaM α} (h : Keeps mctx mref cctx cref I m) :
    KeepsCS mctx mref cctx cref I (_root_.liftM m : CompilerM α) :=
  fun _ => KCS.liftM h

theorem KeepsCS.liftIO {α : Type} {x : IO α} (h : Keeps mctx mref cctx cref I (_root_.liftM x : MetaM α)) :
    KeepsCS mctx mref cctx cref I (_root_.liftM x : CompilerM α) :=
  fun _ => KCS.liftIO h

theorem KeepsCS.liftBaseIO {α : Type} {x : BaseIO α}
    (h : Keeps mctx mref cctx cref I (_root_.liftM x : MetaM α)) :
    KeepsCS mctx mref cctx cref I (_root_.liftM x : CompilerM α) :=
  fun _ => KCS.liftBaseIO h

theorem KeepsCS.refGet {σ : Type} {r : IO.Ref σ} (h : Keeps mctx mref cctx cref I (ST.Ref.get r : MetaM σ)) :
    KeepsCS mctx mref cctx cref I (ST.Ref.get r : CompilerM σ) :=
  fun _ => KCS.refGet h

theorem KeepsCS.refSet {σ : Type} {r : IO.Ref σ} {v : σ}
    (h : Keeps mctx mref cctx cref I (ST.Ref.set r v : MetaM Unit)) :
    KeepsCS mctx mref cctx cref I (ST.Ref.set r v : CompilerM Unit) :=
  fun _ => KCS.refSet h

theorem KeepsCS.refModify {σ : Type} {r : IO.Ref σ} {f : σ → σ}
    (h : Keeps mctx mref cctx cref I (ST.Ref.modify r f : MetaM Unit)) :
    KeepsCS mctx mref cctx cref I (ST.Ref.modify r f : CompilerM Unit) :=
  fun _ => KCS.refModify h

theorem KeepsCS.get : KeepsCS mctx mref cctx cref I (MonadState.get : CompilerM CircuitState) := fun _ => KCS.get

/-- `get >>= f`: the continuation is asked about the state read (pointed) -/
theorem KeepsCS.bindGet {β : Type} {f : CircuitState → CompilerM β}
    (h : ∀ st, KCS mctx mref cctx cref I st (f st)) :
    KeepsCS mctx mref cctx cref I ((MonadState.get : CompilerM CircuitState) >>= f) :=
  fun st => KCS.bindGet (h st)

theorem KeepsCS.getCompilerState : KeepsCS mctx mref cctx cref I CompilerM.getCompilerState :=
  fun _ => KCS.getCompilerState

theorem KeepsCS.read : KeepsCS mctx mref cctx cref I (MonadReader.read : CompilerM CompilerState) :=
  fun _ => KCS.read

theorem KeepsCS.bindCtx {β : Type} {f : CompilerState → CompilerM β}
    (h : ∀ cs, CtxOk cs → KeepsCS mctx mref cctx cref I (f cs)) :
    KeepsCS mctx mref cctx cref I (CompilerM.getCompilerState >>= f) :=
  fun st => KCS.bindCtx fun cs hc => h cs hc st

theorem KeepsCS.bindRead {β : Type} {f : CompilerState → CompilerM β}
    (h : ∀ cs, CtxOk cs → KeepsCS mctx mref cctx cref I (f cs)) :
    KeepsCS mctx mref cctx cref I ((MonadReader.read : CompilerM CompilerState) >>= f) :=
  fun st => KCS.bindRead fun cs hc => h cs hc st

theorem KeepsCS.withReader {α : Type} {k : CompilerM α} (f : CompilerState → CompilerState)
    (hf : ∀ ctx, CtxOk ctx → CtxOk (f ctx)) (h : KeepsCS mctx mref cctx cref I k) :
    KeepsCS mctx mref cctx cref I (withReader f k) :=
  fun st => KCS.withReader f hf (h st)

theorem KeepsCS.tryCatch {α : Type} {x : CompilerM α} {h : Exception → CompilerM α}
    (hx : KeepsCS mctx mref cctx cref I x) (hh : ∀ e, OkExc e → KeepsCS mctx mref cctx cref I (h e)) :
    KeepsCS mctx mref cctx cref I (MonadExcept.tryCatch x h) :=
  fun st => KCS.tryCatch (hx st) fun e he => hh e he st

theorem KeepsCS.map {α β : Type} {c : CompilerM α} (f : α → β) (h : KeepsCS mctx mref cctx cref I c) :
    KeepsCS mctx mref cctx cref I (f <$> c) :=
  fun st => KCS.map f (h st)

theorem KeepsCS.forIn_list {α β : Type} (f : α → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCS mctx mref cctx cref I (f a b)) (l : List α) (b : β) :
    KeepsCS mctx mref cctx cref I (forIn l b f) :=
  fun st => KCS.forIn_list f hf l b st

theorem KeepsCS.forIn_array {α β : Type} (f : α → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCS mctx mref cctx cref I (f a b)) (as : Array α) (b : β) :
    KeepsCS mctx mref cctx cref I (forIn as b f) :=
  fun st => KCS.forIn_array f hf as b st

theorem KeepsCS.forIn_range {β : Type} (f : Nat → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCS mctx mref cctx cref I (f a b)) (r : Std.Legacy.Range) (b : β) :
    KeepsCS mctx mref cctx cref I (forIn r b f) :=
  fun st => KCS.forIn_range f hf r b st

theorem KeepsCS.pureE {ρ α : Type} (a : α) :
    KeepsCS mctx mref cctx cref I (Pure.pure a : ExceptT ρ CompilerM α) := fun _ => KCS.pureE a

theorem KeepsCS.throwE {ρ α : Type} (r : ρ) :
    KeepsCS mctx mref cctx cref I (throwThe ρ r : ExceptT ρ CompilerM α) := fun _ => KCS.throwE r

theorem KeepsCS.bindE {ρ α β : Type} {m : ExceptT ρ CompilerM α} {f : α → ExceptT ρ CompilerM β}
    (h1 : KeepsCS mctx mref cctx cref I m) (h2 : ∀ a, KeepsCS mctx mref cctx cref I (f a)) :
    KeepsCS mctx mref cctx cref I (m >>= f : ExceptT ρ CompilerM β) :=
  fun st => KCS.bindE (h1 st) fun a st' _ => h2 a st'

theorem KeepsCS.liftE {ρ α : Type} {c : CompilerM α} (h : KeepsCS mctx mref cctx cref I c) :
    KeepsCS mctx mref cctx cref I (_root_.liftM c : ExceptT ρ CompilerM α) :=
  fun st => KCS.liftE (h st)

/-- a state-neutral action (final state = initial) whose world behaviour is `KeepsCP` -/
theorem KCS.ofKeepsCP_neutral {α : Type} {c : CompilerM α}
    (h : KeepsCP mctx mref cctx cref I c) (hn : ∀ ctx st a st' w w', (c ctx st) mctx mref cctx cref w = .ok (a, st') w' → st' = st) :
    KeepsCS mctx mref cctx cref I c := by
  intro st ctx hc hs
  intro w hw
  have h1 := h ctx st hc w hw
  unfold endW ErrOk at h1
  cases hm : (c ctx st) mctx mref cctx cref w with
  | ok p w' =>
    rw [hm] at h1
    show I w' ∧ GoodS st p.2
    rw [hn ctx st p.1 p.2 w w' (by simpa using hm)]
    exact ⟨h1.1, GoodS.refl hs⟩
  | error e w' =>
    rw [hm] at h1
    exact h1

end Unpointed


/-! ## (fkids3) results that carry a fact: the child pair of `handleDefinitionUnfold`

`OptPFc`: an optional child pair is `PairPF` when present. `NoRetS st c`: the run of `c` from `st` never RETURNS (it throws, in the class).
`KCS.bindTryChild` is the one rule that lets the child pair's `PairPF` reach the continuation through `try (some <$> liftMetaM (childSynthEntry n)) catch h`
when the handler `h` always throws. Pure calculus: no law, no premise. -/

def OptPFc (o : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) : Prop := ∀ r, o = some r → PairPF r

theorem OptPFc.some' {r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design} (h : PairPF r) : OptPFc (some r) := by
  intro r' h'
  cases h'
  exact h

section NoRet
variable (mctx mref cctx cref)

def NoRetS {α : Type} (I : Void IO.RealWorld → Prop) (st : CircuitState) (c : CompilerM α) : Prop :=
  ∀ (ctx : CompilerState), CtxOk ctx → StatePF st →
    Triple mctx mref cctx cref I (c ctx st) (fun _ _ => False) (fun e w => I w ∧ OkExc e)

def NoRetSA {α : Type} (I : Void IO.RealWorld → Prop) (c : CompilerM α) : Prop :=
  ∀ st : CircuitState, NoRetS mctx mref cctx cref I st c

end NoRet

section NoRetRules
variable {I : Void IO.RealWorld → Prop} {st : CircuitState}

theorem NoRetS.throw {α : Type} (e : Exception) (he : OkExc e) :
    NoRetS mctx mref cctx cref I st (MonadExcept.throw e : CompilerM α) :=
  fun _ _ _ => Triple.throw e fun w hw => ⟨hw, he⟩

theorem NoRetS.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : KCS mctx mref cctx cref I st c)
    (h2 : ∀ a st', GoodS st st' → NoRetS mctx mref cctx cref I st' (f a)) :
    NoRetS mctx mref cctx cref I st (c >>= f) := by
  intro ctx hc hs
  refine Triple.bind (h1 ctx hc hs) (fun p => ?_)
  obtain ⟨a, s⟩ := p
  intro w hw
  have hg : GoodS st s := hw.2
  exact (h2 a s hg ctx hc hg.2.1) w hw.1

theorem NoRetS.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    (ha : c → NoRetS mctx mref cctx cref I st a) (hb : ¬c → NoRetS mctx mref cctx cref I st b) :
    NoRetS mctx mref cctx cref I st (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem NoRetS.dite {α : Type} {c : Prop} [Decidable c] {a : c → CompilerM α} {b : ¬c → CompilerM α}
    (ha : ∀ h, NoRetS mctx mref cctx cref I st (a h)) (hb : ∀ h, NoRetS mctx mref cctx cref I st (b h)) :
    NoRetS mctx mref cctx cref I st (if h : c then a h else b h) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact ha hc
  · rw [dif_neg hc]; exact hb hc

theorem Triple.liftC {α : Type} {m : MetaM α} {Q : α → Void IO.RealWorld → Prop}
    {R : Exception → Void IO.RealWorld → Prop} {ctx : CompilerState} {st : CircuitState}
    (h : Triple mctx mref cctx cref I m Q R) :
    Triple mctx mref cctx cref I (CompilerM.liftMetaM m ctx st) (fun p w => Q p.1 w ∧ p.2 = st) R :=
  Triple.bind h fun a => Triple.pure (a := (a, st)) fun w hw => ⟨hw, rfl⟩

/-- a lifted `throwError`: it keeps the invariant (`hk`) and never returns (`throwError_not_runs`) -/
theorem NoRetS.liftThrowError {α : Type} (msg : MessageData)
    (hk : Keeps mctx mref cctx cref I (Lean.throwError msg : MetaM α)) :
    NoRetS mctx mref cctx cref I st (CompilerM.liftMetaM (Lean.throwError msg : MetaM α)) := by
  intro ctx hc hs
  have h0 : Triple mctx mref cctx cref I (Lean.throwError msg : MetaM α) (fun _ _ => False)
      (fun e w => I w ∧ OkExc e) := by
    intro w hw
    have h := keeps_iff.mp hk w hw
    cases hm : (Lean.throwError msg : MetaM α) mctx mref cctx cref w with
    | ok a w1 => exact (throwError_not_runs msg hm).elim
    | error e w1 => rw [hm] at h; exact h
  exact Triple.conseq (Triple.liftC h0) (fun w hw => hw) (fun _ _ h => h.1.elim) (fun _ _ h => h)

theorem NoRetS.tryCatch {α : Type} {x h : _} (hx : NoRetS mctx mref cctx cref I st x)
    (hh : ∀ e, OkExc e → NoRetS mctx mref cctx cref I st (h e)) :
    NoRetS mctx mref cctx cref I st (MonadExcept.tryCatch (α := α) x h) :=
  fun ctx hc hs => Triple.tryCatchQ (hx ctx hc hs) fun e he => hh e he ctx hc hs

/-- **The child pair reaches the continuation**: `try (some <$> liftMetaM (childSynthEntry n)) catch h` with a handler that never
returns, followed by `f`: `f` is asked only for `some r` with `PairPF r`. -/
theorem KCS.bindTryChild {β : Type} {n : Name} {h : Exception → CompilerM (Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design))}
    {f : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) → CompilerM β}
    (hc : Triple mctx mref cctx cref I (childSynthEntry n) (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e))
    (hh : ∀ e, OkExc e → NoRetS mctx mref cctx cref I st (h e))
    (hf : ∀ r st', PairPF r → GoodS st st' → KCS mctx mref cctx cref I st' (f (some r))) :
    KCS mctx mref cctx cref I st
      (MonadExcept.tryCatch (some <$> CompilerM.liftMetaM (childSynthEntry n)) h >>= f) := by
  intro ctx hc' hs
  have hl : Triple mctx mref cctx cref I ((some <$> CompilerM.liftMetaM (childSynthEntry n) : CompilerM _) ctx st)
      (fun p w => I w ∧ ∃ r, p.1 = some r ∧ PairPF r ∧ p.2 = st) (fun e w => I w ∧ OkExc e) :=
    Triple.bind (Triple.liftC hc (ctx := ctx) (st := st)) fun p =>
      Triple.pure (a := (some p.1, p.2)) fun w hw => ⟨hw.1.1, p.1, rfl, hw.1.2, hw.2⟩
  refine Triple.bind (Q := fun p w => I w ∧ ∃ r, p.1 = some r ∧ PairPF r ∧ p.2 = st)
    (Triple.tryCatchQ hl fun e he => Triple.conseq (hh e he ctx hc' hs) (fun w hw => hw)
      (fun _ _ hf => hf.elim) (fun _ _ hR => hR)) (fun p => ?_)
  obtain ⟨a, s⟩ := p
  intro w hw
  obtain ⟨hI, r, har, hr, hsr⟩ := hw
  have har' : a = some r := har
  have hsr' : s = st := hsr
  subst har' hsr'
  exact hf r s hr (GoodS.refl hs) ctx hc' hs w hI

theorem KCS.forIn_list_mem {α β : Type} (f : α → β → CompilerM (ForInStep β)) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, KeepsCS mctx mref cctx cref I (f a b)) →
    ∀ (b : β) (st : CircuitState), KCS mctx mref cctx cref I st (forIn l b f)
  | [], _, b, st => by
    rw [List.forIn_nil]
    exact KCS.pure b
  | a :: l, hf, b, st => by
    rw [List.forIn_cons]
    refine KCS.bind (hf a (List.mem_cons_self ..) b st) (fun r st' _ => ?_)
    cases r with
    | done b' => exact KCS.pure b'
    | yield b' => exact KCS.forIn_list_mem f l (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' st'

end NoRetRules

end Tools.ShippingGen4FKidsCalc
