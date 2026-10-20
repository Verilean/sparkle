import Tools.ShippingChildHarness

/-! # Walking a compiler definition: the invariant kept, step by step

`Keeps I m` / `KeepsC I c` — from a world satisfying `I`, the run ends in
one, returning or throwing — for a program built from binds, `pure`, `if`,
`match`, `throw`, state reads and writes, lifted `MetaM` actions and calls of
other definitions, follows from the same for its parts. The rules are the
theorems below; the tactic `vc` applies them along the program's syntax:

* a bind, `pure`, `if`, `match`, `let`, a `throw`, a state operation: the rule;
* a call of a local hypothesis (the recursive translator, a continuation): it;
* a call of a definition with a registered `@[keeps]` theorem: that theorem;
* an operation whose frame is a generic law (`Framed`): the law;
* any other NON-recursive definition: unfolded, and walked.

It fails at an operation it has nothing for — an opaque (`partial`) function,
a primitive without a law, a recursive definition without a theorem — and
names it. Nothing is assumed by the tactic: what it closes is a kernel-checked
proof from the rules, the laws and the hypotheses in scope. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Sparkle.IR.Builder (CircuitState)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The rules, in `Keeps` form -/

theorem Keeps.pure {α : Type} {I : Void IO.RealWorld → Prop} (a : α) :
    Keeps mctx mref cctx cref I (Pure.pure a : MetaM α) :=
  keeps_iff.mpr (Triple.pure fun _ hw => hw)

theorem Keeps.bind {α β : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α} {f : α → MetaM β}
    (h1 : Keeps mctx mref cctx cref I m) (h2 : ∀ a, Keeps mctx mref cctx cref I (f a)) :
    Keeps mctx mref cctx cref I (m >>= f) :=
  keeps_iff.mpr (Triple.bind (keeps_iff.mp h1) fun a => keeps_iff.mp (h2 a))

theorem Keeps.ite {α : Type} {c : Prop} [Decidable c] {I : Void IO.RealWorld → Prop}
    {a b : MetaM α} (ha : c → Keeps mctx mref cctx cref I a)
    (hb : ¬c → Keeps mctx mref cctx cref I b) :
    Keeps mctx mref cctx cref I (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem Keeps.dite {α : Type} {c : Prop} [Decidable c] {I : Void IO.RealWorld → Prop}
    {a : c → MetaM α} {b : ¬c → MetaM α} (ha : ∀ h, Keeps mctx mref cctx cref I (a h))
    (hb : ∀ h, Keeps mctx mref cctx cref I (b h)) :
    Keeps mctx mref cctx cref I (if h : c then a h else b h) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact ha hc
  · rw [dif_neg hc]; exact hb hc

/-- A plain `throw` of an exception in the class. -/
theorem Keeps.throw {α : Type} {I : Void IO.RealWorld → Prop} (e : Exception) (he : OkExc e) :
    Keeps mctx mref cctx cref I (throw e : MetaM α) :=
  keeps_iff.mpr (Triple.throw e fun _ hw => ⟨hw, he⟩)

/-- `throwError` of a message in the class. -/
theorem Keeps.throwError {α : Type} (L : RefLaws mref cref) (D : Nat) (msg : MessageData)
    (hmsg : OkMsg msg) :
    Keeps mctx mref cctx cref (J L D) (Lean.throwError msg : MetaM α) :=
  keeps_iff.mpr (Triple.throwErr L msg hmsg D)

/-- An operation whose frame is a law. -/
theorem Keeps.framed {α : Type} (L : RefLaws mref cref) (D : Nat) {p : MetaM α} (hp : Op p) :
    Keeps mctx mref cctx cref (J L D) p :=
  keeps_iff.mpr (Triple.op L hp D)

theorem Keeps.mapM {α β : Type} {I : Void IO.RealWorld → Prop} (f : α → MetaM β)
    (hf : ∀ x, Keeps mctx mref cctx cref I (f x)) (l : List α) :
    Keeps mctx mref cctx cref I (l.mapM f) :=
  keeps_iff.mpr (Triple.mapM f (fun x => keeps_iff.mp (hf x)) l)

/-- `try x catch e => h e`: the handler runs from the world the failing `x`
ended in — or, for an interrupt or a runtime exception, does not run and the
exception goes on from that same world (`Core.tryCatch`). -/
theorem Keeps.tryCatch {α : Type} {I : Void IO.RealWorld → Prop} {x : MetaM α}
    {h : Exception → MetaM α} (hx : Keeps mctx mref cctx cref I x)
    (hh : ∀ e, OkExc e → Keeps mctx mref cctx cref I (h e)) :
    Keeps mctx mref cctx cref I (MonadExcept.tryCatch x h) := by
  rw [keeps_iff] at hx ⊢
  intro w hw
  have h1 := hx w hw
  change match (Core.tryCatch (x mctx mref) (fun e => h e mctx mref)) cctx cref w with
    | .ok _ w' => I w' | .error e w' => I w' ∧ OkExc e
  unfold Core.tryCatch
  change match (EST.tryCatch (x mctx mref cctx cref)
      (fun ex => (if (ex.isInterrupt || ex.isRuntime) = true then (MonadExcept.throw ex : CoreM α)
        else h ex mctx mref) cctx cref)) w with
    | .ok _ w' => I w' | .error e w' => I w' ∧ OkExc e
  unfold EST.tryCatch
  cases hxw : x mctx mref cctx cref w with
  | ok a w1 => rw [hxw] at h1; exact h1
  | error e w1 =>
    rw [hxw] at h1
    dsimp only
    by_cases hc : (e.isInterrupt || e.isRuntime) = true
    · rw [if_pos hc]; exact h1
    · rw [if_neg hc]
      exact keeps_iff.mp (hh e h1.2) w1 h1.1

/-- An action that returns in the world it started in (a context read). -/
theorem Keeps.of_ok {α : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α}
    (h : ∀ w, ∃ a, m mctx mref cctx cref w = .ok a w) : Keeps mctx mref cctx cref I m := by
  intro w hw
  obtain ⟨a, ha⟩ := h w
  unfold endW ErrOk; rw [ha]; exact ⟨hw, trivial⟩

/-- `withReader` on the Meta context: the action, in the changed context. -/
theorem Keeps.withReader {α : Type} {I : Void IO.RealWorld → Prop} {x : MetaM α}
    (f : Meta.Context → Meta.Context)
    (h : ∀ mctx' : Meta.Context, Keeps mctx' mref cctx cref I x) :
    Keeps mctx mref cctx cref I (withReader f x) :=
  fun w hw => h (f mctx) w hw

theorem Keeps.map {α β : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α} (f : α → β)
    (h : Keeps mctx mref cctx cref I m) : Keeps mctx mref cctx cref I (f <$> m) :=
  Keeps.bind h fun a => Keeps.pure (f a)

/-- `lambdaTelescope`: its continuation, in whatever contexts it runs. -/
theorem Keeps.lambdaTelescope {α : Type} (L : RefLaws mref cref) (D : Nat) (e : Lean.Expr)
    (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b,
      Keeps mctx' mref cctx' cref (J L D) (k xs b)) :
    Keeps mctx mref cctx cref (J L D) (Lean.Meta.lambdaTelescope e k cleanup) :=
  L.lamTelescope (J L D) (fun _ _ h1 h2 h3 hq hw => J_same L ⟨h1, h2, h3⟩ hq hw) e k cleanup hk

/-- `forallTelescopeReducing`: its continuation, in whatever contexts it runs. -/
theorem Keeps.forallTelescopeReducing {α : Type} (L : RefLaws mref cref) (D : Nat) (ty : Lean.Expr)
    (k : Array Lean.Expr → Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b,
      Keeps mctx' mref cctx' cref (J L D) (k xs b)) :
    Keeps mctx mref cctx cref (J L D) (Lean.Meta.forallTelescopeReducing ty k) :=
  L.telescope (J L D) (fun _ _ h1 h2 h3 hq hw => J_same L ⟨h1, h2, h3⟩ hq hw) ty k hk

/-- A `for` loop over a list: its body, at every element and accumulator. -/
theorem Keeps.forIn_list {α β : Type} {I : Void IO.RealWorld → Prop}
    (f : α → β → MetaM (ForInStep β)) (hf : ∀ a b, Keeps mctx mref cctx cref I (f a b)) :
    ∀ (l : List α) (b : β), Keeps mctx mref cctx cref I (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact Keeps.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine Keeps.bind (hf a b) (fun r => ?_)
    cases r with
    | done b' => exact Keeps.pure b'
    | yield b' => exact Keeps.forIn_list f hf l b'

theorem Keeps.forIn_array {α β : Type} {I : Void IO.RealWorld → Prop}
    (f : α → β → MetaM (ForInStep β)) (hf : ∀ a b, Keeps mctx mref cctx cref I (f a b))
    (as : Array α) (b : β) : Keeps mctx mref cctx cref I (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact Keeps.forIn_list f hf _ b

theorem Keeps.forIn_range {β : Type} {I : Void IO.RealWorld → Prop}
    (f : Nat → β → MetaM (ForInStep β)) (hf : ∀ a b, Keeps mctx mref cctx cref I (f a b))
    (r : Std.Legacy.Range) (b : β) : Keeps mctx mref cctx cref I (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact Keeps.forIn_list f hf _ b

/-! ### `ExceptT ρ MetaM` (a `do` block with an early `return`): the same rules.
An `ExceptT ρ MetaM α` action IS a `MetaM (Except ρ α)` action. -/

theorem Keeps.pureE {ρ α : Type} {I : Void IO.RealWorld → Prop} (a : α) :
    Keeps mctx mref cctx cref I (Pure.pure a : ExceptT ρ MetaM α) :=
  Keeps.pure (Except.ok a)

theorem Keeps.throwE {ρ α : Type} {I : Void IO.RealWorld → Prop} (r : ρ) :
    Keeps mctx mref cctx cref I (throwThe ρ r : ExceptT ρ MetaM α) :=
  Keeps.pure (Except.error r)

theorem Keeps.bindE {ρ α β : Type} {I : Void IO.RealWorld → Prop} {m : ExceptT ρ MetaM α}
    {f : α → ExceptT ρ MetaM β} (h1 : Keeps mctx mref cctx cref I m)
    (h2 : ∀ a, Keeps mctx mref cctx cref I (f a)) :
    Keeps mctx mref cctx cref I ((m >>= f : ExceptT ρ MetaM β)) :=
  Keeps.bind (m := (m : MetaM (Except ρ α))) h1 fun r => by
    cases r with
    | ok a => exact h2 a
    | error e => exact Keeps.pure (Except.error e)

theorem Keeps.liftE {ρ α : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α}
    (h : Keeps mctx mref cctx cref I m) :
    Keeps mctx mref cctx cref I (_root_.liftM m : ExceptT ρ MetaM α) :=
  Keeps.bind h fun a => Keeps.pure (Except.ok a)

/-- `withLocalDeclD`: its continuation, in whatever contexts it runs. -/
theorem Keeps.withLocalDeclD {α : Type} (L : RefLaws mref cref) (D : Nat) (n : Name)
    (ty : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x,
      Keeps mctx' mref cctx' cref (J L D) (k x)) :
    Keeps mctx mref cctx cref (J L D) (Lean.Meta.withLocalDeclD n ty k) :=
  L.localDecl (J L D) (fun _ _ h1 h2 h3 hq hw => J_same L ⟨h1, h2, h3⟩ hq hw) n ty k hk

/-- `withLetDecl`: its continuation, in whatever contexts it runs. -/
theorem Keeps.withLetDecl {α : Type} (L : RefLaws mref cref) (D : Nat) (n : Name)
    (ty v : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x,
      Keeps mctx' mref cctx' cref (J L D) (k x)) :
    Keeps mctx mref cctx cref (J L D) (Lean.Meta.withLetDecl n ty v k) :=
  L.letDecl (J L D) (fun _ _ h1 h2 h3 hq hw => J_same L ⟨h1, h2, h3⟩ hq hw) n ty v k hk

/-! ## The rules, in `KeepsC` form -/

theorem KeepsC.intro {α : Type} {I : Void IO.RealWorld → Prop} {c : CompilerM α}
    (h : ∀ (ctx : CompilerState) (st : CircuitState), Keeps mctx mref cctx cref I (c ctx st)) :
    KeepsC mctx mref cctx cref I c := h

theorem KeepsC.apply {α : Type} {I : Void IO.RealWorld → Prop} {c : CompilerM α}
    (h : KeepsC mctx mref cctx cref I c) (ctx : CompilerState) (st : CircuitState) :
    Keeps mctx mref cctx cref I (c ctx st) := h ctx st

theorem KeepsC.pure {α : Type} {I : Void IO.RealWorld → Prop} (a : α) :
    KeepsC mctx mref cctx cref I (Pure.pure a : CompilerM α) :=
  keepsC_iff.mpr (TripleC.pure fun _ hw => hw)

theorem KeepsC.bind {α β : Type} {I : Void IO.RealWorld → Prop} {c : CompilerM α}
    {f : α → CompilerM β} (h1 : KeepsC mctx mref cctx cref I c)
    (h2 : ∀ a, KeepsC mctx mref cctx cref I (f a)) :
    KeepsC mctx mref cctx cref I (c >>= f) :=
  keepsC_iff.mpr (TripleC.bind (keepsC_iff.mp h1) fun a => keepsC_iff.mp (h2 a))

theorem KeepsC.ite {α : Type} {c : Prop} [Decidable c] {I : Void IO.RealWorld → Prop}
    {a b : CompilerM α} (ha : c → KeepsC mctx mref cctx cref I a)
    (hb : ¬c → KeepsC mctx mref cctx cref I b) :
    KeepsC mctx mref cctx cref I (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem KeepsC.dite {α : Type} {c : Prop} [Decidable c] {I : Void IO.RealWorld → Prop}
    {a : c → CompilerM α} {b : ¬c → CompilerM α} (ha : ∀ h, KeepsC mctx mref cctx cref I (a h))
    (hb : ∀ h, KeepsC mctx mref cctx cref I (b h)) :
    KeepsC mctx mref cctx cref I (if h : c then a h else b h) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact ha hc
  · rw [dif_neg hc]; exact hb hc

theorem KeepsC.throw {α : Type} {I : Void IO.RealWorld → Prop} (e : Exception) (he : OkExc e) :
    KeepsC mctx mref cctx cref I (throw e : CompilerM α) :=
  keepsC_iff.mpr (TripleC.throw e fun _ hw => ⟨hw, he⟩)

theorem KeepsC.lift {α : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α}
    (h : Keeps mctx mref cctx cref I m) :
    KeepsC mctx mref cctx cref I (CompilerM.liftMetaM m) :=
  keepsC_iff.mpr (TripleC.lift (keeps_iff.mp h))

theorem KeepsC.liftM {α : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α}
    (h : Keeps mctx mref cctx cref I m) :
    KeepsC mctx mref cctx cref I (liftM m : CompilerM α) :=
  keepsC_iff.mpr (TripleC.lift (keeps_iff.mp h))

theorem KeepsC.get {I : Void IO.RealWorld → Prop} :
    KeepsC mctx mref cctx cref I (get : CompilerM CircuitState) :=
  keepsC_iff.mpr TripleC.get

theorem KeepsC.set {I : Void IO.RealWorld → Prop} (s : CircuitState) :
    KeepsC mctx mref cctx cref I (set s : CompilerM PUnit) :=
  keepsC_iff.mpr (TripleC.set s)

theorem KeepsC.modify {I : Void IO.RealWorld → Prop} (f : CircuitState → CircuitState) :
    KeepsC mctx mref cctx cref I (modify f : CompilerM PUnit) :=
  fun _ st => Keeps.pure (PUnit.unit, f st)

theorem KeepsC.read {I : Void IO.RealWorld → Prop} :
    KeepsC mctx mref cctx cref I (read : CompilerM CompilerState) :=
  fun ctx st => Keeps.pure (ctx, st)

theorem KeepsC.getCompilerState {I : Void IO.RealWorld → Prop} :
    KeepsC mctx mref cctx cref I CompilerM.getCompilerState :=
  keepsC_iff.mpr TripleC.getCompilerState

theorem KeepsC.withReader {α : Type} {I : Void IO.RealWorld → Prop} {k : CompilerM α}
    (f : CompilerState → CompilerState) (h : KeepsC mctx mref cctx cref I k) :
    KeepsC mctx mref cctx cref I (withReader f k) :=
  fun ctx st => h (f ctx) st

theorem KeepsC.tryCatch {α : Type} {I : Void IO.RealWorld → Prop} {x : CompilerM α}
    {h : Exception → CompilerM α} (hx : KeepsC mctx mref cctx cref I x)
    (hh : ∀ e, OkExc e → KeepsC mctx mref cctx cref I (h e)) :
    KeepsC mctx mref cctx cref I (MonadExcept.tryCatch x h) :=
  fun ctx st => Keeps.tryCatch (hx ctx st) fun e he => hh e he ctx st

theorem KeepsC.map {α β : Type} {I : Void IO.RealWorld → Prop} {c : CompilerM α} (f : α → β)
    (h : KeepsC mctx mref cctx cref I c) : KeepsC mctx mref cctx cref I (f <$> c) :=
  KeepsC.bind h fun a => KeepsC.pure (f a)

theorem KeepsC.forIn_list {α β : Type} {I : Void IO.RealWorld → Prop}
    (f : α → β → CompilerM (ForInStep β)) (hf : ∀ a b, KeepsC mctx mref cctx cref I (f a b)) :
    ∀ (l : List α) (b : β), KeepsC mctx mref cctx cref I (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact KeepsC.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine KeepsC.bind (hf a b) (fun r => ?_)
    cases r with
    | done b' => exact KeepsC.pure b'
    | yield b' => exact KeepsC.forIn_list f hf l b'

theorem KeepsC.forIn_array {α β : Type} {I : Void IO.RealWorld → Prop}
    (f : α → β → CompilerM (ForInStep β)) (hf : ∀ a b, KeepsC mctx mref cctx cref I (f a b))
    (as : Array α) (b : β) : KeepsC mctx mref cctx cref I (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact KeepsC.forIn_list f hf _ b

theorem KeepsC.forIn_range {β : Type} {I : Void IO.RealWorld → Prop}
    (f : Nat → β → CompilerM (ForInStep β)) (hf : ∀ a b, KeepsC mctx mref cctx cref I (f a b))
    (r : Std.Legacy.Range) (b : β) : KeepsC mctx mref cctx cref I (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact KeepsC.forIn_list f hf _ b

/-- A ref operation written directly in `CompilerM`. -/
theorem KeepsC.refGet {σ : Type} {I : Void IO.RealWorld → Prop} {r : IO.Ref σ}
    (h : Keeps mctx mref cctx cref I (ST.Ref.get r : MetaM σ)) :
    KeepsC mctx mref cctx cref I (ST.Ref.get r : CompilerM σ) :=
  KeepsC.lift h

theorem KeepsC.refSet {σ : Type} {I : Void IO.RealWorld → Prop} {r : IO.Ref σ} {v : σ}
    (h : Keeps mctx mref cctx cref I (ST.Ref.set r v : MetaM Unit)) :
    KeepsC mctx mref cctx cref I (ST.Ref.set r v : CompilerM Unit) :=
  KeepsC.lift h

theorem KeepsC.refModify {σ : Type} {I : Void IO.RealWorld → Prop} {r : IO.Ref σ} {f : σ → σ}
    (h : Keeps mctx mref cctx cref I (ST.Ref.modify r f : MetaM Unit)) :
    KeepsC mctx mref cctx cref I (ST.Ref.modify r f : CompilerM Unit) :=
  KeepsC.lift h

/-- A `BaseIO` action lifted straight into `CompilerM`. -/
theorem KeepsC.liftBaseIO {α : Type} {I : Void IO.RealWorld → Prop} {x : BaseIO α}
    (h : Keeps mctx mref cctx cref I (_root_.liftM x : MetaM α)) :
    KeepsC mctx mref cctx cref I (_root_.liftM x : CompilerM α) :=
  KeepsC.lift h

/-- An `IO` action lifted straight into `CompilerM`. -/
theorem KeepsC.liftIO {α : Type} {I : Void IO.RealWorld → Prop} {x : IO α}
    (h : Keeps mctx mref cctx cref I (_root_.liftM x : MetaM α)) :
    KeepsC mctx mref cctx cref I (_root_.liftM x : CompilerM α) :=
  KeepsC.lift h

/-! ### A result that carries a caught exception: its fact goes to the continuation -/

/-- `try x catch e => h e` with a postcondition: the handler gets an exception
in the class, from the world the failing `x` ended in. -/
theorem Triple.tryCatchQ {α : Type} {I : Void IO.RealWorld → Prop} {x : MetaM α}
    {h : Exception → MetaM α} {Q : α → Void IO.RealWorld → Prop}
    (hx : Triple mctx mref cctx cref I x Q (fun e w => I w ∧ OkExc e))
    (hh : ∀ e, OkExc e → Triple mctx mref cctx cref I (h e) Q (fun e w => I w ∧ OkExc e)) :
    Triple mctx mref cctx cref I (MonadExcept.tryCatch x h) Q (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have h1 := hx w hw
  change match (Core.tryCatch (x mctx mref) (fun e => h e mctx mref)) cctx cref w with
    | .ok a w' => Q a w' | .error e w' => I w' ∧ OkExc e
  unfold Core.tryCatch
  change match (EST.tryCatch (x mctx mref cctx cref)
      (fun ex => (if (ex.isInterrupt || ex.isRuntime) = true then (MonadExcept.throw ex : CoreM α)
        else h ex mctx mref) cctx cref)) w with
    | .ok a w' => Q a w' | .error e w' => I w' ∧ OkExc e
  unfold EST.tryCatch
  cases hxw : x mctx mref cctx cref w with
  | ok a w1 => rw [hxw] at h1; exact h1
  | error e w1 =>
    rw [hxw] at h1
    dsimp only
    by_cases hc : (e.isInterrupt || e.isRuntime) = true
    · rw [if_pos hc]; exact h1
    · rw [if_neg hc]
      exact hh e h1.2 w1 h1.1

theorem TripleC.tryCatchQ {α : Type} {I : Void IO.RealWorld → Prop} {x : CompilerM α}
    {h : Exception → CompilerM α} {Q : α → Void IO.RealWorld → Prop}
    (hx : TripleC mctx mref cctx cref I x Q (fun e w => I w ∧ OkExc e))
    (hh : ∀ e, OkExc e → TripleC mctx mref cctx cref I (h e) Q (fun e w => I w ∧ OkExc e)) :
    TripleC mctx mref cctx cref I (MonadExcept.tryCatch x h) Q (fun e w => I w ∧ OkExc e) :=
  fun ctx st => Triple.tryCatchQ (hx ctx st) fun e he => hh e he ctx st

/-- A bind on a program whose result carries a caught exception (its second
component): the continuation is asked only for an exception in the class. -/
theorem KeepsC.bindCaught {σ β : Type} (L : RefLaws mref cref) (D : Nat)
    {c : CompilerM (σ × Option Exception)} {f : σ × Option Exception → CompilerM β}
    (h1 : TripleC mctx mref cctx cref (J L D) c (fun a w => J L D w ∧ OkOpt a.2) (JE L D))
    (h2 : ∀ a, OkOpt a.2 → KeepsC mctx mref cctx cref (J L D) (f a)) :
    KeepsC mctx mref cctx cref (J L D) (c >>= f) :=
  keepsC_iff.mpr (TripleC.bind h1 fun a ctx st w hw => keepsC_iff.mp (h2 a hw.2) ctx st w hw.1)

/-- `KeepsC.bindCaught` under an early-return layer (`ExceptT`). -/
theorem KeepsC.bindCaughtE {ρ σ β : Type} (L : RefLaws mref cref) (D : Nat)
    {c : CompilerM (σ × Option Exception)} {f : σ × Option Exception → ExceptT ρ CompilerM β}
    (h1 : TripleC mctx mref cctx cref (J L D) c (fun a w => J L D w ∧ OkOpt a.2) (JE L D))
    (h2 : ∀ a, OkOpt a.2 → KeepsC mctx mref cctx cref (J L D) (f a)) :
    KeepsC mctx mref cctx cref (J L D)
      (((_root_.liftM c : ExceptT ρ CompilerM (σ × Option Exception)) >>= f :
        ExceptT ρ CompilerM β)) :=
  keepsC_iff.mpr (TripleC.bind
    (c := ((_root_.liftM c : ExceptT ρ CompilerM (σ × Option Exception)) :
      CompilerM (Except ρ (σ × Option Exception))))
    (Q := fun r w => J L D w ∧ ∀ a, r = Except.ok a → OkOpt a.2)
    (TripleC.bind h1 fun a => TripleC.pure (a := (Except.ok a : Except ρ (σ × Option Exception)))
      fun w hw => ⟨hw.1, fun a' h => by cases h; exact hw.2⟩)
    (fun r => by
      cases r with
      | ok a => exact fun ctx st w hw => keepsC_iff.mp (h2 a (hw.2 a rfl)) ctx st w hw.1
      | error e => exact TripleC.pure (a := (Except.error e : Except ρ β)) fun w hw => hw.1))

theorem KeepsC.pureE {ρ α : Type} {I : Void IO.RealWorld → Prop} (a : α) :
    KeepsC mctx mref cctx cref I (Pure.pure a : ExceptT ρ CompilerM α) :=
  KeepsC.pure (Except.ok a)

theorem KeepsC.throwE {ρ α : Type} {I : Void IO.RealWorld → Prop} (r : ρ) :
    KeepsC mctx mref cctx cref I (throwThe ρ r : ExceptT ρ CompilerM α) :=
  KeepsC.pure (Except.error r)

theorem KeepsC.bindE {ρ α β : Type} {I : Void IO.RealWorld → Prop} {m : ExceptT ρ CompilerM α}
    {f : α → ExceptT ρ CompilerM β} (h1 : KeepsC mctx mref cctx cref I m)
    (h2 : ∀ a, KeepsC mctx mref cctx cref I (f a)) :
    KeepsC mctx mref cctx cref I ((m >>= f : ExceptT ρ CompilerM β)) :=
  KeepsC.bind (c := (m : CompilerM (Except ρ α))) h1 fun r => by
    cases r with
    | ok a => exact h2 a
    | error e => exact KeepsC.pure (Except.error e)

theorem KeepsC.liftE {ρ α : Type} {I : Void IO.RealWorld → Prop} {c : CompilerM α}
    (h : KeepsC mctx mref cctx cref I c) :
    KeepsC mctx mref cctx cref I (_root_.liftM c : ExceptT ρ CompilerM α) :=
  KeepsC.bind h fun a => KeepsC.pure (Except.ok a)

/-! ## The tactic -/

/-- Theorems `vc` may apply at a call of the constant their conclusion is about. -/
initialize keepsExt : SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k ((m.getD k #[]).push v)
    initial := {} }

/-- The program of a `Keeps` / `KeepsC` statement (`true` for `KeepsC`). -/
def keepsProg? (t : Expr) : Option (Bool × Expr) :=
  if t.isAppOfArity ``Keeps 7 then some (false, t.appArg!)
  else if t.isAppOfArity ``KeepsC 7 then some (true, t.appArg!)
  else none

/-- `@[keeps]`: register a theorem concluding `Keeps … (c …)` or `KeepsC … (c …)`. -/
syntax (name := keepsAttr) "keeps" : attr

initialize registerBuiltinAttribute {
  name := `keepsAttr
  descr := "a theorem `vc` applies at a call of the definition it is about"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let key ← MetaM.run' <| forallTelescope info.type fun _ body => do
      match keepsProg? body with
      | some (_, p) =>
        match p.getAppFn with
        | .const c _ => pure c
        | _ => throwError "@[keeps]: the program's head is not a constant"
      | none => throwError "@[keeps]: not a Keeps / KeepsC statement"
    keepsExt.add (key, decl) kind }

/-- Walk each alternative of a `match` once, as a local fact, and close every
case of the split with it. OFF by default: measured on the helpers file it
made the build 60 times slower (3 s → 190 s) — an alternative walked without
the split's equations is walked in full, also where the split would have
closed it — so it is kept only as an experiment for a `match` whose catch-all
is large. -/
register_option vc.shareAlts : Bool := { defValue := false }

/-- Walk a join point once, as a local fact (on by default; off only to
measure what sharing saves). -/
register_option vc.shareJoinPoints : Bool := { defValue := true }

/-- Wall-clock budget of one `vc` call in milliseconds (0: none). When it is
exceeded the tactic fails and reports where its time went. -/
register_option vc.budgetMs : Nat := { defValue := 0 }

/-- Print the head of every program `vc` visits (to find a step that hangs). -/
register_option vc.trace : Bool := { defValue := false }

/-- Report where `vc` spent its time, also on success. -/
register_option vc.stats : Bool := { defValue := false }

/-- Per-stage counters of the current `vc` call: stage ↦ (calls, milliseconds). -/
initialize vcStats : IO.Ref (Std.HashMap String (Nat × Nat)) ← IO.mkRef {}
initialize vcStart : IO.Ref Nat ← IO.mkRef 0
initialize vcLastUnfold : IO.Ref Name ← IO.mkRef .anonymous
/-- Programs visited, up to the names of local variables: shape ↦ (visits, a
representative). Only filled under `vc.stats` / a budget. -/
initialize vcShapes : IO.Ref (Std.HashMap UInt64 (Nat × Expr)) ← IO.mkRef {}
/-- The chain of programs being walked (outermost first), as short labels. -/
initialize vcStack : IO.Ref (Array String) ← IO.mkRef #[]
/-- For a program shape: the chain at its first visit; and, for the largest
shape seen twice, the two chains (to see where a duplication starts). -/
initialize vcFirstPath : IO.Ref (Std.HashMap UInt64 (Array String)) ← IO.mkRef {}
initialize vcDup : IO.Ref (Option (Nat × Array String × Array String)) ← IO.mkRef none

namespace VC

/-- A note in the trace file `VC_TRACE_FILE` (written at once: a command's
stderr is shown only when the command ends). -/
def vcNote (msg : Unit → MetaM String) : MetaM Unit := do
  if let some f ← IO.getEnv "VC_TRACE_FILE" then
    let m ← msg ()
    IO.FS.withFile f .append fun hd => hd.putStrLn m

/-- Run `x`, charging its time to `stage`. -/
def timed {α : Type} (stage : String) (x : MetaM α) : MetaM α := do
  let t0 ← IO.monoMsNow
  vcNote fun _ => return s!"  > {stage}"
  try x
  finally
    let dt := (← IO.monoMsNow) - t0
    vcStats.modify fun m => let (c, ms) := m.getD stage (0, 0); m.insert stage (c + 1, ms + dt)

/-- The programs visited most often, with how often and how large they are. -/
def shapesLine : MetaM String := do
  let l := ((← vcShapes.get).toList.map (·.2)).mergeSort (fun a b => a.1 ≥ b.1)
  let mut out := ""
  for (c, e) in l.take 12 do
    let txt := ((← ppExpr e).pretty.replace "\n" " ").take 150
    out := out ++ s!"\n  {c}× [size {e.approxDepth}] {txt}"
  -- the LARGEST programs visited more than once: where a duplication starts
  out := out ++ "\n  largest revisited:"
  let big := (l.filter (·.1 ≥ 2)).mergeSort (fun a b => a.2.approxDepth ≥ b.2.approxDepth)
  for (c, e) in big.take 8 do
    let txt := ((← ppExpr e).pretty.replace "\n" " ").take 220
    out := out ++ s!"\n  {c}× [size {e.approxDepth}] {txt}"
  return out

def statsLine : MetaM String := do
  let m ← vcStats.get
  let (heads, stages) := m.toList.partition (·.1.startsWith "@")
  let l := stages.mergeSort (fun a b => a.2.2 ≥ b.2.2)
  let hs := (heads.mergeSort (fun a b => a.2.1 ≥ b.2.1)).take 14
  return ", ".intercalate (l.map fun (k, c, ms) => s!"{k}: {c}× {ms}ms") ++ " | visits " ++
    ", ".intercalate (hs.map fun (k, c, _) => s!"{k} {c}") ++ " | most revisited programs:" ++
    (← shapesLine) ++ (match ← vcDup.get with
      | some (sz, a, b) =>
        let common := (a.zip b).takeWhile (fun (x, y) => x == y) |>.size
        s!"\n  largest program walked twice (size {sz}): the two walks share {common} enclosing steps, then\n    1st: {(a.extract common (common + 6)).toList}\n    2nd: {(b.extract common (common + 6)).toList}\n    last shared: {(a.extract (common - 3) common).toList}\n    end of 2nd: {(b.extract (b.size - 9) b.size).toList}"
      | none => "")

/-- Apply `e` to `g` by its SYNTACTIC binders only: instantiate them, unify
the conclusion with the goal, and return what is left to prove. (`apply`
also unfolds the conclusion to find more binders — `Keeps` is a `∀` —
and can then miss the intended instance.) -/
def applyExact (g : MVarId) (e : Expr) : MetaM (List MVarId) := g.withContext do
  let (ms, bis, concl) ← forallMetaTelescope (← instantiateMVars (← inferType e))
  let gT ← instantiateMVars (← g.getType)
  -- a `Keeps` / `KeepsC` statement against one: argument by argument. (Unifying
  -- the two applications whole, a mismatch in an early argument — another
  -- context — makes the unifier unfold `Keeps` on both sides and compare the
  -- runs of the two programs: unbounded time and memory on a large program.)
  let ok ← match keepsProg? concl.cleanupAnnotations, keepsProg? gT.cleanupAnnotations with
    | some (c1, _), some (c2, _) =>
      if c1 != c2 then pure false
      else
        let (as, bs) := (concl.cleanupAnnotations.getAppArgs, gT.cleanupAnnotations.getAppArgs)
        let mut ok := true
        for a in as, b in bs do
          if ok then
            unless ← isDefEq a b do ok := false
        pure ok
    | _, _ => isDefEq concl gT
  unless ok do
    throwError "vc: {e} does not apply"
  for m in ms, bi in bis do
    if bi.isInstImplicit then
      unless ← m.mvarId!.isAssigned do
        m.mvarId!.assign (← synthInstance (← inferType m))
  g.assign (mkAppN e ms)
  let mut out := []
  for m in ms do
    unless ← m.mvarId!.isAssigned do
      -- a `Unit` argument: unification succeeds by eta for `Unit` without
      -- assigning it (a join point `jp : Unit → m α` called as `jp ()`); it has
      -- one value
      let mT ← whnfR (← instantiateMVars (← inferType m))
      if mT.isConstOf ``Unit || mT.isAppOf ``PUnit then
        m.mvarId!.assign (if mT.isConstOf ``Unit then mkConst ``Unit.unit
          else mkConst ``PUnit.unit mT.getAppFn.constLevels!)
        continue
      -- what is left must be a proposition: an undetermined type or value
      -- means the statement did not really match
      unless ← isProp (← inferType m) do throwError "vc: {e} leaves {← inferType m} undetermined"
      out := out ++ [m.mvarId!]
  return out

/-- Try `k`; undo everything it did if it fails. -/
def attempt (k : MetaM Unit) : MetaM Bool := do
  let s ← saveState
  try k; return true catch _ => s.restore; return false

/-- The constants never unfolded: the monad operations the rules are about. -/
def opaqueHeads : List Name :=
  [``Bind.bind, ``Pure.pure, ``ite, ``dite, ``MonadExcept.throw, ``throw, ``Lean.throwError,
   ``liftM, ``monadLift, ``MonadLiftT.monadLift, ``MonadLift.monadLift, ``CompilerM.liftMetaM,
   ``get, ``getThe, ``MonadState.get, ``set, ``MonadStateOf.set, ``modify, ``modifyGet,
   ``read, ``readThe, ``MonadReader.read, ``withReader, ``MonadWithReaderOf.withReader,
   ``MonadWithReader.withReader, ``CompilerM.getCompilerState, ``ST.Ref.get, ``ST.Ref.set,
   ``ST.Ref.modify, ``ST.Ref.modifyGet, ``IO.mkRef, ``List.mapM, ``ForIn.forIn, ``forIn]

/-- Could the statement pattern `pat` (its binders are `xs`) be about the
program `p`? Decided on syntax alone, before any unification: same head
constant, and at every EXPLICIT argument the pattern fixes by a constant
head, the program has that head too. (Unifying a pattern with an unrelated
large program makes the unifier unfold the program; this filter is what keeps
a failed attempt cheap.) -/
def mayMatch (xs : Array Expr) (pat p : Expr) : MetaM Bool := do
  let (pf, qf) := (pat.getAppFn, p.getAppFn)
  if pf.isFVar && xs.contains pf then return true
  unless pf.isConst && qf.isConst do return true
  unless pf.constName! == qf.constName! do return false
  let (pa, qa) := (pat.getAppArgs, p.getAppArgs)
  unless pa.size == qa.size do return false
  let info ← getFunInfoNArgs pf pa.size
  for i in [0:pa.size] do
    if h : i < info.paramInfo.size then
      unless info.paramInfo[i].isExplicit do continue
    let (a, b) := (pa[i]!.getAppFn, qa[i]!.getAppFn)
    if a.isConst then
      if b.isConst then
        unless a.constName! == b.constName! do return false
      else unless b.isFVar || b.isMVar || b.isProj do return false
  return true

/-- Close `g` by a tactic, with no error recovery: a failing tactic must fail,
not admit the goal. -/
def closeBy (g : MVarId) (stx : Syntax) : MetaM Unit := do
  let gs ← (Lean.Elab.Term.withoutErrToSorry
    (Lean.Elab.Tactic.run g (Lean.Elab.Tactic.withoutRecover (Lean.Elab.Tactic.evalTactic stx)))).run'
  unless gs.isEmpty do throwError "not closed"

/-- Close a side goal: a hypothesis, or constructors (of `Framed`, `SideRef`),
each tried only when its statement's program has the goal's head. -/
partial def side (g : MVarId) (depth : Nat := 4) : MetaM Unit := g.withContext do
  if ← attempt g.assumption then return
  let tm ← instantiateMVars (← g.getType)
  -- the inline attempt's result fact (`KeepsC.bindCaught`'s first premise)
  if tm.isAppOf ``Tools.ShippingChildInv.TripleC then
    -- (the lemma is proved after this file: named by a plain identifier, a
    -- quoted one would be hygienic and not resolve)
    -- with the translator's hypothesis from the context (the program applies
    -- an eta-expansion of the translator: by definitional unfolding)
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if ← attempt (do closeBy g (← `(tactic|
          exact $(mkIdent `Tools.ShippingChildInv.tryInlineUnfold_tripleC) _ _ _
            (fun mctx cctx e hint top named => $(mkIdent d.userName) mctx cctx e hint top named)
            _ _ _))) then return
    throwError "vc: no result fact for {tm}"
  -- a message / exception of the tracked class: the closure rules
  if tm.isAppOf ``Tools.ShippingChildInv.OkMsg || tm.isAppOf ``Tools.ShippingChildInv.OkExc then
    if ← attempt (do closeBy g (← `(tactic| okmsg))) then return
    -- from a returned caught exception (a hypothesis `OkOpt (some ex)`)
    for d in ← getLCtx do
      if (← instantiateMVars d.type).isAppOf ``Tools.ShippingChildInv.OkOpt then
        if ← attempt (do closeBy g (← `(tactic| exact $(mkIdent d.userName) _ rfl))) then return
    throwError "vc: the message is not shown to be in the tracked class: {tm}"
  if tm.isAppOf ``Tools.ShippingChildInv.OkOpt then
    if ← attempt (do closeBy g (← `(tactic|
        first | exact Tools.ShippingChildInv.OkOpt.none
              | exact Tools.ShippingChildInv.OkOpt.some (by assumption)))) then return
    throwError "vc: the returned exception is not shown to be in the tracked class: {tm}"
  -- a size bound (the premise of an induction hypothesis of a definition
  -- recursive on sub-terms): arithmetic over `sizeOf`
  let t0 ← instantiateMVars (← g.getType)
  if t0.isAppOfArity ``LT.lt 4 && (t0.getArg! 0).isConstOf ``Nat then
    if ← attempt (do closeBy g (← `(tactic| first | omega | (subst_vars; simp only [Lean.Expr.app.sizeOf_spec] at *; omega)))) then return
  if depth == 0 then throwError "vc: side goal {← g.getType}"
  let t ← whnfR (← instantiateMVars (← g.getType))
  let .const ind _ := t.getAppFn | throwError "vc: side goal {t}"
  let some (.inductInfo ii) := (← getEnv).find? ind | throwError "vc: side goal {t}"
  let goalHead := t.appArg!.getAppFn
  for ctor in ii.ctors do
    -- a constructor about another operation is not tried
    let ok ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels ctor)) fun xs body => do
      let h := body.appArg!.getAppFn
      if !(h.isFVar || h.isMVar || !(h.isConst && goalHead.isConst) || h.constName! == goalHead.constName!) then
        return false
      mayMatch xs body.appArg! t.appArg!
    unless ok do continue
    if ← attempt (do
        let gs ← applyExact g (← mkConstWithFreshMVarLevels ctor)
        for g' in gs do side g' (depth - 1)) then return
  throwError "vc: no law for {t}"

/-- One `let` / `have` / beta step at the head of the program, if any. -/
def simpHead? (p : Expr) : Option Expr :=
  let p' := p.consumeMData
  if p'.isLet then some (p'.letBody!.instantiate1 p'.letValue!)
  else if p'.isHeadBetaTarget then some p'.headBeta
  -- a `let` in function position (a `CompilerM` action applied to its states)
  else if p'.getAppFn.isLet then
    some (mkAppN (p'.getAppFn.letBody!.instantiate1 p'.getAppFn.letValue!) p'.getAppArgs)
  else if p' != p then some p'
  else none

/-- Close a goal whose hypotheses contradict each other (a branch the
surrounding `match` / `if` has already excluded). -/
def absurdBranch (g : MVarId) : MetaM Unit := do
  -- bounded: on a large context `simp_all` can run very long, and this is
  -- only an attempt
  let x : MetaM Unit := closeBy g (← `(tactic| first | contradiction | (exfalso; simp_all)))
  let bounded : MetaM Unit :=
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 10000 * 1000 }) (withCurrHeartbeats x)
  tryCatchRuntimeEx bounded fun e => throw (Exception.error .missing m!"not absurd ({e.toMessageData})")

/-- A context read: the run returns in the world it started in, by computation. -/
def readOnly (g : MVarId) : MetaM Unit := do
  let [g'] ← applyExact g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.of_ok)
    | throwError "of_ok"
  closeBy g' (← `(tactic| (intro w; exact ⟨_, rfl⟩)))

mutual

/-- Apply `e`, then walk every goal it leaves. -/
partial def applyThen (g : MVarId) (e : Expr) (fuel : Nat) : MetaM Unit := do
  let gs ← applyExact g e
  for g' in gs do
    unless ← g'.isAssigned do walk g' fuel

/-- If `e` applies, COMMIT to it: walk what it leaves, and let a failure there
be the failure (it is the one worth reporting). `false` if `e` does not apply. -/
partial def commitApply (g : MVarId) (e : Expr) (fuel : Nat) : MetaM Bool := do
  let s ← saveState
  let key := "apply:" ++ (if e.isConst then (toString e.constName!).replace "Tools.ShippingChildInv." "" else "hyp")
  let gs ← try timed key (applyExact g e) catch _ => s.restore; return false
  for g' in gs do
    unless ← g'.isAssigned do walk g' fuel
  return true

/-- Walk a goal: a `Keeps` / `KeepsC` statement by its program, anything else
as a side goal. -/
partial def walk (g : MVarId) (fuel : Nat) : MetaM Unit := do
  if fuel == 0 then throwError "vc: out of fuel"
  vcStats.modify fun m => let (c, ms) := m.getD "walk" (0, 0); m.insert "walk" (c + 1, ms)
  let budget := vc.budgetMs.get (← getOptions)
  if budget != 0 && (← IO.monoMsNow) - (← vcStart.get) > budget then
    throw (Exception.error (← getRef) (MessageData.tagged `vcFinal
      m!"vc: over its {budget} ms budget — {← statsLine}"))
  let (_, g) ← g.intros
  let depth := (← vcStack.get).size
  try
    try walkCore g (fuel - 1)
    finally vcStack.modify (·.shrink depth)
  catch e =>
    -- a branch that cannot happen (only for a program's goal: a side goal
    -- that fails is just not provable this way)
    let isProg := (keepsProg? (← instantiateMVars (← g.getType)).cleanupAnnotations).isSome
    -- only at the innermost failing goal: an enclosing goal has no more
    -- hypotheses than it, so if that one is not absurd neither is this one
    vcNote fun _ => return s!"  failed: {((← e.toMessageData.toString).take 300)}"
    if e.toMessageData.hasTag (· == `vcFinal) then throw e
    let headName := match keepsProg? (← instantiateMVars (← g.getType)).cleanupAnnotations with
      | some (_, q) => toString q.getAppFn.constName?
      | none => "side"
    -- (`isProg && (← …)` would run the attempt first: no short-circuit under `←`)
    let closed ← if isProg then timed s!"absurd@{headName}" (attempt (absurdBranch g)) else pure false
    unless closed do
      throw (Exception.error e.getRef (MessageData.tagged `vcFinal e.toMessageData))

partial def walkCore (g : MVarId) (fuel : Nat) : MetaM Unit := do
  g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let some (isC, p) := keepsProg? t | side g
  let pm0 := p.consumeMData
  if vc.stats.get (← getOptions) || vc.budgetMs.get (← getOptions) != 0 then
    let h := p.getAppFn
    let fvName ← if h.isFVar then h.fvarId!.getUserName else pure .anonymous
    let k := "@" ++ (if h.isConst then toString h.constName! else if h.isFVar then
      toString fvName else if pm0.isLet then "let:" ++ toString pm0.letName! else "other")
    vcStats.modify fun m => let (c, ms) := m.getD k (0, 0); m.insert k (c + 1, ms)
    -- the program's shape: local variables forgotten
    let shape := (p.replace fun e => if e.isFVar then some (mkConst `x) else none).hash
    vcShapes.modify fun m => let (c, _) := m.getD shape (0, p); m.insert shape (c + 1, p)
    let label := s!"{if isC then "C" else "M"}:{if h.isConst then toString h.constName!.getString! else if h.isFVar then toString fvName else if pm0.isLet then "let " ++ toString pm0.letName! else "·"}#{shape % 10000}"
    let path := (← vcStack.get).push label
    match (← vcFirstPath.get).get? shape with
    | none => vcFirstPath.modify (·.insert shape path)
    | some first =>
      let sz := p.approxDepth.toNat
      if ((← vcDup.get).map (·.1)).getD 0 < sz then vcDup.set (some (sz, first, path))
    vcStack.modify (·.push label)
  if vc.trace.get (← getOptions) then
    let h := p.getAppFn
    IO.eprintln s!"vc {if isC then "C" else "M"} {if h.isConst then toString h.constName! else if h.isFVar then "fvar" else if h.isProj then "proj" else if p.isLet then "let" else if p.isLambda then "lam" else "other"} args={p.getAppNumArgs}"
    unless h.isConst || h.isFVar || h.isProj do IO.eprintln s!"   :: {((← ppExpr p).pretty.take 400)}"
    -- (a command's stderr is shown only when the command ends; a run that does
    -- not end is followed in this file)
    if let some f ← IO.getEnv "VC_TRACE_FILE" then
      let ms := (← IO.monoMsNow) - (← vcStart.get)
      IO.FS.withFile f .append fun hd => hd.putStrLn
        s!"{ms} {if isC then "C" else "M"} {h.constName?.getD (if h.isFVar then `fvar else `other)} args={p.getAppNumArgs} size={p.approxDepth}"
  -- a join point (`have jp := fun r => …; …`, used at several exits of a `do`
  -- block): walked ONCE, as a local fact about `jp`, instead of once per use
  let pm := p.consumeMData
  if pm.isLet then
    let (jn, jT, jv, jb) := (pm.letName!, pm.letType!, pm.letValue!, pm.letBody!)
    -- its result type: `CompilerM α`, `MetaM α`, or either under an `ExceptT ρ`
    -- (an early `return`), which IS the base monad at `Except ρ α`
    let resTy (r : Expr) : Option (Bool × Expr) :=
      if r.isAppOf ``CompilerM then some (true, r.appArg!)
      else if r.isAppOf ``Lean.Meta.MetaM then some (false, r.appArg!)
      else if (r.isAppOf ``ExceptT || r.isAppOf ``EarlyReturnT) && r.getAppNumArgs == 3 then
        let (ρ, m, α) := (r.getArg! 0, r.getArg! 1, r.getArg! 2)
        let exc := mkApp2 (mkConst ``Except [.zero, .zero]) ρ α
        if m.isConstOf ``CompilerM then some (true, exc)
        else if m.isConstOf ``Lean.Meta.MetaM then some (false, exc)
        else none
      else none
    let kind? ← forallTelescope jT fun xs r => do
      -- (also a local action without arguments, `let act : CompilerM α := do …`)
      return (resTy r).map fun (c, a) => (c, a.abstract xs)
    if let some (jC, _) := (if vc.shareJoinPoints.get (← getOptions) then kind? else none) then
      let keepsFn := t.appFn!
      -- a `have` (the body does not depend on the value): the body is walked
      -- for ANY `jp` with the fact — `(fun jp hjp => body's proof) value fact`.
      -- The value is then in no goal of the body's walk; kept there as a local
      -- definition, every `match` split under it carries it in its motive, and
      -- the proof term of a large definition grows past any memory.
      if pm.letNondep! then
        let ka := keepsFn.getAppArgs
        let facts (anyCtx : Bool) : MetaM (Expr × Expr) :=
          forallTelescope jT fun xs r => do
            let some (_, α') := resTy r | throwError "vc: join point type"
            let mk (f mc cc : Expr) := mkAppN (mkConst (if jC then ``KeepsC else ``Keeps))
              #[mc, ka[1]!, cc, ka[3]!, α', ka[5]!, (mkAppN f xs).headBeta]
            let close (f : Expr) : MetaM Expr :=
              if anyCtx then
                withLocalDeclD `mctx' (mkConst ``Lean.Meta.Context) fun mc =>
                  withLocalDeclD `cctx' (mkConst ``Lean.Core.Context) fun cc => do
                    mkForallFVars (#[mc, cc] ++ xs) (mk f mc cc)
              else mkForallFVars xs (mk f ka[0]! ka[2]!)
            -- about the value, and about a variable standing for it
            let t1 ← close jv
            let t2 ← withLocalDeclD jn jT fun jp => do
              let hT ← close jp
              withLocalDeclD `hjp hT fun hjp =>
                mkForallFVars #[jp, hjp] (mkApp keepsFn (jb.instantiate1 jp))
            pure (t1, t2)
        let run (anyCtx : Bool) : MetaM Unit := do
          let (t1, t2) ← facts anyCtx
          let h1 ← mkFreshExprSyntheticOpaqueMVar t1
          walk h1.mvarId! fuel
          let h1 ← (do
            let v ← instantiateMVars h1
            if v.hasMVar then pure h1
            else timed "seal" (mkAuxTheorem t1 v) : MetaM Expr)
          let h2 ← mkFreshExprSyntheticOpaqueMVar t2
          walk h2.mvarId! fuel
          -- each of the two, once proved, is an auxiliary theorem (checked by
          -- the kernel there): the enclosing proof term refers to it by name
          let v2 ← instantiateMVars h2
          let h2 ← if v2.hasMVar then pure h2 else timed "seal" (mkAuxTheorem t2 v2)
          g.assign (mkApp2 h2 jv h1)
        let sj ← saveState
        try run true
        catch _ =>
          sj.restore
          run false
        return
      let g1 ← g.replaceTargetDefEq (mkLet jn jT jv (mkApp keepsFn jb))
      let (jp, g2) ← g1.intro jn
      -- the fact, for EVERY Meta and Core context if that can be walked (the
      -- join point may be used under a changed context — `withLocalDecl` — and
      -- a fact about this context only would not apply there, so its body
      -- would be walked again at each such use); else for this context
      let stmt (anyCtx : Bool) : MetaM Expr := g2.withContext do
        forallTelescope jT fun xs r => do
          let ka := keepsFn.getAppArgs
          let some (_, α') := resTy r | throwError "vc: join point type"
          let mk (mc cc : Expr) := mkAppN (mkConst (if jC then ``KeepsC else ``Keeps))
            #[mc, ka[1]!, cc, ka[3]!, α', ka[5]!, mkAppN (mkFVar jp) xs]
          if anyCtx then
            withLocalDeclD `mctx' (mkConst ``Lean.Meta.Context) fun mc =>
              withLocalDeclD `cctx' (mkConst ``Lean.Core.Context) fun cc => do
                mkForallFVars (#[mc, cc] ++ xs) (mk mc cc)
          else mkForallFVars xs (mk ka[0]! ka[2]!)
      let sj ← saveState
      let (hT, hm) ← try
          let hT ← stmt true
          let hm ← g2.withContext (mkFreshExprSyntheticOpaqueMVar hT)
          walk hm.mvarId! fuel
          pure (hT, hm)
        catch _ =>
          sj.restore
          let hT ← stmt false
          let hm ← g2.withContext (mkFreshExprSyntheticOpaqueMVar hT)
          walk hm.mvarId! fuel
          pure (hT, hm)
      let (_, g3) ← (← g2.assert `hjp hT hm).intro1
      return ← walk g3 fuel
  -- `let`, `have`, beta
  if let some p' := simpHead? p then
    let g ← g.replaceTargetDefEq (mkApp t.appFn! p')
    return ← walk g fuel
  let fn := p.getAppFn
  let rule (kn cn : Name) : MetaM Unit := do
    applyThen g (← mkConstWithFreshMVarLevels (if isC then cn else kn)) fuel
  -- the same rule in the base monad, or under an `ExceptT` (early `return`)
  let rule2 (kn cn kE cE : Name) : MetaM Unit := do
    if ← commitApply g (← mkConstWithFreshMVarLevels (if isC then cn else kn)) fuel then return
    applyThen g (← mkConstWithFreshMVarLevels (if isC then cE else kE)) fuel
  -- a recursor applied to a variable (`Except.casesOn x …` after an early
  -- `return`): by cases on it
  if let .const rn _ := fn then
    if isCasesOnRecursor (← getEnv) rn || (← isRec rn) then
      -- on a constructor: compute
      let p' ← whnfCore p
      if p' != p then
        let g ← g.replaceTargetDefEq (mkApp t.appFn! p')
        return ← walk g fuel
      if let some major := p.getAppArgs.findRev? (·.isFVar) then
        let subgoals ← timed "cases" (g.cases major.fvarId!)
        for sg in subgoals do walk sg.mvarId fuel
        return
  -- a `match` on something that is not a variable: name it first (with its
  -- equation), so the split is by cases on a variable
  if let some app ← matchMatcherApp? p then
    let ds := app.discrs.filter (!·.isFVar)
    if !ds.isEmpty then
      let gargs : Array GeneralizeArg := ds.mapIdx fun i d =>
        { expr := d, xName? := some (Name.mkSimple s!"x{i}"), hName? := some (Name.mkSimple s!"hx{i}") }
      if let some (_, g') ← timed "generalize" (try some <$> g.generalize gargs catch _ => pure none) then
        return ← walk g' fuel
  -- a `match`: every alternative once, then each case of the split by it
  if let some app ← matchMatcherApp? p then
    if vc.shareAlts.get (← getOptions) && app.alts.size ≥ 2 then
      let s0 ← saveState
      let shared ← try
          let keepsFn := t.appFn!
          let mut facts : Array (Expr × Expr) := #[]
          for alt in app.alts, n in app.altNumParams do
            let hT ← lambdaBoundedTelescope alt n fun xs body => mkForallFVars xs (mkApp keepsFn body)
            let hm ← mkFreshExprSyntheticOpaqueMVar hT
            walk hm.mvarId! fuel
            facts := facts.push (hT, hm)
          pure (some facts)
        catch _ => s0.restore; pure none
      if let some facts := shared then
        -- exactly THIS `match` (the program's head): `splitTarget?` would pick any
        -- `match` in the goal, also a pure one inside an argument, and every
        -- such split copies the rest of the program into each of its cases
        let gs ← timed "split" (Lean.Meta.Split.splitMatch g p)
        for g' in gs do
          let (_, g') ← g'.intros
          let closed ← g'.withContext do
            let mut done := false
            for (hT, hm) in facts do
              if done then break
              let s1 ← saveState
              let ok ← try
                  let (ms, _, concl) ← forallMetaTelescope hT
                  -- on syntax first: an alternative about another program is not unified
                  let gT := (← instantiateMVars (← g'.getType)).cleanupAnnotations
                  let plausible ← mayMatch ms concl.appArg!.headBeta gT.appArg!
                  if plausible && (← timed "alt-fact" (isDefEq concl gT)) then
                    -- a pattern variable the body does not use: any value
                    for m in ms do
                      unless ← m.mvarId!.isAssigned do
                        m.mvarId!.assign (← mkDefault (← inferType m))
                    g'.assign (mkAppN hm ms)
                    pure true
                  else pure false
                catch _ => pure false
              if ok then done := true else s1.restore
            pure done
          unless closed do walk g' fuel
        return
    -- exactly THIS `match` (the program's head): `splitTarget?` would pick any
    -- `match` in the goal, also a pure one inside an argument, and every such
    -- split copies the rest of the program into each of its cases
    let gs ← timed "split" (Lean.Meta.Split.splitMatch g p)
    for g' in gs do walk g' fuel
    return
  -- a `CompilerM` action given as a function of its states
  if isC && p.isLambda then
    -- a `try … catch` written as a function of the compiler state
    if ← commitApply g
        (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.KeepsC.tryCatch) fuel then return
    return ← applyThen g (← mkConstWithFreshMVarLevels ``KeepsC.intro) fuel
  -- a `MetaM` `try … catch` given as a function of the Meta context
  if !isC && p.isLambda then
    if ← commitApply g
        (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.tryCatch) fuel then return
  -- a hypothesis about this program (the recursive translator, a continuation, the child entry)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let fits ← forallTelescope ty fun _ body => pure <|
      match keepsProg? body with
      | some (c, q) => c == isC && q.getAppFn == fn
      | none => false
    if fits then
      vcNote fun _ => return s!"  hyp {← d.fvarId.getUserName} fits"
      if ← commitApply g d.toExpr fuel then return
      vcNote fun _ => return s!"  hyp {← d.fvarId.getUserName} not applied"
      if vc.trace.get (← getOptions) then
        let s ← saveState
        try discard <| applyExact g d.toExpr
        catch e => IO.eprintln s!"vc hyp {← d.fvarId.getUserName} fits, not applied: {← e.toMessageData.toString}\n  hyp: {← ppExpr ty}\n  goal: {← ppExpr t}"
        s.restore
  -- `try … catch` (the instance's `tryCatch` field, applied)
  -- (a projection only if it IS the `tryCatch` field: field 1 of `MonadExcept` /
  -- `MonadExceptOf`; unifying the rule with any other projection is costly)
  let isTryCatchProj := match fn with
    | .proj sn i _ => (sn == ``MonadExcept || sn == ``MonadExceptOf) && i == 1
    | _ => false
  if isTryCatchProj || fn.isConstOf ``MonadExcept.tryCatch ||
      fn.isConstOf ``tryCatchThe || fn.isConstOf ``MonadExceptOf.tryCatch then
    if ← timed "tryCatch?" (attempt (rule ``Tools.ShippingChildInv.Keeps.tryCatch ``Tools.ShippingChildInv.KeepsC.tryCatch)) then
      return
  -- a field of an instance, applied (e.g. the `default` of a monadic type): reduce it
  if fn.isProj then
    let inst ← timed "projInst" (withTransparency .instances (whnf fn.projExpr!))
    let p' ← whnfCore (mkAppN (fn.updateProj! inst) p.getAppArgs)
    if p' != p then
      let g ← g.replaceTargetDefEq (mkApp t.appFn! p')
      return ← walk g fuel
  -- a `CompilerM` action applied to its two states (inside a `MetaM`
  -- continuation): back to the `CompilerM` rules, before any `MetaM` rule is
  -- tried against it (unifying those would unfold the `CompilerM` instances)
  if !isC && p.getAppNumArgs ≥ 2 then
    let c' := p.appFn!.appFn!
    let ct ← inferType c'
    let isCM := ct.isAppOf ``CompilerM ||
      (ct.isAppOf ``ReaderT && (ct.getAppArgs[0]?.map (·.isConstOf ``CompilerState)).getD false)
    if isCM then
      if ← commitApply g (← mkConstWithFreshMVarLevels ``KeepsC.apply) fuel then return
  -- a local definition (a join point being walked): its value
  if fn.isFVar then
    if let some v ← fn.fvarId!.getValue? then
      vcNote fun _ => return s!"  local value of {← fn.fvarId!.getUserName}"
      let g ← g.replaceTargetDefEq (mkApp t.appFn! (p.replace fun e => if e == fn then some v else none).headBeta)
      return ← walk g fuel
  match fn with
  | .const c _ =>
    -- Lean's own internals are not walked: the public primitive that led
    -- here needs a law
    if (toString c).startsWith "_private.Lean." then
      throwError "vc: reached the Lean internal {c} (last unfolded: {← vcLastUnfold.get}); the public primitive needs a law"
    if c == ``Bind.bind then
      -- a program returning a caught exception with its result: the fact
      -- that it is in the class goes to the continuation
      -- (committed: a failure below is the failure to report)
      if isC then
        if let some x := p.getAppArgs[4]? then
          if x.isAppOf ``Sparkle.Compiler.Elab.Rec.tryInlineUnfold then
            return ← applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.KeepsC.bindCaught) fuel
          if x.isApp && x.appArg!.isAppOf ``Sparkle.Compiler.Elab.Rec.tryInlineUnfold then
            return ← applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.KeepsC.bindCaughtE) fuel
      return ← rule2 ``Keeps.bind ``KeepsC.bind ``Tools.ShippingChildInv.Keeps.bindE
        ``Tools.ShippingChildInv.KeepsC.bindE
    if c == ``Functor.map then return ← rule ``Keeps.map ``KeepsC.map
    -- an `if` whose condition is closed (`true = true` after unfolding a call
    -- with literal arguments): only the branch taken
    if c == ``ite && p.getAppNumArgs == 5 then
      let cond := p.getArg! 1
      -- only the literal case `b₁ = b₂` of two Boolean constants (evaluating
      -- an arbitrary closed condition can run a long computation)
      let lit? : Option Bool := match cond.eq? with
        | some (_, l, r) =>
          if (l.isConstOf ``Bool.true || l.isConstOf ``Bool.false) &&
              (r.isConstOf ``Bool.true || r.isConstOf ``Bool.false) then
            some (l.constName! == r.constName!)
          else none
        | none => none
      if let some d := lit? then
        if true then
          let br := if d then p.getArg! 3 else p.getArg! 4
          let g ← g.replaceTargetDefEq (mkApp t.appFn! br)
          return ← walk g fuel
    -- a `for` loop
    if c == ``ForIn.forIn || c == ``forIn then
      -- the rule by the collection's type (trying the others means unifying
      -- unrelated `ForIn` instances, which is slow)
      let ρ := (p.getAppArgs[1]?.getD default).getAppFn
      let pick : Option (Name × Name) :=
        if ρ.isConstOf ``List then
          some (``Tools.ShippingChildInv.Keeps.forIn_list, ``Tools.ShippingChildInv.KeepsC.forIn_list)
        else if ρ.isConstOf ``Array then
          some (``Tools.ShippingChildInv.Keeps.forIn_array, ``Tools.ShippingChildInv.KeepsC.forIn_array)
        else if ρ.isConstOf ``Std.Legacy.Range then
          some (``Tools.ShippingChildInv.Keeps.forIn_range, ``Tools.ShippingChildInv.KeepsC.forIn_range)
        else none
      if let some (kn, cn) := pick then
        if ← commitApply g (← mkConstWithFreshMVarLevels (if isC then cn else kn)) fuel then return
    if c == ``Pure.pure then
      return ← rule2 ``Keeps.pure ``KeepsC.pure ``Tools.ShippingChildInv.Keeps.pureE
        ``Tools.ShippingChildInv.KeepsC.pureE
    if c == ``ite then return ← rule ``Keeps.ite ``KeepsC.ite
    if c == ``dite then return ← rule ``Keeps.dite ``KeepsC.dite
    if c == ``throwThe || c == ``MonadExceptOf.throw then
      if ← commitApply g (← mkConstWithFreshMVarLevels
          (if isC then ``Tools.ShippingChildInv.KeepsC.throwE else ``Tools.ShippingChildInv.Keeps.throwE)) fuel then
        return
    if c == ``MonadExcept.throw || c == ``throw then
      return ← rule2 ``Keeps.throw ``KeepsC.throw ``Tools.ShippingChildInv.Keeps.throwE
        ``Tools.ShippingChildInv.KeepsC.throwE
    -- registered theorems
    for lem in (keepsExt.getState (← getEnv)).getD c #[] do
      if ← commitApply g (← mkConstWithFreshMVarLevels lem) fuel then return
    if isC && c == ``CompilerM.liftMetaM then
      return ← applyThen g (← mkConstWithFreshMVarLevels ``KeepsC.lift) fuel
    if isC then
      for lem in [``KeepsC.liftM, ``Tools.ShippingChildInv.KeepsC.liftIO,
          ``Tools.ShippingChildInv.KeepsC.liftBaseIO,
          ``Tools.ShippingChildInv.KeepsC.liftE, ``Tools.ShippingChildInv.KeepsC.refGet,
          ``Tools.ShippingChildInv.KeepsC.refSet, ``Tools.ShippingChildInv.KeepsC.refModify,
          ``KeepsC.get, ``KeepsC.set, ``KeepsC.modify,
          ``KeepsC.read, ``KeepsC.getCompilerState, ``KeepsC.withReader] do
        let ok ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels lem)) fun _ body =>
          pure (body.appArg!.getAppFn.constName? == some c)
        if ok then
          if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels lem) fuel) then return
    else
      if [``read, ``readThe, ``MonadReader.read, ``MonadReaderOf.read, ``Lean.getLCtx,
          ``Lean.MonadLCtx.getLCtx, ``Lean.getRef, ``Lean.MonadRef.getRef, ``Lean.getOptions,
          ``Lean.MonadOptions.getOptions].contains c then
        if ← timed "readOnly" (attempt (readOnly g)) then return
      if [``withReader, ``MonadWithReaderOf.withReader, ``MonadWithReader.withReader].contains c then
        if ← attempt (do
            applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.withReader) fuel) then
          return
      -- a `CoreM` context read, lifted
      if c == ``liftM || c == ``monadLift || c == ``MonadLiftT.monadLift then
        if ← timed "readOnly" (attempt (readOnly g)) then return
        -- a lift into an `ExceptT` layer (only when the program's type is one)
        if (← inferType p).isAppOf ``ExceptT then
          if ← commitApply g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.liftE) fuel then
            return
      if c == ``Lean.throwError then
        if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Keeps.throwError) fuel) then return
      if c == ``List.mapM then
        if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Keeps.mapM) fuel) then return
      if c == ``Lean.Meta.withLetDecl then
        return ← applyThen g
          (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.withLetDecl) fuel
      if c == ``Lean.Meta.withLocalDeclD then
        return ← applyThen g
          (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.withLocalDeclD) fuel
      if c == ``Lean.Meta.lambdaTelescope then
        return ← applyThen g
          (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.lambdaTelescope) fuel
      if c == ``Lean.Meta.forallTelescopeReducing then
        return ← applyThen g
          (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.forallTelescopeReducing) fuel
      -- a `CompilerM` action applied to its states
      if p.getAppNumArgs ≥ 2 then
        let c' := p.appFn!.appFn!
        let ct ← inferType c'
        if ct.isAppOf ``CompilerM || ct.isAppOf ``ReaderT then
          if ← commitApply g (← mkConstWithFreshMVarLevels ``KeepsC.apply) fuel then return
      -- an operation whose frame is a law
      if ← timed "framed" (attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Keeps.framed) fuel)) then
        return
    if opaqueHeads.contains c then throwError "vc: no rule for {p}"
    vcLastUnfold.set c
    -- any other definition: unfold it, unless it is recursive
    let g' ← timed "unfold" (try Lean.Meta.unfoldTarget g c catch _ => throwError "vc: cannot unfold {c} in {p}")
    let t' ← instantiateMVars (← g'.getType)
    if t' == t then throwError "vc: {c} is opaque (no rule, no law, no theorem)"
    if let some (_, p') := keepsProg? t' then
      if (p'.find? (·.isConstOf c)).isSome then
        throwError "vc: {c} is recursive and has no @[keeps] theorem"
    walk g' fuel
  | _ => throwError "vc: no rule for {p}"

end

end VC

/-- `unfold` for a private constant of another module (Lean's own loop under
`Array.mapM`), named by its module and name. -/
elab "unfoldPriv" md:ident n:ident : tactic =>
  Lean.Elab.Tactic.liftMetaTactic1 fun g =>
    Lean.Meta.unfoldTarget g (Lean.mkPrivateNameCore md.getId n.getId)

/-- A private constant of another module, by its module and name. -/
elab "privConst%" md:ident n:ident : term =>
  mkConstWithFreshMVarLevels (Lean.mkPrivateNameCore md.getId n.getId)

/-- Walk the goal's program (see the file's header). -/
elab "vc" : tactic => Lean.Elab.Tactic.liftMetaTactic fun g => do
  vcStats.set {}
  vcShapes.set {}
  vcStack.set #[]
  vcFirstPath.set {}
  vcDup.set none
  vcStart.set (← IO.monoMsNow)
  VC.walk g 2000
  VC.vcNote fun _ => return s!"walk done {(← IO.monoMsNow) - (← vcStart.get)}"
  if (← IO.getEnv "VC_TRACE_FILE").isSome then
    let pf ← instantiateMVars (mkMVar g)
    VC.vcNote fun _ => return s!"proof instantiated {(← IO.monoMsNow) - (← vcStart.get)}; mvars left: {pf.hasMVar}"
    let n := pf.numObjs
    VC.vcNote fun _ => return s!"proof objects (shared) {← n} at {(← IO.monoMsNow) - (← vcStart.get)}"
  if vc.stats.get (← getOptions) then
    logInfo m!"vc: {(← IO.monoMsNow) - (← vcStart.get)} ms — {← VC.statsLine}"
  return []

end Tools.ShippingChildInv
