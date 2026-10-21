import Tools.ShippingChildTranslateA
-- UNBUILT (unit B, round 2): runs wa1.. recorded in REPORT-B.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field.
-- Law witnesses: `O : RefLawsAOps MkRefd mref cref`, `hA : AdmCtx O.quiet mctx cctx`,
-- `hS : StableA O.quiet I`; and, ONLY for the rules about `withLocalDeclD`/`withLetDecl`/
-- `lambdaTelescope`/`forallTelescopeReducing`, `T : RefLawsATele O.quiet mref cref`
-- (the separate assumption family; a program that reaches such a call and has no `T` in scope
-- is NOT walked: the tactic fails there and names it).
-- Reused law-free: `Keeps.pure/bind/ite/dite/throw/mapM/tryCatch/map/of_ok/forIn_*`,
-- `KeepsC.*` (Tools/ShippingChildVC.lean), the calculus of Tools/ShippingChildTranslateA.lean,
-- the tactic helpers of Tools/ShippingChildVC.lean (`VC.attempt/closeBy/simpHead?/…`).
-- NOT used: `RefLaws`, `RefLawsCore`, `J L D`, `Keeps.framed`, `Keeps.withLocalDeclD`, …
--
-- # `vca`: the walker `vc` (Tools/ShippingChildVC.lean) for the admissible boundary
--
-- Same algorithm as `vc` (bind/ite/dite/match/let/join-point rules chosen by the program's
-- head, unfolding of non-recursive definitions, registered theorems, hypotheses), with:
--  * `KeepsC` replaced by `KeepsCP` (compiler contexts WITH `CtxOk`); a read of the compiler
--    context hands `CtxOk` to its continuation (`KeepsCP.bindRead`, `bindCtx`);
--  * `Keeps.framed L D` replaced by `keepsA_framed O hA hS` / `keepsA_diag O hA hS` /
--    `keepsA_throwError` (the side goal `FramedA MkRefd p` / `Diag p` closed by constructors);
--  * `Keeps.withReader` replaced by `Keeps.withReaderA` (the update keeps `canUnfold?`, so the
--    context stays admissible; the side goal `∀ m, (f m).canUnfold? = m.canUnfold?` by `rfl`);
--  * the law arguments `O`, `hA`, `hS`, `T` of a rule are taken from the local context (`O`
--    by its type, the Props by `assumption`), and a join-point fact is stated for every
--    ADMISSIBLE context (`∀ mctx' cctx', AdmCtx q mctx' cctx' → …`).

namespace Tools.ShippingChildWalkA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildVertA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The rules not in the calculus yet -/

section Rules
variable {I : Void IO.RealWorld → Prop}

theorem KeepsCP.intro {α : Type} {c : CompilerM α}
    (h : ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
      Keeps mctx mref cctx cref I (c ctx st)) : KeepsCP mctx mref cctx cref I c := h

theorem KeepsCP.apply {α : Type} {c : CompilerM α} (h : KeepsCP mctx mref cctx cref I c)
    (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState) (hc : CtxOk ctx) :
    Keeps mctx mref cctx cref I (c ctx st) := h ctx st hc

theorem KeepsCP.liftM {α : Type} {m : MetaM α} (h : Keeps mctx mref cctx cref I m) :
    KeepsCP mctx mref cctx cref I (_root_.liftM m : CompilerM α) :=
  KeepsCP.of (KeepsC.liftM h)

theorem KeepsCP.liftIO {α : Type} {x : IO α} (h : Keeps mctx mref cctx cref I (_root_.liftM x : MetaM α)) :
    KeepsCP mctx mref cctx cref I (_root_.liftM x : CompilerM α) :=
  KeepsCP.of (KeepsC.liftIO h)

theorem KeepsCP.liftBaseIO {α : Type} {x : BaseIO α}
    (h : Keeps mctx mref cctx cref I (_root_.liftM x : MetaM α)) :
    KeepsCP mctx mref cctx cref I (_root_.liftM x : CompilerM α) :=
  KeepsCP.of (KeepsC.liftBaseIO h)

theorem KeepsCP.refGet {σ : Type} {r : IO.Ref σ}
    (h : Keeps mctx mref cctx cref I (ST.Ref.get r : MetaM σ)) :
    KeepsCP mctx mref cctx cref I (ST.Ref.get r : CompilerM σ) :=
  KeepsCP.of (KeepsC.refGet h)

theorem KeepsCP.refSet {σ : Type} {r : IO.Ref σ} {v : σ}
    (h : Keeps mctx mref cctx cref I (ST.Ref.set r v : MetaM Unit)) :
    KeepsCP mctx mref cctx cref I (ST.Ref.set r v : CompilerM Unit) :=
  KeepsCP.of (KeepsC.refSet h)

theorem KeepsCP.refModify {σ : Type} {r : IO.Ref σ} {f : σ → σ}
    (h : Keeps mctx mref cctx cref I (ST.Ref.modify r f : MetaM Unit)) :
    KeepsCP mctx mref cctx cref I (ST.Ref.modify r f : CompilerM Unit) :=
  KeepsCP.of (KeepsC.refModify h)

theorem KeepsCP.read : KeepsCP mctx mref cctx cref I (MonadReader.read : CompilerM CompilerState) :=
  KeepsCP.of KeepsC.read

/-- **A read of the compiler context hands its provenance to the continuation.** -/
theorem KeepsCP.bindRead {β : Type} {f : CompilerState → CompilerM β}
    (h : ∀ cs, CtxOk cs → KeepsCP mctx mref cctx cref I (f cs)) :
    KeepsCP mctx mref cctx cref I ((MonadReader.read : CompilerM CompilerState) >>= f) :=
  fun ctx st hc => h ctx hc ctx st hc

theorem KeepsCP.tryCatch {α : Type} {x : CompilerM α} {h : Exception → CompilerM α}
    (hx : KeepsCP mctx mref cctx cref I x)
    (hh : ∀ e, OkExc e → KeepsCP mctx mref cctx cref I (h e)) :
    KeepsCP mctx mref cctx cref I (MonadExcept.tryCatch x h) :=
  fun ctx st hc => Keeps.tryCatch (hx ctx st hc) fun e he => hh e he ctx st hc

theorem KeepsCP.map {α β : Type} {c : CompilerM α} (f : α → β)
    (h : KeepsCP mctx mref cctx cref I c) : KeepsCP mctx mref cctx cref I (f <$> c) :=
  KeepsCP.bind h fun a => KeepsCP.pure (f a)

theorem KeepsCP.forIn_list {α β : Type} (f : α → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCP mctx mref cctx cref I (f a b)) :
    ∀ (l : List α) (b : β), KeepsCP mctx mref cctx cref I (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact KeepsCP.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine KeepsCP.bind (hf a b) (fun r => ?_)
    cases r with
    | done b' => exact KeepsCP.pure b'
    | yield b' => exact KeepsCP.forIn_list f hf l b'

theorem KeepsCP.forIn_array {α β : Type} (f : α → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCP mctx mref cctx cref I (f a b)) (as : Array α) (b : β) :
    KeepsCP mctx mref cctx cref I (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact KeepsCP.forIn_list f hf _ b

theorem KeepsCP.forIn_range {β : Type} (f : Nat → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCP mctx mref cctx cref I (f a b)) (r : Std.Legacy.Range) (b : β) :
    KeepsCP mctx mref cctx cref I (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact KeepsCP.forIn_list f hf _ b

theorem KeepsCP.pureE {ρ α : Type} (a : α) :
    KeepsCP mctx mref cctx cref I (Pure.pure a : ExceptT ρ CompilerM α) :=
  KeepsCP.pure (Except.ok a)

theorem KeepsCP.throwE {ρ α : Type} (r : ρ) :
    KeepsCP mctx mref cctx cref I (throwThe ρ r : ExceptT ρ CompilerM α) :=
  KeepsCP.pure (Except.error r)

theorem KeepsCP.bindE {ρ α β : Type} {m : ExceptT ρ CompilerM α} {f : α → ExceptT ρ CompilerM β}
    (h1 : KeepsCP mctx mref cctx cref I m) (h2 : ∀ a, KeepsCP mctx mref cctx cref I (f a)) :
    KeepsCP mctx mref cctx cref I ((m >>= f : ExceptT ρ CompilerM β)) :=
  KeepsCP.bind (c := (m : CompilerM (Except ρ α))) h1 fun r => by
    cases r with
    | ok a => exact h2 a
    | error e => exact KeepsCP.pure (Except.error e)

theorem KeepsCP.liftE {ρ α : Type} {c : CompilerM α} (h : KeepsCP mctx mref cctx cref I c) :
    KeepsCP mctx mref cctx cref I (_root_.liftM c : ExceptT ρ CompilerM α) :=
  KeepsCP.bind h fun a => KeepsCP.pure (Except.ok a)

end Rules

/-! ## A result that carries a caught exception: its fact goes to the continuation

`TripleCP`: the postcondition form of `KeepsCP` (from every `CtxOk` compiler context). Only what
`tryInlineUnfold` and its caller need. -/

/-- `Triple` for a `CompilerM` action, from every compiler context WITH `CtxOk`. -/
def TripleCP (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) {α : Type} (P : Void IO.RealWorld → Prop)
    (c : CompilerM α) (Q : α → Void IO.RealWorld → Prop)
    (R : Exception → Void IO.RealWorld → Prop) : Prop :=
  ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Triple mctx mref cctx cref P (c ctx st) (fun p => Q p.1) R

section TripleCPRules
variable {I : Void IO.RealWorld → Prop}

theorem TripleCP.ofKeepsCP {α : Type} {c : CompilerM α}
    (h : KeepsCP mctx mref cctx cref I c) :
    TripleCP mctx mref cctx cref I c (fun _ => I) (fun e w => I w ∧ OkExc e) :=
  fun ctx st hc => keeps_iff.mp (h ctx st hc)

theorem TripleCP.pure {α : Type} {P : Void IO.RealWorld → Prop} {a : α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (h : ∀ w, P w → Q a w) :
    TripleCP mctx mref cctx cref P (Pure.pure a : CompilerM α) Q R :=
  fun _ st _ => Triple.pure (a := (a, st)) h

theorem TripleCP.bind {α β : Type} {P : Void IO.RealWorld → Prop} {c : CompilerM α}
    {f : α → CompilerM β} {Q : α → Void IO.RealWorld → Prop} {Q' : β → Void IO.RealWorld → Prop}
    {R : Exception → Void IO.RealWorld → Prop}
    (h1 : TripleCP mctx mref cctx cref P c Q R)
    (h2 : ∀ a, TripleCP mctx mref cctx cref (Q a) (f a) Q' R) :
    TripleCP mctx mref cctx cref P (c >>= f) Q' R :=
  fun ctx st hc => Triple.bind (h1 ctx st hc) fun p => by
    obtain ⟨a, s⟩ := p
    exact h2 a ctx s hc

theorem TripleCP.ite {α : Type} {c : Prop} [Decidable c] {P : Void IO.RealWorld → Prop}
    {a b : CompilerM α} {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (ha : c → TripleCP mctx mref cctx cref P a Q R) (hb : ¬c → TripleCP mctx mref cctx cref P b Q R) :
    TripleCP mctx mref cctx cref P (if c then a else b) Q R := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem TripleCP.tryCatchQ {α : Type} {x : CompilerM α} {h : Exception → CompilerM α}
    {Q : α → Void IO.RealWorld → Prop}
    (hx : TripleCP mctx mref cctx cref I x Q (fun e w => I w ∧ OkExc e))
    (hh : ∀ e, OkExc e → TripleCP mctx mref cctx cref I (h e) Q (fun e w => I w ∧ OkExc e)) :
    TripleCP mctx mref cctx cref I (MonadExcept.tryCatch x h) Q (fun e w => I w ∧ OkExc e) :=
  fun ctx st hc => Triple.tryCatchQ (hx ctx st hc) fun e he => hh e he ctx st hc

/-- A bind on a program whose result carries a caught exception (its second component): the
continuation is asked only for an exception in the class. -/
theorem KeepsCP.bindCaught {σ β : Type}
    {c : CompilerM (σ × Option Exception)} {f : σ × Option Exception → CompilerM β}
    (h1 : TripleCP mctx mref cctx cref I c (fun a w => I w ∧ OkOpt a.2)
      (fun e w => I w ∧ OkExc e))
    (h2 : ∀ a, OkOpt a.2 → KeepsCP mctx mref cctx cref I (f a)) :
    KeepsCP mctx mref cctx cref I (c >>= f) :=
  fun ctx st hc => keeps_iff.mpr (Triple.bind (h1 ctx st hc) fun p => by
    obtain ⟨a, s⟩ := p
    exact fun w hw => keeps_iff.mp (h2 a hw.2 ctx s hc) w hw.1)

end TripleCPRules

/-! ## The telescope laws, one by one

`RefLawsATele` (Tools/ShippingChildInvA.lean:301) bundles four laws. A program that runs only
`withLocalDeclD` and `withLetDecl` needs just these two, so each is a named proposition (the
field's own statement) and `RefLawsATele` provides all four. -/

/-- The law for `withLocalDeclD` (`RefLawsATele.localDecl`). -/
def LocalDeclLawA (quiet : Void IO.RealWorld → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)

/-- The law for `withLetDecl` (`RefLawsATele.letDecl`). -/
def LetDeclLawA (quiet : Void IO.RealWorld → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)

/-- The law for `lambdaTelescope` (`RefLawsATele.lamTelescope`). -/
def LamTelescopeLawA (quiet : Void IO.RealWorld → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup)

/-- The law for `forallTelescopeReducing` (`RefLawsATele.telescope`). -/
def ForallTelescopeLawA (quiet : Void IO.RealWorld → Prop)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)

theorem RefLawsATele.localDeclLaw {q : Void IO.RealWorld → Prop}
    (T : RefLawsATele q mref cref) : LocalDeclLawA q mref cref := T.localDecl
theorem RefLawsATele.letDeclLaw {q : Void IO.RealWorld → Prop}
    (T : RefLawsATele q mref cref) : LetDeclLawA q mref cref := T.letDecl
theorem RefLawsATele.lamTelescopeLaw {q : Void IO.RealWorld → Prop}
    (T : RefLawsATele q mref cref) : LamTelescopeLawA q mref cref := T.lamTelescope
theorem RefLawsATele.forallTelescopeLaw {q : Void IO.RealWorld → Prop}
    (T : RefLawsATele q mref cref) : ForallTelescopeLawA q mref cref := T.telescope

/-! ## The law-dependent rules in `Keeps` form -/

section Laws
variable {Fresh : (σ : Type) → IO.Ref σ → Prop} (O : RefLawsAOps Fresh mref cref)
  (hA : AdmCtx O.quiet mctx cctx) {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

theorem keepsA_throwError {α : Type} (msg : MessageData) (hmsg : OkMsg msg) :
    Keeps mctx mref cctx cref I (Lean.throwError msg : MetaM α) :=
  keeps_iff.mpr (tripleA_throwErr O hA hS msg hmsg)

omit O hA hS in
/-- `withReader` on the Meta context by an update that keeps the unfolding callback: the
action, in the (still admissible) changed context. -/
theorem Keeps.withReaderA {q : Void IO.RealWorld → Prop} (hA : AdmCtx q mctx cctx)
    {α : Type} {x : MetaM α} (f : Meta.Context → Meta.Context)
    (hf : ∀ m, (f m).canUnfold? = m.canUnfold?)
    (h : AdmCtx q (f mctx) cctx → Keeps (f mctx) mref cctx cref I x) :
    Keeps mctx mref cctx cref I (withReader f x) :=
  fun w hw => h (fun g hg => hA g ((hf mctx).symm.trans hg)) w hw

theorem keepsA_withLocalDeclD (T : LocalDeclLawA O.quiet mref cref) {α : Type} (n : Name)
    (ty : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) :
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k) :=
  T I hA hS.1 hS.2 n ty k hk

theorem keepsA_withLetDecl (T : LetDeclLawA O.quiet mref cref) {α : Type} (n : Name)
    (ty v : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) :
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k) :=
  T I hA hS.1 hS.2 n ty v k hk

theorem keepsA_lambdaTelescope (T : LamTelescopeLawA O.quiet mref cref) {α : Type} (e : Lean.Expr)
    (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) :
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup) :=
  T I hA hS.1 hS.2 e k cleanup hk

theorem keepsA_forallTelescopeReducing (T : ForallTelescopeLawA O.quiet mref cref) {α : Type}
    (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) :
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k) :=
  T I hA hS.1 hS.2 ty k hk

end Laws

-- the circuit-state primitives and the calculus, registered for the walker
open Lean Elab in
/-- Theorems `vca` may apply at a call of the constant their conclusion is about. -/
initialize keepsAExt : SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k ((m.getD k #[]).push v)
    initial := {} }

/-- The program of a `Keeps` / `KeepsCP` statement (`true` for `KeepsCP`). -/
def keepsProgA? (t : Expr) : Option (Bool × Expr) :=
  if t.isAppOfArity ``Keeps 7 then some (false, t.appArg!)
  else if t.isAppOfArity ``KeepsCP 7 then some (true, t.appArg!)
  else none

/-- `@[keepsA]`: register a theorem concluding `Keeps … (c …)` or `KeepsCP … (c …)`. -/
syntax (name := keepsAAttr) "keepsA" : attr

initialize registerBuiltinAttribute {
  name := `keepsAAttr
  descr := "a theorem `vca` applies at a call of the definition it is about"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let key ← MetaM.run' <| forallTelescope info.type fun _ body => do
      match keepsProgA? body with
      | some (_, p) =>
        match p.getAppFn with
        | .const c _ => pure c
        | _ => throwError "@[keepsA]: the program's head is not a constant"
      | none => throwError "@[keepsA]: not a Keeps / KeepsCP statement"
    keepsAExt.add (key, decl) kind }

namespace VCA
open Tools.ShippingChildInv.VC (attempt closeBy mayMatch timed vcNote simpHead? absurdBranch readOnly opaqueHeads statsLine)

/-- Names the walker must not unfold before trying the law rules. -/
def readHeads : List Name :=
  [``read, ``readThe, ``MonadReader.read, ``MonadReaderOf.read]

/-- Assign the law arguments `O : RefLawsAOps …` of a rule from the local context. -/
def fillLaws (ms : Array Expr) : MetaM Unit := do
  for m in ms do
    unless ← m.mvarId!.isAssigned do
      let ty ← instantiateMVars (← inferType m)
      -- the quietness predicate of a rule (`{q}` of `AdmCtx q`): that of the local `O`
      if ty.isForall && ty.bindingDomain!.isAppOf ``Void && ty.bindingBody!.isProp then
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          if (← instantiateMVars d.type).isAppOf ``RefLawsAOps then
            let s ← saveState
            try
              let q ← mkAppM ``RefLawsAOps.quiet #[d.toExpr]
              if ← isDefEq m q then break
              s.restore
            catch _ => s.restore
      if ty.isAppOf ``RefLawsAOps then
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let s ← saveState
          if ← isDefEq d.type ty then
            m.mvarId!.assign d.toExpr
            break
          else s.restore

/-- `VC.applyExact`, with the law arguments taken from the local context. -/
def applyExactA (g : MVarId) (e : Expr) : MetaM (List MVarId) := g.withContext do
  let (ms, bis, concl) ← forallMetaTelescope (← instantiateMVars (← inferType e))
  let gT ← instantiateMVars (← g.getType)
  let ok ← match keepsProgA? concl.cleanupAnnotations, keepsProgA? gT.cleanupAnnotations with
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
    throwError "vca: {e} does not apply"
  fillLaws ms
  for m in ms, bi in bis do
    if bi.isInstImplicit then
      unless ← m.mvarId!.isAssigned do
        m.mvarId!.assign (← synthInstance (← inferType m))
  g.assign (mkAppN e ms)
  let mut out := []
  for m in ms do
    unless ← m.mvarId!.isAssigned do
      let mT ← whnfR (← instantiateMVars (← inferType m))
      if mT.isConstOf ``Unit || mT.isAppOf ``PUnit then
        m.mvarId!.assign (if mT.isConstOf ``Unit then mkConst ``Unit.unit
          else mkConst ``PUnit.unit mT.getAppFn.constLevels!)
        continue
      unless ← isProp (← inferType m) do throwError "vca: {e} leaves {← inferType m} undetermined"
      out := out ++ [m.mvarId!]
  return out

/-- Close a side goal: a hypothesis, or constructors (of `FramedA`, `Diag`, `SideRef`),
each tried only when its statement's program has the goal's head. -/
partial def side (g : MVarId) (depth : Nat := 4) : MetaM Unit := g.withContext do
  if ← attempt g.assumption then return
  let tm ← instantiateMVars (← g.getType)
  -- the inline attempt's result fact (`KeepsCP.bindCaught`'s first premise)
  if tm.isAppOf ``Tools.ShippingChildWalkA.TripleCP then
    -- (the lemma is proved after this file: named by a plain identifier)
    if ← attempt (do closeBy g (← `(tactic|
        exact $(mkIdent `Tools.ShippingChildLegacyHandlersA.tryInlineUnfold_tripleCP) (by assumption)
          (by assumption) _ (by assumption) (by assumption) _ _ _))) then return
    throwError "vca: no result fact for {tm}"
  if tm.isAppOf ``Tools.ShippingChildInv.OkMsg || tm.isAppOf ``Tools.ShippingChildInv.OkExc then
    if ← attempt (do closeBy g (← `(tactic| okmsg))) then return
    for d in ← getLCtx do
      if (← instantiateMVars d.type).isAppOf ``Tools.ShippingChildInv.OkOpt then
        if ← attempt (do closeBy g (← `(tactic| exact $(mkIdent d.userName) _ rfl))) then return
    throwError "vca: the message is not shown to be in the tracked class: {tm}"
  if tm.isAppOf ``Tools.ShippingChildInv.OkOpt then
    if ← attempt (do closeBy g (← `(tactic|
        first | exact Tools.ShippingChildInv.OkOpt.none
              | exact Tools.ShippingChildInv.OkOpt.some (by assumption)))) then return
    throwError "vca: the returned exception is not shown to be in the tracked class: {tm}"
  -- a size bound (the premise of an induction hypothesis of a definition recursive on
  -- sub-terms): arithmetic over `sizeOf`
  if tm.isAppOfArity ``LT.lt 4 && (tm.getArg! 0).isConstOf ``Nat then
    if ← attempt (do closeBy g (← `(tactic| first | omega | (subst_vars; simp only [Lean.Expr.app.sizeOf_spec] at *; omega)))) then return
  -- the context updates: `(f m).canUnfold? = m.canUnfold?` and the provenance of a changed
  -- compiler context
  if tm.isForall then
    if ← attempt (do closeBy g (← `(tactic| (intro _; rfl)))) then return
    if ← attempt (do closeBy g (← `(tactic| (intro _ hc _ h; exact hc _ h)))) then return
  -- the provenance of the compiler context's cache ref: `CtxOk ctx` and `ctx.exprCache = some r`
  if tm.isAppOf ``Tools.ShippingChildFresh.MkRefd then
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type).isAppOf ``CtxOk then
        if ← attempt (do closeBy g (← `(tactic| exact $(mkIdent d.userName) _ (by assumption)))) then return
  if depth == 0 then throwError "vca: side goal {← g.getType}"
  let t ← whnfR (← instantiateMVars (← g.getType))
  let .const ind _ := t.getAppFn | throwError "vca: side goal {t}"
  let some (.inductInfo ii) := (← getEnv).find? ind | throwError "vca: side goal {t}"
  let goalHead := t.appArg!.getAppFn
  for ctor in ii.ctors do
    let ok ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels ctor)) fun xs body => do
      let h := body.appArg!.getAppFn
      if !(h.isFVar || h.isMVar || !(h.isConst && goalHead.isConst) || h.constName! == goalHead.constName!) then
        return false
      mayMatch xs body.appArg! t.appArg!
    unless ok do continue
    if ← attempt (do
        let gs ← applyExactA g (← mkConstWithFreshMVarLevels ctor)
        for g' in gs do side g' (depth - 1)) then return
  throwError "vca: no law for {t}"

mutual

partial def applyThen (g : MVarId) (e : Expr) (fuel : Nat) : MetaM Unit := do
  let gs ← applyExactA g e
  for g' in gs do
    unless ← g'.isAssigned do walk g' fuel

partial def commitApply (g : MVarId) (e : Expr) (fuel : Nat) : MetaM Bool := do
  let s ← saveState
  let key := "apply:" ++ (if e.isConst then (toString e.constName!).replace "Tools.ShippingChildWalkA." "" else "hyp")
  let gs ← try timed key (applyExactA g e) catch _ => s.restore; return false
  for g' in gs do
    unless ← g'.isAssigned do walk g' fuel
  return true

partial def walk (g : MVarId) (fuel : Nat) : MetaM Unit := do
  if fuel == 0 then throwError "vca: out of fuel"
  vcStats.modify fun m => let (c, ms) := m.getD "walk" (0, 0); m.insert "walk" (c + 1, ms)
  let budget := vc.budgetMs.get (← getOptions)
  if budget != 0 && (← IO.monoMsNow) - (← vcStart.get) > budget then
    throw (Exception.error (← getRef) (MessageData.tagged `vcFinal
      m!"vca: over its {budget} ms budget — {← statsLine}"))
  let (_, g) ← g.intros
  let depth := (← vcStack.get).size
  try
    try walkCore g (fuel - 1)
    finally vcStack.modify (·.shrink depth)
  catch e =>
    let isProg := (keepsProgA? (← instantiateMVars (← g.getType)).cleanupAnnotations).isSome
    vcNote fun _ => return s!"  failed: {((← e.toMessageData.toString).take 300)}"
    if e.toMessageData.hasTag (· == `vcFinal) then throw e
    let headName := match keepsProgA? (← instantiateMVars (← g.getType)).cleanupAnnotations with
      | some (_, q) => toString q.getAppFn.constName?
      | none => "side"
    let closed ← if isProg then timed s!"absurd@{headName}" (attempt (absurdBranch g)) else pure false
    unless closed do
      throw (Exception.error e.getRef (MessageData.tagged `vcFinal e.toMessageData))

partial def walkCore (g : MVarId) (fuel : Nat) : MetaM Unit := do
  g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let some (isC, p) := keepsProgA? t | side g
  let pm0 := p.consumeMData
  if vc.stats.get (← getOptions) || vc.budgetMs.get (← getOptions) != 0 then
    let h := p.getAppFn
    let fvName ← if h.isFVar then h.fvarId!.getUserName else pure .anonymous
    let k := "@" ++ (if h.isConst then toString h.constName! else if h.isFVar then
      toString fvName else if pm0.isLet then "let:" ++ toString pm0.letName! else "other")
    vcStats.modify fun m => let (c, ms) := m.getD k (0, 0); m.insert k (c + 1, ms)
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
    IO.eprintln s!"vca {if isC then "C" else "M"} {if h.isConst then toString h.constName! else if h.isFVar then "fvar" else if h.isProj then "proj" else if p.isLet then "let" else if p.isLambda then "lam" else "other"} args={p.getAppNumArgs}"
    unless h.isConst || h.isFVar || h.isProj do IO.eprintln s!"   :: {((← ppExpr p).pretty.take 400)}"
  if let some f ← IO.getEnv "VC_TRACE_FILE" then
    let h := p.getAppFn
    let ms := (← IO.monoMsNow) - (← vcStart.get)
    IO.FS.withFile f .append fun hd => hd.putStrLn
      s!"{ms} {if isC then "C" else "M"} {h.constName?.getD (if h.isFVar then `fvar else `other)} args={p.getAppNumArgs} size={p.approxDepth}"
  let pm := p.consumeMData
  -- a join point (`have jp := fun r => …; …`, used at several exits of a `do` block): walked
  -- ONCE, as a local fact about `jp`
  if pm.isLet then
    let (jn, jT, jv, jb) := (pm.letName!, pm.letType!, pm.letValue!, pm.letBody!)
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
      return (resTy r).map fun (c, a) => (c, a.abstract xs)
    if let some (jC, _) := (if vc.shareJoinPoints.get (← getOptions) then kind? else none) then
      let keepsFn := t.appFn!
      let ka := keepsFn.getAppArgs
      -- the admissibility hypothesis of this context, if any (for the fact about EVERY
      -- admissible context)
      let adm? : Option Expr ← do
        let mut r := none
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let ty ← instantiateMVars d.type
          if ty.isAppOf ``AdmCtx && ty.getAppNumArgs == 3 then
            if (← isDefEq (ty.getArg! 1) ka[0]!) && (← isDefEq (ty.getArg! 2) ka[2]!) then
              r := some (ty.getArg! 0)
              break
        pure r
      let mkK (xsApp : Expr) (α' mc cc : Expr) : Expr := mkAppN (mkConst (if jC then ``KeepsCP else ``Keeps))
        #[mc, ka[1]!, cc, ka[3]!, α', ka[5]!, xsApp]
      if pm.letNondep! then
        let facts (anyCtx : Bool) : MetaM (Expr × Expr) :=
          forallTelescope jT fun xs r => do
            let some (_, α') := resTy r | throwError "vca: join point type"
            let close (f : Expr) : MetaM Expr :=
              if anyCtx then
                match adm? with
                | some q =>
                  withLocalDeclD `mctx' (mkConst ``Lean.Meta.Context) fun mc =>
                    withLocalDeclD `cctx' (mkConst ``Lean.Core.Context) fun cc => do
                      withLocalDeclD `hA' (mkApp3 (mkConst ``AdmCtx) q mc cc) fun hA' =>
                        mkForallFVars (#[mc, cc, hA'] ++ xs) (mkK (mkAppN f xs).headBeta α' mc cc)
                | none => throwError "vca: no admissibility hypothesis"
              else mkForallFVars xs (mkK (mkAppN f xs).headBeta α' ka[0]! ka[2]!)
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
      let stmt (anyCtx : Bool) : MetaM Expr := g2.withContext do
        forallTelescope jT fun xs r => do
          let some (_, α') := resTy r | throwError "vca: join point type"
          if anyCtx then
            match adm? with
            | some q =>
              withLocalDeclD `mctx' (mkConst ``Lean.Meta.Context) fun mc =>
                withLocalDeclD `cctx' (mkConst ``Lean.Core.Context) fun cc =>
                  withLocalDeclD `hA' (mkApp3 (mkConst ``AdmCtx) q mc cc) fun hA' => do
                    mkForallFVars (#[mc, cc, hA'] ++ xs) (mkK (mkAppN (mkFVar jp) xs) α' mc cc)
            | none => throwError "vca: no admissibility hypothesis"
          else mkForallFVars xs (mkK (mkAppN (mkFVar jp) xs) α' ka[0]! ka[2]!)
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
  let rule2 (kn cn kE cE : Name) : MetaM Unit := do
    if ← commitApply g (← mkConstWithFreshMVarLevels (if isC then cn else kn)) fuel then return
    applyThen g (← mkConstWithFreshMVarLevels (if isC then cE else kE)) fuel
  if let .const rn _ := fn then
    if isCasesOnRecursor (← getEnv) rn || (← isRec rn) then
      let p' ← whnfCore p
      if p' != p then
        let g ← g.replaceTargetDefEq (mkApp t.appFn! p')
        return ← walk g fuel
      if let some major := p.getAppArgs.findRev? (·.isFVar) then
        let subgoals ← timed "cases" (g.cases major.fvarId!)
        for sg in subgoals do walk sg.mvarId fuel
        return
  if let some app ← matchMatcherApp? p then
    let ds := app.discrs.filter (!·.isFVar)
    if !ds.isEmpty then
      let gargs : Array GeneralizeArg := ds.mapIdx fun i d =>
        { expr := d, xName? := some (Name.mkSimple s!"x{i}"), hName? := some (Name.mkSimple s!"hx{i}") }
      if let some (_, g') ← timed "generalize" (try some <$> g.generalize gargs catch _ => pure none) then
        return ← walk g' fuel
  if let some _ ← matchMatcherApp? p then
    let gs ← timed "split" (Lean.Meta.Split.splitMatch g p)
    for g' in gs do walk g' fuel
    return
  -- a `CompilerM` action given as a function of its states
  if isC && p.isLambda then
    if ← commitApply g
        (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.KeepsCP.tryCatch) fuel then return
    return ← applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.KeepsCP.intro) fuel
  if !isC && p.isLambda then
    if ← commitApply g
        (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.tryCatch) fuel then return
  -- a hypothesis about this program (the recursive translator, a continuation, a handler)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let fits ← forallTelescope ty fun _ body => pure <|
      match keepsProgA? body with
      | some (c, q) => c == isC && q.getAppFn == fn
      | none => false
    if fits then
      vcNote fun _ => return s!"  hyp {← d.fvarId.getUserName} fits"
      if ← commitApply g d.toExpr fuel then return
      vcNote fun _ => return s!"  hyp {← d.fvarId.getUserName} not applied"
  let isTryCatchProj := match fn with
    | .proj sn i _ => (sn == ``MonadExcept || sn == ``MonadExceptOf) && i == 1
    | _ => false
  if isTryCatchProj || fn.isConstOf ``MonadExcept.tryCatch ||
      fn.isConstOf ``tryCatchThe || fn.isConstOf ``MonadExceptOf.tryCatch then
    if ← timed "tryCatch?" (attempt (rule ``Tools.ShippingChildInv.Keeps.tryCatch ``Tools.ShippingChildWalkA.KeepsCP.tryCatch)) then
      return
  if fn.isProj then
    let inst ← timed "projInst" (withTransparency .instances (whnf fn.projExpr!))
    let p' ← whnfCore (mkAppN (fn.updateProj! inst) p.getAppArgs)
    if p' != p then
      let g ← g.replaceTargetDefEq (mkApp t.appFn! p')
      return ← walk g fuel
  -- a `CompilerM` action applied to its two states (inside a `MetaM` continuation)
  if !isC && p.getAppNumArgs ≥ 2 then
    let c' := p.appFn!.appFn!
    let ct ← inferType c'
    let isCM := ct.isAppOf ``CompilerM ||
      (ct.isAppOf ``ReaderT && (ct.getAppArgs[0]?.map (·.isConstOf ``CompilerState)).getD false)
    if isCM then
      if ← commitApply g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.KeepsCP.apply) fuel then return
  if fn.isFVar then
    if let some v ← fn.fvarId!.getValue? then
      vcNote fun _ => return s!"  local value of {← fn.fvarId!.getUserName}"
      let g ← g.replaceTargetDefEq (mkApp t.appFn! (p.replace fun e => if e == fn then some v else none).headBeta)
      return ← walk g fuel
  match fn with
  | .const c _ =>
    if (toString c).startsWith "_private.Lean." then
      throwError "vca: reached the Lean internal {c} (last unfolded: {← vcLastUnfold.get}); the public primitive needs a law"
    if c == ``Bind.bind then
      -- a read of the compiler context: its provenance goes to the continuation
      if isC then
        if let some x := p.getAppArgs[4]? then
          -- a program returning a caught exception with its result: the fact that it is in
          -- the class goes to the continuation (committed)
          if x.isAppOf ``Sparkle.Compiler.Elab.Rec.tryInlineUnfold then
            return ← applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.KeepsCP.bindCaught) fuel
          if readHeads.contains (x.getAppFn.constName?.getD .anonymous) then
            if ← commitApply g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.KeepsCP.bindRead) fuel then return
          if x.getAppFn.isConstOf ``CompilerM.getCompilerState then
            if ← commitApply g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildTranslateA.KeepsCP.bindCtx) fuel then return
      return ← rule2 ``Keeps.bind ``Tools.ShippingChildTranslateA.KeepsCP.bind ``Tools.ShippingChildInv.Keeps.bindE
        ``Tools.ShippingChildWalkA.KeepsCP.bindE
    if c == ``Functor.map then return ← rule ``Keeps.map ``Tools.ShippingChildWalkA.KeepsCP.map
    if c == ``ite && p.getAppNumArgs == 5 then
      let cond := p.getArg! 1
      let lit? : Option Bool := match cond.eq? with
        | some (_, l, r) =>
          if (l.isConstOf ``Bool.true || l.isConstOf ``Bool.false) &&
              (r.isConstOf ``Bool.true || r.isConstOf ``Bool.false) then
            some (l.constName! == r.constName!)
          else none
        | none => none
      if let some d := lit? then
        let br := if d then p.getArg! 3 else p.getArg! 4
        let g ← g.replaceTargetDefEq (mkApp t.appFn! br)
        return ← walk g fuel
    if c == ``ForIn.forIn || c == ``forIn then
      let ρ := (p.getAppArgs[1]?.getD default).getAppFn
      let pick : Option (Name × Name) :=
        if ρ.isConstOf ``List then
          some (``Tools.ShippingChildInv.Keeps.forIn_list, ``Tools.ShippingChildWalkA.KeepsCP.forIn_list)
        else if ρ.isConstOf ``Array then
          some (``Tools.ShippingChildInv.Keeps.forIn_array, ``Tools.ShippingChildWalkA.KeepsCP.forIn_array)
        else if ρ.isConstOf ``Std.Legacy.Range then
          some (``Tools.ShippingChildInv.Keeps.forIn_range, ``Tools.ShippingChildWalkA.KeepsCP.forIn_range)
        else none
      if let some (kn, cn) := pick then
        if ← commitApply g (← mkConstWithFreshMVarLevels (if isC then cn else kn)) fuel then return
    if c == ``Pure.pure then
      return ← rule2 ``Keeps.pure ``Tools.ShippingChildTranslateA.KeepsCP.pure ``Tools.ShippingChildInv.Keeps.pureE
        ``Tools.ShippingChildWalkA.KeepsCP.pureE
    if c == ``ite then return ← rule ``Keeps.ite ``Tools.ShippingChildTranslateA.KeepsCP.ite
    if c == ``dite then return ← rule ``Keeps.dite ``Tools.ShippingChildTranslateA.KeepsCP.dite
    if c == ``throwThe || c == ``MonadExceptOf.throw then
      if ← commitApply g (← mkConstWithFreshMVarLevels
          (if isC then ``Tools.ShippingChildWalkA.KeepsCP.throwE else ``Tools.ShippingChildInv.Keeps.throwE)) fuel then
        return
    if c == ``MonadExcept.throw || c == ``throw then
      return ← rule2 ``Keeps.throw ``Tools.ShippingChildTranslateA.KeepsCP.throw ``Tools.ShippingChildInv.Keeps.throwE
        ``Tools.ShippingChildWalkA.KeepsCP.throwE
    -- registered theorems
    for lem in (keepsAExt.getState (← getEnv)).getD c #[] do
      if ← commitApply g (← mkConstWithFreshMVarLevels lem) fuel then return
    if isC && c == ``CompilerM.liftMetaM then
      return ← applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildTranslateA.KeepsCP.lift) fuel
    if isC then
      for lem in [``Tools.ShippingChildWalkA.KeepsCP.liftM, ``Tools.ShippingChildWalkA.KeepsCP.liftIO,
          ``Tools.ShippingChildWalkA.KeepsCP.liftBaseIO,
          ``Tools.ShippingChildWalkA.KeepsCP.liftE, ``Tools.ShippingChildWalkA.KeepsCP.refGet,
          ``Tools.ShippingChildWalkA.KeepsCP.refSet, ``Tools.ShippingChildWalkA.KeepsCP.refModify,
          ``Tools.ShippingChildTranslateA.KeepsCP.get, ``Tools.ShippingChildTranslateA.KeepsCP.set,
          ``Tools.ShippingChildTranslateA.KeepsCP.modify,
          ``Tools.ShippingChildWalkA.KeepsCP.read, ``Tools.ShippingChildTranslateA.KeepsCP.getCompilerState,
          ``Tools.ShippingChildTranslateA.KeepsCP.withReader] do
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
            applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.Keeps.withReaderA) fuel) then
          return
      if c == ``liftM || c == ``monadLift || c == ``MonadLiftT.monadLift then
        if ← timed "readOnly" (attempt (readOnly g)) then return
        if (← inferType p).isAppOf ``ExceptT then
          if ← commitApply g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.liftE) fuel then
            return
      if c == ``Lean.throwError then
        if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.keepsA_throwError) fuel) then return
      if c == ``List.mapM then
        if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.mapM) fuel) then return
      if c == ``Lean.Meta.withLetDecl then
        return ← applyThen g
          (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.keepsA_withLetDecl) fuel
      if c == ``Lean.Meta.withLocalDeclD then
        return ← applyThen g
          (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.keepsA_withLocalDeclD) fuel
      if c == ``Lean.Meta.lambdaTelescope then
        return ← applyThen g
          (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.keepsA_lambdaTelescope) fuel
      if c == ``Lean.Meta.forallTelescopeReducing then
        return ← applyThen g
          (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.keepsA_forallTelescopeReducing) fuel
      if p.getAppNumArgs ≥ 2 then
        let c' := p.appFn!.appFn!
        let ct ← inferType c'
        if ct.isAppOf ``CompilerM || ct.isAppOf ``ReaderT then
          if ← commitApply g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildWalkA.KeepsCP.apply) fuel then return
      -- an operation whose frame is a law
      if ← timed "framed" (attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildVCA.keepsA_framed) fuel)) then
        return
      if ← timed "diag" (attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Tools.ShippingChildVCA.keepsA_diag) fuel)) then
        return
    if opaqueHeads.contains c then throwError "vca: no rule for {p}"
    vcLastUnfold.set c
    let g' ← timed "unfold" (try Lean.Meta.unfoldTarget g c catch _ => throwError "vca: cannot unfold {c} in {p}")
    let t' ← instantiateMVars (← g'.getType)
    if t' == t then throwError "vca: {c} is opaque (no rule, no law, no theorem)"
    if let some (_, p') := keepsProgA? t' then
      if (p'.find? (·.isConstOf c)).isSome then
        throwError "vca: {c} is recursive and has no @[keepsA] theorem"
    walk g' fuel
  | _ => throwError "vca: no rule for {p}"

end

end VCA

/-- Walk the goal's program (see the file's header). -/
elab "vca" : tactic => Lean.Elab.Tactic.liftMetaTactic fun g => do
  vcStats.set {}
  vcShapes.set {}
  vcStack.set #[]
  vcFirstPath.set {}
  vcDup.set none
  vcStart.set (← IO.monoMsNow)
  VCA.walk g 2000
  if vc.stats.get (← getOptions) then
    logInfo m!"vca: {(← IO.monoMsNow) - (← vcStart.get)} ms — {← Tools.ShippingChildInv.VC.statsLine}"
  return []

end Tools.ShippingChildWalkA
