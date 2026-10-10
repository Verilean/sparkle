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

theorem Keeps.throw {α : Type} {I : Void IO.RealWorld → Prop} (e : Exception) :
    Keeps mctx mref cctx cref I (throw e : MetaM α) :=
  keeps_iff.mpr (Triple.throw e fun _ hw => hw)

theorem Keeps.throwError {α : Type} (L : RefLaws mref cref) (D : Nat) (msg : MessageData) :
    Keeps mctx mref cctx cref (J L D) (Lean.throwError msg : MetaM α) :=
  keeps_iff.mpr (Triple.throwErr L msg D)

/-- An operation whose frame is a law. -/
theorem Keeps.framed {α : Type} (L : RefLaws mref cref) (D : Nat) {p : MetaM α} (hp : Framed p) :
    Keeps mctx mref cctx cref (J L D) p :=
  keeps_iff.mpr (Triple.frame L hp D)

theorem Keeps.mapM {α β : Type} {I : Void IO.RealWorld → Prop} (f : α → MetaM β)
    (hf : ∀ x, Keeps mctx mref cctx cref I (f x)) (l : List α) :
    Keeps mctx mref cctx cref I (l.mapM f) :=
  keeps_iff.mpr (Triple.mapM f (fun x => keeps_iff.mp (hf x)) l)

/-- `try x catch e => h e`: the handler runs from the world the failing `x`
ended in — or, for an interrupt or a runtime exception, does not run and the
exception goes on from that same world (`Core.tryCatch`). -/
theorem Keeps.tryCatch {α : Type} {I : Void IO.RealWorld → Prop} {x : MetaM α}
    {h : Exception → MetaM α} (hx : Keeps mctx mref cctx cref I x)
    (hh : ∀ e, Keeps mctx mref cctx cref I (h e)) :
    Keeps mctx mref cctx cref I (MonadExcept.tryCatch x h) := by
  intro w hw
  have h1 := hx w hw
  unfold endW at h1 ⊢
  change I (match (Core.tryCatch (x mctx mref) (fun e => h e mctx mref)) cctx cref w with
    | .ok _ w' => w' | .error _ w' => w')
  unfold Core.tryCatch
  change I (match (EST.tryCatch (x mctx mref cctx cref)
      (fun ex => (if (ex.isInterrupt || ex.isRuntime) = true then (MonadExcept.throw ex : CoreM α)
        else h ex mctx mref) cctx cref)) w with
    | .ok _ w' => w' | .error _ w' => w')
  unfold EST.tryCatch
  cases hxw : x mctx mref cctx cref w with
  | ok a w1 => rw [hxw] at h1; exact h1
  | error e w1 =>
    rw [hxw] at h1
    dsimp only
    by_cases hc : (e.isInterrupt || e.isRuntime) = true
    · rw [if_pos hc]; exact h1
    · rw [if_neg hc]
      have := hh e w1 h1
      unfold endW at this
      exact this

/-- An action that returns in the world it started in (a context read). -/
theorem Keeps.of_ok {α : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α}
    (h : ∀ w, ∃ a, m mctx mref cctx cref w = .ok a w) : Keeps mctx mref cctx cref I m := by
  intro w hw
  obtain ⟨a, ha⟩ := h w
  unfold endW; rw [ha]; exact hw

theorem Keeps.map {α β : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α} (f : α → β)
    (h : Keeps mctx mref cctx cref I m) : Keeps mctx mref cctx cref I (f <$> m) :=
  Keeps.bind h fun a => Keeps.pure (f a)

/-- `forallTelescopeReducing`: its continuation, in whatever contexts it runs. -/
theorem Keeps.forallTelescopeReducing {α : Type} (L : RefLaws mref cref) (D : Nat) (ty : Lean.Expr)
    (k : Array Lean.Expr → Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b,
      Keeps mctx' mref cctx' cref (J L D) (k xs b)) :
    Keeps mctx mref cctx cref (J L D) (Lean.Meta.forallTelescopeReducing ty k) :=
  L.telescope (J L D) (fun _ _ h1 h2 h3 hw => J_same L ⟨h1, h2, h3⟩ hw) ty k hk

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

theorem KeepsC.throw {α : Type} {I : Void IO.RealWorld → Prop} (e : Exception) :
    KeepsC mctx mref cctx cref I (throw e : CompilerM α) :=
  keepsC_iff.mpr (TripleC.throw e fun _ hw => hw)

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
    (hh : ∀ e, KeepsC mctx mref cctx cref I (h e)) :
    KeepsC mctx mref cctx cref I (MonadExcept.tryCatch x h) :=
  fun ctx st => Keeps.tryCatch (hx ctx st) fun e => hh e ctx st

theorem KeepsC.map {α β : Type} {I : Void IO.RealWorld → Prop} {c : CompilerM α} (f : α → β)
    (h : KeepsC mctx mref cctx cref I c) : KeepsC mctx mref cctx cref I (f <$> c) :=
  KeepsC.bind h fun a => KeepsC.pure (f a)

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

namespace VC

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
   ``ST.Ref.modify, ``IO.mkRef, ``List.mapM]

/-- Close a side goal: a hypothesis, or constructors (of `Framed`, `SideRef`),
each tried only when its statement's program has the goal's head. -/
partial def side (g : MVarId) (depth : Nat := 4) : MetaM Unit := g.withContext do
  if ← attempt g.assumption then return
  if depth == 0 then throwError "vc: side goal {← g.getType}"
  let t ← whnfR (← instantiateMVars (← g.getType))
  let .const ind _ := t.getAppFn | throwError "vc: side goal {t}"
  let some (.inductInfo ii) := (← getEnv).find? ind | throwError "vc: side goal {t}"
  let goalHead := t.appArg!.getAppFn
  for ctor in ii.ctors do
    -- a constructor about another operation is not tried
    let ok ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels ctor)) fun _ body => do
      let h := body.appArg!.getAppFn
      pure (h.isFVar || h.isMVar || !(h.isConst && goalHead.isConst) || h.constName! == goalHead.constName!)
    unless ok do continue
    if ← attempt (do
        let gs ← g.apply (← mkConstWithFreshMVarLevels ctor)
        for g' in gs do side g' (depth - 1)) then return
  throwError "vc: no law for {t}"

/-- One `let` / `have` / beta step at the head of the program, if any. -/
def simpHead? (p : Expr) : Option Expr :=
  let p' := p.consumeMData
  if p'.isLet then some (p'.letBody!.instantiate1 p'.letValue!)
  else if p'.isHeadBetaTarget then some p'.headBeta
  else if p' != p then some p'
  else none

/-- Close `g` by a tactic, with no error recovery: a failing tactic must fail,
not admit the goal. -/
def closeBy (g : MVarId) (stx : Syntax) : MetaM Unit := do
  let gs ← (Lean.Elab.Term.withoutErrToSorry
    (Lean.Elab.Tactic.run g (Lean.Elab.Tactic.withoutRecover (Lean.Elab.Tactic.evalTactic stx)))).run'
  unless gs.isEmpty do throwError "not closed"

/-- Close a goal whose hypotheses contradict each other (a branch the
surrounding `match` / `if` has already excluded). -/
def absurdBranch (g : MVarId) : MetaM Unit := do
  closeBy g (← `(tactic| first | contradiction | (exfalso; simp_all)))

/-- A context read: the run returns in the world it started in, by computation. -/
def readOnly (g : MVarId) : MetaM Unit := do
  let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.of_ok)
    | throwError "of_ok"
  closeBy g' (← `(tactic| (intro w; exact ⟨_, rfl⟩)))

mutual

/-- Apply `e`, then walk every goal it leaves. -/
partial def applyThen (g : MVarId) (e : Expr) (fuel : Nat) : MetaM Unit := do
  let gs ← g.apply e
  for g' in gs do
    unless ← g'.isAssigned do walk g' fuel

/-- Walk a goal: a `Keeps` / `KeepsC` statement by its program, anything else
as a side goal. -/
partial def walk (g : MVarId) (fuel : Nat) : MetaM Unit := do
  if fuel == 0 then throwError "vc: out of fuel"
  let (_, g) ← g.intros
  try walkCore g (fuel - 1)
  catch e =>
    -- a branch that cannot happen
    unless ← attempt (absurdBranch g) do throw e

partial def walkCore (g : MVarId) (fuel : Nat) : MetaM Unit := do
  g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let some (isC, p) := keepsProg? t | side g
  -- `let`, `have`, beta
  if let some p' := simpHead? p then
    let g ← g.replaceTargetDefEq (mkApp t.appFn! p')
    return ← walk g fuel
  let fn := p.getAppFn
  let rule (kn cn : Name) : MetaM Unit := do
    applyThen g (← mkConstWithFreshMVarLevels (if isC then cn else kn)) fuel
  -- a `match`
  if (← matchMatcherApp? p).isSome then
    let some gs ← Lean.Meta.splitTarget? g | throwError "vc: cannot split {p}"
    for g' in gs do walk g' fuel
    return
  -- a `CompilerM` action given as a function of its states
  if isC && p.isLambda then
    return ← applyThen g (← mkConstWithFreshMVarLevels ``KeepsC.intro) fuel
  -- a hypothesis about this program (the recursive translator, a continuation, the child entry)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let fits ← forallTelescope ty fun _ body => pure <|
      match keepsProg? body with
      | some (c, q) => c == isC && (q.getAppFn == fn || q.getAppFn.isFVar && fn.isFVar)
      | none => false
    if fits then
      if ← attempt (applyThen g d.toExpr fuel) then return
  -- `try … catch` (the instance's `tryCatch` field, applied)
  if fn.isProj || fn.isConstOf ``MonadExcept.tryCatch || fn.isConstOf ``MonadExcept.tryCatch ||
      fn.isConstOf ``tryCatchThe || fn.isConstOf ``MonadExceptOf.tryCatch then
    if ← attempt (rule ``Tools.ShippingChildInv.Keeps.tryCatch ``Tools.ShippingChildInv.KeepsC.tryCatch) then return
  -- a field of an instance, applied (e.g. the `default` of a monadic type): reduce it
  if fn.isProj then
    let inst ← withTransparency .instances (whnf fn.projExpr!)
    let p' ← whnfCore (mkAppN (fn.updateProj! inst) p.getAppArgs)
    if p' != p then
      let g ← g.replaceTargetDefEq (mkApp t.appFn! p')
      return ← walk g fuel
  match fn with
  | .const c _ =>
    if c == ``Bind.bind then return ← rule ``Keeps.bind ``KeepsC.bind
    if c == ``Functor.map then return ← rule ``Keeps.map ``KeepsC.map
    if c == ``Pure.pure then return ← rule ``Keeps.pure ``KeepsC.pure
    if c == ``ite then return ← rule ``Keeps.ite ``KeepsC.ite
    if c == ``dite then return ← rule ``Keeps.dite ``KeepsC.dite
    if c == ``MonadExcept.throw || c == ``throw then return ← rule ``Keeps.throw ``KeepsC.throw
    -- registered theorems
    for lem in (keepsExt.getState (← getEnv)).getD c #[] do
      if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels lem) fuel) then return
    if isC && c == ``CompilerM.liftMetaM then
      return ← applyThen g (← mkConstWithFreshMVarLevels ``KeepsC.lift) fuel
    if isC then
      for lem in [``KeepsC.liftM, ``KeepsC.get, ``KeepsC.set, ``KeepsC.modify,
          ``KeepsC.read, ``KeepsC.getCompilerState, ``KeepsC.withReader] do
        let ok ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels lem)) fun _ body =>
          pure (body.appArg!.getAppFn.constName? == some c)
        if ok then
          if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels lem) fuel) then return
    else
      if [``read, ``readThe, ``MonadReader.read, ``MonadReaderOf.read, ``Lean.getLCtx,
          ``Lean.MonadLCtx.getLCtx, ``Lean.getRef, ``Lean.MonadRef.getRef, ``Lean.getOptions,
          ``Lean.MonadOptions.getOptions].contains c then
        if ← attempt (readOnly g) then return
      if c == ``Lean.throwError then
        if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Keeps.throwError) fuel) then return
      if c == ``List.mapM then
        if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Keeps.mapM) fuel) then return
      if c == ``Lean.Meta.forallTelescopeReducing then
        return ← applyThen g
          (← mkConstWithFreshMVarLevels ``Tools.ShippingChildInv.Keeps.forallTelescopeReducing) fuel
      -- an operation whose frame is a law
      if ← attempt (do applyThen g (← mkConstWithFreshMVarLevels ``Keeps.framed) fuel) then return
      -- a `CompilerM` action applied to its states
      if p.getAppNumArgs ≥ 2 then
        let c' := p.appFn!.appFn!
        if (← whnfR (← inferType c')).isAppOf ``ReaderT || (← inferType c').isAppOf ``CompilerM then
          if ← attempt (do
              applyThen g (← mkAppM ``KeepsC.apply #[← mkFreshExprMVar none]) fuel) then return
    if opaqueHeads.contains c then throwError "vc: no rule for {p}"
    -- any other definition: unfold it, unless it is recursive
    let g' ← try Lean.Meta.unfoldTarget g c catch _ => throwError "vc: cannot unfold {c} in {p}"
    let t' ← instantiateMVars (← g'.getType)
    if t' == t then throwError "vc: {c} is opaque (no rule, no law, no theorem)"
    if let some (_, p') := keepsProg? t' then
      if (p'.find? (·.isConstOf c)).isSome then
        throwError "vc: {c} is recursive and has no @[keeps] theorem"
    walk g' fuel
  | _ => throwError "vc: no rule for {p}"

end

end VC

/-- Walk the goal's program (see the file's header). -/
elab "vc" : tactic => Lean.Elab.Tactic.liftMetaTactic fun g => do
  VC.walk g 2000
  return []

end Tools.ShippingChildInv
