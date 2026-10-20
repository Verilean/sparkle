import Tools.ShippingChildPathA
-- NOT BUILT (worker par/tr, base 6a231b89). Isolated: only Tools/ShippingChildFallbackA.lean and
-- Tools/ShippingChildTranslatePathA.lean use it.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only (no `RefLaws`, no
-- `RefLawsCore`, no `RefLawsCore.toAOps`/`toA`, no `J L D`/`JE L D`, no `Triple.frame L`/`diag L`).
-- Reused law-free lemmas (statements checked: no law bundle): `Keeps`, `KeepsC`, `keeps_iff`,
-- `keepsC_iff`, `Triple.bind`/`pure`, `TripleC.*` (Harness, stated before its law variable),
-- `KeepsC.pure`/`throw`/`lift`/`get`/`set`/`modify`/`getCompilerState` (VC, generic in `I`),
-- `Keeps.pure`/`bind`, the `okmsg` tactic; from PathA/VertA/VCA: `makeWireA`, `addInputA`,
-- `addOutputA`, `emitAssignA`, `wireWidthA`, `keepsA_framed`, `StableA`.
-- NOT reused: `fuelFix_keepsC` (ShippingChildTranslate.lean). It is law-free, but its premise and
-- conclusion quantify EVERY Meta/Core context and EVERY compiler context; the new laws hold only at
-- admissible contexts (`AdmCtx`) and the cache laws only for refs with provenance. `fuelFix_of`
-- below is the same fuel induction, generic in the predicate (law-free, three lines).
-- Writing-time guesses (marked `-- guess: Tn` below):
--  T1 `KeepsCP.bind`/`bindCtx`: the `(c >>= f) ctx st` vs `c ctx st >>= …` unification is the one
--     `TripleC.bind`/`TripleC.getCompilerState` (Harness, built) rely on;
--  T2 `ctxOk_entry`: `have h' : some r = some r' := h` by defeq (projection of a structure
--     literal), `cases h'` substitutes;
--  T3 `instantiateMVars` beta-reduces the continuation goals of `refine … (fun x => ?_)`, so
--     `cases hc : cs.exprCache` finds the discriminant (fallback `try dsimp only` before it);
--  T4 the hit read in `cacheLookupValidated` elaborates as `liftM (ST.Ref.get r : IO _) >>= …`
--     (`FramedA.exprCacheGetIO`); fallback `FramedA.exprCacheGet`;
--  T5 `recordTranslation`: `if cacheable then (getCompilerState >>= fun s => match s.exprCache …)`
--     with an implicit `else pure ()`;
--  T6 `translateCanonicalSignalBinaryA`: `rw [hw]` rewrites the width discriminant (fallback
--     `simp only [hw]`); the operand `if true = true` is closed by `KeepsCP.ite` with the dead
--     branch refuted, or is already reduced (fallback: the recursive call directly);
--  T7 `translateCoreA`: `split` on the three-discriminant match leaves the equation
--     `canonicalSignalBitVecWidth e.getAppArgs = some n` in context (`by assumption`);
--  T8 `translateStepWithA`: after `unfold` + `dsimp only` (zeta of `cacheable` and of the join
--     point) the program is `if … then (cacheLookupValidated e >>= fun r => match r …) else REST`;
--     the `kbase` driver walks REST (bind/ite/split/pure), whichever form `unless` takes;
--  T9 `fuelFix_of`: `translateFuelFix step (k+1)` is defeq to `step (translateFuelFix step k)`
--     (fallback `unfold translateFuelFix`, as `fuelFix_keepsC` did);
--  T10 `lookupVarP`/`bindSourceVariableP`: after `unfold`, `Keeps.pure _` closes the applied
--     lambda by beta;
--  T11 the copies of `makeWireA` (`emitRegisterA`, `emitMemoryA`, …) follow the built proof
--     (`get`, `split` on the `let (name, cs') := …` match, `set`, `dsimp only`, `split` on
--     `legacyCacheWidth? ty`).

/-! # The translator's own code under the admissible boundary

## The restricted compiler-context triple (design point)

The translation cache ref the translator's cache code uses is NOT bound by the
code: it comes from the compiler context (`ctx.exprCache = some r`), and
`FramedA.exprCacheGet/Modify r hr` needs `hr : MkRefd _ r`. `KeepsC`
quantifies EVERY compiler context — including ones carrying an arbitrary ref,
for which no law applies. So here:

* `CtxOk ctx` — every cache ref the context carries has provenance
  (`∀ r, ctx.exprCache = some r → MkRefd _ r`; a context with no cache is OK);
* `KeepsCP … I c` — `c` keeps `I` from every circuit state and every
  compiler context WITH `CtxOk` (not `True`: a context's ref must have been
  returned by an `IO.mkRef` run).

Established: `ctxOk_entry` (the entry's context `entryCompilerState b r` with
`MkRefd r`), preserved by `withVarMapping` (`withVarMappingP`) and by any
`withReader` whose update keeps `exprCache` (`KeepsCP.withReader`), and
`KeepsCP.bindCtx` hands the provenance of a read context
(`getCompilerState`) to its continuation. Every `KeepsC` fact is a `KeepsCP`
fact (`KeepsCP.of`).

## Proved here, for any STABLE invariant `I` (`StableA O.quiet I`)

* the circuit-state primitives (`makeWireP`, …, `emitRegisterA`,
  `emitMemoryA`, `freshNameA`, `emitInstanceA`, `addModuleToDesignA`,
  `lookupVarP`, `bindSourceVariableP`);
* `cacheLookupValidatedA` (read of the context's cache: `FramedA.exprCacheGetIO r
  hr`, `hr` from `CtxOk`), `recordTranslationA` (`FramedA.exprCacheModify r _ hr`);
* `translateCoreA` (a bound variable, a `Signal.pure` literal, a canonical
  library operator with its two recursive operand translations) given the
  recursive argument;
* `translateStepWithA`: one step, given the recursive argument and the
  fallback;
* `fuelFix_of` (law-free) and `translateA_of_fallback`: the translator keeps
  `I` in every admissible context and every `CtxOk` compiler context, given that
  the fallback does whenever its recursive argument does (`RecA`).

The fallback itself is decomposed in Tools/ShippingChildFallbackA.lean. -/

namespace Tools.ShippingChildTranslateA
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The restricted triple -/

/-- Every translation-cache ref the compiler context carries has provenance. -/
def CtxOk (ctx : CompilerState) : Prop :=
  ∀ r, ctx.exprCache = some r → MkRefd (Lean.ExprStructMap String) r

/-- `KeepsC` restricted to compiler contexts with `CtxOk`. -/
def KeepsCP (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) {α : Type} (I : Void IO.RealWorld → Prop)
    (c : CompilerM α) : Prop :=
  ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (c ctx st)

theorem ctxOk_entry (b : Bool) {r : IO.Ref (Lean.ExprStructMap String)}
    (hr : MkRefd (Lean.ExprStructMap String) r) : CtxOk (entryCompilerState b r) := by
  intro r' h
  have h' : some r = some r' := h  -- guess: T2
  cases h'
  exact hr

theorem ctxOk_none (ctx : CompilerState) (h : ctx.exprCache = none) : CtxOk ctx := by
  intro r hr
  rw [h] at hr
  cases hr

section Calculus
variable {I : Void IO.RealWorld → Prop}

theorem KeepsCP.of {α : Type} {c : CompilerM α} (h : KeepsC mctx mref cctx cref I c) :
    KeepsCP mctx mref cctx cref I c :=
  fun ctx st _ => h ctx st

theorem KeepsCP.ofT {α : Type} {c : CompilerM α}
    (h : TripleC mctx mref cctx cref I c (fun _ => I) (fun e w => I w ∧ OkExc e)) :
    KeepsCP mctx mref cctx cref I c :=
  KeepsCP.of (keepsC_iff.mpr h)

theorem KeepsCP.pure {α : Type} (a : α) :
    KeepsCP mctx mref cctx cref I (Pure.pure a : CompilerM α) :=
  KeepsCP.of (KeepsC.pure a)

theorem KeepsCP.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    (h1 : KeepsCP mctx mref cctx cref I c) (h2 : ∀ a, KeepsCP mctx mref cctx cref I (f a)) :
    KeepsCP mctx mref cctx cref I (c >>= f) :=
  fun ctx st hc => keeps_iff.mpr (Triple.bind (keeps_iff.mp (h1 ctx st hc)) fun p => by  -- guess: T1
    obtain ⟨a, s⟩ := p
    exact keeps_iff.mp (h2 a ctx s hc))

theorem KeepsCP.ite {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    (ha : c → KeepsCP mctx mref cctx cref I a) (hb : ¬c → KeepsCP mctx mref cctx cref I b) :
    KeepsCP mctx mref cctx cref I (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

theorem KeepsCP.dite {α : Type} {c : Prop} [Decidable c] {a : c → CompilerM α}
    {b : ¬c → CompilerM α} (ha : ∀ h, KeepsCP mctx mref cctx cref I (a h))
    (hb : ∀ h, KeepsCP mctx mref cctx cref I (b h)) :
    KeepsCP mctx mref cctx cref I (if h : c then a h else b h) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact ha hc
  · rw [dif_neg hc]; exact hb hc

theorem KeepsCP.throw {α : Type} (e : Exception) (he : OkExc e) :
    KeepsCP mctx mref cctx cref I (throw e : CompilerM α) :=
  KeepsCP.of (KeepsC.throw e he)

/-- `throw e >>= k`: the continuation never runs. -/
theorem KeepsCP.throwBind {α β : Type} (e : Exception) (he : OkExc e) (k : α → CompilerM β) :
    KeepsCP mctx mref cctx cref I ((throw e : CompilerM α) >>= k) := by
  refine KeepsCP.ofT (TripleC.bind (Q := fun _ _ => False)
    (TripleC.throw e fun _ hw => ⟨hw, he⟩) ?_)
  intro _ _ _ w hf
  exact hf.elim

theorem KeepsCP.lift {α : Type} {m : MetaM α} (h : Keeps mctx mref cctx cref I m) :
    KeepsCP mctx mref cctx cref I (CompilerM.liftMetaM m) :=
  KeepsCP.of (KeepsC.lift h)

theorem KeepsCP.get : KeepsCP mctx mref cctx cref I (get : CompilerM Sparkle.IR.Builder.CircuitState) :=
  KeepsCP.of KeepsC.get

theorem KeepsCP.set (s : Sparkle.IR.Builder.CircuitState) :
    KeepsCP mctx mref cctx cref I (set s : CompilerM PUnit) :=
  KeepsCP.of (KeepsC.set s)

theorem KeepsCP.modify (f : Sparkle.IR.Builder.CircuitState → Sparkle.IR.Builder.CircuitState) :
    KeepsCP mctx mref cctx cref I (modify f : CompilerM PUnit) :=
  KeepsCP.of (KeepsC.modify f)

theorem KeepsCP.getCompilerState :
    KeepsCP mctx mref cctx cref I CompilerM.getCompilerState :=
  KeepsCP.of KeepsC.getCompilerState

/-- A context change that keeps provenance. -/
theorem KeepsCP.withReader {α : Type} {k : CompilerM α} (f : CompilerState → CompilerState)
    (hf : ∀ ctx, CtxOk ctx → CtxOk (f ctx)) (h : KeepsCP mctx mref cctx cref I k) :
    KeepsCP mctx mref cctx cref I (withReader f k) :=
  fun ctx st hc => h (f ctx) st (hf ctx hc)

/-- **The read context has provenance**: its continuation is asked only for
contexts with `CtxOk`. -/
theorem KeepsCP.bindCtx {β : Type} {f : CompilerState → CompilerM β}
    (h : ∀ cs, CtxOk cs → KeepsCP mctx mref cctx cref I (f cs)) :
    KeepsCP mctx mref cctx cref I (CompilerM.getCompilerState >>= f) :=
  fun ctx st hc => keeps_iff.mpr (Triple.bind (Q := fun p w => I w ∧ CtxOk p.1)  -- guess: T1
    (Triple.pure (a := (ctx, st)) fun _ hw => ⟨hw, hc⟩) fun p => by
      obtain ⟨a, s⟩ := p
      intro w hw
      exact keeps_iff.mp (h a hw.2 ctx s hc) w hw.1)

end Calculus

/-- `withVarMapping` keeps provenance (the update leaves `exprCache`). -/
theorem withVarMappingP {I : Void IO.RealWorld → Prop} {α : Type} (fv : FVarId) (wn : String)
    {k : CompilerM α} (hk : KeepsCP mctx mref cctx cref I k) :
    KeepsCP mctx mref cctx cref I (CompilerM.withVarMapping fv wn k) := by
  unfold CompilerM.withVarMapping
  refine KeepsCP.bindCtx (fun old hold => ?_)
  refine KeepsCP.withReader _ ?_ hk
  intro _ _ r h
  exact hold r h

/-- The generic walker step: `pure`, the circuit state, `throw` (of a message
in the class), `if`, the context read, a bind, a `match`. -/
macro "kbase" : tactic => `(tactic| first
  | exact Tools.ShippingChildTranslateA.KeepsCP.pure _
  | exact Tools.ShippingChildTranslateA.KeepsCP.get
  | exact Tools.ShippingChildTranslateA.KeepsCP.set _
  | exact Tools.ShippingChildTranslateA.KeepsCP.modify _
  | exact Tools.ShippingChildTranslateA.KeepsCP.throw _ (by okmsg)
  | exact Tools.ShippingChildTranslateA.KeepsCP.throwBind _ (by okmsg) _
  | refine Tools.ShippingChildTranslateA.KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
  | refine Tools.ShippingChildTranslateA.KeepsCP.dite (fun _ => ?_) (fun _ => ?_)
  | refine Tools.ShippingChildTranslateA.KeepsCP.bindCtx (fun _ _ => ?_)
  | refine Tools.ShippingChildTranslateA.KeepsCP.bind ?_ (fun _ => ?_)
  | split)

/-! ## The circuit-state primitives -/

section Prims
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

theorem makeWireP (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    KeepsCP mctx mref cctx cref I (CompilerM.makeWire hint ty named) :=
  KeepsCP.ofT (makeWireA O hA hS hint ty named)

theorem addInputP (name : String) (ty : Sparkle.IR.Type.HWType) :
    KeepsCP mctx mref cctx cref I (CompilerM.addInput name ty) :=
  KeepsCP.ofT (addInputA O hA hS name ty)

theorem addOutputP (name : String) (ty : Sparkle.IR.Type.HWType) :
    KeepsCP mctx mref cctx cref I (CompilerM.addOutput name ty) :=
  KeepsCP.ofT (addOutputA O hA hS name ty)

theorem emitAssignP (lhs : String) (rhs : Sparkle.IR.AST.Expr) :
    KeepsCP mctx mref cctx cref I (CompilerM.emitAssign lhs rhs) :=
  KeepsCP.ofT (emitAssignA lhs rhs)

theorem emitRegisterA (hint clk rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Nat)
    (ty : Sparkle.IR.Type.HWType) (named : Bool) (rk : Sparkle.IR.Type.ResetKind) :
    KeepsCP mctx mref cctx cref I (CompilerM.emitRegister hint clk rst input initVal ty named rk) := by
  refine KeepsCP.ofT ?_
  unfold CompilerM.emitRegister  -- guess: T11
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  dsimp only
  split
  · refine TripleC.bind (wireWidthA O hA hS _) ?_
    intro _
    exact TripleC.pure fun _ hw => hw
  · exact TripleC.pure fun _ hw => hw

theorem emitMemoryA (hint : String) (aw dw : Nat) (clk : String)
    (wa wd we ra : Sparkle.IR.AST.Expr) (named : Bool) :
    KeepsCP mctx mref cctx cref I (CompilerM.emitMemory hint aw dw clk wa wd we ra named) := by
  refine KeepsCP.ofT ?_
  unfold CompilerM.emitMemory  -- guess: T11
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  refine TripleC.bind (wireWidthA O hA hS _) ?_
  intro _
  exact TripleC.pure fun _ hw => hw

end Prims

section LawFree
variable {I : Void IO.RealWorld → Prop}

theorem emitRegisterStmtA (out clk rst : String) (input : Sparkle.IR.AST.Expr) (initVal : Nat)
    (rk : Sparkle.IR.Type.ResetKind) :
    KeepsCP mctx mref cctx cref I (CompilerM.emitRegisterStmt out clk rst input initVal rk) := by
  refine KeepsCP.ofT ?_
  unfold CompilerM.emitRegisterStmt
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  exact TripleC.set _

theorem emitInstanceA (mn instName : String) (conns : List (String × Sparkle.IR.AST.Expr)) :
    KeepsCP mctx mref cctx cref I (CompilerM.emitInstance mn instName conns) := by
  refine KeepsCP.ofT ?_
  unfold CompilerM.emitInstance
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  exact TripleC.set _

theorem addModuleToDesignA (m : Sparkle.IR.AST.Module) :
    KeepsCP mctx mref cctx cref I (CompilerM.addModuleToDesign m) := by
  refine KeepsCP.ofT ?_
  unfold CompilerM.addModuleToDesign
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  exact TripleC.set _

theorem freshNameA (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (CompilerM.freshName hint named) := by
  refine KeepsCP.ofT ?_
  unfold CompilerM.freshName
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  exact TripleC.pure fun _ hw => hw

theorem lookupVarP (id : FVarId) :
    KeepsCP mctx mref cctx cref I (CompilerM.lookupVar id) := by
  intro ctx st _
  unfold CompilerM.lookupVar  -- guess: T10
  exact Keeps.pure _

theorem bindSourceVariableP (id : FVarId) (w : String) :
    KeepsCP mctx mref cctx cref I (CompilerM.bindSourceVariable id w) := by
  intro ctx st _
  unfold CompilerM.bindSourceVariable  -- guess: T10
  exact Keeps.pure _

end LawFree

/-! ## The translation cache (the context's ref, with provenance) -/

section Cache
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

/-- **The validated lookup**: the context's cache ref has provenance
(`CtxOk`), so its read is `FramedA.exprCacheGetIO r hr`; the record's read is
pure circuit-state work. -/
theorem cacheLookupValidatedA (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (cacheLookupValidated e) := by
  unfold cacheLookupValidated
  refine KeepsCP.bindCtx (fun cs hcs => ?_)
  try dsimp only  -- guess: T3
  cases hc : cs.exprCache with
  | none => exact KeepsCP.pure _
  | some r =>
    have hr := hcs r hc
    refine KeepsCP.bind (KeepsCP.lift ?_) (fun hit => ?_)
    · first  -- guess: T4
        | exact Keeps.bind (keepsA_framed O hA hS (FramedA.exprCacheGetIO r hr)) fun _ => Keeps.pure _
        | exact Keeps.bind (keepsA_framed O hA hS (FramedA.exprCacheGet r hr)) fun _ => Keeps.pure _
    · cases hit with
      | none => exact KeepsCP.pure _
      | some w =>
        refine KeepsCP.bind KeepsCP.get (fun s => ?_)
        split <;> exact KeepsCP.pure _

/-- **The record**: the circuit-state record, and the cache insert
`FramedA.exprCacheModify r _ hr` with `hr` from `CtxOk`. -/
theorem recordTranslationA (e : Lean.Expr) (w : String) (cacheable : Bool) :
    KeepsCP mctx mref cctx cref I (recordTranslation e w cacheable) := by
  unfold recordTranslation
  refine KeepsCP.bind (KeepsCP.modify _) (fun _ => ?_)
  refine KeepsCP.ite (fun _ => ?_) (fun _ => KeepsCP.pure _)  -- guess: T5
  refine KeepsCP.bindCtx (fun cs hcs => ?_)
  try dsimp only  -- guess: T3
  cases hc : cs.exprCache with
  | none => exact KeepsCP.pure _
  | some r => exact KeepsCP.lift (keepsA_framed O hA hS (FramedA.exprCacheModify r _ (hcs r hc)))

end Cache

/-! ## The core -/

section Core
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

theorem translateSignalPureLiteralA (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSignalPureLiteral? args hint named) := by
  unfold translateSignalPureLiteral?
  split
  · refine KeepsCP.bind (makeWireP O hA hS _ _ _) (fun _ => ?_)
    refine KeepsCP.bind (emitAssignP _ _) (fun _ => ?_)
    exact KeepsCP.pure _
  · exact KeepsCP.pure _

/-- The canonical operator with BOTH operands Signals and a literal width: the
width branch is the literal one (`hw`), the operands are two recursive
translations. -/
theorem translateCanonicalSignalBinaryA (rec : TranslateFn)
    (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
    (e : Lean.Expr) (op : Sparkle.IR.AST.Operator) (args : Array Lean.Expr) (hint : String)
    (named : Bool) (n : Nat) (hw : canonicalSignalBitVecWidth args = some n) :
    KeepsCP mctx mref cctx cref I
      (translateCanonicalSignalBinary rec e op args true true hint named) := by
  unfold translateCanonicalSignalBinary
  first | rw [hw] | simp only [hw]  -- guess: T6
  refine KeepsCP.bind (KeepsCP.pure _) (fun _ => ?_)
  refine KeepsCP.bind (makeWireP O hA hS _ _ _) (fun _ => ?_)
  first  -- guess: T6
    | refine KeepsCP.bind (KeepsCP.ite (fun _ => hrec _ _ _ _) (fun h => (h rfl).elim))
        (fun _ => ?_)
    | refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  first
    | refine KeepsCP.bind (KeepsCP.ite (fun _ => hrec _ _ _ _) (fun h => (h rfl).elim))
        (fun _ => ?_)
    | refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (emitAssignP _ _) (fun _ => ?_)
  exact KeepsCP.pure _

/-- **The core**: a bound variable (`lookupVar`), a `Signal.pure` literal, a
canonical library operator (two recursive operand translations, a wire, an
assign), else `none`. -/
theorem translateCoreA (rec : TranslateFn)
    (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateCore rec e hint top named) := by
  unfold translateCore
  split
  · exact lookupVarP _
  · split
    · refine KeepsCP.ite (fun _ => translateSignalPureLiteralA O hA hS _ _ _) (fun _ => ?_)
      split
      · refine KeepsCP.bind
          (translateCanonicalSignalBinaryA O hA hS rec hrec _ _ _ _ _ _ (by assumption))  -- guess: T7
          (fun _ => ?_)
        exact KeepsCP.pure _
      · exact KeepsCP.pure _
    · exact KeepsCP.pure _

/-- **One step of the knot**, given the recursive argument and the fallback
(both at this admissible context): the validated lookup, the core, the record,
or the fallback. -/
theorem translateStepWithA (fallback : TranslateFn → TranslateFn) (rec : TranslateFn)
    (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
    (hfb : ∀ e hint top named, KeepsCP mctx mref cctx cref I (fallback rec e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateStepWith fallback rec e hint top named) := by
  unfold translateStepWith
  try dsimp only  -- guess: T8
  repeat (first
    | exact hfb _ _ _ _
    | exact cacheLookupValidatedA O hA hS _
    | exact recordTranslationA O hA hS _ _ _
    | exact translateCoreA O hA hS rec hrec _ _ _ _
    | kbase)

end Core

/-! ## The fuel induction -/

/-- The translator handed in as `rec` keeps `I` in every ADMISSIBLE context
and every `CtxOk` compiler context. -/
def RecA (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) (rec : TranslateFn) :
    Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named)

/-- **The fuel induction, generic in the predicate** (law-free). -/
theorem fuelFix_of {P : TranslateFn → Prop} (step : TranslateFn → TranslateFn)
    (h0 : P (translateFuelFix step 0)) (hs : ∀ rec, P rec → P (step rec)) :
    ∀ k, P (translateFuelFix step k)
  | 0 => h0
  | k + 1 => by
    first  -- guess: T9
      | exact hs _ (fuelFix_of step h0 hs k)
      | (unfold translateFuelFix; exact hs _ (fuelFix_of step h0 hs k))

/-- At fuel 0 the translator throws a message in the class. -/
theorem fuelZeroA (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop)
    (step : TranslateFn → TranslateFn) : RecA O I (translateFuelFix step 0) := by
  intro mctx cctx _ e hint top named
  unfold translateFuelFix
  exact KeepsCP.throw _ (by okmsg)

/-- **The translator from its fallback**: if the fallback keeps `I` whenever
its recursive argument does (`RecA`), the shipping translator does. -/
theorem translateA_of_fallback (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
    (hS : StableA O.quiet I) (tenv : Lean.Environment)
    (hF : ∀ rec, RecA O I rec → RecA O I (translateFallback tenv rec)) :
    RecA O I (fun e h t n => translateExprToWire tenv e h t n) := by
  have hfix : RecA O I (translateFuelFix (translateStep tenv) translateFuelLimit) := by
    refine fuelFix_of (P := RecA O I) (translateStep tenv) (fuelZeroA O I _) ?_ _
    intro rec hrec mctx cctx hA e hint top named
    unfold translateStep
    exact translateStepWithA O hA hS (translateFallback tenv) rec (hrec mctx cctx hA)
      (hF rec hrec mctx cctx hA) e hint top named
  intro mctx cctx hA e hint top named
  first
    | exact hfix mctx cctx hA e hint top named
    | (unfold translateExprToWire; exact hfix mctx cctx hA e hint top named)

end Tools.ShippingChildTranslateA
