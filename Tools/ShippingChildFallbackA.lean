import Tools.ShippingChildTranslateA
import Tools.ShippingChildKWalk
-- BUILT by the integrator: fb1-fb12 exit 1 (the generic `repeat (first | exact … | kbase)` walk timed out at 13 sites, also at 1M heartbeats (fb2); replaced by the head-directed `kwalk` (Tools/ShippingChildKWalk.lean); the instance dispatch and the 15-arm fallback walked from the printed terms (run pr2); `instAddModulesA` by induction + equation lemma), fb13 exit 0 (worker par/tr, base 6a231b89). Isolated: only Tools/ShippingChildTranslatePathA.lean uses
-- it. No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only; NO `RefLawsATele`
-- (no arm proved here runs a telescope). Reused law-free: the calculus of
-- Tools/ShippingChildTranslateA.lean, `keepsA_framed`, `stableA_JQ`, `runsTo_get_readOf`,
-- `Triple.bindQ`, `keeps_iff`, `okmsg`.
-- Writing-time guesses (marked `-- guess: Fn`):
--  F1 `set_option hygiene false in macro "karm"`: the names in the quotation (`hrec`, `O`, `hA`,
--     `hS`, the lemmas) resolve at the USE site; an alternative naming an absent hypothesis fails
--     inside `first` and the next is tried;
--  F2 after `unfold <arm>` (+ `try dsimp only` for beta/zeta), the arm's `do` block is walked by
--     `karm`/`kbase` (bind, ite, `split` of `match`/`let (a, b) :=`, the lemmas); the old proofs
--     (`vc`, ShippingChildFallback.lean) walked the same bodies with the same rules;
--  F3 `split` on `match e with` (translateBoolUncachedWith, memory, instance arm): `e` is a
--     variable, as in `vc`'s `Split.splitMatch` after its generalisation (built);
--  F4 the `if c then throw …` statements of the instance helpers elaborate either to
--     `ite c (throw … >>= k) k` or to `(ite c (throw …) (pure ())) >>= k`; both are walked
--     (`throwBind` / `bind`+`ite`);
--  F5 `okmsg` closes the `m!"Instance of {recName}: …"` message (MessageData.ofName unfolds to
--     `ofFormatWithInfos`) as it did inside `vc` for `instLinkGuard_keepsC`;
--  F6 `translateFallbackA`: `split` on `match fallbackKind e with` yields the 15 arms in
--     declaration order; each is closed by `first` over the arm lemmas (order-independent);
--  F7 `refine translateControlCachedWithA O hA hS _ (fun _ _ _ _ => ?_) _ _ _ _` assigns `lower`
--     from the goal; the arm lemma then closes `lower e h t n`;
--  F8 `childEntryA_of_childKeeps`: copy of the built `childSynthEntry_keeps` (bindQ on the
--     synthesis read, `subst`, matcher reduction by `exact`).

/-! # The fallback, decomposed into its handlers, under the admissible boundary

`translateFallback env rec` dispatches on `fallbackKind e` (Elab.lean:8818).
EVERY handler it reaches, and what this file does with it:

| arm (`fallbackKind`) | handler | status |
|---|---|---|
| `boolControl` | `translateControlCachedWith (translateBoolUncachedWith rec legacyImpl)` | PROVED (`translateBoolUncachedWithA`): literals, compares, Bool binary ops, Bool mux, complement, applicative Bool ops; its own legacy fall-through is premise `LegacyImplA` |
| `vectorMux n` | `translateVectorMuxUncachedWith` | PROVED |
| `setWidth ws wt` | `translateSetWidthUncachedWith` | PROVED |
| `register w v` | `translateRegisterUncachedWith` | PROVED |
| `registerEnable w v` | `translateRegisterEnableUncachedWith` | PROVED |
| `loopRegister w v` | `translateLoopRegisterUncachedWith` | PROVED (`FramedA.freshFVar`) |
| `circuitDo w v` | `translateCircuitDoUncachedWith` | PROVED |
| `circuitDo2 …` | `translateCircuitDo2UncachedWith` | PROVED |
| `memory aw dw` | `translateMemoryUncachedWith` | PROVED |
| `slice` | `translateSliceUncachedWith` | PROVED |
| `concat m n` | `translateConcatUncachedWith` | PROVED |
| `concatLit …` | `translateConcatLitUncachedWith` | PROVED |
| `zextMap ws k` | `translateSetWidthUncachedWith rec ws (k + ws)` | PROVED |
| `sliceF` | `translateSliceFUncachedWith` | PROVED |
| `other` | `translateInstanceOrFallback env rec` | dispatch PROVED (`translateInstanceOrFallbackA`) with: |
| | — single-output child call: `childSynthEntry` + `translateInstanceUncachedWith` | `translateInstanceUncachedWithA` PROVED (module registration, clk/rst plumbing, arity check, operand translations, the single-out instance cache `FramedA.sideGet/sideModify .singleOut`, link check, instance statement); the child synthesis is premise `ChildEntryA` (from `ChildKeepsA O D` at `JQ`, `childEntryA_of_childKeeps`) |
| | — projection of a multi-output child: `projFieldName?`, `childSynthEntry`, `translateProjInstanceUncachedWith` | `translateProjInstanceUncachedWithA` PROVED given premise `CanonKeyA` (the call key `canonHardwareKey`, a fuel fixpoint of `whnf`/`instantiateMVars`/… steps, not migrated); `projFieldName?` is premise `ProjFieldNameA` (it runs `forallTelescopeReducing`: needs `RefLawsATele.telescope`, plus `getConstInfoInduct`/`Ctor` and `getUserName` walks — not attempted) |
| | — everything else | `Rec.translateExprToWireCached` — premise `LegacyCachedA` |

Every arm is wrapped in `translateControlCachedWith` (`translateControlCachedWithA`,
PROVED: `cacheLookupValidatedA`, `recordTranslationA`).

The premises, one per handler NOT migrated (each named after it):
* `LegacyImplA`   — `Rec.translateExprToWireImpl` (the legacy translator's main body:
  `handleApplicative`, `handleBitVecOps`, `handleRegister`, `handleMux`, `handleMemory`,
  `handleLoop`, `handleCircuitMonad`, `handleDefinitionUnfold`, … — telescopes and
  `whnf`-driven helpers; NOT decomposed here);
* `LegacyCachedA` — `Rec.translateExprToWireCached` (its cache wrapper around the same);
* `CanonKeyA`     — `canonHardwareKey`;
* `ProjFieldNameA` — `projFieldName?` (needs `RefLawsATele`);
* `ChildEntryA`   — `childSynthEntry` (the child recursion; `ChildKeepsA` at `JQ`).

`translate_keepsA`: the shipping translator keeps `I` given exactly these five. -/

namespace Tools.ShippingChildFallbackA
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

-- (F1) the arm walker: the recursive translator, the primitives, then `kbase`
set_option hygiene false in
macro "karm" : tactic => `(tactic| kwalk [makeWireP, emitAssignP, addInputP, bindSourceVariableP,
  lookupVarP, emitRegisterStmtA, emitRegisterA, emitMemoryA, freshNameA, emitInstanceA,
  addModuleToDesignA])
-- (integrator, after fb1/fb2: the old `repeat (first | exact … | kbase)` walk timed out at every
-- site; `kwalk` (Tools/ShippingChildKWalk.lean) picks the rule by the program's head first)

/-! ## The result emitters -/

section Emit
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

theorem emitBoolResultA (rhs : Sparkle.IR.AST.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitBoolResult rhs hint named) := by
  unfold emitBoolResult
  karm

theorem emitCompareResultA (le : SignalCompareKind) (a b hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitCompareResult le a b hint named) := by
  unfold emitCompareResult
  exact emitBoolResultA O hA hS _ _ _

theorem emitBoolLiteralA (value : Bool) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitBoolLiteral value hint named) := by
  unfold emitBoolLiteral
  exact emitBoolResultA O hA hS _ _ _

theorem emitCastResultA (rhs : Sparkle.IR.AST.Expr) (wt : Nat) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitCastResult rhs wt hint named) := by
  unfold emitCastResult
  karm

theorem emitSliceResultA (rhs : Sparkle.IR.AST.Expr) (len : Nat) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (emitSliceResult rhs len hint named) := by
  unfold emitSliceResult
  karm

theorem emitMuxResultA (c t el hint : String) (named : Bool) (ty : Sparkle.IR.Type.HWType) :
    KeepsCP mctx mref cctx cref I (emitMuxResult c t el hint named ty) := by
  unfold emitMuxResult
  karm

theorem emitConcatConstA (k v : Nat) :
    KeepsCP mctx mref cctx cref I (emitConcatConst k v) := by
  unfold emitConcatConst
  exact emitCastResultA O hA hS _ _ _ _

theorem translateConcatActsA (w : Nat) (hiAct loAct : CompilerM String)
    (hhi : KeepsCP mctx mref cctx cref I hiAct) (hlo : KeepsCP mctx mref cctx cref I loAct)
    (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateConcatActs w hiAct loAct hint named) := by
  unfold translateConcatActs
  refine KeepsCP.bind (makeWireP O hA hS _ _ _) (fun _ => ?_)
  refine KeepsCP.bind hhi (fun _ => ?_)
  refine KeepsCP.bind hlo (fun _ => ?_)
  refine KeepsCP.bind (emitAssignP _ _) (fun _ => ?_)
  exact KeepsCP.pure _

end Emit

/-! ## The arms (given the recursive argument at this context) -/

section Arms
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) (rec : TranslateFn)
  (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
include O hA hS hrec

theorem translateMuxWithA (resultType : CompilerM Sparkle.IR.Type.HWType)
    (hres : KeepsCP mctx mref cctx cref I resultType) (c t el : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateMuxWith rec resultType c t el hint named) := by
  unfold translateMuxWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind hres (fun _ => ?_)
  exact emitMuxResultA O hA hS _ _ _ _ _ _

theorem translateBoolBinaryA (kind : SignalBoolBinKind) (a b : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateBoolBinary rec kind a b hint named) := by
  unfold translateBoolBinary
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitBoolResultA O hA hS _ _ _

theorem translateSignalCompareA (le : SignalCompareKind) (a b : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSignalCompare rec le a b hint named) := by
  unfold translateSignalCompare
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitCompareResultA O hA hS _ _ _ _ _

theorem translateAppCompareA (le : SignalCompareKind) (a b : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateAppCompare rec le a b hint named) := by
  unfold translateAppCompare
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitCompareResultA O hA hS _ _ _ _ _

theorem translateAppBoolBinaryA (kind : SignalBoolBinKind) (a b : Lean.Expr) (hint : String)
    (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateAppBoolBinary rec kind a b hint named) := by
  unfold translateAppBoolBinary
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitBoolResultA O hA hS _ _ _

theorem translateAppBool2A (f : AppBool2) (a b : Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateAppBool2 rec f a b hint named) := by
  unfold translateAppBool2
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (emitBoolResultA O hA hS _ _ _) (fun _ => ?_)
  exact emitBoolResultA O hA hS _ _ _

theorem translateAppBoolA (op : AppBoolOp) (a b : Lean.Expr) (hint : String) (named : Bool) :
    KeepsCP mctx mref cctx cref I (translateAppBool rec op a b hint named) := by
  unfold translateAppBool
  split
  · exact translateAppCompareA O hA hS rec hrec _ _ _ _ _
  · exact translateAppBoolBinaryA O hA hS rec hrec _ _ _ _ _
  · exact translateAppBool2A O hA hS rec hrec _ _ _ _ _

/-- **The Bool-control arm**: literals, compares, Bool binary operators, the Bool
mux, complement, applicative Bool ops — and, for any other shape, the legacy
handler handed in (`hleg`). -/
theorem translateBoolUncachedWithA (legacy : TranslateFn)
    (hleg : ∀ e hint top named, KeepsCP mctx mref cctx cref I (legacy e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateBoolUncachedWith rec legacy e hint top named) := by
  unfold translateBoolUncachedWith
  try dsimp only
  kwalk [hleg _ _ _ _, emitBoolLiteralA O hA hS _ _ _, translateSignalCompareA O hA hS rec hrec _ _ _ _ _, translateBoolBinaryA O hA hS rec hrec _ _ _ _ _, translateMuxWithA O hA hS rec hrec _ (KeepsCP.pure _) _ _ _ _ _, translateAppBoolA O hA hS rec hrec _ _ _ _ _]  -- guess: F3

theorem translateVectorMuxUncachedWithA (n : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateVectorMuxUncachedWith rec n e hint top named) := by
  unfold translateVectorMuxUncachedWith
  exact translateMuxWithA O hA hS rec hrec _ (KeepsCP.pure _) _ _ _ _ _

theorem translateSetWidthUncachedWithA (ws wt : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSetWidthUncachedWith rec ws wt e hint top named) := by
  unfold translateSetWidthUncachedWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitCastResultA O hA hS _ _ _ _

theorem translateSliceUncachedWithA (start len : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSliceUncachedWith rec start len e hint top named) := by
  unfold translateSliceUncachedWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitSliceResultA O hA hS _ _ _ _

theorem translateSliceFUncachedWithA (start len : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateSliceFUncachedWith rec start len e hint top named) := by
  unfold translateSliceFUncachedWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitSliceResultA O hA hS _ _ _ _

theorem translateConcatUncachedWithA (m n : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateConcatUncachedWith rec m n e hint top named) := by
  unfold translateConcatUncachedWith translateConcatWith
  exact translateConcatActsA O hA hS _ _ _ (hrec _ _ _ _) (hrec _ _ _ _) _ _

theorem translateConcatLitUncachedWithA (hi : Bool) (k v w : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateConcatLitUncachedWith rec hi k v w e hint top named) := by
  unfold translateConcatLitUncachedWith
  refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
  · exact translateConcatActsA O hA hS _ _ _ (emitConcatConstA O hA hS _ _) (hrec _ _ _ _) _ _
  · exact translateConcatActsA O hA hS _ _ _ (hrec _ _ _ _) (emitConcatConstA O hA hS _ _) _ _

theorem translateRegisterUncachedWithA (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateRegisterUncachedWith rec w v e hint top named) := by
  unfold translateRegisterUncachedWith
  refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
  exact emitRegisterA O hA hS _ _ _ _ _ _ _ _

theorem translateRegisterEnableUncachedWithA (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I
      (translateRegisterEnableUncachedWith rec w v e hint top named) := by
  unfold translateRegisterEnableUncachedWith
  try dsimp only
  karm

theorem translateLoopRegisterUncachedWithA (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateLoopRegisterUncachedWith rec w v e hint top named) := by
  unfold translateLoopRegisterUncachedWith
  try dsimp only  -- guess: F2
  karm

theorem translateCircuitDoUncachedWithA (w v : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateCircuitDoUncachedWith rec w v e hint top named) := by
  unfold translateCircuitDoUncachedWith
  try dsimp only  -- guess: F2
  karm

theorem translateCircuitDo2UncachedWithA (w v0 v1 ret : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I
      (translateCircuitDo2UncachedWith rec w v0 v1 ret e hint top named) := by
  unfold translateCircuitDo2UncachedWith
  try dsimp only  -- guess: F2
  karm

theorem translateMemoryUncachedWithA (aw dw : Nat) (e : Lean.Expr) (hint : String)
    (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateMemoryUncachedWith rec aw dw e hint top named) := by
  unfold translateMemoryUncachedWith
  try dsimp only  -- guess: F3
  karm

/-- One recursive translation per instance operand. -/
theorem instArgsA :
    ∀ (rest : List (Sparkle.IR.AST.Port × Lean.Expr)) (acc : List (String × Sparkle.IR.AST.Expr))
      (i : Nat), KeepsCP mctx mref cctx cref I (instArgs rec acc rest i)
  | [], acc, i => by unfold instArgs; exact KeepsCP.pure _
  | (p, a) :: rest, acc, i => by
    have ih := fun acc i => instArgsA rest acc i
    unfold instArgs
    refine KeepsCP.bind (hrec _ _ _ _) (fun _ => ?_)
    exact ih _ _

end Arms

/-! ## The shared validated-cache wrapper -/

section Wrapper
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

theorem translateControlCachedWithA (lower : TranslateFn)
    (hlow : ∀ e hint top named, KeepsCP mctx mref cctx cref I (lower e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateControlCachedWith lower e hint top named) := by
  unfold translateControlCachedWith
  try dsimp only
  kwalk [hlow _ _ _ _, cacheLookupValidatedA O hA hS _, recordTranslationA O hA hS _ _ _]

/-! ## The instance helpers (child compile in hand) -/

theorem instArmCacheGetA : Keeps mctx mref cctx cref I instArmCacheGet := by
  unfold instArmCacheGet
  exact keepsA_framed O hA hS (FramedA.sideGet .singleOut)

theorem instArmCachePutA (key w : String) : Keeps mctx mref cctx cref I (instArmCachePut key w) := by
  unfold instArmCachePut
  exact keepsA_framed O hA hS (FramedA.sideModify _ .singleOut)

theorem instArmOutGetA : Keeps mctx mref cctx cref I instArmOutGet := by
  unfold instArmOutGet
  exact keepsA_framed O hA hS (FramedA.sideGet .subInstOut)

theorem instArmOutPutA (key : UInt64) (out w : String) :
    Keeps mctx mref cctx cref I (instArmOutPut key out w) := by
  unfold instArmOutPut
  exact keepsA_framed O hA hS (FramedA.sideModify _ .subInstOut)

theorem instAddModulesA (existing : List String) :
    ∀ ms : List Sparkle.IR.AST.Module,
      KeepsCP mctx mref cctx cref I (instAddModules existing ms) := by
  -- (integrator, after fb6-fb9 timed out at the declaration: `induction` instead of a
  -- recursive theorem)
  intro ms
  induction ms with
  | nil => rw [instAddModules.eq_1]; exact KeepsCP.pure _
  | cons m ms ih =>
    -- (`unfold` timed out in `simp`, fb11: the equation lemma by `rw`)
    rw [instAddModules.eq_2]
    exact KeepsCP.ite (fun _ => KeepsCP.bind (addModuleToDesignA _) (fun _ => ih)) (fun _ => ih)

theorem instRegisterChildA (existing : List String) (sub : Sparkle.IR.AST.Module) :
    KeepsCP mctx mref cctx cref I (instRegisterChild existing sub) := by
  unfold instRegisterChild
  try dsimp only
  kwalk [addModuleToDesignA _]

theorem instClkRstA :
    ∀ (ps : List Sparkle.IR.AST.Port) (acc : List (String × Sparkle.IR.AST.Expr)),
      KeepsCP mctx mref cctx cref I (instClkRst acc ps)
  | [], acc => by unfold instClkRst; exact KeepsCP.pure _
  | p :: ps, acc => by
    have ih := fun acc => instClkRstA ps acc
    unfold instClkRst
    try dsimp only
    kwalk [ih _, addInputP O hA hS _ _]  -- guess: F4

theorem instOutWiresA (callKey : UInt64) (hint : String) :
    ∀ (ps : List Sparkle.IR.AST.Port) (conns : List (String × Sparkle.IR.AST.Expr))
      (ws : List (String × String)),
      KeepsCP mctx mref cctx cref I (instOutWires callKey hint ps conns ws)
  | [], conns, ws => by unfold instOutWires; exact KeepsCP.pure _
  | outP :: rest, conns, ws => by
    have ih := fun conns ws => instOutWiresA callKey hint rest conns ws
    unfold instOutWires
    refine KeepsCP.bind (makeWireP O hA hS _ _ _) (fun _ => ?_)
    refine KeepsCP.bind (KeepsCP.lift (instArmOutPutA O hA hS _ _ _)) (fun _ => ?_)
    exact ih _ _

end Wrapper

section LawFreeInst
variable {I : Void IO.RealWorld → Prop}

theorem instArityCheckA (mn : Name) (need got : Nat) :
    KeepsCP mctx mref cctx cref I (instArityCheck mn need got) := by
  unfold instArityCheck
  refine KeepsCP.ite (fun _ => KeepsCP.throw _ (by okmsg)) (fun _ => KeepsCP.pure _)

theorem instLinkCheckA (mn : Name) (child : Sparkle.IR.AST.Module)
    (conns : List (String × Sparkle.IR.AST.Expr)) :
    KeepsCP mctx mref cctx cref I (instLinkCheck mn child conns) := by
  unfold instLinkCheck
  refine KeepsCP.bind KeepsCP.get (fun _ => ?_)
  unfold instLinkGuard
  refine KeepsCP.ite (fun _ => KeepsCP.pure _) (fun _ => KeepsCP.throw _ (by okmsg))  -- guess: F5

/-- The call key: a builder-state save/restore around `canonHardwareKey`
(premise `hcanon`: not migrated). -/
theorem instCallKeyA (hcanon : ∀ a, KeepsCP mctx mref cctx cref I (canonHardwareKey a))
    (a : Lean.Expr) : KeepsCP mctx mref cctx cref I (instCallKey a) := by
  unfold instCallKey
  refine KeepsCP.bind KeepsCP.get (fun _ => ?_)
  refine KeepsCP.bind (hcanon _) (fun _ => ?_)
  refine KeepsCP.bind (KeepsCP.set _) (fun _ => ?_)
  exact KeepsCP.pure _

end LawFreeInst

/-! ## The instance lowerings -/

section Inst
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) (rec : TranslateFn)
  (hrec : ∀ e hint top named, KeepsCP mctx mref cctx cref I (rec e hint top named))
include O hA hS hrec

/-- **The single-output instance lowering** (child compile in hand). -/
theorem translateInstanceUncachedWithA (mn : Name) (sub : Sparkle.IR.AST.Module)
    (subD : Sparkle.IR.AST.Design) (singleOut : Sparkle.IR.AST.Port)
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I
      (translateInstanceUncachedWith rec mn sub subD singleOut e hint top named) := by
  unfold translateInstanceUncachedWith
  try dsimp only  -- guess: F2
  kwalk [instArmCacheGetA O hA hS, instArmCachePutA O hA hS, hrec _ _ _ _, instAddModulesA O hA hS _ _, instRegisterChildA O hA hS _ _, instClkRstA O hA hS _ _, instArityCheckA _ _ _, instArgsA O hA hS rec hrec _ _ _, KeepsCP.lift (instArmCacheGetA O hA hS), KeepsCP.lift (instArmCachePutA O hA hS _ _), makeWireP O hA hS _ _ _, freshNameA _ _, instLinkCheckA _ _ _, emitInstanceA _ _ _]

/-- **The multi-output projection lowering** (child compile in hand), given
the call key's `canonHardwareKey` (premise) and the legacy fall-through. -/
theorem translateProjInstanceUncachedWithA
    (hcanon : ∀ a, KeepsCP mctx mref cctx cref I (canonHardwareKey a))
    (recName : Name) (sub : Sparkle.IR.AST.Module) (subD : Sparkle.IR.AST.Design)
    (fieldName : String) (recordArg : Lean.Expr) (legacy : TranslateFn)
    (hleg : ∀ e hint top named, KeepsCP mctx mref cctx cref I (legacy e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I
      (translateProjInstanceUncachedWith rec recName sub subD fieldName recordArg legacy
        e hint top named) := by
  unfold translateProjInstanceUncachedWith
  try dsimp only  -- guess: F2
  kwalk [instArmOutGetA O hA hS, hleg _ _ _ _, hrec _ _ _ _, instCallKeyA hcanon _, KeepsCP.lift (instArmOutGetA O hA hS), instAddModulesA O hA hS _ _, instRegisterChildA O hA hS _ _, instClkRstA O hA hS _ _, instArityCheckA _ _ _, instArgsA O hA hS rec hrec _ _ _, instOutWiresA O hA hS _ _ _ _ _, freshNameA _ _, instLinkCheckA _ _ _, emitInstanceA _ _ _]

/-- **The instance arm** (`fallbackKind e = .other`): the dispatch on the
head, the child's synthesis (`hchild`), the two certified lowerings under the
validated cache wrapper, else the legacy translator (`hlegC`). -/
theorem translateInstanceOrFallbackA (env : Lean.Environment)
    (hchild : ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c))
    (hpf : ∀ n s, Keeps mctx mref cctx cref I (projFieldName? n s))
    (hcanon : ∀ a, KeepsCP mctx mref cctx cref I (canonHardwareKey a))
    (hlegC : ∀ e hint top named, KeepsCP mctx mref cctx cref I
      (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named))
    (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsCP mctx mref cctx cref I (translateInstanceOrFallback env rec e hint top named) := by
  unfold translateInstanceOrFallback
  -- (integrator, after fb1-fb8 timed out on the generic walk: the elaborated term, printed by
  -- `#print` (run pr2), walked by hand)
  split
  · refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
    · refine KeepsCP.bind (KeepsCP.lift (hchild _)) (fun sub => ?_)
      split
      · exact translateControlCachedWithA O hA hS _
          (translateInstanceUncachedWithA O hA hS rec hrec _ _ _ _) _ _ _ _
      · exact hlegC _ _ _ _
    · split
      · split
        · refine KeepsCP.ite (fun _ => ?_) (fun _ => hlegC _ _ _ _)
          refine KeepsCP.bind (KeepsCP.lift (hpf _ _)) (fun fo => ?_)
          cases fo with
          | some fieldName =>
            refine KeepsCP.bind (KeepsCP.lift (hchild _)) (fun sub => ?_)
            exact KeepsCP.ite
              (fun _ => translateControlCachedWithA O hA hS _
                (translateProjInstanceUncachedWithA O hA hS rec hrec hcanon _ _ _ _ _ _
                  (fun e h t n => hlegC e h t n)) _ _ _ _)
              (fun _ => hlegC _ _ _ _)
          | none => exact hlegC _ _ _ _
        · exact hlegC _ _ _ _
      · exact hlegC _ _ _ _
  · exact hlegC _ _ _ _

end Inst

/-! ## The premises: one per handler not migrated -/

/-- `Rec.translateExprToWireImpl` (the legacy translator's main body). -/
def LegacyImplA (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ rec, RecA O I rec →
    RecA O I (fun e h t n => Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e h t n)

/-- `Rec.translateExprToWireCached` (its cache wrapper). -/
def LegacyCachedA (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ rec, RecA O I rec →
    RecA O I (fun e h t n => Rec.translateExprToWireCached (fun e h t n => rec e h t n) e h t n)

/-- `canonHardwareKey` (the multi-output call key). -/
def CanonKeyA (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ a, KeepsCP mctx mref cctx cref I (canonHardwareKey a)

/-- `projFieldName?` (runs `forallTelescopeReducing`: needs `RefLawsATele`). -/
def ProjFieldNameA (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ n s, Keeps mctx mref cctx cref I (projFieldName? n s)

/-- `childSynthEntry` (the child recursion). -/
def ChildEntryA (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c)

/-- **The memoised child entry at depth `D`** keeps `JQ` in every admissible
context (the new-boundary analogue of `ChildKeeps L D`). -/
def ChildKeepsA (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref (JQ O.quiet D) (synthesizeChild c)

/-! ## The fallback and the translator -/

/-- **The fallback, one arm per `fallbackKind`.** -/
theorem translateFallbackA (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
    (hS : StableA O.quiet I) (tenv : Lean.Environment)
    (hImpl : LegacyImplA O I) (hCached : LegacyCachedA O I) (hcanon : CanonKeyA O I)
    (hpf : ProjFieldNameA O I) (hchild : ChildEntryA O I)
    (rec : TranslateFn) (hrec : RecA O I rec) : RecA O I (translateFallback tenv rec) := by
  intro mctx cctx hA e hint top named
  have hr := hrec mctx cctx hA
  have hI := hImpl rec hrec mctx cctx hA
  have hC := hCached rec hrec mctx cctx hA
  unfold translateFallback
  try dsimp only
  -- (integrator, after fb1-fb8: one `kwalk` over the 15 arms, each chosen by its head)
  split
  all_goals kwalk [translateControlCachedWithA O hA hS,
    (translateBoolUncachedWithA O hA hS rec hr _ (fun e h t n => hI e h t n)),
    translateVectorMuxUncachedWithA O hA hS rec hr, translateSetWidthUncachedWithA O hA hS rec hr,
    translateRegisterUncachedWithA O hA hS rec hr,
    translateRegisterEnableUncachedWithA O hA hS rec hr,
    translateLoopRegisterUncachedWithA O hA hS rec hr,
    translateCircuitDoUncachedWithA O hA hS rec hr,
    translateCircuitDo2UncachedWithA O hA hS rec hr,
    translateMemoryUncachedWithA O hA hS rec hr, translateSliceUncachedWithA O hA hS rec hr,
    translateConcatUncachedWithA O hA hS rec hr, translateConcatLitUncachedWithA O hA hS rec hr,
    translateSliceFUncachedWithA O hA hS rec hr,
    (translateInstanceOrFallbackA O hA hS rec hr tenv (hchild mctx cctx hA)
      (hpf mctx cctx hA) (hcanon mctx cctx hA) (fun e h t n => hC e h t n))]

/-- **The shipping translator keeps a stable `I`**, in every admissible context
and every `CtxOk` compiler context, given exactly the five premises (one per
handler not migrated). -/
theorem translate_keepsA (O : RefLawsAOps MkRefd mref cref) {I : Void IO.RealWorld → Prop}
    (hS : StableA O.quiet I) (tenv : Lean.Environment)
    (hImpl : LegacyImplA O I) (hCached : LegacyCachedA O I) (hcanon : CanonKeyA O I)
    (hpf : ProjFieldNameA O I) (hchild : ChildEntryA O I) :
    RecA O I (fun e h t n => translateExprToWire tenv e h t n) :=
  translateA_of_fallback O hS tenv
    (fun rec hrec => translateFallbackA O hS tenv hImpl hCached hcanon hpf hchild rec hrec)

/-! ## The child entry from the memoised child's keep (`JQ`) -/

/-- The synthesis ref's read under `JQ`: it returns `some synthesizeChild`. -/
theorem tripleA_synthRead (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) :
    Triple mctx mref cctx cref (JQ O.quiet D) (sparkleChildSynth.get : MetaM _)
      (fun s w => JQ O.quiet D w ∧ s = some synthesizeChild)
      (fun e w => JQ O.quiet D w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ D) FramedA.synthGet) w hw
  cases hm : (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    rw [hm] at hK
    exact ⟨hK, (runsTo_get_readOf _ hm).trans hw.2.1⟩
  | error e w1 => rw [hm] at hK; exact hK

/-- **`ChildEntryA` at `JQ O.quiet D` from `ChildKeepsA O D`.** -/
theorem childEntryA_of_childKeeps (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hC : ChildKeepsA O D) : ChildEntryA O (JQ O.quiet D) := by
  intro mctx cctx hA c
  rw [keeps_iff]
  unfold childSynthEntry
  refine Triple.bindQ (tripleA_synthRead O hA D) ?_  -- guess: F8
  intro s hs
  subst hs
  exact keeps_iff.mp (hC mctx cctx hA c)

/-- **The translator at `JQ O.quiet D`**, the child recursion through
`ChildKeepsA O D`. -/
theorem translate_keepsJQ (O : RefLawsAOps MkRefd mref cref) (D : Nat) (tenv : Lean.Environment)
    (hImpl : LegacyImplA O (JQ O.quiet D)) (hCached : LegacyCachedA O (JQ O.quiet D))
    (hcanon : CanonKeyA O (JQ O.quiet D)) (hpf : ProjFieldNameA O (JQ O.quiet D))
    (hC : ChildKeepsA O D) :
    RecA O (JQ O.quiet D) (fun e h t n => translateExprToWire tenv e h t n) :=
  translate_keepsA O (stableA_JQ _ D) tenv hImpl hCached hcanon hpf
    (childEntryA_of_childKeeps O D hC)

end Tools.ShippingChildFallbackA
