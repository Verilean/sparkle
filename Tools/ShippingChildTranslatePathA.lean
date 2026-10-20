import Tools.ShippingChildFallbackA
-- BUILT by the integrator: tp1 exit 0 (first try) (worker par/tr, base 6a231b89). Isolated: only Tools/ShippingChildDepthA.lean uses it.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps MkRefd mref cref` at `hA : AdmCtx O.quiet mctx cctx` only.
-- The proofs of `emitLeavesAP`, `bindInputPortAP`, `bindCertifiedInputsAP`, `certRest_keepsAP`,
-- `fromConst_certified_keepsAP` COPY the built PathA proofs (pa1 exit 0) with `TripleC` replaced by
-- the restricted `KeepsCP` (Tools/ShippingChildTranslateA.lean); the PathA guesses P1-P6 carry over.
-- Writing-time guesses (new):
--  Q1 `emitLeavesAP`: the throw-then-tail branch closes by `KeepsCP.throwBind` (PathA closed it
--     with `TripleC.bind (Q := False)`, the same term inside `throwBind`);
--  Q2 `certRest_keepsAP`: `bindCertifiedInputsAP … _ _ _ (ctxOk_entry false hr)` fixes the
--     compiler context to `entryCompilerState false r` by unification with the type of
--     `ctxOk_entry`, and `Triple.bind` unifies it with `(compiler.run ctx).run st` (PathA P3);
--  Q3 `translate e h t n` for `translateExprToWire tenv` is accepted against the RecA instance
--     `(fun e h t n => translateExprToWire tenv e h t n) e h t n` (beta).

/-! # The certified branch with the translator in RESTRICTED form

PathA (`Tools/ShippingChildPathA.lean`) states the translator hypothesis of
`emitLeavesA`/`certRest_keepsA`/`fromConst_certified_*` as `KeepsC` — over
EVERY compiler context. The translator's own cache code only has laws for a
context whose cache ref has provenance, so the translator is proved
(`translate_keepsA`, Tools/ShippingChildFallbackA.lean) only in the restricted
form `KeepsCP` (contexts with `CtxOk`). Here the same certified branch is
re-proved from the RESTRICTED hypothesis:

* the entry's context `entryCompilerState false r` has `CtxOk` from the
  provenance `hr : MkRefd _ r` that `certified_keepsA` threads
  (`ctxOk_entry`);
* the binder walk keeps `CtxOk` (`withVarMapping` leaves `exprCache`:
  `withVarMappingP`);
* `emitLeaves` calls the translator in that context.

Then `fromConst_certified_hbody_of_handlers` plugs the translator
(`translate_keepsJQ` at depth 1, child recursion through `ChildKeepsA O 1`)
into the certified branch: the shape of `core_tripleA`'s `hbody` for the
certified constants, from exactly the handler premises of
Tools/ShippingChildFallbackA.lean. -/

namespace Tools.ShippingChildTranslatePathA
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
open Tools.ShippingChildFallbackA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Walk
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

/-- `emitLeaves`, the translator hypothesis restricted to `CtxOk` contexts. -/
theorem emitLeavesAP (translate : TranslateFn) (b : Bool) (r : IO.Ref (Lean.ExprStructMap String))
    (hr : MkRefd _ r)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named)) :
    ∀ (leaves : List (String × Lean.Expr)) (fw : Option String) (idx : Nat),
      KeepsCP mctx mref cctx cref I (emitLeaves translate r (profLogIO b) leaves fw idx)
  | [], fw, idx => by
    unfold emitLeaves
    exact KeepsCP.pure _
  | (pn, le) :: rest, fw, idx => by
    unfold emitLeaves
    have clock : KeepsCP mctx mref cctx cref I (CompilerM.liftMetaM (liftM IO.monoMsNow)) :=
      KeepsCP.lift (keepsA_framed O hA hS FramedA.monoMs)
    have calls : KeepsCP mctx mref cctx cref I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCallCounter)) :=
      KeepsCP.lift (keepsA_framed O hA hS (FramedA.sideGet .callCounter))
    have hits : KeepsCP mctx mref cctx cref I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCacheHits)) :=
      KeepsCP.lift (keepsA_framed O hA hS (FramedA.sideGet .cacheHits))
    have log : ∀ msg, KeepsCP mctx mref cctx cref I
        (CompilerM.liftMetaM (liftM (profLogIO b msg))) :=
      fun msg => KeepsCP.lift (keepsA_diag O hA hS (Diag.profLog b msg))
    refine KeepsCP.bind clock ?_; intro t0
    refine KeepsCP.bind calls ?_; intro c0
    refine KeepsCP.bind hits ?_; intro h0
    refine KeepsCP.bind (log _) ?_; intro _
    refine KeepsCP.bind (htr le pn false true) ?_; intro lw
    refine KeepsCP.bind clock ?_; intro t1
    refine KeepsCP.bind calls ?_; intro c1
    refine KeepsCP.bind hits ?_; intro h1
    refine KeepsCP.bind (log _) ?_; intro _
    dsimp only  -- PathA guess P1
    refine KeepsCP.ite
      (fun _ => KeepsCP.bind (KeepsCP.lift
        (keepsA_framed O hA hS (FramedA.exprCacheModify r _ hr))) (fun _ => ?_))  -- PathA guess P2
      (fun _ => ?_)
    all_goals
      try dsimp only
      refine KeepsCP.bind KeepsCP.get ?_
      intro cs
      try dsimp only
      refine KeepsCP.ite (fun _ => ?_) (fun _ => ?_)
      · exact KeepsCP.throwBind _ (by okmsg) _  -- guess: Q1
      · try dsimp only
        refine KeepsCP.bind (addOutputP O hA hS _ _) ?_
        intro _
        refine KeepsCP.bind (emitAssignP _ _) ?_
        intro _
        exact emitLeavesAP translate b r hr htr rest _ _  -- (recursive call: section variables fixed)

theorem bindInputPortAP {α : Type} (fv : FVarId) (bn : String) (ty : Sparkle.IR.Type.HWType)
    (k : CompilerM α) (hk : KeepsCP mctx mref cctx cref I k) :
    KeepsCP mctx mref cctx cref I (bindInputPort fv bn ty k) := by
  unfold bindInputPort
  refine KeepsCP.bind (makeWireP O hA hS _ _ _) (fun _ => ?_)
  refine KeepsCP.bind (addInputP O hA hS _ _) (fun _ => ?_)
  exact withVarMappingP _ _ hk

theorem bindCertifiedInputsAP {α : Type} (k : CompilerM α)
    (hk : KeepsCP mctx mref cctx cref I k) :
    ∀ l : List ((Name × GateBinder) × FVarId),
      KeepsCP mctx mref cctx cref I (bindCertifiedInputs k l)
  | [] => by unfold bindCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindCertifiedInputs
    exact bindCertifiedInputsAP k hk rest
  | ((_, .signal _), _) :: rest => by
    unfold bindCertifiedInputs
    exact bindInputPortAP O hA hS _ _ _ _ (bindCertifiedInputsAP k hk rest)

/-- **`hrest` of `certified_keepsA`, from the RESTRICTED translator**: the
entry context `entryCompilerState false r` has `CtxOk` from `hr`. -/
theorem certRest_keepsAP (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named))
    (ids : List FVarId) (r : IO.Ref (Lean.ExprStructMap String)) (hr : MkRefd _ r) :
    Keeps mctx mref cctx cref I (certRest translate (profLogIO b) declName bs body ids r) := by
  unfold certRest
  refine keeps_iff.mpr ?_
  try dsimp only  -- PathA guess P3
  refine Triple.bind (keeps_iff.mp (bindCertifiedInputsAP O hA hS _
    (emitLeavesAP O hA hS translate b r hr htr _ _ _) _ _ _ (ctxOk_entry false hr))) ?_  -- guess: Q2
  rintro ⟨_, fs⟩
  exact finishSynthA declName fs

theorem certified_keepsAP_of_translate (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I (synthesizeCertified translate (profLogIO b) declName bs body) :=
  certified_keepsA O hA hS translate (profLogIO b) declName bs body
    (fun ids r hr => certRest_keepsAP O hA hS translate b declName bs body htr ids r hr)

/-- **The certified branch of `synthesizeFromConst`**, from the RESTRICTED
translator (copy of `fromConst_certified_keepsA`). -/
theorem fromConst_certified_keepsAP (translate : TranslateFn) (b : Bool) (declName : Name)
    (constInfo : ConstantInfo) (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)}
    {body : Lean.Expr} (hshape : certifiedShape? false [] constInfo = some (bs, body))
    (htr : ∀ e hint top named, KeepsCP mctx mref cctx cref I (translate e hint top named)) :
    Keeps mctx mref cctx cref I
      (synthesizeFromConst translate (profLogIO b) declName [] false true constInfo isInst) := by
  have hd : (if true = true then certifiedShape? false [] constInfo else none) = some (bs, body) := by
    first  -- PathA guess P4
      | exact (if_pos rfl).trans hshape
      | (rw [if_pos rfl]; exact hshape)
      | simpa using hshape
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  rw [hd]
  first  -- PathA guesses P5, P6
    | refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_
    | (dsimp only; refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_)
  intro _
  refine Keeps.bind (certified_keepsAP_of_translate O hA hS translate b declName bs body htr) ?_
  intro result
  refine Keeps.bind (keepsA_framed O hA hS (FramedA.sideModify _ .subModule)) ?_
  intro _
  exact Keeps.pure _

end Walk

/-! ## The translator plugged in -/

/-- **The certified branch at depth `D` from the handler premises.** For a
constant whose certified shape matches, the body at `JQ O.quiet D` with the
entry's translator keeps the invariant, given the five handler premises of
Tools/ShippingChildFallbackA.lean at `JQ O.quiet D` — the child entry through
`ChildKeepsA O D`. -/
theorem fromConst_certified_of_handlers (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (D : Nat) (declName : Name) (tenv : Lean.Environment)
    (b : Bool) (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)}
    {body : Lean.Expr} (hshape : certifiedShape? false [] ci = some (bs, body))
    (hImpl : LegacyImplA O (JQ O.quiet D)) (hCached : LegacyCachedA O (JQ O.quiet D))
    (hcanon : CanonKeyA O (JQ O.quiet D)) (hpf : ProjFieldNameA O (JQ O.quiet D))
    (hC : ChildKeepsA O D) :
    Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst) :=
  fromConst_certified_keepsAP O hA (stableA_JQ _ D) _ b declName ci isInst hshape
    (fun e h t n => translate_keepsJQ O D tenv hImpl hCached hcanon hpf hC mctx cctx hA e h t n)  -- guess: Q3

/-- **The certified part of `core_tripleA`'s `hbody`, from the handler
premises** (depth 1; the child recursion through `ChildKeepsA O 1`, see
Tools/ShippingChildDepthA.lean). -/
theorem fromConst_certified_hbody_of_handlers (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) {tenv : Lean.Environment} (b : Bool)
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)}
    {body : Lean.Expr} (hshape : certifiedShape? false [] ci = some (bs, body))
    (hImpl : LegacyImplA O (JQ O.quiet 1)) (hCached : LegacyCachedA O (JQ O.quiet 1))
    (hcanon : CanonKeyA O (JQ O.quiet 1)) (hpf : ProjFieldNameA O (JQ O.quiet 1))
    (hC : ChildKeepsA O 1) :
    Keeps mctx mref cctx cref (JQ O.quiet 1)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst) :=
  fromConst_certified_of_handlers O hA 1 declName tenv b ci isInst hshape hImpl hCached hcanon
    hpf hC

end Tools.ShippingChildTranslatePathA
