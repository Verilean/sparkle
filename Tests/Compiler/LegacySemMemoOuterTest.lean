import Tools.ShippingLegacySemMemoOuter
import Tests.Compiler.LegacySemInstanceTest

variable {tenv : Lean.Environment}

/-! # `useDbl` at the outermost entry, without the memo disjunct; the audit

`useDbl_output` (`Tests/Compiler/LegacySemInstanceTest.lean`) concludes
`MemoHit ∨ …` for a run of `synthesizeFromConst` with the certified front end
OFF (the configuration in which `useDbl` reaches the legacy arm). Here:

* `useDbl_output_at` — the same for ONE run (`RunsTo`), first disjunct a fact
  about this run's start world;
* `useDbl_output_outer` — for a returning run of the ENTRY
  `synthesizeCombinationalCoreWith (real translator) ``useDbl [] false
  (certifiedFrontEnd := false)` from synthesis depth 0: no memo disjunct.
  Premises beyond `useDbl_output`'s: the boundary (`L : RefLawsM`, depth 0,
  quiet) and `hci` — every read of the declaration in these contexts returns
  `.defnInfo dv` (with the front end off the entry constant is the
  declaration as read: `entryConst_off`).

Both are under `RefLawsM`: an EXTENSION of the trust base, never proved
against the runtime. The audit below THROWS on a non-standard axiom. -/

open Lean Meta Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingLegacySem
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMemo (RefLawsM)

namespace Sparkle.Tests.Compiler.LegacySemInstanceTest

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`useDbl_output` for ONE run.** -/
theorem useDbl_output_at (L : RefLawsM mref cref)
    {logProf : String → IO Unit} {dv : DefinitionVal}
    {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {xTy : Lean.Expr} {w0 w1 : Void IO.RealWorld}
    (htel : LamTelescopeOne)
    (hbody : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      ∃ (T b : Lean.Expr) (bi : BinderInfo),
        stripMemoizeWrappers body0 = Lean.Expr.lam `x T b bi ∧ b.isLambda = false ∧
        T.instantiateRevRange 0 0 #[] = xTy ∧
        ∀ id : FVarId, b.instantiateRevRange 0 1 #[Lean.Expr.fvar id] = callE id)
    (hinf : InfersBits xTy 8)
    (hinfT : InfersNoCatch xTy)
    (hres : ∀ id : FVarId, SignalTyped (callE id))
    (hmap : ∀ (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
      HasMappedFVar (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hplain : PlainHead tenv ``dbl)
    (hnosub : ∀ (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (fuel : Nat),
      NoSubModule (translateFuelFix (translateStep tenv) fuel)
        (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hunfE : ∀ (xid : FVarId) (e' : Lean.Expr), InlineUnfolds (callE xid) e' →
      ∃ dom : Lean.Expr, e' = dblUnfoldE dom xid)
    (hr : RunsTo (synthesizeFromConst
      (fun e hint top named => translateExprToWire tenv e hint top named)
      logProf ``useDbl [] false false (.defnInfo dv) isInst) mctx mref cctx cref w0 (m, d) w1) :
    (L.mval w0).get? ``useDbl = some (m, d) ∨
    ∃ (id : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (useDblBinders.zip [id])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``useDbl)) →
      Tools.ShippingMixedEntrySoundness.RawValueAt 8 useDblBinders m initial mems
        (bits id 8 + bits id 8).toNat := by
  have htele : ∀ body0,
      Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (OneBinderScope `x xTy callE) := by
    intro body0 hopen
    obtain ⟨T, b, bi, hb, hl, hT, hi⟩ := hbody body0 hopen
    exact telescopeIn_of_lam htel hb hl hT hi
  rcases one_binder_entry_output_bound_at L (cfe := false) (nm := `x) (n := 8) (T := xTy)
      (leafOf := callE)
      (fun h => absurd h Bool.false_ne_true) (fun h => absurd h Bool.false_ne_true)
      (fun h => absurd h Bool.false_ne_true) htele (isSignalBinderType_frame xTy) hinf hinfT
      (fun id => ⟨rfl, hres id⟩) hr with hit | ⟨id, cache, H⟩
  · exact Or.inl hit
  · refine Or.inr ⟨id, cache, ?_⟩
    intro bools bits initial mems values
    exact H bools bits initial mems values
      (.bits 8 (bits id 8 + bits id 8)) (Nat.succ_pos 7)
      (LeafDom.inlineAt (dbl_notCore id)
        (fun fuel => dbl_reachesAt (hmap id cache bools bits) hplain
          (translateFuelFix (translateStep tenv) fuel) (hnosub id cache bools bits fuel) "out")
        (fun e' hU => by
          obtain ⟨dom, rfl⟩ := hunfE id e' hU
          exact LeafDom.dom (dbl_unfold_dom (useDbl_input id cache bools bits))))

/-- **`useDbl` at the OUTERMOST entry (front end off), with no memo
disjunct.** -/
theorem useDbl_output_outer (L : RefLawsM mref cref)
    {dv : DefinitionVal} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {xTy : Lean.Expr} {w0 w1 : Void IO.RealWorld}
    (h0 : L.dval w0 = 0) (hq : L.quiet w0)
    (hci : ∀ (v1 : Void IO.RealWorld) (ci : ConstantInfo) (v2 : Void IO.RealWorld),
      RunsTo (getConstInfo ``useDbl) mctx mref cctx cref v1 ci v2 → ci = .defnInfo dv)
    (htel : LamTelescopeOne)
    (hbody : ∀ body0, Tools.ShippingEntrySoundness.MReturns (openRecordInputs dv.value) body0 →
      ∃ (T b : Lean.Expr) (bi : BinderInfo),
        stripMemoizeWrappers body0 = Lean.Expr.lam `x T b bi ∧ b.isLambda = false ∧
        T.instantiateRevRange 0 0 #[] = xTy ∧
        ∀ id : FVarId, b.instantiateRevRange 0 1 #[Lean.Expr.fvar id] = callE id)
    (hinf : InfersBits xTy 8)
    (hinfT : InfersNoCatch xTy)
    (hres : ∀ id : FVarId, SignalTyped (callE id))
    (hmap : ∀ (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n),
      HasMappedFVar (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hplain : ∀ {tenv : Lean.Environment}, PlainHead tenv ``dbl)
    (hnosub : ∀ {tenv : Lean.Environment} (id : FVarId) (cache : IO.Ref (ExprStructMap String))
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (fuel : Nat),
      NoSubModule (translateFuelFix (translateStep tenv) fuel)
        (setupOf ``useDbl useDblBinders [id] cache bools bits).context (callE id))
    (hunfE : ∀ (xid : FVarId) (e' : Lean.Expr), InlineUnfolds (callE xid) e' →
      ∃ dom : Lean.Expr, e' = dblUnfoldE dom xid)
    (hr : RunsTo (synthesizeCombinationalCoreWith
      (fun env e hint top named => translateExprToWire env e hint top named)
      ``useDbl [] false false) mctx mref cctx cref w0 (m, d) w1) :
    ∃ (id : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Sparkle.IR.Semantics.Env) (mems : Sparkle.IR.Semantics.MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (useDblBinders.zip [id])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl ``useDbl)) →
      Tools.ShippingMixedEntrySoundness.RawValueAt 8 useDblBinders m initial mems
        (bits id 8 + bits id 8).toNat := by
  obtain ⟨b, envR, ci, v1, v2, v3, v4, v5, v6, hget, henv, hrun, hempty⟩ :=
    Tools.ShippingMemo.outer_reset_reaches_with L h0 hq hr
  rw [Tools.ShippingMemo.entryConst_off] at hrun
  rw [hci v1 ci v2 hget] at hrun
  rcases useDbl_output_at L htel hbody hinf hinfT hres hmap hplain hnosub hunfE hrun with
    hit | H
  · rw [hempty] at hit
    rw [Tools.ShippingMemo.get?_empty] at hit
    cases hit
  · exact H

-- The acceptance check: standard axioms only. This one THROWS.
run_cmd Lean.Elab.Command.liftTermElabM do
  let audited : List Name := [
    ``useDbl_output_at, ``useDbl_output_outer,
    ``Tools.ShippingMemo.outer_reset_reaches_with,
    ``Tools.ShippingMemo.entryConst_off,
    ``Tools.ShippingLegacySem.tuple_entry_output_at,
    ``Tools.ShippingLegacySem.tuple_entry_output_miss,
    ``Tools.ShippingLegacySem.tuple_entry_output_outer,
    ``Tools.ShippingLegacySem.one_binder_entry_output_bound_at]
  for n in audited do
    let axs ← Lean.collectAxioms n
    if axs.any fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then
      throwError "{n} depends on a non-standard axiom: {axs}"
  logInfo m!"MEMO BOUNDARY (OUTER), AXIOM AUDIT: {audited} depend on no axiom beyond propext, Classical.choice, Quot.sound (they are stated UNDER the hypothesis RefLawsM, which is not proved against the runtime)"

end Sparkle.Tests.Compiler.LegacySemInstanceTest
