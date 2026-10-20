import Tools.ShippingChildVCA
-- BUILT by the integrator: vt1 ran out of memory (stopped: `exact (body {} … {})` forced the saved maps), vt2 exit 1 (`CircuitM.init` → `Sparkle.IR.Builder.CircuitM.init`), vt3 exit 0 (317 jobs) (round par/vert, base 777630e9). Isolated: no existing file uses it.
-- No `sorry`, no `axiom`, no `native_decide`, no new law. Law witness: `O : RefLawsAOps MkRefd mref cref`
-- only (no `RefLaws`, no `RefLawsCore`, no `RefLawsCore.toAOps`/`toA`, no `RefLawsATele`).
-- Writing-time guesses:
--  W1 the prefix walk copies `core_triple0` (ShippingChildBalance.lean, built bl1): `unfold` +
--     `simp only [Bool.false_eq_true, ↓reduceIte]`, the `d`-kept guard, `simp only [h0, ↓reduceIte]`
--     with `h0 : (d == 0) = true`, then 7 pures, 4 sets, clear, 7 sets, the depth bump;
--  W2 `Triple.conseq (P := JQ O.quiet 0) …` with `fun _ h => h` accepts `OutQ`/`JQ … 0` by defeq;
--  W3 in `body`, `subst hd` then `exact keeps_iff.mp (hbody _ _ _)` accepts `JQ q (0 + 1)` for
--     `JQ q 1` (Nat literal defeq); fallback `simpa using`;
--  W4 `fin`: `tripleJ_depthModify` concludes `JQ q ((fun x => x - 1) (d + 1))`; the `conseq`
--     closes it with `Nat.add_sub_cancel` after `show`;
--  W5 `certified_keepsA`: after `unfold synthesizeCertified`, `Keeps.bind`/`Keeps.mapM`/`Keeps.dite`
--     unify against the do-block; in the then-branch `show … (IO.mkRef {} >>= fun r => certRest …)`
--     is accepted by defeq (zeta of `innerBody`; the `let (_, s) ← …` matcher of
--     `synthesizeCertified` vs of `certRest` — both unfold to the same `match`);
--  W6 `OkExc (Exception.error .missing "fresh …")`: `OkMsg.str _` after `show`, fallback `.fmt _`.

/-! # Vertical migration: ONE real entry path under the admissible boundary

Witness: `O : RefLawsAOps MkRefd mref cref` (the restricted operations laws,
with `Fresh := MkRefd`, Tools/ShippingChildFresh.lean) and `hA : AdmCtx
O.quiet mctx cctx`. No old law bundle is used (audit:
Tests/Compiler/ChildVertAuditTest.lean).

Proved:
* `core_tripleA`: the CORE entry `synthesizeCombinationalCore declName [] false`
  — the one the `<p>_designClosedB` / `<p>_sat` theorems run — from
  `OutQ O.quiet` ends, on EVERY outcome, in `OutQ O.quiet`, exceptions in the
  class: profile read, profile log (`O.diag`), depth read, depth guard
  (`O.frameT`/`O.excOk`), the saved maps, 4 resets, the cache clear
  (`O.cacheSet`), 7 resets, the bump to 1 (`O.depthSet`), the body at
  depth 1, and the `finally` (`O.depthModify'`, back to 0).
  PREMISE (not migrated): `hbody` — the body `synthesizeFromConst …` keeps
  `JQ O.quiet 1` (the analogue of the old `bodyRel`; under the new boundary
  it is NOT proved).
* `certified_keepsA`: the certified sub-path `synthesizeCertified` (reached
  from `synthesizeFromConst`'s certified branch, Elab.lean:5296) keeps any
  stable invariant through `mkFreshFVarId`s, the distinctness branch and the
  `IO.mkRef` of the translation cache, and hands the rest a cache ref WITH
  PROVENANCE (`MkRefd`). PREMISE (not migrated): `hrest` — the translation
  run and `finishSynth` keep the invariant FOR refs with `MkRefd` (its own
  ref accesses are `FramedA MkRefd` steps, e.g. `keepsA_exprCacheGet`).
  The connection `synthesizeFromConst → synthesizeCertified` (so that
  `certified_keepsA` discharges part of `hbody`) is OPEN. -/

namespace Tools.ShippingChildVertA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A set of another per-synthesis ref under `JQ` (a `FramedA.sideSet`). -/
macro "aset " O:term:max hA:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableA_JQ _ $D)
      (FramedA.sideSet _ ?s))) ?_
   case s => constructor
   intro _))
/-- A `pure` under `JQ`. -/
macro "apure " q:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.pure (Q := fun _ => JQ $q $D) (fun w hw => hw)) ?_; intro _))

/-- The `finally` of an outermost run: from depth `d + 1` back to `d`; the
nested-restore branch (if taken) is seven framed sets. -/
theorem finA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) (d : Nat)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (JQ O.quiet (d + 1))
      (do
        ST.Ref.modify sparkleSynthDepth fun x => x - 1
        if (d != 0) = true then do
            ST.Ref.set sparkleFvarValueMap m1
            ST.Ref.set sparkleWireWidthCache m2
            ST.Ref.set sparkleLetWireCache m3
            ST.Ref.set sparkleLoopWireCache m4
            ST.Ref.set sparkleWireCanon m5
            ST.Ref.set sparkleSubInstanceOutputs m6
            ST.Ref.set sparkleSingleOutInstanceCache m7
          else pure () : MetaM Unit)
      (fun _ => JQ O.quiet d) (EQ O.quiet d) := by
  refine Triple.bind (Triple.conseq (tripleJ_depthModify O hA (d + 1) (fun x => x - 1))
    (fun _ h => h) (Q' := fun _ => JQ O.quiet d)
    (fun _ w h => by show JQ O.quiet d w; have h' : JQ O.quiet (d + 1 - 1) w := h  -- guess: W4
                     rw [Nat.add_sub_cancel] at h'; exact h')
    (fun _ _ h => h)) ?_
  intro _
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  aset O hA d; aset O hA d; aset O hA d; aset O hA d; aset O hA d; aset O hA d
  exact keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ d) (FramedA.sideSet _ .singleOut))

/-- **The core entry under the admissible boundary, from an outermost
world, on every outcome.** Laws: `O` (with provenance `MkRefd`) at the
admissible context `hA`. Premise `hbody`: the body keeps `JQ O.quiet 1`
(NOT migrated). -/
theorem core_tripleA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (declName : Name)
    (hbody : ∀ {tenv : Lean.Environment} (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQ O.quiet 1)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Triple mctx mref cctx cref (OutQ O.quiet) (synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e) := by
  refine Triple.conseq (P := JQ O.quiet 0) (Q := fun _ => JQ O.quiet 0) (R := EQ O.quiet 0) ?_
    (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h)  -- guess: W2
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]  -- guess: W1
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ 0) (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsA_diag O hA (stableA_JQ _ 0)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = 0)
    (Triple.conseq (tripleA_depthGet O hA (stableA_JQ _ 0)) (fun _ h => h)
      (Q' := fun d w => JQ O.quiet 0 w ∧ d = 0)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.2.2⟩) (fun _ _ h => h)) ?_
  intro d hd
  have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
      (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
      (m7 : Std.HashMap String String),
      Triple mctx mref cctx cref (JQ O.quiet (d + 1))
        (_root_.tryFinally
          (do
            let constInfo ← getConstInfo declName
            let env ← getEnv
            synthesizeFromConst (fun e h t n => translateExprToWire env e h t n)
              (profLogIO prof.isSome) declName [] false true
              (entryConst true false [] constInfo (instancePredicate env) (userInliner env)
                (structEnv env))
              (instancePredicate env))
          (do
            ST.Ref.modify sparkleSynthDepth fun x => x - 1
            if (d != 0) = true then do
                ST.Ref.set sparkleFvarValueMap m1
                ST.Ref.set sparkleWireWidthCache m2
                ST.Ref.set sparkleLetWireCache m3
                ST.Ref.set sparkleLoopWireCache m4
                ST.Ref.set sparkleWireCanon m5
                ST.Ref.set sparkleSubInstanceOutputs m6
                ST.Ref.set sparkleSingleOutInstanceCache m7
              else pure () : MetaM Unit))
        (fun _ => JQ O.quiet d) (EQ O.quiet d) := by
    intro m1 m2 m3 m4 m5 m6 m7
    refine Triple.tryFinally (M := JQ O.quiet (d + 1)) (E := OkExc) ?_
      (finA O hA d m1 m2 m3 m4 m5 m6 m7)
    refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ (d + 1))
      (FramedA.constInfo _))) ?_
    intro ci
    refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ (d + 1)) FramedA.env)) ?_
    intro env
    subst hd
    -- (writing-time guess W3: `JQ q (0 + 1)` vs `JQ q 1`)
    first
      | exact keeps_iff.mp (hbody prof.isSome _ _)
      | exact keeps_iff.mp (hbody (tenv := env) prof.isSome _ _)
  refine Triple.ite (fun _ => ?_) (fun _ => ?_)
  · -- at the limit: the entry throws before touching the depth
    refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr O hA (stableA_JQ _ 0) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have h0 : (d == 0) = true := by subst hd; first | rfl | decide | simp
    simp only [h0, ↓reduceIte]
    apure O.quiet 0; apure O.quiet 0; apure O.quiet 0; apure O.quiet 0; apure O.quiet 0
    apure O.quiet 0; apure O.quiet 0
    aset O hA 0; aset O hA 0; aset O hA 0; aset O hA 0
    refine Triple.bind (tripleJ_clear O hA 0) ?_
    intro _
    aset O hA 0; aset O hA 0; aset O hA 0; aset O hA 0; aset O hA 0; aset O hA 0; aset O hA 0
    refine Triple.bind (tripleJ_depthSet O hA 0 (d + 1)) ?_
    intro _
    -- `body` ends in `JQ q d`, `d = 0`
    -- (integrator, after vt1 ran out of memory: let the seven saved maps unify, as `core_triple0`
    -- does; forcing them to `{}` started an expensive definitional search)
    subst hd
    exact body _ _ _ _ _ _ _

/-! ## The `IO.mkRef` sub-path: `synthesizeCertified` -/

/-- What `synthesizeCertified` runs after allocating its translation cache
`r` (copied from Sparkle/Compiler/Elab.lean:2941-2946, `innerBody` inlined). -/
def certRest (translate : TranslateFn) (logProf : String → IO Unit) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr) (ids : List FVarId)
    (r : IO.Ref (Lean.ExprStructMap String)) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let compiler := bindCertifiedInputs
    (emitLeaves translate r logProf [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)]
      none 0) (bs.zip ids)
  let (_, finalCircuitState) ←
    (compiler.run (entryCompilerState false r)).run
      (Sparkle.IR.Builder.CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName))
  finishSynth declName [] false finalCircuitState

/-- **The certified sub-path threads provenance.** Under `O` at an admissible
context, for a stable invariant: if the rest keeps it FOR every cache ref
with `MkRefd` (premise `hrest`, not migrated), the whole `synthesizeCertified`
keeps it. The allocation is `FramedA.mkExprCache`; the provenance of the
allocated ref comes from the run (`tripleA_mkExprCache`), not from a
`Fresh := True`. -/
theorem certified_keepsA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
    (translate : TranslateFn) (logProf : String → IO Unit) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (hrest : ∀ (ids : List FVarId) (r : IO.Ref (Lean.ExprStructMap String)), MkRefd _ r →
      Keeps mctx mref cctx cref I (certRest translate logProf declName bs body ids r)) :
    Keeps mctx mref cctx cref I (synthesizeCertified translate logProf declName bs body) := by
  unfold synthesizeCertified
  refine Keeps.bind (Keeps.mapM _ (fun _ => keepsA_framed O hA hS FramedA.freshFVar) _) ?_
  intro ids
  refine Keeps.dite (fun _ => ?_) (fun _ => Keeps.throw _ ?_)
  · -- (writing-time guess W5)
    show Keeps mctx mref cctx cref I
      ((IO.mkRef ({} : Lean.ExprStructMap String) : MetaM (IO.Ref (Lean.ExprStructMap String)))
        >>= fun r => certRest translate logProf declName bs body ids r)
    exact keepsA_mkExprCache_bind O hA hS {} (fun r hr => hrest ids r hr)
  · -- (writing-time guess W6)
    first
      | exact OkMsg.str _
      | (unfold OkExc; exact OkMsg.str _)
      | (show OkMsg (stringToMessageData _); exact OkMsg.str _)
      | exact OkMsg.fmt _

end Tools.ShippingChildVertA
