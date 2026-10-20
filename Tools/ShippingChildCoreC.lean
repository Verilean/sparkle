import Tools.ShippingChildCacheA
import Tools.ShippingChildVertA
-- UNBUILT (worker par/ca, base d39a62f4). Isolated: no existing file uses it (only the audit
-- Tests/Compiler/ChildVertAuditTest.lean imports it).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / boundary field. Law witness:
-- `O : RefLawsAOps Fresh mref cref` at `hA : AdmCtx O.quiet mctx cctx` only (no old law bundle,
-- no old-to-new conversion, no telescope laws; no old `RealChild`/`CacheInv`/`InvW`/`J L D`).
-- Reused law-free lemmas: `Triple.bind`/`bindQ`/`conseq`/`ite`/`pure`/`tryFinally`, `keeps_iff`
-- (ShippingChildKeeps.lean); `tripleA_depthGet`, `tripleA_throwErr`, `keepsA_framed`,
-- `keepsA_diag` (ShippingChildVCA.lean, stated for any stable invariant).
-- THE ONLY PREMISE of `core_tripleAC`: `hbodyC` — below the depth limit, the body
-- `synthesizeFromConst …` keeps `JQC O (D + 1)` (the analogue of `core_tripleA`'s `hbody`, with
-- the cache half, and asked only below the limit as in the built `core_keeps`). NOT proved here.
-- The walk copies the BUILT `core_keeps` (ShippingChildKeeps.lean:385, both branches) and `finA`
-- (ShippingChildVertA.lean), with `J L D` / `JQ` replaced by `JQC O D` and every
-- `Triple.frame L X D` by `keepsA_framed O hA (stableA_JQC O D) X`.
-- Writing-time guesses (marked `-- guess: Kn` below):
--  K1 the macros `cset`/`cget`/`cpure` (copies of `aset`/`apure` of ShippingChildVertA and `tget`
--     of ShippingChildKeeps) elaborate with `stableA_JQC`;
--  K2 `subst hd` with `hd : d = D` eliminates `D` (as in `core_keeps`), so `hbodyC` is at `d`;
--  K3 in the nested branch `simp only [h0, Bool.false_eq_true, ↓reduceIte]` leaves the seven
--     reads `ST.Ref.get sparkle…` (as in `core_keeps`), each a `FramedA.sideGet`;
--  K4 `exact body _ _ _ _ _ _ _` lets the seven saved maps unify (never forced to `{}`);
--  K5 `(@hbodyC c)` keeps the implicit `{tenv}` binder un-instantiated.

/-! # The core entry keeps the cache half, at every depth

`core_tripleAC`: from `JQC O D`, the core entry
`synthesizeCombinationalCore declName [] false` ends in `JQC O D` on EVERY
outcome, exceptions in the class, at any depth `D`:
* at the limit the entry throws before changing anything (`O.frameT`/`O.excOk`);
* outermost (`D = 0`): 7 pures, 4 framed sets, the cache clear
  (`tripleC_clear'`: the cache half re-established from `{}`), 7 framed sets;
* nested (`D ≠ 0`): 7 framed reads (the saved maps), 7 framed sets, NO clear
  (the cache half is carried);
* then the depth bump to `D + 1` (`tripleC_depthSet`), the body under
  `hbodyC`, and the `finally` (`finC`: depth back to `D` by
  `tripleC_depthModify`, the nested restore is seven framed sets).

`full_tripleAC`: the same for `synthesizeCombinational` (core, one env read,
pure post-processing). `hentryT_of_body` / `hentry_of_body` derive the
premises `hentryT` / `hentry` of Tools/ShippingChildCacheA.lean from
`hbodyC`; `synthesizeChild_realA'`, `synthesizeChild_tripleC'` and
`closeInstsM_realA'` restate the cache endpoints with `hbodyC` in place of
them. -/

namespace Tools.ShippingChildCoreC
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {Fresh : (σ : Type) → IO.Ref σ → Prop}

/-- A set of another per-synthesis ref under `JQC` (a `FramedA.sideSet`). -/
macro "cset " O:term:max hA:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableA_JQC $O $D)
      (FramedA.sideSet _ ?s))) ?_
   case s => constructor
   intro _))  -- guess: K1
/-- A read of another per-synthesis ref under `JQC` (a `FramedA.sideGet`). -/
macro "cget " O:term:max hA:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableA_JQC $O $D)
      (FramedA.sideGet ?s))) ?_
   case s => constructor
   intro _))
/-- A `pure` under `JQC`. -/
macro "cpure " O:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.pure (Q := fun _ => JQC $O $D) (fun w hw => hw)) ?_; intro _))

/-- The `finally` of the entry under `JQC`: from depth `d + 1` back to `d`;
the nested-restore branch (if taken) is seven framed sets. -/
theorem finC (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx) (d : Nat)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (JQC O (d + 1))
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
      (fun _ => JQC O d) (EQC O d) := by
  refine Triple.bind (Triple.conseq (tripleC_depthModify O hA (d + 1) (fun x => x - 1))
    (fun _ h => h) (Q' := fun _ => JQC O d)
    (fun _ w h => by show JQC O d w; have h' : JQC O (d + 1 - 1) w := h
                     rw [Nat.add_sub_cancel] at h'; exact h')
    (fun _ _ h => h)) ?_
  intro _
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d
  exact keeps_iff.mp (keepsA_framed O hA (stableA_JQC O d) (FramedA.sideSet _ .singleOut))

/-- **The core entry keeps `JQC` at every depth, on every outcome.** The only
premise: `hbodyC`, the body keeps `JQC O (D + 1)` below the depth limit. -/
theorem core_tripleAC (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (declName : Name)
    (hbodyC : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQC O D) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQC O D) (EQC O D) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O D) (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsA_diag O hA (stableA_JQC O D)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.conseq (tripleA_depthGet O hA (stableA_JQC O D)) (fun _ h => h)
      (Q' := fun d w => JQC O D w ∧ d = D)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.1.2.2⟩) (fun _ _ h => h)) ?_
  intro d hd
  subst hd  -- guess: K2
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · -- at the limit: the entry throws before touching the depth
    refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr O hA (stableA_JQC O d) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : d < sparkleSynthDepthLimit := Nat.lt_of_not_ge hlt
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (JQC O (d + 1))
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
          (fun _ => JQC O d) (EQC O d) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := JQC O (d + 1)) (E := OkExc) ?_
        (finC O hA d m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
        (FramedA.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
        FramedA.env)) ?_
      intro env
      exact keeps_iff.mp (hbodyC hlt prof.isSome _ _)
    by_cases h0 : (d == 0) = true
    · -- outermost: the cache is cleared, the cache half re-established
      simp only [h0, ↓reduceIte]
      cpure O d; cpure O d; cpure O d; cpure O d; cpure O d; cpure O d; cpure O d
      cset O hA d; cset O hA d; cset O hA d; cset O hA d
      refine Triple.bind (tripleC_clear' O hA d) ?_
      intro _
      cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d
      refine Triple.bind (tripleC_depthSet O hA d (d + 1)) ?_
      intro _
      exact body _ _ _ _ _ _ _  -- guess: K4
    · -- nested: the parent's maps are read (and restored in the `finally`), no clear
      simp only [h0, Bool.false_eq_true, ↓reduceIte]  -- guess: K3
      cget O hA d; cget O hA d; cget O hA d; cget O hA d; cget O hA d; cget O hA d; cget O hA d
      cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d; cset O hA d
      refine Triple.bind (tripleC_depthSet O hA d (d + 1)) ?_
      intro _
      exact body _ _ _ _ _ _ _

/-- The full entry: the core, then one environment-variable read and pure
post-processing. -/
theorem full_tripleAC (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {declName : Name}
    (hcore : Triple mctx mref cctx cref (JQC O D) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQC O D) (EQC O D)) :
    Triple mctx mref cctx cref (JQC O D) (synthesizeCombinational declName)
      (fun _ => JQC O D) (EQC O D) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind hcore ?_
  rintro ⟨m, dd⟩
  dsimp only
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O D) (FramedA.ioEnv _))) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-! ## The cache endpoints with `hbodyC` in place of `hentry` -/

/-- `hentryT` of ShippingChildCacheA from `hbodyC`. -/
theorem hentryT_of_body (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {c : Name}
    (hbodyC : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQC O D) (synthesizeCombinational c)
      (fun _ => JQC O D) (EQC O D) :=
  full_tripleAC O hA (core_tripleAC O hA D c @hbodyC)  -- guess: K5

/-- `hentry` of ShippingChildCacheA from `hbodyC`. -/
theorem hentry_of_body (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {c : Name}
    (hbodyC : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst)) :
    ∀ w1 r1 w2, JQC O D w1 →
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w1 r1 w2 → JQC O D w2 :=
  fun _ _ _ hw h => runs_of_triple (hentryT_of_body O hA @hbodyC) hw h

/-- **`synthesizeChild` under `JQC`, cache hit included, from `hbodyC`.** -/
theorem synthesizeChild_realA' (O : RefLawsAOps Fresh mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} {n : Name}
    (hbodyC : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          n [] false true ci isInst))
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    RealChildA O n y ∧ JQC O D w' :=
  synthesizeChild_realA O hA (hentry_of_body O hA @hbodyC) hw h

/-- `synthesizeChild_tripleC` from `hbodyC`. -/
theorem synthesizeChild_tripleC' (O : RefLawsAOps Fresh mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} {n : Name}
    (hbodyC : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          n [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQC O D) (synthesizeChild n)
      (fun r w => RealChildA O n r ∧ JQC O D w) (EQC O D) :=
  synthesizeChild_tripleC O hA (hentryT_of_body O hA @hbodyC)

/-- **The one-output closing's children, cache hits included, from
`hbodyC`** (for every callee). -/
theorem closeInstsM_realA' (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat}
    (hbodyC : ∀ (c : Name) {tenv : Lean.Environment}, D < sparkleSynthDepthLimit →
      ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQC O (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst))
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : JQC O D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        RealChildA O (shape.insts[k]).1 y) ∧
      JQC O D w' :=
  closeInstsM_realA O hA (fun c => hentry_of_body O hA (@hbodyC c)) hw hr

end Tools.ShippingChildCoreC
