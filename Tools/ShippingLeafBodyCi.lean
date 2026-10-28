import Tools.ShippingLeafKeepCache
import Tools.ShippingChildFrontCP
import Tools.ShippingChildTranslatePathA
import Tools.ShippingLeafCtxQ
import Tools.ShippingSeqChildIface
-- BUILT at the final committed SHA: see REPORT-SR6.md for run names / exits (earlier runs b1,b2 exit 1; b3..b8 exit 0 on intermediate trees).
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # `hbodyK` localised to the real leaf's constant (unit SR6, L8al, part A)

`Tools.ShippingLeafKeepCache` left the body premise `hbodyK`: `synthesizeFromConst … ci isInst` keeps the cache
value for ARBITRARY `tenv`/`ci`/`isInst`. Here the body is the one the entry actually runs,
`getConstInfo declName >>= fun ci => getEnv >>= fun env => synthesizeFromConst … (entryConst … ci …) …`, and
the run facts pin its `ci`/`env`:
* `MachineDefines` (both certified gates refuse `entryConst … ci …`, `machineShape?` of the structure facts of
  the environment the run reads is `shape`) — instantiated at the three reads of THIS run (`getConstInfo`, the
  entry's `getEnv`, and the machine branch's own `getEnv`);
* `MachineCloses` (`synthesizeMachineCertified` of `shape` returns `some _` — the legacy tail is not reached);
* `shape.insts = []` (the machine branch closes no instances: `closeInstsM`/`closeInstsGM`, hence
  `synthesizeChild`, are not reached by the branch itself).
What remains is the translator at the ONE expression `emitLeaves` translates (`LeafTranslatorKeeps`, in the
compiler contexts the binder walk produces, `BoundIn`); it is discharged for a quoted machine body in
`Tools/ShippingLeafTermKeeps.lean`. -/

namespace Tools.ShippingLeafBodyCi
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildCoreC
open Tools.ShippingChildVertA Tools.ShippingChildPathA Tools.ShippingChildTranslateA
open Tools.ShippingChildTranslatePathA Tools.ShippingChildFallbackA Tools.ShippingChildFrontA
open Tools.ShippingChildFrontCP Tools.ShippingChildDepthA Tools.ShippingLeafCtxQ
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingLeafKeepCache
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses Tools.ShippingSeqChildIface Tools.ShippingSeqChildIfaceA Tools.ShippingGateChildComb
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedEntrySoundness

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A triple that also records the run: the start world satisfies `P` and `m` runs from it to the result. -/
theorem tripleWithRun {α : Type} {P : Void IO.RealWorld → Prop} {m : MetaM α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (h : Triple mctx mref cctx cref P m Q R) :
    Triple mctx mref cctx cref P m
      (fun a w' => Q a w' ∧ ∃ w, P w ∧ RunsTo m mctx mref cctx cref w a w') R := by
  intro w hw
  have hh := h w hw
  cases hm : m mctx mref cctx cref w with
  | ok a w' => rw [hm] at hh; exact ⟨hh, w, hw, hm⟩
  | error e w' => rw [hm] at hh; exact hh

/-- A triple from its instances at a single start world. -/
theorem tripleOfPointwise {α : Type} {P : Void IO.RealWorld → Prop} {m : MetaM α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (h : ∀ w, P w → Triple mctx mref cctx cref (fun w' => w' = w) m Q R) :
    Triple mctx mref cctx cref P m Q R := fun w hw => h w hw w rfl

theorem tripleBindPure {α β : Type} {P : Void IO.RealWorld → Prop} {a : α} {f : α → MetaM β}
    {Q : β → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (h : Triple mctx mref cctx cref P (f a) Q R) :
    Triple mctx mref cctx cref P (Pure.pure a >>= f) Q R := by
  first
    | exact h
    | (intro w hw; exact h w hw)

section Walk
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I)
include O hA hS

/-- `emitLeaves` with the translator hypothesis only at the listed leaves (hint = port name, `top = false`,
`named = true`, as `emitLeaves` calls it), in the contexts `P`. -/
theorem emitLeavesQ {P : CompilerState → Prop} (translate : TranslateFn) (b : Bool)
    (r : IO.Ref (Lean.ExprStructMap String)) (hr : MkRefd _ r) :
    ∀ (leaves : List (String × Lean.Expr)) (fw : Option String) (idx : Nat),
      (∀ pn le, (pn, le) ∈ leaves → KeepsCQ mctx mref cctx cref P I (translate le pn false true)) →
      KeepsCQ mctx mref cctx cref P I (emitLeaves translate r (profLogIO b) leaves fw idx)
  | [], fw, idx, _ => by
    unfold emitLeaves
    exact KeepsCQ.pure _
  | (pn, le) :: rest, fw, idx, htr => by
    unfold emitLeaves
    have clock : KeepsCQ mctx mref cctx cref P I (CompilerM.liftMetaM (liftM IO.monoMsNow)) :=
      KeepsCQ.lift (keepsA_framed O hA hS FramedA.monoMs)
    have calls : KeepsCQ mctx mref cctx cref P I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCallCounter)) :=
      KeepsCQ.lift (keepsA_framed O hA hS (FramedA.sideGet .callCounter))
    have hits : KeepsCQ mctx mref cctx cref P I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCacheHits)) :=
      KeepsCQ.lift (keepsA_framed O hA hS (FramedA.sideGet .cacheHits))
    have log : ∀ msg, KeepsCQ mctx mref cctx cref P I
        (CompilerM.liftMetaM (liftM (profLogIO b msg))) :=
      fun msg => KeepsCQ.lift (keepsA_diag O hA hS (Diag.profLog b msg))
    refine KeepsCQ.bind clock ?_; intro t0
    refine KeepsCQ.bind calls ?_; intro c0
    refine KeepsCQ.bind hits ?_; intro h0
    refine KeepsCQ.bind (log _) ?_; intro _
    refine KeepsCQ.bind (htr pn le (List.mem_cons_self ..)) ?_; intro lw
    refine KeepsCQ.bind clock ?_; intro t1
    refine KeepsCQ.bind calls ?_; intro c1
    refine KeepsCQ.bind hits ?_; intro h1
    refine KeepsCQ.bind (log _) ?_; intro _
    dsimp only
    refine KeepsCQ.ite
      (fun _ => KeepsCQ.bind (KeepsCQ.lift
        (keepsA_framed O hA hS (FramedA.exprCacheModify r _ hr))) (fun _ => ?_))
      (fun _ => ?_)
    all_goals
      try dsimp only
      refine KeepsCQ.bind KeepsCQ.get ?_
      intro cs
      try dsimp only
      refine KeepsCQ.ite (fun _ => ?_) (fun _ => ?_)
      · exact KeepsCQ.throwBind _ (by okmsg) _
      · try dsimp only
        refine KeepsCQ.bind (KeepsCQ.ofCP (addOutputP O hA hS _ _)) ?_
        intro _
        refine KeepsCQ.bind (KeepsCQ.ofCP (emitAssignP _ _)) ?_
        intro _
        exact emitLeavesQ translate b r hr rest _ _
          (fun pn' le' hm => htr pn' le' (List.mem_cons_of_mem _ hm))

/-- **`synthesizeMixedCertified` from the translator at THE ONE leaf expression it translates.** The only
call of `translate` is `translate (instFVars ids 0 body) "out" false true`, `ids` the fresh fvars. -/
theorem mixed_keepsLeaf (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (htr : ∀ ids : List FVarId, ids.length = bs.length →
      KeepsCQ mctx mref cctx cref (BoundIn (bs.zip ids)) I
        (translate (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) "out" false true)) :
    Keeps mctx mref cctx cref I
      (synthesizeMixedCertified translate (profLogIO b) declName bs body) := by
  rw [keeps_iff]
  unfold synthesizeMixedCertified
  refine Triple.bind
    (Triple.mapM _ (fun _ => keeps_iff.mp (keepsA_framed O hA hS FramedA.freshFVar)) _) ?_
  intro ids
  split
  · rename_i hids
    dsimp only
    refine Triple.bindQ (φ := MkRefd _) (tripleA_mkExprCache O hA hS _) ?_
    intro cacheRef hr
    have hwalk := bindMixedQ O hA hS
      (emitLeaves translate cacheRef (profLogIO b)
        [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids) []
      (by
        simp only [List.nil_append]
        exact emitLeavesQ O hA hS translate b cacheRef hr _ _ _ (by
          intro pn le hm
          simp only [List.mem_singleton, Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          exact htr ids hids.2))
    refine Triple.bind
      (keeps_iff.mp (hwalk _ _ (ctxOk_entry false hr) (fun p hp => by simp at hp))) ?_
    rintro ⟨_, fs⟩
    exact finishSynthA declName fs
  · exact Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩

/-- **`synthesizeMachineCertified` of a shape WITHOUT calls** (`insts = []`): the mixed harness and the pure
closing; no `synthesizeChild`, so neither `hchild` nor `hsv`. -/
theorem machineCert_keepsLeaf (translate : TranslateFn) (b : Bool) (declName : Name)
    (shape : MachineShape) (hno : shape.insts = [])
    (htr : ∀ ids : List FVarId, ids.length = shape.binders.length →
      KeepsCQ mctx mref cctx cref (BoundIn (shape.binders.zip ids)) I
        (translate (instFVars (ids.map Lean.Expr.fvar).toArray 0 shape.body) "out" false true)) :
    Keeps mctx mref cctx cref I
      (synthesizeMachineCertified translate (profLogIO b) declName shape) := by
  rw [keeps_iff]
  unfold synthesizeMachineCertified
  refine Triple.bind
    (keeps_iff.mp (mixed_keepsLeaf O hA hS translate b declName shape.binders shape.body htr)) ?_
  rintro ⟨t, d⟩
  dsimp only
  split
  · split
    · exact Triple.pure fun _ hw => hw
    · rename_i hi; rw [hno] at hi; exact absurd hi (by simp)
  · exact Triple.pure fun _ hw => hw

/-- The translator at THE leaf expression of a shape (the only expression `emitLeaves` translates in
`synthesizeMixedCertified … shape.binders shape.body`), at every environment and every choice of the fresh
fvars, in the compiler contexts that bind the non-domain binders' fvars (`BoundIn`: that is the context the
binder walk hands to `emitLeaves`). PREMISE of Part A; discharged for a quoted machine body in
`Tools/ShippingLeafTermKeeps.lean` (`leafTranslatorKeeps_of_quote`). -/
def LeafTranslatorKeeps (I : Void IO.RealWorld → Prop) (shape : MachineShape) : Prop :=
  ∀ (tenv : Lean.Environment) (ids : List FVarId), ids.length = shape.binders.length →
    KeepsCQ mctx mref cctx cref (BoundIn (shape.binders.zip ids)) I
      (translateExprToWire tenv (instFVars (ids.map Lean.Expr.fvar).toArray 0 shape.body) "out" false true)

/-- **The body of the entry, for the real leaf's constant.** The run reads `ci` (`getConstInfo declName`) and
the environment `env` (`getEnv`), and hands `synthesizeFromConst` the constant `entryConst … ci …`. The run
facts that pin it are those of `MachineDefines` (both gates refuse it, `machineShape?` of the structure
facts of the environment the run reads is `shape`); `MachineCloses` (`synthesizeMachineCertified` of this
shape does not return `none`, so the legacy tail is not reached); `shape.insts = []` (no calls: the machine
branch closes no instances, so no `synthesizeChild`). What remains is the translator at the leaf expression. -/
theorem leaf_body_triple (declName : Name) (shape : MachineShape) (b : Bool)
    (hno : shape.insts = [])
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (htr : LeafTranslatorKeeps (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) I shape) :
    Triple mctx mref cctx cref I
      (do
        let constInfo ← getConstInfo declName
        let env ← getEnv
        synthesizeFromConst (fun e h t n => translateExprToWire env e h t n) (profLogIO b)
          declName [] false true
          (entryConst true false [] constInfo (instancePredicate env) (userInliner env)
            (structEnv env))
          (instancePredicate env))
      (fun _ => I) (fun e w => I w ∧ OkExc e) := by
  refine Triple.bind (tripleWithRun (keeps_iff.mp (keepsA_framed O hA hS (FramedA.constInfo _)))) ?_
  intro ci
  refine Triple.bind (tripleWithRun (Triple.conseq (keeps_iff.mp (keepsA_framed O hA hS FramedA.env))
    (fun _ h => h.1) (fun _ _ h => h) (fun _ _ h => h))) ?_
  intro env
  refine tripleOfPointwise fun w2 hw2 => ?_
  obtain ⟨hI2, w1, ⟨hI1, w0, hI0, hrun1⟩, hrun2⟩ := hw2
  have hf := entry w0 ci w1 w1 env w2 w1 env w2 hrun1 hrun2 hrun2
  have hd1 : (if true = true then certifiedShape? false []
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env))
      else none) = none := by simpa using hf.1
  have hd2 : (if true = true then mixedCertifiedShape? false []
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env))
      (instancePredicate env) else none) = none := by simpa using hf.2.1
  first | delta synthesizeFromConst | unfold synthesizeFromConst
  rw [hd1, hd2]
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true, List.isEmpty_nil]
  refine Triple.bind (tripleWithRun (Triple.conseq (keeps_iff.mp (keepsA_framed O hA hS FramedA.env))
    (fun w h => by subst h; exact hI2) (fun _ _ h => h) (fun _ _ h => h))) ?_
  intro env'
  refine tripleOfPointwise fun w4 hw4 => ?_
  obtain ⟨hI4, w3, hw3, hrun3⟩ := hw4
  have hsh := (entry w0 ci w1 w1 env w2 w3 env' w4 hrun1 hrun2 hrun3).2.2
  rw [hsh]
  refine tripleBindPure ?_
  dsimp only
  refine Triple.bind (tripleWithRun (Triple.conseq
    (keeps_iff.mp (machineCert_keepsLeaf O hA hS _ b declName shape hno (htr env)))
    (fun w h => by subst h; exact hI4) (fun _ _ h => h) (fun _ _ h => h))) ?_
  intro r
  refine tripleOfPointwise fun w5 hw5 => ?_
  obtain ⟨hI5, w', hw', hrun⟩ := hw5
  have hne := closes (profLogIO b) w' r w5 hrun
  cases r with
  | none => exact absurd rfl hne
  | some result =>
    dsimp only
    refine Triple.conseq (keeps_iff.mp ?_) (fun w h => by subst h; exact hI5) (fun _ _ h => h)
      (fun _ _ h => h)
    refine Keeps.bind (keepsA_diag O hA hS (Diag.profLog b _)) ?_
    intro _
    refine Keeps.bind (keepsA_framed O hA hS (FramedA.sideModify _ .subModule)) ?_
    intro _
    exact Keeps.pure _


end Walk

section Core
variable (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
include O hA

/-- **Nested entry (`D ≠ 0`) keeps the cache value, body premise localised to the real leaf.** Same as
`core_tripleK` with `hbodyK` (arbitrary `ci`/`isInst`) replaced by the facts about THE constant the run reads:
`entry`/`closes`/`hno` and the translator at the leaf expression `htr`. -/
theorem core_tripleKL (D : Nat) (hD : D ≠ 0) (c0 : Std.HashMap Name Res) (declName : Name)
    (shape : MachineShape) (hno : shape.insts = [])
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (htr : LeafTranslatorKeeps (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
      (JK O (D + 1) c0) shape) :
    Triple mctx mref cctx cref (JK O D c0) (synthesizeCombinationalCore declName [] false)
      (fun _ => JK O D c0) (fun e w => JK O D c0 w ∧ OkExc e) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableK O D c0) (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsA_diag O hA (stableK O D c0)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.conseq (tripleA_depthGet O hA (stableK O D c0)) (fun _ h => h)
      (Q' := fun d w => JK O D c0 w ∧ d = D)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.1.1.2.2⟩) (fun _ _ h => h)) ?_
  intro d hd
  subst hd
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr O hA (stableK O d c0) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (JK O (d + 1) c0)
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
          (fun _ => JK O d c0) (fun e w => JK O d c0 w ∧ OkExc e) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := JK O (d + 1) c0) (E := OkExc) ?_
        (finK O hA d c0 m1 m2 m3 m4 m5 m6 m7)
      exact leaf_body_triple O hA (stableK O (d + 1) c0) declName shape prof.isSome hno entry closes htr
    have h0 : ¬ ((d == 0) = true) := by
      intro h; apply hD; simpa using h
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    kget O hA d c0; kget O hA d c0; kget O hA d c0; kget O hA d c0; kget O hA d c0
    kget O hA d c0; kget O hA d c0
    kset O hA d c0; kset O hA d c0; kset O hA d c0; kset O hA d c0; kset O hA d c0
    kset O hA d c0; kset O hA d c0
    refine Triple.bind (tripleK_depthSet O hA d (d + 1) c0) ?_
    intro _
    exact body _ _ _ _ _ _ _

/-- **Outermost entry (`D = 0`), body premise localised to the real leaf.** -/
theorem core_tripleK0L (declName : Name)
    (shape : MachineShape) (hno : shape.insts = [])
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (htr : LeafTranslatorKeeps (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
      (JK O 1 {}) shape) :
    Triple mctx mref cctx cref (JQC O 0) (synthesizeCombinationalCore declName [] false)
      (fun _ => JK O 0 {}) (fun _ _ => True) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keepsT (keepsA_framed O hA (stableA_JQC O 0) (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keepsT (keepsA_diag O hA (stableA_JQC O 0)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = 0)
    (Triple.conseq (tripleA_depthGet O hA (stableA_JQC O 0)) (fun _ h => h)
      (Q' := fun d w => JQC O 0 w ∧ d = 0)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.1.2.2⟩) (fun _ _ _ => trivial)) ?_
  intro d hd
  subst hd
  refine Triple.ite (fun hge => ?_) (fun hlt => ?_)
  · exfalso
    unfold sparkleSynthDepthLimit at hge
    omega
  · have h0 : ((0 : Nat) == 0) = true := rfl
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (JK O (0 + 1) {})
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
              if (0 != 0) = true then do
                  ST.Ref.set sparkleFvarValueMap m1
                  ST.Ref.set sparkleWireWidthCache m2
                  ST.Ref.set sparkleLetWireCache m3
                  ST.Ref.set sparkleLoopWireCache m4
                  ST.Ref.set sparkleWireCanon m5
                  ST.Ref.set sparkleSubInstanceOutputs m6
                  ST.Ref.set sparkleSingleOutInstanceCache m7
                else pure () : MetaM Unit))
          (fun _ => JK O 0 {}) (fun e w => JK O 0 {} w ∧ OkExc e) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := JK O (0 + 1) {}) (E := OkExc) ?_
        (finK O hA 0 {} m1 m2 m3 m4 m5 m6 m7)
      exact leaf_body_triple O hA (stableK O (0 + 1) {}) declName shape prof.isSome hno entry closes htr
    simp only [h0, ↓reduceIte]
    qpure O 0; qpure O 0; qpure O 0; qpure O 0; qpure O 0; qpure O 0; qpure O 0
    qset O hA 0; qset O hA 0; qset O hA 0; qset O hA 0
    refine Triple.bind (Triple.conseq (tripleK_clear O hA 0) (fun _ h => h.1) (fun _ _ h => h)
      (fun _ _ h => h)) ?_
    intro _
    k0set O hA 0; k0set O hA 0; k0set O hA 0; k0set O hA 0; k0set O hA 0; k0set O hA 0
    k0set O hA 0
    refine Triple.bind (tripleK_depthSet O hA 0 (0 + 1) {}) ?_
    intro _
    exact Triple.conseq (body _ _ _ _ _ _ _) (fun _ h => h) (fun _ _ h => h) (fun _ _ _ => trivial)

/-- **(a) `hkeep` at `D ≠ 0` for the real leaf** (premises: `entry`, `closes`, `hno`, `htr` at every start cache). -/
theorem hkeep_nestedL {D : Nat} (hD : D ≠ 0) {n : Name} (shape : MachineShape)
    (hno : shape.insts = [])
    (entry : MachineDefines mctx mref cctx cref n shape)
    (closes : MachineCloses mctx mref cctx cref n shape)
    (htr : ∀ c0 : Std.HashMap Name Res,
      LeafTranslatorKeeps (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        (JK O (D + 1) c0) shape) :
    ∀ w1 r1 w2, JQC O D w1 →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      JQC O D w2 ∧ cv w2 = cv w1 := by
  intro w1 r1 w2 hw1 hrun
  have hT := full_tripleK O hA
    (core_tripleKL O hA D hD (cv w1) n shape hno entry closes (htr (cv w1)))
  exact runs_of_triple hT ⟨hw1, rfl⟩ hrun

/-- **(b) the run at `D = 0` for the real leaf.** -/
theorem hkeep_zeroL {n : Name} (shape : MachineShape)
    (hno : shape.insts = [])
    (entry : MachineDefines mctx mref cctx cref n shape)
    (closes : MachineCloses mctx mref cctx cref n shape)
    (htr : LeafTranslatorKeeps (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
      (JK O 1 {}) shape) :
    ∀ w1 r1 w2, JQC O 0 w1 →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      JQC O 0 w2 ∧ cv w2 = {} := by
  intro w1 r1 w2 hw1 hrun
  have hT := full_tripleK0 O hA (core_tripleK0L O hA n shape hno entry closes htr)
  exact runs_of_triple hT hw1 hrun

end Core

/-! ## Plugged into the leaf-miss consumer -/

/-- **(a) `synthesizeChild_leafMiss_nested` with `hbodyK` replaced by facts about THIS leaf's constant.**
`hbodyK` (arbitrary `tenv`/`ci`/`isInst`) is gone: the body is `synthesizeFromConst` of the constant the run
reads, and what is used about it is `entry : MachineDefines` (the pinned `ci`/`env` reads), `closes`
(`MachineCloses`), `hno : d.shape.insts = []` (no calls), and the translator at the leaf expression `htr`. -/
theorem synthesizeChild_leafMiss_nestedL (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : D ≠ 0) {n : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
    (htr : ∀ c0 : Std.HashMap Name Res,
      LeafTranslatorKeeps (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        (JK O (D + 1) c0) d.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w)) (hmiss : (cv w).get? n = none)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CohWith (cv w) y ∧ CacheCoh (cv w') := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hw1⟩ := jqc_cacheGet O hA hw hget
  have hc1 := cacheGet_cv O hA hw hget
  cases hc : m.get? n with
  | some r' => rw [hm] at hc; rw [hmiss] at hc; cases hc
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hr : RealChildA O n r := RealChildA.of_jqc O hA hw1 hrun
    have hI := seqChild_of_realA O d ok hbody hno outTy entry closes hr
    obtain ⟨hw2, hk2⟩ := hkeep_nestedL O hA hD d.shape hno entry (closes mctx cctx) htr w1 r w2 hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    have hc3 := (O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw2.1.1 hmod).1
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    rw [hc3, hk2, hc1]
    exact leafMiss_cacheCoh hcl hk hmiss hI.name hI.design

/-- **(b) `synthesizeChild` leaf miss at `D = 0`, `hbodyK` replaced by facts about THIS leaf's constant.** -/
theorem synthesizeChild_leafMiss_zeroL (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {n : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
    (htr : LeafTranslatorKeeps (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
      (JK O 1 {}) d.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w) (hmiss : (cv w).get? n = none)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    cv w' = ({} : Std.HashMap Name Res).insert n y ∧ CacheClosed (cv w') ∧ KeyTop (cv w') ∧
      CohWith ({} : Std.HashMap Name Res) y ∧ CacheCoh (cv w') := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hw1⟩ := jqc_cacheGet O hA hw hget
  cases hc : m.get? n with
  | some r' => rw [hm] at hc; rw [hmiss] at hc; cases hc
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hr : RealChildA O n r := RealChildA.of_jqc O hA hw1 hrun
    have hI := seqChild_of_realA O d ok hbody hno outTy entry closes hr
    obtain ⟨hw2, hk2⟩ := hkeep_zeroL O hA d.shape hno entry (closes mctx cctx) htr w1 r w2 hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    have hc3 := (O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw2.1.1 hmod).1
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    rw [hc3, hk2]
    have hmiss0 : ({} : Std.HashMap Name Res).get? n = none := by simp
    obtain ⟨a, b, c, e⟩ := leafMiss_cacheCoh cacheClosed_empty keyTop_empty hmiss0 hI.name hI.design
    exact ⟨rfl, a, b, c, e⟩

end Tools.ShippingLeafBodyCi

#print axioms Tools.ShippingLeafBodyCi.leaf_body_triple
#print axioms Tools.ShippingLeafBodyCi.core_tripleKL
#print axioms Tools.ShippingLeafBodyCi.core_tripleK0L
#print axioms Tools.ShippingLeafBodyCi.hkeep_nestedL
#print axioms Tools.ShippingLeafBodyCi.hkeep_zeroL
#print axioms Tools.ShippingLeafBodyCi.synthesizeChild_leafMiss_nestedL
#print axioms Tools.ShippingLeafBodyCi.synthesizeChild_leafMiss_zeroL
