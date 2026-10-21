import Tools.ShippingChildComposeC
-- UNBUILT (unit CN2): see REPORT-CN2.md for the build runs.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Law witness: `O`, `hA`, `T` as in
-- `Tools.ShippingChildComposeC` (the SAME assumptions as `bodyStepC_of_tele`; nothing is added).

/-! # The cache-entry pin through the depth induction (unit CN2, step 2)

`JQP O D L := JQC O D ∧ pinL L`, where `pinL L w` says: for every `(c, y) ∈ L` the world's cache
value maps `c ↦ y`. `JQP` is `StableA` (the pin depends on the world only through `cv`).

PROVED here (copies of the CoreC / DepthC / ComposeC walks at `I := JQP O D L`, `D ≥ 1`):
* `core_tripleAP`, `full_tripleAP`: nested core entry keeps `JQP` (no cache clear: that happens only at
  depth 0, which is excluded by `1 ≤ D`; the cache writes of the entry are the child insert only);
* `synthesizeChild_tripleP`: `synthesizeChild n` from `JQP O D L` returns a `RealChildA`, ends in `JQP O D L`
  and leaves `(cv w).get? n = some r`. A hit changes nothing; a miss inserts under a key that is
  ABSENT at the read, hence different from every pinned key (`pinL` at the read);
* `childKeepsP_all_of_tele`, `synthesizeChild_pinned`: the depth induction at `JQP` (from `T`).
This is a SEPARATE induction from `childKeepsC_all` (copy, not a modification of unit D/E files).
Not shown: runtime fit of the laws. -/

namespace Tools.ShippingChildPinC
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFrontCP
open Tools.ShippingChildFresh
open Tools.ShippingChildCacheA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildDepthC
open Tools.ShippingChildCoreC
open Tools.ShippingChildComposeC

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The pin: every `(c, y)` of `L` is an entry of the world's cache value. -/
def pinL (L : List (Name × Res)) (w : Void IO.RealWorld) : Prop :=
  ∀ p ∈ L, (cv w).get? p.1 = some p.2

/-- `JQC` together with the pin. -/
def JQP (O : RefLawsAOps MkRefd mref cref) (D : Nat) (L : List (Name × Res))
    (w : Void IO.RealWorld) : Prop :=
  JQC O D w ∧ pinL L w

/-- `JQP` with the thrown exception in the class. -/
def EQP (O : RefLawsAOps MkRefd mref cref) (D : Nat) (L : List (Name × Res)) :
    Exception → Void IO.RealWorld → Prop :=
  fun e w => JQP O D L w ∧ OkExc e

theorem stableA_JQP (O : RefLawsAOps MkRefd mref cref) (D : Nat) (L : List (Name × Res)) :
    StableA O.quiet (JQP O D L) :=
  ⟨fun _ h => h.1.1.1, fun w w' hc hs hd hq h =>
    ⟨(stableA_JQC O D).2 w w' hc hs hd hq h.1, fun p hp => by rw [hc]; exact h.2 p hp⟩⟩

/-- A set of another per-synthesis ref under `JQP`. -/
macro "psset " O:term:max hA:term:max D:term:max L:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableA_JQP $O $D $L)
      (FramedA.sideSet _ ?s))) ?_
   case s => constructor
   intro _))
/-- A read of another per-synthesis ref under `JQP`. -/
macro "psget " O:term:max hA:term:max D:term:max L:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableA_JQP $O $D $L)
      (FramedA.sideGet ?s))) ?_
   case s => constructor
   intro _))

/-- The depth set keeps the pin (`cv` is unchanged: `O.depthSet`). -/
theorem tripleP_depthSet (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D v : Nat) (L : List (Name × Res)) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQP O D L) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => JQP O v L) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.depthSet hA _ _ _ _ h hw.1.1.1
    refine ⟨⟨⟨O.depthSetQ hA _ _ _ _ h hw.1.1.1, hk.2.1.trans hw.1.1.2.1, hk.2.2⟩, ?_⟩, ?_⟩
    · rw [hk.1]; exact hw.1.2
    · intro p hp; rw [hk.1]; exact hw.2 p hp

/-- The depth modify keeps the pin (`O.depthModify'`: `cv` unchanged). -/
theorem tripleP_depthModify (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (f : Nat → Nat) (L : List (Name × Res))
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQP O D L) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => JQP O (f D) L) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw h => by
    have hk := O.depthModify' hA f hw.1.1.1 h
    have hq' : O.quiet w' := by
      obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
      have hq1 := O.frameQ hA _ FramedA.depthGet w hw.1.1.1
      rw [endW_of_runs hg] at hq1
      exact O.depthSetQ hA _ _ _ _ hs hq1
    refine ⟨⟨⟨hq', hk.2.1.trans hw.1.1.2.1, ?_⟩, ?_⟩, ?_⟩
    · rw [hk.2.2, hw.1.1.2.2]
    · rw [hk.1]; exact hw.1.2
    · intro p hp; rw [hk.1]; exact hw.2 p hp

/-- The `finally` of the entry under `JQP`. -/
theorem finP (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) (d : Nat)
    (L : List (Name × Res))
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (JQP O (d + 1) L)
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
      (fun _ => JQP O d L) (EQP O d L) := by
  refine Triple.bind (Triple.conseq (tripleP_depthModify O hA (d + 1) (fun x => x - 1) L)
    (fun _ h => h) (Q' := fun _ => JQP O d L)
    (fun _ w h => by show JQP O d L w; have h' : JQP O (d + 1 - 1) L w := h
                     rw [Nat.add_sub_cancel] at h'; exact h')
    (fun _ _ h => h)) ?_
  intro _
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  psset O hA d L; psset O hA d L; psset O hA d L; psset O hA d L; psset O hA d L; psset O hA d L
  exact keeps_iff.mp (keepsA_framed O hA (stableA_JQP O d L) (FramedA.sideSet _ .singleOut))

/-- **The nested core entry keeps `JQP` (depth `D ≥ 1`, no clear), on every outcome.** -/
theorem core_tripleAP (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (hD : 1 ≤ D) (L : List (Name × Res)) (declName : Name)
    (hbodyP : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQP O (D + 1) L)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQP O D L) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQP O D L) (EQP O D L) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQP O D L) (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsA_diag O hA (stableA_JQP O D L)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.conseq (tripleA_depthGet O hA (stableA_JQP O D L)) (fun _ h => h)
      (Q' := fun d w => JQP O D L w ∧ d = D)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.1.1.2.2⟩) (fun _ _ h => h)) ?_
  intro d hd
  subst hd
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr O hA (stableA_JQP O d L) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : d < sparkleSynthDepthLimit := Nat.lt_of_not_ge hlt
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (JQP O (d + 1) L)
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
          (fun _ => JQP O d L) (EQP O d L) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := JQP O (d + 1) L) (E := OkExc) ?_
        (finP O hA d L m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQP O (d + 1) L)
        (FramedA.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQP O (d + 1) L)
        FramedA.env)) ?_
      intro env
      exact keeps_iff.mp (hbodyP hlt prof.isSome _ _)
    have h0 : ¬ ((d == 0) = true) := by
      intro h; simp at h; omega
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    psget O hA d L; psget O hA d L; psget O hA d L; psget O hA d L; psget O hA d L
    psget O hA d L; psget O hA d L
    psset O hA d L; psset O hA d L; psset O hA d L; psset O hA d L; psset O hA d L
    psset O hA d L; psset O hA d L
    refine Triple.bind (tripleP_depthSet O hA d (d + 1) L) ?_
    intro _
    exact body _ _ _ _ _ _ _

/-- The full nested entry: the core, one environment read, pure post-processing. -/
theorem full_tripleAP (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {L : List (Name × Res)} {declName : Name}
    (hcore : Triple mctx mref cctx cref (JQP O D L)
      (synthesizeCombinationalCore declName [] false) (fun _ => JQP O D L) (EQP O D L)) :
    Triple mctx mref cctx cref (JQP O D L) (synthesizeCombinational declName)
      (fun _ => JQP O D L) (EQP O D L) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind hcore ?_
  rintro ⟨m, dd⟩
  dsimp only
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQP O D L) (FramedA.ioEnv _))) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-- The cache read under `JQP`: the value read is the world's cache value. -/
theorem tripleP_cacheGet (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (L : List (Name × Res)) :
    Triple mctx mref cctx cref (JQP O D L) (sparkleChildCache.get : MetaM _)
      (fun m w => JQP O D L w ∧ m = cv w) (EQP O D L) := by
  intro w hw
  have hK := keeps_iff.mp (keepsA_framed O hA (stableA_JQP O D L) FramedA.cacheGet) w hw
  cases hm : (sparkleChildCache.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    rw [hm] at hK
    have hk := O.frame hA _ FramedA.cacheGet w hw.1.1.1
    rw [endW_of_runs hm] at hk
    exact ⟨hK, (runsTo_get_readOf _ hm).trans hk.1.symm⟩
  | error e w1 => rw [hm] at hK; exact hK

/-- **The child insert keeps `JQP`** when the key is none of the pinned keys, and records the entry. -/
theorem jqp_insert_runs (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {L : List (Name × Res)} {n : Name} {r : Res} {w : Void IO.RealWorld} {u : Unit}
    {w' : Void IO.RealWorld} (hw : JQP O D L w) (hr : RealChildA O n r)
    (hn : ∀ p ∈ L, p.1 ≠ n)
    (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert n r) :
      MetaM Unit) mctx mref cctx cref w u w') :
    JQP O D L w' ∧ (cv w').get? n = some r := by
  have hk := O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw.1.1.1 h
  have hjq := jqc_insert_runs O hA hw.1 hr h
  have hcv : cv w' = (cv w).insert n r := hk.1
  refine ⟨⟨hjq, fun p hp => ?_⟩, ?_⟩
  · have hne : ¬ (n == p.1) = true := fun h' => hn p hp (beq_iff_eq.mp h').symm
    rw [hcv, Std.HashMap.get?_insert, if_neg hne]
    exact hw.2 p hp
  · rw [hcv, Std.HashMap.get?_insert, if_pos (by simp)]

/-- **`synthesizeChild` under `JQP`, on every outcome**: a returned value is a `RealChildA`, the
end world is `JQP` (the pin is kept) and the cache holds the returned value for `n`. -/
theorem synthesizeChild_tripleP (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} {L : List (Name × Res)} {n : Name}
    (hentryT : Triple mctx mref cctx cref (JQP O D L) (synthesizeCombinational n)
      (fun _ => JQP O D L) (EQP O D L)) :
    Triple mctx mref cctx cref (JQP O D L) (synthesizeChild n)
      (fun r w => RealChildA O n r ∧ JQP O D L w ∧ (cv w).get? n = some r) (EQP O D L) := by
  unfold synthesizeChild
  refine Triple.bind (tripleP_cacheGet O hA D L) ?_
  intro m
  cases hc : m.get? n with
  | some r =>
    try dsimp only
    exact Triple.pure fun w hw =>
      ⟨hw.1.1.2 n r (by rw [← hw.2]; exact hc), hw.1, by rw [← hw.2]; exact hc⟩
  | none =>
    try dsimp only
    by_cases hn : ∀ p ∈ L, p.1 ≠ n
    · refine Triple.conseq (P := JQP O D L) ?_ (fun _ hw => hw.1) (fun _ _ h => h)
        (fun _ _ h => h)
      refine Triple.bind (triple_withRun hentryT) ?_
      intro r
      refine Triple.bind (Q := fun _ w => JQP O D L w ∧ RealChildA O n r ∧ (cv w).get? n = some r)
        ?_ (fun _ => Triple.pure fun w hw => ⟨hw.2.1, hw.1, hw.2.2⟩)
      refine Triple.of_runs (refModify_runs _ _) fun w u w' hw h => ?_
      obtain ⟨hw2, w1, hw1, hrun⟩ := hw
      have hr : RealChildA O n r := RealChildA.of_jqc O hA hw1.1 hrun
      have hins := jqp_insert_runs O hA hw2 hr hn h
      exact ⟨hins.1, hr, hins.2⟩
    · intro w hw
      exfalso
      apply hn
      intro p hp heq
      have := hw.1.2 p hp
      rw [heq, ← hw.2, hc] at this
      cases this

/-- `hentryT` for `JQP` from the body at `D + 1`. -/
theorem hentryT_of_bodyP (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : 1 ≤ D) {L : List (Name × Res)} {c : Name}
    (hbodyP : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQP O (D + 1) L)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQP O D L) (synthesizeCombinational c)
      (fun _ => JQP O D L) (EQP O D L) :=
  full_tripleAP O hA (core_tripleAP O hA D hD L c @hbodyP)

/-! ## The depth induction at `JQP` -/

/-- The body at depth `D` keeps `JQP` (every admissible context, declaration and constant). -/
def BodyKeepsP (O : RefLawsAOps MkRefd mref cref) (D : Nat) (L : List (Name × Res)) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo)
      (isInst : Lean.Expr → Bool),
    Keeps mctx mref cctx cref (JQP O D L)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst)

/-- The restricted translator at `JQP O D L` from the child entry at `JQP O D L` and `T`. -/
theorem translate_keepsP_of_tele (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (D : Nat) (L : List (Name × Res))
    (hC : ChildSynthA O (JQP O D L)) (tenv : Lean.Environment) :
    RecA O (JQP O D L) (fun e h t n => translateExprToWire tenv e h t n) :=
  have hS := stableA_JQP O D L
  have hchild : ChildEntryA O (JQP O D L) :=
    childEntryA_of_childSynthA O hS (fun _ h => h.1.1.2.1) hC
  have hcanon : CanonKeyA O (JQP O D L) := Tools.ShippingChildCanonKeyA.canonKeyA O hS
  have hImpl : LegacyImplA O (JQP O D L) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_tele O hS T hcanon hchild
  translate_keepsA O hS tenv hImpl
    (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl O hS hImpl) hcanon
    (Tools.ShippingChildProjFieldA.projFieldNameA O T hS) hchild

/-- One depth step at `JQP` with the handlers discharged locally. -/
theorem bodyKeepsP_of_tele (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (D : Nat) (L : List (Name × Res)) (hC : ChildSynthA O (JQP O D L)) : BodyKeepsP O D L :=
  have hS := stableA_JQP O D L
  have hchild : ChildEntryA O (JQP O D L) :=
    childEntryA_of_childSynthA O hS (fun _ h => h.1.1.2.1) hC
  have hcanon : CanonKeyA O (JQP O D L) := Tools.ShippingChildCanonKeyA.canonKeyA O hS
  have hImpl : LegacyImplA O (JQP O D L) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_tele O hS T hcanon hchild
  fun mctx cctx hA declName tenv b ci isInst =>
    fromConst_frontends_of_handlers O hA hS hImpl
      (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl O hS hImpl) hcanon
      (Tools.ShippingChildProjFieldA.projFieldNameA O T hS) hC (fun _ h => h.1.1.2.1)
      tenv b declName ci isInst
      (fun _ _ => Tools.ShippingChildLegacyTailA.legacyTailA_generic O T hS hA _
        (translate_keepsP_of_tele O T D L hC tenv) b declName ci isInst)

/-- One step: the child entry at `D ≥ 1` from the body at `D + 1`. -/
theorem childKeepsP_of_body (O : RefLawsAOps MkRefd mref cref) (D : Nat) (hD : 1 ≤ D)
    (L : List (Name × Res)) (hB : D < sparkleSynthDepthLimit → BodyKeepsP O (D + 1) L) :
    ChildSynthA O (JQP O D L) := by
  intro mctx cctx hA c
  rw [keeps_iff]
  refine Triple.conseq (synthesizeChild_tripleP O hA (D := D) (L := L) (n := c)
    (hentryT_of_bodyP O hA hD ?_)) (fun _ h => h) (fun _ _ h => h.2.1) (fun _ _ h => h)
  intro tenv hl b ci isInst
  exact hB hl mctx cctx hA c tenv b ci isInst

/-- **The child entry at `JQP` at every depth `D ≥ 1`** (induction on `limit - D`). -/
theorem childKeepsP_all_of_tele (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (L : List (Name × Res)) :
    ∀ D, 1 ≤ D → ChildSynthA O (JQP O D L) := by
  have key : ∀ k D, sparkleSynthDepthLimit - D = k → 1 ≤ D → ChildSynthA O (JQP O D L) := by
    intro k
    induction k with
    | zero =>
      intro D hk hD
      exact childKeepsP_of_body O D hD L (fun hl => absurd hl (by omega))
    | succ k ih =>
      intro D hk hD
      exact childKeepsP_of_body O D hD L
        (fun _ => bodyKeepsP_of_tele O T (D + 1) L (ih (D + 1) (by omega) (by omega)))
  intro D hD
  exact key _ D rfl hD

/-- **`synthesizeChild` from a pinned world** (depth `D ≥ 1`): the result is a `RealChildA`, the pin
`L` survives, and the cache then maps the callee to the returned child. -/
theorem synthesizeChild_pinned (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D)
    (L : List (Name × Res)) (c : Name) :
    Triple mctx mref cctx cref (JQP O D L) (synthesizeChild c)
      (fun r w => RealChildA O c r ∧ JQP O D L w ∧ (cv w).get? c = some r) (EQP O D L) :=
  synthesizeChild_tripleP O hA
    (hentryT_of_bodyP O hA hD fun {tenv} _ b ci isInst =>
      bodyKeepsP_of_tele O T (D + 1) L (childKeepsP_all_of_tele O T L (D + 1) (by omega))
        mctx cctx hA c tenv b ci isInst)

end Tools.ShippingChildPinC

#print axioms Tools.ShippingChildPinC.synthesizeChild_pinned
