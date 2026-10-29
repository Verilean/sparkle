import Tools.ShippingGen2T1
import Tools.ShippingChildPinC
set_option autoImplicit false
-- NOT BUILT (written without a build; scripts/gen2/KEEPCHILD_POST_FREEZE.md §B, approved).
-- No `sorry`, no `axiom`, no `native_decide`. No change to Tools/ShippingGen2Defs.lean (current `ShipsRes`/`InvAt`).

/-! # Gen2 M3: G-KEEP-CHILD at `InvAt` (freeze §B, lemmas 1-13)

A copy of the ChildPinC chain (Tools/ShippingChildPinC.lean: `psset`/`psget` :62-72, `tripleP_depthSet` :75,
`tripleP_depthModify` :86, `finP` :104, `core_tripleAP` :133, `full_tripleAP` :207, `tripleP_cacheGet` :222,
`synthesizeChild_tripleP` :255, `hentryT_of_bodyP` :292, `childKeepsP_of_body` :346) with `JQP O D L` replaced by
`InvAt L P Reach D` (Tools/ShippingGen2Defs.lean:144, `JQC ∧ CacheShips (cv w)`). Every framed or diagnostic step
keeps `cv`, so the `CacheShips` conjunct rides along exactly as the pin did; the only cache write of the nested
entry at `1 ≤ D` is the child insert (the clear at depth 0 is excluded by `1 ≤ D`, as `h0` in `core_tripleAP`).

The insertion of a REACHED name's result needs `ShipsRes` of that result: it is `IHAt D` applied to the inner full
entry's run, from its START world (the world after the framed cache read, which is still `InvAt D`).

PROVED here: `keepChild_proved : KeepChildStmt L P Reach`, `synthesizeChild_shipsRes` (returning-run form), and
`t1_of_step_kc` (`t1_of_step` with `hKC` discharged; still conditional on the other premises). -/

namespace Tools.ShippingGen2
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

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `InvAt` with the thrown exception in the class (the `E(D)` of the freeze; as `EQP`, ChildPinC.lean:52). -/
def EInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) :
    Exception → Void IO.RealWorld → Prop :=
  fun e w => InvAt L P Reach D w ∧ OkExc e

/-! ## 1. Per-ref steps (freeze #1-#4) -/

/-- #1 A set of another per-synthesis ref under `InvAt` (copy of `psset`, ChildPinC.lean:62). -/
macro "iset " L:term:max hA:term:max P:term:max R:term:max D:term:max : tactic => `(tactic|
  (refine Tools.ShippingChildInv.Triple.bind (Tools.ShippingChildInv.keeps_iff.mp
      (Tools.ShippingChildVCA.keepsA_framed (Tools.ShippingGen2.Laws.O $L) $hA
        (Tools.ShippingGen2.stableA_invAt $L $P $R $D)
        (Tools.ShippingChildInvA.FramedA.sideSet _ ?s))) ?_
   case s => constructor
   intro _))
/-- #1 A read of another per-synthesis ref under `InvAt` (copy of `psget`, ChildPinC.lean:68). -/
macro "iget " L:term:max hA:term:max P:term:max R:term:max D:term:max : tactic => `(tactic|
  (refine Tools.ShippingChildInv.Triple.bind (Tools.ShippingChildInv.keeps_iff.mp
      (Tools.ShippingChildVCA.keepsA_framed (Tools.ShippingGen2.Laws.O $L) $hA
        (Tools.ShippingGen2.stableA_invAt $L $P $R $D)
        (Tools.ShippingChildInvA.FramedA.sideGet ?s))) ?_
   case s => constructor
   intro _))

/-- #2 The depth set keeps `InvAt` at the new depth (`O.depthSet`: `cv` unchanged; copy of ChildPinC.lean:75). -/
theorem tripleInv_depthSet (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D v : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (InvAt L P Reach D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => InvAt L P Reach v) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := L.O.depthSet hA _ _ _ _ h hw.1.1.1
    refine ⟨⟨⟨L.O.depthSetQ hA _ _ _ _ h hw.1.1.1, hk.2.1.trans hw.1.1.2.1, hk.2.2⟩, ?_⟩, ?_⟩
    · rw [hk.1]; exact hw.1.2
    · rw [hk.1]; exact hw.2

/-- #3 The depth modify keeps `InvAt` at `f D` (`O.depthModify'`: `cv` unchanged; copy of ChildPinC.lean:86). -/
theorem tripleInv_depthModify (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) (f : Nat → Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (InvAt L P Reach D) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => InvAt L P Reach (f D)) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw h => by
    have hk := L.O.depthModify' hA f hw.1.1.1 h
    have hq' : L.O.quiet w' := by
      obtain ⟨w1, hg, hs⟩ := Tools.ShippingChildBndCore.modify_split sparkleSynthDepth f h
      have hq1 := L.O.frameQ hA _ FramedA.depthGet w hw.1.1.1
      rw [endW_of_runs hg] at hq1
      exact L.O.depthSetQ hA _ _ _ _ hs hq1
    refine ⟨⟨⟨hq', hk.2.1.trans hw.1.1.2.1, ?_⟩, ?_⟩, ?_⟩
    · rw [hk.2.2, hw.1.1.2.2]
    · rw [hk.1]; exact hw.1.2
    · rw [hk.1]; exact hw.2

/-- #4 The `finally` of the entry under `InvAt` (copy of `finP`, ChildPinC.lean:104). -/
theorem finInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (d : Nat)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (InvAt L P Reach (d + 1))
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
      (fun _ => InvAt L P Reach d) (EInv L P Reach d) := by
  refine Triple.bind (Triple.conseq (tripleInv_depthModify L P Reach hA (d + 1) (fun x => x - 1))
    (fun _ h => h) (Q' := fun _ => InvAt L P Reach d)
    (fun _ w h => by show InvAt L P Reach d w; have h' : InvAt L P Reach (d + 1 - 1) w := h
                     rw [Nat.add_sub_cancel] at h'; exact h')
    (fun _ _ h => h)) ?_
  intro _
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  iset L hA P Reach d; iset L hA P Reach d; iset L hA P Reach d; iset L hA P Reach d
  iset L hA P Reach d; iset L hA P Reach d
  exact keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach d) (FramedA.sideSet _ .singleOut))

/-! ## 2. The nested entry (freeze #5, #6, #11) -/

/-- #5 **The nested core entry keeps `InvAt` (depth `D ≥ 1`, no clear), on every outcome** (copy of
`core_tripleAP`, ChildPinC.lean:133). The cache clear (depth 0) is excluded by `1 ≤ D` (`h0`). -/
theorem core_tripleAInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) (hD : 1 ≤ D) (declName : Name)
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (InvAt L P Reach (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Triple mctx mref cctx cref (InvAt L P Reach D) (synthesizeCombinationalCore declName [] false)
      (fun _ => InvAt L P Reach D) (EInv L P Reach D) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach D)
    (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsA_diag L.O hA (stableA_invAt L P Reach D)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.conseq (tripleA_depthGet L.O hA (stableA_invAt L P Reach D)) (fun _ h => h)
      (Q' := fun d w => InvAt L P Reach D w ∧ d = D)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.1.1.2.2⟩) (fun _ _ h => h)) ?_
  intro d hd
  subst hd
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr L.O hA (stableA_invAt L P Reach d) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : d < sparkleSynthDepthLimit := Nat.lt_of_not_ge hlt
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (InvAt L P Reach (d + 1))
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
          (fun _ => InvAt L P Reach d) (EInv L P Reach d) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := InvAt L P Reach (d + 1)) (E := OkExc) ?_
        (finInv L P Reach hA d m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (d + 1))
        (FramedA.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (d + 1))
        FramedA.env)) ?_
      intro env
      exact keeps_iff.mp (hbody hlt prof.isSome _ _)
    have h0 : ¬ ((d == 0) = true) := by
      intro h; simp at h; omega
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    iget L hA P Reach d; iget L hA P Reach d; iget L hA P Reach d; iget L hA P Reach d
    iget L hA P Reach d; iget L hA P Reach d; iget L hA P Reach d
    iset L hA P Reach d; iset L hA P Reach d; iset L hA P Reach d; iset L hA P Reach d
    iset L hA P Reach d; iset L hA P Reach d; iset L hA P Reach d
    refine Triple.bind (tripleInv_depthSet L P Reach hA d (d + 1)) ?_
    intro _
    exact body _ _ _ _ _ _ _

/-- #6 The full nested entry: the core, one environment read, pure post-processing (copy of `full_tripleAP`,
ChildPinC.lean:207). -/
theorem full_tripleAInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {declName : Name}
    (hcore : Triple mctx mref cctx cref (InvAt L P Reach D)
      (synthesizeCombinationalCore declName [] false) (fun _ => InvAt L P Reach D) (EInv L P Reach D)) :
    Triple mctx mref cctx cref (InvAt L P Reach D) (synthesizeCombinational declName)
      (fun _ => InvAt L P Reach D) (EInv L P Reach D) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind hcore ?_
  rintro ⟨m, dd⟩
  dsimp only
  refine Triple.bind (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach D)
    (FramedA.ioEnv _))) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-- #11 `hentryT` for `InvAt` from the body at `D + 1` (copy of `hentryT_of_bodyP`, ChildPinC.lean:292). -/
theorem hentryT_of_bodyInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D) {c : Name}
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (InvAt L P Reach (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst)) :
    Triple mctx mref cctx cref (InvAt L P Reach D) (synthesizeCombinational c)
      (fun _ => InvAt L P Reach D) (EInv L P Reach D) :=
  full_tripleAInv L P Reach hA (core_tripleAInv L P Reach hA D hD c @hbody)

/-! ## 3. The cache (freeze #7-#9) -/

/-- #7 The cache read under `InvAt`: the value read is the world's cache value (copy of `tripleP_cacheGet`,
ChildPinC.lean:222). -/
theorem tripleInv_cacheGet (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) :
    Triple mctx mref cctx cref (InvAt L P Reach D) (sparkleChildCache.get : MetaM _)
      (fun m w => InvAt L P Reach D w ∧ m = cv w) (EInv L P Reach D) := by
  intro w hw
  have hK := keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach D) FramedA.cacheGet) w hw
  cases hm : (sparkleChildCache.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    rw [hm] at hK
    have hk := L.O.frame hA _ FramedA.cacheGet w hw.1.1.1
    rw [endW_of_runs hm] at hk
    exact ⟨hK, (runsTo_get_readOf _ hm).trans hk.1.symm⟩
  | error e w1 => rw [hm] at hK; exact hK

/-- #8 The insert of a shipping entry keeps `CacheShips` (copy of `cacheInvA_insert`, ChildCacheA.lean:134). An
unreached key needs nothing (`hr` is only asked under `Reach n`). -/
theorem cacheShips_insert (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {m : Std.HashMap Name Res} {n : Name} {r : Res}
    (h : CacheShips L P Reach m) (hr : Reach n → ShipsRes L P n r) :
    CacheShips L P Reach (m.insert n r) := by
  intro c' r' hR h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : n = c' := by simpa using heq
    subst this
    cases h'
    exact hr hR
  · exact h c' r' hR h'

/-- #9 **The child insert keeps `InvAt`** (`jqc_insert_runs`, ChildCacheA.lean:263, for the `JQC` half;
`O.cacheModify'` + #8 for the `CacheShips` half). -/
theorem invAt_insert_runs (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {D : Nat} {n : Name} {r : Res} {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (hw : InvAt L P Reach D w) (hr : RealChildA L.O n r) (hs : Reach n → ShipsRes L P n r)
    (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert n r) :
      MetaM Unit) mctx mref cctx cref w u w') :
    InvAt L P Reach D w' := by
  have hk := L.O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw.1.1.1 h
  have hcv : cv w' = (cv w).insert n r := hk.1
  refine ⟨jqc_insert_runs L.O hA hw.1 hr h, ?_⟩
  rw [hcv]
  exact cacheShips_insert L P Reach hw.2 hs

/-! ## 4. The memoised child entry (freeze #10, #13) -/

/-- #10 **`synthesizeChild` under `InvAt`, on every outcome** (copy of `synthesizeChild_tripleP`,
ChildPinC.lean:255, without the pin/absence split). A returned value is a `RealChildA`, ships if the name is
reached, and the end world is `InvAt D`.
* Hit: `RealChildA` from the `JQC` cache half, `ShipsRes` from `CacheShips`, both of the read world's cache value.
* Miss: `triple_withRun hentryT` (ChildCacheA.lean:337) gives the START world `w0` of the full entry with
  `InvAt D w0`; `RealChildA.of_jqc` and `IHAt D` at that run give the two facts of the inserted value; #9. -/
theorem synthesizeChild_tripleInv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {n : Name} (hIH : IHAt L P Reach D)
    (hentryT : Triple mctx mref cctx cref (InvAt L P Reach D) (synthesizeCombinational n)
      (fun _ => InvAt L P Reach D) (EInv L P Reach D)) :
    Triple mctx mref cctx cref (InvAt L P Reach D) (synthesizeChild n)
      (fun r w => RealChildA L.O n r ∧ (Reach n → ShipsRes L P n r) ∧ InvAt L P Reach D w)
      (EInv L P Reach D) := by
  unfold synthesizeChild
  refine Triple.bind (tripleInv_cacheGet L P Reach hA D) ?_
  intro m
  cases hc : m.get? n with
  | some r =>
    try dsimp only
    exact Triple.pure fun w hw =>
      ⟨hw.1.1.2 n r (by rw [← hw.2]; exact hc),
        fun hR => hw.1.2 n r hR (by rw [← hw.2]; exact hc), hw.1⟩
  | none =>
    try dsimp only
    refine Triple.conseq (P := InvAt L P Reach D) ?_ (fun _ hw => hw.1) (fun _ _ h => h)
      (fun _ _ h => h)
    refine Triple.bind (triple_withRun hentryT) ?_
    intro r
    refine Triple.bind
      (Q := fun _ w => InvAt L P Reach D w ∧ RealChildA L.O n r ∧ (Reach n → ShipsRes L P n r))
      ?_ (fun _ => Triple.pure fun w hw => ⟨hw.2.1, hw.2.2, hw.1⟩)
    refine Triple.of_runs (refModify_runs _ _) fun w u w' hw h => ?_
    obtain ⟨hw2, w0, hw0, hrun⟩ := hw
    -- `w0`: the start world of the full entry (after the framed cache read), `InvAt D w0`
    have hr : RealChildA L.O n r := RealChildA.of_jqc L.O hA hw0.1 hrun
    have hs : Reach n → ShipsRes L P n r := fun hR => hIH n hR mctx cctx w0 w r hA hw0 hrun
    exact ⟨invAt_insert_runs L P Reach hA hw2 hr hs h, hr, hs⟩

/-- #13 **Returning-run form: a returned child of a reached name ships** (used by G-SERVED and G-POST). No
`hentryT` premise: the run is decomposed (the cache read, then hit or miss).
* Hit: the value is the read world's cache entry; `CacheShips` of that world (the read is framed, #7).
* Miss: `IHAt D` is applied at the PRE-ENTRY `InvAt D` world `w1`, i.e. the world after the cache read, which is
  exactly the world the inner full entry `synthesizeCombinational n` starts from; `InvAt D w1` holds by the framed
  cache read (#7 at `hw`). The insert and the return after it do not change the value.
`hA` is the admissible context that `IHAt` and the framed read ask for. -/
theorem synthesizeChild_shipsRes (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res}
    (hw : InvAt L P Reach D w) (hIH : IHAt L P Reach D)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') :
    Reach n → ShipsRes L P n r := by
  intro hR
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  -- the framed cache read: the pre-entry world `w1` is `InvAt D`, and `m` is its cache value
  have hw1 : InvAt L P Reach D w1 ∧ m = cv w1 :=
    runs_of_triple (tripleInv_cacheGet L P Reach hA D) hw hget
  cases hc : m.get? n with
  | some y =>
    simp only [hc] at h
    obtain ⟨hy, -⟩ := RunsTo.pure_world h
    rw [hy]
    exact hw1.1.2 n y hR (by rw [← hw1.2]; exact hc)
  | none =>
    simp only [hc] at h
    -- the inner full entry, run from the pre-entry world `w1`
    obtain ⟨r1, w2, hrun, h⟩ := RunsTo.bind h
    obtain ⟨u, w3, -, h⟩ := RunsTo.bind h
    obtain ⟨hy, -⟩ := RunsTo.pure_world h
    rw [hy]
    exact hIH n hR mctx cctx w1 w2 r1 hA hw1.1 hrun

/-! ## 5. G-KEEP-CHILD (freeze #12) and the T1 corollary -/

/-- #12 **G-KEEP-CHILD, PROVED** (copy of `childKeepsP_of_body`, ChildPinC.lean:346, with #10 and #11). -/
theorem keepChild_proved (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) :
    KeepChildStmt L P Reach := by
  intro D hD hB hIH
  show Tools.ShippingChildFrontCP.ChildSynthA L.O (InvAt L P Reach D)
  intro mctx cctx hA c
  rw [keeps_iff]
  refine Triple.conseq (synthesizeChild_tripleInv L P Reach hA (D := D) (n := c) hIH
    (hentryT_of_bodyInv L P Reach hA hD ?_)) (fun _ h => h) (fun _ _ h => h.2.2) (fun _ _ h => h)
  intro tenv hl b ci isInst
  exact hB hl mctx cctx hA c tenv b ci isInst

/-- **`t1_of_step` with `hKC` discharged** by `keepChild_proved`. Still CONDITIONAL on `StepStmt`,
`ServedShips0Stmt`, `NoTopStmt` (and `hLim`, which `limitStmt_proved` discharges). -/
theorem t1_of_step_kc (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hStep : StepStmt L P DataOk)
    (hSS : ServedShips0Stmt L P Reach DataOk) (hNT : NoTopStmt L Reach) (hLim : LimitStmt L) :
    T1Stmt L P Reach DataOk :=
  t1_of_step L P Reach DataOk hStep (keepChild_proved L P Reach) hSS hNT hLim

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.keepChild_proved
#print axioms Tools.ShippingGen2.synthesizeChild_shipsRes
#print axioms Tools.ShippingGen2.t1_of_step_kc
