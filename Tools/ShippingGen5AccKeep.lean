import Tools.ShippingGen5AccInd
import Tools.ShippingGen2KeepChild
set_option autoImplicit false
-- Built in the Pod (g5ac-r6) at 5c38c6fc: `kjob lake build Tools.ShippingGen5AccKeep`, exit 0, 711 jobs (the build was of the identical content; this header is the only later change). Clean issue-linked build is the coder's. No sorry / axiom / native_decide.

/-! # DG-ACC unit A5a: `AccKeepChildStmt` (scripts/gen5/DG_ACC_FREEZE_REV3.md §2.1, items 1-5)

A copy of M3's G-KEEP-CHILD chain (`Tools/ShippingGen2KeepChild.lean:46-369`) with `InvAt L P Reach` replaced by
`AccInvAt K L Reach`, `CacheShips` by `CacheAcc K Reach` and `ShipsRes L P n r` by `Acc (CallRel K) n`. The cache insert is
`cacheAcc_insert` (A2). The statement `AccKeepChildStmt K L Reach` is closed here WITHOUT any route, data-link, reads or
`hrow` premise: `AccIHAt` is used only in the miss case of `synthesizeChild_accRes`-style steps and `CacheAcc` in the hit case.

Scope of "no `hrow`": this is a statement about the ordinary static edges (the `Acc` induction) only; it says nothing about
the supply of `ServedP` in general (`hrow` of M3's `servedShips0_proved` belongs to the trace chain, not copied here).
Nothing here supplies `MachineRouteAt`, reads, `RunDataLink`/`ReachCover`, `GenSFacts` or off-route coverage. Not DG-ACC /
M5 / FG completion. -/

namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness
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

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
variable (K : AssignKit ι dom env₀)

/-- `InvAt` with the thrown exception in the class (the `E(D)` of the freeze; as `EQP`, ChildPinC.lean:52). -/
def AccEInv (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) :
    Exception → Void IO.RealWorld → Prop :=
  fun e w => AccInvAt K L Reach D w ∧ OkExc e

/-! ## 1. Per-ref steps (freeze #1-#4) -/

/-- #1 A set of another per-synthesis ref under `InvAt` (copy of `psset`, ChildPinC.lean:62). -/
macro "aiset " K:term:max L:term:max hA:term:max R:term:max D:term:max : tactic => `(tactic|
  (refine Tools.ShippingChildInv.Triple.bind (Tools.ShippingChildInv.keeps_iff.mp
      (Tools.ShippingChildVCA.keepsA_framed (Tools.ShippingGen2.Laws.O $L) $hA
        (Tools.ShippingGen5Acc.stableA_accInvAt $K $L $R $D)
        (Tools.ShippingChildInvA.FramedA.sideSet _ ?s))) ?_
   case s => constructor
   intro _))
/-- #1 A read of another per-synthesis ref under `InvAt` (copy of `psget`, ChildPinC.lean:68). -/
macro "aiget " K:term:max L:term:max hA:term:max R:term:max D:term:max : tactic => `(tactic|
  (refine Tools.ShippingChildInv.Triple.bind (Tools.ShippingChildInv.keeps_iff.mp
      (Tools.ShippingChildVCA.keepsA_framed (Tools.ShippingGen2.Laws.O $L) $hA
        (Tools.ShippingGen5Acc.stableA_accInvAt $K $L $R $D)
        (Tools.ShippingChildInvA.FramedA.sideGet ?s))) ?_
   case s => constructor
   intro _))

/-- #2 The depth set keeps `InvAt` at the new depth (`O.depthSet`: `cv` unchanged; copy of ChildPinC.lean:75). -/
theorem tripleAcc_depthSet (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D v : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => AccInvAt K L Reach v) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := L.O.depthSet hA _ _ _ _ h hw.1.1.1
    refine ⟨⟨⟨L.O.depthSetQ hA _ _ _ _ h hw.1.1.1, hk.2.1.trans hw.1.1.2.1, hk.2.2⟩, ?_⟩, ?_⟩
    · rw [hk.1]; exact hw.1.2
    · rw [hk.1]; exact hw.2

/-- #3 The depth modify keeps `InvAt` at `f D` (`O.depthModify'`: `cv` unchanged; copy of ChildPinC.lean:86). -/
theorem tripleAcc_depthModify (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) (f : Nat → Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => AccInvAt K L Reach (f D)) R :=
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
theorem finAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (d : Nat)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (AccInvAt K L Reach (d + 1))
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
      (fun _ => AccInvAt K L Reach d) (AccEInv K L Reach d) := by
  refine Triple.bind (Triple.conseq (tripleAcc_depthModify K L Reach hA (d + 1) (fun x => x - 1))
    (fun _ h => h) (Q' := fun _ => AccInvAt K L Reach d)
    (fun _ w h => by show AccInvAt K L Reach d w; have h' : AccInvAt K L Reach (d + 1 - 1) w := h
                     rw [Nat.add_sub_cancel] at h'; exact h')
    (fun _ _ h => h)) ?_
  intro _
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  aiset K L hA Reach d; aiset K L hA Reach d; aiset K L hA Reach d; aiset K L hA Reach d
  aiset K L hA Reach d; aiset K L hA Reach d
  exact keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach d) (FramedA.sideSet _ .singleOut))

/-! ## 2. The nested entry (freeze #5, #6, #11) -/

/-- #5 **The nested core entry keeps `InvAt` (depth `D ≥ 1`, no clear), on every outcome** (copy of
`core_tripleAP`, ChildPinC.lean:133). The cache clear (depth 0) is excluded by `1 ≤ D` (`h0`). -/
theorem core_tripleAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) (hD : 1 ≤ D) (declName : Name)
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (AccInvAt K L Reach (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinationalCore declName [] false)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach D)
    (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsA_diag L.O hA (stableA_accInvAt K L Reach D)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.conseq (tripleA_depthGet L.O hA (stableA_accInvAt K L Reach D)) (fun _ h => h)
      (Q' := fun d w => AccInvAt K L Reach D w ∧ d = D)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.1.1.2.2⟩) (fun _ _ h => h)) ?_
  intro d hd
  subst hd
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr L.O hA (stableA_accInvAt K L Reach d) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : d < sparkleSynthDepthLimit := Nat.lt_of_not_ge hlt
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (AccInvAt K L Reach (d + 1))
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
          (fun _ => AccInvAt K L Reach d) (AccEInv K L Reach d) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := AccInvAt K L Reach (d + 1)) (E := OkExc) ?_
        (finAcc K L Reach hA d m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach (d + 1))
        (FramedA.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach (d + 1))
        FramedA.env)) ?_
      intro env
      exact keeps_iff.mp (hbody hlt prof.isSome _ _)
    have h0 : ¬ ((d == 0) = true) := by
      intro h; simp at h; omega
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    aiget K L hA Reach d; aiget K L hA Reach d; aiget K L hA Reach d; aiget K L hA Reach d
    aiget K L hA Reach d; aiget K L hA Reach d; aiget K L hA Reach d
    aiset K L hA Reach d; aiset K L hA Reach d; aiset K L hA Reach d; aiset K L hA Reach d
    aiset K L hA Reach d; aiset K L hA Reach d; aiset K L hA Reach d
    refine Triple.bind (tripleAcc_depthSet K L Reach hA d (d + 1)) ?_
    intro _
    exact body _ _ _ _ _ _ _

/-- #6 The full nested entry: the core, one environment read, pure post-processing (copy of `full_tripleAP`,
ChildPinC.lean:207). -/
theorem full_tripleAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {declName : Name}
    (hcore : Triple mctx mref cctx cref (AccInvAt K L Reach D)
      (synthesizeCombinationalCore declName [] false) (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational declName)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind hcore ?_
  rintro ⟨m, dd⟩
  dsimp only
  refine Triple.bind (keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach D)
    (FramedA.ioEnv _))) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-- #11 `hentryT` for `InvAt` from the body at `D + 1` (copy of `hentryT_of_bodyP`, ChildPinC.lean:292). -/
theorem hentryT_of_bodyAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D) {c : Name}
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (AccInvAt K L Reach (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst)) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational c)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D) :=
  full_tripleAcc K L Reach hA (core_tripleAcc K L Reach hA D hD c @hbody)

/-! ## 3. The cache (freeze #7-#9) -/

/-- #7 The cache read under `InvAt`: the value read is the world's cache value (copy of `tripleP_cacheGet`,
ChildPinC.lean:222). -/
theorem tripleAcc_cacheGet (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (sparkleChildCache.get : MetaM _)
      (fun m w => AccInvAt K L Reach D w ∧ m = cv w) (AccEInv K L Reach D) := by
  intro w hw
  have hK := keeps_iff.mp (keepsA_framed L.O hA (stableA_accInvAt K L Reach D) FramedA.cacheGet) w hw
  cases hm : (sparkleChildCache.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    rw [hm] at hK
    have hk := L.O.frame hA _ FramedA.cacheGet w hw.1.1.1
    rw [endW_of_runs hm] at hk
    exact ⟨hK, (runsTo_get_readOf _ hm).trans hk.1.symm⟩
  | error e w1 => rw [hm] at hK; exact hK


/-- #9 **The child insert keeps `InvAt`** (`jqc_insert_runs`, ChildCacheA.lean:263, for the `JQC` half;
`O.cacheModify'` + #8 for the `CacheShips` half). -/
theorem accInvAt_insert_runs (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {D : Nat} {n : Name} {r : Res} {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (hw : AccInvAt K L Reach D w) (hr : RealChildA L.O n r) (hs : Reach n → Acc (CallRel K) n)
    (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert n r) :
      MetaM Unit) mctx mref cctx cref w u w') :
    AccInvAt K L Reach D w' := by
  have hk := L.O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw.1.1.1 h
  have hcv : cv w' = (cv w).insert n r := hk.1
  refine ⟨jqc_insert_runs L.O hA hw.1 hr h, ?_⟩
  rw [hcv]
  exact cacheAcc_insert K hw.2 hs

/-! ## 4. The memoised child entry (freeze #10, #13) -/

/-- #10 **`synthesizeChild` under `InvAt`, on every outcome** (copy of `synthesizeChild_tripleP`,
ChildPinC.lean:255, without the pin/absence split). A returned value is a `RealChildA`, ships if the name is
reached, and the end world is `InvAt D`.
* Hit: `RealChildA` from the `JQC` cache half, `Acc` from `CacheAcc`, both of the read world's cache value.
* Miss: `triple_withRun hentryT` (ChildCacheA.lean:337) gives the START world `w0` of the full entry with
  `InvAt D w0`; `RealChildA.of_jqc` and `IHAt D` at that run give the two facts of the inserted value; #9. -/
theorem synthesizeChild_tripleAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {n : Name} (hIH : AccIHAt K L Reach D)
    (hentryT : Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational n)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeChild n)
      (fun r w => RealChildA L.O n r ∧ (Reach n → Acc (CallRel K) n) ∧ AccInvAt K L Reach D w)
      (AccEInv K L Reach D) := by
  unfold synthesizeChild
  refine Triple.bind (tripleAcc_cacheGet K L Reach hA D) ?_
  intro m
  cases hc : m.get? n with
  | some r =>
    try dsimp only
    exact Triple.pure fun w hw =>
      ⟨hw.1.1.2 n r (by rw [← hw.2]; exact hc),
        fun hR => hw.1.2 n r hR (by rw [← hw.2]; exact hc), hw.1⟩
  | none =>
    try dsimp only
    refine Triple.conseq (P := AccInvAt K L Reach D) ?_ (fun _ hw => hw.1) (fun _ _ h => h)
      (fun _ _ h => h)
    refine Triple.bind (triple_withRun hentryT) ?_
    intro r
    refine Triple.bind
      (Q := fun _ w => AccInvAt K L Reach D w ∧ RealChildA L.O n r ∧ (Reach n → Acc (CallRel K) n))
      ?_ (fun _ => Triple.pure fun w hw => ⟨hw.2.1, hw.2.2, hw.1⟩)
    refine Triple.of_runs (refModify_runs _ _) fun w u w' hw h => ?_
    obtain ⟨hw2, w0, hw0, hrun⟩ := hw
    -- `w0`: the start world of the full entry (after the framed cache read), `InvAt D w0`
    have hr : RealChildA L.O n r := RealChildA.of_jqc L.O hA hw0.1 hrun
    have hs : Reach n → Acc (CallRel K) n := fun hR => hIH n hR mctx cctx w0 w r hA hw0 hrun
    exact ⟨accInvAt_insert_runs K L Reach hA hw2 hr hs h, hr, hs⟩

/-- #13 **Returning-run form: a returned child of a reached name ships** (used by G-SERVED and G-POST). No
`hentryT` premise: the run is decomposed (the cache read, then hit or miss).
* Hit: the value is the read world's cache entry; `CacheAcc` of that world (the read is framed, #7).
* Miss: `IHAt D` is applied at the PRE-ENTRY `InvAt D` world `w1`, i.e. the world after the cache read, which is
  exactly the world the inner full entry `synthesizeCombinational n` starts from; `InvAt D w1` holds by the framed
  cache read (#7 at `hw`). The insert and the return after it do not change the value.
`hA` is the admissible context that `IHAt` and the framed read ask for. -/
theorem synthesizeChild_accRes (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res}
    (hw : AccInvAt K L Reach D w) (hIH : AccIHAt K L Reach D)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') :
    Reach n → Acc (CallRel K) n := by
  intro hR
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  -- the framed cache read: the pre-entry world `w1` is `InvAt D`, and `m` is its cache value
  have hw1 : AccInvAt K L Reach D w1 ∧ m = cv w1 :=
    runs_of_triple (tripleAcc_cacheGet K L Reach hA D) hw hget
  cases hc : m.get? n with
  | some y =>
    simp only [hc] at h
    obtain ⟨-, -⟩ := RunsTo.pure_world h
    exact hw1.1.2 n y hR (by rw [← hw1.2]; exact hc)
  | none =>
    simp only [hc] at h
    -- the inner full entry, run from the pre-entry world `w1`
    obtain ⟨r1, w2, hrun, h⟩ := RunsTo.bind h
    obtain ⟨u, w3, -, h⟩ := RunsTo.bind h
    obtain ⟨-, -⟩ := RunsTo.pure_world h
    exact hIH n hR mctx cctx w1 w2 r1 hA hw1.1 hrun

/-! ## 5. G-KEEP-CHILD (freeze #12) and the T1 corollary -/

/-- #12 **G-KEEP-CHILD, PROVED** (copy of `childKeepsP_of_body`, ChildPinC.lean:346, with #10 and #11). -/
theorem accKeepChild_proved (L : Laws mref cref) (Reach : Name → Prop) :
    AccKeepChildStmt K L Reach := by
  intro D hD hB hIH
  show Tools.ShippingChildFrontCP.ChildSynthA L.O (AccInvAt K L Reach D)
  intro mctx cctx hA c
  rw [keeps_iff]
  refine Triple.conseq (synthesizeChild_tripleAcc K L Reach hA (D := D) (n := c) hIH
    (hentryT_of_bodyAcc K L Reach hA hD ?_)) (fun _ h => h) (fun _ _ h => h.2.2) (fun _ _ h => h)
  intro tenv hl b ci isInst
  exact hB hl mctx cctx hA c tenv b ci isInst

end Tools.ShippingGen5Acc

#print axioms Tools.ShippingGen5Acc.accKeepChild_proved
#print axioms Tools.ShippingGen5Acc.synthesizeChild_accRes
