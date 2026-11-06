import Tools.ShippingChildCoreC
import Tools.ShippingChildDepthC
import Tools.ShippingChildComposeC
import Tools.ShippingChildRunAMain
import Tools.ShippingCallsGateA
set_option autoImplicit false
-- FG circuit pilot S2h (part 1): a HISTORY invariant `JQH` for the child cache — every cache entry carries the evidence `E` that held at the start of the run that created it. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §34.
-- `RealChildA`, `JQC`, `CacheInvA` and every lemma about them are UNCHANGED; this file ADDS `RealChildE`, `CacheE`, `JQH` and the versions of the cache/entry lemmas that need the invariant (copies of ShippingChildCacheA / ShippingChildCoreC with `JQC` ↦ `JQH`; the only new proof steps are the cache clear (`CacheE {}`), the miss insert (the evidence is taken from the miss premise `MissE`) and the hit (the evidence is read from the cache entry)).

namespace Tools.ShippingFGCircuitS2hHist
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
open Tools.ShippingChildVertA
open Tools.ShippingChildCacheA
open Tools.ShippingChildCoreC

/-- the evidence a child run's start world can carry (contexts and world of the run) -/
abbrev StartEv := Meta.Context → Core.Context → Void IO.RealWorld → Prop

section Defs
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A real child WITH the saved reads of its run.** As `RealChildA.run` (same fields), plus `ev : E mctx cctx w`: the evidence at the start world `w` of the run that produced `r`; and the cache at `w` is again of this kind (the history that created the entry). -/
inductive RealChildE (O : RefLawsAOps MkRefd mref cref) (E : StartEv) : Name → Res → Prop
  | run {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld)
      (adm : AdmCtx O.quiet mctx cctx)
      (cache : ∀ c' r', (cv w).get? c' = some r' → RealChildE O E c' r')
      (synth : sv w = some synthesizeChild)
      (quiet : O.quiet w)
      (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w')
      (ev : E mctx cctx w) : RealChildE O E c r

/-- forgetting the saved reads -/
theorem RealChildE.toA {O : RefLawsAOps MkRefd mref cref} {E : StartEv} {c : Name} {r : Res}
    (h : RealChildE O E c r) : RealChildA O c r := by
  induction h with
  | run mctx cctx w w' adm cache synth quiet hr ev ih =>
    exact RealChildA.run mctx cctx w w' adm (fun c' r' h' => ih c' r' h') synth quiet hr

/-- every entry of the map is a `RealChildE` -/
def CacheE (O : RefLawsAOps MkRefd mref cref) (E : StartEv) (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → RealChildE O E c r

/-- **The history invariant**: `JQ` plus a cache whose every entry was created by a run with the evidence `E` at its start. -/
def JQH (O : RefLawsAOps MkRefd mref cref) (E : StartEv) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  JQ O.quiet D w ∧ CacheE O E (cv w)

/-- `JQH` with the thrown exception in the class -/
def EQH (O : RefLawsAOps MkRefd mref cref) (E : StartEv) (D : Nat) : Exception → Void IO.RealWorld → Prop :=
  fun e w => JQH O E D w ∧ OkExc e

theorem cacheE_empty (O : RefLawsAOps MkRefd mref cref) (E : StartEv) : CacheE O E {} := by
  intro c r h
  first
    | simp at h
    | (rw [Std.HashMap.get?_empty] at h; cases h)

theorem cacheE_insert {O : RefLawsAOps MkRefd mref cref} {E : StartEv} {m : Std.HashMap Name Res} {c : Name}
    {r : Res} (h : CacheE O E m) (hr : RealChildE O E c r) : CacheE O E (m.insert c r) := by
  intro c' r' h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : c = c' := by simpa using heq
    subst this
    cases h'
    exact hr
  · exact h c' r' h'

/-- `JQH` implies `JQC` (the forgetful direction: nothing of the old development changes) -/
theorem JQH.toC {O : RefLawsAOps MkRefd mref cref} {E : StartEv} {D : Nat} {w : Void IO.RealWorld}
    (h : JQH O E D w) : JQC O D w :=
  ⟨h.1, fun c r hm => (h.2 c r hm).toA⟩

theorem stableA_JQH (O : RefLawsAOps MkRefd mref cref) (E : StartEv) (D : Nat) : StableA O.quiet (JQH O E D) :=
  ⟨fun _ h => h.1.1, fun w w' hc hs hd hq h =>
    ⟨(stableA_JQ O.quiet D).2 w w' hc hs hd hq h.1, by rw [hc]; exact h.2⟩⟩

end Defs

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The miss premise** (NAMED HYPOTHESIS, FG D.T-4h; used only where `synthesizeChild n` finds no entry): in a `JQH` world at depth `D ≥ 1` whose cache has no entry for `n`, the evidence `E` holds for the context pair of the call. It is asked of the worlds of a history whose every entry already carries its own evidence, and only where a run is about to be created; a cache hit asks nothing (the evidence is read from the entry). -/
def MissE (O : RefLawsAOps MkRefd mref cref) (E : StartEv) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat), 1 ≤ D → ∀ (n : Name) (w : Void IO.RealWorld),
      JQH O E D w → (cv w).get? n = none → E mctx cctx w

/-! ## the steps of `JQH` -/

theorem keepsH_framed (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    (D : Nat) {α : Type} {p : MetaM α} (hp : FramedA MkRefd p) :
    Keeps mctx mref cctx cref (JQH O E D) p :=
  keepsA_framed O hA (stableA_JQH O E D) hp

theorem jqh_cacheGet (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    {D : Nat} {w : Void IO.RealWorld} {m : Std.HashMap Name Res} {w' : Void IO.RealWorld}
    (hw : JQH O E D w)
    (h : RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w') :
    m = cv w' ∧ JQH O E D w' := by
  have hk := O.frame hA _ FramedA.cacheGet w hw.1.1
  have hq := O.frameQ hA _ FramedA.cacheGet w hw.1.1
  rw [endW_of_runs h] at hk hq
  exact ⟨(runsTo_get_readOf _ h).trans hk.1.symm, (stableA_JQH O E D).2 w w' hk.1 hk.2.1 hk.2.2 (fun _ => hq) hw⟩

/-- the cache read as a triple: the value read is the cache of the world -/
theorem tripleH_cacheGet (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    (D : Nat) :
    Triple mctx mref cctx cref (JQH O E D) (sparkleChildCache.get : MetaM _)
      (fun m w => JQH O E D w ∧ m = cv w) (EQH O E D) := by
  intro w hw
  have hK := keeps_iff.mp (keepsH_framed O hA D FramedA.cacheGet) w hw
  cases hm : (sparkleChildCache.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    obtain ⟨ha, hw1⟩ := jqh_cacheGet O hA hw hm
    exact ⟨hw1, ha⟩
  | error e w1 => rw [hm] at hK; exact hK

/-- **Cache initialisation**: the depth-0 clear establishes the history invariant from `JQ` (the cache becomes `{}`) -/
theorem tripleH_clear (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ O.quiet D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => JQH O E D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.cacheSet hA _ _ _ _ h hw.1
    refine ⟨⟨O.cacheSetQ hA _ _ _ _ h hw.1, hk.2.1.trans hw.2.1, hk.2.2.trans hw.2.2⟩, ?_⟩
    rw [hk.1]; exact cacheE_empty O E

theorem tripleH_clear' (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQH O E D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => JQH O E D) R :=
  Triple.conseq (tripleH_clear O hA D) (fun _ h => h.1) (fun _ _ h => h) (fun _ _ h => h)

theorem tripleH_depthSet (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    (D v : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQH O E D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => JQH O E v) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.depthSet hA _ _ _ _ h hw.1.1
    refine ⟨⟨O.depthSetQ hA _ _ _ _ h hw.1.1, hk.2.1.trans hw.1.2.1, hk.2.2⟩, ?_⟩
    rw [hk.1]; exact hw.2

theorem tripleH_depthModify (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    (D : Nat) (f : Nat → Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQH O E D) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => JQH O E (f D)) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw h => by
    have hk := O.depthModify' hA f hw.1.1 h
    have hq' : O.quiet w' := by
      obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
      have hq1 := O.frameQ hA _ FramedA.depthGet w hw.1.1
      rw [endW_of_runs hg] at hq1
      exact O.depthSetQ hA _ _ _ _ hs hq1
    refine ⟨⟨hq', hk.2.1.trans hw.1.2.1, ?_⟩, ?_⟩
    · rw [hk.2.2, hw.1.2.2]
    · rw [hk.1]; exact hw.2

/-- **The miss insert keeps the invariant** when the inserted entry carries its saved reads -/
theorem jqh_insert_runs (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    {D : Nat} {n : Name} {r : Res} {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (hw : JQH O E D w) (hr : RealChildE O E n r)
    (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert n r) :
      MetaM Unit) mctx mref cctx cref w u w') :
    JQH O E D w' := by
  have hk := O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw.1.1 h
  have hq' : O.quiet w' := by
    obtain ⟨w1, hg, hs⟩ := modify_split sparkleChildCache
      (fun m : Std.HashMap Name Res => m.insert n r) h
    have hq1 := O.frameQ hA _ FramedA.cacheGet w hw.1.1
    rw [endW_of_runs hg] at hq1
    exact O.cacheSetQ hA _ _ _ _ hs hq1
  refine ⟨⟨hq', hk.2.1.trans hw.1.2.1, hk.2.2.trans hw.1.2.2⟩, ?_⟩
  rw [hk.1]; exact cacheE_insert hw.2 hr

/-! ## the memoised child entry: hit takes the evidence out, miss saves it -/

/-- **`synthesizeChild` as a triple under `JQH`, on every outcome.** Hit: the returned value is the cache's entry, a `RealChildE` (its saved reads are read from the entry). Miss: the nested run starts in a `JQH` world with no entry for `n`; the miss premise gives `E` for it, so its result is a `RealChildE`; the insert keeps `JQH`. Premise `hentryT`: the nested real entry keeps `JQH` (derived below from the body premise). -/
theorem synthesizeChild_tripleH (O : RefLawsAOps MkRefd mref cref) {E : StartEv}
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D) (hmiss : MissE O E) {n : Name}
    (hentryT : Triple mctx mref cctx cref (JQH O E D) (synthesizeCombinational n)
      (fun _ => JQH O E D) (EQH O E D)) :
    Triple mctx mref cctx cref (JQH O E D) (synthesizeChild n)
      (fun r w => RealChildE O E n r ∧ JQH O E D w) (EQH O E D) := by
  unfold synthesizeChild
  refine Triple.bind (tripleH_cacheGet O hA D) ?_
  intro m
  cases hc : m.get? n with
  | some r =>
    try dsimp only
    exact Triple.pure fun w hw => ⟨by rw [hw.2] at hc; exact hw.1.2 n r hc, hw.1⟩
  | none =>
    try dsimp only
    refine Triple.conseq (P := fun w => JQH O E D w ∧ (cv w).get? n = none) ?_
      (fun _ hw => ⟨hw.1, by rw [← hw.2]; exact hc⟩) (fun _ _ h => h) (fun _ _ h => h)
    refine Triple.bind (triple_withRun
      (Triple.conseq (P' := fun w => JQH O E D w ∧ (cv w).get? n = none) hentryT (fun _ hw => hw.1) (fun _ _ h => h) (fun _ _ h => h))) ?_
    intro r
    refine Triple.bind (Q := fun _ w => JQH O E D w ∧ RealChildE O E n r) ?_
      (fun _ => Triple.pure fun w hw => ⟨hw.2, hw.1⟩)
    refine Triple.of_runs (refModify_runs _ _) fun w u w' hw h => ?_
    obtain ⟨hw2, w1, hw1, hrun⟩ := hw
    have hr : RealChildE O E n r :=
      RealChildE.run mctx cctx w1 _ hA hw1.1.2 hw1.1.1.2.1 hw1.1.1.1 hrun (hmiss mctx cctx hA D hD n w1 hw1.1 hw1.2)
    exact ⟨jqh_insert_runs O hA hw2 hr h, hr⟩

/-- A set of another per-synthesis ref under `JQH` (a `FramedA.sideSet`). -/
macro "hset " O:term:max hA:term:max E:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableA_JQH $O $E $D)
      (FramedA.sideSet _ ?s))) ?_
   case s => constructor
   intro _))
/-- A read of another per-synthesis ref under `JQH` (a `FramedA.sideGet`). -/
macro "hget " O:term:max hA:term:max E:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableA_JQH $O $E $D)
      (FramedA.sideGet ?s))) ?_
   case s => constructor
   intro _))
/-- A `pure` under `JQH`. -/
macro "hpure " O:term:max E:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.pure (Q := fun _ => JQH $O $E $D) (fun w hw => hw)) ?_; intro _))

/-- The `finally` of the entry under `JQC`: from depth `d + 1` back to `d`;
the nested-restore branch (if taken) is seven framed sets. -/
theorem finH (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv} (d : Nat)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (JQH O E (d + 1))
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
      (fun _ => JQH O E d) (EQH O E d) := by
  refine Triple.bind (Triple.conseq (tripleH_depthModify O hA (d + 1) (fun x => x - 1))
    (fun _ h => h) (Q' := fun _ => JQH O E d)
    (fun _ w h => by show JQH O E d w; have h' : JQH O E (d + 1 - 1) w := h
                     rw [Nat.add_sub_cancel] at h'; exact h')
    (fun _ _ h => h)) ?_
  intro _
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d
  exact keeps_iff.mp (keepsA_framed O hA (stableA_JQH O E d) (FramedA.sideSet _ .singleOut))

/-- **The core entry keeps `JQC` at every depth, on every outcome.** The only
premise: `hbodyH`, the body keeps `JQH O E (D + 1)` below the depth limit. -/
theorem core_tripleAH (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    (D : Nat) (declName : Name)
    (hbodyH : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQH O E (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQH O E D) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQH O E D) (EQH O E D) := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQH O E D) (FramedA.ioEnv _))) ?_
  intro prof
  refine Triple.bind (keeps_iff.mp (keepsA_diag O hA (stableA_JQH O E D)
    (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.conseq (tripleA_depthGet O hA (stableA_JQH O E D)) (fun _ h => h)
      (Q' := fun d w => JQH O E D w ∧ d = D)
      (fun _ _ h => ⟨h.1, h.2.trans h.1.1.2.2⟩) (fun _ _ h => h)) ?_
  intro d hd
  subst hd  -- guess: K2
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · -- at the limit: the entry throws before touching the depth
    refine Triple.bind (Q := fun _ _ => False)
      (tripleA_throwErr O hA (stableA_JQH O E d) _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : d < sparkleSynthDepthLimit := Nat.lt_of_not_ge hlt
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (JQH O E (d + 1))
          (_root_.tryFinally
            (do
              let constInfo ← getConstInfo declName
              let env ← getEnv
              if (entryInlinerError? env true false [] constInfo (instancePredicate env)).isSome then
                throwError (stringToMessageData s!"{declName}: {(entryInlinerError? env true false []
                  constInfo (instancePredicate env)).getD ""}")
              else
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
          (fun _ => JQH O E d) (EQH O E d) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := JQH O E (d + 1)) (E := OkExc) ?_
        (finH O hA d m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQH O E (d + 1))
        (FramedA.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQH O E (d + 1))
        FramedA.env)) ?_
      intro env
      refine Triple.ite (fun _ => ?_) (fun _ => ?_)
      · exact tripleA_throwErr O hA (stableA_JQH O E (d + 1)) _ (by first | exact .str _ | exact .fmt _)
      · exact keeps_iff.mp (hbodyH hlt prof.isSome _ _)
    by_cases h0 : (d == 0) = true
    · -- outermost: the cache is cleared, the cache half re-established
      simp only [h0, ↓reduceIte]
      hpure O E d; hpure O E d; hpure O E d; hpure O E d; hpure O E d; hpure O E d; hpure O E d
      hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d
      refine Triple.bind (tripleH_clear' O hA d) ?_
      intro _
      hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d
      refine Triple.bind (tripleH_depthSet O hA d (d + 1)) ?_
      intro _
      exact body _ _ _ _ _ _ _  -- guess: K4
    · -- nested: the parent's maps are read (and restored in the `finally`), no clear
      simp only [h0, Bool.false_eq_true, ↓reduceIte]  -- guess: K3
      hget O hA E d; hget O hA E d; hget O hA E d; hget O hA E d; hget O hA E d; hget O hA E d; hget O hA E d
      hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d; hset O hA E d
      refine Triple.bind (tripleH_depthSet O hA d (d + 1)) ?_
      intro _
      exact body _ _ _ _ _ _ _

/-- The full entry: the core, then one environment-variable read and pure
post-processing. -/
theorem full_tripleAH (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    {D : Nat} {declName : Name}
    (hcore : Triple mctx mref cctx cref (JQH O E D) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQH O E D) (EQH O E D)) :
    Triple mctx mref cctx cref (JQH O E D) (synthesizeCombinational declName)
      (fun _ => JQH O E D) (EQH O E D) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind hcore ?_
  rintro ⟨m, dd⟩
  dsimp only
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableA_JQH O E D) (FramedA.ioEnv _))) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)


/-! ## the endpoints with the body premise in place of the entry premise -/

theorem hentryT_of_bodyH (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {E : StartEv}
    {D : Nat} {c : Name}
    (hbodyH : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQH O E (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQH O E D) (synthesizeCombinational c)
      (fun _ => JQH O E D) (EQH O E D) :=
  full_tripleAH O hA (core_tripleAH O hA D c @hbodyH)

/-- **`synthesizeChild` under `JQH`, cache hit and miss, from the body premise** (and the miss premise) -/
theorem synthesizeChild_tripleH' (O : RefLawsAOps MkRefd mref cref) {E : StartEv}
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D) (hmiss : MissE O E) {n : Name}
    (hbodyH : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQH O E (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          n [] false true ci isInst)) :
    Triple mctx mref cctx cref (JQH O E D) (synthesizeChild n)
      (fun r w => RealChildE O E n r ∧ JQH O E D w) (EQH O E D) :=
  synthesizeChild_tripleH O hA hD hmiss (hentryT_of_bodyH O hA @hbodyH)

theorem synthesizeChild_realH' (O : RefLawsAOps MkRefd mref cref) {E : StartEv}
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D) (hmiss : MissE O E) {n : Name}
    (hbodyH : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JQH O E (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          n [] false true ci isInst))
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQH O E D w)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    RealChildE O E n y ∧ JQH O E D w' :=
  runs_of_triple (synthesizeChild_tripleH' O hA hD hmiss @hbodyH) hw h

end Tools.ShippingFGCircuitS2hHist

#print axioms Tools.ShippingFGCircuitS2hHist.synthesizeChild_tripleH
#print axioms Tools.ShippingFGCircuitS2hHist.core_tripleAH
#print axioms Tools.ShippingFGCircuitS2hHist.synthesizeChild_realH'
