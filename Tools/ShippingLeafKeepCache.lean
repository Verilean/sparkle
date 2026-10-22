import Tools.ShippingLeafMissCoh
import Tools.ShippingChildCoreC
import Tools.ShippingSeqChildIface
import Tools.ShippingMachineCloses
import Tools.ShippingMachineAuto
import Tools.ShippingMixedEntrySoundness
import Tools.ShippingGateChildComb
-- BUILT at the final committed SHA: see REPORT-SR5.md for run names / exits (k1,k2 exit 1; k3 exit 0 on the pre-header-edit tree).
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # `hkeep` split by depth (unit SR5, L8ak)

`hkeep` of `Tools.ShippingLeafMissCoh.synthesizeChild_leafMiss` says that the nested run
`synthesizeCombinational n` leaves the cache VALUE alone (`cv w2 = cv w`). The entry
`synthesizeCombinationalCore` treats the cache by depth:

* depth `D ≠ 0` (nested): NO clear — seven framed reads, seven framed sets of OTHER refs, the depth bump, the
  body, the `finally` (depth back, seven framed sets of other refs), and pure post-processing;
* depth `D = 0` (outermost): the cache is SET to `{}` before the body.

`JK O D c0 := JQC O D ∧ cv = c0` is a stable invariant (`stableK`). PROVED here, from the existing laws only:
* `core_tripleK` / `full_tripleK` (D ≠ 0): everything in the entry OTHER than the body keeps `JK O D c0`,
  i.e. keeps the cache value, so `cv` at the end of the run is `cv` at the start iff the BODY keeps it;
* `core_tripleK0` / `full_tripleK0` (D = 0): the entry establishes `cv = {}` and everything other than the body
  keeps it.
The single remaining premise of each is the BODY (`hbodyK`/`hbodyK0`): `synthesizeFromConst …` keeps the cache
value. That is NOT derived here: the body is where `synthesizeChild` (hence a cache insert) can occur, and the
facts of the existing boundary track `JQC` (a cache of real children), not the cache value, across the body.
Hence the exact statement that holds is "entry prefix / `finally` / post-processing are cache-neutral at D ≠ 0 and
cache-clearing at D = 0; the body is the only place a leaf run could extend the cache". -/

namespace Tools.ShippingLeafKeepCache
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildCoreC
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingSeqChildIface Tools.ShippingSeqChildIfaceA
open Tools.ShippingMachineCloses
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
  {Fresh : (σ : Type) → IO.Ref σ → Prop}

/-- `JQC` with the cache VALUE fixed to `c0`. -/
def JK (O : RefLawsAOps Fresh mref cref) (D : Nat) (c0 : Std.HashMap Name Res)
    (w : Void IO.RealWorld) : Prop :=
  JQC O D w ∧ cv w = c0

theorem stableK (O : RefLawsAOps Fresh mref cref) (D : Nat) (c0 : Std.HashMap Name Res) :
    StableA O.quiet (JK O D c0) :=
  ⟨fun _ h => h.1.1.1, fun w w' hc hs hd hq h =>
    ⟨(stableA_JQC O D).2 w w' hc hs hd hq h.1, hc.trans h.2⟩⟩

/-- Setting the depth keeps `JK` (at the new depth). -/
theorem tripleK_depthSet (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D v : Nat) (c0 : Std.HashMap Name Res) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JK O D c0) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => JK O v c0) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.depthSet hA _ _ _ _ h hw.1.1.1
    refine ⟨⟨⟨O.depthSetQ hA _ _ _ _ h hw.1.1.1, hk.2.1.trans hw.1.1.2.1, hk.2.2⟩, ?_⟩, ?_⟩
    · rw [hk.1]; exact hw.1.2
    · rw [hk.1]; exact hw.2

/-- Modifying the depth keeps `JK` (at `f D`). -/
theorem tripleK_depthModify (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (f : Nat → Nat) (c0 : Std.HashMap Name Res)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JK O D c0) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => JK O (f D) c0) R :=
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
    · rw [hk.1]; exact hw.2

/-- **The depth-0 clear establishes `cv = {}`** (and the cache half) from `JQ`. -/
theorem tripleK_clear (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ O.quiet D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => JK O D {}) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.cacheSet hA _ _ _ _ h hw.1
    refine ⟨⟨⟨O.cacheSetQ hA _ _ _ _ h hw.1, hk.2.1.trans hw.2.1, hk.2.2.trans hw.2.2⟩, ?_⟩, hk.1⟩
    rw [hk.1]; exact cacheInvA_empty O

macro "kset " O:term:max hA:term:max D:term:max c0:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableK $O $D $c0)
      (FramedA.sideSet _ ?s))) ?_
   case s => constructor
   intro _))
macro "kget " O:term:max hA:term:max D:term:max c0:term:max : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsA_framed $O $hA (stableK $O $D $c0)
      (FramedA.sideGet ?s))) ?_
   case s => constructor
   intro _))
macro "kpure " O:term:max D:term:max c0:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.pure (Q := fun _ => JK $O $D $c0) (fun w hw => hw)) ?_; intro _))

/-- The `finally` of the entry under `JK`. -/
theorem finK (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx) (d : Nat)
    (c0 : Std.HashMap Name Res)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (JK O (d + 1) c0)
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
      (fun _ => JK O d c0) (fun e w => JK O d c0 w ∧ OkExc e) := by
  refine Triple.bind (Triple.conseq (tripleK_depthModify O hA (d + 1) (fun x => x - 1) c0)
    (fun _ h => h) (Q' := fun _ => JK O d c0)
    (fun _ w h => by show JK O d c0 w; have h' : JK O (d + 1 - 1) c0 w := h
                     rw [Nat.add_sub_cancel] at h'; exact h')
    (fun _ _ h => h)) ?_
  intro _
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  kset O hA d c0; kset O hA d c0; kset O hA d c0; kset O hA d c0; kset O hA d c0; kset O hA d c0
  exact keeps_iff.mp (keepsA_framed O hA (stableK O d c0) (FramedA.sideSet _ .singleOut))

/-- **Nested entry (`D ≠ 0`) keeps the cache value; the body is the only premise.** -/
theorem core_tripleK (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (D : Nat) (hD : D ≠ 0) (c0 : Std.HashMap Name Res) (declName : Name)
    (hbodyK : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JK O (D + 1) c0)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
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
  · have hlt : d < sparkleSynthDepthLimit := Nat.lt_of_not_ge hlt
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
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
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableK O (d + 1) c0)
        (FramedA.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableK O (d + 1) c0)
        FramedA.env)) ?_
      intro env
      exact keeps_iff.mp (hbodyK hlt prof.isSome _ _)
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

/-- A `Keeps` as a triple whose exceptional outcome is not tracked. -/
theorem keepsT {I : Void IO.RealWorld → Prop} {α : Type} {p : MetaM α}
    (h : Keeps mctx mref cctx cref I p) :
    Triple mctx mref cctx cref I p (fun _ => I) (fun _ _ => True) :=
  Triple.conseq (keeps_iff.mp h) (fun _ h => h) (fun _ _ h => h) (fun _ _ _ => trivial)

macro "qset " O:term:max hA:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (keepsT (keepsA_framed $O $hA (stableA_JQC $O $D)
      (FramedA.sideSet _ ?s))) ?_
   case s => constructor
   intro _))
macro "qpure " O:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (Triple.pure (Q := fun _ => JQC $O $D) (fun w hw => hw)) ?_; intro _))
macro "k0set " O:term:max hA:term:max D:term:max : tactic => `(tactic|
  (refine Triple.bind (keepsT (keepsA_framed $O $hA (stableK $O $D {})
      (FramedA.sideSet _ ?s))) ?_
   case s => constructor
   intro _))

/-- **Outermost entry (`D = 0`) ends with `cv = {}` before the body; the body is the only premise.** From
`JQC O 0` (the entry clears the cache; exceptional outcomes are not tracked, the limit branch is closed by
`sparkleSynthDepthLimit = 1024`). -/
theorem core_tripleK0 (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (declName : Name)
    (hbodyK : ∀ {tenv : Lean.Environment}, ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JK O 1 {})
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
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
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableK O (0 + 1) {})
        (FramedA.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableK O (0 + 1) {})
        FramedA.env)) ?_
      intro env
      exact keeps_iff.mp (hbodyK prof.isSome _ _)
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

/-- The full entry at `D ≠ 0`: the core, one environment read, pure post-processing. -/
theorem full_tripleK (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {c0 : Std.HashMap Name Res} {declName : Name}
    (hcore : Triple mctx mref cctx cref (JK O D c0) (synthesizeCombinationalCore declName [] false)
      (fun _ => JK O D c0) (fun e w => JK O D c0 w ∧ OkExc e)) :
    Triple mctx mref cctx cref (JK O D c0) (synthesizeCombinational declName)
      (fun _ => JK O D c0) (fun e w => JK O D c0 w ∧ OkExc e) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind hcore ?_
  rintro ⟨m, dd⟩
  dsimp only
  refine Triple.bind (keeps_iff.mp (keepsA_framed O hA (stableK O D c0) (FramedA.ioEnv _))) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-- The full entry at `D = 0`. -/
theorem full_tripleK0 (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name}
    (hcore : Triple mctx mref cctx cref (JQC O 0) (synthesizeCombinationalCore declName [] false)
      (fun _ => JK O 0 {}) (fun _ _ => True)) :
    Triple mctx mref cctx cref (JQC O 0) (synthesizeCombinational declName)
      (fun _ => JK O 0 {}) (fun _ _ => True) := by
  unfold synthesizeCombinational synthesizeCombinationalWith
  refine Triple.bind hcore ?_
  rintro ⟨m, dd⟩
  dsimp only
  refine Triple.bind (keepsT (keepsA_framed O hA (stableK O 0 {}) (FramedA.ioEnv _))) ?_
  intro x
  exact Triple.ite (fun _ => Triple.pure fun w hw => hw) (fun _ => Triple.pure fun w hw => hw)

/-- **(a) `hkeep` at `D ≠ 0`, reduced to the body.** -/
theorem hkeep_nested (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {n : Name}
    (hbodyK : ∀ (c0 : Std.HashMap Name Res) {tenv : Lean.Environment},
      D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JK O (D + 1) c0)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          n [] false true ci isInst)) :
    ∀ w1 r1 w2, JQC O D w1 →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      JQC O D w2 ∧ cv w2 = cv w1 := by
  intro w1 r1 w2 hw1 hrun
  have hT := full_tripleK O hA (core_tripleK O hA D hD (cv w1) n (@hbodyK (cv w1)))
  exact runs_of_triple hT ⟨hw1, rfl⟩ hrun

/-- **(b) the run at `D = 0`**: after the run the cache VALUE is `{}`, whatever the start cache was. -/
theorem hkeep_zero (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx) {n : Name}
    (hbodyK : ∀ {tenv : Lean.Environment}, ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JK O 1 {})
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          n [] false true ci isInst)) :
    ∀ w1 r1 w2, JQC O 0 w1 →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 →
      JQC O 0 w2 ∧ cv w2 = {} := by
  intro w1 r1 w2 hw1 hrun
  have hT := full_tripleK0 O hA (core_tripleK0 O hA n @hbodyK)
  exact runs_of_triple hT hw1 hrun

/-! ## Plugged into the leaf-miss consumer -/

/-- The cache read leaves the cache value: `cv w1 = cv w` (the frame law at `FramedA.cacheGet`). -/
theorem cacheGet_cv (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {w : Void IO.RealWorld} {m : Std.HashMap Name Res} {w1 : Void IO.RealWorld}
    (hw : JQC O D w)
    (h : RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1) : cv w1 = cv w := by
  have hk := O.frame hA _ FramedA.cacheGet w hw.1.1
  rw [endW_of_runs h] at hk
  exact hk.1

/-- **(a) `synthesizeChild_leafMiss` at `D ≠ 0` with `hentry`/`hkeep` replaced by the body premise `hbodyK`.**
Remaining premises: `hbodyK` (the body keeps the cache value), the start-cache clauses `hcl`/`hk`/`hmiss`, and
the data premises of `seqChild_of_realA`. -/
theorem synthesizeChild_leafMiss_nested (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : D ≠ 0) {n : Name}
    (hbodyK : ∀ (c0 : Std.HashMap Name Res) {tenv : Lean.Environment},
      D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JK O (D + 1) c0)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          n [] false true ci isInst))
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
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
    obtain ⟨hw2, hk2⟩ := hkeep_nested O hA hD hbodyK w1 r w2 hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    have hc3 := (O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw2.1.1 hmod).1
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    rw [hc3, hk2, hc1]
    exact leafMiss_cacheCoh hcl hk hmiss hI.name hI.design

/-- **(b) `synthesizeChild` leaf miss at `D = 0`.** The entry clears the cache, so NO start-cache clause is needed
for `CacheClosed`/`KeyTop`/`CohWith`: the cache before the insert is `{}`. Premises: `hmiss` (miss branch),
`hbodyK0` (the body keeps `cv = {}`), and the data premises of `seqChild_of_realA`. -/
theorem synthesizeChild_leafMiss_zero (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {n : Name}
    (hbodyK : ∀ {tenv : Lean.Environment}, ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (JK O 1 {})
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          n [] false true ci isInst))
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
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
    obtain ⟨hw2, hk2⟩ := hkeep_zero O hA hbodyK w1 r w2 hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    have hc3 := (O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw2.1.1 hmod).1
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    rw [hc3, hk2]
    have hmiss0 : ({} : Std.HashMap Name Res).get? n = none := by simp
    obtain ⟨a, b, c, e⟩ := leafMiss_cacheCoh cacheClosed_empty keyTop_empty hmiss0 hI.name hI.design
    exact ⟨rfl, a, b, c, e⟩

end Tools.ShippingLeafKeepCache

#print axioms Tools.ShippingLeafKeepCache.core_tripleK
#print axioms Tools.ShippingLeafKeepCache.core_tripleK0
#print axioms Tools.ShippingLeafKeepCache.hkeep_nested
#print axioms Tools.ShippingLeafKeepCache.hkeep_zero
#print axioms Tools.ShippingLeafKeepCache.synthesizeChild_leafMiss_nested
#print axioms Tools.ShippingLeafKeepCache.synthesizeChild_leafMiss_zero
