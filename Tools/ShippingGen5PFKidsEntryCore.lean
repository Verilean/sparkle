-- Gen5 port of Tools.ShippingGen4FKidsEntryCore (scripts/gen4/PARAM_ASSEMBLY.md §Gen5): copy for the gen5 Elab; only the marked parts differ.
import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4KWalkEntry
import Tools.ShippingGen4FKidsEntry
import Tools.ShippingGen4FKidsEntryArms
import Tools.ShippingGen5PKWalkEntryCore
namespace Tools.ShippingGen4FKidsEntryCore
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
open Tools.ShippingChildFrontA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4FKidsEntry

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

-- F-kids StatePF walk: the entry `synthesizeCombinationalCoreWith` (nested and outermost) for the PF world `KPF`/`KPFX`. Port of Tools.ShippingGen4KWalkEntryCore; the generic lemmas (try/finally, depth, framed sets, resets) are reused from there. Takes `MemoFamily` as a HYPOTHESIS `M`; adds NO premise. No sorry.
open Tools.ShippingGen4KWalkEntryCore
open Tools.ShippingGen4FKidsEntryArms

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `try x finally fin`, with different post-conditions for a returning and a throwing `x`; `fin` never throws. -/
theorem tryFinallySplitQ {α β : Type} {P Me : Void IO.RealWorld → Prop} {Q : α → Void IO.RealWorld → Prop} {E : Exception → Prop}
    {x : MetaM α} {fin : MetaM β}
    (hx : Triple mctx mref cctx cref P x Q (fun e w => Me w ∧ E e))
    (hfo : ∀ a, Triple mctx mref cctx cref (Q a) fin (fun _ => Q a) (fun _ _ => False))
    (hfe : Triple mctx mref cctx cref Me fin (fun _ => Me) (fun _ _ => False)) :
    Triple mctx mref cctx cref P (_root_.tryFinally x fin) Q (fun e w => Me w ∧ E e) := by
  intro w hw
  have h1 := hx w hw
  change match (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w with
    | .ok a w' => Q a w' | .error e w' => Me w' ∧ E e
  unfold EST.bind
  simp only [MonadFinally.tryFinally']
  cases hxw : x mctx mref cctx cref w with
  | ok a w1 =>
    rw [hxw] at h1
    have h2 := hfo a w1 h1
    dsimp only
    cases hfw : fin mctx mref cctx cref w1 with
    | ok b w2 => rw [hfw] at h2; simpa [EST.pure] using h2
    | error e' w2 => rw [hfw] at h2; exact h2.elim
  | error e w1 =>
    rw [hxw] at h1
    have h2 := hfe w1 h1.1
    dsimp only
    cases hfw : fin mctx mref cctx cref w1 with
    | ok b w2 => rw [hfw] at h2; simpa [EST.pure] using ⟨h2, h1.2⟩
    | error e' w2 => rw [hfw] at h2; exact h2.elim

theorem triple_constConj {α : Type} {P Q : Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    {m : MetaM α} (φ : Prop) (h : Triple mctx mref cctx cref P m (fun _ => Q) R) :
    Triple mctx mref cctx cref (fun w => P w ∧ φ) m (fun _ w => Q w ∧ φ) R := by
  intro w hw
  have h1 := h w hw.1
  cases hm : m mctx mref cctx cref w with
  | ok a w1 => rw [hm] at h1; exact ⟨h1, hw.2⟩
  | error e w1 => rw [hm] at h1; exact h1

section Core
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- The child-cache reset `set v` from an empty memo: afterwards the memo is empty and the child cache is `v`. -/
theorem triple_childResetPS (v : Std.HashMap Name Res) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KW O (fun m _ => m = {})) (sparkleChildCache.set v : MetaM Unit)
      (fun _ => KW O (fun m c => m = {} ∧ c = v)) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.cacheSet hA v w u w' h hw.1
    have hm := M.frameCacheSet hA v w u w' h hw.1
    refine ⟨O.cacheSetQ hA v w u w' h hw.1, hk.2.1.trans hw.2.1, ?_⟩
    rw [hm]
    exact ⟨hw.2.2, hk.1⟩

omit M hA in
theorem stableK_KDS : StableK O.quiet (fun w => KPF O w ∧ dv w ≠ 0) :=
  ⟨fun _ h => h.1.1, fun w w' hc hs hd hm hq h => ⟨kw_transfer hc hs hm hq h.1, by rw [hd]; exact h.2⟩⟩

/-- The depth read, under `KWalk ∧ dv ≠ 0`: returns a nonzero depth, keeps `KWalk` (it cannot throw). -/
theorem tripleK_depthGetNZS {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (fun w => KPF O w ∧ dv w ≠ 0) (ST.Ref.get sparkleSynthDepth : MetaM Nat)
      (fun d w => KPF O w ∧ d ≠ 0) R :=
  Triple.of_runs (refGet_runs _) fun w a w' hw h => by
    have hK := keepsK_framedNM M hA (stableK_KDS (O := O)) FramedNM.depthGet w hw
    rw [endW_of_runs h] at hK
    have ha : a = dv w := runsTo_get_readOf _ h
    exact ⟨hK.1.1, by rw [ha]; exact hw.2⟩

set_option hygiene false in
macro "kgetP" : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KPF O)
      (FramedNM.sideGet ?s))) ?_
   case s => constructor
   intro _))
set_option hygiene false in
macro "ksetP" : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KPF O)
      (FramedNM.sideSet _ ?s))) ?_
   case s => constructor
   intro _))

/-- **The entry for a nested run** (`depth ≠ 0`), from the arm `hbody` (K to K_declName, K on failure). -/
theorem entryNested_windowPS (hlog : LogMvKS O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (hbody : ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (KPF O)
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
        (fun r w => KPFX O declName w ∧ PairPF r) (fun e w => KPF O w ∧ OkExc e)) :
    Triple mctx mref cctx cref (fun w => KPF O w ∧ dv w ≠ 0)
      (synthesizeCombinationalCoreWith translate declName [] false true)
      (fun r w => KPFX O declName w ∧ PairPF r) (fun e w => KPF O w ∧ OkExc e) := by
  unfold synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (R := fun e w => KPF O w ∧ OkExc e) (Q := fun _ w => KPF O w ∧ dv w ≠ 0)
    (Triple.conseq (keeps_iff.mp (keepsK_framedNM M hA (stableK_KDS (O := O)) (FramedNM.ioEnv _)))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
  intro prof
  refine Triple.bind (R := fun e w => KPF O w ∧ OkExc e) (Q := fun _ w => KPF O w ∧ dv w ≠ 0)
    (Triple.conseq (keeps_iff.mp (keepsK_profLogS M hA (stableK_KDS (O := O)) hlog prof.isSome _))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d ≠ 0) (tripleK_depthGetNZS M hA) ?_
  intro d hd
  refine Triple.ite (fun _ => ?_) (fun _ => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleK_throwErr M hA (stableK_KPF O) _
        (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have h0 : (d == 0) = false := by simpa using hd
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    kgetP; kgetP; kgetP; kgetP; kgetP; kgetP; kgetP
    ksetP; ksetP; ksetP; ksetP; ksetP; ksetP; ksetP
    refine Triple.bind (triple_depthSetK M hA (fun m c => MemoKeysInChild m c ∧ CachePF m ∧ CachePF c) (d + 1)) ?_
    intro _
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (KPF O)
          (_root_.tryFinally
            (do
              let constInfo ← getConstInfo declName
              let env ← getEnv
              if (entryInlinerError? env true false [] constInfo (instancePredicate env)).isSome then
                throwError (stringToMessageData s!"{declName}: {(entryInlinerError? env true
                  false [] constInfo (instancePredicate env)).getD ""}")
              else
              synthesizeFromConst (translate env) (profLogIO prof.isSome) declName [] false true
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
          (fun r w => KPFX O declName w ∧ PairPF r) (fun e w => KPF O w ∧ OkExc e) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine tryFinallySplitQ (Q := fun r w => KPFX O declName w ∧ PairPF r) (Me := KPF O) (E := OkExc) ?_
        (fun a => triple_constConj (PairPF a)
          (fin_totalK M hA (fun m c => MemoKeysExc declName m c ∧ CachePF m ∧ CachePF c) d m1 m2 m3 m4 m5 m6 m7))
        (fin_totalK M hA (fun m c => MemoKeysInChild m c ∧ CachePF m ∧ CachePF c) d m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KPF O)
        (FramedNM.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KPF O)
        FramedNM.env)) ?_
      intro env
      refine Triple.ite (fun _ => ?_) (fun _ => ?_)
      · exact tripleK_throwErr M hA (stableK_KPF O)
          (stringToMessageData s!"{declName}: {(entryInlinerError? env true
            false [] ci (instancePredicate env)).getD ""}") (OkMsg.str _)
      · exact hbody prof.isSome env _ _
    exact body _ _ _ _ _ _ _

/-! ## The outermost run (depth 0): the resets re-establish K -/

omit M hA in
theorem kw_weak {P : Std.HashMap Name Res → Std.HashMap Name Res → Prop} {w : Void IO.RealWorld}
    (h : KW O P w) : KW O (fun _ _ => True) w := ⟨h.1, h.2.1, trivial⟩

omit M hA in
theorem stableK_I0 : StableK O.quiet (fun w => KW O (fun _ _ => True) w ∧ dv w = 0) :=
  ⟨fun _ h => h.1.1, fun w w' hc hs hd hm hq h =>
    ⟨kw_transfer (P := fun _ _ => True) hc hs hm hq h.1, by rw [hd]; exact h.2⟩⟩

/-- The depth read at depth 0. -/
theorem tripleK_depthGetZ {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (fun w => KW O (fun _ _ => True) w ∧ dv w = 0)
      (ST.Ref.get sparkleSynthDepth : MetaM Nat)
      (fun d w => KW O (fun _ _ => True) w ∧ d = 0) R :=
  Triple.of_runs (refGet_runs _) fun w a w' hw h => by
    have hK := keepsK_framedNM M hA (stableK_I0 (O := O)) FramedNM.depthGet w hw
    rw [endW_of_runs h] at hK
    have ha : a = dv w := runsTo_get_readOf _ h
    exact ⟨hK.1.1, by rw [ha]; exact hw.2⟩

/-- The memo reset `set {}`: the memo is empty afterwards, whatever the child cache is. -/
theorem triple_memoResetK (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KW O P) (sparkleSubModuleCache.set {} : MetaM Unit)
      (fun _ => KW O (fun m _ => m = {})) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    obtain ⟨hq, hc, hs, hm⟩ := memoSet_ctx M hA {} h hw.1
    exact ⟨hq, hs.trans hw.2.1, hm⟩

/-- The child-cache reset `set {}` keeps a predicate that does not look at the child cache. -/
theorem triple_childResetK (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop)
    (hP : ∀ m c c', P m c → P m c') (v : Std.HashMap Name Res) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KW O P) (sparkleChildCache.set v : MetaM Unit) (fun _ => KW O P) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.cacheSet hA v w u w' h hw.1
    have hm := M.frameCacheSet hA v w u w' h hw.1
    refine ⟨O.cacheSetQ hA v w u w' h hw.1, hk.2.1.trans hw.2.1, ?_⟩
    rw [hm]
    exact hP _ _ _ hw.2.2

set_option hygiene false in
macro "kset0" : tactic => `(tactic|
  (refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e) (Triple.conseq
      (keeps_iff.mp (keepsK_framedNM M hA (stableK_KW O _) (FramedNM.sideSet _ ?s)))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨kw_weak h.1, h.2⟩)) ?_
   case s => constructor
   intro _))
set_option hygiene false in
macro "kpure0" : tactic => `(tactic|
  (refine Triple.bind (Triple.pure (Q := fun _ w => KW O (fun _ _ => True) w) (fun w hw => hw)) ?_; intro _))

/-- **The entry for an outermost run** (`depth = 0`): the resets empty the memo (and the child cache), so K holds
afterwards whatever the start world; the rest is `entryNested`. Failure leaves only quietness and the synthesis ref. -/
theorem entryTop_windowPS (hlog : LogMvKS O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (hbody : ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (KPF O)
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
        (fun r w => KPFX O declName w ∧ PairPF r) (fun e w => KPF O w ∧ OkExc e)) :
    Triple mctx mref cctx cref (fun w => KW O (fun _ _ => True) w ∧ dv w = 0)
      (synthesizeCombinationalCoreWith translate declName [] false true)
      (fun r w => KPFX O declName w ∧ PairPF r) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) := by
  unfold synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e)
    (Q := fun _ w => KW O (fun _ _ => True) w ∧ dv w = 0)
    (Triple.conseq (keeps_iff.mp (keepsK_framedNM M hA (stableK_I0 (O := O)) (FramedNM.ioEnv _)))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
  intro prof
  refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e)
    (Q := fun _ w => KW O (fun _ _ => True) w ∧ dv w = 0)
    (Triple.conseq (keeps_iff.mp (keepsK_profLogS M hA (stableK_I0 (O := O)) hlog prof.isSome _))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = 0) (tripleK_depthGetZ M hA) ?_
  intro d hd
  subst hd
  refine Triple.ite (fun _ => ?_) (fun _ => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleK_throwErr M hA (stableK_KW O (fun _ _ => True)) _
        (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have h0 : (0 == 0) = true := rfl
    simp only [h0, ↓reduceIte]
    kpure0; kpure0; kpure0; kpure0; kpure0; kpure0; kpure0
    kset0; kset0; kset0
    refine Triple.bind (Triple.conseq (triple_memoResetK M hA (fun _ _ => True)) (fun _ h => h)
      (fun _ _ h => h) (fun _ _ h => h)) ?_
    intro _
    refine Triple.bind (triple_childResetPS M hA _) ?_
    intro _
    kset0; kset0; kset0; kset0; kset0; kset0; kset0
    refine Triple.bind (R := fun e w => KW O (fun _ _ => True) w ∧ OkExc e)
      (Triple.conseq (R := fun _ _ => False) (triple_depthSetK M hA (fun m c => MemoKeysInChild m c ∧ CachePF m ∧ CachePF c) (0 + 1))
        (fun (w : Void IO.RealWorld) (h : KW O (fun m c => m = {} ∧ c = {}) w) =>
          ⟨h.1, h.2.1, by rw [h.2.2.1, h.2.2.2]; exact ⟨memoKeysInChild_empty _, cachePF_empty, cachePF_empty⟩⟩) (fun _ _ h => h)
        (fun _ _ h => h.elim)) ?_
    intro _
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (KPF O)
          (_root_.tryFinally
            (do
              let constInfo ← getConstInfo declName
              let env ← getEnv
              if (entryInlinerError? env true false [] constInfo (instancePredicate env)).isSome then
                throwError (stringToMessageData s!"{declName}: {(entryInlinerError? env true
                  false [] constInfo (instancePredicate env)).getD ""}")
              else
              synthesizeFromConst (translate env) (profLogIO prof.isSome) declName [] false true
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
          (fun r w => KPFX O declName w ∧ PairPF r) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine tryFinallySplitQ (Q := fun r w => KPFX O declName w ∧ PairPF r) (Me := KW O (fun _ _ => True)) (E := OkExc) ?_
        (fun a => triple_constConj (PairPF a)
          (fin_totalK M hA (fun m c => MemoKeysExc declName m c ∧ CachePF m ∧ CachePF c) 0 m1 m2 m3 m4 m5 m6 m7))
        (fin_totalK M hA (fun _ _ => True) 0 m1 m2 m3 m4 m5 m6 m7)
      refine Triple.conseq ?_ (fun _ h => h) (fun _ _ h => h)
        (fun e w (h : KPF O w ∧ OkExc e) => ⟨kw_weak h.1, h.2⟩)
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KPF O)
        (FramedNM.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (stableK_KPF O)
        FramedNM.env)) ?_
      intro env
      refine Triple.ite (fun _ => ?_) (fun _ => ?_)
      · exact tripleK_throwErr M hA (stableK_KPF O)
          (stringToMessageData s!"{declName}: {(entryInlinerError? env true
            false [] ci (instancePredicate env)).getD ""}") (OkMsg.str _)
      · exact hbody prof.isSome env _ _
    exact body _ _ _ _ _ _ _

end Core

end Tools.ShippingGen4FKidsEntryCore
