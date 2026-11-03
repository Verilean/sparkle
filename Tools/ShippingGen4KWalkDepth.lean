import Tools.ShippingGen4KWalkEntryCore
-- NOT BUILT. S6 (depth induction, part 1) of scripts/gen4/KWALK_PLAN.md, frozen in scripts/gen4/KWALK_S6_FREEZE.md: the window and entry theorems
-- with a DEPTH-INDEXED invariant `KWD O P D = KW O P ∧ dv = D` (the same proofs as Arms/EntryCore with the invariant `KWalk ∧ dv = D`; the
-- `dv` is also a postcondition: a nested run gives the depth back).
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. DIAG-PENDING hypothesis `LogMvK` (see Entry).
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkDepth
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.Assume.MemoFamily
open Tools.Assume.FramedACases
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4KWalkEntry
open Tools.ShippingGen4KWalkEntryCore

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The walk invariant over a key relation `P`, with the synthesis depth pinned to `D`. -/
def KWD (O : RefLawsAOps MkRefd mref cref) (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (D : Nat)
    (w : Void IO.RealWorld) : Prop :=
  KW O P w ∧ dv w = D

theorem stableK_KWD (O : RefLawsAOps MkRefd mref cref) (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop)
    (D : Nat) : StableK O.quiet (KWD O P D) :=
  ⟨fun _ h => h.1.1, fun w w' hc hs hd hm hq h => ⟨kw_transfer hc hs hm hq h.1, by rw [hd]; exact h.2⟩⟩

/-- `try x finally fin`, with a different post-condition for each of the two `fin` runs (after a return, after a throw). -/
theorem tryFinallySplit2 {α β : Type} {P Mo Mo' Me Me' : Void IO.RealWorld → Prop} {E : Exception → Prop}
    {x : MetaM α} {fin : MetaM β}
    (hx : Triple mctx mref cctx cref P x (fun _ => Mo) (fun e w => Me w ∧ E e))
    (hfo : Triple mctx mref cctx cref Mo fin (fun _ => Mo') (fun _ _ => False))
    (hfe : Triple mctx mref cctx cref Me fin (fun _ => Me') (fun _ _ => False)) :
    Triple mctx mref cctx cref P (_root_.tryFinally x fin) (fun _ => Mo') (fun e w => Me' w ∧ E e) := by
  intro w hw
  have h1 := hx w hw
  change match (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w with
    | .ok _ w' => Mo' w' | .error e w' => Me' w' ∧ E e
  unfold EST.bind
  simp only [MonadFinally.tryFinally']
  cases hxw : x mctx mref cctx cref w with
  | ok a w1 =>
    rw [hxw] at h1
    have h2 := hfo w1 h1
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

section Depth
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- A `FramedNM` step that always returns keeps `KWD O P D` and cannot throw. -/
theorem triple_framedNM_totalD (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (D : Nat)
    {α : Type} {p : MetaM α}
    (hp : FramedNM MkRefd p) (total : ∀ w, ∃ a w', RunsTo p mctx mref cctx cref w a w')
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O P D) p (fun _ => KWD O P D) R :=
  Triple.of_runs total fun w a w' hw h => by
    have := keepsK_framedNM M hA (stableK_KWD O P D) hp w hw
    rw [endW_of_runs h] at this
    exact this.1

/-- A depth `set v` takes `KWD O P D` to `KWD O P v` (it cannot throw). -/
theorem triple_depthSetD (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (D v : Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O P D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => KWD O P v) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.depthSet hA _ _ _ _ h hw.1.1
    have hm := M.frameDepthSet hA _ _ _ _ h hw.1.1
    exact ⟨⟨O.depthSetQ hA _ _ _ _ h hw.1.1, hk.2.1.trans hw.1.2.1, by rw [hm, hk.1]; exact hw.1.2.2⟩, hk.2.2⟩

/-- A depth `modify f` takes `KWD O P D` to `KWD O P (f D)` (it cannot throw). -/
theorem triple_depthModifyD (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (D : Nat) (f : Nat → Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O P D) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => KWD O P (f D)) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw h => by
    have hk := O.depthModify' hA f hw.1.1 h
    have hm := M.frameDepthModify hA f _ _ _ h hw.1.1
    have hq' : O.quiet w' := by
      obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
      have hq1 := O.frameQ hA _ FramedA.depthGet w hw.1.1
      rw [endW_of_runs hg] at hq1
      exact O.depthSetQ hA _ _ _ _ hs hq1
    exact ⟨⟨hq', hk.2.1.trans hw.1.2.1, by rw [hm, hk.1]; exact hw.1.2.2⟩, by rw [hk.2.2, hw.2]⟩

/-- The depth read: returns the pinned depth, keeps the invariant (it cannot throw). -/
theorem tripleK_depthGetD (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (D : Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O P D) (ST.Ref.get sparkleSynthDepth : MetaM Nat)
      (fun d w => KWD O P D w ∧ d = D) R :=
  Triple.of_runs (refGet_runs _) fun w a w' hw h => by
    have hK := keepsK_framedNM M hA (stableK_KWD O P D) FramedNM.depthGet w hw
    rw [endW_of_runs h] at hK
    have ha : a = dv w := runsTo_get_readOf _ h
    exact ⟨hK.1, by rw [ha]; exact hw.2⟩

/-- The memo write `memo.modify (·.insert n r)`: `KWD K D` to `KWD K_n D` (it cannot throw). -/
theorem triple_memoInsertD (D : Nat) (n : Name) (r : Res) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O MemoKeysInChild D)
      (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit)
      (fun _ => KWD O (MemoKeysExc n) D) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw hr => by
    have hp : FramedA MkRefd (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit) :=
      framedA_of_memoAccess (MemoAccess.modify _)
    have hf := O.frame hA _ hp w hw.1.1
    rw [endW_of_runs hr] at hf
    exact ⟨kwalk_memoInsert M hA n r hr hw.1, by rw [hf.2.2]; exact hw.2⟩

/-- The child-cache write `child.modify (·.insert n r)` closes the window: `KWD K_n D` to `KWD K D`. -/
theorem triple_childInsertD (D : Nat) (n : Name) (r : Res) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KWD O (MemoKeysExc n) D)
      (sparkleChildCache.modify (·.insert n r) : MetaM Unit)
      (fun _ => KWD O MemoKeysInChild D) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw hr => by
    have hk := O.cacheModify' hA (·.insert n r) hw.1.1 hr
    exact ⟨kwalk_childInsert M hA n r hr hw.1, by rw [hk.2.2]; exact hw.2⟩

/-- The depth-restoring `finally` of a nested run at depth `D`: `KWD O P (D+1)` to `KWD O P D`. Never throws. -/
theorem fin_totalD (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (D : Nat)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (KWD O P (D + 1))
      (do
        ST.Ref.modify sparkleSynthDepth fun x => x - 1
        if (D != 0) = true then do
            ST.Ref.set sparkleFvarValueMap m1
            ST.Ref.set sparkleWireWidthCache m2
            ST.Ref.set sparkleLetWireCache m3
            ST.Ref.set sparkleLoopWireCache m4
            ST.Ref.set sparkleWireCanon m5
            ST.Ref.set sparkleSubInstanceOutputs m6
            ST.Ref.set sparkleSingleOutInstanceCache m7
          else pure () : MetaM Unit)
      (fun _ => KWD O P D) (fun _ _ => False) := by
  have hset : ∀ {σ : Type} {r : IO.Ref σ} (v : σ), SideRefNM r →
      Triple mctx mref cctx cref (KWD O P D) (ST.Ref.set r v : MetaM Unit) (fun _ => KWD O P D)
        (fun _ _ => False) :=
    fun v hr => triple_framedNM_totalD M hA P D (FramedNM.sideSet v hr) (refSet_runs _ _)
  refine Triple.bind (triple_depthModifyD M hA P (D + 1) (fun x => x - 1)) ?_
  intro _
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  refine Triple.conseq ?_ (fun w hw => hw) (fun _ _ h => h) (fun _ _ h => h)
  refine Triple.bind (hset _ .fvarValue) ?_; intro _
  refine Triple.bind (hset _ .wireWidth) ?_; intro _
  refine Triple.bind (hset _ .letWire) ?_; intro _
  refine Triple.bind (hset _ .loopWire) ?_; intro _
  refine Triple.bind (hset _ .wireCanon) ?_; intro _
  refine Triple.bind (hset _ .subInstOut) ?_; intro _
  exact hset _ .singleOut

end Depth

end Tools.ShippingGen4KWalkDepth

#print axioms Tools.ShippingGen4KWalkDepth.triple_memoInsertD
#print axioms Tools.ShippingGen4KWalkDepth.triple_childInsertD
#print axioms Tools.ShippingGen4KWalkDepth.fin_totalD
