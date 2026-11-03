import Tools.ShippingGen4KWalkEntryArms

-- NOT BUILT (rt169). S5 of scripts/gen4/KWALK_PLAN.md: the entry `synthesizeCombinationalCoreWith` for a NESTED run (depth ≠ 0), for `KWalk`: the front matter, the depth set, `try … finally`, with the arm
-- (`hbody`: K to K_declName, K on failure) as a hypothesis. The window opens inside the body and the `finally` (framed sets, a depth modify) keeps K_declName; a failure of the body leaves K.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. DIAG-PENDING hypothesis `LogMvK` (see Entry). No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkEntryCore
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
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4KWalkEntry

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `try x finally fin`, with different post-conditions for a returning and a throwing `x`; `fin` never throws. -/
theorem tryFinallySplit {α β : Type} {P Mo Me : Void IO.RealWorld → Prop} {E : Exception → Prop}
    {x : MetaM α} {fin : MetaM β}
    (hx : Triple mctx mref cctx cref P x (fun _ => Mo) (fun e w => Me w ∧ E e))
    (hfo : Triple mctx mref cctx cref Mo fin (fun _ => Mo) (fun _ _ => False))
    (hfe : Triple mctx mref cctx cref Me fin (fun _ => Me) (fun _ _ => False)) :
    Triple mctx mref cctx cref P (_root_.tryFinally x fin) (fun _ => Mo) (fun e w => Me w ∧ E e) := by
  intro w hw
  have h1 := hx w hw
  change match (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w with
    | .ok _ w' => Mo w' | .error e w' => Me w' ∧ E e
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

theorem tripleK_throwErr {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I) {α : Type} (msg : MessageData) (hmsg : OkMsg msg)
    {Q : α → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref I (Lean.throwError msg : MetaM α) Q (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsK_throwError (α := α) M hA hS msg hmsg) w hw
  cases hm : (Lean.throwError msg : MetaM α) mctx mref cctx cref w with
  | ok a w1 => exact (throwError_not_runs msg hm).elim
  | error e w1 => rw [hm] at hK; exact hK

section Core
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- A depth `set` keeps `KW O P` (it cannot throw). -/
theorem triple_depthSetK (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (v : Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KW O P) (ST.Ref.set sparkleSynthDepth v : MetaM Unit) (fun _ => KW O P) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := O.depthSet hA _ _ _ _ h hw.1
    have hm := M.frameDepthSet hA _ _ _ _ h hw.1
    exact ⟨O.depthSetQ hA _ _ _ _ h hw.1, hk.2.1.trans hw.2.1, by rw [hm, hk.1]; exact hw.2.2⟩

/-- A depth `modify` keeps `KW O P` (it cannot throw). -/
theorem triple_depthModifyK (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (f : Nat → Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KW O P) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) (fun _ => KW O P) R :=
  Triple.of_runs (refModify_runs _ _) fun w u w' hw h => by
    have hk := O.depthModify' hA f hw.1 h
    have hm := M.frameDepthModify hA f _ _ _ h hw.1
    have hq' : O.quiet w' := by
      obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
      have hq1 := O.frameQ hA _ FramedA.depthGet w hw.1
      rw [endW_of_runs hg] at hq1
      exact O.depthSetQ hA _ _ _ _ hs hq1
    exact ⟨hq', hk.2.1.trans hw.2.1, by rw [hm, hk.1]; exact hw.2.2⟩

/-- A `FramedNM` step that always returns keeps `KW O P` and cannot throw. -/
theorem triple_framedNM_total (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) {α : Type} {p : MetaM α}
    (hp : FramedNM MkRefd p) (total : ∀ w, ∃ a w', RunsTo p mctx mref cctx cref w a w')
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (KW O P) p (fun _ => KW O P) R :=
  Triple.of_runs total fun w a w' hw h => by
    have := keeps_KW_framedNM M hA P hp w hw
    rw [endW_of_runs h] at this
    exact this.1

/-- The depth-restoring `finally` of a nested run. Never throws; keeps `KW O P` for every `P`. -/
theorem fin_totalK (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) (d : Nat)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (KW O P)
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
      (fun _ => KW O P) (fun _ _ => False) := by
  have hset : ∀ {σ : Type} {r : IO.Ref σ} (v : σ), SideRefNM r →
      Triple mctx mref cctx cref (KW O P) (ST.Ref.set r v : MetaM Unit) (fun _ => KW O P) (fun _ _ => False) :=
    fun v hr => triple_framedNM_total M hA P (FramedNM.sideSet v hr) (refSet_runs _ _)
  refine Triple.bind (triple_depthModifyK M hA P _) ?_
  intro _
  refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
  refine Triple.bind (hset _ .fvarValue) ?_; intro _
  refine Triple.bind (hset _ .wireWidth) ?_; intro _
  refine Triple.bind (hset _ .letWire) ?_; intro _
  refine Triple.bind (hset _ .loopWire) ?_; intro _
  refine Triple.bind (hset _ .wireCanon) ?_; intro _
  refine Triple.bind (hset _ .subInstOut) ?_; intro _
  exact hset _ .singleOut

omit M hA in
theorem stableK_KD : StableK O.quiet (fun w => KWalk O w ∧ dv w ≠ 0) :=
  ⟨fun _ h => h.1.1, fun w w' hc hs hd hm hq h => ⟨kw_transfer hc hs hm hq h.1, by rw [hd]; exact h.2⟩⟩

/-- The depth read, under `KWalk ∧ dv ≠ 0`: returns a nonzero depth, keeps `KWalk` (it cannot throw). -/
theorem tripleK_depthGetNZ {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (fun w => KWalk O w ∧ dv w ≠ 0) (ST.Ref.get sparkleSynthDepth : MetaM Nat)
      (fun d w => KWalk O w ∧ d ≠ 0) R :=
  Triple.of_runs (refGet_runs _) fun w a w' hw h => by
    have hK := keepsK_framedNM M hA (stableK_KD (O := O)) FramedNM.depthGet w hw
    rw [endW_of_runs h] at hK
    have ha : a = dv w := runsTo_get_readOf _ h
    exact ⟨hK.1.1, by rw [ha]; exact hw.2⟩

set_option hygiene false in
macro "kget" : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (Tools.ShippingGen4KWalkEntryArms.stableK_KWalk O)
      (FramedNM.sideGet ?s))) ?_
   case s => constructor
   intro _))
set_option hygiene false in
macro "kset" : tactic => `(tactic|
  (refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (Tools.ShippingGen4KWalkEntryArms.stableK_KWalk O)
      (FramedNM.sideSet _ ?s))) ?_
   case s => constructor
   intro _))

/-- **The entry for a nested run** (`depth ≠ 0`), from the arm `hbody` (K to K_declName, K on failure). -/
theorem entryNested_windowK (hlog : LogMvK O) (translate : Lean.Environment → TranslateFn) (declName : Name)
    (hbody : ∀ (b : Bool) (env : Lean.Environment) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Triple mctx mref cctx cref (KWalk O)
        (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
        (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e)) :
    Triple mctx mref cctx cref (fun w => KWalk O w ∧ dv w ≠ 0)
      (synthesizeCombinationalCoreWith translate declName [] false true)
      (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e) := by
  unfold synthesizeCombinationalCoreWith
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.bind (R := fun e w => KWalk O w ∧ OkExc e) (Q := fun _ w => KWalk O w ∧ dv w ≠ 0)
    (Triple.conseq (keeps_iff.mp (keepsK_framedNM M hA (stableK_KD (O := O)) (FramedNM.ioEnv _)))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
  intro prof
  refine Triple.bind (R := fun e w => KWalk O w ∧ OkExc e) (Q := fun _ w => KWalk O w ∧ dv w ≠ 0)
    (Triple.conseq (keeps_iff.mp (keepsK_profLog M hA (stableK_KD (O := O)) hlog prof.isSome _))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.2⟩)) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d ≠ 0) (tripleK_depthGetNZ M hA) ?_
  intro d hd
  refine Triple.ite (fun _ => ?_) (fun _ => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleK_throwErr M hA (Tools.ShippingGen4KWalkEntryArms.stableK_KWalk O) _
        (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have h0 : (d == 0) = false := by simpa using hd
    simp only [h0, Bool.false_eq_true, ↓reduceIte]
    kget; kget; kget; kget; kget; kget; kget
    kset; kset; kset; kset; kset; kset; kset
    refine Triple.bind (triple_depthSetK M hA _ (d + 1)) ?_
    intro _
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (KWalk O)
          (_root_.tryFinally
            (do
              let constInfo ← getConstInfo declName
              let env ← getEnv
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
          (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine tryFinallySplit (Mo := KWalkX O declName) (Me := KWalk O) (E := OkExc) ?_
        (fin_totalK M hA (MemoKeysExc declName) d m1 m2 m3 m4 m5 m6 m7)
        (fin_totalK M hA MemoKeysInChild d m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (Tools.ShippingGen4KWalkEntryArms.stableK_KWalk O)
        (FramedNM.constInfo _))) ?_
      intro ci
      refine Triple.bind (keeps_iff.mp (keepsK_framedNM M hA (Tools.ShippingGen4KWalkEntryArms.stableK_KWalk O)
        FramedNM.env)) ?_
      intro env
      exact hbody prof.isSome env _ _
    exact body _ _ _ _ _ _ _

end Core

end Tools.ShippingGen4KWalkEntryCore
