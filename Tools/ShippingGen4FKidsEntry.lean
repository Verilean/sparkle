import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4KWalkFallback
import Tools.ShippingGen4FKidsFallback
import Tools.ShippingChildFrontA
-- BUILT: kjob lake build Tools.ShippingGen4KWalkEntry exit 0 (rt169, source as of 9e5eb088); axioms standard only. Clean build is the coder's. S4 (part 1) of scripts/gen4/KWALK_PLAN.md, frozen in scripts/gen4/KWALK_S4_FREEZE.md: the entry arms' parts (emitLeaves / certified / mixed / machine) and the memo-write step that opens the window, for `KWalk`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom to the family.
-- DIAG-PENDING hypothesis `LogMvKS` (one run of the profile logger leaves the memo as it was): a `def`, NOT a family statement; it is what scripts/gen4/KWALK_DIAG_DECISION.md option A would give.
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsEntry
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

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `withVarMapping` for `KeepsCS` (the update leaves `exprCache`). -/
theorem withVarMappingPS {I : Void IO.RealWorld → Prop} {α : Type} (fv : FVarId) (wn : String)
    {k : CompilerM α} (hk : KeepsCS mctx mref cctx cref I k) :
    KeepsCS mctx mref cctx cref I (CompilerM.withVarMapping fv wn k) := by
  unfold CompilerM.withVarMapping
  refine KeepsCS.bindCtx (fun old hold => ?_)
  refine KeepsCS.withReader _ ?_ hk
  intro _ _ r h
  exact hold r h

/-- **DIAG-PENDING HYPOTHESIS.** One run of the profile logger (`profLogIO b msg`, the entry's `logProf`) leaves the
memo as it was, in a quiet world. The A boundary (`O.diag`) says this of `cv`/`sv`/`dv` and quietness only. -/
def LogMvKS (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ b msg w, O.quiet w →
    mv (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) = mv w

theorem addClockReset_params (m : Sparkle.IR.AST.Module) :
    (addClockResetIfSequential m).parameters = m.parameters := by
  unfold addClockResetIfSequential
  dsimp only
  repeat' split
  all_goals simp [Sparkle.IR.AST.Module.addInput]

theorem init_ok (n : String) :
    StatePF (Sparkle.IR.Builder.CircuitM.init n) ∧ (Sparkle.IR.Builder.CircuitM.init n).module.parameters = [] :=
  ⟨by unfold StatePF; exact designPF_empty _, rfl⟩

/-- `finishSynth` (non-symbolic) of a `StatePF` state with no parameter returns a `PairPF` pair. -/
theorem finishSynthPS {I : Void IO.RealWorld → Prop} (declName : Name) (st : Sparkle.IR.Builder.CircuitState)
    (hst : StatePF st) (hp : st.module.parameters = []) :
    Triple mctx mref cctx cref I (finishSynth declName [] false st)
      (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e) := by
  unfold finishSynth
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.ite (fun _ => Triple.pure fun _ hw => ⟨hw, ?_, hst⟩)
    (fun _ => Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩)
  show (Sparkle.IR.AST.Module.finalize (addClockResetIfSequential st.module)).parameters = []
  simp [Sparkle.IR.AST.Module.finalize, addClockReset_params, hp]

/-! ## Pure facts about the machine closing (parameters and design modules) -/
section MachPure
open Sparkle.IR.AST Sparkle.IR.Machine

theorem designWith_pf (children : List (Sparkle.IR.AST.Module × Design)) (d : Design)
    (hc : ∀ c ∈ children, PairPF c) (hd : DesignPF d) : DesignPF (designWith children d) := by
  unfold designWith DesignPF
  dsimp only
  have key : ∀ (cs : List (Sparkle.IR.AST.Module × Design)) (acc : List Sparkle.IR.AST.Module), (∀ c ∈ cs, PairPF c) →
      (∀ x ∈ acc, ParamFree x) →
      ∀ x ∈ cs.foldl (fun acc (p : Sparkle.IR.AST.Module × Design) =>
        (p.2.modules ++ [p.1]).foldl (fun acc c => if acc.any (·.name == c.name) then acc else acc ++ [c]) acc) acc, ParamFree x := by
    intro cs
    induction cs with
    | nil => intro acc _ h; simpa using h
    | cons p ps ih =>
      intro acc hp h
      simp only [List.foldl_cons]
      apply ih
      · intro c hc; exact hp c (List.mem_cons_of_mem _ hc)
      · have hpp := hp p (List.mem_cons_self ..)
        have inner : ∀ (l : List Sparkle.IR.AST.Module) (acc : List Sparkle.IR.AST.Module), (∀ x ∈ l, ParamFree x) → (∀ x ∈ acc, ParamFree x) →
            ∀ x ∈ l.foldl (fun acc c => if acc.any (·.name == c.name) then acc else acc ++ [c]) acc, ParamFree x := by
          intro l
          induction l with
          | nil => intro acc _ h; simpa using h
          | cons c cs ih2 =>
            intro acc hl ha
            simp only [List.foldl_cons]
            apply ih2
            · intro x hx; exact hl x (List.mem_cons_of_mem _ hx)
            · split
              · exact ha
              · intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact ha x hx
                · simp at hx; rw [hx]; exact hl c (List.mem_cons_self ..)
        apply inner
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hpp.2 x hx
          · simp at hx; rw [hx]; exact hpp.1
        · exact h
  exact key children d.modules hc hd

theorem closeMachine_params (lay : Layout) (t : Sparkle.IR.AST.Module) : (closeMachine lay t).parameters = t.parameters := by
  unfold closeMachine; split <;> rfl

theorem closeLets_params (n : Nat) (t t' : Sparkle.IR.AST.Module) (h : closeLets n t = some t') : t'.parameters = t.parameters := by
  unfold closeLets at h
  dsimp only at h
  repeat' split at h
  all_goals first | (obtain rfl := Option.some.inj h; rfl) | (exfalso; simp at h)

theorem withClockFor_params (children : List (Sparkle.IR.AST.Module × Design)) (m : Sparkle.IR.AST.Module) :
    (withClockFor children m).parameters = m.parameters := by
  unfold withClockFor; dsimp only; split <;> rfl

theorem closeInsts_pf (nIn kI n : Nat) (portNames : List String) (insts : List (List Nat))
    (children : List (Sparkle.IR.AST.Module × Design)) (m : Sparkle.IR.AST.Module) (d : Design)
    (hc : ∀ c ∈ children, PairPF c) (hm : ParamFree m) (hd : DesignPF d) (r)
    (h : closeInsts nIn kI n portNames insts children (m, d) = some r) : PairPF r := by
  unfold closeInsts at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  repeat' (rcases h with ⟨_, _, h⟩)
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨hm, designWith_pf _ _ hc hd⟩
  · simp at h

theorem closeInstsG_pf (nIn kI n : Nat) (portNames : List String) (insts : List (List Nat))
    (fields : List String) (children : List (Sparkle.IR.AST.Module × Design)) (m : Sparkle.IR.AST.Module) (d : Design)
    (hc : ∀ c ∈ children, PairPF c) (hm : ParamFree m) (hd : DesignPF d) (r)
    (h : closeInstsG nIn kI n portNames insts fields children (m, d) = some r) : PairPF r := by
  unfold closeInstsG at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  repeat' (rcases h with ⟨_, _, h⟩)
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨by unfold ParamFree at *; simp [withClockFor_params, hm], designWith_pf _ _ hc hd⟩
  · simp at h

theorem memModule_pf (combo : Bool) (aw dw : Nat) :
    PairPF (Sparkle.Compiler.MachMemory.memModule combo aw dw) :=
  ⟨rfl, by
    intro x hx
    simp [Sparkle.Compiler.MachMemory.memModule] at hx
    rw [hx]; rfl⟩

theorem child_pf (o : Sparkle.Compiler.MachInstOrigin.InstOrigin) (md : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
    (h : Sparkle.Compiler.MachInstOrigin.InstOrigin.child? o = some md) : PairPF md := by
  cases o <;> simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h
  subst h; exact memModule_pf _ _ _

/-- a result `Option` pair, when present, is `PairPF` -/
def OptPF (o : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) : Prop := ∀ r, o = some r → PairPF r
end MachPure

section Arms
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
  {I : Void IO.RealWorld → Prop} (hS : StableK O.quiet I)
include M hA hS

/-- The profile logger keeps a `StableK` invariant, given `LogMvKS`. -/
theorem keepsK_profLogS (hlog : LogMvKS O) (b : Bool) (msg : String) :
    Keeps mctx mref cctx cref I (liftM (profLogIO b msg) : MetaM Unit) := by
  intro w hw
  have hq := hS.1 w hw
  have hk := O.diag hA _ (Diag.profLog b msg) w hq
  have hm := hlog mctx cctx hA b msg w hq
  refine ⟨hS.2 w _ hk.1.1 hk.1.2.1 hk.1.2.2 hm (fun _ => hk.2) hw, ?_⟩
  unfold ErrOk
  cases hmm : (liftM (profLogIO b msg) : MetaM Unit) mctx mref cctx cref w with
  | ok a w1 => exact True.intro
  | error e w1 => exact O.excOk hA _ (.diag (Diag.profLog b msg)) w e w1 hq hmm

/-- `IO.mkRef v` returns a ref with provenance. -/
theorem tripleK_mkExprCacheS (v : Lean.ExprStructMap String) :
    Triple mctx mref cctx cref I (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
      (fun r w => I w ∧ MkRefd _ r) (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsK_framedNM M hA hS (FramedNM.mkExprCache v)) w hw
  cases hm : (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String))) mctx mref cctx cref w with
  | ok r w1 => rw [hm] at hK; exact ⟨hK, mkRefd_of_runs hm⟩
  | error e w1 => rw [hm] at hK; exact hK

theorem keepsK_mkExprCache_bindS (v : Lean.ExprStructMap String) {β : Type}
    {k : IO.Ref (Lean.ExprStructMap String) → MetaM β}
    (hk : ∀ r, MkRefd _ r → Keeps mctx mref cctx cref I (k r)) :
    Keeps mctx mref cctx cref I
      ((IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String))) >>= k) :=
  keeps_iff.mpr (Triple.bindQ (φ := MkRefd _) (tripleK_mkExprCacheS M hA hS v)
    fun r hr => keeps_iff.mp (hk r hr))

/-! ## The binder walk and the leaf emission -/

theorem bindInputPortKPS {α : Type} (fv : FVarId) (bn : String) (ty : Sparkle.IR.Type.HWType) (k : CompilerM α)
    (hk : KeepsCS mctx mref cctx cref I k) :
    KeepsCS mctx mref cctx cref I (bindInputPort fv bn ty k) := by
  unfold bindInputPort
  refine KeepsCS.bind (makeWirePS M hA hS _ _ _) (fun _ => ?_)
  refine KeepsCS.bind (addInputPS M hA hS _ _) (fun _ => ?_)
  exact withVarMappingPS _ _ hk

theorem bindCertifiedInputsKPS {α : Type} (k : CompilerM α) (hk : KeepsCS mctx mref cctx cref I k) :
    ∀ l : List ((Name × GateBinder) × FVarId),
      KeepsCS mctx mref cctx cref I (bindCertifiedInputs k l)
  | [] => by unfold bindCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindCertifiedInputs
    exact bindCertifiedInputsKPS k hk rest
  | ((_, .signal _), _) :: rest => by
    unfold bindCertifiedInputs
    exact bindInputPortKPS M hA hS _ _ _ _ (bindCertifiedInputsKPS k hk rest)

theorem bindMixedCertifiedInputsKPS {α : Type} (k : CompilerM α) (hk : KeepsCS mctx mref cctx cref I k) :
    ∀ l : List ((Name × MixedGateBinder) × FVarId),
      KeepsCS mctx mref cctx cref I (bindMixedCertifiedInputs k l)
  | [] => by unfold bindMixedCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindMixedCertifiedInputsKPS k hk rest
  | ((_, .bool), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPortKPS M hA hS _ _ _ _ (bindMixedCertifiedInputsKPS k hk rest)
  | ((_, .bits _), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPortKPS M hA hS _ _ _ _ (bindMixedCertifiedInputsKPS k hk rest)

/-- **`emitLeaves` for `StableK`**, the translator hypothesis restricted to `CtxOk` contexts (copy of `emitLeavesAP`):
every op but the translator is a `FramedNM` op or the logger (`hlog`). -/
theorem emitLeavesKPS (hlog : LogMvKS O)
    (translate : TranslateFn) (b : Bool) (r : IO.Ref (Lean.ExprStructMap String))
    (hr : MkRefd _ r)
    (htr : ∀ e hint top named, KeepsCS mctx mref cctx cref I (translate e hint top named)) :
    ∀ (leaves : List (String × Lean.Expr)) (fw : Option String) (idx : Nat),
      KeepsCS mctx mref cctx cref I (emitLeaves translate r (profLogIO b) leaves fw idx)
  | [], fw, idx => by
    unfold emitLeaves
    exact KeepsCS.pure _
  | (pn, le) :: rest, fw, idx => by
    unfold emitLeaves
    have clock : KeepsCS mctx mref cctx cref I (CompilerM.liftMetaM (liftM IO.monoMsNow)) :=
      KeepsCS.lift (keepsK_framedNM M hA hS FramedNM.monoMs)
    have calls : KeepsCS mctx mref cctx cref I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCallCounter)) :=
      KeepsCS.lift (keepsK_framedNM M hA hS (FramedNM.sideGet .callCounter))
    have hits : KeepsCS mctx mref cctx cref I
        (CompilerM.liftMetaM (ST.Ref.get sparkleCacheHits)) :=
      KeepsCS.lift (keepsK_framedNM M hA hS (FramedNM.sideGet .cacheHits))
    have log : ∀ msg, KeepsCS mctx mref cctx cref I
        (CompilerM.liftMetaM (liftM (profLogIO b msg))) :=
      fun msg => KeepsCS.lift (keepsK_profLogS M hA hS hlog b msg)
    refine KeepsCS.bind clock ?_; intro t0
    refine KeepsCS.bind calls ?_; intro c0
    refine KeepsCS.bind hits ?_; intro h0
    refine KeepsCS.bind (log _) ?_; intro _
    refine KeepsCS.bind (htr le pn false true) ?_; intro lw
    refine KeepsCS.bind clock ?_; intro t1
    refine KeepsCS.bind calls ?_; intro c1
    refine KeepsCS.bind hits ?_; intro h1
    refine KeepsCS.bind (log _) ?_; intro _
    dsimp only
    refine KeepsCS.ite
      (fun _ => KeepsCS.bind (KeepsCS.lift
        (keepsK_framedNM M hA hS (FramedNM.exprCacheModify r _ hr))) (fun _ => ?_))
      (fun _ => ?_)
    all_goals
      try dsimp only
      refine KeepsCS.bind KeepsCS.get ?_
      intro cs
      try dsimp only
      refine KeepsCS.ite (fun _ => ?_) (fun _ => ?_)
      · exact KeepsCS.throwBind _ (by okmsg) _
      · try dsimp only
        refine KeepsCS.bind (addOutputPS M hA hS _ _) ?_
        intro _
        refine KeepsCS.bind (emitAssignPS _ _) ?_
        intro _
        exact emitLeavesKPS hlog translate b r hr htr rest _ _

/-- `certRest` (the binder walk, the one leaf, the `CircuitM` run, `finishSynth`): returns a `PairPF` pair. -/
theorem certRest_keepsKS (hlog : LogMvKS O)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsCS mctx mref cctx cref I (translate e hint top named))
    (ids : List FVarId) (r : IO.Ref (Lean.ExprStructMap String)) (hr : MkRefd _ r) :
    Triple mctx mref cctx cref I (certRest translate (profLogIO b) declName bs body ids r)
      (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e) := by
  unfold certRest
  try dsimp only
  have hi := init_ok (Sparkle.IR.ModuleName.ofDecl declName)
  refine Triple.bindQ (P' := I) (φ := fun p => GoodS (Sparkle.IR.Builder.CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) p.2)
    ?hh ?_
  case hh =>
    exact bindCertifiedInputsKPS M hA hS _
      (emitLeavesKPS M hA hS hlog translate b r hr htr _ _ _) _ _ _ (ctxOk_entry false hr) hi.1
  rintro ⟨_, fs⟩ hg
  exact finishSynthPS declName fs hg.2.1 (hg.2.2 hi.2)

/-- `synthesizeCertified` (copy of `certified_keepsA`), returning a `PairPF` pair. -/
theorem certified_keepsKS (hlog : LogMvKS O)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsCS mctx mref cctx cref I (translate e hint top named)) :
    Triple mctx mref cctx cref I (synthesizeCertified translate (profLogIO b) declName bs body)
      (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e) := by
  unfold synthesizeCertified
  refine Triple.bind (Triple.mapM _ (fun _ => keeps_iff.mp (keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd)))) _) ?_
  intro ids
  split
  · refine Triple.bindQ (φ := MkRefd _) (tripleK_mkExprCacheS M hA hS _) ?_
    intro r hr
    exact certRest_keepsKS M hA hS hlog translate b declName bs body htr ids r hr
  · exact Triple.throw _ fun _ hw => ⟨hw, by
      first
        | exact OkMsg.str _
        | (unfold OkExc; exact OkMsg.str _)
        | (show OkMsg (stringToMessageData _); exact OkMsg.str _)
        | exact OkMsg.fmt _⟩

/-- `synthesizeMixedCertified` (copy of `mixed_keepsA`). -/
theorem mixed_keepsKS (hlog : LogMvKS O)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (htr : ∀ e hint top named, KeepsCS mctx mref cctx cref I (translate e hint top named)) :
    Triple mctx mref cctx cref I
      (synthesizeMixedCertified translate (profLogIO b) declName bs body)
      (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e) := by
  unfold synthesizeMixedCertified
  refine Triple.bind
    (Triple.mapM _ (fun _ => keeps_iff.mp (keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd)))) _) ?_
  intro ids
  split
  · dsimp only
    refine Triple.bindQ (φ := MkRefd _) (tripleK_mkExprCacheS M hA hS _) ?_
    intro cacheRef hr
    have hi := init_ok (Sparkle.IR.ModuleName.ofDecl declName)
    refine Triple.bindQ (P' := I) (φ := fun p => GoodS (Sparkle.IR.Builder.CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)) p.2)
      ?hh ?_
    case hh =>
      exact bindMixedCertifiedInputsKPS M hA hS _
        (emitLeavesKPS M hA hS hlog translate b cacheRef hr htr _ _ _) _ _ _ (ctxOk_entry false hr) hi.1
    rintro ⟨_, fs⟩ hg
    exact finishSynthPS declName fs hg.2.1 (hg.2.2 hi.2)
  · exact Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩

/-! ## The machine synthesis -/

theorem tripleK_synthGetS (hsv : ∀ w, I w → sv w = some synthesizeChild) :
    Triple mctx mref cctx cref I (sparkleChildSynth.get : MetaM _)
      (fun s w => I w ∧ s = some synthesizeChild) (fun e w => I w ∧ OkExc e) := by
  intro w hw
  have hK := keeps_iff.mp (keepsK_framedNM M hA hS FramedNM.synthGet) w hw
  cases hm : (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w with
  | ok a w1 =>
    rw [hm] at hK
    exact ⟨hK, (runsTo_get_readOf _ hm).trans (hsv w hw)⟩
  | error e w1 => rw [hm] at hK; exact hK

omit M hA hS in
theorem Triple.mapMQ_loop {α β : Type} {I : Void IO.RealWorld → Prop}
    {R : Exception → Void IO.RealWorld → Prop} {φ : β → Prop} (f : α → MetaM β)
    (hf : ∀ x, Triple mctx mref cctx cref I (f x) (fun y w => I w ∧ φ y) R) :
    ∀ (l : List α) (acc : List β), (∀ y ∈ acc, φ y) →
      Triple mctx mref cctx cref I (List.mapM.loop f l acc) (fun ys w => I w ∧ ∀ y ∈ ys, φ y) R
  | [], acc, hacc => Triple.pure fun _ hw => ⟨hw, fun y hy => hacc y (List.mem_reverse.mp hy)⟩
  | x :: xs, acc, hacc =>
    Triple.bindQ (P' := I) (φ := φ) (hf x) fun y hy =>
      Triple.mapMQ_loop f hf xs (y :: acc) (by
        intro z hz
        rcases List.mem_cons.mp hz with h | h
        · rw [h]; exact hy
        · exact hacc z h)

omit M hA hS in
theorem Triple.mapMQ {α β : Type} {I : Void IO.RealWorld → Prop}
    {R : Exception → Void IO.RealWorld → Prop} {φ : β → Prop} (f : α → MetaM β)
    (hf : ∀ x, Triple mctx mref cctx cref I (f x) (fun y w => I w ∧ φ y) R) (l : List α) :
    Triple mctx mref cctx cref I (l.mapM f) (fun ys w => I w ∧ ∀ y ∈ ys, φ y) R :=
  Triple.mapMQ_loop f hf l [] (by intro y hy; simp at hy)

theorem closeInstsM_keepsKS (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hchild : ∀ c, Triple mctx mref cctx cref I (synthesizeChild c)
      (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e))
    (shape : MachineShape) (t m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design)
    (hm : ParamFree m) (hd : DesignPF design) :
    Triple mctx mref cctx cref I (closeInstsM shape t m design)
      (fun o w => I w ∧ OptPF o) (fun e w => I w ∧ OkExc e) := by
  unfold closeInstsM
  refine Triple.bindQ (tripleK_synthGetS M hA hS hsv) ?_
  intro s hs
  subst hs
  dsimp only
  refine Triple.bindQ (P' := I) (φ := fun cs => ∀ c ∈ cs, PairPF c)
    (Triple.mapMQ (φ := PairPF) _ (fun x => ?_) _) ?_
  · obtain ⟨c, _, _⟩ := x
    exact hchild c
  · intro cs hcs
    exact Triple.pure fun _ hw => ⟨hw, fun r hr => closeInsts_pf _ _ _ _ _ cs _ _ hcs hm hd r hr⟩

theorem closeInstsGM_keepsKS (hsv : ∀ w, I w → sv w = some synthesizeChild)
    (hchild : ∀ c, Triple mctx mref cctx cref I (synthesizeChild c)
      (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e))
    (shape : MachineShape) (t m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design)
    (hm : ParamFree m) (hd : DesignPF design) :
    Triple mctx mref cctx cref I (closeInstsGM shape t m design)
      (fun o w => I w ∧ OptPF o) (fun e w => I w ∧ OkExc e) := by
  unfold closeInstsGM
  refine Triple.bindQ (tripleK_synthGetS M hA hS hsv) ?_
  intro s hs
  subst hs
  dsimp only
  refine Triple.bindQ (P' := I) (φ := fun cs => ∀ c ∈ cs, PairPF c)
    (Triple.mapMQ (φ := PairPF) _ (fun x => ?_) _) ?_
  · obtain ⟨c, o⟩ := x
    dsimp only
    cases hh : Sparkle.Compiler.MachInstOrigin.InstOrigin.child? o with
    | some md => exact Triple.pure fun _ hw => ⟨hw, child_pf o md hh⟩
    | none => exact hchild c
  · intro cs hcs
    exact Triple.pure fun _ hw => ⟨hw, fun r hr => closeInstsG_pf _ _ _ _ _ _ cs _ _ hcs hm hd r hr⟩

theorem machineCert_keepsKS (hlog : LogMvKS O)
    (translate : TranslateFn) (b : Bool) (declName : Name)
    (htr : ∀ e hint top named, KeepsCS mctx mref cctx cref I (translate e hint top named))
    (hchild : ∀ c, Triple mctx mref cctx cref I (synthesizeChild c)
      (fun r w => I w ∧ PairPF r) (fun e w => I w ∧ OkExc e))
    (hsv : ∀ w, I w → sv w = some synthesizeChild) (shape : MachineShape) :
    Triple mctx mref cctx cref I
      (synthesizeMachineCertified translate (profLogIO b) declName shape)
      (fun o w => I w ∧ OptPF o) (fun e w => I w ∧ OkExc e) := by
  unfold synthesizeMachineCertified
  refine Triple.bindQ (P' := I) (φ := PairPF)
    (mixed_keepsKS M hA hS hlog translate b declName shape.binders shape.body htr) ?_
  rintro ⟨t, d⟩ hp
  dsimp only
  split
  next t' heq =>
    have ht' : ParamFree t' := by
      have := closeLets_params _ _ _ heq
      unfold ParamFree at *
      rw [this]; exact hp.1
    have hm : ParamFree (Sparkle.IR.Machine.closeMachine shape.layout t') := by
      unfold ParamFree at *
      rw [closeMachine_params]; exact ht'
    split
    · exact Triple.pure fun _ hw => ⟨hw, fun r hr => by cases hr; exact ⟨hm, hp.2⟩⟩
    · split
      · exact closeInstsM_keepsKS M hA hS hsv hchild _ _ _ _ hm hp.2
      · exact closeInstsGM_keepsKS M hA hS hsv hchild _ _ _ _ hm hp.2
  next => exact Triple.pure fun _ hw => ⟨hw, fun r hr => by cases hr⟩

end Arms

/-! ## The window: the memo write of `n` opens it (K → K_n) -/

section Window
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- The memo write `memo.modify (·.insert n r)`: from K, returns in K_n (it cannot throw). -/
theorem triple_memoInsertS (n : Name) (r : Res) :
    Triple mctx mref cctx cref (KWalk O)
      (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit)
      (fun _ => KWalkX O n) (fun e w => KWalk O w ∧ OkExc e) := by
  intro w hw
  obtain ⟨a, w', hr⟩ := refModify_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleSubModuleCache (·.insert n r) w
  have e := hr
  unfold RunsTo at e
  rw [e]
  exact kwalk_memoInsert M hA n r hr hw

/-- A memo read that hits, or any step that leaves K: K weakens to K_n. -/
theorem kwalkX_of_kwalkS {n : Name} {w : Void IO.RealWorld} (h : KWalk O w) : KWalkX O n w :=
  ⟨h.1, h.2.1, memoKeysInChild_exc n h.2.2⟩

end Window


/-! ## The PF world: the K world with both caches `PairPF` -/

/-- every entry of a cache map is a `PairPF` pair -/
def CachePF (m : Std.HashMap Name Res) : Prop := ∀ n r, m.get? n = some r → PairPF r

theorem cachePF_empty : CachePF ({} : Std.HashMap Name Res) := by
  intro n r h; simp at h

theorem cachePF_insert {m : Std.HashMap Name Res} (n : Name) (r : Res) (hm : CachePF m) (hr : PairPF r) :
    CachePF (m.insert n r) := by
  intro k v h
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
  split at h
  · cases h; exact hr
  · exact hm k v (by rw [Std.HashMap.get?_eq_getElem?]; exact h)

/-- K with the caches `PairPF` -/
def KPF (O : RefLawsAOps MkRefd mref cref) (w : Void IO.RealWorld) : Prop :=
  KW O (fun m c => MemoKeysInChild m c ∧ CachePF m ∧ CachePF c) w

/-- K_n with the caches `PairPF` -/
def KPFX (O : RefLawsAOps MkRefd mref cref) (n : Name) (w : Void IO.RealWorld) : Prop :=
  KW O (fun m c => MemoKeysExc n m c ∧ CachePF m ∧ CachePF c) w

theorem stableK_KPF (O : RefLawsAOps MkRefd mref cref) : StableK O.quiet (KPF O) := stableK_KW O _

section WindowPF
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
include M hA

/-- The memo write of a `PairPF` result opens the window: from KPF, returns in KPFX n. -/
theorem triple_memoInsertPS (n : Name) (r : Res) (hr : PairPF r) :
    Triple mctx mref cctx cref (KPF O)
      (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit)
      (fun _ => KPFX O n) (fun e w => KPF O w ∧ OkExc e) := by
  intro w hw
  obtain ⟨a, w', hr'⟩ := refModify_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleSubModuleCache (·.insert n r) w
  have e := hr'
  unfold RunsTo at e
  rw [e]
  obtain ⟨hq, hc, hs, hm⟩ := memoModify_ctx M hA _ hr' hw.1
  refine ⟨hq, hs.trans hw.2.1, ?_⟩
  obtain ⟨h1, h2, h3⟩ := hw.2.2
  rw [hm, hc]
  exact ⟨memoKeysExc_insert n r h1, cachePF_insert n r h2 hr, h3⟩

/-- The child-cache write of a `PairPF` result closes the window: from KPFX n, returns in KPF. -/
theorem triple_childInsertPS (n : Name) (r : Res) (hr : PairPF r) :
    Triple mctx mref cctx cref (KPFX O n)
      (sparkleChildCache.modify (·.insert n r) : MetaM Unit)
      (fun _ => KPF O) (fun e w => KPFX O n w ∧ OkExc e) := by
  intro w hw
  obtain ⟨a, w', hr'⟩ := refModify_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleChildCache (·.insert n r) w
  have e := hr'
  unfold RunsTo at e
  rw [e]
  obtain ⟨hq, hc, hs, hm⟩ := childModify_ctx M hA _ hr' hw.1
  refine ⟨hq, hs.trans hw.2.1, ?_⟩
  obtain ⟨h1, h2, h3⟩ := hw.2.2
  rw [hm, hc]
  exact ⟨memoKeysInChild_of_exc_insert n r h1, h2, cachePF_insert n r h3 hr⟩

omit M hA in
theorem kpfx_of_kpf {n : Name} {w : Void IO.RealWorld} (h : KPF O w) : KPFX O n w :=
  ⟨h.1, h.2.1, memoKeysInChild_exc n h.2.2.1, h.2.2.2⟩

end WindowPF

end Tools.ShippingGen4FKidsEntry

#print axioms Tools.ShippingGen4FKidsEntry.certified_keepsKS
#print axioms Tools.ShippingGen4FKidsEntry.machineCert_keepsKS
#print axioms Tools.ShippingGen4FKidsEntry.triple_memoInsertS
#print axioms Tools.ShippingGen4FKidsEntry.triple_memoInsertPS
#print axioms Tools.ShippingGen4FKidsEntry.triple_childInsertPS
