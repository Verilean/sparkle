import Tools.Assume.FramedACases
import Tools.ShippingChildVC
-- BUILT: kjob lake build Tools.ShippingGen4KWalk exit 0 (317 jobs, rt164, source as of df94a168); axioms standard only. Clean build is the coder's. Foundation of the K walk (scripts/gen4/KWALK_PLAN.md): `K` = every memo key is a child-cache key.
-- Takes `MemoFamily` (TRUSTED, approved freeze rev2 f23b4bc7) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom.
-- No `sorry`, no `axiom`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.

namespace Tools.ShippingGen4KWalk
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.Assume.MemoFamily
open Tools.Assume.FramedACases

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The invariant -/

/-- K: every memo key is a child-cache key. -/
def MemoKeysInChild (m c : Std.HashMap Name Res) : Prop :=
  ∀ k, m.contains k = true → c.contains k = true

/-- K with one in-flight name `n` (the window between a memo write of `n` and the child-cache insert of `n`). -/
def MemoKeysExc (n : Name) (m c : Std.HashMap Name Res) : Prop :=
  ∀ k, m.contains k = true → c.contains k = true ∨ (n == k) = true

/-- The walk invariant over a key relation `P`: quiet, the synthesis ref pinned to `synthesizeChild`, and `P` of the
memo and child-cache contents. -/
def KW (O : RefLawsAOps MkRefd mref cref) (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop)
    (w : Void IO.RealWorld) : Prop :=
  O.quiet w ∧ sv w = some synthesizeChild ∧ P (mv w) (cv w)

/-- K at a world where translator code runs. -/
def KWalk (O : RefLawsAOps MkRefd mref cref) (w : Void IO.RealWorld) : Prop := KW O MemoKeysInChild w

/-- K_n: K with the in-flight name `n`. -/
def KWalkX (O : RefLawsAOps MkRefd mref cref) (n : Name) (w : Void IO.RealWorld) : Prop :=
  KW O (MemoKeysExc n) w

theorem memoKeysInChild_empty (c : Std.HashMap Name Res) : MemoKeysInChild {} c := by
  intro k hk; simp at hk

theorem memoKeysInChild_exc (n : Name) {m c : Std.HashMap Name Res} (h : MemoKeysInChild m c) :
    MemoKeysExc n m c := fun k hk => Or.inl (h k hk)

theorem memoKeysExc_insert (n : Name) (r : Res) {m c : Std.HashMap Name Res} (h : MemoKeysInChild m c) :
    MemoKeysExc n (m.insert n r) c := by
  intro k hk
  rw [Std.HashMap.contains_insert] at hk
  rcases Bool.or_eq_true_iff.mp hk with h1 | h1
  · exact Or.inr h1
  · exact Or.inl (h k h1)

theorem memoKeysInChild_of_exc_insert (n : Name) (r : Res) {m c : Std.HashMap Name Res}
    (h : MemoKeysExc n m c) : MemoKeysInChild m (c.insert n r) := by
  intro k hk
  rw [Std.HashMap.contains_insert]
  rcases h k hk with h1 | h1
  · exact Bool.or_eq_true_iff.mpr (Or.inr h1)
  · exact Bool.or_eq_true_iff.mpr (Or.inl h1)

theorem memoKeysInChild_mono {m c : Std.HashMap Name Res} (f : Std.HashMap Name Res → Std.HashMap Name Res)
    (hf : ∀ c k, c.contains k = true → (f c).contains k = true) (h : MemoKeysInChild m c) :
    MemoKeysInChild m (f c) := fun k hk => hf c k (h k hk)

theorem kw_quiet {O : RefLawsAOps MkRefd mref cref} {P w} (h : KW O P w) : O.quiet w := h.1

/-- Transfer along a step that leaves the child cache, the synthesis ref and the memo as they were. -/
theorem kw_transfer {O : RefLawsAOps MkRefd mref cref} {P : _ → _ → Prop} {w w'}
    (hc : cv w' = cv w) (hs : sv w' = sv w) (hm : mv w' = mv w) (hq : O.quiet w → O.quiet w')
    (h : KW O P w) : KW O P w' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨hq h1, hs.trans h2, by rw [hm, hc]; exact h3⟩

/-! ## FramedNM / MemoAccess are provenance-framed -/

theorem sideRefNM_toSideRef {σ : Type} {r : IO.Ref σ} (h : SideRefNM r) : SideRef r := by
  cases h <;> constructor

theorem framedNM_toA {Fresh : (σ : Type) → IO.Ref σ → Prop} {α : Type} {p : MetaM α}
    (h : FramedNM Fresh p) : FramedA Fresh p := by
  cases h
  case cacheGet => apply FramedA.cacheGet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case synthGet => apply FramedA.synthGet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case depthGet => apply FramedA.depthGet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case sideGet => apply FramedA.sideGet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case sideSet => apply FramedA.sideSet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case sideModify => apply FramedA.sideModify <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case sideModifyGet => apply FramedA.sideModifyGet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case sideModifyGetIO => apply FramedA.sideModifyGetIO <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case sideGetIO => apply FramedA.sideGetIO <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case sideSetIO => apply FramedA.sideSetIO <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case sideModifyIO => apply FramedA.sideModifyIO <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case ioEnv => apply FramedA.ioEnv <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case constInfo => apply FramedA.constInfo <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case env => apply FramedA.env <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case fvarThrowUnknown => apply FramedA.fvarThrowUnknown <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case whnf => apply FramedA.whnf <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case inferType => apply FramedA.inferType <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case isClass? => apply FramedA.isClass? <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case whnfUntil => apply FramedA.whnfUntil <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case instantiateForall => apply FramedA.instantiateForall <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case mkLambdaFVars => apply FramedA.mkLambdaFVars <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case mkAppM => apply FramedA.mkAppM <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case unfoldDefinition? => apply FramedA.unfoldDefinition? <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case reduce => apply FramedA.reduce <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case metaGet => apply FramedA.metaGet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case coreModifyTrace => apply FramedA.coreModifyTrace <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case metaModify => apply FramedA.metaModify <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case freshFVar => apply FramedA.freshFVar <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case monoMs => apply FramedA.monoMs <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case mkExprCache => apply FramedA.mkExprCache <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case exprCacheGet => apply FramedA.exprCacheGet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case exprCacheGetIO => apply FramedA.exprCacheGetIO <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case localMk => apply FramedA.localMk <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case localGet => apply FramedA.localGet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case localSet => apply FramedA.localSet <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case localModify => apply FramedA.localModify <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case localGetIO => apply FramedA.localGetIO <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case localSetIO => apply FramedA.localSetIO <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case localModifyIO => apply FramedA.localModifyIO <;> first | assumption | exact sideRefNM_toSideRef (by assumption)
  case exprCacheModify => apply FramedA.exprCacheModify <;> first | assumption | exact sideRefNM_toSideRef (by assumption)

theorem framedA_of_memoAccess {Fresh : (σ : Type) → IO.Ref σ → Prop} {α : Type} {p : MetaM α}
    (h : MemoAccess p) : FramedA Fresh p := by
  cases h
  case get => exact FramedA.sideGet SideRef.subModule
  case set => exact FramedA.sideSet _ SideRef.subModule
  case modify => exact FramedA.sideModify _ SideRef.subModule
  case modifyGet => exact FramedA.sideModifyGet _ SideRef.subModule
  case modifyGetIO => exact FramedA.sideModifyGetIO _ SideRef.subModule
  case getIO => exact FramedA.sideGetIO SideRef.subModule
  case setIO => exact FramedA.sideSetIO _ SideRef.subModule
  case modifyIO => exact FramedA.sideModifyIO _ SideRef.subModule

variable {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context}

/-- A framed step (memo accesses included) keeps quietness, the child cache and the synthesis ref, and throws only
in the class: everything the memo-free laws say. -/
theorem framedA_ctx (hA : AdmCtx O.quiet mctx cctx) {α : Type} {p : MetaM α} (hp : FramedA MkRefd p)
    {w : Void IO.RealWorld} (hq : O.quiet w) :
    O.quiet (endW mctx mref cctx cref p w) ∧ cv (endW mctx mref cctx cref p w) = cv w ∧
      sv (endW mctx mref cctx cref p w) = sv w ∧ ErrOk mctx mref cctx cref p w := by
  have h1 := O.frame hA p hp w hq
  refine ⟨O.frameQ hA p hp w hq, h1.1, h1.2.1, ?_⟩
  unfold ErrOk
  cases hm : p mctx mref cctx cref w with
  | ok a w1 => exact True.intro
  | error e w1 => exact O.excOk hA p (.framed hp.toFramed) w e w1 hq hm

/-! ## The general step: a `FramedNM` step keeps `KW O P`, for every `P` -/

theorem keeps_KW_framedNM (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
    (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) {α : Type} {p : MetaM α}
    (hp : FramedNM MkRefd p) : Keeps mctx mref cctx cref (KW O P) p := by
  intro w hw
  obtain ⟨hq, hc, hs, he⟩ := framedA_ctx hA (framedNM_toA hp) hw.1
  have hm := M.frame hA p hp w hw.1
  exact ⟨kw_transfer hc hs hm (fun _ => hq) hw, he⟩

/-- The memo `get` keeps `KW O P`: it returns, leaves the memo as it was, and keeps the other three. -/
theorem keeps_KW_memoGet (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
    (P : Std.HashMap Name Res → Std.HashMap Name Res → Prop) :
    Keeps mctx mref cctx cref (KW O P) (sparkleSubModuleCache.get : MetaM (Std.HashMap Name Res)) := by
  intro w hw
  obtain ⟨a, w1, hr⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleSubModuleCache w
  have hp : FramedA MkRefd (sparkleSubModuleCache.get : MetaM (Std.HashMap Name Res)) :=
    framedA_of_memoAccess MemoAccess.get
  obtain ⟨hq, hc, hs, he⟩ := framedA_ctx hA hp hw.1
  have hm := M.memoGet hA a w w1 hr hw.1
  rw [endW_of_runs hr] at hq hc hs
  rw [endW_of_runs hr]
  exact ⟨kw_transfer hc hs hm (fun _ => hq) hw, he⟩

/-! ## The writers: what the family gives at each write -/

/-- Memo `set v`: quiet, `cv`, `sv` as before; memo is `v`. -/
theorem memoSet_ctx (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx) (v : Std.HashMap Name Res)
    {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w') (hq : O.quiet w) :
    O.quiet w' ∧ cv w' = cv w ∧ sv w' = sv w ∧ mv w' = v := by
  have hp : FramedA MkRefd (sparkleSubModuleCache.set v : MetaM Unit) :=
    framedA_of_memoAccess (MemoAccess.set v)
  obtain ⟨hq', hc, hs, _⟩ := framedA_ctx hA hp hq
  rw [endW_of_runs h] at hq' hc hs
  exact ⟨hq', hc, hs, M.memoSet hA v w u w' h hq⟩

/-- Memo `modify f`. -/
theorem memoModify_ctx (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
    (f : Std.HashMap Name Res → Std.HashMap Name Res) {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w') (hq : O.quiet w) :
    O.quiet w' ∧ cv w' = cv w ∧ sv w' = sv w ∧ mv w' = f (mv w) := by
  have hp : FramedA MkRefd (sparkleSubModuleCache.modify f : MetaM Unit) :=
    framedA_of_memoAccess (MemoAccess.modify f)
  obtain ⟨hq', hc, hs, _⟩ := framedA_ctx hA hp hq
  rw [endW_of_runs h] at hq' hc hs
  exact ⟨hq', hc, hs, M.memoModify hA f w u w' h hq⟩

/-- Child-cache `modify f`: quiet, `sv`; cache is `f (cv w)`; memo as before (`frameCacheModify`). -/
theorem childModify_ctx (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
    (f : Std.HashMap Name Res → Std.HashMap Name Res) {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w') (hq : O.quiet w) :
    O.quiet w' ∧ cv w' = f (cv w) ∧ sv w' = sv w ∧ mv w' = mv w := by
  obtain ⟨w1, hg, hs⟩ := modify_split sparkleChildCache f h
  have hq1 := O.frameQ hA _ FramedA.cacheGet w hq
  rw [endW_of_runs hg] at hq1
  exact ⟨O.cacheSetQ hA _ _ _ _ hs hq1, (O.cacheModify' hA f hq h).1, (O.cacheModify' hA f hq h).2.1,
    M.frameCacheModify hA f w u w' h hq⟩

/-! ## The K lifecycle at the writers -/

/-- The depth-0 reset of the memo (`set {}`): K holds, whatever the child cache is. -/
theorem kwalk_memoReset (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx) {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (sparkleSubModuleCache.set {} : MetaM Unit) mctx mref cctx cref w u w')
    (hw : KW O (fun _ _ => True) w) : KWalk O w' := by
  obtain ⟨hq, hc, hs, hm⟩ := memoSet_ctx M hA {} h hw.1
  exact ⟨hq, hs.trans hw.2.1, by rw [hm]; exact memoKeysInChild_empty _⟩

/-- A memo write of `n` opens the window: K gives K_n. -/
theorem kwalk_memoInsert (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx) (n : Name) (r : Res)
    {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit) mctx mref cctx cref w u w')
    (hw : KWalk O w) : KWalkX O n w' := by
  obtain ⟨hq, hc, hs, hm⟩ := memoModify_ctx M hA _ h hw.1
  refine ⟨hq, hs.trans hw.2.1, ?_⟩
  rw [hm, hc]
  exact memoKeysExc_insert n r hw.2.2

/-- The child-cache insert of `n` closes the window: K_n gives K. -/
theorem kwalk_childInsert (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx) (n : Name) (r : Res)
    {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (sparkleChildCache.modify (·.insert n r) : MetaM Unit) mctx mref cctx cref w u w')
    (hw : KWalkX O n w) : KWalk O w' := by
  obtain ⟨hq, hc, hs, hm⟩ := childModify_ctx M hA _ h hw.1
  refine ⟨hq, hs.trans hw.2.1, ?_⟩
  rw [hm, hc]
  exact memoKeysInChild_of_exc_insert n r hw.2.2

/-- Any monotone child-cache `modify` keeps K. -/
theorem kwalk_childMono (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx)
    (f : Std.HashMap Name Res → Std.HashMap Name Res)
    (hf : ∀ c k, c.contains k = true → (f c).contains k = true) {w w' : Void IO.RealWorld} {u : Unit}
    (h : RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w')
    (hw : KWalk O w) : KWalk O w' := by
  obtain ⟨hq, hc, hs, hm⟩ := childModify_ctx M hA f h hw.1
  refine ⟨hq, hs.trans hw.2.1, ?_⟩
  rw [hm, hc]
  exact memoKeysInChild_mono f hf hw.2.2

/-! ## Composition (the generic rules, restated for `KW O P`) -/

theorem keeps_KW_pure {P} {α : Type} (a : α) : Keeps mctx mref cctx cref (KW O P) (Pure.pure a : MetaM α) :=
  Keeps.pure a

theorem keeps_KW_bind {P} {α β : Type} {m : MetaM α} {f : α → MetaM β}
    (h1 : Keeps mctx mref cctx cref (KW O P) m) (h2 : ∀ a, Keeps mctx mref cctx cref (KW O P) (f a)) :
    Keeps mctx mref cctx cref (KW O P) (m >>= f) := Keeps.bind h1 h2

theorem keeps_KW_seq {P} {α β : Type} {m : MetaM α} {n : MetaM β}
    (h1 : Keeps mctx mref cctx cref (KW O P) m) (h2 : Keeps mctx mref cctx cref (KW O P) n) :
    Keeps mctx mref cctx cref (KW O P) (m >>= fun _ => n) := Keeps.bind h1 fun _ => h2

theorem keeps_KW_ite {P} {α : Type} {c : Prop} [Decidable c] {a b : MetaM α}
    (ha : c → Keeps mctx mref cctx cref (KW O P) a) (hb : ¬c → Keeps mctx mref cctx cref (KW O P) b) :
    Keeps mctx mref cctx cref (KW O P) (if c then a else b) := Keeps.ite ha hb

theorem keeps_KW_tryCatch {P} {α : Type} {x : MetaM α} {h : Exception → MetaM α}
    (hx : Keeps mctx mref cctx cref (KW O P) x)
    (hh : ∀ e, OkExc e → Keeps mctx mref cctx cref (KW O P) (h e)) :
    Keeps mctx mref cctx cref (KW O P) (MonadExcept.tryCatch x h) := Keeps.tryCatch hx hh

/-! ## The four combinators, through `MemoTele` -/

theorem kw_tele_transfer (P : _ → _ → Prop) :
    ∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      KW O P w → KW O P w' := fun _ _ hc hs _ hm hq h => kw_transfer hc hs hm hq h

theorem keeps_KW_forallTelescopeReducing (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx) (P) {α : Type}
    (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref (KW O P) (k xs b)) :
    Keeps mctx mref cctx cref (KW O P) (Lean.Meta.forallTelescopeReducing ty k) :=
  M.tele.telescope (KW O P) hA (fun _ h => h.1) (kw_tele_transfer P) ty k hk

theorem keeps_KW_lambdaTelescope (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx) (P) {α : Type}
    (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref (KW O P) (k xs b)) :
    Keeps mctx mref cctx cref (KW O P) (Lean.Meta.lambdaTelescope e k cleanup) :=
  M.tele.lamTelescope (KW O P) hA (fun _ h => h.1) (kw_tele_transfer P) e k cleanup hk

theorem keeps_KW_withLocalDeclD (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx) (P) {α : Type}
    (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref (KW O P) (k x)) :
    Keeps mctx mref cctx cref (KW O P) (Lean.Meta.withLocalDeclD n ty k) :=
  M.tele.localDecl (KW O P) hA (fun _ h => h.1) (kw_tele_transfer P) n ty k hk

theorem keeps_KW_withLetDecl (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx) (P) {α : Type}
    (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref (KW O P) (k x)) :
    Keeps mctx mref cctx cref (KW O P) (Lean.Meta.withLetDecl n ty v k) :=
  M.tele.letDecl (KW O P) hA (fun _ h => h.1) (kw_tele_transfer P) n ty v k hk

#print axioms keeps_KW_framedNM
#print axioms keeps_KW_memoGet
#print axioms kwalk_memoReset
#print axioms kwalk_memoInsert
#print axioms kwalk_childInsert
#print axioms kwalk_childMono
#print axioms keeps_KW_forallTelescopeReducing

end Tools.ShippingGen4KWalk
