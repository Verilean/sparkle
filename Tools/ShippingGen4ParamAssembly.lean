import Tools.ShippingGen4FKids
import Tools.ShippingGen4FKidsObl
import Tools.ShippingGen4FTop
import Tools.ShippingGen4Shape
import Tools.ShippingGen4ParamBridgeLegal
import Tools.ShippingGen4ParamBridgeSpecExpr
set_option autoImplicit false

/-! # M4 parametric assembly (scripts/gen4/PARAM_ASSEMBLY.md): `LegalBinding` and `AllPos` from a real run -/

namespace Tools.ShippingGen4ParamAssembly
open Tools.ShippingGen4FKids Tools.ShippingGen4FKidsParams Tools.ShippingGen4FKidsObl Tools.ShippingGen4FTop Tools.ShippingGen4Shape
open Tools.ShippingGen4ParamEntry Tools.ShippingLegacySem Tools.ShippingGen4ParamIface Tools.ShippingGen4ParamBridgeLegal Tools.ShippingGen4ParamLayerA
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
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele
open Tools.ShippingGen4KWalkDepth
open Tools.Assume.FramedACases
open Tools.ShippingGen4FKidsDepth
open Tools.ShippingGen4FKidsEntryArms
open Tools.ShippingGen4FKidsDepthEntry
open Tools.ShippingGen4FKidsLegacyTail
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4KWalkEntryCore
open Tools.ShippingGen4FKidsDepthArms
open Tools.ShippingChildLegacyTailA
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingGen4FKidsTranslate
open Tools.ShippingGen4FKidsLegacyArm
open Tools.ShippingGen4FKidsFallback
open Tools.ShippingGen4FKidsLegacyCached
open Tools.ShippingGen4FKidsDepthInduct
open Tools.ShippingGen4FKidsLegacyFinal
open Tools.ShippingGen4FKidsDepthTop
open Tools.ShippingGen4ParamEntry
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingLegacySem Tools.ShippingGen4ParamEntry
open Tools.ShippingGen4ParamIface Tools.ShippingGen4ParamBridgeLegal Tools.ShippingGen4ParamLayerA


/-! ## 1. The constructive direction of `validateBindings`

`legal_of_facts` is the converse of `legal_facts` (ParamBridgeLegal): the five clauses (a)-(e) of the private
`validateBindings`, each stated as a Lean proposition, give `LegalBinding`. -/

theorem filter_len_one {names : List String} (h : names.Nodup) :
    ∀ a ∈ names, (names.filter (· == a)).length = 1 := by
  induction names with
  | nil => intro a ha; cases ha
  | cons x t ih =>
    intro a ha
    have hn := List.nodup_cons.mp h
    by_cases hx : x = a
    · subst hx
      have : t.filter (· == x) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hbx
        have : b = x := by simpa using hbx
        exact hn.1 (this ▸ hb)
      simp [List.filter_cons, this]
    · have hat : a ∈ t := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hx
        · exact h
      have hxa : (x == a) = false := by simpa using hx
      simp [List.filter_cons, hxa, ih hn.2 a hat]

theorem dupName_none (names : List String) (h : names.Nodup) :
    names.find? (fun name => decide ((names.filter (· == name)).length > 1)) = none := by
  rw [List.find?_eq_none]
  intro a ha
  simp [filter_len_one h a ha]

theorem forIn_all_yield {α : Type} (l : List α) (f : α → PUnit → Except String (ForInStep PUnit))
    (h : ∀ a ∈ l, f a PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn l PUnit.unit f = .ok PUnit.unit := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.forIn_cons, h x List.mem_cons_self]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem legal_of_facts {D : Design} {θ : List (String × Nat)}
    (ha : ∀ m ∈ D.modules, (m.parameters.map (·.name)).Nodup)
    (hb : (θ.map (·.1)).Nodup)
    (hc : ∀ p ∈ θ, ∃ m ∈ D.modules, ∃ q ∈ m.parameters, q.name = p.1)
    (hd : ∀ p ∈ θ, p.2 ≠ 0)
    (he : ∀ m ∈ D.modules, ∀ q ∈ m.parameters, ∃ v, θ.lookup q.name = some v) :
    LegalBinding D θ := by
  unfold LegalBinding
  unfold_priv validateBindings
  unfold_priv validateParameterDeclarations
  unfold_priv duplicateName?
  rw [forIn_all_yield D.modules _ (by
    intro m hm
    dsimp only
    rw [dupName_none _ (ha m hm)]
    rfl)]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dupName_none _ hb]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [forIn_all_yield θ _ (by
    intro p hp
    obtain ⟨name, value⟩ := p
    obtain ⟨m, hm, q, hq, hqn⟩ := hc (name, value) hp
    have hcont : (List.flatMap (fun hardwareModule => List.map (fun x => x.name) hardwareModule.parameters) D.modules).contains name = true := by
      rw [List.contains_iff_mem]
      exact List.mem_flatMap.mpr ⟨m, hm, List.mem_map.mpr ⟨q, hq, hqn⟩⟩
    have hv : (value == 0) = false := by simpa using hd (name, value) hp
    have hmem : ∃ a, a ∈ D.modules ∧ ∃ a_1, a_1 ∈ a.parameters ∧ a_1.name = name := ⟨m, hm, q, hq, hqn⟩
    simp [hcont, hv, pure, Except.pure, hmem])]
  rw [forIn_all_yield _ _ (by
    intro name hn
    obtain ⟨m, hm, hmq⟩ := List.mem_flatMap.mp hn
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmq
    obtain ⟨v, hv⟩ := he m hm q hq
    simp [hv, pure, Except.pure])]

/-! ## 2. A returning `synthesizeFromConst` run reads a definition -/

theorem sfc_defn
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : MReturns (synthesizeFromConst translate logProf declName parameters true cfe ci isInst) (M, D)) :
    ∃ dv, ci = .defnInfo dv := by
  cases ci with
  | defnInfo dv => exact ⟨dv, rfl⟩
  | _ =>
    exfalso
    unfold synthesizeFromConst at hr
    simp only [certifiedShape_off true parameters _ (by simp),
      mixedCertifiedShape_off true parameters _ isInst (by simp), ite_self,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hr
    all_goals (
      obtain ⟨y, hy, a3⟩ := MReturns.bind hr
      obtain rfl := MReturns.pure hy
      dsimp only at a3
      obtain ⟨y2, hy2, h2⟩ := MReturns.bind a3
      obtain rfl := MReturns.pure hy2
      dsimp only at h2
      obtain ⟨_, _, h3⟩ := MReturns.bind h2
      unfold Lean.throwError at h3
      obtain ⟨_, _, h4⟩ := MReturns.bind h3
      obtain ⟨_, _, h5⟩ := MReturns.bind h4
      exact MReturns.throw h5)

/-! ## 3. Facts about θ and the declared names -/

theorem keys_nodup_of_dupParams {θ : List (String × Nat)} (h : dupParams θ = false) :
    (θ.map (·.1)).Nodup := by
  unfold dupParams at h
  have h1 : ∀ p ∈ θ, ¬ ((θ.filter fun q => q.1 == p.1).length > 1) := by
    intro p hp
    have := List.any_eq_false.mp h p hp
    simpa using this
  clear h
  induction θ with
  | nil => exact List.nodup_nil
  | cons p t ih =>
    rw [List.map_cons, List.nodup_cons]
    have hfc : ∀ r : String × Nat, ((p :: t).filter fun q => q.1 == r.1).length ≥ (t.filter fun q => q.1 == r.1).length := by
      intro r
      rw [List.filter_cons]
      split <;> simp
    refine ⟨?_, ih (fun (r : String × Nat) hr => fun hlen => h1 r (List.mem_cons_of_mem _ hr) (Nat.lt_of_lt_of_le hlen (hfc r)))⟩
    intro hmem
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hmem
    have hpos : 0 < (t.filter fun x => x.1 == p.1).length :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨hq, by simpa using hqp⟩)
    apply h1 p List.mem_cons_self
    rw [List.filter_cons]
    simp only [beq_self_eq_true, ↓reduceIte, List.length_cons]
    omega

theorem allPos_of_zeroParam {θ : List (String × Nat)} (h : zeroParam θ = false) : AllPos θ := by
  intro p hp
  unfold zeroParam at h
  have := List.any_eq_false.mp h p hp
  have h2 : (p.2 == 0) = false := by simpa using this
  exact Nat.pos_of_ne_zero (by intro hz; simp [hz] at h2)

theorem lookup_some_of_mem_keys {θ : List (String × Nat)} {n : String} (h : n ∈ θ.map (·.1)) :
    ∃ v, θ.lookup n = some v := by
  induction θ with
  | nil => simp at h
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.lookup]
    by_cases hk : (n == k) = true
    · simp [hk]
    · have hk' : n ≠ k := by simpa using hk
      have : n ∈ t.map (·.1) := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h hk'
        · exact h
      simp [hk, ih this]

theorem legal_names_declared {D : Design} {θ : List (String × Nat)} (h : LegalBinding D θ) :
    ∀ p ∈ θ, ∃ m ∈ D.modules, ∃ q ∈ m.parameters, q.name = p.1 := by
  unfold LegalBinding at h
  unfold_priv validateBindings at h
  obtain ⟨_, -, h⟩ := except_bind_ok' h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · obtain ⟨_, h1, h⟩ := except_bind_ok' h
    have e1 := Tools.ShippingGen4ParamBridgeLegal.forIn_yield_each _ _ (by
      intro a
      split <;> (try split) <;> simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]) h1
    intro p hp
    have := e1 p hp
    obtain ⟨name, value⟩ := p
    by_cases hc : (List.flatMap (fun hardwareModule => List.map (fun x => x.name) hardwareModule.parameters) D.modules).contains name = true
    · rw [List.contains_iff_mem] at hc
      obtain ⟨m, hm, hmq⟩ := List.mem_flatMap.mp hc
      obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hmq
      exact ⟨m, hm, q, hq, hqn⟩
    · exfalso
      dsimp only at this
      have hc' : (!(List.flatMap (fun hardwareModule => List.map (fun x => x.name) hardwareModule.parameters) D.modules).contains name) = true := by
        simpa using hc
      rw [if_pos hc'] at this
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at this


variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem run_facts {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O) (htel : LamTelescopeN)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {θ : List (String × Nat)}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hw : KWD O (fun _ _ => True) 0 w)
    (h : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w') :
    (θ.map (·.1)).Nodup ∧ AllPos θ ∧
    (M'.parameters.map (·.name)).Nodup ∧ (∀ p ∈ θ, ∃ q ∈ M'.parameters, q.name = p.1) ∧
    (∀ q ∈ M'.parameters, ∃ v, θ.lookup q.name = some v) ∧
    (∀ x ∈ D'.modules, x.parameters = []) := by
  obtain ⟨M0, D0, w1, hcore, hMp, -, -, -, -⟩ := fpost_run_top h
  obtain ⟨hdup, hzero⟩ := core_symbolic_prologue hcore
  obtain ⟨logProf, envR, ci, w1', w2, w3, w4, w5, w6, -, -, hsyn⟩ := core_symbolic_reads hcore
  obtain ⟨dv, rfl⟩ := sfc_defn hsyn.mreturns
  obtain ⟨-, hcov, -⟩ := fTop_out htel hsyn.mreturns
  obtain ⟨hnd, hsub⟩ := fKidsObl_params M hmsg hA hw h
  refine ⟨keys_nodup_of_dupParams hdup, allPos_of_zeroParam hzero, hnd, ?_, ?_, fKidsObl_noGuard M hmsg hA hw h⟩
  · intro p hp
    obtain ⟨q, hq, hqn⟩ := hcov p hp
    exact ⟨q, hMp ▸ hq, hqn⟩
  · intro q hq
    exact lookup_some_of_mem_keys (hsub q hq)


/-- A module of the returned design has the top's name: the `any` branch of `SpecDesign`. -/
def Collides (M' : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design) : Prop :=
  ∃ x ∈ D'.modules, x.name = M'.name

theorem specDesign_of_collides {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : Collides M' D') : SpecDesign M' D' = D' := by
  obtain ⟨x, hx, e⟩ := h
  unfold SpecDesign
  rw [if_pos (List.any_eq_true.mpr ⟨x, hx, by simpa using e⟩)]

theorem specDesign_of_not_collides {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : ¬ Collides M' D') : SpecDesign M' D' = D'.addModule M' :=
  specDesign_eq_addModule (fun x hx e => h ⟨x, hx, e⟩)

theorem legal_assembly {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hmsg : MsgMvK O) (htel : LamTelescopeN)
    {mctx cctx} (hA : AdmCtx O.quiet mctx cctx) {declName : Name} {θ : List (String × Nat)}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hw : KWD O (fun _ _ => True) 0 w)
    (h : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w') :
    AllPos θ ∧
    (¬ Collides M' D' → LegalBinding (SpecDesign M' D') θ) ∧
    (Collides M' D' → (LegalBinding (SpecDesign M' D') θ ↔ θ = [])) := by
  obtain ⟨hθ, hpos, hnd, hcov, hbound, hfree⟩ := run_facts M hmsg htel hA hw h
  refine ⟨hpos, fun hnc => ?_, fun hc => ?_⟩
  · rw [specDesign_of_not_collides hnc]
    refine legal_of_facts ?_ hθ ?_ (fun p hp => Nat.pos_iff_ne_zero.mp (hpos p hp)) ?_
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · rw [hfree m hm]; exact List.nodup_nil
      · rw [List.mem_singleton.mp hm]; exact hnd
    · intro p hp
      obtain ⟨q, hq, hqn⟩ := hcov p hp
      exact ⟨M', List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)), q, hq, hqn⟩
    · intro m hm q hq
      rcases List.mem_append.mp hm with hm | hm
      · rw [hfree m hm] at hq; cases hq
      · rw [List.mem_singleton.mp hm] at hq; exact hbound q hq
  · rw [specDesign_of_collides hc]
    constructor
    · intro hl
      cases hθ' : θ with
      | nil => rfl
      | cons p t =>
        exfalso
        obtain ⟨m, hm, q, hq, -⟩ := legal_names_declared hl p (hθ' ▸ List.mem_cons_self)
        rw [hfree m hm] at hq; cases hq
    · intro he
      subst he
      refine legal_of_facts ?_ hθ (fun p hp => by cases hp) (fun p hp => by cases hp) ?_
      · intro m hm; rw [hfree m hm]; exact List.nodup_nil
      · intro m hm q hq; rw [hfree m hm] at hq; cases hq

end Tools.ShippingGen4ParamAssembly

#print axioms Tools.ShippingGen4ParamAssembly.legal_of_facts
#print axioms Tools.ShippingGen4ParamAssembly.run_facts
#print axioms Tools.ShippingGen4ParamAssembly.legal_assembly
