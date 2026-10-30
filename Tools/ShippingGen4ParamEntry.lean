import Tools.ShippingEntrySoundness
import Tools.ShippingMachineLinked
import Sparkle.IR.Specialize
set_option autoImplicit false
-- NOT BUILT (kjob/g4par-impl; the SHA is synced after `kjob lake build Tools.ShippingGen4ParamEntry`). No sorry / axiom /
-- native_decide; no production edit.

/-! # M4 parametric entry: structure lemmas I1, I2, I3a, I3b, I5a (scripts/gen4/PARAMETRIC_FREEZE.md rev3 §9.1, f0a4698a)

Independent STRUCTURAL lemmas about the symbolic entry and `specializeDesign`; the statements are the frozen ones.
LIMITS (as in the approval):
* I3b (`core_symbolic_reads`) is the existence-world PEEL of a returning run: some world pair reads `ci` and runs
  `synthesizeFromConst` on it. It is NOT a linked run/env guarantee (no relation between the three worlds, no
  environment or cache statement); I3c (depth/cache balance) is not stated.
* I5a (`specializeDesign_ok_facts`) compares module NAMES only (`moduleByName`/`childMap` mapped to `.name`); it says
  nothing about port widths or semantic commutation. It is not `LegalBinding`/success (I5b) and not S3.
* §9.2 semantic interface, I3c, I4, I5b, coverage and FG are not supplied here.
`specializeModuleUnchecked` is file-private; I5a unfolds it with a tactic that names its mangled private constant
(no production edit, no visibility change, no new assumption). -/

namespace Tools.ShippingGen4ParamEntry
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness

/-! ## I1 -/

theorem certifiedShape_off (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (h : (symbolicMode || !parameters.isEmpty) = true) :
    certifiedShape? symbolicMode parameters ci = none := by
  unfold certifiedShape?
  split
  · simp [h]
  · rfl

theorem mixedCertifiedShape_off (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool)
    (h : (symbolicMode || !parameters.isEmpty) = true) :
    mixedCertifiedShape? symbolicMode parameters ci isInst = none := by
  unfold mixedCertifiedShape?
  split
  · simp [h]
  · rfl

theorem machineShape_off (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (senv : StructEnv) (allowInsts : Bool)
    (h : (symbolicMode || !parameters.isEmpty) = true) :
    machineShape? symbolicMode parameters ci senv allowInsts = none := by
  unfold machineShape?
  split
  · simp [h]
  · rfl

theorem entryConst_off (certifiedFrontEnd symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) (inl : Lean.Expr → Lean.Expr)
    (projs : StructEnv) (h : (symbolicMode || !parameters.isEmpty) = true) :
    entryConst certifiedFrontEnd symbolicMode parameters ci isInst inl projs = ci := by
  unfold entryConst
  by_cases hs : symbolicMode = true
  · simp [hs]
  · have hs' : symbolicMode = false := by simpa using hs
    have hp : parameters.isEmpty = false := by simp [hs'] at h; simpa using h
    simp [hs', hp]

theorem runsTo_throw {α : Type} (e : Exception) {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {a : α} :
    ¬ RunsTo (throw e : MetaM α) mctx mref cctx cref w a w' := by
  intro h
  unfold RunsTo at h
  cases h

theorem runsTo_throwError {α : Type} (msg : MessageData) {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {a : α} :
    ¬ RunsTo (throwError msg : MetaM α) mctx mref cctx cref w a w' := by
  intro h
  unfold Lean.throwError at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  exact runsTo_throw _ h

theorem runsTo_pure {α : Type} {x a : α} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (h : RunsTo (pure x : MetaM α) mctx mref cctx cref w a w') : a = x ∧ w' = w := by
  unfold RunsTo at h
  cases h
  exact ⟨rfl, rfl⟩

theorem forIn_unit_yield {l : List (String × Nat)} {Q : String × Nat → Prop}
    {F : String × Nat → PUnit → MetaM (ForInStep PUnit)} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {a : PUnit}
    (h : RunsTo (forIn l PUnit.unit F) mctx mref cctx cref w a w')
    (hF : ∀ x ∈ l, ∀ (r : PUnit) (w w'' : Void IO.RealWorld) (s : ForInStep PUnit),
      RunsTo (F x r) mctx mref cctx cref w s w'' → s = ForInStep.yield PUnit.unit ∧ Q x) :
    ∀ x ∈ l, Q x := by
  induction l generalizing w with
  | nil => intro x hx; cases hx
  | cons y l ih =>
    rw [List.forIn_cons] at h
    obtain ⟨s, w1, h1, h2⟩ := RunsTo.bind h
    obtain ⟨hs, hQ⟩ := hF y (by simp) PUnit.unit w w1 s h1
    subst hs
    simp only at h2
    have := ih h2 (fun x hx => hF x (by simp [hx]))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hQ
    · exact this x hx

theorem finishSynth_symbolic {declName : Name} {parameters : List (String × Nat)}
    {fcs : CircuitState} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (finishSynth declName parameters true fcs) mctx mref cctx cref w (M, D) w') :
    (fcs.module.body.any fun stmt => match stmt with
        | .register .. | .memory .. | .inst .. => true
        | _ => false) = false
    ∧ (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1)
    ∧ Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true
    ∧ M = fcs.module.finalize
    ∧ D = fcs.design := by
  unfold finishSynth at h
  simp only [↓reduceIte] at h
  split at h
  next hb =>
    obtain ⟨_, _, h1, -⟩ := RunsTo.bind h
    exact (runsTo_throwError _ h1).elim
  next hb =>
    obtain ⟨_, w1, h1, h2⟩ := RunsTo.bind h
    have hq := forIn_unit_yield h1 (by
      intro x _ r w w'' s hr
      by_cases hx : (!fcs.module.parameters.any fun parameter => parameter.name == x.fst) = true
      · rw [if_pos hx] at hr
        obtain ⟨_, _, h3, -⟩ := RunsTo.bind hr
        exact (runsTo_throwError _ h3).elim
      · rw [if_neg hx] at hr
        obtain ⟨rfl, -⟩ := runsTo_pure hr
        exact ⟨rfl, by simpa using hx⟩)
    by_cases hc' : ¬ (Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true)
    · rw [if_neg hc'] at h2
      exact (runsTo_throw _ h2).elim
    have hc : Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true := by simpa using hc'
    rw [if_pos hc] at h2
    obtain ⟨he, -⟩ := runsTo_pure h2
    have hb' : (fcs.module.body.any fun stmt => match stmt with
        | .register .. | .memory .. | .inst .. => true
        | _ => false) = false := Bool.eq_false_iff.mpr hb
    have hid : addClockResetIfSequential fcs.module = fcs.module := by
      unfold addClockResetIfSequential
      rw [if_neg]
      intro hr
      obtain ⟨s, hs, hs2⟩ := List.any_eq_true.mp hr
      have := List.any_eq_false.mp hb' s hs
      cases s <;> simp at this hs2
    rw [hid] at he
    have he' := Prod.mk.inj he.symm
    refine ⟨hb', ?_, hc, he'.1.symm, he'.2.symm⟩
    intro p hp
    exact hq p hp

def Tsyn : Lean.Environment → TranslateFn := fun env e hn t n => translateExprToWire env e hn t n
def dupParams (parameters : List (String × Nat)) : Bool :=
  parameters.any fun (name, _) => (parameters.filter fun (other, _) => other == name).length > 1
def zeroParam (parameters : List (String × Nat)) : Bool :=
  parameters.any fun (_, v) => v == 0

theorem core_symbolic_prologue {translate : Lean.Environment → TranslateFn} {declName : Name}
    {parameters : List (String × Nat)} {cfe : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (synthesizeCombinationalCoreWith translate declName parameters true cfe)
      mctx mref cctx cref w (M, D) w') :
    dupParams parameters = false ∧ zeroParam parameters = false := by
  unfold synthesizeCombinationalCoreWith at h
  simp only [↓reduceIte] at h
  by_cases hd : dupParams parameters = true
  · have hd' : (parameters.any fun x => decide ((List.filter (fun x_1 => x_1.fst == x.fst) parameters).length > 1)) = true := hd
    rw [if_pos hd'] at h
    obtain ⟨_, _, h1, -⟩ := RunsTo.bind h
    exact (runsTo_throwError _ h1).elim
  · have hd' : ¬ (parameters.any fun x => decide ((List.filter (fun x_1 => x_1.fst == x.fst) parameters).length > 1)) = true := hd
    rw [if_neg hd'] at h
    obtain ⟨_, w1, h1, -⟩ := RunsTo.bind h
    have hq := forIn_unit_yield (Q := fun x : String × Nat => (x.2 == 0) = false) h1 (by
      intro x _ r w w'' s hr
      by_cases hx : (x.snd == 0) = true
      · rw [if_pos hx] at hr
        obtain ⟨_, _, h3, -⟩ := RunsTo.bind hr
        exact (runsTo_throwError _ h3).elim
      · rw [if_neg hx] at hr
        obtain ⟨rfl, -⟩ := runsTo_pure hr
        exact ⟨rfl, by simpa using hx⟩)
    refine ⟨Bool.eq_false_iff.mpr hd, ?_⟩
    unfold zeroParam
    apply List.any_eq_false.mpr
    intro x hx
    have := hq x hx
    simpa using this

theorem core_symbolic_prologue_throws {translate : Lean.Environment → TranslateFn} {declName : Name}
    {parameters : List (String × Nat)} {cfe : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    (h : (dupParams parameters || zeroParam parameters) = true)
    (r : Sparkle.IR.AST.Module × Design) (w' : Void IO.RealWorld) :
    ¬ RunsTo (synthesizeCombinationalCoreWith translate declName parameters true cfe)
      mctx mref cctx cref w r w' := by
  intro hr
  obtain ⟨h1, h2⟩ := core_symbolic_prologue hr
  simp [h1, h2] at h

set_option maxHeartbeats 1600000 in
theorem core_symbolic_reads {declName : Name} {parameters : List (String × Nat)}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
      mctx mref cctx cref w (M, D) w') :
    ∃ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (Tsyn envR) logProf declName parameters true true ci
        (instancePredicate envR)) mctx mref cctx cref w3 (M, D) w4 := by
  have hp := core_symbolic_prologue h
  unfold synthesizeCombinationalCoreWith at h
  simp only [↓reduceIte] at h
  have hd' : ¬ (parameters.any fun x => decide ((List.filter (fun x_1 => x_1.fst == x.fst) parameters).length > 1)) = true := by
    have := hp.1
    unfold dupParams at this
    simpa using this
  rw [if_neg hd'] at h
  obtain ⟨_, w1, h1, h⟩ := RunsTo.bind h
  iterate 40 (all_goals (first | peel_bind h | peel_ite h | skip))
  all_goals (
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    rw [entryConst_off _ _ _ _ _ _ _ (by simp)] at h
    exact ⟨_, env, ci, _, w2, _, _, _, _, hget, henv, h⟩)

open Lean Elab Tactic in
/-- unfold the file-private `specializeModuleUnchecked` at a hypothesis -/
elab "unfold_spec_unchecked " "at " h:ident : tactic => do
  let n := (Name.mkNum (`_private ++ `Sparkle.IR.Specialize) 0) ++ `Sparkle.IR.Specialize.specializeModuleUnchecked
  evalTactic (← `(tactic| unfold $(mkIdent n):ident at $h:ident))

inductive F2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : F2 R [] []
  | cons {a b l l'} : R a b → F2 R l l' → F2 R (a :: l) (b :: l')

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {k : α → Except ε β} {b : β}
    (h : (x >>= k) = .ok b) : ∃ a, k a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, h⟩

 except_bind_ok' {ε α β : Type} {x : Except ε α} {k : α → Except ε β} {b : β}
    (h : (x >>= k) = .ok b) : ∃ a, x = .ok a ∧ k a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem F2_mono {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) {l : List α}
    {l' : List β} (h : F2 R l l') : F2 S l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hRS _ _ hab) ih

theorem F2_map_name {l l' : List Sparkle.IR.AST.Module}
    (h : F2 (fun a b => b.name = a.name) l l') : l'.map (·.name) = l.map (·.name) := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hab, ih]

theorem F2_params {l l' : List Sparkle.IR.AST.Module}
    (h : F2 (fun _ b => b.parameters = []) l l') : ∀ m ∈ l', m.parameters = [] := by
  induction h with
  | nil => intro m hm; cases hm
  | cons hab _ ih =>
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hab
    · exact ih m hm

theorem mapM_forall2 {α β : Type} {f : α → Except String β} {l : List α} {l' : List β}
    (h : l.mapM f = .ok l') : F2 (fun a b => f a = .ok b) l l' := by
  induction l generalizing l' with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure] at h
    cases h
    exact .nil
  | cons a l ih =>
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hf : f a with
    | error e => rw [hf] at h; cases h
    | ok b =>
      rw [hf] at h
      simp only at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        simp only at h
        cases h
        exact .cons hf (ih hl)

theorem find_name_forall2 {l l' : List Sparkle.IR.AST.Module}
    (h : F2 (fun a b => b.name = a.name) l l') (mn : String) :
    (l'.find? (fun c => c.name == mn)).map (·.name) = (l.find? (fun c => c.name == mn)).map (·.name) := by
  induction h with
  | nil => rfl
  | @cons a b l1 l2 hab _ ih =>
    simp only [List.find?_cons, hab]
    cases hc : a.name == mn
    · exact ih
    · simp [hab]

theorem specializeDesign_ok_facts {design D' : Design} {bindings : Sparkle.IR.Specialize.Bindings}
    (h : Sparkle.IR.Specialize.specializeDesign design bindings = .ok D') :
    (design.findModule design.topModule).isSome = true
    ∧ D'.topModule = design.topModule
    ∧ D'.modules.map (·.name) = design.modules.map (·.name)
    ∧ (∀ m ∈ D'.modules, m.parameters = [])
    ∧ (∀ mn : String,
        (Sparkle.IR.Machine.moduleByName D'.modules mn).map (·.name)
          = (Sparkle.IR.Machine.moduleByName design.modules mn).map (·.name))
    ∧ (∀ mn : String,
        (Tools.ShippingMachineLinked.childMap D'.modules mn).map (fun c => c.1.name)
          = (Tools.ShippingMachineLinked.childMap design.modules mn).map (fun c => c.1.name)) := by
  unfold Sparkle.IR.Specialize.specializeDesign at h
  by_cases hn : (design.findModule design.topModule).isNone = true
  · simp only [hn, ↓reduceIte] at h
    simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · have hn' : (design.findModule design.topModule).isNone = false := Bool.eq_false_iff.mpr hn
    simp only [hn', Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, -, h⟩ := except_bind_ok' h
    obtain ⟨mods, hmods, h⟩ := except_bind_ok' h
    have hD : D' = { topModule := design.topModule, modules := mods } := by
      have : (Except.ok { topModule := design.topModule, modules := mods } : Except String Design) = Except.ok D' := h
      exact (Except.ok.inj this).symm
    have hf := mapM_forall2 hmods
    have hR : F2 (fun a b => b.name = a.name ∧ b.parameters = []) design.modules mods := by
      refine F2_mono ?_ hf
      intro a b hab
      unfold_spec_unchecked at hab
      obtain ⟨_, hab⟩ := except_bind_ok hab
      obtain ⟨_, hab⟩ := except_bind_ok hab
      obtain ⟨_, hab⟩ := except_bind_ok hab
      obtain ⟨_, hab⟩ := except_bind_ok hab
      obtain ⟨_, hab⟩ := except_bind_ok hab
      cases hab
      exact ⟨rfl, rfl⟩
    have hN : F2 (fun a b => b.name = a.name) design.modules mods := F2_mono (fun _ _ h => h.1) hR
    have hP : F2 (fun _ b => b.parameters = []) design.modules mods := F2_mono (fun _ _ h => h.2) hR
    subst hD
    refine ⟨?_, rfl, F2_map_name hN, F2_params hP, fun mn => find_name_forall2 hN mn, ?_⟩
    · cases hfm : design.findModule design.topModule <;> simp_all
    · intro mn
      have := find_name_forall2 hN mn
      simp only [Tools.ShippingMachineLinked.childMap, Option.map_map, Sparkle.IR.Machine.moduleByName]
      simpa [Function.comp_def] using this

end Tools.ShippingGen4ParamEntry
