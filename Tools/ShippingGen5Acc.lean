import Tools.ShippingGen5SemPkg
import Tools.ShippingChildBndCore
set_option autoImplicit false
-- Built in g5ac-r2 at bfa8f81b (Pod `kjob lake build Tools.ShippingGen5Acc`, exit 0; AccCheck: exit 0, TYPE 11 (3 theorems + CallRel by isDefEq, logged), MUTANT 8, AXIOMS standard, CLOSURE OK). Clean build is the coder's.
-- No sorry / axiom / native_decide.

/-! # DG-ACC / DG-ASSIGN units A1-A2 (scripts/gen5/DG_ACC_FREEZE.md rev0 §2, §3, §5.1; rev1 §A)

Pure kernel over a replacement-point kit. Nothing here is DG-SEM's `genSem`, DG-DATAOF's `dataOf` or a `GenData`: they are the
fields of `AssignKit`, each the type the owner's freeze states, and each theorem field is a statement the owner's unit is to prove
(no field is a new law). Integration (A6) instantiates `K` with the owner's constants; the lemmas below are then used as they are
(Q2: the lemmas on the kit are made here; unified with DG-SEM's `genS_some_inv_of_unfold` at integration, see freeze rev1 §A.4).

* A1: `AssignKit`, `entry₀`, `dataOf₀`, `CallEdge`, `callEdge_of_ord`, `genStep`, `genSAcc`, `genS`, `genSAcc_irrel`, `genS_step`,
  `genS_unfold` (locality: only the ordinary callees of the entry are read), `genS_some_inv`.
* A2: `CacheAcc`, `cacheAcc_insert`, `cacheAcc_empty`, `ReachEdge`, `genS_isSome_of_cover`.

Conditional on nothing but the kit's spec fields. `AccServedStmt`, `AccKeepChildStmt`, `GenSFacts`, `CoverAt` are NOT here. -/
namespace Tools.ShippingGen5Acc
open Lean Sparkle.Compiler.Elab Sparkle.IR.Machine Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingChildBndCore (cv)
open Tools.ShippingChildInv (Res)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

/-- C1. The entry constant of `X` exactly as `T1Hyp.defines` / the run reads it. -/
def entry₀ (env₀ : Environment) (X : Name) : Option ConstantInfo :=
  (env₀.find? X).map fun ci =>
    entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀)

/-- Replacement points. `GD E` is DG-SEM's `GenData E (structEnv env₀)`, `dOf` its `.d`. -/
structure AssignKit (ι : Type) (dom : ι → Sparkle.Core.Domain.DomainConfig) (env₀ : Environment) where
  dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData
  GD : ConstantInfo → Type
  dOf : {E : ConstantInfo} → GD E → MachineData
  genData₀ : (E : ConstantInfo) → Option (GD E)
  ordCallees : (d : MachineData) → List (Fin d.shape.insts.length)
  genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} → GD E → SemPkg ι dom
  mem_ordCallees : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
    k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none
  genData₀_dataOf : ∀ {E g}, genData₀ E = some g →
    ((machineShape? false [] E (structEnv env₀)).bind (dataOf E (structEnv env₀))) = some (dOf g)
  genSem_local : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E} (g : GD E),
    (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) →
    genSem Q X g = genSem Q' X g
  genSem_decl : ∀ Q X {E} (g : GD E), (genSem Q X g).decl = X
  genSem_d : ∀ Q X {E} (g : GD E), (genSem Q X g).d = dOf g

section Pure
open Classical

variable {env₀ : Environment} (K : AssignKit ι dom env₀)

/-- C1. The reader data of `X`'s entry. -/
def dataOf₀ (X : Name) : Option MachineData :=
  (entry₀ env₀ X).bind fun E => (machineShape? false [] E (structEnv env₀)).bind (K.dataOf E (structEnv env₀))

theorem dataOf₀_of_genData₀ {X : Name} {E : ConstantInfo} {g : K.GD E} (hE : entry₀ env₀ X = some E)
    (hg : K.genData₀ E = some g) : dataOf₀ K X = some (K.dOf g) := by
  have h := K.genData₀_dataOf hg
  unfold dataOf₀
  rw [hE]
  exact h

/-- C2. Static call edge: ordinary (non-memory-origin) instances only. -/
def CallEdge (X c : Name) : Prop :=
  ∃ d, dataOf₀ K X = some d ∧ ∃ k, ∃ hk : k < d.shape.insts.length,
    (d.shape.instOrigins.getD k .ord).child? = none ∧ (d.shape.insts[k]'hk).1 = c

theorem callEdge_of_ord {X : Name} {E : ConstantInfo} {g : K.GD E} (hE : entry₀ env₀ X = some E)
    (hg : K.genData₀ E = some g) :
    ∀ k ∈ K.ordCallees (K.dOf g), CallEdge K X ((K.dOf g).shape.insts[k]).1 := by
  intro k hk
  exact ⟨K.dOf g, dataOf₀_of_genData₀ K hE hg, k.1, k.2, (K.mem_ordCallees _ k).1 hk, rfl⟩

/-- `CallRel c X := CallEdge X c`: `Acc (CallRel K) X` means every ordinary static callee chain below `X` is well-founded. -/
abbrev CallRel : Name → Name → Prop := flip (CallEdge K)

/-- The step at `X` given the direct callees' values (`Qx` is `none` off the direct callees). Strict: every ordinary callee is `some`. -/
noncomputable def genStep (X : Name) (ih : ∀ c, CallEdge K X c → Option (SemPkg ι dom)) : Option (SemPkg ι dom) :=
  let Qx : Name → Option (SemPkg ι dom) := fun c => if h : CallEdge K X c then ih c h else none
  match entry₀ env₀ X with
  | none => none
  | some E =>
    match K.genData₀ E with
    | none => none
    | some g =>
      if ∀ k ∈ K.ordCallees (K.dOf g), (Qx ((K.dOf g).shape.insts[k]).1).isSome
      then some (K.genSem Qx X g) else none

/-- `Acc.rec` with `motive := fun _ _ => Option (SemPkg ι dom)`. -/
noncomputable def genSAcc : ∀ X, Acc (CallRel K) X → Option (SemPkg ι dom) :=
  fun X h => Acc.rec (motive := fun _ _ => Option (SemPkg ι dom)) (fun X _ ih => genStep K X (fun c hc => ih c hc)) h

noncomputable def genS (X : Name) : Option (SemPkg ι dom) :=
  if h : Acc (CallRel K) X then genSAcc K X h else none

theorem genSAcc_intro (X : Name) (hs : ∀ y, CallRel K y X → Acc (CallRel K) y) :
    genSAcc K X (Acc.intro X hs) = genStep K X (fun c hc => genSAcc K c (hs c hc)) := rfl

theorem genSAcc_irrel (X : Name) (h h' : Acc (CallRel K) X) : genSAcc K X h = genSAcc K X h' := rfl

theorem genS_of_acc (X : Name) (h : Acc (CallRel K) X) : genS K X = genSAcc K X h := by
  unfold genS
  rw [dif_pos h]

theorem genS_of_not_acc (X : Name) (h : ¬ Acc (CallRel K) X) : genS K X = none := by
  unfold genS
  rw [dif_neg h]

theorem genS_step (X : Name) (h : Acc (CallRel K) X) :
    genS K X = genStep K X (fun c _ => genS K c) := by
  rw [genS_of_acc K X h]
  cases h with
  | intro _ hs =>
    rw [genSAcc_intro]
    congr 1
    funext c hc
    exact (genS_of_acc K c (hs c hc)).symm

theorem genS_unfold {X : Name} {E : ConstantInfo} {g : K.GD E} (hacc : Acc (CallRel K) X)
    (hE : entry₀ env₀ X = some E) (hg : K.genData₀ E = some g) :
    genS K X =
      if (∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome)
      then some (K.genSem (genS K) X g) else none := by
  have hQ : ∀ k ∈ K.ordCallees (K.dOf g),
      (fun c => if h : CallEdge K X c then genS K c else none) ((K.dOf g).shape.insts[k]).1 =
        genS K ((K.dOf g).shape.insts[k]).1 := by
    intro k hk
    simp only [dif_pos (callEdge_of_ord K hE hg k hk)]
  have hsem := K.genSem_local (fun c => if h : CallEdge K X c then genS K c else none) (genS K) X g hQ
  have hguard : (∀ k ∈ K.ordCallees (K.dOf g),
      ((fun c => if h : CallEdge K X c then genS K c else none) ((K.dOf g).shape.insts[k]).1).isSome) ↔
      (∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome) :=
    forall_congr' fun k => forall_congr' fun hk => by rw [hQ k hk]
  rw [genS_step K X hacc]
  unfold genStep
  simp only [hE, hg]
  by_cases h : ∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome
  · rw [if_pos h, if_pos (hguard.2 h), hsem]
  · rw [if_neg h, if_neg (fun h' => h (hguard.1 h'))]

theorem genS_some_inv {X : Name} {s : SemPkg ι dom} (hs : genS K X = some s) :
    ∃ (E : ConstantInfo) (g : K.GD E), entry₀ env₀ X = some E ∧ K.genData₀ E = some g ∧ Acc (CallRel K) X ∧
      (∀ k ∈ K.ordCallees (K.dOf g), ∃ sc, genS K ((K.dOf g).shape.insts[k]).1 = some sc) ∧
      s = K.genSem (genS K) X g := by
  by_cases hacc : Acc (CallRel K) X
  · cases hE : entry₀ env₀ X with
    | none =>
      rw [genS_step K X hacc] at hs
      unfold genStep at hs
      simp [hE] at hs
    | some E =>
      cases hg : K.genData₀ E with
      | none =>
        rw [genS_step K X hacc] at hs
        unfold genStep at hs
        simp [hE, hg] at hs
      | some g =>
        rw [genS_unfold K hacc hE hg] at hs
        by_cases h : ∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome
        · rw [if_pos h] at hs
          refine ⟨E, g, rfl, hg, hacc, fun k hk => Option.isSome_iff_exists.1 (h k hk), ?_⟩
          exact (Option.some.inj hs).symm
        · rw [if_neg h] at hs
          cases hs
  · rw [genS_of_not_acc K X hacc] at hs
    cases hs

end Pure

/-! ## A2: `CacheAcc`, reachability closure, strictness closes -/

section A2
open Classical

variable {env₀ : Environment} (K : AssignKit ι dom env₀)

/-- The cache invariant: a REACHED cached key is `Acc`. Restricted to `Reach`, as `CacheShips` (freeze rev0 §5.1). -/
def CacheAcc (Reach : Name → Prop) (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, Reach c → m.get? c = some r → Acc (CallRel K) c

/-- Mirror of `cacheShips_insert` (ShippingGen2KeepChild.lean:255): an unreached key needs nothing. -/
theorem cacheAcc_insert {Reach : Name → Prop} {m : Std.HashMap Name Res} {n : Name} {r : Res}
    (h : CacheAcc K Reach m) (hr : Reach n → Acc (CallRel K) n) :
    CacheAcc K Reach (m.insert n r) := by
  intro c' r' hR h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : n = c' := by simpa using heq
    subst this
    exact hr hR
  · exact h c' r' hR h'

theorem cacheAcc_empty (Reach : Name → Prop) : CacheAcc K Reach {} := by
  intro c r _ h
  simp at h

/-- The least `CallEdge`-closed `Reach` over a top predicate (pure; static edges directly). -/
inductive ReachEdge (Top : Name → Prop) : Name → Prop
  | top {c : Name} : Top c → ReachEdge Top c
  | edge {X c : Name} : ReachEdge Top X → CallEdge K X c → ReachEdge Top c

/-- COVERAGE premise (DG-COVER + DG-WFCOVER + DG-ENV): every name of `Reach` has an entry and reader data. -/
def CoverAt (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∃ (E : ConstantInfo) (g : K.GD E), entry₀ env₀ c = some E ∧ K.genData₀ E = some g

/-- Strictness closes: the ordinary callees of reached names are reached, so `genS` exists on all of `Reach`. -/
theorem genS_isSome_of_cover {Reach : Name → Prop} (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hacc : ∀ c, Reach c → Acc (CallRel K) c) (hcov : CoverAt K Reach) :
    ∀ c, Reach c → ∃ s, genS K c = some s := by
  have key : ∀ c, Acc (CallRel K) c → Reach c → ∃ s, genS K c = some s := by
    intro c h
    induction h with
    | intro c hs ih =>
      intro hc
      obtain ⟨E, g, hE, hg⟩ := hcov c hc
      rw [genS_unfold K (hacc c hc) hE hg]
      have hgd : ∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome := by
        intro k hk
        have he := callEdge_of_ord K hE hg k hk
        obtain ⟨s', hs'⟩ := ih _ he (hcl c _ hc he)
        rw [hs']
        rfl
      rw [if_pos hgd]
      exact ⟨_, rfl⟩
  exact fun c hc => key c (hacc c hc) hc

end A2

end Tools.ShippingGen5Acc
