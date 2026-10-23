import Tools.ShippingHierStateG
import Tools.ShippingMachineShipsDepth
set_option autoImplicit false
-- BUILT (unit SRM21): dev runs l1 (exit 1), l2 (exit 1), l3 (exit 1), l4 (exit 0); the final-SHA rebuild in REPORT-SRM21.md is the only final evidence.
-- SCOPE: generic lemmas for the question "can `QDepthLift raw D b` (SRM20) be derived from source facts?".  Statements are those fixed in scripts/srm21/EXPECTED.txt before this file existed.
--  * a step-wise simulation of two `KStep`s (`evalAssignsKG_sim`, `stepModuleTG_sim`, `runModuleTG_sim`) under a relation `R` on instance states;
--  * `stepModuleTG_instFree`: ONE step of an instance-free module (`runModuleTG_instFree` is the run version);
--  * (P1) `GrandInstFree`/`QGrandInstFree` (Props on `D.modules` through `childMap`), (P2) `runModuleTG_depth2_depth1_of_grandInstFree`, (P3) `resetNk_depth_lift`.
-- `runKS_instFree` is about the RUN of an instance-free child (`runKS`); the depth-2 vs depth-1 step of an instance that is NOT instance-free itself is compared here step by step.
-- PREMISE (not proved here): `GrandInstFree` for a concrete design.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm21Lift
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked
open Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingMachineShipsDepth Tools.ShippingMachineDepth
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RegDedup (declWidth)

/-! ## Simulation of two child steps -/

/-- The results of two steps agree on the environment and are `R`-related on the state (both fail, or both succeed). -/
def SimO {σ₂ σ₁ : Type} (R : σ₂ → σ₁ → Prop) : Option (Env × σ₂) → Option (Env × σ₁) → Prop
  | none, none => True
  | some (e, s), some (e', s') => e = e' ∧ R s s'
  | _, _ => False

/-- Module states are related: registers and memories equal, instance states `R`-related. -/
def KCorr {σ₂ σ₁ : Type} (R : σ₂ → σ₁ → Prop) (s₂ : KState σ₂) (s₁ : KState σ₁) : Prop :=
  s₂.st = s₁.st ∧ s₂.mems = s₁.mems ∧ ∀ i, R (s₂.kids i) (s₁.kids i)

theorem evalAssignsKG_sim {σ₂ σ₁ : Type} (KS₂ : KStep σ₂) (KS₁ : KStep σ₁) (R : σ₂ → σ₁ → Prop)
    (we : WEnv) (children : String → Option (Module × WEnv)) (kids₂ : String → σ₂) (kids₁ : String → σ₁) (mems : MEnv)
    (hk : ∀ i, R (kids₂ i) (kids₁ i)) :
    ∀ (body : List Stmt) (env : Env) (acc₂ : String → σ₂) (acc₁ : String → σ₁),
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe, children mn = some (child, cwe) →
        ∀ cin env' s₂ s₁, R s₂ s₁ → SimO R (KS₂ child cwe cin env' s₂) (KS₁ child cwe cin env' s₁)) →
      (∀ i, R (acc₂ i) (acc₁ i)) →
      SimO (fun a₂ a₁ => ∀ i, R (a₂ i) (a₁ i))
        (evalAssignsKG KS₂ we children kids₂ mems body env acc₂) (evalAssignsKG KS₁ we children kids₁ mems body env acc₁)
  | [], env, acc₂, acc₁, _, ha => by
    simp only [evalAssignsKG]
    exact ⟨rfl, ha⟩
  | .assign l r :: rest, env, acc₂, acc₁, hs, ha => by
    simp only [evalAssignsKG]
    cases hv : evalExpr we env r with
    | none => simp [SimO]
    | some v =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      exact evalAssignsKG_sim KS₂ KS₁ R we children kids₂ kids₁ mems hk rest _ acc₂ acc₁
        (fun mn iname conns hm => hs mn iname conns (List.mem_cons_of_mem _ hm)) ha
  | .register .. :: rest, env, acc₂, acc₁, hs, ha => by
    simp only [evalAssignsKG]
    exact evalAssignsKG_sim KS₂ KS₁ R we children kids₂ kids₁ mems hk rest _ acc₂ acc₁
      (fun mn iname conns hm => hs mn iname conns (List.mem_cons_of_mem _ hm)) ha
  | .memory name aw dw c wa wd we' ra rd cr ew er :: rest, env, acc₂, acc₁, hs, ha => by
    have hs' : ∀ mn iname conns, Stmt.inst mn iname conns ∈ rest → ∀ child cwe, children mn = some (child, cwe) →
        ∀ cin env' s₂ s₁, R s₂ s₁ → SimO R (KS₂ child cwe cin env' s₂) (KS₁ child cwe cin env' s₁) :=
      fun mn iname conns hm => hs mn iname conns (List.mem_cons_of_mem _ hm)
    cases cr with
    | false =>
      simp only [evalAssignsKG, Bool.false_eq_true, if_false]
      exact evalAssignsKG_sim KS₂ KS₁ R we children kids₂ kids₁ mems hk rest _ acc₂ acc₁ hs' ha
    | true =>
      simp only [evalAssignsKG, if_true]
      cases hc : comboReads we mems name aw dw ((ra, rd) :: er) env with
      | none => simp [SimO]
      | some env' =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        exact evalAssignsKG_sim KS₂ KS₁ R we children kids₂ kids₁ mems hk rest _ acc₂ acc₁ hs' ha
  | .inst mn iname conns :: rest, env, acc₂, acc₁, hs, ha => by
    have hs' : ∀ mn iname conns, Stmt.inst mn iname conns ∈ rest → ∀ child cwe, children mn = some (child, cwe) →
        ∀ cin env' s₂ s₁, R s₂ s₁ → SimO R (KS₂ child cwe cin env' s₂) (KS₁ child cwe cin env' s₁) :=
      fun mn iname conns hm => hs mn iname conns (List.mem_cons_of_mem _ hm)
    simp only [evalAssignsKG]
    cases hc : children mn with
    | none => simp [SimO]
    | some p =>
      obtain ⟨child, cwe⟩ := p
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hst := hs mn iname conns List.mem_cons_self child cwe hc (inConns child.outputs conns) env _ _ (hk iname)
      cases h2 : KS₂ child cwe (inConns child.outputs conns) env (kids₂ iname) with
      | none =>
        cases h1 : KS₁ child cwe (inConns child.outputs conns) env (kids₁ iname) with
        | none => simp [SimO]
        | some q => rw [h2, h1] at hst; exact hst.elim
      | some q2 =>
        cases h1 : KS₁ child cwe (inConns child.outputs conns) env (kids₁ iname) with
        | none => rw [h2, h1] at hst; exact hst.elim
        | some q1 =>
          rw [h2, h1] at hst
          obtain ⟨cres, ks'⟩ := q2
          obtain ⟨cres', ks1'⟩ := q1
          obtain ⟨hce, hks⟩ := hst
          subst hce
          simp only [Option.bind_some]
          exact evalAssignsKG_sim KS₂ KS₁ R we children kids₂ kids₁ mems hk rest _ _ _ hs'
            (fun n => by
              by_cases hn : n = iname
              · simp only [hn, if_true]; exact hks
              · simp only [hn, if_false]; exact ha n)

theorem stepModuleTG_sim {σ₂ σ₁ : Type} (KS₂ : KStep σ₂) (KS₁ : KStep σ₁) (R : σ₂ → σ₁ → Prop)
    (we : WEnv) (children : String → Option (Module × WEnv)) (body : List Stmt)
    (hs : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe, children mn = some (child, cwe) →
        ∀ cin env' s₂ s₁, R s₂ s₁ → SimO R (KS₂ child cwe cin env' s₂) (KS₁ child cwe cin env' s₁))
    (env0 : Env) (s₂ : KState σ₂) (s₁ : KState σ₁) (hc : KCorr R s₂ s₁) :
    SimO (KCorr R) (stepModuleTG KS₂ we children body env0 s₂) (stepModuleTG KS₁ we children body env0 s₁) := by
  obtain ⟨h1, h2, h3⟩ := hc
  have hE := evalAssignsKG_sim KS₂ KS₁ R we children s₂.kids s₁.kids s₁.mems h3 body env0 s₂.kids s₁.kids hs h3
  simp only [stepModuleTG, h1, h2]
  cases hE₂ : evalAssignsKG KS₂ we children s₂.kids s₁.mems body env0 s₂.kids with
  | none =>
    cases hE₁ : evalAssignsKG KS₁ we children s₁.kids s₁.mems body env0 s₁.kids with
    | none => simp [SimO]
    | some q => rw [hE₂, hE₁] at hE; exact hE.elim
  | some q2 =>
    cases hE₁ : evalAssignsKG KS₁ we children s₁.kids s₁.mems body env0 s₁.kids with
    | none => rw [hE₂, hE₁] at hE; exact hE.elim
    | some q1 =>
      rw [hE₂, hE₁] at hE
      obtain ⟨envF, k2⟩ := q2
      obtain ⟨envF', k1⟩ := q1
      obtain ⟨hee, hkk⟩ := hE
      subst hee
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases hN : regNexts we s₁.mems body envF with
      | none => simp [SimO]
      | some nexts =>
        simp only [Option.bind_some]
        cases hM : memNexts we body s₁.mems envF with
        | none => simp [SimO]
        | some mems' =>
          simp only [Option.bind_some]
          exact ⟨rfl, rfl, rfl, hkk⟩

theorem runModuleTG_sim {σ₂ σ₁ : Type} (KS₂ : KStep σ₂) (KS₁ : KStep σ₁) (R : σ₂ → σ₁ → Prop)
    (we : WEnv) (children : String → Option (Module × WEnv)) (body : List Stmt)
    (hs : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe, children mn = some (child, cwe) →
        ∀ cin env' s₂ s₁, R s₂ s₁ → SimO R (KS₂ child cwe cin env' s₂) (KS₁ child cwe cin env' s₁))
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (s₂ : KState σ₂) (s₁ : KState σ₁), KCorr R s₂ s₁ →
      runModuleTG KS₂ we children body seed k s₂ = runModuleTG KS₁ we children body seed k s₁
  | 0, _, _, _ => rfl
  | k + 1, s₂, s₁, hc => by
    have hst := stepModuleTG_sim KS₂ KS₁ R we children body hs (seed k s₂.st) s₂ s₁ hc
    have hsd : seed k s₂.st = seed k s₁.st := by rw [hc.1]
    rw [hsd] at hst
    simp only [runModuleTG]
    rw [hsd]
    cases h2 : stepModuleTG KS₂ we children body (seed k s₁.st) s₂ with
    | none =>
      cases h1 : stepModuleTG KS₁ we children body (seed k s₁.st) s₁ with
      | none => simp
      | some q => rw [h2, h1] at hst; exact hst.elim
    | some q2 =>
      cases h1 : stepModuleTG KS₁ we children body (seed k s₁.st) s₁ with
      | none => rw [h2, h1] at hst; exact hst.elim
      | some q1 =>
        rw [h2, h1] at hst
        obtain ⟨envF, t2⟩ := q2
        obtain ⟨envF', t1⟩ := q1
        obtain ⟨hee, hkk⟩ := hst
        subst hee
        have hrec := runModuleTG_sim KS₂ KS₁ R we children body hs seed k t2 t1 hkk
        simp [hrec]

/-! ## One step of an instance-free module -/

theorem stepModuleTG_instFree {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (body : List Stmt) (hf : instFree body)
    (env0 : Env) (s : KState σ) :
    stepModuleTG KS we children body env0 s =
      (stepModule we body env0 s.mems).map fun r => (r.1, (⟨applyNexts s.st r.2.1, r.2.2, s.kids⟩ : KState σ)) := by
  simp only [stepModuleTG, stepModule, evalAssignsKG_instFree KS we children s.kids s.mems body env0 s.kids hf]
  cases hE : evalAssigns we s.mems body env0 with
  | none => rfl
  | some envF =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    cases hN : regNexts we s.mems body envF with
    | none => rfl
    | some nexts =>
      simp only [Option.bind_some]
      cases hM : memNexts we body s.mems envF with
      | none => rfl
      | some mems' => rfl

/-! ## (P1) the real-data Prop, the correspondence, (P2), (P3) -/

/-- **(P1)** every module reached at depth 2 from `body` (an instance of an instance) is instance-free: stated on `D.modules` through `childMap`. -/
def GrandInstFree (D : Design) (body : List Stmt) : Prop :=
  ∀ (mn1 i1 : String) (c1 : List (String × Expr)) (gc1 : Module) (w1 : WEnv),
    Stmt.inst mn1 i1 c1 ∈ body → childMap D.modules mn1 = some (gc1, w1) →
    ∀ (mn2 i2 : String) (c2 : List (String × Expr)) (gc2 : Module) (w2 : WEnv),
      Stmt.inst mn2 i2 c2 ∈ gc1.body → childMap D.modules mn2 = some (gc2, w2) → instFree gc2.body

/-- (P1) for the shipped body (run agreement) and for the core body `raw` (`ResetNk` ranges over `raw.body`). -/
def QGrandInstFree (raw : Module) (D : Design) (b : Module) : Prop :=
  GrandInstFree D (checkedOptimize b).body ∧ GrandInstFree D raw.body

/-- depth-1 grandchild state vs depth-0 grandchild state: registers and memories equal -/
def GkCorr (g2 : KT 1) (g1 : KT 0) : Prop := KState.st g2 = KidState.st g1 ∧ KState.mems g2 = KidState.mems g1

/-- depth-2 instance state vs depth-1 instance state -/
def KidCorr (k2 : KT 2) (k1 : KT 1) : Prop :=
  KState.st k2 = KState.st k1 ∧ KState.mems k2 = KState.mems k1 ∧ ∀ gi : String, GkCorr (KState.kids k2 gi) (KState.kids k1 gi)

/-- an instance-free grandchild steps the same at depth 1 as flat -/
theorem simO_instFree_step (C : String → Option (Module × WEnv)) (gc : Module) (cwe : WEnv) (hf : instFree gc.body)
    (cin : List (String × Expr)) (env : Env) (g2 : KT 1) (g1 : KT 0) (h : GkCorr g2 g1) :
    SimO GkCorr (KSn C 1 gc cwe cin env g2) (KSn C 0 gc cwe cin env g1) := by
  obtain ⟨h1, h2⟩ := h
  show SimO GkCorr (stepModuleTG (KSn C 0) cwe C gc.body (connEnvS cin env (KState.st g2)) g2)
    (flatKS gc cwe cin env g1)
  rw [stepModuleTG_instFree _ _ _ _ hf]
  simp only [flatKS]
  rw [h1, h2]
  cases stepModule cwe gc.body (connEnvS cin env (KidState.st g1)) (KidState.mems g1) with
  | none => simp [SimO]
  | some r => exact ⟨rfl, rfl, rfl⟩

/-- **(P2)** the depth-2 and the depth-1 run of the shipped body agree from related instance states, given (P1) for the shipped body -/
theorem runModuleTG_depth2_depth1_of_grandInstFree (D : Design) (b : Module)
    (hf : GrandInstFree D (checkedOptimize b).body)
    (kids2 : String → KT 2) (kids1 : String → KT 1) (hc : ∀ i, KidCorr (kids2 i) (kids1 i))
    (seed : Nat → (String → Nat) → Env) (T : Nat) (st0 : String → Nat) (mems : MEnv) :
    runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules) (checkedOptimize b).body seed T
        (⟨st0, mems, kids2⟩ : KState (KT 2)) =
    runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules) (checkedOptimize b).body seed T
        (⟨st0, mems, kids1⟩ : KState (KT 1)) := by
  refine runModuleTG_sim (KSn (childMap D.modules) 2) (KSn (childMap D.modules) 1) KidCorr _ _ _ ?_ seed T _ _ ⟨rfl, rfl, hc⟩
  intro mn iname conns hm child cwe hch cin env s₂ s₁ hs
  obtain ⟨hst, hmm, hkk⟩ := hs
  show SimO KidCorr (stepModuleTG (KSn (childMap D.modules) 1) cwe (childMap D.modules) child.body (connEnvS cin env (KState.st s₂)) s₂)
    (stepModuleTG (KSn (childMap D.modules) 0) cwe (childMap D.modules) child.body (connEnvS cin env (KState.st s₁)) s₁)
  rw [show KState.st s₂ = KState.st s₁ from hst]
  exact stepModuleTG_sim (KSn (childMap D.modules) 1) (KSn (childMap D.modules) 0) GkCorr cwe (childMap D.modules) child.body
    (fun mn2 i2 c2 hm2 gc2 cwe2 hch2 cin' env' g2 g1 hg =>
      simO_instFree_step (childMap D.modules) gc2 cwe2 (hf mn iname conns child cwe hm hch mn2 i2 c2 gc2 cwe2 hm2 hch2) cin' env' g2 g1 hg)
    _ s₂ s₁ ⟨hst, hmm, hkk⟩

/-- the all-zero instance state used for the (unused) great-grandchildren of an instance-free grandchild -/
def emptyKid : KidState := ⟨fun _ => 0, fun _ _ => 0⟩

/-- **(P3)** the `ResetNk` depth lift, given (P1) for `raw.body`: kids2 copies each instance's and grandchild's registers and memories from kids1 -/
theorem resetNk_depth_lift (raw : Module) (D : Design) (hf : GrandInstFree D raw.body)
    (kids1 : String → KT 1) (h : ResetNk 1 raw D kids1) :
    ∃ kids2 : String → KT 2, ResetNk 2 raw D kids2 ∧ ∀ i, KidCorr (kids2 i) (kids1 i) := by
  refine ⟨fun i => (⟨KState.st (kids1 i), KState.mems (kids1 i),
      fun gi => (⟨KidState.st (KState.kids (kids1 i) gi), KidState.mems (KState.kids (kids1 i) gi), fun _ => emptyKid⟩ : KState KidState)⟩ :
      KState (KT 1)), ?_, fun i => ⟨rfl, rfl, fun gi => ⟨rfl, rfl⟩⟩⟩
  intro i mc ⟨conns, hinst⟩ hmod
  obtain ⟨a, b, c, d⟩ := h i mc ⟨conns, hinst⟩ hmod
  refine ⟨a, b, c, ?_⟩
  intro mn iname conns' mc' hinst2 hmb
  obtain ⟨e1, e2, e3, -⟩ := d mn iname conns' mc' hinst2 hmb
  refine ⟨e1, e2, e3, ?_⟩
  intro mn' iname' conns'' mc'' hinst3 _
  have hfree := hf mc.name i conns mc (declWidth mc) hinst (by simp [childMap, hmod]) mn iname conns' mc' (declWidth mc') hinst2
    (by simp [childMap, hmb])
  have := hfree _ hinst3
  simp [Sparkle.IR.Machine.isInst] at this

end Tools.ShippingSrm21Lift
