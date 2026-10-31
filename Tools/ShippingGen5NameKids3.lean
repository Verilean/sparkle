import Tools.ShippingGen5NameKids2
set_option autoImplicit false
-- NOT BUILT: no build of this file has been recorded yet. Written against freeze BOUNDARY_AUDIT_FREEZE_U3.md §3 (+ §7 amendments). 5 theorems + 5 definitions.
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U3: rank propagation and `hself` / `sepK` / `parent` for all reached declarations

Conditional statements (freeze U3 §3). `GraphAgrees`, `ReachSpans`, `InClass` of the top and `MemTagsNamed` of each reached shape are
PREMISES; none is supplied here. No Laws, no runtime, no compiler definition, no new TRUSTED row. -/

namespace Tools.ShippingGen5NameKids3
open Lean (Name)
open Sparkle.Compiler.Elab (MachineShape)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingSrm7Rank (CallGraph callees declRank InClass kidModName rkOf_edge rkOf_decl inClass_rank)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGen5NameKids2 (MemTagsNamed kidNameAt hself_of_rank sepK_parent_of_supply)
open Tools.ShippingSrm12Corr (instTagged_exists_idx)

/-- an edge of the call graph through an ORDINARY (non-memory) call entry -/
def OrdEdge (g : CallGraph) (a b : Name) : Prop :=
  ∃ (ks : List (Name × InstOrigin)) (o : InstOrigin), callees g a = some ks ∧ (b, o) ∈ ks ∧ memKey o = none

/-- the graph carries exactly the reached declarations' tagged call entries -/
def GraphAgrees (g : CallGraph) (Reach : Name → Prop) (S : Name → Option MachineShape) : Prop :=
  ∀ c, Reach c → callees g c = (S c).map MachineShape.instTagged

/-- `T1Hyp.closed`, restated over `S` -/
def ReachClosed (Reach : Name → Prop) (S : Name → Option MachineShape) : Prop :=
  ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
    (sp.instOrigins.getD k InstOrigin.ord).child? = none → Reach (sp.insts[k]'hk).1

/-- the reflexive-transitive closure of `OrdEdge g` from `top` -/
inductive OrdPath (g : CallGraph) (top : Name) : Name → Prop
  | refl : OrdPath g top top
  | step {a b : Name} : OrdPath g top a → OrdEdge g a b → OrdPath g top b

/-- every reached declaration is reachable from `top` through ordinary edges (the converse of `ReachClosed`; NOT supplied by this unit) -/
def ReachSpans (g : CallGraph) (top : Name) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → OrdPath g top c

private theorem kidModName_of_none {c : Name} {o : InstOrigin} (h : memKey o = none) :
    kidModName (c, o) = Sparkle.IR.ModuleName.ofDecl c := by
  cases o with
  | ord => rfl
  | field i => rfl
  | mem cb aw dw => exact absurd h (by simp [memKey])

private theorem child_none_of_memKey_none {o : InstOrigin} (h : memKey o = none) : o.child? = none := by
  cases o with
  | ord => rfl
  | field i => rfl
  | mem cb aw dw => exact absurd h (by simp [memKey])

theorem rank_of_ordEdge {g : CallGraph} {F r : Nat} {a b : Name}
    (hr : declRank g F a = some r) (he : OrdEdge g a b) :
    ∃ r', declRank g F b = some r' ∧ r' < r := by
  obtain ⟨ks, o, hks, hmem, hm⟩ := he
  obtain ⟨r', hr', hlt⟩ := rkOf_edge hr hks hmem
  rw [kidModName_of_none hm, rkOf_decl] at hr'
  exact ⟨r', hr', hlt⟩

theorem rank_of_reach {g : CallGraph} {F r : Nat} {top c : Name}
    (hr : declRank g F top = some r) (hc : OrdPath g top c) :
    ∃ r', declRank g F c = some r' ∧ r' ≤ r := by
  induction hc with
  | refl => exact ⟨r, hr, Nat.le_refl r⟩
  | step _ he ih =>
    obtain ⟨r1, h1, hle⟩ := ih
    obtain ⟨r2, h2, hlt⟩ := rank_of_ordEdge h1 he
    exact ⟨r2, h2, by omega⟩

theorem reach_of_ordEdges {g : CallGraph} {Reach : Name → Prop} {S : Name → Option MachineShape} {top c : Name}
    (hg : GraphAgrees g Reach S) (hcl : ReachClosed Reach S) (ht : Reach top)
    (hc : OrdPath g top c) : Reach c := by
  induction hc with
  | refl => exact ht
  | step _ he ih =>
    rename_i a b _
    obtain ⟨ks, o, hks, hmem, hm⟩ := he
    have hga := hg a ih
    rw [hks] at hga
    cases hS : S a with
    | none => rw [hS] at hga; cases hga
    | some sp =>
      rw [hS] at hga
      have hks' : ks = sp.instTagged := Option.some.inj hga
      subst hks'
      obtain ⟨k, hk, hbo⟩ := instTagged_exists_idx sp hmem
      have e1 : b = (sp.insts[k]'hk).1 := congrArg Prod.fst hbo
      have e2 : o = originAt sp k := congrArg Prod.snd hbo
      subst e1
      refine hcl a ih sp hS k hk ?_
      rw [e2] at hm
      exact child_none_of_memKey_none hm

theorem hself_all_reached {g : CallGraph} {B r : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach) :
    ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      memKey (originAt sp k) = none → (sp.insts[k]'hk).1 ≠ c := by
  intro c hc sp hS
  obtain ⟨r0, h0, -, -⟩ := inClass_rank hin
  obtain ⟨r', hr', -⟩ := rank_of_reach h0 (hsp c hc)
  have hgc : callees g c = some sp.instTagged := by rw [hg c hc, hS]; rfl
  exact hself_of_rank sp hgc hr'

theorem sepK_parent_all_reached {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach)
    (hmem : ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp) :
    ∀ c, Reach c → ∀ sp, S c = some sp →
      (∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
        kidNameAt sp k = kidNameAt sp k' →
        (sp.insts[k]'hk).1 = (sp.insts[k']'hk').1 ∧ memKey (originAt sp k) = memKey (originAt sp k')) ∧
      (∀ (k : Nat), k < sp.insts.length → kidNameAt sp k ≠ Sparkle.IR.ModuleName.ofDecl c) := by
  intro c hc sp hS
  obtain ⟨r0, h0, -, -⟩ := inClass_rank hin
  obtain ⟨r', hr', -⟩ := rank_of_reach h0 (hsp c hc)
  have hgc : callees g c = some sp.instTagged := by rw [hg c hc, hS]; rfl
  exact sepK_parent_of_supply sp c (hmem c hc sp hS) hgc hr'

end Tools.ShippingGen5NameKids3
