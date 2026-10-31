import Tools.ShippingGen5NameKids
import Tools.ShippingSrm12Corr
import Tools.ShippingKid
import Tools.ShippingSrm7Rank
import Tools.ShippingMemOnlyNames
set_option autoImplicit false
-- Pod build (kjob lake build Tools.ShippingGen5NameKids2, exit 0, 685 jobs) on the tree of b870656c; NOT a clean issue-linked build (coder runs that). Written against freeze BOUNDARY_AUDIT_FREEZE_U2.md §3. 7 theorems + 2 definitions (kidNameAt, MemTagsNamed).
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U2: the premises `hn`, `hmemSame`, `hself` from a chosen `nameK`, `MemTagsNamed`, and a rank

Name facts only (freeze U2 §3). `hn_kidNameAt` restates the CHOICE `nameK := kidNameAt shape`; it is not a fact about the
compiler. `MemTagsNamed` of the actual `MachineDefines` shape, the graph/rank premises of `hself_of_rank`, B3-B7 and the G5
joint satisfiability are NOT supplied here. No Laws, no runtime, no compiler definition, no new TRUSTED row. -/

namespace Tools.ShippingGen5NameKids2
open Lean (Name)
open Sparkle.Compiler.Elab (MachineShape)
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Compiler.MachMemory (memChildName memModule)
open Tools.ShippingSrm7Rank (kidModName CallGraph callees declRank rkOf rkOf_edge rkOf_decl)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt TagsAgree tagAgrees)
open Tools.ShippingSrm12Corr (instTagged_mem_idx)

def kidNameAt (shape : MachineShape) (k : Nat) : String :=
  kidModName (((shape.insts[k]?).map Prod.fst).getD Name.anonymous, originAt shape k)

def MemTagsNamed (shape : MachineShape) : Prop :=
  ∀ (k : Nat) (hk : k < shape.insts.length) (cb : Bool) (aw dw : Nat),
    originAt shape k = InstOrigin.mem cb aw dw → (shape.insts[k]'hk).1 = memChildName cb aw dw

private theorem eq_mem_of_memKey {o : InstOrigin} {a : Bool × Nat × Nat} (h : memKey o = some a) :
    o = InstOrigin.mem a.1 a.2.1 a.2.2 := by
  cases o with
  | ord => exact absurd h (by simp [memKey])
  | field i => exact absurd h (by simp [memKey])
  | mem cb aw dw =>
    have e : (cb, aw, dw) = a := Option.some.inj h
    subst e
    rfl

private theorem kidModName_of_none {c : Name} {o : InstOrigin} (h : memKey o = none) : kidModName (c, o) = ofDecl c := by
  cases o with
  | ord => rfl
  | field i => rfl
  | mem cb aw dw => exact absurd h (by simp [memKey])

private theorem eq_mem_of_child {o : InstOrigin} {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (h : o.child? = some y) : ∃ cb aw dw, o = InstOrigin.mem cb aw dw ∧ y = memModule cb aw dw := by
  cases o with
  | ord => cases h
  | field i => cases h
  | mem cb aw dw => exact ⟨cb, aw, dw, rfl, (Option.some.inj h).symm⟩

theorem hn_kidNameAt (shape : MachineShape) :
    ∀ (k : Nat) (hk : k < shape.insts.length),
      kidNameAt shape k = kidModName ((shape.insts[k]'hk).1, originAt shape k) := by
  intro k hk
  simp [kidNameAt, List.getElem?_eq_getElem hk]

theorem memTagsNamed_of_tagsAgree (shape : MachineShape) (h : TagsAgree shape) : MemTagsNamed shape := by
  intro k hk cb aw dw ho
  have h1 := h _ (instTagged_mem_idx shape hk)
  simp only [] at h1
  rw [ho] at h1
  exact of_decide_eq_true (show decide ((shape.insts[k]'hk).1 = memChildName cb aw dw) = true from h1)

theorem hmemSame_of_memTagsNamed (shape : MachineShape) (h : MemTagsNamed shape) :
    ∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      memKey (originAt shape k) ≠ none → memKey (originAt shape k) = memKey (originAt shape k') →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1 := by
  intro k hk k' hk' hne hkey
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  have ha' : memKey (originAt shape k') = some a := by rw [← hkey]; exact ha
  rw [h k hk a.1 a.2.1 a.2.2 (eq_mem_of_memKey ha), h k' hk' a.1 a.2.1 a.2.2 (eq_mem_of_memKey ha')]

theorem hself_of_rank {g : CallGraph} {F r : Nat} {declName : Name} (shape : MachineShape)
    (hgraph : callees g declName = some shape.instTagged) (hr : declRank g F declName = some r) :
    ∀ (k : Nat) (hk : k < shape.insts.length), memKey (originAt shape k) = none →
      (shape.insts[k]'hk).1 ≠ declName := by
  intro k hk hm heq
  obtain ⟨r', hr', hlt⟩ := rkOf_edge hr hgraph (instTagged_mem_idx shape hk)
  rw [kidModName_of_none hm, rkOf_decl, heq, hr] at hr'
  have := Option.some.inj hr'
  omega

theorem kidNameAt_eq_memModule_name (shape : MachineShape) :
    ∀ (k : Nat) (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
      (originAt shape k).child? = some y → kidNameAt shape k = y.1.name := by
  intro k y hy
  obtain ⟨cb, aw, dw, ho, rfl⟩ := eq_mem_of_child hy
  rw [Tools.ShippingMemOnlyNames.memModule_name]
  simp only [kidNameAt]
  rw [ho]
  rfl

theorem memModule_name_ne_ofDecl (shape : MachineShape) :
    ∀ (k : Nat) (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
      (originAt shape k).child? = some y → ∀ (C : Name), y.1.name ≠ ofDecl C := by
  intro k y hy C
  obtain ⟨cb, aw, dw, -, rfl⟩ := eq_mem_of_child hy
  rw [Tools.ShippingMemOnlyNames.memModule_name]
  exact (Tools.ShippingModuleName.ofDecl_ne_ofMem C cb aw dw).symm

theorem sepK_parent_of_supply {g : CallGraph} {F r : Nat} (shape : MachineShape) (declName : Name)
    (hmem : MemTagsNamed shape) (hgraph : callees g declName = some shape.instTagged)
    (hr : declRank g F declName = some r) :
    (∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      kidNameAt shape k = kidNameAt shape k' →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1 ∧ memKey (originAt shape k) = memKey (originAt shape k')) ∧
    (∀ (k : Nat), k < shape.insts.length → kidNameAt shape k ≠ ofDecl declName) :=
  ⟨Tools.ShippingGen5NameKids.hsep_of_kidNames shape.insts (originAt shape) (kidNameAt shape)
      (hn_kidNameAt shape) (hmemSame_of_memTagsNamed shape hmem),
   Tools.ShippingGen5NameKids.hparent_of_kidNames shape.insts (originAt shape) (kidNameAt shape) declName
      (hn_kidNameAt shape) (hself_of_rank shape hgraph hr)⟩

end Tools.ShippingGen5NameKids2
