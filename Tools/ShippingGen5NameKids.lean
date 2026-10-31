import Tools.ShippingSrm7Rank
import Tools.ShippingMemClosesKidsT
import Tools.ShippingModuleName
set_option autoImplicit false
-- NOT BUILT (unit U1 of BOUNDARY-AUDIT; scripts/gen5/BOUNDARY_AUDIT_FREEZE.md §1.3). No clean build has been run on this file yet.
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U1: separation of kid module names

Name algebra only: five statements about `kidModName` / `memKey`, typed as in freeze §1.3. They derive the
`hsep` / `hparent` binder shapes of `machineClosesAtA_of_memKids'` FROM the premises `hn` (the name of each kid is
`kidModName (callee, origin)`), `hmemSame` and `hself`. Those three premises remain and are not discharged here, so this is
not the supply of N1 as a whole; B3 `hparentD`, B4 `hdisjD`, B5 `hfresh`, B7 `hn` stay OPEN. No Laws, no runtime, no
compiler definition, no new TRUSTED row. -/

namespace Tools.ShippingGen5NameKids
open Lean (Name)
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingSrm7Rank (kidModName)
open Tools.ShippingMemCloses (memKey)

private theorem kidModName_of_none {c : Name} {o : InstOrigin} (h : memKey o = none) : kidModName (c, o) = ofDecl c := by
  cases o with
  | ord => rfl
  | field i => rfl
  | mem cb aw dw => exact absurd h (by simp [memKey])

private theorem kidModName_of_some {c : Name} {o : InstOrigin} {k : Bool × Nat × Nat} (h : memKey o = some k) :
    kidModName (c, o) = ofMem k.1 k.2.1 k.2.2 := by
  cases o with
  | ord => exact absurd h (by simp [memKey])
  | field i => exact absurd h (by simp [memKey])
  | mem cb aw dw =>
    have e : (cb, aw, dw) = k := Option.some.inj h
    subst e
    rfl

theorem kidModName_inj_nonmem {c c' : Name} {o o' : InstOrigin}
    (h : memKey o = none) (h' : memKey o' = none)
    (e : kidModName (c, o) = kidModName (c', o')) : c = c' := by
  rw [kidModName_of_none h, kidModName_of_none h'] at e
  exact Tools.ShippingModuleName.ofDecl_injective e

theorem kidModName_ne_mem {c c' : Name} {o o' : InstOrigin} (h : memKey o = none) (h' : memKey o' ≠ none) :
    kidModName (c, o) ≠ kidModName (c', o') := by
  obtain ⟨k', hk'⟩ := Option.ne_none_iff_exists'.mp h'
  rw [kidModName_of_none h, kidModName_of_some hk']
  exact Tools.ShippingModuleName.ofDecl_ne_ofMem c _ _ _

theorem kidModName_inj_mem {c c' : Name} {o o' : InstOrigin} {k k' : Bool × Nat × Nat}
    (h : memKey o = some k) (h' : memKey o' = some k')
    (e : kidModName (c, o) = kidModName (c', o')) : k = k' := by
  rw [kidModName_of_some h, kidModName_of_some h'] at e
  obtain ⟨e1, e2, e3⟩ := Tools.ShippingModuleName.ofMem_injective e
  exact Prod.ext e1 (Prod.ext e2 e3)

theorem hsep_of_kidNames {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hmemSame : ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length),
      memKey (org k) ≠ none → memKey (org k) = memKey (org k') → (insts[k]'hk).1 = (insts[k']'hk').1) :
    ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length), nameK k = nameK k' →
      (insts[k]'hk).1 = (insts[k']'hk').1 ∧ memKey (org k) = memKey (org k') := by
  intro k hk k' hk' e
  rw [hn k hk, hn k' hk'] at e
  by_cases hm : memKey (org k) = none
  · by_cases hm' : memKey (org k') = none
    · exact ⟨kidModName_inj_nonmem hm hm' e, hm.trans hm'.symm⟩
    · exact absurd e (kidModName_ne_mem hm hm')
  · by_cases hm' : memKey (org k') = none
    · exact absurd e.symm (kidModName_ne_mem hm' hm)
    · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hm
      obtain ⟨a', ha'⟩ := Option.ne_none_iff_exists'.mp hm'
      have hk2 : a = a' := kidModName_inj_mem ha ha' e
      have hmk : memKey (org k) = memKey (org k') := by rw [ha, ha', hk2]
      exact ⟨hmemSame k hk k' hk' hm hmk, hmk⟩

theorem hparent_of_kidNames {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (declName : Name)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hself : ∀ (k : Nat) (hk : k < insts.length), memKey (org k) = none → (insts[k]'hk).1 ≠ declName) :
    ∀ (k : Nat), k < insts.length → nameK k ≠ ofDecl declName := by
  intro k hk e
  rw [hn k hk] at e
  by_cases hm : memKey (org k) = none
  · rw [kidModName_of_none hm] at e
    exact hself k hk hm (Tools.ShippingModuleName.ofDecl_injective e)
  · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hm
    rw [kidModName_of_some ha] at e
    exact Tools.ShippingModuleName.ofDecl_ne_ofMem declName _ _ _ e.symm

end Tools.ShippingGen5NameKids
