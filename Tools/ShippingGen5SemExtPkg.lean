import Tools.ShippingGen5SemExt
import Tools.ShippingGen5T2Tie
import Tools.ShippingGen5T2Range
set_option autoImplicit false
-- Pod build exit 0 (kjob lake build Tests.Gen5.SemExtPkgCheck, 749 jobs) ONLY with the one-line S1 pattern fix of `callField_at` in Tools/ShippingGen5T2Tie.lean (43977202) applied as an UNCOMMITTED local patch: at 1c300db6 Tools.ShippingGen5T2Tie itself does not elaborate. Clean build is the coder's. No sorry/axiom/native_decide.
/-! # DG-SEM U5E (scripts/gen5/DG_SEM_FREEZE_P4E.md §5.2, rev3 §6): `GenExtAtCall` for a package whose forgotten data is `genSemI`

`Tools.ShippingGen2.GenExtAtCall p q k hk` (T2-TIE's `hDG_SEM`) from `p.toSem = genSemI (semOf P) X g`, the callee package `hq`, and
`hord` (call `k` is not a memory origin). `hnd` is derived from `t2r_ok_outNames_nodup q.d q.ok`; `callKind ≠ .domain` from `g.wf` (RowB).
Conditional on `hp`, `hq`, `hord`; nothing here supplies them for a real run, nor `CallOutRange`, causality, ACC, M5 or FG. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Sparkle.Compiler.MachInstOrigin

theorem genExtAtCall_of_genSem {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Name)
    (g : GenIn) (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hq : P (p.d.shape.insts[k]'hk).1 = some q)
    (hord : (originOf p.d k).child? = none) :
    Tools.ShippingGen2.GenExtAtCall p q k hk := by
  have hd : p.d = g.d := by rw [← d_toSem, hp, genSemI_d]
  have hgen : genSemI (semOf P) X g = .gen (genSemGen (semOf P) X g) := by
    unfold genSemI
    rw [if_neg]
    have : g.d.shape.insts ≠ [] := by
      intro h
      rw [hd, h] at hk
      exact absurd hk (by simp)
    simp [this]
  rw [hgen] at hp
  have hkD : p.kD = kDOf g.d := by
    rw [← kD_toSem, hp]; rfl
  have hextS : p.extS = (SemPkg.gen (genSemGen (semOf P) X g)).extS := by rw [← extS_toSem, hp]
  have hextBS : p.extBS = (SemPkg.gen (genSemGen (semOf P) X g)).extBS := by rw [← extBS_toSem, hp]
  have hlsrc : p.lsrc = (SemPkg.gen (genSemGen (semOf P) X g)).lsrc := by rw [← lsrc_toSem, hp]
  have hkn : k < g.d.shape.insts.length := hd ▸ hk
  rcases hinst : (p.d.shape.insts[k]'hk) with ⟨c, a, κ0⟩
  have hk' : g.d.shape.insts[k]? = some (c, a, κ0) := by
    rw [← hd, List.getElem?_eq_getElem hk, hinst]
  rw [hinst] at hq
  have hno : ∀ cb aw dw, originOf g.d k ≠ .mem cb aw dw := by
    intro cb aw dw h
    rw [hd, h] at hord
    simp [InstOrigin.child?] at hord
  have hκ : ((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain = callKind g.d k := by
    rw [hd, hkD]; rfl
  have hQ : semOf P c = some q.toSem := by simp [semOf, hq]
  have hnd : g.d.shape.instFields ≠ [] → (q.toSem.d.shape.layout.outs.map (·.name)).Nodup := by
    intro _
    rw [d_toSem]
    exact Tools.ShippingGen2.t2r_ok_outNames_nodup q.d q.ok
  have hnodom : callKind g.d k ≠ .domain := by
    have hwf := g.wf
    unfold GenWF at hwf
    have hB : RowB g.d = true := by
      simp only [Bool.and_eq_true] at hwf
      exact hwf.1.2
    unfold RowB at hB
    have h2 := List.all_eq_true.mp hB k (List.mem_range.mpr hkn)
    simp only [Bool.and_eq_true] at h2
    have h3 := h2.1
    intro hc
    rw [hc] at h3
    simp at h3
  intro i bools bits k' o f ho hcf hf
  have hsel : selIdx g.d q.toSem k = some k' := by
    refine selIdx_of_callField g.d q.toSem k k' o (by rw [d_toSem]; exact ho) ?_ hnd
    rw [d_toSem]
    unfold Tools.ShippingGen2.CallField at hcf
    rw [hd] at hcf
    exact hcf
  have hl := lsrcAt_genSemGen (semOf P) X g i bools bits
  dsimp only at hl
  unfold Tools.ShippingGen2.decA Tools.ShippingGen2.decB at hf
  rw [hinst, hlsrc] at hf
  dsimp only at hf
  rw [← hl] at hf
  rw [← src_toSem, ← d_toSem, ← kD_toSem] at hf
  let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen (semOf P) X g).body i bools bits)
  have heq := calleeOut_eq_src (semOf P) g i Sst (extBOf (semOf P) g i bools bits Sst)
    (extOf (semOf P) g i bools bits Sst) k c a κ0 q.toSem k' f hk' hQ hsel hf
  rw [hκ, hkD, hextS, hextBS]
  rcases hκc : callKind g.d k with _ | _ | w
  · exact absurd hκc hnodom
  · intro τ
    have h1 := ext_call_final_bool (semOf P) g i bools bits Sst k c a κ0 hk' hno hκc
    have h2 : (extBOf (semOf P) g i bools bits Sst (kDOf g.d + k)).val τ = (f τ != 0) := by
      rw [h1]; dsimp only; rw [heq]
    exact h2
  · intro τ
    have h1 := ext_call_final_bits (semOf P) g i bools bits Sst k c a κ0 w hk' hno hκc
    have h2 : (extOf (semOf P) g i bools bits Sst (kDOf g.d + k) w).val τ = BitVec.ofNat w (f τ) := by
      rw [h1]; dsimp only; rw [heq]
    exact h2

end Tools.ShippingGen5Sem
