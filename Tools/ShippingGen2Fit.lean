import Tools.ShippingHierOptRun
import Tools.ShippingMachineEntry
set_option autoImplicit false

/-! # S4-BD basics: the run-local fit (scripts/gen2/S4_FIT_FREEZE.md rev2 §1, §2 c4)

BUILT: g2fit-bbca065d at bbca065d and g2fc-c6951eb8 at c6951eb8 (exit 0; standard axioms).

* `KSBoundedRun`: on ONE run `envs`, every wire an instance's output port drives fits that port's width.
  No child invariant, no quantification over environments (contrast `KSBoundedIn`, HierOptRun.lean:658).
* `fitX_of_runR`: `fitX_of_run` (HierOptRun.lean:668) with `Inv`, `hKSb`, `hnd` and the kids-invariant premise
  replaced by `KSBoundedRun` on the run's own `envs`; `hIW` is kept.
* `posEnc_lt`: the encoded value of a binder fits the binder kind's hardware width.

The opens mirror Tools/ShippingHierOptRun.lean (lines 27-33), plus that namespace itself. -/
namespace Tools.ShippingGen2Fit
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.HierCheck
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierStateG
open Tools.ShippingHierState Tools.ShippingHierOptLinked
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingHierOptRun

/-- **The run-local fit**: at every cycle `j` of the run `envs`, every wire `x` that an instance of `body`
connects to an output port `p` of its child carries a value below `2 ^ p.ty.bitWidth`. -/
def KSBoundedRun (children : String → Option (Module × WEnv)) (body : List Stmt) (envs : List Env) : Prop :=
  ∀ j (hj : j < envs.length), ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
    children mn = some (child, cwe) → ∀ p ∈ child.outputs, ∀ x,
      conns.lookup p.name = some (.ref x) → (envs[j]'hj) x < 2 ^ p.ty.bitWidth

/-- **The extracted inputs fit along a linked run, from the run-local fit**: the instance-driven ones by
`KSBoundedRun` on the same `envs` at their ports' widths (`instOutWidthsOk`), the others are never written
and keep their start values. A copy of `fitX_of_run` (Tools/ShippingHierOptRun.lean:668-763) without
`Inv`, `hKSb`, `hnd` and the kids-invariant premise. -/
theorem fitX_of_runR {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv)) (m : Module)
    (ins : Nat → String → Nat) (hwf : linkedWF children m.body = true)
    (hIW : instOutWidthsOk children (declWidth m) m.body = true) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs →
      KSBoundedRun children m.body envs →
      (∀ x ∈ (openIns m).map (·.name), x ∉ bodyInstOuts children m.body →
        s.st x < 2 ^ declWidth m x) →
      ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
        (envs[j]'hj) x < 2 ^ declWidth m x
  | 0, _, envs, h, _, _, j, hj, _, _ => by
    simp only [runModuleTG, Option.some.injEq] at h; subst h; cases hj
  | k + 1, s, envs, h, hB, hst, j, hj, x, hx => by
    have hmf := memFree_of_linkedWF _ hwf
    simp only [runModuleTG] at h
    cases hS : stepModuleTG KS (declWidth m) children m.body (seedIn m ins k s.st) s with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, s'⟩ := r
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG KS (declWidth m) children m.body (seedIn m ins) k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    unfold stepModuleTG at hS
    cases hK : evalAssignsKG KS (declWidth m) children s.kids s.mems m.body
        (seedIn m ins k s.st) s.kids with
    | none => simp [hK] at hS
    | some ek =>
    obtain ⟨envF', kids'⟩ := ek
    cases hN : regNexts (declWidth m) s.mems m.body envF' with
    | none => simp [hK, hN] at hS
    | some nexts =>
    have hM : memNexts (declWidth m) m.body s.mems envF' = some s.mems :=
      Tools.ConeFold.memNexts_memFree _ m.body hmf s.mems envF'
    simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    have hXp := List.mem_map.mp hx
    obtain ⟨px, hpx, hpxn⟩ := hXp
    have hflt := (List.mem_filter.mp hpx).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hflt
    have hxd : x ∉ drivesOf m.body := by
      rw [← hpxn]; simpa [List.contains_eq_mem] using hflt.1.2
    have hxi : x ∉ m.inputs.map (·.name) := by
      rw [← hpxn]; simpa [List.contains_eq_mem] using hflt.2
    cases j with
    | zero =>
      show envF' x < _
      by_cases hO : x ∈ bodyInstOuts children m.body
      · obtain ⟨mn, iname, conns, child, cwe, hmem, hc, hw⟩ := bodyInstOuts_mem hO
        unfold instOutWires at hw
        obtain ⟨p, hp, hpw⟩ := List.mem_filterMap.mp hw
        have hl : conns.lookup p.name = some (.ref x) := by
          revert hpw
          cases conns.lookup p.name with
          | none => intro h; cases h
          | some e => cases e <;> intro h <;> cases h <;> rfl
        rw [instOutWidthsOk_at hIW hmem hc p hp x hl]
        exact hB 0 hj mn iname conns hmem child cwe hc p hp x hl
      · rw [linked_frameKG KS (declWidth m) children s.kids s.mems x m.body _ envF' s.kids kids'
          hwf hK (fun hl => hxd (linkedWrites_drives _ hl hO))]
        simp only [seedIn, List.contains_eq_mem, hxi, decide_false, Bool.false_eq_true, if_false]
        exact hst x hx hO
    | succ j =>
      have := fitX_of_runR KS children m ins hwf hIW k
        ⟨applyNexts s.st nexts, s.mems, kids'⟩ rest hR
        (fun j' hj' mn iname conns hmem child cwe hc p hp y hl => by
          have h1 := hB (j' + 1) (by simp only [List.length_cons]; omega)
            mn iname conns hmem child cwe hc p hp y hl
          simpa using h1)
        (fun y hy hyO => by
          show applyNexts s.st nexts y < _
          have hyp := List.mem_map.mp hy
          obtain ⟨py, hpy, hpyn⟩ := hyp
          have hf := (List.mem_filter.mp hpy).2
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
          have hyd : y ∉ drivesOf m.body := by
            rw [← hpyn]; simpa [List.contains_eq_mem] using hf.1.2
          rw [applyNexts_out (fun p hp he => hyd (by
            rw [← he]; exact regNexts_names _ s.mems m.body envF' nexts hmf hN p hp))]
          exact hst y hy hyO) j (by simpa using hj) x hx
      simpa using this

/-- **c4**: the encoded value of the binder at `pos` fits its kind's hardware width. -/
theorem posEnc_lt (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (pos : Nat)
    (κ : Sparkle.Compiler.Elab.MixedGateBinder) :
    Tools.ShippingMachineEntry.posEnc bools bits pos κ <
      2 ^ (Tools.ShippingMachineEntry.kindTy κ).bitWidth := by
  cases κ with
  | domain => exact Nat.two_pow_pos _
  | bool => exact Tools.ShippingMuxLoweringSoundness.encodeBool_lt (bools pos)
  | bits n => exact (bits pos n).isLt

end Tools.ShippingGen2Fit
