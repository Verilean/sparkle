import Tools.ShippingMachineShipsDepth
import Tools.ShippingSrm21Lift
import Tools.ShippingMachineInst
set_option autoImplicit false

/-! # M2-a C1-C3: the memory-kid bound at every height (scripts/gen2/MEMPARENT_FREEZE.md rev1 §1, approved 121c09fe)

* `memInvN n`: the read latch of a MEMORY child (guarded by "the child is a built memory module") is within its port
  width, at height `n`.
* `memKSn_boundedIn`: under `kidsMem`, every child step at `KSn n` keeps it and bounds the outputs. Height 0 is
  `memKS_boundedIn`; height `n+1` reduces to the flat step because a memory module has no instances
  (`stepModuleTG_instFree`).
* `resetNk_memInvN`: `ResetNk n` implies it (`ResetN`'s third conjunct: the read latch is 0).
* `memModule_instFree`, `kidsMem_child`: named helpers. -/
namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth Tools.ShippingSrm21Lift
open Tools.ShippingMachineDepthRun (childMap_some)
open Sparkle.Compiler.MachMemory (memModule memParams?)

/-- C1: the memory-kid invariant at height `n` (guarded, so that it holds of every non-memory module). -/
def memInvN (n : Nat) (c : Module) (s : KT n) : Prop :=
  (∃ (cb : Bool) (aw dw : Nat), c = (memModule cb aw dw).1) → memInv c ⟨stOf n s, memsOf n s⟩

/-- A built memory module has no instances. -/
theorem memModule_instFree (cb : Bool) (aw dw : Nat) : instFree (memModule cb aw dw).1.body := by
  intro st hst
  simp only [memModule, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl <;> rfl

/-- `kidsMem`: the child of an instance is a built memory module. -/
theorem kidsMem_child {children : String → Option (Module × WEnv)} {body : List Stmt}
    (hok : kidsMem children body = true) {mn iname : String} {conns : List (String × Expr)}
    (hmem : Stmt.inst mn iname conns ∈ body) {child : Module} {cwe : WEnv}
    (hc : children mn = some (child, cwe)) : ∃ (cb : Bool) (aw dw : Nat), child = (memModule cb aw dw).1 := by
  have h1 := List.all_eq_true.mp hok _ hmem
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
  obtain ⟨-, h1⟩ := h1
  rw [hc] at h1
  simp only at h1
  cases hp : memParams? child with
  | none => rw [hp] at h1; cases h1
  | some prm =>
    obtain ⟨cb, aw, dw⟩ := prm
    rw [hp] at h1
    exact ⟨cb, aw, dw, of_decide_eq_true h1⟩

/-- **C2**: the memory-kid bound at every height. -/
theorem memKSn_boundedIn (ms : List Module) (body : List Stmt) (hok : kidsMem (childMap ms) body = true) :
    ∀ n, KSBoundedIn (childMap ms) (KSn (childMap ms) n) body (memInvN n) := by
  intro n mn iname conns hmem child cwe hc env s cres s' hinv hk
  obtain ⟨cb, aw, dw, hch⟩ := kidsMem_child hok hmem hc
  have hflat := memKS_boundedIn (childMap ms) body hok mn iname conns hmem child cwe hc env
  cases n with
  | zero =>
    have h := hflat s cres s' (hinv ⟨cb, aw, dw, hch⟩) hk
    exact ⟨h.1, by unfold memInvN; intro _; exact h.2⟩
  | succ n =>
    have hf : instFree child.body := hch ▸ memModule_instFree cb aw dw
    have hk' := hk
    simp only [KSn, succKS] at hk'
    rw [stepModuleTG_instFree _ _ _ _ hf] at hk'
    cases hst : stepModule cwe child.body
        (Tools.ShippingHierarchySoundness.connEnvS (inConns child.outputs conns) env s.st) s.mems with
    | none => rw [hst] at hk'; simp at hk'
    | some r =>
      rw [hst] at hk'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk'
      obtain ⟨rfl, rfl⟩ := hk'
      have hkf : flatKS child cwe (inConns child.outputs conns) env ⟨s.st, s.mems⟩ =
          some (r.1, ⟨applyNexts s.st r.2.1, r.2.2⟩) := by
        simp only [flatKS, hst, Option.map_some]
      have h := hflat ⟨s.st, s.mems⟩ _ _ (hinv ⟨cb, aw, dw, hch⟩) hkf
      exact ⟨h.1, by unfold memInvN; intro _; exact h.2⟩

/-- **C3**: the reset state satisfies the memory-kid invariant at every height. -/
theorem resetNk_memInvN (n : Nat) : ResetImpliesInv (ResetNk n) (memInvN n) := by
  intro m D kids hR mn iname conns hmem child cwe hc
  unfold memInvN
  intro hg
  obtain ⟨cb, aw, dw, hch⟩ := hg
  obtain ⟨x, hx, hr⟩ := childMap_some.mp hc
  have hcx : child = x := (Prod.mk.inj hr).1
  subst hcx
  have hn : child.name = mn := Tools.ShippingMachineInst.moduleByName_name hx
  have hRN := hR iname child ⟨conns, by rw [hn]; exact hmem⟩ (by rw [hn]; exact hx)
  have h3 := hRN.2.2.1
  subst hch
  have h0 := h3 "mem" aw dw "clk" (.ref "wa") (.ref "wd") (.ref "we") (.ref "ra") "out_rdata" cb [] []
    (by simp [memModule])
  unfold memInv
  intro p _
  show stOf n (kids iname) "out_rdata" < 2 ^ p.ty.bitWidth
  rw [h0]; exact Nat.two_pow_pos _

end Tools.ShippingGen2
