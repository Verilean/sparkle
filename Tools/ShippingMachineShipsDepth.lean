import Tools.ShippingMachineDepthRun
import Tools.ShippingHierSVRun

/-! # Children at depth keep their outputs within their widths

`machine_ships_hier` needs the children's steps to keep their output ports
within their declared widths. For one-level children that is
`flatKS_boundedIn`; here for the depth-`n` step `KSn`: a child whose every
output port is assigned once by a self-masked expression (and drives no
instance connection) keeps it within the port's width, whatever its own
children do — the port's final value is that expression's value. -/
namespace Tools.ShippingMachineShipsDepth
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierStateG
open Tools.ShippingHierState Tools.ShippingHierOptRun Tools.ShippingMachineShipsHier
open Sparkle.IR.Reorder (writesOf stmtWrites)

/-- No instance connection of `body` reads or drives `l`. -/
def NoConnRef (l : String) (body : List Stmt) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ c ∈ conns, c.2 ≠ .ref l

theorem NoConnRef.tail {l : String} {st : Stmt} {rest : List Stmt} (h : NoConnRef l (st :: rest)) :
    NoConnRef l rest := fun mn i c hm => h mn i c (List.mem_cons_of_mem _ hm)

theorem not_instOut {outs : List Port} {conns : List (String × Expr)} {l : String}
    (h : ∀ c ∈ conns, c.2 ≠ .ref l) : l ∉ instOutWires outs conns := by
  intro hm
  unfold instOutWires at hm
  obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hm
  revert hp
  cases hl : conns.lookup p.name with
  | none => intro h; cases h
  | some e =>
    cases e with
    | ref w =>
      intro he; cases he
      exact h _ (Tools.ShippingHierSVRun.lookup_mem hl) rfl
    | _ => intro h; cases h

/-- The stateful fold leaves a name no assignment writes and no connection names. -/
theorem evalAssignsKG_frame {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv) (l : String) :
    ∀ (body : List Stmt) (env envF : Env) (acc acc' : String → σ),
      Tools.ConeFold.memFree body → l ∉ writesOf body → NoConnRef l body →
      evalAssignsKG KS we children kids mems body env acc = some (envF, acc') → envF l = env l
  | [], env, envF, acc, acc', _, _, _, h => by
    simp only [evalAssignsKG, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | st :: rest, env, envF, acc, acc', hmf, hw, hnc, h => by
    have hmf' : Tools.ConeFold.memFree rest := by
      cases st <;> simp_all [Tools.ConeFold.memFree]
    have hw' : l ∉ writesOf rest := fun hm => hw (by
      unfold writesOf at hm ⊢
      exact List.mem_flatMap.mpr (by
        obtain ⟨s, hs, hl⟩ := List.mem_flatMap.mp hm
        exact ⟨s, List.mem_cons_of_mem _ hs, hl⟩))
    cases st with
    | assign l' r =>
      simp only [evalAssignsKG] at h
      cases hv : evalExpr we env r with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        have hne : l ≠ l' := fun he => hw (by subst he; simp [writesOf, stmtWrites])
        rw [evalAssignsKG_frame KS we children kids mems l rest _ envF acc acc' hmf' hw' hnc.tail h]
        simp [hne]
    | inst mn iname conns =>
      simp only [evalAssignsKG, Option.bind_eq_bind] at h
      cases hc : children mn with
      | none => simp [hc] at h
      | some cp =>
        obtain ⟨child, cwe⟩ := cp
        simp only [hc, Option.bind_some] at h
        cases hk : KS child cwe (inConns child.outputs conns) env (kids iname) with
        | none => simp [hk] at h
        | some kr =>
          obtain ⟨cres, ks'⟩ := kr
          simp only [hk, Option.bind_some] at h
          rw [evalAssignsKG_frame KS we children kids mems l rest _ envF _ acc' hmf' hw' hnc.tail h]
          exact bindOuts_frame conns cres l child.outputs env
            (not_instOut (hnc mn iname conns List.mem_cons_self))
    | register o c rk i iv =>
      simp only [evalAssignsKG] at h
      exact evalAssignsKG_frame KS we children kids mems l rest env envF acc acc' hmf' hw' hnc.tail h
    | memory => simp [Tools.ConeFold.memFree] at hmf

/-- The final value of a name assigned once and named by no connection. -/
theorem evalAssignsKG_once {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv)
    {l : String} {r : Expr} :
    ∀ (body : List Stmt) (env envF : Env) (acc acc' : String → σ),
      evalAssignsKG KS we children kids mems body env acc = some (envF, acc') →
      Tools.ConeFold.memFree body → Stmt.assign l r ∈ body → (writesOf body).count l = 1 →
      NoConnRef l body → ∃ env v, evalExpr we env r = some v ∧ envF l = v
  | [], _, _, _, _, _, _, hm, _, _ => by cases hm
  | st :: rest, env, envF, acc, acc', h, hmf, hm, hc, hnc => by
    have hmf' : Tools.ConeFold.memFree rest := by
      cases st <;> simp_all [Tools.ConeFold.memFree]
    cases st with
    | assign l' r' =>
      simp only [evalAssignsKG] at h
      cases hv : evalExpr we env r' with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        have hcount : (writesOf (Stmt.assign l' r' :: rest)).count l =
            (if l' = l then 1 else 0) + (writesOf rest).count l := by
          simp only [writesOf, List.flatMap_cons, stmtWrites, List.count_append, List.count_singleton]
          by_cases he : l' = l <;> simp [he, beq_iff_eq]
        rw [hcount] at hc
        by_cases he : l' = l
        · subst he
          have h0 : (writesOf rest).count l' = 0 := by simp at hc; omega
          have hnot : l' ∉ writesOf rest := List.count_eq_zero.mp h0
          rcases List.mem_cons.mp hm with heq | hin
          · cases heq
            refine ⟨env, v, hv, ?_⟩
            rw [evalAssignsKG_frame KS we children kids mems l' rest _ envF acc acc' hmf' hnot hnc.tail h]
            simp
          · exfalso
            apply hnot
            unfold writesOf
            exact List.mem_flatMap.mpr ⟨_, hin, by simp [stmtWrites]⟩
        · simp only [he, if_false, Nat.zero_add] at hc
          rcases List.mem_cons.mp hm with heq | hin
          · cases heq; exact absurd rfl he
          · exact evalAssignsKG_once KS we children kids mems rest _ envF acc acc' h hmf' hin hc hnc.tail
    | inst mn iname conns =>
      simp only [evalAssignsKG, Option.bind_eq_bind] at h
      cases hcc : children mn with
      | none => simp [hcc] at h
      | some cp =>
        obtain ⟨child, cwe⟩ := cp
        simp only [hcc, Option.bind_some] at h
        cases hk : KS child cwe (inConns child.outputs conns) env (kids iname) with
        | none => simp [hk] at h
        | some kr =>
          obtain ⟨cres, ks'⟩ := kr
          simp only [hk, Option.bind_some] at h
          rcases List.mem_cons.mp hm with heq | hin
          · cases heq
          · exact evalAssignsKG_once KS we children kids mems rest _ envF _ acc' h hmf' hin
              (by simpa [writesOf, stmtWrites] using hc) hnc.tail
    | register o c rk i iv =>
      simp only [evalAssignsKG] at h
      rcases List.mem_cons.mp hm with heq | hin
      · cases heq
      · exact evalAssignsKG_once KS we children kids mems rest env envF acc acc' h hmf' hin
          (by simpa [writesOf, stmtWrites] using hc) hnc.tail
    | memory => simp [Tools.ConeFold.memFree] at hmf

/-- Decidable: every output port of `c` is assigned once by a self-masked
expression no wider than the port, named by no connection; no memory. -/
def outsMaskedN (c : Module) : Bool :=
  noMem c.body && c.outputs.all fun p =>
    outMasked (Sparkle.IR.RegDedup.declWidth c) c.body p &&
      c.body.all fun st => match st with
        | .inst _ _ conns => conns.all fun cn => decide (cn.2 ≠ .ref p.name)
        | _ => true

/-- Decidable: every instance of `body` has a child with masked outputs. -/
def kidsMaskedN (ms : List Module) (body : List Stmt) : Bool :=
  body.all fun st => match st with
    | .inst mn _ _ => match Sparkle.IR.Machine.moduleByName ms mn with
      | some child => outsMaskedN child
      | none => false
    | _ => true

/-- **Children with masked outputs keep them within their widths, at every depth.** -/
theorem KSn_boundedIn (ms : List Module) (body : List Stmt) (hok : kidsMaskedN ms body = true) :
    ∀ n, KSBoundedIn (Tools.ShippingMachineLinked.childMap ms)
      (KSn (Tools.ShippingMachineLinked.childMap ms) n) body (fun _ _ => True) := by
  intro n mn iname conns hmem child cwe hc env s cres s' _ hk
  refine ⟨?_, True.intro⟩
  intro p hp
  obtain ⟨x, hx, hxe⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hc
  injection hxe with hx1 hcwe
  subst hx1
  subst hcwe
  have h1 := List.all_eq_true.mp hok _ hmem
  simp only [hx] at h1
  simp only [outsMaskedN, Bool.and_eq_true] at h1
  obtain ⟨hnm, hout⟩ := h1
  have hpm := List.all_eq_true.mp hout p hp
  simp only [Bool.and_eq_true] at hpm
  obtain ⟨hmask, hconn⟩ := hpm
  simp only [outMasked, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hmask
  obtain ⟨hcount, st, hst', hm⟩ := hmask
  have hnc : NoConnRef p.name child.body := by
    intro mn' i' cs hmi c hcin he
    have := List.all_eq_true.mp hconn _ hmi
    simp only [List.all_eq_true] at this
    have := this c hcin
    simp [he] at this
  have hmf := memFree_of_noMem hnm
  cases st with
  | assign l r =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
    obtain ⟨⟨hl, hsm⟩, hw⟩ := hm
    subst hl
    have hbound : ∀ envF : Env, (∃ env' v, evalExpr (Sparkle.IR.RegDedup.declWidth child) env' r = some v ∧
        envF p.name = v) → envF p.name < 2 ^ p.ty.bitWidth := by
      intro envF ⟨env', v, hv, hfin⟩
      rw [hfin]
      exact Nat.lt_of_lt_of_le (selfMasked_lt hsm hv) (Nat.pow_le_pow_right (by omega) hw)
    cases n with
    | zero =>
      simp only [KSn, flatKS] at hk
      cases hst : stepModule (Sparkle.IR.RegDedup.declWidth child) child.body
          (connEnvS (inConns child.outputs conns) env s.st) s.mems with
      | none => rw [hst] at hk; cases hk
      | some r0 =>
        obtain ⟨envF, nexts, mems', hF, -, -, rfl⟩ := stepModule_some hst
        rw [hst] at hk
        simp only [Option.map_some] at hk
        rw [← (Prod.mk.inj (Option.some.inj hk)).1]
        exact hbound envF (evalAssigns_once _ s.mems child.body _ envF hF hmf hst' hcount)
    | succ k =>
      simp only [KSn, succKS, stepModuleTG] at hk
      cases hK : evalAssignsKG (KSn (Tools.ShippingMachineLinked.childMap ms) k)
          (Sparkle.IR.RegDedup.declWidth child) (Tools.ShippingMachineLinked.childMap ms) s.kids s.mems
          child.body (connEnvS (inConns child.outputs conns) env s.st) s.kids with
      | none => rw [hK] at hk; simp at hk
      | some ek =>
        obtain ⟨envF, kids'⟩ := ek
        rw [hK] at hk
        simp only [Option.bind_eq_bind, Option.bind_some] at hk
        cases hN : regNexts (Sparkle.IR.RegDedup.declWidth child) s.mems child.body envF with
        | none => rw [hN] at hk; simp at hk
        | some nexts =>
          rw [hN] at hk
          simp only [Option.bind_some] at hk
          cases hM : memNexts (Sparkle.IR.RegDedup.declWidth child) child.body s.mems envF with
          | none => rw [hM] at hk; simp at hk
          | some mems' =>
            rw [hM] at hk
            simp only [Option.bind_some] at hk
            rw [← (Prod.mk.inj (Option.some.inj hk)).1]
            exact hbound envF (evalAssignsKG_once _ _ _ s.kids s.mems child.body _ envF s.kids kids' hK
              hmf hst' hcount hnc)
  | _ => simp at hm

/-- The children's reset at depth `n`: every instance's child at its reset state. -/
def ResetNk (n : Nat) (m : Module) (D : Design) (kids : String → KT n) : Prop :=
  ∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
    Sparkle.IR.Machine.moduleByName D.modules mc.name = some mc →
    Tools.ShippingMachineDepth.ResetN D n mc (kids iname)

/-- The composed theorem at depth `n` in the general form (its wiring dropped). -/
theorem composedG_of_NW {n : Nat} {declName : Name} {d : Tools.ShippingMachineAuto.MachineData}
    {kD : Nat} {m : Module} {dsn : Design} {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {src : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → Nat →
      Sparkle.Core.Signal.Signal (dom i) Bool}
    (h : Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext extB) :
    ComposedG (fun D => KSn (Tools.ShippingMachineLinked.childMap D.modules) n) (ResetNk n)
      declName d kD m dsn dom src ext extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, _, _, _, H⟩ := h
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, fun i bools bits T seed st0 mems kids a b c e f g =>
    H i bools bits T seed st0 mems kids a b c e f g⟩

end Tools.ShippingMachineShipsDepth
