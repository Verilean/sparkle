import Tools.ShippingHierTyped
import Tools.ShippingHierSVRun

/-! # The emitted Verilog of a module with combinational children

`linked_sv_run` takes a stateful linked run (`runModuleTG KS`) for any child
step `KS`. A combinational child is the step `combKS`: the child's
assignments on the connection-fed environment, no state. A combinational
linked run (`runModuleH`) whose children compute from their input ports
(`kidsLocal`) is a `runModuleTG combKS` run with the same environments
(`runModuleTG_of_H`): `runModuleH` feeds the child every connection, the
stateful step only the input ones, and a local child's outputs do not see
the difference. The oracle seeding's bound comes from the width-typed run
(`fitX_of_typed`), so the shipped module's EMITTED VERILOG runs as its
linked run (`linked_sv_of_runH`). -/
namespace Tools.ShippingHierSVRunH
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf writesOf stmtWrites)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierState
open Tools.ShippingHierStateG Tools.ShippingMachineLinked Tools.ShippingHierOptRunH
open Tools.ShippingSeqOptSoundness (seedIn)

/-- A combinational child's step: its assignments on the connection-fed
environment (it has no memory, so no memory state is read). -/
def combKS : KStep Unit := fun child cwe cin env _ =>
  (evalAssigns cwe (fun _ _ => 0) child.body (connEnv cin env)).map fun r => (r, ())

theorem connEnv_local {cin : List (String × Expr)} {env env' : Env}
    (h : ∀ c ∈ cin, ∀ w, c.2 = .ref w → env w = env' w) :
    connEnv cin env = connEnv cin env' := by
  funext n
  unfold connEnv
  cases hl : cin.lookup n with
  | none => rfl
  | some e =>
    cases e with
    | ref w => exact h _ (Tools.ShippingHierSVRun.lookup_mem hl) w rfl
    | _ => rfl

theorem combKS_local : KSLocal combKS := by
  intro child cwe cin env env' s h
  simp only [combKS, connEnv_local h]

/-- A memory-free fold reads no memory. -/
theorem evalAssigns_mems (we : WEnv) (mems mems' : MEnv) :
    ∀ (body : List Stmt) (env : Env), Tools.ConeFold.memFree body →
      evalAssigns we mems body env = evalAssigns we mems' body env
  | [], _, _ => rfl
  | st :: rest, env, hm => by
    have hm' : Tools.ConeFold.memFree rest := by
      cases st <;> simp_all [Tools.ConeFold.memFree]
    cases st with
    | assign l r =>
      simp only [evalAssigns]
      cases evalExpr we env r with
      | none => rfl
      | some v =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        exact evalAssigns_mems we mems mems' rest _ hm'
    | register => exact evalAssigns_mems we mems mems' rest env hm'
    | inst => exact evalAssigns_mems we mems mems' rest env hm'
    | memory => simp [Tools.ConeFold.memFree] at hm

theorem bindOuts_congr (conns : List (String × Expr)) (c1 c2 : Env) :
    ∀ (outs : List Port) (env : Env), (∀ p ∈ outs, c1 p.name = c2 p.name) →
      bindOuts outs conns c1 env = bindOuts outs conns c2 env
  | [], _, _ => rfl
  | p :: outs, env, h => by
    show bindOuts outs conns c1
      (match conns.lookup p.name with
       | some (.ref w) => fun n => if n = w then c1 p.name else env n
       | _ => env) =
      bindOuts outs conns c2
      (match conns.lookup p.name with
       | some (.ref w) => fun n => if n = w then c2 p.name else env n
       | _ => env)
    rw [h p List.mem_cons_self]
    exact bindOuts_congr conns c1 c2 outs _ (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem lookup_inConns {outs : List Port} {n : String} (hn : n ∉ outs.map (·.name)) :
    ∀ (conns : List (String × Expr)), (inConns outs conns).lookup n = conns.lookup n
  | [] => rfl
  | (a, e) :: rest => by
    unfold inConns
    simp only [List.filter_cons]
    by_cases ha : (outs.map (·.name)).contains a = true
    · have hne : (n == a) = false := by
        simp only [beq_eq_false_iff_ne]
        intro h; subst h; exact hn (by simpa [List.contains_eq_mem] using ha)
      simp only [ha, Bool.not_true, Bool.false_eq_true, if_false, List.lookup, hne]
      exact lookup_inConns hn rest
    · simp only [Bool.not_eq_true] at ha
      simp only [ha, Bool.not_false, if_true, List.lookup]
      split
      · rfl
      · exact lookup_inConns hn rest

/-- **The linked fold with combinational local children is the stateful
fold with `combKS`.** -/
theorem evalAssignsKG_of_H (W : WEnv) (ms : List Module) (mems : MEnv) (kids : String → Unit) :
    ∀ (body : List Stmt) (env envF : Env) (acc : String → Unit),
      Tools.ConeFold.memFree body → kidsLocal ms body = true →
      evalAssignsH W (childMap ms) mems body env = some envF →
      ∃ acc', evalAssignsKG combKS W (childMap ms) kids mems body env acc = some (envF, acc')
  | [], env, envF, acc, _, _, h => by
    simp only [evalAssignsH, Option.some.injEq] at h
    subst h; exact ⟨acc, rfl⟩
  | st :: rest, env, envF, acc, hm, hloc, h => by
    have hm' : Tools.ConeFold.memFree rest := by
      cases st <;> simp_all [Tools.ConeFold.memFree]
    simp only [kidsLocal, List.all_cons, Bool.and_eq_true] at hloc
    obtain ⟨hst, hrest⟩ := hloc
    have hrest' : kidsLocal ms rest = true := hrest
    cases st with
    | assign l r =>
      simp only [evalAssignsH] at h
      cases hv : evalExpr W env r with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        simp only [evalAssignsKG, hv, Option.bind_eq_bind, Option.bind_some]
        exact evalAssignsKG_of_H W ms mems kids rest _ envF acc hm' hrest' h
    | register => exact evalAssignsKG_of_H W ms mems kids rest env envF acc hm' hrest' h
    | memory => simp [Tools.ConeFold.memFree] at hm
    | inst mn iname conns =>
      cases hc : Sparkle.IR.Machine.moduleByName ms mn with
      | none => simp [hc] at hst
      | some c =>
        simp only [hc, Bool.and_eq_true] at hst
        obtain ⟨⟨⟨hnm, hcl⟩, hw⟩, hio⟩ := hst
        have hC : childMap ms mn = some (c, declWidth c) := by simp [childMap, hc]
        simp only [evalAssignsH, hC, Option.bind_eq_bind, Option.bind_some] at h
        cases hE : evalAssigns (declWidth c) mems c.body (connEnv conns env) with
        | none => simp [hE] at h
        | some cres =>
          simp only [hE, Option.bind_some] at h
          have hmf := Tools.ShippingMachineShipsHier.memFree_of_noMem hnm
          have hagree : ∀ n ∈ c.inputs.map (·.name),
              connEnv conns env n = connEnv (inConns c.outputs conns) env n := by
            intro n hn
            have hno : n ∉ c.outputs.map (·.name) := by
              intro hmo
              obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmo
              have := List.all_eq_true.mp hio p hp
              simp [List.contains_eq_mem, hn] at this
            simp only [connEnv, lookup_inConns hno conns]
          obtain ⟨r2, hr2, hagr⟩ := evalAssigns_local _ mems c.body _ _ _ cres hmf hcl hagree hE
          have hr2' : evalAssigns (declWidth c) (fun _ _ => 0) c.body
              (connEnv (inConns c.outputs conns) env) = some r2 := by
            rw [← evalAssigns_mems _ mems _ c.body _ hmf]; exact hr2
          have hbo : bindOuts c.outputs conns r2 env = bindOuts c.outputs conns cres env :=
            bindOuts_congr conns r2 cres c.outputs env (fun p hp => hagr p.name
              (List.mem_append_right _ (by
                have := List.all_eq_true.mp hw p hp
                simpa [List.contains_eq_mem] using this)))
          simp only [evalAssignsKG, hC, combKS, hr2', Option.map_some, Option.bind_eq_bind,
            Option.bind_some, hbo]
          exact evalAssignsKG_of_H W ms mems kids rest _ envF _ hm' hrest' h

/-- **A combinational linked run with local children is a stateful linked
run with `combKS`**, from any children's (trivial) states. -/
theorem runModuleTG_of_H (W : WEnv) (ms : List Module) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env)
    (hm : Tools.ConeFold.memFree body) (hloc : kidsLocal ms body = true) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv) (kids : String → Unit) (envs : List Env),
      runModuleH W (childMap ms) body seed T st mems = some envs →
      runModuleTG combKS W (childMap ms) body seed T ⟨st, mems, kids⟩ = some envs
  | 0, _, _, _, envs, h => by
    simp only [runModuleH, Option.some.injEq] at h; subst h; rfl
  | k + 1, st, mems, kids, envs, h => by
    simp only [runModuleH] at h
    cases hS : stepModuleH W (childMap ms) body (seed k st) mems with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, nexts, mems', hF, hN, hM, rfl⟩ := stepModuleH_some hS
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleH W (childMap ms) body seed k (applyNexts st nexts) mems' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    obtain ⟨kids', hK⟩ := evalAssignsKG_of_H W ms mems kids body _ envF kids hm hloc hF
    simp only [runModuleTG, stepModuleTG, hK, hN, hM, Option.bind_eq_bind, Option.bind_some]
    rw [runModuleTG_of_H W ms body seed hm hloc k _ mems' kids' rest hR]
    rfl

/-- **The shipped module's emitted Verilog, children combinational.** A
combinational linked run of a width-typed module with local children is the
run of its emitted Verilog from the oracle seeding (the instance outputs at
each cycle the values its children drove), under the emitted-Verilog check
and width agreement of the module, from inputs and a state that fit. -/
theorem linked_sv_of_runH (ms : List Module) {o : Module} {wof : String → Option Nat}
    (hty : Tools.ShippingHierTyped.hierTyped (childMap ms) o = true)
    (hloc : kidsLocal ms o.body = true)
    (hwf : linkedWF (childMap ms) o.body = true)
    (hOut : ∀ w ∈ bodyInstOuts (childMap ms) o.body, w ∈ (Sparkle.IR.HierCheck.openIns o).map (·.name))
    (hOW : ∀ w ∈ bodyInstOuts (childMap ms) o.body, declWidth o w ≤ Tools.SVParser.EmitSem.weOf wof w)
    (hok : o.body.all Tools.ShippingHierSVSoundness.seqStmtOkI = true)
    (hsv : Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwag : ∀ n ∈ Tools.ShippingSeqSVSoundness.seqNames o.body,
      declWidth o n = Tools.SVParser.EmitSem.weOf wof n)
    (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ o.inputs.map (·.name) → ins t x < 2 ^ declWidth o x)
    (hinsW : ∀ t x, x ∈ o.inputs.map (·.name) → ins t x < 2 ^ Tools.SVParser.EmitSem.weOf wof x)
    {T : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env}
    (hrun : runModuleH (declWidth o) (childMap ms) o.body (seedIn o ins) T st mems = some envs)
    (hstD : Tools.ShippingHierTyped.BoundOff (declWidth o) (o.outputs.map (·.name)) st)
    (hst : Bounded (Tools.SVParser.EmitSem.weOf wof) st) :
    ∃ pairs regs mprog,
      Tools.SVParser.EmitSem.emitAssigns wof o.body = some pairs ∧
      Tools.SVParser.EmitSem.emitRegs wof o.body = some regs ∧
      Tools.SVParser.EmitSem.emitMemWrites wof o.body = some mprog ∧
      Tools.SVParser.EmitSem.runModuleSV wof pairs regs mprog
        (Tools.ShippingHierSVRun.oracle (childMap ms) o.body
          (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) (seedIn o ins)) T st mems = some envs := by
  have hfit := Tools.ShippingHierTyped.fitX_of_typed ms o ins hty hinsFit hrun hstD
  have hmf := Tools.ShippingHierOptRun.memFree_of_linkedWF _ hwf
  have hrunT := runModuleTG_of_H (declWidth o) ms o.body (seedIn o ins) hmf hloc T st mems
    (fun _ => ()) envs hrun
  apply Tools.ShippingHierSVRun.linked_sv_run combKS (childMap ms) hwf hok hsv hwag hrunT _ hst
  intro k st' hb n
  simp only [Tools.ShippingHierSVRun.oracle, seedOuts]
  split
  · rename_i hO
    have hO' : n ∈ bodyInstOuts (childMap ms) o.body := by simpa [List.contains_eq_mem] using hO
    cases hj : envs[T - 1 - k]? with
    | none => simp only [Option.getD_none]; exact Nat.two_pow_pos _
    | some e =>
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
      simp only [Option.getD_some]
      exact Nat.lt_of_lt_of_le (hfit _ hlt n (hOut n hO'))
        (Nat.pow_le_pow_right (by omega) (hOW n hO'))
  · exact Tools.ShippingSeqSVSoundness.seedIn_bounded hinsW k st' hb n

end Tools.ShippingHierSVRunH
