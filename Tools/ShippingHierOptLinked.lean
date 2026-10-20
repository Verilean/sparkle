import Tools.ShippingHierStateG
import Tools.ShippingHierOptSoundness

/-! # The stateful linked run as an open run

`linked_open` reads a combinational linked evaluation as the open-module
evaluation from the oracle seeding (instance-output wires at their final
values). The same holds for one cycle of the STATEFUL linked semantics
(`evalAssignsKG`: each instance steps its child by `KS`): the instance
statements only bind their outputs (`bindOuts`), whatever the child's step,
so the cycle's final environment is the open fold's from the oracle
seeding. This is the direction the optimizer check on instance-bearing
modules needs: from the linked run of the module the compiler built to the
open run the extracted-interface check speaks about. -/
namespace Tools.ShippingHierOptLinked
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf evalExpr_congr)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierStateG
open Tools.ShippingHierState

/-- A cycle of the stateful linked fold writes only assignment targets and
instance outputs. -/
theorem linked_frameKG {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv)
    (n : String) :
    ∀ (body : List Stmt) (env envF : Env) (acc acc' : String → σ),
      linkedWF children body = true →
      evalAssignsKG KS we children kids mems body env acc = some (envF, acc') →
      n ∉ linkedWrites children body → envF n = env n
  | [], env, envF, acc, acc', _, h, _ => by
    simp only [evalAssignsKG, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | .assign l r :: rest, env, envF, acc, acc', hwf, h, hn => by
    have hrest : linkedWF children rest = true := by
      have : (!(bodyInstOuts children rest).contains l &&
          (refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
          linkedWF children rest) = true := hwf
      simp only [Bool.and_eq_true] at this
      exact this.2
    simp only [evalAssignsKG] at h
    cases hv : evalExpr we env r with
    | none => simp [hv] at h
    | some v =>
      simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
      have hsplit : n ≠ l ∧ n ∉ linkedWrites children rest :=
        ⟨fun eq => hn (eq ▸ List.mem_cons_self), fun hm => hn (List.mem_cons_of_mem _ hm)⟩
      rw [linked_frameKG KS we children kids mems n rest _ envF acc acc' hrest h hsplit.2]
      simp [hsplit.1]
  | .inst mn iname conns :: rest, env, envF, acc, acc', hwf, h, hn => by
    cases hc : children mn with
    | none => simp [linkedWF, hc] at hwf
    | some cp =>
      obtain ⟨child, cwe⟩ := cp
      have hrest : linkedWF children rest = true := by
        have : linkedWF children (.inst mn iname conns :: rest) = true := hwf
        simp only [linkedWF, hc, Bool.and_eq_true] at this
        exact this.2
      simp only [evalAssignsKG, hc, Option.bind_eq_bind, Option.bind_some] at h
      cases hk : KS child cwe (inConns child.outputs conns) env (kids iname) with
      | none => simp [hk] at h
      | some kr =>
        obtain ⟨cres, ks'⟩ := kr
        simp only [hk, Option.bind_some] at h
        have hn' : n ∉ instOutWires child.outputs conns ++ linkedWrites children rest := by
          have : linkedWrites children (.inst mn iname conns :: rest) =
              instOutWires child.outputs conns ++ linkedWrites children rest := by
            show stmtInstOuts children (.inst mn iname conns) ++ _ = _
            simp [stmtInstOuts, hc]
          rw [this] at hn
          exact hn
        rw [linked_frameKG KS we children kids mems n rest _ envF _ acc' hrest h
          (fun hm => hn' (List.mem_append_right _ hm))]
        exact bindOuts_frame conns cres n child.outputs env
          (fun hm => hn' (List.mem_append_left _ hm))
  | .register o c rk i iv :: rest, env, envF, acc, acc', hwf, h, hn => by
    simp only [evalAssignsKG] at h
    exact linked_frameKG KS we children kids mems n rest env envF acc acc' hwf h hn
  | .memory .. :: _, _, _, _, _, hwf, _, _ => by simp [linkedWF] at hwf

/-- **A cycle of the stateful linked run is the open fold from the oracle
seeding.** -/
theorem linked_openKG {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv) :
    ∀ (body : List Stmt) (env envF : Env) (acc acc' : String → σ),
      linkedWF children body = true →
      evalAssignsKG KS we children kids mems body env acc = some (envF, acc') →
      evalAssigns we mems body (seedOuts children body envF env) = some envF
  | [], env, envF, acc, acc', _, h => by
    simp only [evalAssignsKG, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    have : seedOuts children [] env env = env := by
      funext n; simp [seedOuts, bodyInstOuts]
    rw [this]
    rfl
  | .assign l r :: rest, env, envF, acc, acc', hwf, h => by
    have hwf' : (!(bodyInstOuts children rest).contains l &&
        (refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
        linkedWF children rest) = true := hwf
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hwf'
    obtain ⟨⟨hl, hrefs⟩, hrest⟩ := hwf'
    simp only [evalAssignsKG] at h
    cases hv : evalExpr we env r with
    | none => simp [hv] at h
    | some v =>
      simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
      have ih := linked_openKG KS we children kids mems rest _ envF acc acc' hrest h
      have hseed : seedOuts children (.assign l r :: rest) envF env =
          seedOuts children rest envF env := rfl
      rw [hseed]
      have hexpr : evalExpr we (seedOuts children rest envF env) r = some v := by
        rw [← hv]
        apply evalExpr_congr
        intro n hn
        show (if (bodyInstOuts children rest).contains n then envF n else env n) = env n
        rw [hrefs n hn]
        rfl
      show ((evalExpr we (seedOuts children rest envF env) r).bind fun v =>
        evalAssigns we mems rest
          (fun m => if m = l then v else seedOuts children rest envF env m)) = some envF
      rw [hexpr]
      have hfun : (fun m => if m = l then v else seedOuts children rest envF env m) =
          seedOuts children rest envF (fun m => if m = l then v else env m) := by
        funext m
        show (if m = l then v else
            (if (bodyInstOuts children rest).contains m then envF m else env m)) =
          (if (bodyInstOuts children rest).contains m then envF m
            else (if m = l then v else env m))
        by_cases hm : m = l
        · rw [hm, hl]
          simp
        · simp [hm]
      simp only [Option.bind_some]
      rw [hfun]
      exact ih
  | .inst mn iname conns :: rest, env, envF, acc, acc', hwf, h => by
    cases hc : children mn with
    | none => simp [linkedWF, hc] at hwf
    | some cp =>
      obtain ⟨child, cwe⟩ := cp
      have hwf' : ((instOutWires child.outputs conns).all
            (fun w => !(linkedWrites children rest).contains w) &&
          decide (instOutWires child.outputs conns).Nodup &&
          conns.all (fun c =>
            match c.2 with
            | .ref w => (instOutWires child.outputs conns).contains w ||
                !(linkedWrites children rest).contains w
            | _ => true) && linkedWF children rest) = true := by
        have : linkedWF children (.inst mn iname conns :: rest) = true := hwf
        simp only [linkedWF, hc] at this
        exact this
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hwf'
      obtain ⟨⟨⟨houts, -⟩, -⟩, hrest⟩ := hwf'
      simp only [evalAssignsKG, hc, Option.bind_eq_bind, Option.bind_some] at h
      cases hk : KS child cwe (inConns child.outputs conns) env (kids iname) with
      | none => simp [hk] at h
      | some kr =>
        obtain ⟨cres, ks'⟩ := kr
        simp only [hk, Option.bind_some] at h
        have ih := linked_openKG KS we children kids mems rest _ envF _ acc' hrest h
        have houtsEq : bodyInstOuts children (.inst mn iname conns :: rest) =
            instOutWires child.outputs conns ++ bodyInstOuts children rest := by
          show stmtInstOuts children (.inst mn iname conns) ++ _ = _
          simp [stmtInstOuts, hc]
        have hfun : seedOuts children (.inst mn iname conns :: rest) envF env =
            seedOuts children rest envF (bindOuts child.outputs conns cres env) := by
          funext n
          show (if (bodyInstOuts children (.inst mn iname conns :: rest)).contains n
              then envF n else env n) =
            (if (bodyInstOuts children rest).contains n then envF n
              else bindOuts child.outputs conns cres env n)
          rw [houtsEq]
          by_cases hR : (bodyInstOuts children rest).contains n = true
          · rw [hR]
            simp [List.contains_eq_mem] at hR ⊢
            simp [hR]
          · have hR' : (bodyInstOuts children rest).contains n = false := by
              simpa using hR
            rw [hR']
            by_cases hT : n ∈ instOutWires child.outputs conns
            · have hcont : (instOutWires child.outputs conns ++
                  bodyInstOuts children rest).contains n = true := by
                simp [List.contains_eq_mem, hT]
              rw [hcont]
              have hnw : n ∉ linkedWrites children rest := by
                have := houts n hT
                simpa [List.contains_eq_mem] using this
              simp only [if_true, Bool.false_eq_true, if_false]
              exact linked_frameKG KS we children kids mems n rest _ envF _ acc' hrest h hnw
            · have hcont : (instOutWires child.outputs conns ++
                  bodyInstOuts children rest).contains n = false := by
                have hR'' : n ∉ bodyInstOuts children rest := by
                  simpa [List.contains_eq_mem] using hR'
                simp [List.contains_eq_mem, hT, hR'']
              rw [hcont]
              simp only [Bool.false_eq_true, if_false]
              exact (bindOuts_frame conns cres n child.outputs env hT).symm
        show evalAssigns we mems rest
          (seedOuts children (.inst mn iname conns :: rest) envF env) = some envF
        rw [hfun]
        exact ih
  | .register o c rk i iv :: rest, env, envF, acc, acc', hwf, h => by
    simp only [evalAssignsKG] at h
    exact linked_openKG KS we children kids mems rest env envF acc acc' hwf h
  | .memory .. :: _, _, _, _, _, hwf, _ => by simp [linkedWF] at hwf

/-- The fold sets only its own instances' next states. -/
theorem kids_frameKG {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv)
    (n : String) :
    ∀ (body : List Stmt) (env envF : Env) (acc acc' : String → σ),
      evalAssignsKG KS we children kids mems body env acc = some (envF, acc') →
      n ∉ instNames body → acc' n = acc n
  | [], env, envF, acc, acc', h, _ => by
    simp only [evalAssignsKG, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
  | .assign l r :: rest, env, envF, acc, acc', h, hn => by
    simp only [evalAssignsKG] at h
    cases hv : evalExpr we env r with
    | none => simp [hv] at h
    | some v =>
      simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
      exact kids_frameKG KS we children kids mems n rest _ envF acc acc' h hn
  | .inst mn iname conns :: rest, env, envF, acc, acc', h, hn => by
    have hn' : n ≠ iname ∧ n ∉ instNames rest :=
      ⟨fun e => hn (e ▸ List.mem_cons_self), fun hm => hn (List.mem_cons_of_mem _ hm)⟩
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
        rw [kids_frameKG KS we children kids mems n rest _ envF _ acc' h hn'.2]
        simp [hn'.1]
  | .register .. :: rest, env, envF, acc, acc', h, hn => by
    simp only [evalAssignsKG] at h
    exact kids_frameKG KS we children kids mems n rest env envF acc acc' h hn
  | .memory nm aw dw c wa wd wen ra rd cr ew er :: rest, env, envF, acc, acc', h, hn => by
    simp only [evalAssignsKG] at h
    split at h
    · cases hcm : comboReads we mems nm aw dw ((ra, rd) :: er) env with
      | none => simp [hcm] at h
      | some env' =>
        simp only [hcm, Option.bind_eq_bind, Option.bind_some] at h
        exact kids_frameKG KS we children kids mems n rest _ envF acc acc' h hn
    · exact kids_frameKG KS we children kids mems n rest env envF acc acc' h hn

/-- What a cycle of the stateful linked fold says of each instance: its
child stepped, from the instance's state, on an environment agreeing with
the final one on every wire the instance reads (other than its own
outputs), to the instance's next state, and its outputs are the final
values of the wires they drive. -/
def ConsistentKG {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    (kids : String → σ) (body : List Stmt) (envF : Env) (acc' : String → σ) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
    ∃ (child : Module) (cwe : WEnv) (envAt cres : Env),
      children mn = some (child, cwe) ∧
      KS child cwe (inConns child.outputs conns) envAt (kids iname) = some (cres, acc' iname) ∧
      (∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ instOutWires child.outputs conns →
        envAt w = envF w) ∧
      (∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
        envF w = cres p.name)

theorem linked_consistentKG {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv) :
    ∀ (body : List Stmt) (env envF : Env) (acc acc' : String → σ),
      linkedWF children body = true → (instNames body).Nodup →
      evalAssignsKG KS we children kids mems body env acc = some (envF, acc') →
      ConsistentKG KS children kids body envF acc'
  | [], _, _, _, _, _, _, _ => by
    intro mn iname conns hmem
    cases hmem
  | .assign l r :: rest, env, envF, acc, acc', hwf, hnd, h => by
    have hrest : linkedWF children rest = true := by
      have : (!(bodyInstOuts children rest).contains l &&
          (refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
          linkedWF children rest) = true := hwf
      simp only [Bool.and_eq_true] at this
      exact this.2
    simp only [evalAssignsKG] at h
    cases hv : evalExpr we env r with
    | none => simp [hv] at h
    | some v =>
      simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
      have ih := linked_consistentKG KS we children kids mems rest _ envF acc acc' hrest hnd h
      intro mn iname conns hmem
      rcases List.mem_cons.mp hmem with hbad | hmem
      · cases hbad
      · exact ih mn iname conns hmem
  | .inst mn0 iname0 conns0 :: rest, env, envF, acc, acc', hwf, hnd, h => by
    cases hc : children mn0 with
    | none => simp [linkedWF, hc] at hwf
    | some cp =>
      obtain ⟨child, cwe⟩ := cp
      have hwf' : ((instOutWires child.outputs conns0).all
            (fun w => !(linkedWrites children rest).contains w) &&
          decide (instOutWires child.outputs conns0).Nodup &&
          conns0.all (fun c =>
            match c.2 with
            | .ref w => (instOutWires child.outputs conns0).contains w ||
                !(linkedWrites children rest).contains w
            | _ => true) && linkedWF children rest) = true := by
        have : linkedWF children (.inst mn0 iname0 conns0 :: rest) = true := hwf
        simp only [linkedWF, hc] at this
        exact this
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at hwf'
      obtain ⟨⟨⟨houts, hndo⟩, hreads⟩, hrest⟩ := hwf'
      have hnd' : iname0 ∉ instNames rest ∧ (instNames rest).Nodup := by
        have : (iname0 :: instNames rest).Nodup := hnd
        exact List.nodup_cons.mp this
      have h0 := h
      simp only [evalAssignsKG, hc, Option.bind_eq_bind, Option.bind_some] at h
      cases hk : KS child cwe (inConns child.outputs conns0) env (kids iname0) with
      | none => simp [hk] at h
      | some kr =>
        obtain ⟨cres, ks'⟩ := kr
        simp only [hk, Option.bind_some] at h
        have ih := linked_consistentKG KS we children kids mems rest _ envF _ acc' hrest hnd'.2 h
        intro mn iname conns hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · cases heq
          have hacc : acc' iname0 = ks' := by
            rw [kids_frameKG KS we children kids mems iname0 rest _ envF _ acc' h hnd'.1]
            simp
          refine ⟨child, cwe, env, cres, hc, by rw [hacc]; exact hk, ?_, ?_⟩
          · intro c hcm w hw hnot
            have hc' := hreads c hcm
            rw [hw] at hc'
            have hc' : ((instOutWires child.outputs conns0).contains w ||
                !(linkedWrites children rest).contains w) = true := hc'
            have hcontF : (instOutWires child.outputs conns0).contains w = false := by
              simpa [List.contains_eq_mem] using hnot
            rw [hcontF] at hc'
            have hnwRest : w ∉ linkedWrites children rest := by
              simpa [List.contains_eq_mem] using hc'
            have hnw : w ∉ linkedWrites children (.inst mn0 iname0 conns0 :: rest) := by
              have hEq : linkedWrites children (.inst mn0 iname0 conns0 :: rest) =
                  instOutWires child.outputs conns0 ++ linkedWrites children rest := by
                show stmtInstOuts children (.inst mn0 iname0 conns0) ++ _ = _
                simp [stmtInstOuts, hc]
              rw [hEq]
              intro hm
              rcases List.mem_append.mp hm with hm | hm
              · exact hnot hm
              · exact hnwRest hm
            exact (linked_frameKG KS we children kids mems w _ env envF acc acc' hwf h0 hnw).symm
          · intro p hp w hw
            have hwOut : w ∈ instOutWires child.outputs conns0 :=
              mem_instOutWires hp hw
            have hnwRest : w ∉ linkedWrites children rest := by
              have := houts w hwOut
              simpa [List.contains_eq_mem] using this
            rw [linked_frameKG KS we children kids mems w rest _ envF _ acc' hrest h hnwRest]
            exact bindOuts_value conns0 cres child.outputs env hndo p hp w hw
        · exact ih mn iname conns hmem
  | .register o c rk i iv :: rest, env, envF, acc, acc', hwf, hnd, h => by
    simp only [evalAssignsKG] at h
    have ih := linked_consistentKG KS we children kids mems rest env envF acc acc' hwf hnd h
    intro mn iname conns hmem
    rcases List.mem_cons.mp hmem with hbad | hmem
    · cases hbad
    · exact ih mn iname conns hmem
  | .memory .. :: _, _, _, _, _, hwf, _, _ => by simp [linkedWF] at hwf

end Tools.ShippingHierOptLinked
