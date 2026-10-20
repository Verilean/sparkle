import Tools.ShippingHierarchySoundness
import Sparkle.IR.ReorderInvariance

/-! # The linked semantics as the open-module semantics plus consistency

Every layer after the core entry — the checked optimizer, the emitted
SystemVerilog semantics, the parser roundtrip — is stated in the
OPEN-MODULE view: an instance statement is a no-op and its output wires are
free inputs. This file connects that view to the linked semantics
(`evalAssignsH`, where an instance statement runs its child):

* `linked_open`: a linked run to `envF` IS the open run started from the
  environment in which the instance-output wires are pre-seeded with their
  final values;
* `linked_consistent`: those seeded values are not arbitrary — each
  instance's outputs equal its child's evaluation on an environment that
  agrees with the final one on everything the instance reads.

Together they say the linked result is THE consistent solution of the open
module, which is what lets the open-module layers speak about hierarchical
designs. The side condition `linkedWF` is a decidable well-formedness
check of the body (single assignment of instance outputs, no read of an
instance output before its instance). -/
namespace Tools.ShippingHierOpen
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf evalExpr_congr)
open Tools.ShippingHierarchySoundness

/-- The parent wires one instance drives: the references its connections
give the child's output ports. -/
def instOutWires (outs : List Port) (conns : List (String × Expr)) : List String :=
  outs.filterMap fun p =>
    match conns.lookup p.name with
    | some (.ref w) => some w
    | _ => none

/-- The wires a statement's instance (if it is one) drives. -/
def stmtInstOuts (children : String → Option (Module × WEnv)) : Stmt → List String
  | .inst mn _ conns =>
    match children mn with
    | some (child, _) => instOutWires child.outputs conns
    | none => []
  | _ => []

/-- Every instance-output wire of the body. -/
def bodyInstOuts (children : String → Option (Module × WEnv)) : List Stmt → List String
  | [] => []
  | st :: rest => stmtInstOuts children st ++ bodyInstOuts children rest

/-- The wires the linked fold writes: assignment targets and instance outputs. -/
def linkedWrites (children : String → Option (Module × WEnv)) : List Stmt → List String
  | [] => []
  | .assign l _ :: rest => l :: linkedWrites children rest
  | st :: rest => stmtInstOuts children st ++ linkedWrites children rest

/-- Decidable well-formedness of a body for the linked/open correspondence:
an assignment neither targets nor reads an instance output of a LATER
instance; an instance's output wires are pairwise distinct and never written
again; the wires an instance reads are never written afterwards. Combo-read
memories are outside the correspondence. -/
def linkedWF (children : String → Option (Module × WEnv)) : List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    !(bodyInstOuts children rest).contains l &&
      (refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
      linkedWF children rest
  | .inst mn iname conns :: rest =>
    (match children mn with
     | some (child, _) =>
       (instOutWires child.outputs conns).all
           (fun w => !(linkedWrites children rest).contains w) &&
         decide (instOutWires child.outputs conns).Nodup &&
         conns.all (fun c =>
           match c.2 with
           | .ref w => (instOutWires child.outputs conns).contains w ||
               !(linkedWrites children rest).contains w
           | _ => true)
     | none => false) && linkedWF children rest
  | .register _ _ _ _ _ :: rest => linkedWF children rest
  | .memory .. :: _ => false

theorem mem_instOutWires {outs : List Port} {conns : List (String × Expr)}
    {p : Port} {w : String} (hp : p ∈ outs)
    (hw : conns.lookup p.name = some (.ref w)) : w ∈ instOutWires outs conns := by
  unfold instOutWires
  exact List.mem_filterMap.mpr ⟨p, hp, by rw [hw]⟩

theorem instOutWires_cons (q : Port) (outs : List Port) (conns : List (String × Expr)) :
    instOutWires (q :: outs) conns =
      (match conns.lookup q.name with
       | some (.ref w) => [w]
       | _ => []) ++ instOutWires outs conns := by
  unfold instOutWires
  rw [List.filterMap_cons]
  cases hl : conns.lookup q.name with
  | none => rfl
  | some e => cases e <;> rfl

/-! ## What `bindOuts` writes -/

theorem bindOuts_frame (conns : List (String × Expr)) (cres : Env) (n : String) :
    ∀ (outs : List Port) (env : Env), n ∉ instOutWires outs conns →
      bindOuts outs conns cres env n = env n
  | [], _, _ => rfl
  | p :: outs, env, hn => by
    show bindOuts outs conns cres
      (match conns.lookup p.name with
       | some (.ref w) => fun n => if n = w then cres p.name else env n
       | _ => env) n = env n
    cases hl : conns.lookup p.name with
    | none =>
      have hn' : n ∉ instOutWires outs conns := by
        simpa [instOutWires, hl] using hn
      exact bindOuts_frame conns cres n outs env hn'
    | some e =>
      cases e with
      | ref w =>
        have hsplit : n ≠ w ∧ n ∉ instOutWires outs conns := by
          have : n ∉ w :: instOutWires outs conns := by
            simpa [instOutWires, hl] using hn
          exact ⟨fun eq => this (eq ▸ List.mem_cons_self),
            fun h => this (List.mem_cons_of_mem _ h)⟩
        rw [bindOuts_frame conns cres n outs _ hsplit.2]
        simp [hsplit.1]
      | const v w =>
        have hn' : n ∉ instOutWires outs conns := by
          simpa [instOutWires, hl] using hn
        exact bindOuts_frame conns cres n outs env hn'
      | op o args =>
        have hn' : n ∉ instOutWires outs conns := by
          simpa [instOutWires, hl] using hn
        exact bindOuts_frame conns cres n outs env hn'
      | concat args =>
        have hn' : n ∉ instOutWires outs conns := by
          simpa [instOutWires, hl] using hn
        exact bindOuts_frame conns cres n outs env hn'
      | slice e hi lo =>
        have hn' : n ∉ instOutWires outs conns := by
          simpa [instOutWires, hl] using hn
        exact bindOuts_frame conns cres n outs env hn'
      | sliceDim e hi lo =>
        have hn' : n ∉ instOutWires outs conns := by
          simpa [instOutWires, hl] using hn
        exact bindOuts_frame conns cres n outs env hn'
      | index a i =>
        have hn' : n ∉ instOutWires outs conns := by
          simpa [instOutWires, hl] using hn
        exact bindOuts_frame conns cres n outs env hn'

/-- With pairwise-distinct output wires, each connected output port's wire
carries exactly that port's value. -/
theorem bindOuts_value (conns : List (String × Expr)) (cres : Env) :
    ∀ (outs : List Port) (env : Env), (instOutWires outs conns).Nodup →
      ∀ p ∈ outs, ∀ w, conns.lookup p.name = some (.ref w) →
        bindOuts outs conns cres env w = cres p.name
  | [], _, _, p, hp, _, _ => by cases hp
  | q :: outs, env, hnd, p, hp, w, hw => by
    show bindOuts outs conns cres
      (match conns.lookup q.name with
       | some (.ref w') => fun n => if n = w' then cres q.name else env n
       | _ => env) w = cres p.name
    rcases List.mem_cons.mp hp with rfl | hp'
    · -- this port writes `w`; nothing after it does
      rw [hw]
      have hnd' : (w :: instOutWires outs conns).Nodup := by
        simpa [instOutWires, hw] using hnd
      rw [bindOuts_frame conns cres w outs _ (List.nodup_cons.mp hnd').1]
      simp
    · have hndRest : (instOutWires outs conns).Nodup := by
        refine hnd.sublist ?_
        rw [instOutWires_cons]
        exact List.sublist_append_right _ _
      exact bindOuts_value conns cres outs _ hndRest p hp' w hw

/-! ## The frame of the linked fold -/

/-- The linked fold leaves every wire it does not write untouched. -/
theorem linked_frame (we : WEnv) (children : String → Option (Module × WEnv))
    (mems : MEnv) (n : String) :
    ∀ (body : List Stmt) (env envF : Env),
      evalAssignsH we children mems body env = some envF →
      n ∉ linkedWrites children body → envF n = env n
  | [], env, envF, h, _ => by
    cases h
    rfl
  | .assign l r :: rest, env, envF, h, hn => by
    have h' : ((evalExpr we env r).bind fun v =>
        evalAssignsH we children mems rest (fun m => if m = l then v else env m)) =
        some envF := h
    cases hv : evalExpr we env r with
    | none => rw [hv] at h'; cases h'
    | some v =>
      rw [hv] at h'
      have hsplit : n ≠ l ∧ n ∉ linkedWrites children rest :=
        ⟨fun eq => hn (eq ▸ List.mem_cons_self), fun hm => hn (List.mem_cons_of_mem _ hm)⟩
      rw [linked_frame we children mems n rest _ envF h' hsplit.2]
      simp [hsplit.1]
  | .inst mn iname conns :: rest, env, envF, h, hn => by
    have h' : ((children mn).bind fun cp =>
        (evalAssigns cp.2 mems cp.1.body (connEnv conns env)).bind fun cres =>
          evalAssignsH we children mems rest
            (bindOuts cp.1.outputs conns cres env)) = some envF := h
    cases hc : children mn with
    | none => rw [hc] at h'; cases h'
    | some cp =>
      obtain ⟨child, cwe⟩ := cp
      rw [hc] at h'
      cases hr : evalAssigns cwe mems child.body (connEnv conns env) with
      | none =>
        have h'' : ((evalAssigns cwe mems child.body (connEnv conns env)).bind fun cres =>
            evalAssignsH we children mems rest
              (bindOuts child.outputs conns cres env)) = some envF := h'
        rw [hr] at h''
        cases h''
      | some cres =>
        have h'' : ((evalAssigns cwe mems child.body (connEnv conns env)).bind fun cres =>
            evalAssignsH we children mems rest
              (bindOuts child.outputs conns cres env)) = some envF := h'
        rw [hr] at h''
        have hn' : n ∉ instOutWires child.outputs conns ++ linkedWrites children rest := by
          have : linkedWrites children (.inst mn iname conns :: rest) =
              instOutWires child.outputs conns ++ linkedWrites children rest := by
            show stmtInstOuts children (.inst mn iname conns) ++ _ = _
            simp [stmtInstOuts, hc]
          rw [this] at hn
          exact hn
        rw [linked_frame we children mems n rest _ envF h''
          (fun hm => hn' (List.mem_append_right _ hm))]
        exact bindOuts_frame conns cres n child.outputs env
          (fun hm => hn' (List.mem_append_left _ hm))
  | .register o c rk i iv :: rest, env, envF, h, hn => by
    exact linked_frame we children mems n rest env envF h hn
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, env, envF, h, hn => by
    exact linked_frame we children mems n rest env envF h hn

/-! ## The bridge -/

/-- The oracle seeding: instance-output wires carry their final values,
everything else the given environment. -/
def seedOuts (children : String → Option (Module × WEnv)) (body : List Stmt)
    (envF env : Env) : Env :=
  fun n => if (bodyInstOuts children body).contains n then envF n else env n

/-- **The linked run is the open run from the oracle seeding.** -/
theorem linked_open (we : WEnv) (children : String → Option (Module × WEnv))
    (mems : MEnv) :
    ∀ (body : List Stmt) (env envF : Env), linkedWF children body = true →
      evalAssignsH we children mems body env = some envF →
      evalAssigns we mems body (seedOuts children body envF env) = some envF
  | [], env, envF, _, h => by
    cases h
    rfl
  | .assign l r :: rest, env, envF, hwf, h => by
    have hwf' : (!(bodyInstOuts children rest).contains l &&
        (refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
        linkedWF children rest) = true := hwf
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hwf'
    obtain ⟨⟨hl, hrefs⟩, hrest⟩ := hwf'
    have h' : ((evalExpr we env r).bind fun v =>
        evalAssignsH we children mems rest (fun m => if m = l then v else env m)) =
        some envF := h
    cases hv : evalExpr we env r with
    | none => rw [hv] at h'; cases h'
    | some v =>
      rw [hv] at h'
      have ih := linked_open we children mems rest _ envF hrest h'
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
      show evalAssigns we mems rest
        (fun m => if m = l then v else seedOuts children rest envF env m) = some envF
      rw [hfun]
      exact ih
  | .inst mn iname conns :: rest, env, envF, hwf, h => by
    have h' : ((children mn).bind fun cp =>
        (evalAssigns cp.2 mems cp.1.body (connEnv conns env)).bind fun cres =>
          evalAssignsH we children mems rest
            (bindOuts cp.1.outputs conns cres env)) = some envF := h
    cases hc : children mn with
    | none => rw [hc] at h'; cases h'
    | some cp =>
      obtain ⟨child, cwe⟩ := cp
      rw [hc] at h'
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
      cases hr : evalAssigns cwe mems child.body (connEnv conns env) with
      | none =>
        have h'' : ((evalAssigns cwe mems child.body (connEnv conns env)).bind fun cres =>
            evalAssignsH we children mems rest
              (bindOuts child.outputs conns cres env)) = some envF := h'
        rw [hr] at h''
        cases h''
      | some cres =>
        have h'' : ((evalAssigns cwe mems child.body (connEnv conns env)).bind fun cres =>
            evalAssignsH we children mems rest
              (bindOuts child.outputs conns cres env)) = some envF := h'
        rw [hr] at h''
        have ih := linked_open we children mems rest _ envF hrest h''
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
              exact linked_frame we children mems n rest _ envF h'' hnw
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
  | .register o c rk i iv :: rest, env, envF, hwf, h => by
    have ih := linked_open we children mems rest env envF hwf h
    exact ih
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, env, envF, hwf, _ => by
    cases hwf

/-- Each instance's outputs, in the final environment, are its child's
evaluation on an environment agreeing with the final one on every wire the
instance reads. -/
def Consistent (children : String → Option (Module × WEnv)) (mems : MEnv)
    (body : List Stmt) (envF : Env) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
    ∃ (child : Module) (cwe : WEnv) (envAt cres : Env),
      children mn = some (child, cwe) ∧
      evalAssigns cwe mems child.body (connEnv conns envAt) = some cres ∧
      (∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ instOutWires child.outputs conns →
        envAt w = envF w) ∧
      (∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
        envF w = cres p.name)

/-- **The oracle values are the children's values.** -/
theorem linked_consistent (we : WEnv) (children : String → Option (Module × WEnv))
    (mems : MEnv) :
    ∀ (body : List Stmt) (env envF : Env), linkedWF children body = true →
      evalAssignsH we children mems body env = some envF →
      Consistent children mems body envF
  | [], _, _, _, _ => by
    intro mn iname conns hmem
    cases hmem
  | .assign l r :: rest, env, envF, hwf, h => by
    have hwf' : (!(bodyInstOuts children rest).contains l &&
        (refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
        linkedWF children rest) = true := hwf
    simp only [Bool.and_eq_true] at hwf'
    have h' : ((evalExpr we env r).bind fun v =>
        evalAssignsH we children mems rest (fun m => if m = l then v else env m)) =
        some envF := h
    cases hv : evalExpr we env r with
    | none => rw [hv] at h'; cases h'
    | some v =>
      rw [hv] at h'
      have ih := linked_consistent we children mems rest _ envF hwf'.2 h'
      intro mn iname conns hmem
      rcases List.mem_cons.mp hmem with hbad | hmem
      · cases hbad
      · exact ih mn iname conns hmem
  | .inst mn0 iname0 conns0 :: rest, env, envF, hwf, h => by
    have h' : ((children mn0).bind fun cp =>
        (evalAssigns cp.2 mems cp.1.body (connEnv conns0 env)).bind fun cres =>
          evalAssignsH we children mems rest
            (bindOuts cp.1.outputs conns0 cres env)) = some envF := h
    cases hc : children mn0 with
    | none => rw [hc] at h'; cases h'
    | some cp =>
      obtain ⟨child, cwe⟩ := cp
      rw [hc] at h'
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
      obtain ⟨⟨⟨houts, hnd⟩, hreads⟩, hrest⟩ := hwf'
      cases hr : evalAssigns cwe mems child.body (connEnv conns0 env) with
      | none =>
        have h'' : ((evalAssigns cwe mems child.body (connEnv conns0 env)).bind fun cres =>
            evalAssignsH we children mems rest
              (bindOuts child.outputs conns0 cres env)) = some envF := h'
        rw [hr] at h''
        cases h''
      | some cres =>
        have h'' : ((evalAssigns cwe mems child.body (connEnv conns0 env)).bind fun cres =>
            evalAssignsH we children mems rest
              (bindOuts child.outputs conns0 cres env)) = some envF := h'
        rw [hr] at h''
        have ih := linked_consistent we children mems rest _ envF hrest h''
        intro mn iname conns hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · cases heq
          refine ⟨child, cwe, env, cres, hc, hr, ?_, ?_⟩
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
            exact (linked_frame we children mems w _ env envF h hnw).symm
          · intro p hp w hw
            have hwOut : w ∈ instOutWires child.outputs conns0 :=
              mem_instOutWires hp hw
            have hnwRest : w ∉ linkedWrites children rest := by
              have := houts w hwOut
              simpa [List.contains_eq_mem] using this
            rw [linked_frame we children mems w rest _ envF h'' hnwRest]
            exact bindOuts_value conns0 cres child.outputs env hnd p hp w hw
        · exact ih mn iname conns hmem
  | .register o c rk i iv :: rest, env, envF, hwf, h => by
    have ih := linked_consistent we children mems rest env envF hwf h
    intro mn iname conns hmem
    rcases List.mem_cons.mp hmem with hbad | hmem
    · cases hbad
    · exact ih mn iname conns hmem
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, env, envF, hwf, _ => by
    cases hwf

/-! ## Boundedness of the oracle seeding -/

/-- Decidable: every instance-output wire sits, in the given width
environment, at exactly its child port's width. -/
def instOutWidthsOk (children : String → Option (Module × WEnv)) (W : WEnv) :
    List Stmt → Bool
  | [] => true
  | .inst mn _ conns :: rest =>
    (match children mn with
     | some (child, _) =>
       child.outputs.all fun p =>
         match conns.lookup p.name with
         | some (.ref w) => W w == p.ty.bitWidth
         | _ => true
     | none => false) && instOutWidthsOk children W rest
  | _ :: rest => instOutWidthsOk children W rest

/-- Every linked child's outputs fit their declared port widths, whatever
environment the child is evaluated on. -/
def ChildOutsBounded (children : String → Option (Module × WEnv)) (mems : MEnv) : Prop :=
  ∀ mn child cwe, children mn = some (child, cwe) →
    ∀ envIn cres, evalAssigns cwe mems child.body envIn = some cres →
      ∀ p ∈ child.outputs, cres p.name < 2 ^ p.ty.bitWidth

/-- An instance-output wire of the body comes from some instance statement
and one of its child's output ports. -/
theorem mem_bodyInstOuts {children : String → Option (Module × WEnv)} {n : String} :
    ∀ {body : List Stmt}, n ∈ bodyInstOuts children body →
      ∃ mn iname conns child cwe p, Stmt.inst mn iname conns ∈ body ∧
        children mn = some (child, cwe) ∧ p ∈ child.outputs ∧
        conns.lookup p.name = some (.ref n)
  | [], h => by cases h
  | st :: rest, h => by
    rcases List.mem_append.mp h with h | h
    · cases st with
      | inst mn iname conns =>
        have h' : n ∈ (match children mn with
            | some (child, _) => instOutWires child.outputs conns
            | none => []) := h
        cases hc : children mn with
        | none => rw [hc] at h'; cases h'
        | some cp =>
          obtain ⟨child, cwe⟩ := cp
          rw [hc] at h'
          obtain ⟨p, hp, hpn⟩ := List.mem_filterMap.mp h'
          refine ⟨mn, iname, conns, child, cwe, p, List.mem_cons_self, hc, hp, ?_⟩
          cases hl : conns.lookup p.name with
          | none => rw [hl] at hpn; cases hpn
          | some e =>
            rw [hl] at hpn
            cases e <;> first | (cases hpn; rfl) | cases hpn
      | assign l r => cases h
      | register o c rk i iv => cases h
      | memory nm aw dw clk wa wd wen ra rd cr ew er => cases h
    · obtain ⟨mn, iname, conns, child, cwe, p, hm, hc, hp, hl⟩ := mem_bodyInstOuts h
      exact ⟨mn, iname, conns, child, cwe, p, List.mem_cons_of_mem _ hm, hc, hp, hl⟩

theorem instOutWidthsOk_at {children : String → Option (Module × WEnv)} {W : WEnv}
    {mn iname : String} {conns : List (String × Expr)} {child : Module} {cwe : WEnv} :
    ∀ {body : List Stmt}, instOutWidthsOk children W body = true →
      Stmt.inst mn iname conns ∈ body → children mn = some (child, cwe) →
      ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
        W w = p.ty.bitWidth
  | [], _, hm, _, _, _, _, _ => by cases hm
  | st :: rest, hok, hm, hc, p, hp, w, hl => by
    rcases List.mem_cons.mp hm with heq | hm'
    · subst heq
      have hok' : ((match children mn with
          | some (child, _) =>
            child.outputs.all fun p =>
              match conns.lookup p.name with
              | some (.ref w) => W w == p.ty.bitWidth
              | _ => true
          | none => false) && instOutWidthsOk children W rest) = true := hok
      rw [hc] at hok'
      simp only [Bool.and_eq_true, List.all_eq_true] at hok'
      have := hok'.1 p hp
      rw [hl] at this
      exact eq_of_beq this
    · have hrest : instOutWidthsOk children W rest = true := by
        cases st with
        | inst mn' iname' conns' =>
          have hok' : ((match children mn' with
              | some (child, _) =>
                child.outputs.all fun p =>
                  match conns'.lookup p.name with
                  | some (.ref w) => W w == p.ty.bitWidth
                  | _ => true
              | none => false) && instOutWidthsOk children W rest) = true := hok
          simp only [Bool.and_eq_true] at hok'
          exact hok'.2
        | assign l r => exact hok
        | register o c rk i iv => exact hok
        | memory nm aw dw clk wa wd wen ra rd cr ew er => exact hok
      exact instOutWidthsOk_at hrest hm' hc p hp w hl

/-- **The oracle seeding is width-bounded** once the given environment is,
the children's outputs fit their ports, and each instance-output wire sits
at its port's width. -/
theorem seedOuts_bounded {children : String → Option (Module × WEnv)} {mems : MEnv}
    {body : List Stmt} {W : WEnv} {env envF : Env}
    (hinit : Bounded W env) (hcons : Consistent children mems body envF)
    (hw : instOutWidthsOk children W body = true)
    (hcb : ChildOutsBounded children mems) :
    Bounded W (seedOuts children body envF env) := by
  intro n
  show (if (bodyInstOuts children body).contains n then envF n else env n) < 2 ^ W n
  by_cases hc : (bodyInstOuts children body).contains n = true
  · rw [if_pos hc]
    have hmem : n ∈ bodyInstOuts children body := by
      simpa [List.contains_eq_mem] using hc
    obtain ⟨mn, iname, conns, child, cwe, p, hm, hch, hp, hl⟩ := mem_bodyInstOuts hmem
    obtain ⟨child', cwe', envAt, cres, hch', hrun, -, houts⟩ := hcons mn iname conns hm
    rw [hch] at hch'
    cases hch'
    rw [houts p hp n hl, instOutWidthsOk_at hw hm hch p hp n hl]
    exact hcb mn child cwe hch _ cres hrun p hp
  · rw [if_neg hc]
    exact hinit n

end Tools.ShippingHierOpen
