import Tools.ShippingHierOpen
import Sparkle.IR.Machine

/-! # The open run is the linked run, when the children compute the seeds

`Tools.ShippingHierOpen.linked_open` goes from the linked elaboration of a
body (instances evaluated by their children) to the open one (instance
outputs seeded). The machine theorems are stated in the OPEN semantics; to
compose them with the children's theorems the converse is needed: if the
open run from the seeding succeeds and every child, fed with the run's
values on its input connections, computes exactly the values seeded on its
output connections, then the linked elaboration succeeds with the same
result. This file proves that, and its per-cycle and per-run forms for the
linked module semantics (`stepModuleH`, `runModuleH`: the parent's
registers and memories as in `stepModule`, each instance a combinational
child evaluated by `evalAssigns`). -/
namespace Tools.ShippingMachineLinked
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf evalExpr_congr writesOf stmtWrites)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen

/-- What a child is assumed to compute: fed with any environment that agrees
with `envF` on the wires of its input connections, it succeeds and its
output ports carry `envF`'s values on their connected wires. -/
def ChildComputes (we0 : WEnv) (children : String → Option (Module × WEnv)) (mems : MEnv)
    (envF : Env) (mn : String) (conns : List (String × Expr)) : Prop :=
  ∃ child cwe, children mn = some (child, cwe) ∧
    ∀ env1 : Env, (∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ instOutWires child.outputs conns →
        env1 w = envF w) →
      ∃ cres, evalAssigns cwe mems child.body (connEnv conns env1) = some cres ∧
        ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) → cres p.name = envF w

theorem linkedWrites_assign_mem {children : String → Option (Module × WEnv)} :
    ∀ {body : List Stmt} {l : String} {r : Expr}, Stmt.assign l r ∈ body →
      l ∈ linkedWrites children body
  | [], _, _, h => by cases h
  | st :: rest, l, r, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · have := linkedWrites_assign_mem (children := children) h
      cases st with
      | assign l' r' => exact List.mem_cons_of_mem _ this
      | _ => exact List.mem_append_right _ this

/-- The open fold writes assignment targets only. -/
theorem writes_sub_linked {children : String → Option (Module × WEnv)} :
    ∀ (body : List Stmt) (n : String), n ∈ writesOf body →
      linkedWF children body = true → n ∈ linkedWrites children body
  | [], _, h, _ => by simp [writesOf] at h
  | .assign l r :: rest, n, h, hwf => by
    have hwf' : linkedWF children rest = true := by
      simp only [linkedWF, Bool.and_eq_true] at hwf; exact hwf.2
    simp only [writesOf, List.flatMap_cons, stmtWrites, List.mem_append, List.mem_singleton]
      at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (writes_sub_linked rest n h hwf')
  | .inst mn iname conns :: rest, n, h, hwf => by
    have hwf' : linkedWF children rest = true := by
      simp only [linkedWF, Bool.and_eq_true] at hwf; exact hwf.2
    simp only [writesOf, List.flatMap_cons, stmtWrites, List.nil_append] at h
    exact List.mem_append_right _ (writes_sub_linked rest n h hwf')
  | .register o c rk i iv :: rest, n, h, hwf => by
    simp only [writesOf, List.flatMap_cons, stmtWrites, List.nil_append] at h
    exact List.mem_append_right _ (writes_sub_linked rest n h hwf)
  | .memory .. :: _, _, _, hwf => by simp [linkedWF] at hwf

/-- The open fold of a body without memories leaves unwritten wires alone. -/
theorem evalAssigns_frame (we : WEnv) (mems : MEnv) (children : String → Option (Module × WEnv)) :
    ∀ (body : List Stmt) (env result : Env) (z : String), linkedWF children body = true →
      evalAssigns we mems body env = some result → z ∉ writesOf body → result z = env z
  | [], _, _, _, _, h, _ => by cases h; rfl
  | .assign l r :: rest, env, result, z, hwf, h, hz => by
    have hwf' : linkedWF children rest = true := by
      simp only [linkedWF, Bool.and_eq_true] at hwf; exact hwf.2
    have h' : ((evalExpr we env r).bind fun v =>
        evalAssigns we mems rest (fun m => if m = l then v else env m)) = some result := h
    cases hv : evalExpr we env r with
    | none => rw [hv] at h'; cases h'
    | some v =>
      rw [hv] at h'
      simp only [writesOf, List.flatMap_cons, stmtWrites, List.mem_append, List.mem_singleton,
        not_or] at hz
      rw [evalAssigns_frame we mems children rest _ result z hwf' h' hz.2]
      simp [hz.1]
  | .inst mn iname conns :: rest, env, result, z, hwf, h, hz => by
    have hwf' : linkedWF children rest = true := by
      simp only [linkedWF, Bool.and_eq_true] at hwf; exact hwf.2
    exact evalAssigns_frame we mems children rest env result z hwf' h (by
      simpa [writesOf, stmtWrites] using hz)
  | .register o c rk i iv :: rest, env, result, z, hwf, h, hz =>
    evalAssigns_frame we mems children rest env result z hwf h (by
      simpa [writesOf, stmtWrites] using hz)
  | .memory .. :: _, _, _, _, hwf, _, _ => by simp [linkedWF] at hwf

/-- An instance output of a body is one of its linked writes. -/
theorem bodyInstOuts_sub {children : String → Option (Module × WEnv)} :
    ∀ (body : List Stmt) (n : String), n ∈ bodyInstOuts children body →
      n ∈ linkedWrites children body
  | [], _, h => by simp [bodyInstOuts] at h
  | st :: rest, n, h => by
    simp only [bodyInstOuts, List.mem_append] at h
    cases st with
    | assign l r =>
      simp only [stmtInstOuts, List.not_mem_nil, false_or] at h
      exact List.mem_cons_of_mem _ (bodyInstOuts_sub rest n h)
    | _ =>
      rcases h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (bodyInstOuts_sub rest n h)

/-- **The open run is the linked run** when every child computes the values
seeded on its output connections. -/
theorem open_linked (we : WEnv) (children : String → Option (Module × WEnv)) (mems : MEnv)
    (envF : Env) :
    ∀ (body : List Stmt) (env : Env), linkedWF children body = true →
      evalAssigns we mems body (seedOuts children body envF env) = some envF →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
        ChildComputes we children mems envF mn conns) →
      evalAssignsH we children mems body env = some envF
  | [], env, _, h, _ => by
    have : seedOuts children [] envF env = env := by
      funext n; simp [seedOuts, bodyInstOuts]
    rw [this] at h
    cases h
    rfl
  | .assign l r :: rest, env, hwf, h, hch => by
    have hwf' : (!(bodyInstOuts children rest).contains l &&
        (refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
        linkedWF children rest) = true := hwf
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hwf'
    obtain ⟨⟨hl, hrefs⟩, hrest⟩ := hwf'
    have hseed : seedOuts children (.assign l r :: rest) envF env =
        seedOuts children rest envF env := rfl
    rw [hseed] at h
    have h' : ((evalExpr we (seedOuts children rest envF env) r).bind fun v =>
        evalAssigns we mems rest
          (fun m => if m = l then v else seedOuts children rest envF env m)) = some envF := h
    have hexpr : evalExpr we (seedOuts children rest envF env) r = evalExpr we env r := by
      apply evalExpr_congr
      intro n hn
      show (if (bodyInstOuts children rest).contains n then envF n else env n) = env n
      rw [show (bodyInstOuts children rest).contains n = false from by
        simpa using hrefs n hn]
      rfl
    rw [hexpr] at h'
    cases hv : evalExpr we env r with
    | none => rw [hv] at h'; cases h'
    | some v =>
      rw [hv] at h'
      show ((evalExpr we env r).bind fun v =>
        evalAssignsH we children mems rest (fun m => if m = l then v else env m)) = some envF
      rw [hv]
      apply open_linked we children mems envF rest _ hrest _
        (fun mn iname conns hm => hch mn iname conns (List.mem_cons_of_mem _ hm))
      have heq : seedOuts children rest envF (fun m => if m = l then v else env m) =
          (fun m => if m = l then v else seedOuts children rest envF env m) := by
        funext m
        unfold seedOuts
        by_cases hm : m = l
        · subst hm
          rw [show (bodyInstOuts children rest).contains m = false from by simpa using hl]
          simp
        · simp [hm]
      rw [heq]
      exact h'
  | .inst mn iname conns :: rest, env, hwf, h, hch => by
    obtain ⟨child, cwe, hc, hcomp⟩ := hch mn iname conns List.mem_cons_self
    have hwf' : ((match children mn with
        | some (child, _) =>
          (instOutWires child.outputs conns).all
              (fun w => !(linkedWrites children rest).contains w) &&
            decide (instOutWires child.outputs conns).Nodup &&
            conns.all (fun c =>
              match c.2 with
              | .ref w => (instOutWires child.outputs conns).contains w ||
                  !(linkedWrites children rest).contains w
              | _ => true)
        | none => false) && linkedWF children rest) = true := hwf
    rw [hc] at hwf'
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      at hwf'
    obtain ⟨⟨⟨_, hnd⟩, hconns⟩, hrest⟩ := hwf'
    have houts : bodyInstOuts children (.inst mn iname conns :: rest) =
        instOutWires child.outputs conns ++ bodyInstOuts children rest := by
      show stmtInstOuts children (.inst mn iname conns) ++ _ = _
      simp [stmtInstOuts, hc]
    -- the open run skips the instance
    have hskip : evalAssigns we mems (.inst mn iname conns :: rest)
        (seedOuts children (.inst mn iname conns :: rest) envF env) =
        evalAssigns we mems rest (seedOuts children (.inst mn iname conns :: rest) envF env) :=
      rfl
    rw [hskip] at h
    -- the child's inputs: the run's final values
    have hin : ∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ instOutWires child.outputs conns →
        env w = envF w := by
      intro c hcm w hw hno
      have hcw := hconns c hcm
      rw [hw] at hcw
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcw
      have hnotw : w ∉ linkedWrites children rest := by
        rcases hcw with hcw | hcw
        · exact absurd (by simpa using hcw) hno
        · simpa using hcw
      have hnotInst : w ∉ bodyInstOuts children (.inst mn iname conns :: rest) := by
        rw [houts]
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hno hm
        · exact hnotw (bodyInstOuts_sub rest w hm)
      have hfin := evalAssigns_frame we mems children rest _ envF w hrest h
        (fun hm => hnotw (writes_sub_linked rest w hm hrest))
      rw [hfin]
      show env w = (if (bodyInstOuts children (.inst mn iname conns :: rest)).contains w then
        envF w else env w)
      rw [show (bodyInstOuts children (.inst mn iname conns :: rest)).contains w = false from by
        simpa using hnotInst]
      rfl
    obtain ⟨cres, hcres, hvals⟩ := hcomp env hin
    show ((children mn).bind fun cp =>
        (evalAssigns cp.2 mems cp.1.body (connEnv conns env)).bind fun cres =>
          evalAssignsH we children mems rest (bindOuts cp.1.outputs conns cres env)) = some envF
    rw [hc]
    show ((evalAssigns cwe mems child.body (connEnv conns env)).bind fun cres =>
          evalAssignsH we children mems rest (bindOuts child.outputs conns cres env)) = some envF
    rw [hcres]
    show evalAssignsH we children mems rest (bindOuts child.outputs conns cres env) = some envF
    apply open_linked we children mems envF rest _ hrest _
      (fun mn' iname' conns' hm => hch mn' iname' conns' (List.mem_cons_of_mem _ hm))
    have heq : seedOuts children rest envF (bindOuts child.outputs conns cres env) =
        seedOuts children (.inst mn iname conns :: rest) envF env := by
      funext n
      unfold seedOuts
      rw [houts]
      by_cases hr : (bodyInstOuts children rest).contains n = true
      · have hm : n ∈ bodyInstOuts children rest := by simpa using hr
        simp [hm]
      · by_cases hi : n ∈ instOutWires child.outputs conns
        · have hr' : (bodyInstOuts children rest).contains n = false := by simpa using hr
          rw [hr', show (instOutWires child.outputs conns ++ bodyInstOuts children rest).contains n
            = true from by simp [hi]]
          simp only [Bool.false_eq_true, if_false, if_true]
          obtain ⟨p, hp, hpl⟩ : ∃ p ∈ child.outputs, conns.lookup p.name = some (.ref n) := by
            unfold instOutWires at hi
            obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp hi
            refine ⟨p, hp, ?_⟩
            cases hl : conns.lookup p.name with
            | none => rw [hl] at hpe; cases hpe
            | some e =>
              rw [hl] at hpe
              cases e with
              | ref w => simp only [Option.some.injEq] at hpe; rw [hpe]
              | _ => cases hpe
          rw [bindOuts_value conns cres child.outputs env hnd p hp n hpl]
          exact hvals p hp n hpl
        · have hr' : (bodyInstOuts children rest).contains n = false := by simpa using hr
          have hm : n ∉ bodyInstOuts children rest := by simpa using hr
          rw [hr', show (instOutWires child.outputs conns ++ bodyInstOuts children rest).contains n
            = false from by simp [hi, hm]]
          simp only [Bool.false_eq_true, if_false]
          exact bindOuts_frame conns cres n child.outputs env hi
    rw [heq]
    exact h
  | .register o c rk i iv :: rest, env, hwf, h, hch => by
    show evalAssignsH we children mems rest env = some envF
    exact open_linked we children mems envF rest env hwf h
      (fun mn iname conns hm => hch mn iname conns (List.mem_cons_of_mem _ hm))
  | .memory .. :: _, _, hwf, _, _ => by simp [linkedWF] at hwf

/-! ## The linked module semantics -/

/-- One cycle of a module whose instances are combinational children: the
linked elaboration, then the parent's registers and memories as in
`stepModule`. -/
def stepModuleH (we : WEnv) (children : String → Option (Module × WEnv)) (body : List Stmt)
    (env0 : Env) (mems : MEnv) : Option (Env × List (String × Nat) × MEnv) := do
  let envF ← evalAssignsH we children mems body env0
  let nexts ← regNexts we mems body envF
  let mems' ← memNexts we body mems envF
  some (envF, nexts, mems')

/-- `runModule` with the linked cycle. -/
def runModuleH (we : WEnv) (children : String → Option (Module × WEnv)) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) : Nat → (String → Nat) → MEnv → Option (List Env)
  | 0, _, _ => some []
  | k + 1, st, mems => do
    let (envF, nexts, mems') ← stepModuleH we children body (seed k st) mems
    let rest ← runModuleH we children body seed k (applyNexts st nexts) mems'
    some (envF :: rest)

/-- **The linked run is the open run** from seeds `seed'` that agree with the
cycle's seeds except on the instances' output wires, when every child, at
every cycle, computes what the open run carries on its outputs. -/
theorem runModuleH_of_open (we : WEnv) (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed seed' : Nat → (String → Nat) → Env) (hwf : linkedWF children body = true)
    (H : ∀ t st mems envF, evalAssigns we mems body (seed' t st) = some envF →
      seed' t st = seedOuts children body envF (seed t st) ∧
      ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
        ChildComputes we children mems envF mn conns) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModule we body seed' k st mems = some envs →
      runModuleH we children body seed k st mems = some envs
  | 0, _, _, envs, h => h
  | k + 1, st, mems, envs, h => by
    have hstep : stepModuleH we children body (seed k st) mems =
        stepModule we body (seed' k st) mems := by
      cases hF : evalAssigns we mems body (seed' k st) with
      | none =>
        -- no open run: the cycle fails on both sides only if the linked one does too
        simp only [runModule, stepModule, hF] at h
        cases h
      | some envF =>
        obtain ⟨hseed, hch⟩ := H k st mems envF hF
        have hlinked : evalAssignsH we children mems body (seed k st) = some envF := by
          apply open_linked we children mems envF body (seed k st) hwf _ hch
          rw [← hseed]; exact hF
        unfold stepModuleH stepModule
        rw [hlinked, hF]
    show (stepModuleH we children body (seed k st) mems).bind (fun r =>
        (runModuleH we children body seed k (applyNexts st r.2.1) r.2.2).bind
          (fun rest => some (r.1 :: rest))) = some envs
    have h' : (stepModule we body (seed' k st) mems).bind (fun r =>
        (runModule we body seed' k (applyNexts st r.2.1) r.2.2).bind
          (fun rest => some (r.1 :: rest))) = some envs := h
    rw [hstep]
    cases hS : stepModule we body (seed' k st) mems with
    | none => rw [hS] at h'; cases h'
    | some r =>
      rw [hS] at h'
      simp only [Option.bind_some] at h' ⊢
      cases hR : runModule we body seed' k (applyNexts st r.2.1) r.2.2 with
      | none => rw [hR] at h'; cases h'
      | some rest =>
        rw [hR] at h'
        rw [runModuleH_of_open we children body seed seed' hwf H k _ _ rest hR]
        exact h'

/-! ## The compiler's order check is the correspondence's condition -/

/-- A design's modules as the linked semantics reads them. -/
def childMap (ms : List Module) : String → Option (Module × WEnv) :=
  fun mn => (Sparkle.IR.Machine.moduleByName ms mn).map fun c =>
    (c, Sparkle.IR.RegDedup.declWidth c)

theorem stmtOuts_eq (ms : List Module) (st : Stmt) :
    Sparkle.IR.Machine.stmtOuts (Sparkle.IR.Machine.moduleByName ms) st =
      stmtInstOuts (childMap ms) st := by
  cases st with
  | inst mn iname conns =>
    simp only [Sparkle.IR.Machine.stmtOuts, stmtInstOuts, childMap]
    cases Sparkle.IR.Machine.moduleByName ms mn <;> rfl
  | _ => rfl

theorem bodyOuts_eq (ms : List Module) :
    ∀ body : List Stmt, Sparkle.IR.Machine.bodyOuts (Sparkle.IR.Machine.moduleByName ms) body =
      bodyInstOuts (childMap ms) body
  | [] => rfl
  | st :: rest => by
    simp only [Sparkle.IR.Machine.bodyOuts, bodyInstOuts, stmtOuts_eq, bodyOuts_eq ms rest]

theorem bodyWrites_eq (ms : List Module) :
    ∀ body : List Stmt,
      Sparkle.IR.Machine.bodyWrites (Sparkle.IR.Machine.moduleByName ms) body =
        linkedWrites (childMap ms) body
  | [] => rfl
  | .assign l r :: rest => by
    simp only [Sparkle.IR.Machine.bodyWrites, linkedWrites, bodyWrites_eq ms rest]
  | .inst mn iname conns :: rest => by
    show Sparkle.IR.Machine.stmtOuts _ (.inst mn iname conns) ++ _ =
      stmtInstOuts _ (.inst mn iname conns) ++ _
    rw [stmtOuts_eq, bodyWrites_eq ms rest]
  | .register o c rk i iv :: rest => by
    show Sparkle.IR.Machine.stmtOuts _ (.register o c rk i iv) ++ _ =
      stmtInstOuts _ (.register o c rk i iv) ++ _
    rw [stmtOuts_eq, bodyWrites_eq ms rest]
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest => by
    show Sparkle.IR.Machine.stmtOuts _ (.memory nm aw dw clk wa wd wen ra rd cr ew er) ++ _ =
      stmtInstOuts _ (.memory nm aw dw clk wa wd wen ra rd cr ew er) ++ _
    rw [stmtOuts_eq, bodyWrites_eq ms rest]

theorem linkedOk_eq (ms : List Module) :
    ∀ body : List Stmt,
      Sparkle.IR.Machine.linkedOk (Sparkle.IR.Machine.moduleByName ms) body =
        linkedWF (childMap ms) body
  | [] => rfl
  | .assign l r :: rest => by
    simp only [Sparkle.IR.Machine.linkedOk, linkedWF, bodyOuts_eq, linkedOk_eq ms rest]
  | .inst mn iname conns :: rest => by
    simp only [Sparkle.IR.Machine.linkedOk, linkedWF, linkedOk_eq ms rest, bodyWrites_eq]
    unfold childMap
    cases Sparkle.IR.Machine.moduleByName ms mn <;> rfl
  | .register o c rk i iv :: rest => by
    simp only [Sparkle.IR.Machine.linkedOk, linkedWF, linkedOk_eq ms rest]
  | .memory .. :: _ => rfl

end Tools.ShippingMachineLinked
