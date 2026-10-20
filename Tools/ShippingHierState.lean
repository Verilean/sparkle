import Tools.ShippingMachineLinked

/-! # A hierarchical run with stateful children

`runModuleH` (ShippingMachineLinked) evaluates every instance as a
COMBINATIONAL child. A child with registers or memories keeps a state of
its own across cycles: here each instance (by its instance name) owns a
`KidState` — its registers' values and its memories — and an instance
statement advances its child by one `stepModule` cycle on the
connection-fed environment backed by that state (`connEnvS`), the parent's
own registers and memories stepping as in `stepModule`.

The bridge to the open-module view, as for combinational children: if the
open run from the seeding succeeds and every child, fed with the run's
values on its input connections, steps to outputs equal to the values seeded
on its output connections (and to a next state not depending on the rest of
its environment), then the stateful linked run succeeds with the same
environments (`open_linkedK`, `runModuleT_of_open`). -/
namespace Tools.ShippingHierState
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf evalExpr_congr writesOf stmtWrites)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked

/-- A child instance's state: its registers' values and its memories. -/
structure KidState where
  st : String → Nat
  mems : MEnv

/-- The connections of a child's INPUT ports (its output ports' connections
dropped): what feeds the child; its output ports read its own state. -/
def inConns (outs : List Port) (conns : List (String × Expr)) : List (String × Expr) :=
  conns.filter fun c => !(outs.map (·.name)).contains c.1

/-- One cycle's elaboration with stateful children: an instance steps its
child on the connection-fed environment backed by the child's state at the
start of the cycle (`kids`), binds the child's outputs, and records the
child's next state in `acc`. -/
def evalAssignsK (we : WEnv) (children : String → Option (Module × WEnv))
    (kids : String → KidState) (mems : MEnv) :
    List Stmt → Env → (String → KidState) → Option (Env × (String → KidState))
  | [], env, acc => some (env, acc)
  | .assign l r :: rest, env, acc => do
    let v ← evalExpr we env r
    evalAssignsK we children kids mems rest (fun n => if n = l then v else env n) acc
  | .inst mn iname conns :: rest, env, acc => do
    let (child, cwe) ← children mn
    let (cres, nexts, cmems) ← stepModule cwe child.body
      (connEnvS (inConns child.outputs conns) env (kids iname).st) (kids iname).mems
    evalAssignsK we children kids mems rest (bindOuts child.outputs conns cres env)
      (fun n => if n = iname then ⟨applyNexts (kids iname).st nexts, cmems⟩ else acc n)
  | .register .. :: rest, env, acc => evalAssignsK we children kids mems rest env acc
  | .memory .. :: rest, env, acc => evalAssignsK we children kids mems rest env acc

/-- The children's states after one cycle: each instance's given next
registers and memories (`nx`, `mx`, by instance name). -/
def kidsAfter (kids : String → KidState) (nx : String → List (String × Nat))
    (mx : String → MEnv) : List Stmt → (String → KidState) → (String → KidState)
  | [], acc => acc
  | .inst _ iname _ :: rest, acc =>
    kidsAfter kids nx mx rest
      (fun n => if n = iname then ⟨applyNexts (kids iname).st (nx iname), mx iname⟩ else acc n)
  | _ :: rest, acc => kidsAfter kids nx mx rest acc

/-- What a stateful child is assumed to do in one cycle: fed with any
environment that agrees with `envF` on the wires of its input connections,
it steps to the next registers `nx` and memories `mx` (whatever the rest of
the environment) and its output ports carry `envF`'s values on their
connected wires. -/
def ChildStepsK (children : String → Option (Module × WEnv)) (kids : String → KidState)
    (envF : Env) (mn iname : String) (conns : List (String × Expr))
    (nx : List (String × Nat)) (mx : MEnv) : Prop :=
  ∃ child cwe, children mn = some (child, cwe) ∧
    ∀ env1 : Env, (∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ instOutWires child.outputs conns →
        env1 w = envF w) →
      ∃ cres, stepModule cwe child.body (connEnvS (inConns child.outputs conns) env1
          (kids iname).st) (kids iname).mems = some (cres, nx, mx) ∧
        ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) → cres p.name = envF w

/-- **The open run is the stateful linked run** when every child steps to
the values seeded on its output connections. -/
theorem open_linkedK (we : WEnv) (children : String → Option (Module × WEnv))
    (kids : String → KidState) (mems : MEnv) (envF : Env)
    (nx : String → List (String × Nat)) (mx : String → MEnv) :
    ∀ (body : List Stmt) (env : Env) (acc : String → KidState), linkedWF children body = true →
      evalAssigns we mems body (seedOuts children body envF env) = some envF →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
        ChildStepsK children kids envF mn iname conns (nx iname) (mx iname)) →
      evalAssignsK we children kids mems body env acc =
        some (envF, kidsAfter kids nx mx body acc)
  | [], env, acc, _, h, _ => by
    have : seedOuts children [] envF env = env := by
      funext n; simp [seedOuts, bodyInstOuts]
    rw [this] at h
    cases h
    rfl
  | .assign l r :: rest, env, acc, hwf, h, hch => by
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
        evalAssignsK we children kids mems rest (fun m => if m = l then v else env m) acc) =
          some (envF, kidsAfter kids nx mx rest acc)
      rw [hv]
      apply open_linkedK we children kids mems envF nx mx rest _ acc hrest _
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
  | .inst mn iname conns :: rest, env, acc, hwf, h, hch => by
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
    have hskip : evalAssigns we mems (.inst mn iname conns :: rest)
        (seedOuts children (.inst mn iname conns :: rest) envF env) =
        evalAssigns we mems rest (seedOuts children (.inst mn iname conns :: rest) envF env) :=
      rfl
    rw [hskip] at h
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
        (stepModule cp.2 cp.1.body (connEnvS (inConns cp.1.outputs conns) env (kids iname).st)
          (kids iname).mems).bind
          fun r => evalAssignsK we children kids mems rest (bindOuts cp.1.outputs conns r.1 env)
            (fun n => if n = iname then ⟨applyNexts (kids iname).st r.2.1, r.2.2⟩ else acc n)) =
        some (envF, kidsAfter kids nx mx (.inst mn iname conns :: rest) acc)
    rw [hc]
    show ((stepModule cwe child.body (connEnvS (inConns child.outputs conns) env (kids iname).st)
          (kids iname).mems).bind
          fun r => evalAssignsK we children kids mems rest (bindOuts child.outputs conns r.1 env)
            (fun n => if n = iname then ⟨applyNexts (kids iname).st r.2.1, r.2.2⟩ else acc n)) =
        some (envF, kidsAfter kids nx mx (.inst mn iname conns :: rest) acc)
    rw [hcres]
    show evalAssignsK we children kids mems rest (bindOuts child.outputs conns cres env)
        (fun n => if n = iname then ⟨applyNexts (kids iname).st (nx iname), mx iname⟩
          else acc n) =
      some (envF, kidsAfter kids nx mx rest
        (fun n => if n = iname then ⟨applyNexts (kids iname).st (nx iname), mx iname⟩
          else acc n))
    apply open_linkedK we children kids mems envF nx mx rest _ _ hrest _
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
  | .register o c rk i iv :: rest, env, acc, hwf, h, hch => by
    show evalAssignsK we children kids mems rest env acc =
      some (envF, kidsAfter kids nx mx rest acc)
    exact open_linkedK we children kids mems envF nx mx rest env acc hwf h
      (fun mn iname conns hm => hch mn iname conns (List.mem_cons_of_mem _ hm))
  | .memory .. :: _, _, _, hwf, _, _ => by simp [linkedWF] at hwf

/-! ## The stateful linked module semantics -/

/-- One cycle: the stateful linked elaboration, then the parent's registers
and memories as in `stepModule`; the children's next states. -/
def stepModuleT (we : WEnv) (children : String → Option (Module × WEnv)) (body : List Stmt)
    (env0 : Env) (mems : MEnv) (kids : String → KidState) :
    Option (Env × List (String × Nat) × MEnv × (String → KidState)) := do
  let (envF, kids') ← evalAssignsK we children kids mems body env0 kids
  let nexts ← regNexts we mems body envF
  let mems' ← memNexts we body mems envF
  some (envF, nexts, mems', kids')

/-- `runModule` with stateful children (the seed index counts down, as in
`runModule`). -/
def runModuleT (we : WEnv) (children : String → Option (Module × WEnv)) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) :
    Nat → (String → Nat) → MEnv → (String → KidState) → Option (List Env)
  | 0, _, _, _ => some []
  | k + 1, st, mems, kids => do
    let (envF, nexts, mems', kids') ← stepModuleT we children body (seed k st) mems kids
    let rest ← runModuleT we children body seed k (applyNexts st nexts) mems' kids'
    some (envF :: rest)

/-- A successful cycle of `stepModule`, in its three steps. -/
theorem stepModule_some {we : WEnv} {body : List Stmt} {env0 : Env} {mems : MEnv}
    {r : Env × List (String × Nat) × MEnv} (h : stepModule we body env0 mems = some r) :
    ∃ envF nexts mems', evalAssigns we mems body env0 = some envF ∧
      regNexts we mems body envF = some nexts ∧ memNexts we body mems envF = some mems' ∧
      r = (envF, nexts, mems') := by
  unfold stepModule at h
  cases hE : evalAssigns we mems body env0 with
  | none => simp [hE] at h
  | some envF =>
    cases hN : regNexts we mems body envF with
    | none => simp [hE, hN] at h
    | some nexts =>
      cases hM : memNexts we body mems envF with
      | none => simp [hE, hN, hM] at h
      | some mems' =>
        simp [hE, hN, hM] at h
        exact ⟨envF, nexts, mems', rfl, hN, hM, h.symm⟩

/-- **The stateful linked run is the open run** from seeds `seed'` that agree
with the cycle's seeds except on the instances' output wires, when at every
cycle every child steps to what the open run carries on its outputs. `Kid m`
is what is known with `m` cycles left (the seed index of the next cycle is
`m - 1`) of the parent's state and memories and the children's states; each
cycle keeps it. -/
theorem runModuleT_of_open (we : WEnv) (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed seed' : Nat → (String → Nat) → Env)
    (hwf : linkedWF children body = true)
    (Kid : Nat → (String → Nat) → MEnv → (String → KidState) → Prop)
    (nx : Nat → (String → KidState) → String → List (String × Nat))
    (mx : Nat → (String → KidState) → String → MEnv)
    (H : ∀ m st mems kids envF nexts mems', Kid (m + 1) st mems kids →
      evalAssigns we mems body (seed' m st) = some envF →
      regNexts we mems body envF = some nexts → memNexts we body mems envF = some mems' →
      seed' m st = seedOuts children body envF (seed m st) ∧
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
        ChildStepsK children kids envF mn iname conns (nx m kids iname) (mx m kids iname)) ∧
      Kid m (applyNexts st nexts) mems' (kidsAfter kids (nx m kids) (mx m kids) body kids)) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (kids : String → KidState) (envs : List Env),
      Kid k st mems kids → runModule we body seed' k st mems = some envs →
      runModuleT we children body seed k st mems kids = some envs
  | 0, _, _, _, envs, _, h => h
  | k + 1, st, mems, kids, envs, hk, h => by
    have h' : (stepModule we body (seed' k st) mems).bind (fun r =>
        (runModule we body seed' k (applyNexts st r.2.1) r.2.2).bind
          (fun rest => some (r.1 :: rest))) = some envs := h
    cases hS : stepModule we body (seed' k st) mems with
    | none => rw [hS] at h'; cases h'
    | some r =>
      obtain ⟨envF, nexts, mems', hF, hN, hM, rfl⟩ := stepModule_some hS
      obtain ⟨hseed, hch, hkid⟩ := H k st mems kids envF nexts mems' hk hF hN hM
      have hlinked : evalAssignsK we children kids mems body (seed k st) kids =
          some (envF, kidsAfter kids (nx k kids) (mx k kids) body kids) := by
        apply open_linkedK we children kids mems envF (nx k kids) (mx k kids) body (seed k st)
          kids hwf _ hch
        rw [← hseed]; exact hF
      have hstepT : stepModuleT we children body (seed k st) mems kids =
          some (envF, nexts, mems', kidsAfter kids (nx k kids) (mx k kids) body kids) := by
        simp [stepModuleT, hlinked, hN, hM]
      rw [hS] at h'
      simp only [Option.bind_some] at h'
      cases hR : runModule we body seed' k (applyNexts st nexts) mems' with
      | none => rw [hR] at h'; cases h'
      | some rest =>
        rw [hR] at h'
        simp only [Option.bind_some, Option.some.injEq] at h'
        show (stepModuleT we children body (seed k st) mems kids).bind (fun r =>
          (runModuleT we children body seed k (applyNexts st r.2.1) r.2.2.1 r.2.2.2).bind
            (fun rest => some (r.1 :: rest))) = some envs
        rw [hstepT]
        simp only [Option.bind_some]
        rw [runModuleT_of_open we children body seed seed' hwf Kid nx mx H k _ _ _ rest hkid hR]
        simp [h']

/-! ## The children's own steps -/

theorem lookup_mem :
    ∀ (l : List (String × Expr)) (n : String) (e : Expr), l.lookup n = some e →
      ∃ c ∈ l, c.1 = n ∧ c.2 = e
  | [], _, _, h => by simp at h
  | c :: rest, n, e, h => by
    simp only [List.lookup] at h
    by_cases hn : n = c.1
    · have hb : (n == c.1) = true := by simp [hn]
      rw [hb] at h
      simp only [Option.some.injEq] at h
      exact ⟨c, List.mem_cons_self, hn.symm, h⟩
    · have hb : (n == c.1) = false := by simp [hn]
      rw [hb] at h
      obtain ⟨c', hc', h1, h2⟩ := lookup_mem rest n e h
      exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2⟩

/-- A child's one step, on the final values of the wires feeding it, is its
`ChildStepsK` — when no input connection reads one of the instance's own
output wires. -/
theorem childStepsK_of_step {children : String → Option (Module × WEnv)}
    {kids : String → KidState} {envF : Env} {mn iname : String} {conns : List (String × Expr)}
    {child : Module} {cwe : WEnv} {cres : Env} {nx : List (String × Nat)} {mx : MEnv}
    (hc : children mn = some (child, cwe))
    (hnofb : ∀ c ∈ inConns child.outputs conns, ∀ w, c.2 = .ref w →
      w ∉ instOutWires child.outputs conns)
    (hstep : stepModule cwe child.body (connEnvS (inConns child.outputs conns) envF
      (kids iname).st) (kids iname).mems = some (cres, nx, mx))
    (hout : ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
      cres p.name = envF w) :
    ChildStepsK children kids envF mn iname conns nx mx := by
  refine ⟨child, cwe, hc, fun env1 hagree => ⟨cres, ?_, hout⟩⟩
  have heq : connEnvS (inConns child.outputs conns) env1 (kids iname).st =
      connEnvS (inConns child.outputs conns) envF (kids iname).st := by
    funext n
    unfold connEnvS
    cases hl : (inConns child.outputs conns).lookup n with
    | none => rfl
    | some e =>
      cases e with
      | ref w =>
        obtain ⟨c, hcin, _, hc2⟩ := lookup_mem _ n (.ref w) hl
        have hcm : c ∈ conns := (List.mem_filter.mp hcin).1
        exact hagree c hcm w hc2 (hnofb c hcin w hc2)
      | _ => rfl
  rw [heq]; exact hstep

/-- The instance names of a body, in order. -/
def instNames : List Stmt → List String
  | [] => []
  | .inst _ iname _ :: rest => iname :: instNames rest
  | _ :: rest => instNames rest

theorem kidsAfter_frame (kids : String → KidState) (nx : String → List (String × Nat))
    (mx : String → MEnv) :
    ∀ (body : List Stmt) (acc : String → KidState) (n : String), n ∉ instNames body →
      kidsAfter kids nx mx body acc n = acc n
  | [], _, _, _ => rfl
  | .inst _ iname _ :: rest, acc, n, hn => by
    simp only [instNames, List.mem_cons, not_or] at hn
    show kidsAfter kids nx mx rest _ n = acc n
    rw [kidsAfter_frame kids nx mx rest _ n hn.2]
    simp [Ne.symm hn.1, hn.1]
  | .assign _ _ :: rest, acc, n, hn => kidsAfter_frame kids nx mx rest acc n hn
  | .register .. :: rest, acc, n, hn => kidsAfter_frame kids nx mx rest acc n hn
  | .memory .. :: rest, acc, n, hn => kidsAfter_frame kids nx mx rest acc n hn

theorem kidsAfter_inst (kids : String → KidState) (nx : String → List (String × Nat))
    (mx : String → MEnv) :
    ∀ (body : List Stmt) (acc : String → KidState), (instNames body).Nodup →
      ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
        kidsAfter kids nx mx body acc iname = ⟨applyNexts (kids iname).st (nx iname), mx iname⟩
  | [], _, _, _, _, _, h => by cases h
  | .inst mn' iname' conns' :: rest, acc, hnd, mn, iname, conns, h => by
    simp only [instNames, List.nodup_cons] at hnd
    show kidsAfter kids nx mx rest _ iname = _
    rcases List.mem_cons.mp h with h | h
    · injection h with h1 h2 h3
      subst h2
      rw [kidsAfter_frame kids nx mx rest _ iname hnd.1]
      simp
    · exact kidsAfter_inst kids nx mx rest _ hnd.2 mn iname conns h
  | .assign _ _ :: rest, acc, hnd, mn, iname, conns, h =>
    kidsAfter_inst kids nx mx rest acc hnd mn iname conns (by
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h)
  | .register .. :: rest, acc, hnd, mn, iname, conns, h =>
    kidsAfter_inst kids nx mx rest acc hnd mn iname conns (by
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h)
  | .memory .. :: rest, acc, hnd, mn, iname, conns, h =>
    kidsAfter_inst kids nx mx rest acc hnd mn iname conns (by
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h)

/-- **The stateful linked run from the children's own steps.** If the open
run of the parent produces `P`'s environments (by seed index) and every
child, from its states `KS` (by seed index, before the cycle), stepped on the
values `P` gives the wires feeding it, reaches the next states and outputs
the open run carries on its output wires, then the stateful linked run
produces the same environments. Instance names are distinct and no input
connection reads one of the instance's own output wires (decidable facts of
the module). -/
theorem runModuleT_of_kids (we : WEnv) (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed seed' : Nat → (String → Nat) → Env)
    (hwf : linkedWF children body = true) (hnd : (instNames body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hseed : ∀ t st mems envF, evalAssigns we mems body (seed' t st) = some envF →
      seed' t st = seedOuts children body envF (seed t st))
    (P : Nat → Env) (KS : Nat → String → KidState) (NX : Nat → String → List (String × Nat))
    (MX : Nat → String → MEnv)
    (hkid : ∀ t mn iname conns, Stmt.inst mn iname conns ∈ body → ∃ child cwe cres,
      children mn = some (child, cwe) ∧
      stepModule cwe child.body (connEnvS (inConns child.outputs conns) (P t) (KS (t + 1) iname).st)
        (KS (t + 1) iname).mems = some (cres, NX t iname, MX t iname) ∧
      KS t iname = ⟨applyNexts (KS (t + 1) iname).st (NX t iname), MX t iname⟩ ∧
      ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) → cres p.name = P t w) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (kids : String → KidState) (envs : List Env),
      runModule we body seed' k st mems = some envs →
      (∀ j, j < k → envs[j]? = some (P (k - 1 - j))) →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body → kids iname = KS k iname) →
      runModuleT we children body seed k st mems kids = some envs := by
  intro k st mems kids envs hrun hP hk0
  let Kid : Nat → (String → Nat) → MEnv → (String → KidState) → Prop := fun m st mems kids =>
    (∃ envs', runModule we body seed' m st mems = some envs' ∧
      ∀ j, j < m → envs'[j]? = some (P (m - 1 - j))) ∧
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → kids iname = KS m iname
  apply runModuleT_of_open we children body seed seed' hwf Kid (fun m _ => NX m) (fun m _ => MX m)
    _ k st mems kids envs ⟨⟨envs, hrun, hP⟩, hk0⟩ hrun
  intro m st mems kids envF nexts mems' ⟨⟨envs', hrun', hP'⟩, hkids⟩ hF hN hM
  -- the open run's first environment is `P m`
  have hstep : stepModule we body (seed' m st) mems = some (envF, nexts, mems') := by
    simp [stepModule, hF, hN, hM]
  have h' : (stepModule we body (seed' m st) mems).bind (fun r =>
      (runModule we body seed' m (applyNexts st r.2.1) r.2.2).bind
        (fun rest => some (r.1 :: rest))) = some envs' := hrun'
  rw [hstep] at h'
  simp only [Option.bind_some] at h'
  cases hR : runModule we body seed' m (applyNexts st nexts) mems' with
  | none => rw [hR] at h'; cases h'
  | some rest =>
    rw [hR] at h'
    simp only [Option.bind_some, Option.some.injEq] at h'
    subst h'
    have hP0 := hP' 0 (by omega)
    simp only [List.getElem?_cons_zero, Option.some.injEq, Nat.sub_zero] at hP0
    rw [show m + 1 - 1 = m by omega] at hP0
    refine ⟨hseed m st mems envF hF, ?_, ⟨rest, hR, ?_⟩, ?_⟩
    · intro mn iname conns hm
      obtain ⟨child, cwe, cres, hc, hcs, _, hout⟩ := hkid m mn iname conns hm
      apply childStepsK_of_step hc (hnofb mn iname conns hm child cwe hc)
      · rw [hkids mn iname conns hm, hP0]; exact hcs
      · intro p hp w hw; rw [hP0]; exact hout p hp w hw
    · intro j hj
      have := hP' (j + 1) (by omega)
      simp only [List.getElem?_cons_succ] at this
      rw [this, show m + 1 - 1 - (j + 1) = m - 1 - j by omega]
    · intro mn iname conns hm
      obtain ⟨child, cwe, cres, hc, hcs, hks, hout⟩ := hkid m mn iname conns hm
      rw [kidsAfter_inst kids (NX m) (MX m) body kids hnd mn iname conns hm, hks,
        hkids mn iname conns hm]

/-! ## From the children's own runs -/

/-- The first instance of a body with instance name `iname`: its module and
connections. -/
def instOf : List Stmt → String → Option (String × List (String × Expr))
  | [], _ => none
  | .inst mn i conns :: rest, iname => if i = iname then some (mn, conns) else instOf rest iname
  | _ :: rest, iname => instOf rest iname

theorem mem_instNames : ∀ (body : List Stmt) (mn iname : String) (conns : List (String × Expr)),
    Stmt.inst mn iname conns ∈ body → iname ∈ instNames body
  | [], _, _, _, h => by cases h
  | st :: rest, mn, iname, conns, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h; simp [instNames]
    · have := mem_instNames rest mn iname conns h
      cases st <;> simp only [instNames] <;> first
        | exact List.mem_cons_of_mem _ this
        | exact this

theorem instOf_mem : ∀ (body : List Stmt), (instNames body).Nodup →
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → instOf body iname = some (mn, conns)
  | [], _, _, _, _, h => by cases h
  | .inst mn' i conns' :: rest, hnd, mn, iname, conns, h => by
    simp only [instNames, List.nodup_cons] at hnd
    simp only [instOf]
    rcases List.mem_cons.mp h with h | h
    · injection h with h1 h2 h3
      subst h1; subst h2; subst h3
      simp
    · have hne : i ≠ iname := by
        intro he; subst he
        exact hnd.1 (mem_instNames rest mn i conns h)
      rw [if_neg hne]
      exact instOf_mem rest hnd.2 mn iname conns h
  | .assign _ _ :: rest, hnd, mn, iname, conns, h =>
    instOf_mem rest hnd mn iname conns (by
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h)
  | .register .. :: rest, hnd, mn, iname, conns, h =>
    instOf_mem rest hnd mn iname conns (by
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h)
  | .memory .. :: rest, hnd, mn, iname, conns, h =>
    instOf_mem rest hnd mn iname conns (by
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h)

/-- The cycle of instance `iname`'s child on the values `env` gives the wires
feeding it, from the child's state in `kids` (`none` when the instance or its
child is missing or the step fails). -/
def kidStep (children : String → Option (Module × WEnv)) (body : List Stmt) (env : Env)
    (kids : String → KidState) (iname : String) :
    Option (Env × List (String × Nat) × MEnv) := do
  let (mn, conns) ← instOf body iname
  let (child, cwe) ← children mn
  stepModule cwe child.body (connEnvS (inConns child.outputs conns) env (kids iname).st)
    (kids iname).mems

/-- **The stateful linked run from the children's own runs.** If the open
run of the parent produces `P`'s environments (by seed index) and every
child's own run — fed, at every cycle, with the values `P` gives the wires
feeding it, from its state in `kids` — shows the open run's values on its
output wires, then the stateful linked run produces the same environments.
Instance names are distinct and no input connection reads one of the
instance's own output wires (decidable facts of the module). -/
theorem runModuleT_of_childRuns (we : WEnv) (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed seed' : Nat → (String → Nat) → Env)
    (hwf : linkedWF children body = true) (hnd : (instNames body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hseed : ∀ t st mems envF, evalAssigns we mems body (seed' t st) = some envF →
      seed' t st = seedOuts children body envF (seed t st))
    (P : Nat → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (kids : String → KidState) (envs : List Env),
      runModule we body seed' k st mems = some envs →
      (∀ j, j < k → envs[j]? = some (P (k - 1 - j))) →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∃ child cwe cenvs,
        children mn = some (child, cwe) ∧
        runModule cwe child.body (fun t cst => connEnvS (inConns child.outputs conns) (P t) cst)
          k (kids iname).st (kids iname).mems = some cenvs ∧
        ∀ j, j < k → ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
          (cenvs[j]?).map (· p.name) = some (P (k - 1 - j) w)) →
      runModuleT we children body seed k st mems kids = some envs := by
  intro k st mems kids envs hrun hP hk0
  let Kid : Nat → (String → Nat) → MEnv → (String → KidState) → Prop := fun m st mems kids =>
    (∃ envs', runModule we body seed' m st mems = some envs' ∧
      ∀ j, j < m → envs'[j]? = some (P (m - 1 - j))) ∧
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∃ child cwe cenvs,
      children mn = some (child, cwe) ∧
      runModule cwe child.body (fun t cst => connEnvS (inConns child.outputs conns) (P t) cst)
        m (kids iname).st (kids iname).mems = some cenvs ∧
      ∀ j, j < m → ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
        (cenvs[j]?).map (· p.name) = some (P (m - 1 - j) w)
  let nx : Nat → (String → KidState) → String → List (String × Nat) := fun m kids iname =>
    match kidStep children body (P m) kids iname with
    | some r => r.2.1
    | none => []
  let mx : Nat → (String → KidState) → String → MEnv := fun m kids iname =>
    match kidStep children body (P m) kids iname with
    | some r => r.2.2
    | none => (kids iname).mems
  apply runModuleT_of_open we children body seed seed' hwf Kid nx mx
    _ k st mems kids envs ⟨⟨envs, hrun, hP⟩, hk0⟩ hrun
  intro m st mems kids envF nexts mems' ⟨⟨envs', hrun', hP'⟩, hkids⟩ hF hN hM
  have hstep : stepModule we body (seed' m st) mems = some (envF, nexts, mems') := by
    simp [stepModule, hF, hN, hM]
  have h' : (stepModule we body (seed' m st) mems).bind (fun r =>
      (runModule we body seed' m (applyNexts st r.2.1) r.2.2).bind
        (fun rest => some (r.1 :: rest))) = some envs' := hrun'
  rw [hstep] at h'
  simp only [Option.bind_some] at h'
  cases hR : runModule we body seed' m (applyNexts st nexts) mems' with
  | none => rw [hR] at h'; cases h'
  | some rest =>
    rw [hR] at h'
    simp only [Option.bind_some, Option.some.injEq] at h'
    subst h'
    have hP0 := hP' 0 (by omega)
    simp only [List.getElem?_cons_zero, Option.some.injEq, Nat.sub_zero] at hP0
    rw [show m + 1 - 1 = m by omega] at hP0
    -- each child's first cycle, and the rest of its run
    have hchild : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∃ child cwe cres ctail,
        children mn = some (child, cwe) ∧
        kidStep children body (P m) kids iname = some (cres, nx m kids iname, mx m kids iname) ∧
        stepModule cwe child.body (connEnvS (inConns child.outputs conns) envF (kids iname).st)
          (kids iname).mems = some (cres, nx m kids iname, mx m kids iname) ∧
        runModule cwe child.body (fun t cst => connEnvS (inConns child.outputs conns) (P t) cst)
          m (applyNexts (kids iname).st (nx m kids iname)) (mx m kids iname) = some ctail ∧
        (∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) → cres p.name = envF w) ∧
        ∀ j, j < m → ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
          (ctail[j]?).map (· p.name) = some (P (m - 1 - j) w) := by
      intro mn iname conns hm
      obtain ⟨child, cwe, cenvs, hc, hcrun, hcobs⟩ := hkids mn iname conns hm
      have hcrun' : (stepModule cwe child.body
          (connEnvS (inConns child.outputs conns) (P m) (kids iname).st) (kids iname).mems).bind
          (fun r => (runModule cwe child.body
            (fun t cst => connEnvS (inConns child.outputs conns) (P t) cst) m
            (applyNexts (kids iname).st r.2.1) r.2.2).bind (fun rest => some (r.1 :: rest))) =
          some cenvs := hcrun
      cases hcs : stepModule cwe child.body
          (connEnvS (inConns child.outputs conns) (P m) (kids iname).st) (kids iname).mems with
      | none => rw [hcs] at hcrun'; cases hcrun'
      | some r =>
        obtain ⟨cres, cn, cm⟩ := r
        have hks : kidStep children body (P m) kids iname = some (cres, cn, cm) := by
          simp [kidStep, instOf_mem body hnd mn iname conns hm, hc, hcs]
        have hnx : nx m kids iname = cn := by simp [nx, hks]
        have hmx : mx m kids iname = cm := by simp [mx, hks]
        rw [hcs] at hcrun'
        simp only [Option.bind_some] at hcrun'
        cases hct : runModule cwe child.body
            (fun t cst => connEnvS (inConns child.outputs conns) (P t) cst) m
            (applyNexts (kids iname).st cn) cm with
        | none => rw [hct] at hcrun'; cases hcrun'
        | some ctail =>
          rw [hct] at hcrun'
          simp only [Option.bind_some, Option.some.injEq] at hcrun'
          subst hcrun'
          refine ⟨child, cwe, cres, ctail, hc, by rw [hks, hnx, hmx], by rw [hP0, hnx, hmx]; exact hcs,
            by rw [hnx, hmx]; exact hct, ?_, ?_⟩
          · intro p hp w hw
            have := hcobs 0 (by omega) p hp w hw
            simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at this
            rw [this, show m + 1 - 1 - 0 = m by omega, hP0]
          · intro j hj p hp w hw
            have := hcobs (j + 1) (by omega) p hp w hw
            simp only [List.getElem?_cons_succ] at this
            rw [this, show m + 1 - 1 - (j + 1) = m - 1 - j by omega]
    refine ⟨hseed m st mems envF hF, ?_, ⟨⟨rest, hR, ?_⟩, ?_⟩⟩
    · intro mn iname conns hm
      obtain ⟨child, cwe, cres, ctail, hc, _, hcs, _, hout, _⟩ := hchild mn iname conns hm
      exact childStepsK_of_step hc (hnofb mn iname conns hm child cwe hc) hcs hout
    · intro j hj
      have := hP' (j + 1) (by omega)
      simp only [List.getElem?_cons_succ] at this
      rw [this, show m + 1 - 1 - (j + 1) = m - 1 - j by omega]
    · intro mn iname conns hm
      obtain ⟨child, cwe, cres, ctail, hc, _, _, hct, _, hobs⟩ := hchild mn iname conns hm
      refine ⟨child, cwe, ctail, hc, ?_, hobs⟩
      rw [kidsAfter_inst kids (nx m kids) (mx m kids) body kids hnd mn iname conns hm]
      exact hct

/-! ## Instance outputs keep their seeds in the open run -/

/-- The targets of a body's assignments. -/
def assignTargets : List Stmt → List String
  | [] => []
  | .assign l _ :: rest => l :: assignTargets rest
  | _ :: rest => assignTargets rest

/-- The open fold of a body without memories changes only assignment
targets. -/
theorem evalAssigns_assignFrame (we : WEnv) (mems : MEnv)
    (children : String → Option (Module × WEnv)) :
    ∀ (body : List Stmt) (env result : Env) (z : String), linkedWF children body = true →
      evalAssigns we mems body env = some result → z ∉ assignTargets body → result z = env z
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
      simp only [assignTargets, List.mem_cons, not_or] at hz
      rw [evalAssigns_assignFrame we mems children rest _ result z hwf' h' hz.2]
      simp [hz.1]
  | .inst mn iname conns :: rest, env, result, z, hwf, h, hz => by
    have hwf' : linkedWF children rest = true := by
      simp only [linkedWF, Bool.and_eq_true] at hwf; exact hwf.2
    exact evalAssigns_assignFrame we mems children rest env result z hwf' h (by
      simpa [assignTargets] using hz)
  | .register o c rk i iv :: rest, env, result, z, hwf, h, hz =>
    evalAssigns_assignFrame we mems children rest env result z hwf h (by
      simpa [assignTargets] using hz)
  | .memory .. :: _, _, _, _, hwf, _, _ => by simp [linkedWF] at hwf

theorem assignTargets_sub_linked {children : String → Option (Module × WEnv)} :
    ∀ (body : List Stmt) (n : String), n ∈ assignTargets body → n ∈ linkedWrites children body
  | [], _, h => by cases h
  | .assign l r :: rest, n, h => by
    simp only [assignTargets, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (assignTargets_sub_linked rest n h)
  | .inst .. :: rest, n, h => List.mem_append_right _ (assignTargets_sub_linked rest n h)
  | .register .. :: rest, n, h => List.mem_append_right _ (assignTargets_sub_linked rest n h)
  | .memory .. :: rest, n, h => List.mem_append_right _ (assignTargets_sub_linked rest n h)

/-- An instance's output wire is never an assignment target. -/
theorem instOuts_not_assigned {children : String → Option (Module × WEnv)} :
    ∀ (body : List Stmt) (w : String), linkedWF children body = true →
      w ∈ bodyInstOuts children body → w ∉ assignTargets body
  | [], _, _, h, _ => by simp [bodyInstOuts] at h
  | .assign l r :: rest, w, hwf, h, hw => by
    have hwf' : (!(bodyInstOuts children rest).contains l &&
        (refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
        linkedWF children rest) = true := hwf
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hwf'
    have hrest : w ∈ bodyInstOuts children rest := by
      simpa [bodyInstOuts, stmtInstOuts] using h
    simp only [assignTargets, List.mem_cons] at hw
    rcases hw with rfl | hw
    · have := hwf'.1.1
      simp [hrest] at this
    · exact instOuts_not_assigned rest w hwf'.2 hrest hw
  | .inst mn iname conns :: rest, w, hwf, h, hw => by
    have hwf2 := hwf
    simp only [linkedWF, Bool.and_eq_true] at hwf2
    have hrestwf := hwf2.2
    have hw' : w ∈ assignTargets rest := by simpa [assignTargets] using hw
    simp only [bodyInstOuts, List.mem_append] at h
    rcases h with h | h
    · cases hc : children mn with
      | none => simp [stmtInstOuts, hc] at h
      | some cp =>
        obtain ⟨child, cwe⟩ := cp
        simp only [stmtInstOuts, hc] at h
        have hm := hwf2.1
        rw [hc] at hm
        simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hm
        have := hm.1.1 w h
        have hlw := assignTargets_sub_linked (children := children) rest w hw'
        simp [hlw] at this
    · exact instOuts_not_assigned rest w hrestwf h hw'
  | .register .. :: rest, w, hwf, h, hw =>
    instOuts_not_assigned rest w hwf (by simpa [bodyInstOuts, stmtInstOuts] using h)
      (by simpa [assignTargets] using hw)
  | .memory .. :: _, _, hwf, _, _ => by simp [linkedWF] at hwf

/-- The open run's seeding relation from the same seed: instance outputs
keep their seeds. -/
theorem seed_seedOuts {we : WEnv} {children : String → Option (Module × WEnv)} {mems : MEnv}
    {body : List Stmt} {env envF : Env} (hwf : linkedWF children body = true)
    (h : evalAssigns we mems body env = some envF) :
    env = seedOuts children body envF env := by
  funext n
  unfold seedOuts
  split
  · rename_i hc
    have hn : n ∈ bodyInstOuts children body := by simpa using hc
    exact (evalAssigns_assignFrame we mems children body env envF n hwf h
      (instOuts_not_assigned body n hwf hn)).symm
  · rfl

end Tools.ShippingHierState
