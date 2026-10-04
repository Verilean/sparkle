import Tools.ShippingMachineLinked
import Tools.ShippingMachineInst
import Tools.ShippingMachineAuto

/-! # Composing a machine with its children

The machine theorems are stated in the OPEN semantics: an instance output is
an input of the transition, seeded by the caller. `runModuleH_of_open`
(ShippingMachineLinked) turns an open run into the LINKED run (instances
evaluated by their children) when the seeding is the children's own output.
This file removes the self-reference from that hypothesis: a seeding that
agrees with the caller's seeding off the instance outputs is automatically a
fixed point (no assignment writes an instance output), so what remains is
that every child, fed with the run's values on its argument wires, computes
the value seeded on its output wire. -/
namespace Tools.ShippingMachineCompose
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf writesOf stmtWrites)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked

/-- Under the linked order no assignment writes an instance output. -/
theorem instOuts_not_written {children : String → Option (Module × WEnv)} :
    ∀ (body : List Stmt) (n : String), linkedWF children body = true →
      n ∈ bodyInstOuts children body → n ∉ writesOf body
  | [], _, _, h => by simp [bodyInstOuts] at h
  | .assign l r :: rest, n, hwf, h => by
    have hwf' : (!(bodyInstOuts children rest).contains l &&
        (refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
        linkedWF children rest) = true := hwf
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hwf'
    obtain ⟨⟨hl, _⟩, hrest⟩ := hwf'
    have hl' : l ∉ bodyInstOuts children rest := by simpa using hl
    have h' : n ∈ bodyInstOuts children rest := by
      simpa [bodyInstOuts, stmtInstOuts] using h
    simp only [writesOf, List.flatMap_cons, stmtWrites, List.mem_append, List.mem_singleton,
      not_or]
    refine ⟨fun he => ?_, instOuts_not_written rest n hrest h'⟩
    subst he
    exact hl' h'
  | .inst mn iname conns :: rest, n, hwf, h => by
    have hwf' : linkedWF children rest = true := by
      simp only [linkedWF, Bool.and_eq_true] at hwf; exact hwf.2
    have hw : n ∉ writesOf rest := by
      simp only [bodyInstOuts, List.mem_append] at h
      rcases h with h | h
      · -- an output of this instance: never written afterwards
        simp only [stmtInstOuts] at h
        cases hc : children mn with
        | none => rw [hc] at h; cases h
        | some cc =>
          obtain ⟨child, cwe⟩ := cc
          rw [hc] at h
          simp only [linkedWF, hc, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hwf
          have hnl : n ∉ linkedWrites children rest := by simpa using hwf.1.1.1 n h
          exact fun hn => hnl (writes_sub_linked rest n hn hwf')
      · exact instOuts_not_written rest n hwf' h
    simpa [writesOf, stmtWrites] using hw
  | .register o c rk i iv :: rest, n, hwf, h => by
    have h' : n ∈ bodyInstOuts children rest := by
      simpa [bodyInstOuts, stmtInstOuts] using h
    have := instOuts_not_written rest n hwf h'
    simpa [writesOf, stmtWrites] using this
  | .memory .. :: _, _, hwf, _ => by simp [linkedWF] at hwf

/-- **The linked run from the caller's seeding**, given an open run from a
seeding that differs from it only on instance outputs, and children that
compute the open run's values there. -/
theorem runModuleH_of_seeded (we : WEnv) (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed seed' : Nat → (String → Nat) → Env)
    (hwf : linkedWF children body = true)
    (hoff : ∀ t st n, n ∉ bodyInstOuts children body → seed' t st n = seed t st n)
    (hch : ∀ t st mems envF, evalAssigns we mems body (seed' t st) = some envF →
      ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
        ChildComputes we children mems envF mn conns) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModule we body seed' k st mems = some envs →
      runModuleH we children body seed k st mems = some envs := by
  apply runModuleH_of_open we children body seed seed' hwf
  intro t st mems envF hF
  refine ⟨?_, hch t st mems envF hF⟩
  funext n
  unfold seedOuts
  split
  · rename_i hn
    have hn' : n ∈ bodyInstOuts children body := by simpa using hn
    exact (evalAssigns_frame we mems children body _ envF n hwf hF
      (instOuts_not_written body n hwf hn')).symm
  · rename_i hn
    exact hoff t st n (by simpa using hn)

/-- **The linked run along the open run.** As `runModuleH_of_seeded`, but the
children need only compute at the environments the open run visits — the
cycles of the run, not every register state. -/
theorem runModuleH_of_run (we : WEnv) (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed seed' : Nat → (String → Nat) → Env)
    (hwf : linkedWF children body = true)
    (hoff : ∀ t st n, n ∉ bodyInstOuts children body → seed' t st n = seed t st n) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModule we body seed' k st mems = some envs →
      (∀ j (hj : j < envs.length) (mems' : MEnv) mn iname conns, Stmt.inst mn iname conns ∈ body →
        ChildComputes we children mems' (envs[j]'hj) mn conns) →
      runModuleH we children body seed k st mems = some envs
  | 0, _, _, envs, h, _ => h
  | k + 1, st, mems, envs, h, hch => by
    have h' : (stepModule we body (seed' k st) mems).bind (fun r =>
        (runModule we body seed' k (applyNexts st r.2.1) r.2.2).bind
          (fun rest => some (r.1 :: rest))) = some envs := h
    cases hS : stepModule we body (seed' k st) mems with
    | none => rw [hS] at h'; cases h'
    | some r =>
      obtain ⟨envF, nexts, mems'⟩ := r
      rw [hS] at h'
      simp only [Option.bind_some] at h'
      cases hR : runModule we body seed' k (applyNexts st nexts) mems' with
      | none => rw [hR] at h'; cases h'
      | some rest =>
        rw [hR] at h'
        simp only [Option.bind_some, Option.some.injEq] at h'
        subst h'
        have hF : evalAssigns we mems body (seed' k st) = some envF := by
          unfold stepModule at hS
          cases hE : evalAssigns we mems body (seed' k st) with
          | none => rw [hE] at hS; cases hS
          | some e =>
            rw [hE] at hS
            simp only [Option.bind_some, bind, Option.bind_eq_bind] at hS
            cases hN : regNexts we mems body e with
            | none => rw [hN] at hS; cases hS
            | some ns =>
              rw [hN] at hS
              cases hM : memNexts we body mems e with
              | none => rw [hM] at hS; simp at hS
              | some ms =>
                rw [hM] at hS
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hS
                rw [hS.1]
        have hseed : seed' k st = seedOuts children body envF (seed k st) := by
          funext n
          unfold seedOuts
          split
          · rename_i hn
            exact (evalAssigns_frame we mems children body _ envF n hwf hF
              (instOuts_not_written body n hwf (by simpa using hn))).symm
          · rename_i hn
            exact hoff k st n (by simpa using hn)
        have hlinked : evalAssignsH we children mems body (seed k st) = some envF := by
          apply open_linked we children mems envF body (seed k st) hwf _
            (fun mn iname conns hm => hch 0 (by simp) mems mn iname conns hm)
          rw [← hseed]; exact hF
        have hstep : stepModuleH we children body (seed k st) mems =
            some (envF, nexts, mems') := by
          unfold stepModuleH
          rw [hlinked]
          unfold stepModule at hS
          rw [hF] at hS
          exact hS
        have hrest := runModuleH_of_run we children body seed seed' hwf hoff k _ _ rest hR
          (fun j hj mems'' mn iname conns hm =>
            hch (j + 1) (by simp; omega) mems'' mn iname conns hm)
        show (stepModuleH we children body (seed k st) mems).bind (fun r =>
            (runModuleH we children body seed k (applyNexts st r.2.1) r.2.2).bind
              (fun rest => some (r.1 :: rest))) = some (envF :: rest)
        rw [hstep]
        simp only [Option.bind_some]
        rw [hrest]
        rfl

/-- The environments of an open run are elaborations of the cycles' seeds. -/
theorem runModule_envs (we : WEnv) (body : List Stmt) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModule we body seed k st mems = some envs →
      envs.length = k ∧ ∀ j (hj : j < envs.length), ∃ st' mems',
        evalAssigns we mems' body (seed (k - 1 - j) st') = some (envs[j]'hj)
  | 0, _, _, envs, h => by
    simp only [runModule, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun j hj => absurd hj (by simp)⟩
  | k + 1, st, mems, envs, h => by
    have h' : (stepModule we body (seed k st) mems).bind (fun r =>
        (runModule we body seed k (applyNexts st r.2.1) r.2.2).bind
          (fun rest => some (r.1 :: rest))) = some envs := h
    cases hS : stepModule we body (seed k st) mems with
    | none => rw [hS] at h'; cases h'
    | some r =>
      obtain ⟨envF, nexts, mems'⟩ := r
      rw [hS] at h'
      simp only [Option.bind_some] at h'
      cases hR : runModule we body seed k (applyNexts st nexts) mems' with
      | none => rw [hR] at h'; cases h'
      | some rest =>
        rw [hR] at h'
        simp only [Option.bind_some, Option.some.injEq] at h'
        subst h'
        obtain ⟨hlen, hrest⟩ := runModule_envs we body seed k _ _ rest hR
        refine ⟨by simp [hlen], fun j hj => ?_⟩
        cases j with
        | zero =>
          refine ⟨st, mems, ?_⟩
          unfold stepModule at hS
          cases hE : evalAssigns we mems body (seed k st) with
          | none => rw [hE] at hS; cases hS
          | some e =>
            rw [hE] at hS
            simp only [Option.bind_some, bind, Option.bind_eq_bind] at hS
            cases hN : regNexts we mems body e with
            | none => rw [hN] at hS; cases hS
            | some ns =>
              rw [hN] at hS
              cases hM : memNexts we body mems e with
              | none => rw [hM] at hS; simp at hS
              | some ms =>
                rw [hM] at hS
                simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hS
                show evalAssigns we mems body (seed (k + 1 - 1 - 0) st) = some envF
                rw [show k + 1 - 1 - 0 = k by omega, hE, hS.1]
        | succ j =>
          obtain ⟨st', mems'', h⟩ := hrest j (by simp at hj; omega)
          refine ⟨st', mems'', ?_⟩
          have : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
          rw [this]; exact h

theorem bodyInstOuts_of_mem {children : String → Option (Module × WEnv)} :
    ∀ {body : List Stmt} {st : Stmt} {w : String}, st ∈ body → w ∈ stmtInstOuts children st →
      w ∈ bodyInstOuts children body
  | [], _, _, h, _ => by cases h
  | st' :: rest, st, w, h, hw => by
    simp only [bodyInstOuts, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl hw
    · exact Or.inr (bodyInstOuts_of_mem h hw)

/-! ## A call's child computes its value -/

/-- The argument ports of a child module (its inputs but clock and reset). -/
def argPorts (mc : Module) : List Port :=
  mc.inputs.filter fun p => p.name != "clk" && p.name != "rst"

/-- What a combinational child computes: its single output carries `f` of
its argument ports' values, for every environment whose argument values
satisfy `P` (the child's admissible inputs). This is the form a child's own
theorem gives at one cycle. -/
def ChildFn (mc : Module) (P : List Nat → Prop) (f : List Nat → Nat) : Prop :=
  ∃ outP, mc.outputs = [outP] ∧ ∀ (mems : MEnv) (env : Env), env "rst" = 0 →
    P ((argPorts mc).map fun p => env p.name) →
    ∃ cres, evalAssigns (Sparkle.IR.RegDedup.declWidth mc) mems mc.body env = some cres ∧
      cres outP.name = f ((argPorts mc).map fun p => env p.name)


/-- The connection environment of a zipped port list reads, at each port,
its wire. -/
theorem connEnv_zip (env : Env) (rest : List (String × Expr)) :
    ∀ (ps : List Port) (ws : List String), (ps.map (·.name)).Nodup → ps.length = ws.length →
      ps.map (fun p => connEnv ((ps.zip ws).map (fun (p, w) => ((p : Port).name, Expr.ref w)) ++ rest)
        env p.name) = ws.map env
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | p :: ps, w :: ws, hnd, hlen => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.zip_cons_cons, List.map_cons, List.cons_append, List.map_cons]
    congr 1
    · simp [connEnv, List.lookup]
    · rw [← connEnv_zip env rest ps ws hnd.2 (by simpa using hlen)]
      apply List.map_congr_left
      intro q hq
      have hne : (q.name == p.name) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun he => hnd.1 ⟨q, hq, he⟩
      simp only [connEnv, List.lookup, hne]

/-- The lookup of a name absent from the zipped ports goes to the rest. -/
theorem lookup_zip_rest (rest : List (String × Expr)) (nm : String) :
    ∀ (ps : List Port) (ws : List String), nm ∉ ps.map (·.name) →
      (((ps.zip ws).map (fun (p, w) => ((p : Port).name, Expr.ref w))) ++ rest).lookup nm =
        rest.lookup nm
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: ps, w :: ws, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (nm == p.name) = false := beq_eq_false_iff_ne.mpr h.1
    simp only [List.zip_cons_cons, List.map_cons, List.cons_append, List.lookup, hne]
    exact lookup_zip_rest rest nm ps ws h.2

/-- **A call's child computes the value on its output wire**, when the child
computes `f` and the run's values satisfy the call's equation. -/
theorem childComputes_of_call {we : WEnv} {ms : List Module} {mems : MEnv}
    {envF : Env} {nIn kI n : Nat} {portNames : List String} {k : Nat} {args : List Nat}
    {nm : String} {mc : Module} {mn iname : String} {conns : List (String × Expr)}
    {P : List Nat → Prop} {f : List Nat → Nat}
    (hmc : Sparkle.IR.Machine.moduleByName ms nm = some mc)
    (hcall : Tools.ShippingMachineInst.CallStmt nIn kI n portNames k args mc (.inst mn iname conns))
    (hfn : ChildFn mc P f)
    (hval : ∀ outW argWs, portNames[nIn + k]? = some outW →
      args.mapM (fun j => portNames[nIn + kI + n + j]?) = some argWs →
      P (argWs.map envF) ∧ envF outW = f (argWs.map envF)) :
    ChildComputes we (childMap ms) mems envF mn conns := by
  obtain ⟨outW, argWs, outP, iname', hout, hargs, houts, _, hlen, hnd, hoa, hon, hrst, hst⟩ :=
    hcall
  obtain ⟨outP', houts', hf⟩ := hfn
  rw [houts] at houts'
  cases houts'
  cases hst
  have hA : (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst") = argPorts mc := rfl
  rw [hA] at hlen hnd hon ⊢
  have hname := Tools.ShippingMachineInst.moduleByName_name hmc
  have hmc' : Sparkle.IR.Machine.moduleByName ms mc.name = some mc := by
    rw [hname]; exact hmc
  obtain ⟨hP, heq⟩ := hval outW argWs hout hargs
  refine ⟨mc, Sparkle.IR.RegDedup.declWidth mc, by simp [childMap, hmc'], ?_⟩
  intro env1 hagree
  -- the instance's only output wire is `outW`
  have hlo : (((argPorts mc).zip argWs).map (fun (p, w) => ((p : Port).name, Expr.ref w)) ++
      [(outP.name, Expr.ref outW)]).lookup outP.name = some (.ref outW) := by
    rw [lookup_zip_rest _ _ _ _ hon]; simp [List.lookup]
  have hio : instOutWires mc.outputs
      (((argPorts mc).zip argWs).map (fun (p, w) => ((p : Port).name, Expr.ref w)) ++
        [(outP.name, Expr.ref outW)]) = [outW] := by
    rw [houts]; simp [instOutWires, hlo]
  -- the argument wires agree with the run
  have hargsEq : argWs.map env1 = argWs.map envF := by
    apply List.map_congr_left
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hi' : i < (argPorts mc).length := by omega
    have hmem : ((argPorts mc)[i].name, Expr.ref argWs[i]) ∈
        ((argPorts mc).zip argWs).map (fun (p, w) => ((p : Port).name, Expr.ref w)) ++
          [(outP.name, Expr.ref outW)] := by
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨((argPorts mc)[i], argWs[i]), ?_, rfl⟩
      have : ((argPorts mc).zip argWs)[i]'(by simp; omega) = ((argPorts mc)[i], argWs[i]) := by
        simp [List.getElem_zip]
      rw [← this]; exact List.getElem_mem _
    apply hagree _ hmem argWs[i] rfl
    rw [hio]; simp only [List.mem_singleton]; exact fun he => hoa (he ▸ hw)
  have hvals : (argPorts mc).map (fun p => connEnv
      (((argPorts mc).zip argWs).map (fun (p, w) => ((p : Port).name, Expr.ref w)) ++
        [(outP.name, Expr.ref outW)]) env1 p.name) = argWs.map envF := by
    rw [connEnv_zip env1 _ _ _ hnd hlen, hargsEq]
  have hrst0 : connEnv
      (((argPorts mc).zip argWs).map (fun (p, w) => ((p : Port).name, Expr.ref w)) ++
        [(outP.name, Expr.ref outW)]) env1 "rst" = 0 := by
    have hnr : "rst" ∉ (argPorts mc).map (·.name) := by
      intro h
      obtain ⟨p, hp, he⟩ := List.mem_map.mp h
      have := (List.mem_filter.mp hp).2
      simp [he] at this
    unfold connEnv
    rw [lookup_zip_rest _ _ _ _ hnr]
    have hne : ("rst" == outP.name) = false := beq_eq_false_iff_ne.mpr (Ne.symm hrst)
    simp [List.lookup, hne]
  obtain ⟨cres, hev, hcres⟩ := hf mems _ hrst0 (by rw [hvals]; exact hP)
  refine ⟨cres, hev, ?_⟩
  intro p hp w hw
  rw [houts] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  rw [hlo] at hw
  cases hw
  rw [hcres, hvals, heq]

/-! ## The calls' ports carry the calls' values -/

section Ports
open Lean Sparkle.Compiler.Elab Tools.ShippingMachineEntry Tools.ShippingMixedEntrySoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMachineClose

/-- **Admissibility at the calls' ports.** An environment admissible for
the declaration's binders, changed only at the calls' ports — which then
hold the calls' values — is admissible for the binders with the calls. -/
theorem sourceInputs_extend {declName : Name} {bsD bsI : List (Name × MixedGateBinder)}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} (nd : ids.Nodup)
    (hlen : bsD.length + bsI.length ≤ ids.length) (hI : ∀ b ∈ bsI, b.2 ≠ .domain)
    (hnames : ((machPorts declName ids cache (bsD ++ bsI)).map (·.name)).Nodup)
    {bools : Nat → Bool} {bits : (j : Nat) → (n : Nat) → BitVec n} {env env' : Env}
    (h : SourceInputs declName bsD ids cache bools bits env)
    (hoff : ∀ x, x ∉ ((machPorts declName ids cache (bsD ++ bsI)).drop
      (machPorts declName ids cache bsD).length).map (·.name) → env' x = env x)
    (hon : ∀ k p b, ((machPorts declName ids cache (bsD ++ bsI)).drop
        (machPorts declName ids cache bsD).length)[k]? = some p → bsI[k]? = some b →
      env' p.name = posEnc bools bits (bsD.length + k) b.2) :
    SourceInputs declName (bsD ++ bsI) ids cache bools bits env' := by
  let a := start (entryCompilerState false cache) declName.toString
  let n := bsD.length
  let zb : FVarId → Bool := fun _ => false
  let zv : (id : FVarId) → (n : Nat) → BitVec n := fun _ n => 0#n
  have hz : (bsD ++ bsI).zip ids = bsD.zip (ids.take n) ++ bsI.zip (ids.drop n) := by
    conv => lhs; rw [← List.take_append_drop n ids]
    exact List.zip_append (by simp [n]; omega)
  have hzD : bsD.zip ids = bsD.zip (ids.take n) := zip_take_length _ _
  let PD := inputPorts zb zv (bsD.zip (ids.take n)) a
  let PI := inputPorts zb zv (bsI.zip (ids.drop n)) (prepare zb zv (bsD.zip (ids.take n)) a)
  have hall : machPorts declName ids cache (bsD ++ bsI) = PD ++ PI := by
    unfold machPorts; rw [hz, inputPorts_append]
  have hD : machPorts declName ids cache bsD = PD := by
    unfold machPorts; rw [hzD]
  have hins : (machPorts declName ids cache (bsD ++ bsI)).drop
      (machPorts declName ids cache bsD).length = PI := by
    rw [hall, hD, List.drop_left]
  rw [hins] at hoff hon
  rw [hall, List.map_append] at hnames
  have disj : ∀ p ∈ PD, p.name ∉ PI.map (·.name) := by
    intro p hp hq
    exact (List.nodup_append.mp hnames).2.2 p.name (List.mem_map_of_mem hp) p.name hq rfl
  unfold SourceInputs at h ⊢
  rw [hz, admissible_append]
  rw [hzD] at h
  refine ⟨?_, ?_⟩
  · refine admissible_env_congr _ _ (fun p hp => hoff p.name (disj p ?_)) h
    rwa [show inputPorts (boolValues ids bools) (bitValues ids bits) (bsD.zip (ids.take n)) a = PD
      from inputPorts_congr _ _ _ rfl] at hp
  · have noDom : ∀ b ∈ bsI.zip (ids.drop n), b.1.2 ≠ .domain :=
      fun b hb => hI b.1 (List.of_mem_zip hb).1
    apply admissible_of_ports _ _ noDom
    rw [show inputPorts (boolValues ids bools) (bitValues ids bits) (bsI.zip (ids.drop n))
        (prepare (boolValues ids bools) (bitValues ids bits) (bsD.zip (ids.take n)) a) = PI from
      inputPorts_congr _ _ _ (prepare_state_congr _ _ _ rfl)]
    have piLen : PI.length = bsI.length := by
      rw [(inputPorts_types (bools := zb) (bits := zv) _ _ noDom).length_eq, List.length_zip,
        List.length_drop]
      omega
    apply Zip₂.of_get (by rw [piLen, List.length_zip, List.length_drop]; omega)
    intro i p b hp hb
    obtain ⟨hb1, hb2⟩ := List.getElem?_zip_eq_some.mp hb
    rw [hon i p b.1 hp hb1]
    have hidx : ids.idxOf b.2 = n + i := by
      rw [List.getElem?_drop] at hb2
      have hlt : n + i < ids.length := (List.getElem?_eq_some_iff.mp hb2).1
      have hg : ids[n + i]! = b.2 := by simp [List.getElem!_eq_getElem?_getD, hb2]
      rw [← hg]
      exact index_fresh ids nd (n + i) hlt
    obtain ⟨⟨name, kind⟩, id⟩ := b
    cases kind <;> simp [binderEnc, posEnc, boolValues, bitValues, hidx, n] at hidx ⊢

/-- One port per hardware binder. -/
theorem inputPorts_length {bools bits} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      (inputPorts bools bits L a).length = (L.filter (fun b => b.1.2 != .domain)).length
  | [], _ => rfl
  | ((name, .domain), id) :: rest, a => by
    simp only [inputPorts, List.filter_cons]
    exact inputPorts_length rest _
  | ((name, .bool), id) :: rest, a => by
    simp only [inputPorts, List.filter_cons, List.length_cons]
    simp [inputPorts_length rest]
  | ((name, .bits n), id) :: rest, a => by
    simp only [inputPorts, List.filter_cons, List.length_cons]
    simp [inputPorts_length rest]

theorem filter_zip_length (L : List (Name × MixedGateBinder)) (ids : List FVarId)
    (h : L.length ≤ ids.length) :
    ((L.zip ids).filter (fun b => b.1.2 != .domain)).length =
      (L.filter (fun b => b.2 != .domain)).length := by
  induction L generalizing ids with
  | nil => rfl
  | cons b rest ih =>
    cases ids with
    | nil => simp at h
    | cons id ids =>
      simp only [List.zip_cons_cons, List.filter_cons]
      have := ih ids (by simp at h; omega)
      split <;> simp_all

theorem machPorts_length {declName : Name} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} (L : List (Name × MixedGateBinder))
    (h : L.length ≤ ids.length) :
    (machPorts declName ids cache L).length = (L.filter (fun b => b.2 != .domain)).length := by
  unfold machPorts
  rw [inputPorts_length, filter_zip_length L ids h]

/-- The ports of a binder list with more binders after it. -/
theorem machPorts_append {declName : Name} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} (L1 L2 : List (Name × MixedGateBinder))
    (h : L1.length + L2.length ≤ ids.length) :
    ∃ rest, machPorts declName ids cache (L1 ++ L2) = machPorts declName ids cache L1 ++ rest := by
  have hz : (L1 ++ L2).zip ids = L1.zip (ids.take L1.length) ++ L2.zip (ids.drop L1.length) := by
    conv => lhs; rw [← List.take_append_drop L1.length ids]
    exact List.zip_append (by simp; omega)
  unfold machPorts
  rw [hz, inputPorts_append, ← zip_take_length]
  exact ⟨_, rfl⟩

end Ports

/-- The output wire of a call's instance is an instance output of the body. -/
theorem callStmt_out {ms : List Module} {body : List Stmt} {nIn kI n : Nat}
    {portNames : List String} {k : Nat} {args : List Nat} {mc : Module} {st : Stmt}
    {outW : String} (hst : st ∈ body)
    (hcall : Tools.ShippingMachineInst.CallStmt nIn kI n portNames k args mc st)
    (hmc : Sparkle.IR.Machine.moduleByName ms mc.name = some mc)
    (hout : portNames[nIn + k]? = some outW) :
    outW ∈ bodyInstOuts (childMap ms) body := by
  obtain ⟨outW', argWs, outP, iname, hout', _, houts, _, _, _, _, hon, _, rfl⟩ := hcall
  rw [hout] at hout'
  cases hout'
  apply bodyInstOuts_of_mem hst
  have hA : (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst") = argPorts mc := rfl
  rw [hA] at hon ⊢
  have hlo : (((argPorts mc).zip argWs).map (fun (p, w) => ((p : Port).name, Expr.ref w)) ++
      [(outP.name, Expr.ref outW)]).lookup outP.name = some (.ref outW) := by
    rw [lookup_zip_rest _ _ _ _ hon]; simp [List.lookup]
  simp only [stmtInstOuts, childMap, hmc, Option.map_some, houts, instOutWires,
    List.filterMap_cons, List.filterMap_nil, hlo]
  simp

theorem idxOf_nodup {l : List String} (nd : l.Nodup) :
    ∀ i (h : i < l.length), l.idxOf (l[i]'h) = i := by
  induction l with
  | nil => intro i h; simp at h
  | cons a rest ih =>
    intro i h
    obtain ⟨ha, nd'⟩ := List.nodup_cons.mp nd
    cases i with
    | zero => simp
    | succ i =>
      have hne : (a == rest[i]'(by simp at h; omega)) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun he => ha (he ▸ List.getElem_mem _)
      simp only [List.getElem_cons_succ, List.idxOf_cons, hne, cond_false]
      rw [ih nd' i]

/-! ## The composed theorem -/

section Linked
open Lean Sparkle.Compiler.Elab Tools.ShippingMachineEntry Tools.ShippingMixedEntrySoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMachineAuto
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine (SlotField OutField)
open Tools.ShippingEntrySoundness (weOf)

/-- **A state machine composed with its children.** From the machine
theorem of a declaration with `@[hardware_module]` calls (`MachineTraceL`,
the open-module view in which a call's output is an input), the LINKED run
of the emitted module — every instance evaluated by the module its name
resolves to in the shipped design — shows the source, seeded with the
declaration's own inputs only, provided every call's module computes some
`F k` of its arguments (`ChildFn`) and the source's call is `F k` of the
source's argument values at every cycle. -/
theorem machine_linked {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module} {dsn : Design}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (h : MachineTraceL declName d m dsn dom src ext lsrc)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (P : Nat → List Nat → Prop) (F : Nat → List Nat → Nat) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
        (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
          (fun j => (bools j).val (T - 1 - t)) (fun j n => (ext i bools bits j n).val (T - 1 - t))
          (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        -- every call's module computes `F k`
        (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
          Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
            d.shape.layout.slots.length
            ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
          Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc →
          ChildFn mc (P k) (F k)) →
        -- and the source's call is `F k` of its arguments
        (∀ k args j, (d.shape.insts.map (·.2.1))[k]? = some args → j < T →
          (∀ q ∈ args, q < d.ls.length ∧ q < (lsrc i bools bits).length) ∧
          P k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) ∧
          F k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) =
            posEnc (fun p => (bools p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
              (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)) →
        ∃ envs, runModuleH (weOf m) (childMap dsn.modules) m.body seed T st0 mems = some envs ∧
          envs.length = T ∧
          ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, trace⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T seed st0 mems hin hpass hrst hinit hchild hval
  obtain ⟨nnd, alloc, regsIn, hlets, calls, insts, link, _, _, _⟩ := wired
  -- the ports: the declaration's, the calls', then the slots' and `let`s'
  let bsD := d.bsIn.take kD
  let bsI := d.bsIn.drop kD
  let names := (machPorts declName ids cache d.shape.binders).map (·.name)
  have hbin : d.shape.binders = (bsD ++ bsI) ++ (d.slotBs ++ d.letBs) := by
    rw [List.take_append_drop, ← List.append_assoc]; exact d.binders_split
  have hlenB : (bsD ++ bsI).length + (d.slotBs ++ d.letBs).length ≤ ids.length := by
    rw [len, hbin]; simp only [List.length_append]; omega
  obtain ⟨restP, hrestP⟩ := machPorts_append (declName := declName) (cache := cache)
    (bsD ++ bsI) (d.slotBs ++ d.letBs) hlenB
  have hlenDI : bsD.length + bsI.length ≤ ids.length := by
    have := hlenB; simp only [List.length_append] at this ⊢; omega
  obtain ⟨insP, hinsP⟩ := machPorts_append (declName := declName) (cache := cache) bsD bsI hlenDI
  have hDlen : (machPorts declName ids cache bsD).length = machNIn d.shape := by
    rw [hNIn]; exact machPorts_length bsD (by omega)
  have hDIlen : (machPorts declName ids cache (bsD ++ bsI)).length =
      machNIn d.shape + d.shape.insts.length := by
    rw [machPorts_length _ (by omega), List.filter_append, List.length_append, ← hNIn,
      List.filter_eq_self.mpr (fun b hb => by simpa using hI b hb), hIlen]
  have hinsLen : insP.length = d.shape.insts.length := by
    have := congrArg List.length hinsP
    rw [List.length_append, hDIlen, hDlen] at this; omega
  have hnamesEq : names = ((machPorts declName ids cache bsD).map (·.name) ++
      insP.map (·.name)) ++ restP.map (·.name) := by
    simp only [names]
    rw [show machPorts declName ids cache d.shape.binders =
      machPorts declName ids cache ((bsD ++ bsI) ++ (d.slotBs ++ d.letBs)) by rw [← hbin],
      hrestP, hinsP, List.map_append, List.map_append]
  have hallLen : names.length =
      machNIn d.shape + d.shape.insts.length + d.shape.layout.slots.length +
        d.shape.layout.lets := by
    have hrestLen : restP.length = d.shape.layout.slots.length + d.shape.layout.lets := by
      have h1 := congrArg List.length hrestP
      rw [List.length_append, machPorts_length _ (by simp only [List.length_append] at hlenB ⊢; omega),
        machPorts_length _ (by omega : (bsD ++ bsI).length ≤ ids.length), List.filter_append,
        List.length_append,
        (List.filter_eq_self (l := d.slotBs ++ d.letBs)).mpr (fun b hb => by simpa using hSL b hb),
        List.length_append, hSlen, hLlen] at h1
      omega
    rw [hnamesEq]
    simp only [List.length_append, List.length_map, hDlen, hinsLen, hrestLen]
    omega
  -- the calls' port names
  let insNames := insP.map (·.name)
  have hinsAt : ∀ k, k < d.shape.insts.length →
      names[machNIn d.shape + k]? = insNames[k]? := by
    intro k hk
    rw [hnamesEq, List.append_assoc, List.getElem?_append_right (by simp [hDlen]),
      List.getElem?_append_left (by simp [insNames, hinsLen, hDlen]; omega)]
    simp [hDlen, insNames]
  have hnd' : ((machPorts declName ids cache (bsD ++ bsI)).map (·.name)).Nodup := by
    have := nnd
    rw [show (machPorts declName ids cache d.shape.binders).map (·.name) = names from rfl,
      hnamesEq, ← List.map_append, ← hinsP] at this
    exact (List.nodup_append.mp this).1
  have hinsNd : insNames.Nodup := by
    rw [hinsP, List.map_append] at hnd'
    exact (List.nodup_append.mp hnd').2.1
  -- the values of the calls, by cycle
  let V : Nat → Nat → Nat := fun k j =>
    posEnc (fun p => (bools p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
      (((bsI)[k]?.map (·.2)).getD .domain)
  let seed' : Nat → (String → Nat) → Env := fun t st x =>
    if x ∈ insNames then V (insNames.idxOf x) (T - 1 - t) else seed t st x
  have hoff : ∀ t st x, x ∉ insNames → seed' t st x = seed t st x := by
    intro t st x hx; simp [seed', hx]
  have hon : ∀ t st k p, insP[k]? = some p →
      seed' t st p.name = V k (T - 1 - t) := by
    intro t st k p hp
    have hmem : p.name ∈ insNames := List.mem_map_of_mem (List.mem_of_getElem? hp)
    have hidx : insNames.idxOf p.name = k := by
      have hk : k < insP.length := (List.getElem?_eq_some_iff.mp hp).1
      have : insNames[k]'(by simp [insNames]; exact hk) = p.name := by
        simp [insNames, (List.getElem?_eq_some_iff.mp hp).2]
      rw [← this]; exact idxOf_nodup hinsNd k _
    simp [seed', hmem, hidx]
  -- registers and reset are not calls' ports
  have notIns : ∀ x ∈ names.drop (names.length - d.shape.layout.lets -
      d.shape.layout.slots.length), x ∉ insNames := by
    intro x hx hxi
    have hdrop : names.drop (names.length - d.shape.layout.lets - d.shape.layout.slots.length) =
        restP.map (·.name) := by
      have hL : names.length - d.shape.layout.lets - d.shape.layout.slots.length =
          ((machPorts declName ids cache bsD).map (·.name) ++ insP.map (·.name)).length := by
        rw [hallLen]; simp [hDlen, hinsLen]
      rw [hL, hnamesEq, List.drop_left]
    rw [hdrop] at hx
    have := nnd
    rw [show (machPorts declName ids cache d.shape.binders).map (·.name) = names from rfl,
      hnamesEq] at this
    have hd := (List.nodup_append.mp this).2.2
    exact hd x (List.mem_append_right _ hxi) x hx rfl
  have rstNot : "rst" ∉ insNames := by
    intro h
    have : "rst" ∈ names := by
      rw [hnamesEq]; exact List.mem_append_left _ (List.mem_append_right _ h)
    exact Tools.ShippingRegisterSoundness.not_allocated_rst (alloc _ this)
  -- the open run from `seed'`
  have hlenIds : ids.length = d.shape.binders.length := len
  obtain ⟨envs, hrun, hlenE, hobs, hletobs⟩ := trace i bools bits T seed' st0 mems
    (by
      intro t st ht
      have hsrc := sourceInputs_extend (declName := declName) nd hlenDI hI hnd' (hin t st ht)
        (env' := seed' t st) (fun x hx => hoff t st x (by rwa [hinsP, List.drop_left' (by
          simp)] at hx))
        (fun k p b hp hb => by
          rw [hinsP, List.drop_left' (by simp)] at hp
          rw [hon t st k p hp]
          simp only [V, hb, Option.map_some, Option.getD_some]
          congr 1; simp [bsD]; omega)
      rw [show d.bsIn = bsD ++ bsI from (List.take_append_drop _ _).symm]
      exact hsrc)
    (by
      intro t st r hr
      rw [hoff t st r (notIns r (regsIn r hr))]
      exact hpass t st r hr)
    (by intro t st; rw [hoff t st _ rstNot]; exact hrst t st)
    hinit
  -- the linked run
  have hwf : linkedWF (childMap dsn.modules) m.body = true := by
    rw [← linkedOk_eq]; exact link
  have hoff' : ∀ t st n, n ∉ bodyInstOuts (childMap dsn.modules) m.body →
      seed' t st n = seed t st n := by
    intro t st n hn
    apply hoff
    intro hni
    obtain ⟨k, hk, hkn⟩ := List.getElem_of_mem hni
    have hk' : k < d.shape.insts.length := by simp [insNames, hinsLen] at hk; exact hk
    obtain ⟨args, mc, st', _, hst', hmc, hcall⟩ := calls k hk'
    exact hn (callStmt_out hst' hcall hmc (by rw [hinsAt k hk', List.getElem?_eq_getElem hk, hkn]))
  obtain ⟨_, henvs⟩ := runModule_envs (weOf m) m.body seed' T st0 mems envs hrun
  refine ⟨envs, runModuleH_of_run (weOf m) (childMap dsn.modules) m.body seed seed' hwf hoff'
    T st0 mems envs hrun ?_, hlenE, hobs⟩
  intro j hj mems' mn iname conns hmem
  obtain ⟨k, args, mc, hargs, hmc, hcall⟩ := insts mn iname conns hmem
  have hname : mc.name = mn := Tools.ShippingMachineInst.moduleByName_name hmc
  have hmc' : Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc := by
    rw [hname]; exact hmc
  have hjT : j < T := by omega
  obtain ⟨hq, hP, hF⟩ := hval k args j hargs hjT
  refine childComputes_of_call hmc hcall (hchild k args mc _ hargs hmem hcall hmc') ?_
  intro outW argWs hout hargWs
  -- the argument wires are the `let` wires of the arguments
  have hkI : k < d.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
  have hargVals : argWs.map (envs[j]'hj) =
      args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0 := by
    obtain ⟨hl, hget⟩ := Tools.ShippingMachineInst.mapM_some _ args argWs hargWs
    apply List.ext_getElem (by simp [hl])
    intro q h1 h2
    have hqa : q < args.length := by simpa using h2
    have hqw : q < argWs.length := by simpa using h1
    simp only [List.getElem_map]
    obtain ⟨w, hw, hwq⟩ := hget q hqa
    have hwq' : argWs[q] = w := by
      rw [List.getElem?_eq_getElem hqw] at hwq; exact Option.some.inj hwq
    rw [hwq']
    obtain ⟨hql, hqs⟩ := hq (args[q]'hqa) (List.getElem_mem _)
    -- `w` is `let` wire `args[q]`
    have hlw : lets[args[q]'hqa]? = some w := by
      rw [hlets, List.getElem?_drop]
      rw [← hw]
      congr 1
      rw [hallLen]; omega
    obtain ⟨g, hg⟩ : ∃ g, (lsrc i bools bits)[args[q]'hqa]? = some g :=
      ⟨_, List.getElem?_eq_getElem hqs⟩
    rw [hletobs j hj (args[q]'hqa) w g hlw hg hql, hg]
    rfl
  have hout' : outW = insNames[k]'(by simp [insNames, hinsLen]; exact hkI) := by
    rw [hinsAt k hkI, List.getElem?_eq_getElem (by simp [insNames, hinsLen]; exact hkI)] at hout
    exact (Option.some.inj hout).symm
  -- the call's wire carries the call's value: the open run leaves it as seeded
  obtain ⟨stj, memsj, hev⟩ := henvs j hj
  have hframe := evalAssigns_frame (weOf m) memsj (childMap dsn.modules) m.body _ _ outW hwf hev
    (instOuts_not_written m.body outW hwf (by
      rw [hout']
      obtain ⟨args', mc', st', _, hst', hmc'', hcall'⟩ := calls k hkI
      exact callStmt_out hst' hcall' hmc'' (by
        rw [hinsAt k hkI, List.getElem?_eq_getElem (by simp [insNames, hinsLen]; exact hkI)])))
  have hpk : insP[k]? = some (insP[k]'(by rw [hinsLen]; exact hkI)) :=
    List.getElem?_eq_getElem _
  have hseedv := hon (T - 1 - j) stj k _ hpk
  refine ⟨by rw [hargVals]; exact hP, ?_⟩
  rw [hargVals, hF, hframe, hout']
  simp only [insNames, List.getElem_map]
  rw [hseedv]
  have : T - 1 - (T - 1 - j) = j := by omega
  rw [this]

/-- `machine_linked` with the calls' equations as a premise of their own
(for every input, at every cycle): what the generated `f.machine_linked`
discharges by kernel facts about the declaration. -/
theorem machine_linked_calls {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module} {dsn : Design}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (h : MachineTraceL declName d m dsn dom src ext lsrc)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (P : Nat → List Nat → Prop) (F : Nat → List Nat → Nat)
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k args j,
      (d.shape.insts.map (·.2.1))[k]? = some args →
      (∀ q ∈ args, q < d.ls.length ∧ q < (lsrc i bools bits).length) ∧
      P k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) ∧
      F k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) =
        posEnc (fun p => (bools p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
          (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
        (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
          (fun j => (bools j).val (T - 1 - t)) (fun j n => (ext i bools bits j n).val (T - 1 - t))
          (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        -- every call's module computes `F k`
        (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
          Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
            d.shape.layout.slots.length
            ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
          Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc →
          ChildFn mc (P k) (F k)) →
        ∃ envs, runModuleH (weOf m) (childMap dsn.modules) m.body seed T st0 mems = some envs ∧
          envs.length = T ∧
          ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ :=
    machine_linked h kD hkD hI hIlen hSL hSlen hLlen hNIn P F
  exact ⟨ids, nd, len, cache, regs, rnd, rlen,
    fun i bools bits T seed st0 mems a b c e f => H i bools bits T seed st0 mems a b c e f
      (fun k args j hk _ => hcalls i bools bits k args j hk)⟩

end Linked

end Tools.ShippingMachineCompose
