import Tools.ShippingMachineLinked
import Tools.ShippingMachineInst
import Tools.ShippingMachineEntry

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

/-! ## A call's child computes its value -/

/-- The argument ports of a child module (its inputs but clock and reset). -/
def argPorts (mc : Module) : List Port :=
  mc.inputs.filter fun p => p.name != "clk" && p.name != "rst"

/-- What a combinational child computes: its single output carries `f` of
its argument ports' values, for every environment whose argument values
satisfy `P` (the child's admissible inputs). This is the form a child's own
theorem gives at one cycle. -/
def ChildFn (mc : Module) (P : List Nat → Prop) (f : List Nat → Nat) : Prop :=
  ∃ outP, mc.outputs = [outP] ∧ ∀ (mems : MEnv) (env : Env),
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
  obtain ⟨outW, argWs, outP, iname', hout, hargs, houts, _, hlen, hnd, hoa, hon, hst⟩ := hcall
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
  obtain ⟨cres, hev, hcres⟩ := hf mems _ (by rw [hvals]; exact hP)
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

end Ports

end Tools.ShippingMachineCompose
