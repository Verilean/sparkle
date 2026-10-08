import Tools.ShippingHierOptRun
import Tools.ShippingMachineCompose
import Tools.ShippingMachineShipsHier
import Tools.ShippingHierSVRun
import Tools.ShippingMachineDepthRun

/-! # The optimizer check over the combinational linked run

`hierRefineCheck_linked` carries the STATEFUL linked run (`runModuleTG`).
A machine whose calls are one-output combinational children
(`closeInsts`) runs in the combinational linked semantics `runModuleH`:
each instance evaluates its child on the parent's wires. The same three
steps carry it — the linked run is the open run of the extracted module
(`linked_open`), `refineCheck_transfer`, and the open run of the extracted
optimized module is a linked run of the optimized module
(`runModuleH_of_open`). The last step needs each child to compute its
outputs from its input ports alone (`readsClosed`: every statement reads
input ports or names written before it, and every output port is written),
so the child computes in the optimized module what it computed in the
original. -/
namespace Tools.ShippingHierOptRunH
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.HierCheck
open Sparkle.IR.Reorder (writesOf stmtWrites stmtReads refsOf evalExpr_congr)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen
open Tools.ShippingHierOptRun Tools.ShippingMachineLinked Tools.ShippingHierState
open Tools.ShippingSeqOptSoundness (seedIn)

/-- Every statement reads names of `S` or names written before it. -/
def readsClosed : List String → List Stmt → Bool
  | _, [] => true
  | S, st :: rest => (stmtReads st).all (fun n => S.contains n) && readsClosed (S ++ stmtWrites st) rest

/-- **A closed body's results depend only on its free names.** -/
theorem evalAssigns_local (we : WEnv) (mems : MEnv) :
    ∀ (body : List Stmt) (S : List String) (env1 env2 r1 : Env),
      Tools.ConeFold.memFree body → readsClosed S body = true →
      (∀ n ∈ S, env1 n = env2 n) →
      evalAssigns we mems body env1 = some r1 →
      ∃ r2, evalAssigns we mems body env2 = some r2 ∧ ∀ n ∈ S ++ writesOf body, r2 n = r1 n
  | [], S, env1, env2, r1, _, _, hag, h => by
    simp only [evalAssigns, Option.some.injEq] at h
    subst h
    refine ⟨env2, rfl, fun n hn => ?_⟩
    simp only [writesOf, List.flatMap_nil, List.append_nil] at hn
    exact (hag n hn).symm
  | st :: rest, S, env1, env2, r1, hmf, hcl, hag, h => by
    have hmf' : Tools.ConeFold.memFree rest := by
      cases st <;> simp_all [Tools.ConeFold.memFree]
    simp only [readsClosed, Bool.and_eq_true, List.all_eq_true] at hcl
    obtain ⟨hreads, hrest⟩ := hcl
    cases st with
    | assign l e =>
      simp only [evalAssigns] at h
      cases hv : evalExpr we env1 e with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        have hv2 : evalExpr we env2 e = some v := by
          rw [← hv]; apply evalExpr_congr
          intro n hn
          exact (hag n (by simpa [List.contains_eq_mem] using hreads n hn)).symm
        obtain ⟨r2, hr2, hagr⟩ := evalAssigns_local we mems rest (S ++ [l])
          (fun m => if m = l then v else env1 m) (fun m => if m = l then v else env2 m) r1
          hmf' (by simpa [stmtWrites] using hrest)
          (fun n hn => by
            rcases List.mem_append.mp hn with h | h
            · by_cases hnl : n = l
              · simp [hnl]
              · simp [hnl, hag n h]
            · simp at h; simp [h]) h
        refine ⟨r2, by simp [evalAssigns, hv2, hr2], fun n hn => hagr n ?_⟩
        simp only [writesOf, List.flatMap_cons, stmtWrites, List.mem_append, List.mem_singleton] at hn ⊢
        rcases hn with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    | register o c rk i iv =>
      simp only [evalAssigns] at h
      obtain ⟨r2, hr2, hagr⟩ := evalAssigns_local we mems rest S env1 env2 r1 hmf'
        (by simpa [stmtWrites] using hrest) hag h
      exact ⟨r2, by simpa [evalAssigns] using hr2,
        fun n hn => hagr n (by simpa [writesOf, stmtWrites] using hn)⟩
    | inst mn iname conns =>
      simp only [evalAssigns] at h
      obtain ⟨r2, hr2, hagr⟩ := evalAssigns_local we mems rest S env1 env2 r1 hmf'
        (by simpa [stmtWrites] using hrest) hag h
      exact ⟨r2, by simpa [evalAssigns] using hr2,
        fun n hn => hagr n (by simpa [writesOf, stmtWrites] using hn)⟩
    | memory => simp [Tools.ConeFold.memFree] at hmf

/-- The cycle's statements in the combinational linked semantics. -/
theorem stepModuleH_some {we : WEnv} {children : String → Option (Module × WEnv)}
    {body : List Stmt} {env0 : Env} {mems : MEnv} {r : Env × List (String × Nat) × MEnv}
    (h : stepModuleH we children body env0 mems = some r) :
    ∃ envF nexts mems', evalAssignsH we children mems body env0 = some envF ∧
      regNexts we mems body envF = some nexts ∧ memNexts we body mems envF = some mems' ∧
      r = (envF, nexts, mems') := by
  unfold stepModuleH at h
  cases hE : evalAssignsH we children mems body env0 with
  | none => simp [hE] at h
  | some envF =>
    cases hN : regNexts we mems body envF with
    | none => simp [hE, hN] at h
    | some nexts =>
      cases hM : memNexts we body mems envF with
      | none => simp [hE, hN, hM] at h
      | some mems' =>
        simp only [hE, hN, hM, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
        exact ⟨envF, nexts, mems', rfl, hN, hM, h.symm⟩

theorem linked_writes_drives {children : String → Option (Module × WEnv)} {n : String}
    {body : List Stmt} (h : n ∈ linkedWrites children body) (hO : n ∉ bodyInstOuts children body) :
    n ∈ drivesOf body := linkedWrites_drives body h hO

/-- **The combinational linked run is an open run of the extracted module.** -/
theorem linked_open_runH (W : WEnv) (children : String → Option (Module × WEnv)) (m : Module)
    (insX outsX : List Port) (ins : Nat → String → Nat) (E : Nat → Env)
    (hwf : linkedWF children m.body = true)
    (hOut : ∀ w ∈ bodyInstOuts children m.body, w ∈ insX.map (·.name))
    (hXin : ∀ n ∈ insX.map (·.name), n ∉ m.inputs.map (·.name))
    (hXd : ∀ n ∈ insX.map (·.name), n ∉ drivesOf m.body) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModuleH W children m.body (seedIn m ins) T st mems = some envs →
      (∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j)) →
      runModule W (openBody m.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins)) T st mems = some envs
  | 0, st, mems, envs, h, _ => by simpa [runModuleH, runModule] using h
  | k + 1, st, mems, envs, h, hE => by
    simp only [runModuleH] at h
    cases hS : stepModuleH W children m.body (seedIn m ins k st) mems with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, nexts, mems', hF, hN, hM, rfl⟩ := stepModuleH_some hS
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleH W children m.body (seedIn m ins) k (applyNexts st nexts) mems' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    have hE0 : envF = E k := by
      have := hE 0 (by simp)
      simpa using this
    have hopen := linked_open W children mems m.body _ envF hwf hF
    have hseed : seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k st =
        seedOuts children m.body envF (seedIn m ins k st) := by
      apply seed_eq hOut hXin (fun n _ => by rw [hE0])
      intro n hX hO
      rw [← hE0, linked_frame W children mems n m.body _ envF hF
        (fun hl => hXd n hX (linkedWrites_drives _ hl hO))]
      have hI := hXin n hX
      simp [seedIn, List.contains_eq_mem, hI]
    have ih := linked_open_runH W children m insX outsX ins E hwf hOut hXin hXd k
      (applyNexts st nexts) mems' rest hR (fun j hj => by
        have := hE (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [this]; congr 1; omega)
    simp only [runModule, stepModule, hseed, Tools.ShippingHierOptSoundness.evalAssigns_openBody,
      hopen, regNexts_openBody, memNexts_openBody, hN, hM, Option.bind_eq_bind, Option.bind_some]
    rw [ih]
    rfl

/-- Decidable: the child of every instance of `body` computes its outputs
from its input ports alone. -/
def kidsLocal (ms : List Module) (body : List Stmt) : Bool :=
  body.all fun st => match st with
    | .inst mn _ _ => match Sparkle.IR.Machine.moduleByName ms mn with
      | some c => Tools.ShippingMachineShipsHier.noMem c.body &&
          readsClosed (c.inputs.map (·.name)) c.body &&
          c.outputs.all (fun p => (writesOf c.body).contains p.name) &&
          c.outputs.all (fun p => !(c.inputs.map (·.name)).contains p.name)
      | none => false
    | _ => true

/-- A child with local outputs computes, on any environment agreeing on its
input ports, what it computed. -/
theorem childComputes_of_local {W : WEnv} {ms : List Module} {mems : MEnv} {envF : Env}
    {mn : String} {conns : List (String × Expr)} {child : Module}
    (hc : childMap ms mn = some (child, declWidth child))
    (hmf : Tools.ConeFold.memFree child.body)
    (hcl : readsClosed (child.inputs.map (·.name)) child.body = true)
    (hw : child.outputs.all (fun p => (writesOf child.body).contains p.name) = true)
    (hio : child.outputs.all (fun p => !(child.inputs.map (·.name)).contains p.name) = true)
    (hnofb : ∀ c ∈ inConns child.outputs conns, ∀ w, c.2 = .ref w →
      w ∉ instOutWires child.outputs conns)
    {envAt cres : Env}
    (hev : evalAssigns (declWidth child) mems child.body (connEnv conns envAt) = some cres)
    (hin : ∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ instOutWires child.outputs conns →
      envAt w = envF w)
    (hout : ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) → envF w = cres p.name) :
    ChildComputes W (childMap ms) mems envF mn conns := by
  refine ⟨child, declWidth child, hc, fun env1 hag1 => ?_⟩
  have hagree : ∀ n ∈ child.inputs.map (·.name), connEnv conns envAt n = connEnv conns env1 n := by
    intro n hn
    simp only [connEnv]
    cases hl : conns.lookup n with
    | none => rfl
    | some e =>
      cases e with
      | ref w =>
        have hcm := Tools.ShippingHierSVRun.lookup_mem hl
        have hnotOut : n ∉ child.outputs.map (·.name) := by
          intro hm
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
          have := List.all_eq_true.mp hio p hp
          simp [List.contains_eq_mem, hn] at this
        have hcin : (n, Expr.ref w) ∈ inConns child.outputs conns := by
          unfold inConns
          exact List.mem_filter.mpr ⟨hcm, by simpa [List.contains_eq_mem] using hnotOut⟩
        have hno := hnofb _ hcin w rfl
        show envAt w = env1 w
        rw [hin _ hcm w rfl hno, hag1 _ hcm w rfl hno]
      | _ => rfl
  obtain ⟨r2, hr2, hagr⟩ := evalAssigns_local _ mems child.body _ _ _ cres hmf hcl hagree hev
  refine ⟨r2, hr2, fun p hp w hlw => ?_⟩
  rw [hagr p.name (List.mem_append_right _ (by
    have := List.all_eq_true.mp hw p hp
    simpa [List.contains_eq_mem] using this)), ← hout p hp w hlw]

/-- **The open run of the extracted optimized module is a combinational
linked run of the optimized module.** -/
theorem open_linked_runH (Wm Wo : WEnv) (ms : List Module) (m o : Module) (insX outsX : List Port)
    (ins : Nat → String → Nat) (E : Nat → Env)
    (hwfM : linkedWF (childMap ms) m.body = true) (hwfO : linkedWF (childMap ms) o.body = true)
    (hOM : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → Stmt.inst mn iname conns ∈ m.body)
    (hMO : ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body → Stmt.inst mn iname conns ∈ o.body)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      childMap ms mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hloc : kidsLocal ms o.body = true)
    (hOutM : ∀ w ∈ bodyInstOuts (childMap ms) m.body, w ∈ insX.map (·.name))
    (hOutO : ∀ w ∈ bodyInstOuts (childMap ms) o.body, w ∈ insX.map (·.name))
    (hXin : ∀ n ∈ insX.map (·.name), n ∉ m.inputs.map (·.name))
    (hXdM : ∀ n ∈ insX.map (·.name), n ∉ drivesOf m.body)
    (hXdO : ∀ n ∈ insX.map (·.name), n ∉ drivesOf o.body)
    (hconn : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ c ∈ conns, ∀ w,
      c.2 = .ref w → w ∈ (m.outputs ++ outsX).map (·.name) ∨
        (w ∉ drivesOf m.body ∧ w ∉ drivesOf o.body)) :
    ∀ (T : Nat) (stM stO : String → Nat) (mems : MEnv) (envs envsO : List Env),
      runModuleH Wm (childMap ms) m.body (seedIn m ins) T stM mems = some envs →
      (∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j)) →
      runModule Wo (openBody o.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins)) T stO mems = some envsO →
      (∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        ∀ w ∈ (m.outputs ++ outsX).map (·.name), (envsO[j]'hj) w = (envs[j]'hj') w) →
      (∀ n, n ∉ drivesOf m.body → n ∉ drivesOf o.body → stM n = stO n) →
      runModuleH Wo (childMap ms) o.body (seedIn m ins) T stO mems = some envsO
  | 0, _, _, _, _, envsO, _, _, hO, _, _ => by simpa [runModuleH, runModule] using hO
  | k + 1, stM, stO, mems, envs, envsO, h, hE, hO, hag, hst => by
    have hmfM := memFree_of_linkedWF _ hwfM
    have hmfO := memFree_of_linkedWF _ hwfO
    simp only [runModuleH] at h
    cases hS : stepModuleH Wm (childMap ms) m.body (seedIn m ins k stM) mems with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF', nexts, mems', hF, hN, hM, rfl⟩ := stepModuleH_some hS
    have hMm : mems = mems' := by
      rw [Tools.ConeFold.memNexts_memFree Wm m.body hmfM mems envF'] at hM
      exact Option.some.inj hM
    subst hMm
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleH Wm (childMap ms) m.body (seedIn m ins) k (applyNexts stM nexts) mems with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    have hE0 : envF' = E k := by
      have := hE 0 (by simp)
      simpa using this
    have hframeM : ∀ n, n ∉ linkedWrites (childMap ms) m.body → envF' n = seedIn m ins k stM n :=
      fun n hn => linked_frame Wm (childMap ms) mems n m.body _ envF' hF hn
    have hseedM : seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k stM =
        seedOuts (childMap ms) m.body envF' (seedIn m ins k stM) := by
      apply seed_eq hOutM hXin (fun n _ => by rw [hE0])
      intro n hX hOm
      rw [← hE0, hframeM n (fun hl => hXdM n hX (linkedWrites_drives _ hl hOm))]
      have hI := hXin n hX
      simp [seedIn, List.contains_eq_mem, hI]
    have hopenM : evalAssigns Wm mems (openBody m.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k stM) = some envF' := by
      rw [hseedM, Tools.ShippingHierOptSoundness.evalAssigns_openBody]
      exact linked_open Wm (childMap ms) mems m.body _ envF' hwfM hF
    simp only [runModule] at hO
    cases hSO : stepModule Wo (openBody o.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k stO) mems with
    | none => simp [hSO] at hO
    | some rO =>
    obtain ⟨envFo, nextsO, memsO, hFo, hNo, hMo, rfl⟩ := Tools.ShippingHierState.stepModule_some hSO
    have hMo' : memsO = mems := by
      rw [Tools.ConeFold.memNexts_memFree Wo _ (memFree_openBody _ hmfO) mems envFo] at hMo
      exact (Option.some.inj hMo).symm
    subst hMo'
    simp only [hSO, Option.bind_eq_bind, Option.bind_some] at hO
    cases hRO : runModule Wo (openBody o.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins)) k
        (applyNexts stO nextsO) memsO with
    | none => simp [hRO] at hO
    | some restO =>
    simp only [hRO, Option.bind_some, Option.some.injEq] at hO
    subst hO
    have hund : ∀ w, w ∉ drivesOf m.body → w ∉ drivesOf o.body → envFo w = envF' w := by
      intro w hdM hdO
      rw [Tools.ConeFold.evalAssigns_frame Wo memsO (openBody o.body) _ envFo hFo
          (memFree_openBody _ hmfO) w (fun hw => hdO (writes_drives (writesOf_openBody _ hw))),
        Tools.ConeFold.evalAssigns_frame Wm memsO (openBody m.body) _ envF' hopenM
          (memFree_openBody _ hmfM) w (fun hw => hdM (writes_drives (writesOf_openBody _ hw)))]
      simp only [seedIn]
      split
      · rfl
      · exact (hst w hdM hdO).symm
    have hseedO : seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k stO =
        seedOuts (childMap ms) o.body envFo (seedIn m ins k stO) := by
      apply seed_eq hOutO hXin
      · intro n hn
        have hX := hOutO n hn
        rw [← hE0, hund n (hXdM n hX) (hXdO n hX)]
      · intro n hX hOo
        have hOm : n ∉ bodyInstOuts (childMap ms) m.body := by
          intro hm
          obtain ⟨mn, iname, conns, child, cwe, hmem, hc, hw⟩ := bodyInstOuts_mem hm
          exact hOo (instOut_body hc hw (hMO _ _ _ hmem))
        rw [← hE0, hframeM n (fun hl => hXdM n hX (linkedWrites_drives _ hl hOm))]
        have hI := hXin n hX
        simp only [seedIn, List.contains_eq_mem, hI, decide_false, Bool.false_eq_true, if_false]
        exact hst n (hXdM n hX) (hXdO n hX)
    have hopenO : evalAssigns Wo memsO o.body (seedOuts (childMap ms) o.body envFo (seedIn m ins k stO)) =
        some envFo := by
      rw [← hseedO, ← Tools.ShippingHierOptSoundness.evalAssigns_openBody]
      exact hFo
    have hcons := linked_consistent Wm (childMap ms) memsO m.body _ envF' hwfM hF
    have hagF : ∀ w ∈ (m.outputs ++ outsX).map (·.name), envFo w = envF' w := by
      intro w hw
      have := hag 0 (by simp) (by simp) w hw
      simpa using this
    have hch : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
        ChildComputes Wo (childMap ms) memsO envFo mn conns := by
      intro mn iname conns hmem
      obtain ⟨child, cwe, envAt, cres, hc, hev, hin, hout⟩ := hcons mn iname conns (hOM _ _ _ hmem)
      obtain ⟨x, hx, hxe⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hc
      injection hxe with hx1 hcwe
      subst hx1; subst hcwe
      have hl := List.all_eq_true.mp hloc _ hmem
      simp only [hx, Bool.and_eq_true] at hl
      obtain ⟨⟨⟨hnm, hcl⟩, hwr⟩, hio⟩ := hl
      refine childComputes_of_local hc (Tools.ShippingMachineShipsHier.memFree_of_noMem hnm) hcl hwr hio
        (hnofb mn iname conns hmem _ _ hc) hev ?_ ?_
      · intro c hcm w hw hnot
        rw [hin c hcm w hw hnot]
        rcases hconn mn iname conns hmem c hcm w hw with h1 | ⟨h1, h2⟩
        · exact (hagF w h1).symm
        · exact (hund w h1 h2).symm
      · intro p hp w hw
        rw [← hout p hp w hw]
        have hX := hOutO w (instOut_body hc (mem_instOutWires hp hw) hmem)
        exact hund w (hXdM w hX) (hXdO w hX)
    have hstepO := open_linked Wo (childMap ms) memsO envFo o.body (seedIn m ins k stO) hwfO hopenO hch
    have hNo' : regNexts Wo memsO o.body envFo = some nextsO := by
      rw [← regNexts_openBody]; exact hNo
    have hMo2 : memNexts Wo o.body memsO envFo = some memsO :=
      Tools.ConeFold.memNexts_memFree Wo o.body hmfO memsO envFo
    have ih := open_linked_runH Wm Wo ms m o insX outsX ins E hwfM hwfO hOM hMO hnofb hloc hOutM hOutO
      hXin hXdM hXdO hconn k (applyNexts stM nexts) (applyNexts stO nextsO) memsO rest restO hR
      (fun j hj => by
        have := hE (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [this]; congr 1; omega)
      hRO
      (fun j hj hj' w hw => by
        have := hag (j + 1) (by simp; omega) (by simp; omega) w hw
        simpa using this)
      (fun n hdM hdO => by
        rw [applyNexts_out (fun p hp he => hdM (by
              rw [← he]; exact regNexts_names Wm memsO m.body envF' nexts hmfM hN p hp)),
          applyNexts_out (fun p hp he => hdO (by
              rw [← he]; exact regNexts_names Wo memsO o.body envFo nextsO hmfO hNo' p hp))]
        exact hst n hdM hdO)
    simp only [runModuleH, stepModuleH, hstepO, hNo', hMo2, Option.bind_eq_bind, Option.bind_some]
    rw [ih]
    rfl


theorem runModuleH_length (W : WEnv) (children : String → Option (Module × WEnv)) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModuleH W children body seed T st mems = some envs → envs.length = T
  | 0, _, _, envs, h => by simp only [runModuleH, Option.some.injEq] at h; subst h; rfl
  | k + 1, st, mems, envs, h => by
    simp only [runModuleH] at h
    cases hS : stepModuleH W children body (seed k st) mems with
    | none => simp [hS] at h
    | some r =>
      obtain ⟨envF, nexts, mems', _, _, _, rfl⟩ := stepModuleH_some hS
      simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
      cases hR : runModuleH W children body seed k (applyNexts st nexts) mems' with
      | none => simp [hR] at h
      | some rest =>
        simp only [hR, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [runModuleH_length W children body seed k _ _ rest hR]

/-- **The optimizer check on an instance-bearing module, over the
combinational linked run.** If `hierRefineCheck m o` accepts the optimizer's output `o`,
every run of the stateful linked semantics of `m` (each instance stepping
its child by `KS` from its own state) has a run of `o` from the same state,
of the same length, with the same values on every output port of `m`. The
premises are about the design (the instance bodies are linked-well-formed
with distinct instance names, an instance reads none of its own outputs,
the wires the instances drive are the extracted inputs), the inputs (fit
their widths, reset low), the instance outputs and the registers' start
values (fit their widths). -/
theorem hierRefineCheck_linkedH (ms : List Module) {m o : Module}
    (hchk : Sparkle.IR.RefineCheck.hierRefineCheck m o = true)
    (hwfM : linkedWF (childMap ms) m.body = true) (hwfO : linkedWF (childMap ms) o.body = true)
    (hndM : (instNames m.body).Nodup) (hndO : (instNames o.body).Nodup)
    (hloc : kidsLocal ms o.body = true)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      (childMap ms) mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hOutM : ∀ w ∈ bodyInstOuts (childMap ms) m.body, w ∈ (openIns m).map (·.name))
    (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    (hrstIn : "rst" ∈ m.inputs.map (·.name)) (hrstZ : ∀ t, ins t "rst" = 0)
    {T : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env}
    (hrun : runModuleH (declWidth m) (childMap ms) m.body (seedIn m ins) T st mems = some envs)
    (hfitX : ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x)
    (hfitR : ∀ r ∈ Sparkle.IR.OptCheck.seqRegs (openFlat m (openIns m) (openOuts m)),
      st r.1 < 2 ^ declWidth m r.1) :
    o.inputs = m.inputs ∧ o.outputs = m.outputs ∧
    ∃ envsO, runModuleH (declWidth o) (childMap ms) o.body (seedIn m ins) T st mems = some envsO ∧
      envsO.length = envs.length ∧
      ∀ p ∈ m.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name := by
  -- the check, taken apart
  simp only [Sparkle.IR.RefineCheck.hierRefineCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hk1, hk2⟩, hconnB⟩, hXdOB⟩, hrc⟩ := hchk
  have hOM := Tools.ShippingHierOptSoundness.instsKept_mem hk1
  have hMO := Tools.ShippingHierOptSoundness.instsKept_mem hk2
  have hXin : ∀ n ∈ (openIns m).map (·.name), n ∉ m.inputs.map (·.name) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have := (List.mem_filter.mp hp).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    simpa [List.contains_eq_mem] using this.2
  have hXdM : ∀ n ∈ (openIns m).map (·.name), n ∉ drivesOf m.body := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have := (List.mem_filter.mp hp).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    simpa [List.contains_eq_mem] using this.1.2
  have hXdO : ∀ n ∈ (openIns m).map (·.name), n ∉ drivesOf o.body := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have := List.all_eq_true.mp hXdOB p hp
    simpa [List.contains_eq_mem] using this
  have hconn : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ c ∈ conns, ∀ w,
      c.2 = .ref w → w ∈ (m.outputs ++ (openOuts m)).map (·.name) ∨
        (w ∉ drivesOf m.body ∧ w ∉ drivesOf o.body) := by
    intro mn iname conns hmem c hc w hw
    have h1 := List.all_eq_true.mp hconnB _ hmem
    have h2 := List.all_eq_true.mp h1 c hc
    rw [hw] at h2
    have h3 : (((m.outputs ++ (openOuts m)).map (·.name)).contains w ||
        (!(drivesOf m.body).contains w && !(drivesOf o.body).contains w)) = true := h2
    rcases Bool.or_eq_true_iff.mp h3 with h | h
    · exact Or.inl (by simpa [List.contains_eq_mem] using h)
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      exact Or.inr ⟨by simpa [List.contains_eq_mem] using h.1, by simpa [List.contains_eq_mem] using h.2⟩
  have hOutO : ∀ w ∈ bodyInstOuts (childMap ms) o.body, w ∈ (openIns m).map (·.name) := by
    intro w hw
    obtain ⟨mn, iname, conns, child, cwe, hmem, hc, hwo⟩ := bodyInstOuts_mem hw
    exact hOutM w (instOut_body hc hwo (hOM _ _ _ hmem))
  -- the ports
  obtain ⟨hinP, houtP⟩ := Tools.ShippingRefineSoundness.refineCheck_ports hrc
  have hin : o.inputs = m.inputs := by
    simpa [openFlat] using hinP
  have hout : o.outputs = m.outputs := by
    simpa [openFlat] using houtP
  refine ⟨hin, hout, ?_⟩
  -- 1. the linked run of `m` as an open run of the extracted module
  have hlen := runModuleH_length _ (childMap ms) m.body _ T st mems envs hrun
  let E : Nat → Env := fun k => (envs[T - 1 - k]?).getD (fun _ => 0)
  have hE : ∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j) := by
    intro j hj
    simp only [E]
    rw [show T - 1 - (T - 1 - j) = j by omega]
    simp [hj]
  have hopen := linked_open_runH (declWidth m) (childMap ms) m (openIns m) (openOuts m) ins E hwfM hOutM hXin hXdM
    T st mems envs hrun hE
  -- 2. the extracted pair's check
  have hinsFit' : ∀ t x, x ∈ (openFlat m (openIns m) (openOuts m)).inputs.map (·.name) →
      insOf ((openIns m).map (·.name)) E ins t x < 2 ^ declWidth (openFlat m (openIns m) (openOuts m)) x := by
    intro t x hx
    show insOf ((openIns m).map (·.name)) E ins t x < 2 ^ declWidth m x
    simp only [insOf]
    split
    · rename_i hX
      have hX' : x ∈ (openIns m).map (·.name) := by simpa [List.contains_eq_mem] using hX
      simp only [E]
      cases hj : envs[T - 1 - t]? with
      | none => simp only [Option.getD_none]; exact Nat.two_pow_pos _
      | some e =>
        obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
        simpa using hfitX _ hlt x hX'
    · rename_i hX
      have hX' : x ∉ (openIns m).map (·.name) := by simpa [List.contains_eq_mem] using hX
      simp only [openFlat, List.map_append, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hinsFit t x hx
      · exact absurd hx hX'
  have hrstIn' : "rst" ∈ (openFlat m (openIns m) (openOuts m)).inputs.map (·.name) := by
    simp only [openFlat, List.map_append, List.mem_append]; exact Or.inl hrstIn
  have hrstZ' : ∀ t, insOf ((openIns m).map (·.name)) E ins t "rst" = 0 := by
    intro t
    have : "rst" ∉ (openIns m).map (·.name) := fun h => hXin _ h hrstIn
    simp [insOf, List.contains_eq_mem, this, hrstZ t]
  have hopen' : runModule (declWidth (openFlat m (openIns m) (openOuts m)))
      (openFlat m (openIns m) (openOuts m)).body
      (seedIn (openFlat m (openIns m) (openOuts m))
        (insOf ((openIns m).map (·.name)) E ins)) T st mems = some envs := hopen
  obtain ⟨envsO, hrunO, hlenO, houtsO⟩ := Tools.ShippingRefineSoundness.refineCheck_transfer hrc
    (insOf ((openIns m).map (·.name)) E ins) hinsFit' hrstIn' hrstZ' (stM := st) (stO := st)
    (mems := mems) (fun _ _ => rfl) hfitR hopen'
  -- 3. the open run of the extracted optimized module as a linked run of `o`
  have hlinked := open_linked_runH (declWidth m) (declWidth o) ms m o (openIns m) (openOuts m) ins E
    hwfM hwfO hOM hMO hnofb hloc hOutM hOutO hXin hXdM hXdO hconn T st st mems envs envsO hrun hE
    hrunO
    (fun j hj hj' w hw => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      exact houtsO p hp j hj hj')
    (fun _ _ _ => rfl)
  refine ⟨envsO, hlinked, hlenO, fun p hp j hj hj' => houtsO p (List.mem_append_left _ hp) j hj hj'⟩


/-- **The extracted inputs fit along a combinational linked run**: the
instance-driven ones are children's outputs, each assigned once by a
self-masked expression at most its port's width (`kidsMasked`), the others
keep their start values. -/
theorem fitX_of_runH (ms : List Module) (m : Module) (ins : Nat → String → Nat)
    (hwf : linkedWF (childMap ms) m.body = true)
    (hIW : instOutWidthsOk (childMap ms) (declWidth m) m.body = true)
    (hkm : Tools.ShippingMachineShipsHier.kidsMasked (childMap ms) m.body = true) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModuleH (declWidth m) (childMap ms) m.body (seedIn m ins) T st mems = some envs →
      (∀ x ∈ (openIns m).map (·.name), x ∉ bodyInstOuts (childMap ms) m.body →
        st x < 2 ^ declWidth m x) →
      ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
        (envs[j]'hj) x < 2 ^ declWidth m x
  | 0, _, _, envs, h, _, j, hj, _, _ => by
    simp only [runModuleH, Option.some.injEq] at h; subst h; cases hj
  | k + 1, st, mems, envs, h, hst, j, hj, x, hx => by
    have hmf := memFree_of_linkedWF _ hwf
    simp only [runModuleH] at h
    cases hS : stepModuleH (declWidth m) (childMap ms) m.body (seedIn m ins k st) mems with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, nexts, mems', hF, hN, hM, rfl⟩ := stepModuleH_some hS
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleH (declWidth m) (childMap ms) m.body (seedIn m ins) k (applyNexts st nexts) mems' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    obtain ⟨px, hpx, hpxn⟩ := List.mem_map.mp hx
    have hflt := (List.mem_filter.mp hpx).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hflt
    have hxd : x ∉ drivesOf m.body := by
      rw [← hpxn]; simpa [List.contains_eq_mem] using hflt.1.2
    have hxi : x ∉ m.inputs.map (·.name) := by
      rw [← hpxn]; simpa [List.contains_eq_mem] using hflt.2
    cases j with
    | zero =>
      show envF x < _
      by_cases hO : x ∈ bodyInstOuts (childMap ms) m.body
      · obtain ⟨mn, iname, conns, child, cwe, hmem, hc, hw⟩ := bodyInstOuts_mem hO
        obtain ⟨child', cwe', envAt, cres, hc', hev, -, hout⟩ :=
          linked_consistent (declWidth m) (childMap ms) mems m.body _ envF hwf hF mn iname conns hmem
        rw [hc] at hc'
        cases hc'
        unfold instOutWires at hw
        obtain ⟨p, hp, hpw⟩ := List.mem_filterMap.mp hw
        have hl : conns.lookup p.name = some (.ref x) := by
          revert hpw
          cases conns.lookup p.name with
          | none => intro h; cases h
          | some e => cases e <;> intro h <;> cases h <;> rfl
        rw [hout p hp x hl, instOutWidthsOk_at hIW hmem hc p hp x hl]
        -- the child's output: assigned once by a self-masked expression
        have h1 := List.all_eq_true.mp hkm _ hmem
        simp only [hc, Bool.and_eq_true] at h1
        obtain ⟨hnm, houtM⟩ := h1
        have hpm := List.all_eq_true.mp houtM p hp
        simp only [Tools.ShippingMachineShipsHier.outMasked, Bool.and_eq_true, beq_iff_eq,
          List.any_eq_true] at hpm
        obtain ⟨hcount, st', hst', hm⟩ := hpm
        cases st' with
        | assign l r =>
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
          obtain ⟨⟨hl', hsm⟩, hwd⟩ := hm
          subst hl'
          obtain ⟨env', v, hv, hfin⟩ := Tools.ShippingMachineShipsHier.evalAssigns_once cwe mems
            child.body _ cres hev (Tools.ShippingMachineShipsHier.memFree_of_noMem hnm) hst' hcount
          rw [hfin]
          exact Nat.lt_of_lt_of_le (Tools.ShippingMachineShipsHier.selfMasked_lt hsm hv)
            (Nat.pow_le_pow_right (by omega) hwd)
        | _ => simp at hm
      · rw [linked_frame (declWidth m) (childMap ms) mems x m.body _ envF hF
          (fun hl => hxd (linkedWrites_drives _ hl hO))]
        simp only [seedIn, List.contains_eq_mem, hxi, decide_false, Bool.false_eq_true, if_false]
        exact hst x hx hO
    | succ j =>
      have := fitX_of_runH ms m ins hwf hIW hkm k (applyNexts st nexts) mems' rest hR
        (fun y hy hyO => by
          obtain ⟨py, hpy, hpyn⟩ := List.mem_map.mp hy
          have hf := (List.mem_filter.mp hpy).2
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
          have hyd : y ∉ drivesOf m.body := by
            rw [← hpyn]; simpa [List.contains_eq_mem] using hf.1.2
          rw [applyNexts_out (fun p hp he => hyd (by
            rw [← he]; exact regNexts_names _ mems m.body envF nexts hmf hN p hp))]
          exact hst y hy hyO) j (by simpa using hj) x hx
      simpa using this

end Tools.ShippingHierOptRunH
