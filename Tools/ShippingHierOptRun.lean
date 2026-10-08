import Tools.ShippingHierOptLinked
import Tools.ShippingRefineSoundness
import Tools.ConeFoldSlices

/-! # The optimizer check on instance-bearing modules, over the stateful run

`checkedOptimize` keeps the optimizer's output `o` of an instance-bearing
module `m` only if `hierRefineCheck m o` accepts it: `refineCheck` on the
extracted pair `openFlat m insX outsX` / `openFlat o insX outsX` (instances
dropped, the wires they drive as inputs `insX`, the wires they read as
outputs `outsX`), the instance statements kept both ways, every connection
validated or untouched, and no extracted input driven by `o`.

This file carries a run of the STATEFUL linked semantics of `m`
(`runModuleTG`: every instance steps its own child with its own state) to
one of `o` with the same outputs:

1. the linked run of `m` IS the open run of `openFlat m` whose extracted
   inputs carry, at each cycle, the values the children drove
   (`linked_open_run`, from `linked_openKG`);
2. `refineCheck_transfer` carries it to the open run of `openFlat o`;
3. the open run of `openFlat o` IS a linked run of `o` with the same
   children's steps (`runModuleTG_of_open`): its instances are `m`'s, every
   wire an instance reads has the same value in both modules, and the wires
   the instances drive are the extracted inputs, which `o` does not drive. -/
namespace Tools.ShippingHierOptRun
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.HierCheck
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierStateG
open Tools.ShippingHierState Tools.ShippingHierOptLinked
open Tools.ShippingSeqOptSoundness (seedIn)

theorem regNexts_openBody (we : WEnv) (mems : MEnv) :
    ∀ (body : List Stmt) (env : Env), regNexts we mems (openBody body) env = regNexts we mems body env
  | [], _ => rfl
  | st :: rest, env => by
    have ih := regNexts_openBody we mems rest env
    unfold openBody at ih ⊢
    cases st <;> simp [List.filter_cons, regNexts, ih]

theorem memNexts_openBody (we : WEnv) :
    ∀ (body : List Stmt) (mems : MEnv) (env : Env),
      memNexts we (openBody body) mems env = memNexts we body mems env
  | [], _, _ => rfl
  | st :: rest, mems, env => by
    have ih := fun mems => memNexts_openBody we rest mems env
    unfold openBody at ih ⊢
    cases st <;> simp [List.filter_cons, memNexts, ih]

/-- The extracted inputs' stream: the children's values `E` on the extracted
inputs, the module's input stream elsewhere. -/
def insOf (xs : List String) (E : Nat → Env) (ins : Nat → String → Nat) :
    Nat → String → Nat :=
  fun t x => if xs.contains x then E t x else ins t x

/-- The extracted module's seeding is the oracle seeding of the linked run. -/
theorem seed_eq {m : Module} {insX outsX : List Port} {children : String → Option (Module × WEnv)}
    {B : List Stmt} {E : Nat → Env} {ins : Nat → String → Nat} {k : Nat} {st : String → Nat}
    {envF : Env}
    (hOut : ∀ w ∈ bodyInstOuts children B, w ∈ insX.map (·.name))
    (hXin : ∀ n ∈ insX.map (·.name), n ∉ m.inputs.map (·.name))
    (hEo : ∀ n ∈ bodyInstOuts children B, E k n = envF n)
    (hEx : ∀ n ∈ insX.map (·.name), n ∉ bodyInstOuts children B → E k n = st n) :
    seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k st =
      seedOuts children B envF (seedIn m ins k st) := by
  funext n
  simp only [seedIn, openFlat, seedOuts, insOf, List.map_append, List.contains_append]
  by_cases hO : n ∈ bodyInstOuts children B
  · have hX := hOut n hO
    have hI := hXin n hX
    simp [List.contains_eq_mem, hO, hX, hI, hEo n hO]
  · by_cases hX : n ∈ insX.map (·.name)
    · have hI := hXin n hX
      simp [List.contains_eq_mem, hO, hX, hI, hEx n hX hO]
    · simp [List.contains_eq_mem, hO, hX]

theorem drivesOf_cons {st : Stmt} {rest : List Stmt} {n : String} (h : n ∈ drivesOf rest) :
    n ∈ drivesOf (st :: rest) := by
  simp only [drivesOf, writesOf, List.flatMap_cons, List.mem_append, List.filterMap_cons] at h ⊢
  rcases h with h | h
  · exact Or.inl (Or.inr h)
  · right
    cases st <;> simp_all

/-- What the linked fold writes, outside the instances' outputs, it drives. -/
theorem linkedWrites_drives {children : String → Option (Module × WEnv)} {n : String} :
    ∀ (body : List Stmt), n ∈ linkedWrites children body → n ∉ bodyInstOuts children body →
      n ∈ drivesOf body
  | [], h, _ => by cases h
  | st :: rest, h, hO => by
    have hO' : n ∉ bodyInstOuts children rest := fun hm => hO (by
      show n ∈ stmtInstOuts children st ++ bodyInstOuts children rest
      exact List.mem_append_right _ hm)
    cases st with
    | assign l r =>
      rcases List.mem_cons.mp h with rfl | h
      · simp [drivesOf, writesOf, Sparkle.IR.Reorder.stmtWrites]
      · exact drivesOf_cons (linkedWrites_drives rest h hO')
    | _ =>
      have h' : n ∈ stmtInstOuts children _ ++ linkedWrites children rest := h
      rcases List.mem_append.mp h' with h1 | h1
      · exact absurd (List.mem_append_left _ h1) hO
      · exact drivesOf_cons (linkedWrites_drives rest h1 hO')

/-- **The linked run is an open run of the extracted module**, whose
extracted inputs carry at each cycle the values `E` of that cycle (the
linked run's environments). -/
theorem linked_open_run {σ : Type} (KS : KStep σ) (W : WEnv)
    (children : String → Option (Module × WEnv)) (m : Module) (insX outsX : List Port)
    (ins : Nat → String → Nat) (E : Nat → Env)
    (hwf : linkedWF children m.body = true)
    (hOut : ∀ w ∈ bodyInstOuts children m.body, w ∈ insX.map (·.name))
    (hXin : ∀ n ∈ insX.map (·.name), n ∉ m.inputs.map (·.name))
    (hXd : ∀ n ∈ insX.map (·.name), n ∉ drivesOf m.body) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS W children m.body (seedIn m ins) T s = some envs →
      (∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j)) →
      runModule W (openBody m.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins)) T s.st s.mems =
        some envs
  | 0, s, envs, h, _ => by simpa [runModuleTG, runModule] using h
  | k + 1, s, envs, h, hE => by
    simp only [runModuleTG] at h
    cases hS : stepModuleTG KS W children m.body (seedIn m ins k s.st) s with
    | none => simp [hS] at h
    | some r =>
      obtain ⟨envF, s'⟩ := r
      simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
      cases hR : runModuleTG KS W children m.body (seedIn m ins) k s' with
      | none => simp [hR] at h
      | some rest =>
        simp only [hR, Option.bind_some, Option.some.injEq] at h
        subst h
        unfold stepModuleTG at hS
        cases hK : evalAssignsKG KS W children s.kids s.mems m.body (seedIn m ins k s.st) s.kids with
        | none => simp [hK] at hS
        | some ek =>
          obtain ⟨envF', kids'⟩ := ek
          cases hN : regNexts W s.mems m.body envF' with
          | none => simp [hK, hN] at hS
          | some nexts =>
            cases hM : memNexts W m.body s.mems envF' with
            | none => simp [hK, hN, hM] at hS
            | some mems' =>
              simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
                Option.some.injEq, Prod.mk.injEq] at hS
              obtain ⟨rfl, rfl⟩ := hS
              have hE0 : envF' = E k := by
                have := hE 0 (by simp)
                simpa using this
              have hopen := linked_openKG KS W children s.kids s.mems m.body _ envF' s.kids kids'
                hwf hK
              have hseed : seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k s.st =
                  seedOuts children m.body envF' (seedIn m ins k s.st) := by
                apply seed_eq hOut hXin (fun n _ => by rw [hE0])
                intro n hX hO
                rw [← hE0]
                have hnl : n ∉ linkedWrites children m.body :=
                  fun hl => hXd n hX (linkedWrites_drives _ hl hO)
                rw [linked_frameKG KS W children s.kids s.mems n m.body _ envF' s.kids kids' hwf hK hnl]
                have hI := hXin n hX
                simp [seedIn, List.contains_eq_mem, hI]
              have ih := linked_open_run KS W children m insX outsX ins E hwf hOut hXin hXd k
                ⟨applyNexts s.st nexts, mems', kids'⟩ rest hR (fun j hj => by
                  have := hE (j + 1) (by simp; omega)
                  simp only [List.getElem_cons_succ] at this
                  rw [this]
                  congr 1
                  omega)
              simp only [runModule, stepModule, hseed, Tools.ShippingHierOptSoundness.evalAssigns_openBody,
                hopen, regNexts_openBody, memNexts_openBody, hN, hM, Option.bind_eq_bind,
                Option.bind_some]
              rw [ih]
              rfl

/-! ## Small facts about the bodies -/

theorem memFree_of_linkedWF {children : String → Option (Module × WEnv)} :
    ∀ (body : List Stmt), linkedWF children body = true → Tools.ConeFold.memFree body
  | [], _ => trivial
  | .assign l r :: rest, h => by
    have : (!(bodyInstOuts children rest).contains l &&
        (Sparkle.IR.Reorder.refsOf r).all (fun n => !(bodyInstOuts children rest).contains n) &&
        linkedWF children rest) = true := h
    simp only [Bool.and_eq_true] at this
    exact memFree_of_linkedWF rest this.2
  | .inst mn iname conns :: rest, h => by
    have : linkedWF children (.inst mn iname conns :: rest) = true := h
    simp only [linkedWF, Bool.and_eq_true] at this
    exact memFree_of_linkedWF rest this.2
  | .register .. :: rest, h => memFree_of_linkedWF rest h
  | .memory .. :: _, h => by simp [linkedWF] at h

theorem memFree_openBody : ∀ (body : List Stmt), Tools.ConeFold.memFree body →
    Tools.ConeFold.memFree (openBody body)
  | [], _ => trivial
  | st :: rest, h => by
    unfold openBody
    cases st <;> simp only [List.filter_cons] <;> simp_all [Tools.ConeFold.memFree] <;>
      exact memFree_openBody rest (by simpa [Tools.ConeFold.memFree] using h)

theorem writesOf_openBody {n : String} (body : List Stmt)
    (h : n ∈ writesOf (openBody body)) : n ∈ writesOf body := by
  unfold writesOf openBody at *
  obtain ⟨st, hst, hn⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨st, (List.mem_filter.mp hst).1, hn⟩

theorem writes_drives {n : String} {body : List Stmt} (h : n ∈ writesOf body) :
    n ∈ drivesOf body := List.mem_append_left _ h

/-- The registers' next values are of driven names. -/
theorem regNexts_names (we : WEnv) (mems : MEnv) :
    ∀ (body : List Stmt) (env : Env) (nexts : List (String × Nat)),
      Tools.ConeFold.memFree body → regNexts we mems body env = some nexts →
      ∀ p ∈ nexts, p.1 ∈ drivesOf body
  | [], _, nexts, _, h => by
    simp only [regNexts, Option.some.injEq] at h
    subst h; intro p hp; cases hp
  | st :: rest, env, nexts, hm, h => by
    have hm' : Tools.ConeFold.memFree rest := by
      cases st <;> simp_all [Tools.ConeFold.memFree]
    cases st with
    | register r c rk i iv =>
      simp only [regNexts] at h
      cases hv : evalExpr we env i with
      | none => simp [hv] at h
      | some v =>
        cases hr : regNexts we mems rest env with
        | none => simp [hv, hr] at h
        | some ns =>
          simp only [hv, hr, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · simp [drivesOf]
          · exact drivesOf_cons (regNexts_names we mems rest env ns hm' hr p hp)
    | assign l e =>
      simp only [regNexts] at h
      intro p hp
      exact drivesOf_cons (regNexts_names we mems rest env nexts hm' h p hp)
    | inst mn iname conns =>
      simp only [regNexts] at h
      intro p hp
      exact drivesOf_cons (regNexts_names we mems rest env nexts hm' h p hp)
    | memory => simp [Tools.ConeFold.memFree] at hm

theorem applyNexts_out {st : String → Nat} {nexts : List (String × Nat)} {n : String}
    (h : ∀ p ∈ nexts, p.1 ≠ n) : applyNexts st nexts n = st n := by
  simp only [applyNexts]
  have : nexts.find? (fun p => p.1 == n) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simpa using h p hp
  rw [this]

theorem inst_instNames {mn iname : String} {conns : List (String × Expr)} :
    ∀ {body : List Stmt}, Stmt.inst mn iname conns ∈ body → iname ∈ instNames body
  | [], h => by cases h
  | st :: rest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp [instNames]
    · have := inst_instNames h
      cases st <;> simp [instNames, this]

theorem mem_instNames {n : String} :
    ∀ {body : List Stmt}, n ∈ instNames body → ∃ mn conns, Stmt.inst mn n conns ∈ body
  | [], h => by cases h
  | st :: rest, h => by
    cases st with
    | inst mn iname conns =>
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨mn, conns, List.mem_cons_self⟩
      · obtain ⟨a, b, hm⟩ := mem_instNames h
        exact ⟨a, b, List.mem_cons_of_mem _ hm⟩
    | _ =>
      obtain ⟨a, b, hm⟩ := mem_instNames (body := rest) h
      exact ⟨a, b, List.mem_cons_of_mem _ hm⟩

theorem instOut_body {children : String → Option (Module × WEnv)} {mn iname : String}
    {conns : List (String × Expr)} {child : Module} {cwe : WEnv} {w : String}
    (hc : children mn = some (child, cwe)) (hw : w ∈ instOutWires child.outputs conns) :
    ∀ {body : List Stmt}, Stmt.inst mn iname conns ∈ body → w ∈ bodyInstOuts children body
  | [], h => by cases h
  | st :: rest, h => by
    show w ∈ stmtInstOuts children st ++ bodyInstOuts children rest
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_left _ (by simp [stmtInstOuts, hc, hw])
    · exact List.mem_append_right _ (instOut_body hc hw h)

theorem bodyInstOuts_mem {children : String → Option (Module × WEnv)} {w : String} :
    ∀ {body : List Stmt}, w ∈ bodyInstOuts children body →
      ∃ mn iname conns child cwe, Stmt.inst mn iname conns ∈ body ∧
        children mn = some (child, cwe) ∧ w ∈ instOutWires child.outputs conns
  | [], h => by cases h
  | st :: rest, h => by
    have h' : w ∈ stmtInstOuts children st ++ bodyInstOuts children rest := h
    rcases List.mem_append.mp h' with h1 | h1
    · cases st with
      | inst mn iname conns =>
        cases hc : children mn with
        | none => simp [stmtInstOuts, hc] at h1
        | some cp =>
          obtain ⟨child, cwe⟩ := cp
          simp only [stmtInstOuts, hc] at h1
          exact ⟨mn, iname, conns, child, cwe, List.mem_cons_self, hc, h1⟩
      | _ => simp [stmtInstOuts] at h1
    · obtain ⟨a, b, c, d, e, hm, hc, hw⟩ := bodyInstOuts_mem h1
      exact ⟨a, b, c, d, e, List.mem_cons_of_mem _ hm, hc, hw⟩

/-- **The open run of the extracted optimized module is a linked run of the
optimized module**, with the children stepping as in the linked run of `m`. -/
theorem open_linked_run {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) (Wm Wo : WEnv)
    (children : String → Option (Module × WEnv)) (m o : Module) (insX outsX : List Port)
    (ins : Nat → String → Nat) (E : Nat → Env)
    (hwfM : linkedWF children m.body = true) (hwfO : linkedWF children o.body = true)
    (hndM : (instNames m.body).Nodup) (hndO : (instNames o.body).Nodup)
    (hOM : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → Stmt.inst mn iname conns ∈ m.body)
    (hMO : ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body → Stmt.inst mn iname conns ∈ o.body)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hOutM : ∀ w ∈ bodyInstOuts children m.body, w ∈ insX.map (·.name))
    (hOutO : ∀ w ∈ bodyInstOuts children o.body, w ∈ insX.map (·.name))
    (hXin : ∀ n ∈ insX.map (·.name), n ∉ m.inputs.map (·.name))
    (hXdM : ∀ n ∈ insX.map (·.name), n ∉ drivesOf m.body)
    (hXdO : ∀ n ∈ insX.map (·.name), n ∉ drivesOf o.body)
    (hconn : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ c ∈ conns, ∀ w,
      c.2 = .ref w → w ∈ (m.outputs ++ outsX).map (·.name) ∨
        (w ∉ drivesOf m.body ∧ w ∉ drivesOf o.body)) :
    ∀ (T : Nat) (sM : KState σ) (stO : String → Nat) (envs envsO : List Env),
      runModuleTG KS Wm children m.body (seedIn m ins) T sM = some envs →
      (∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j)) →
      runModule Wo (openBody o.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins)) T stO sM.mems =
        some envsO →
      (∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        ∀ w ∈ (m.outputs ++ outsX).map (·.name), (envsO[j]'hj) w = (envs[j]'hj') w) →
      (∀ n, n ∉ drivesOf m.body → n ∉ drivesOf o.body → sM.st n = stO n) →
      runModuleTG KS Wo children o.body (seedIn m ins) T ⟨stO, sM.mems, sM.kids⟩ = some envsO
  | 0, sM, stO, envs, envsO, _, _, hO, _, _ => by simpa [runModuleTG, runModule] using hO
  | k + 1, sM, stO, envs, envsO, h, hE, hO, hag, hst => by
    have hmfM := memFree_of_linkedWF _ hwfM
    have hmfO := memFree_of_linkedWF _ hwfO
    -- the step of `m`
    simp only [runModuleTG] at h
    cases hS : stepModuleTG KS Wm children m.body (seedIn m ins k sM.st) sM with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, s'⟩ := r
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG KS Wm children m.body (seedIn m ins) k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    unfold stepModuleTG at hS
    cases hK : evalAssignsKG KS Wm children sM.kids sM.mems m.body (seedIn m ins k sM.st) sM.kids with
    | none => simp [hK] at hS
    | some ek =>
    obtain ⟨envF', kids'⟩ := ek
    cases hN : regNexts Wm sM.mems m.body envF' with
    | none => simp [hK, hN] at hS
    | some nexts =>
    have hM : memNexts Wm m.body sM.mems envF' = some sM.mems :=
      Tools.ConeFold.memNexts_memFree Wm m.body hmfM sM.mems envF'
    simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    have hE0 : envF' = E k := by
      have := hE 0 (by simp)
      simpa using this
    -- `m`'s cycle as the extracted module's
    have hframeM : ∀ n, n ∉ linkedWrites children m.body →
        envF' n = seedIn m ins k sM.st n := fun n hn =>
      linked_frameKG KS Wm children sM.kids sM.mems n m.body _ envF' sM.kids kids' hwfM hK hn
    have hseedM : seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k sM.st =
        seedOuts children m.body envF' (seedIn m ins k sM.st) := by
      apply seed_eq hOutM hXin (fun n _ => by rw [hE0])
      intro n hX hOm
      rw [← hE0, hframeM n (fun hl => hXdM n hX (linkedWrites_drives _ hl hOm))]
      have hI := hXin n hX
      simp [seedIn, List.contains_eq_mem, hI]
    have hopenM : evalAssigns Wm sM.mems (openBody m.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k sM.st) = some envF' := by
      rw [hseedM, Tools.ShippingHierOptSoundness.evalAssigns_openBody]
      exact linked_openKG KS Wm children sM.kids sM.mems m.body _ envF' sM.kids kids' hwfM hK
    -- the step of `o`'s extracted module
    simp only [runModule] at hO
    cases hSO : stepModule Wo (openBody o.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k stO) sM.mems with
    | none => simp [hSO] at hO
    | some rO =>
    obtain ⟨envFo, nextsO, memsO, hFo, hNo, hMo, rfl⟩ := stepModule_some hSO
    simp only [hSO, Option.bind_eq_bind, Option.bind_some] at hO
    have hMo' : memsO = sM.mems := by
      rw [Tools.ConeFold.memNexts_memFree Wo _ (memFree_openBody _ hmfO) sM.mems envFo] at hMo
      exact (Option.some.inj hMo).symm
    subst hMo'
    cases hRO : runModule Wo (openBody o.body)
        (seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins)) k
        (applyNexts stO nextsO) sM.mems with
    | none => simp [hRO] at hO
    | some restO =>
    simp only [hRO, Option.bind_some, Option.some.injEq] at hO
    subst hO
    -- undriven wires agree
    have hund : ∀ w, w ∉ drivesOf m.body → w ∉ drivesOf o.body → envFo w = envF' w := by
      intro w hdM hdO
      rw [Tools.ConeFold.evalAssigns_frame Wo sM.mems (openBody o.body) _ envFo hFo
          (memFree_openBody _ hmfO) w (fun hw => hdO (writes_drives (writesOf_openBody _ hw))),
        Tools.ConeFold.evalAssigns_frame Wm sM.mems (openBody m.body) _ envF' hopenM
          (memFree_openBody _ hmfM) w (fun hw => hdM (writes_drives (writesOf_openBody _ hw)))]
      simp only [seedIn]
      split
      · rfl
      · exact (hst w hdM hdO).symm
    -- `o`'s seeding is its oracle seeding
    have hseedO : seedIn (openFlat m insX outsX) (insOf (insX.map (·.name)) E ins) k stO =
        seedOuts children o.body envFo (seedIn m ins k stO) := by
      apply seed_eq hOutO hXin
      · intro n hn
        have hX := hOutO n hn
        rw [← hE0, hund n (hXdM n hX) (hXdO n hX)]
      · intro n hX hOo
        have hOm : n ∉ bodyInstOuts children m.body := by
          intro hm
          obtain ⟨mn, iname, conns, child, cwe, hmem, hc, hw⟩ := bodyInstOuts_mem hm
          exact hOo (instOut_body hc hw (hMO _ _ _ hmem))
        rw [← hE0, hframeM n (fun hl => hXdM n hX (linkedWrites_drives _ hl hOm))]
        have hI := hXin n hX
        simp only [seedIn, List.contains_eq_mem, hI, decide_false, Bool.false_eq_true, if_false]
        exact hst n (hXdM n hX) (hXdO n hX)
    have hopenO : evalAssigns Wo sM.mems o.body (seedOuts children o.body envFo (seedIn m ins k stO)) =
        some envFo := by
      rw [← hseedO, ← Tools.ShippingHierOptSoundness.evalAssigns_openBody]
      exact hFo
    -- each instance of `o` steps its child as in `m`'s run
    have hcons := linked_consistentKG KS Wm children sM.kids sM.mems m.body _ envF' sM.kids kids'
      hwfM hndM hK
    have hagF : ∀ w ∈ (m.outputs ++ outsX).map (·.name), envFo w = envF' w := by
      intro w hw
      have := hag 0 (by simp) (by simp) w hw
      simpa using this
    have hch : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
        ChildStepsKG KS children sM.kids envFo mn iname conns (kids' iname) := by
      intro mn iname conns hmem
      obtain ⟨child, cwe, envAt, cres, hc, hk, hin, hout⟩ := hcons mn iname conns (hOM _ _ _ hmem)
      refine ⟨child, cwe, hc, fun env1 hag1 => ⟨cres, ?_, ?_⟩⟩
      · rw [hloc child cwe _ env1 envAt _ (fun c hcin w hw => by
          have hcm := (List.mem_filter.mp hcin).1
          have hnot := hnofb mn iname conns hmem child cwe hc c hcin w hw
          rw [hag1 c hcm w hw hnot, hin c hcm w hw hnot]
          rcases hconn mn iname conns hmem c hcm w hw with h1 | ⟨h1, h2⟩
          · exact hagF w h1
          · exact hund w h1 h2)]
        exact hk
      · intro p hp w hw
        rw [← hout p hp w hw]
        have hX := hOutO w (instOut_body hc (mem_instOutWires hp hw) hmem)
        exact (hund w (hXdM w hX) (hXdO w hX)).symm
    have hstepO := open_linkedKG KS Wo children sM.kids sM.mems envFo kids' o.body
      (seedIn m ins k stO) sM.kids hwfO hopenO hch
    have hkids : kidsAfterG kids' o.body sM.kids = kids' := by
      funext n
      by_cases hn : n ∈ instNames o.body
      · obtain ⟨mn, conns, hm⟩ := mem_instNames hn
        exact kidsAfterG_inst kids' o.body sM.kids hndO mn n conns hm
      · rw [kidsAfterG_frame kids' o.body sM.kids n hn]
        have hn' : n ∉ instNames m.body := by
          intro h
          obtain ⟨mn, conns, hm⟩ := mem_instNames h
          exact hn (inst_instNames (hMO _ _ _ hm))
        exact (kids_frameKG KS Wm children sM.kids sM.mems n m.body _ envF' sM.kids kids' hK hn').symm
    rw [hkids] at hstepO
    have hNo' : regNexts Wo sM.mems o.body envFo = some nextsO := by
      rw [← regNexts_openBody]; exact hNo
    have hMo2 : memNexts Wo o.body sM.mems envFo = some sM.mems :=
      Tools.ConeFold.memNexts_memFree Wo o.body hmfO sM.mems envFo
    have ih := open_linked_run KS hloc Wm Wo children m o insX outsX ins E hwfM hwfO hndM hndO
      hOM hMO hnofb hOutM hOutO hXin hXdM hXdO hconn k ⟨applyNexts sM.st nexts, sM.mems, kids'⟩
      (applyNexts stO nextsO) rest restO hR
      (fun j hj => by
        have := hE (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [this]; congr 1; omega)
      hRO
      (fun j hj hj' w hw => by
        have := hag (j + 1) (by simp; omega) (by simp; omega) w hw
        simpa using this)
      (fun n hdM hdO => by
        show applyNexts sM.st nexts n = applyNexts stO nextsO n
        rw [applyNexts_out (fun p hp he => hdM (by
              rw [← he]; exact regNexts_names Wm sM.mems m.body envF' nexts hmfM hN p hp)),
          applyNexts_out (fun p hp he => hdO (by
              rw [← he]; exact regNexts_names Wo sM.mems o.body envFo nextsO hmfO hNo' p hp))]
        exact hst n hdM hdO)
    simp only [runModuleTG, stepModuleTG, hstepO, hNo', hMo2, Option.bind_eq_bind, Option.bind_some]
    rw [ih]
    rfl

theorem runModuleTG_length {σ : Type} (KS : KStep σ) (W : WEnv)
    (children : String → Option (Module × WEnv)) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS W children body seed T s = some envs → envs.length = T
  | 0, _, envs, h => by simp only [runModuleTG, Option.some.injEq] at h; subst h; rfl
  | k + 1, s, envs, h => by
    simp only [runModuleTG] at h
    cases hS : stepModuleTG KS W children body (seed k s.st) s with
    | none => simp [hS] at h
    | some r =>
      simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
      cases hR : runModuleTG KS W children body seed k r.2 with
      | none => simp [hR] at h
      | some rest =>
        simp only [hR, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [runModuleTG_length KS W children body seed k r.2 rest hR]

/-- **The optimizer check on an instance-bearing module, over the stateful
linked run.** If `hierRefineCheck m o` accepts the optimizer's output `o`,
every run of the stateful linked semantics of `m` (each instance stepping
its child by `KS` from its own state) has a run of `o` from the same state,
of the same length, with the same values on every output port of `m`. The
premises are about the design (the instance bodies are linked-well-formed
with distinct instance names, an instance reads none of its own outputs,
the wires the instances drive are the extracted inputs), the inputs (fit
their widths, reset low), the instance outputs and the registers' start
values (fit their widths). -/
theorem hierRefineCheck_linked {σ : Type} (KS : KStep σ) (hloc : KSLocal KS)
    (children : String → Option (Module × WEnv)) {m o : Module}
    (hchk : Sparkle.IR.RefineCheck.hierRefineCheck m o = true)
    (hwfM : linkedWF children m.body = true) (hwfO : linkedWF children o.body = true)
    (hndM : (instNames m.body).Nodup) (hndO : (instNames o.body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hOutM : ∀ w ∈ bodyInstOuts children m.body, w ∈ (openIns m).map (·.name))
    (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    (hrstIn : "rst" ∈ m.inputs.map (·.name)) (hrstZ : ∀ t, ins t "rst" = 0)
    {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs)
    (hfitX : ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x)
    (hfitR : ∀ r ∈ Sparkle.IR.OptCheck.seqRegs (openFlat m (openIns m) (openOuts m)),
      s.st r.1 < 2 ^ declWidth m r.1) :
    o.inputs = m.inputs ∧ o.outputs = m.outputs ∧
    ∃ envsO, runModuleTG KS (declWidth o) children o.body (seedIn m ins) T s = some envsO ∧
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
  have hOutO : ∀ w ∈ bodyInstOuts children o.body, w ∈ (openIns m).map (·.name) := by
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
  have hlen := runModuleTG_length KS _ children m.body _ T s envs hrun
  let E : Nat → Env := fun k => (envs[T - 1 - k]?).getD (fun _ => 0)
  have hE : ∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j) := by
    intro j hj
    simp only [E]
    rw [show T - 1 - (T - 1 - j) = j by omega]
    simp [hj]
  have hopen := linked_open_run KS (declWidth m) children m (openIns m) (openOuts m) ins E hwfM hOutM hXin hXdM
    T s envs hrun hE
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
        (insOf ((openIns m).map (·.name)) E ins)) T s.st s.mems = some envs := hopen
  obtain ⟨envsO, hrunO, hlenO, houtsO⟩ := Tools.ShippingRefineSoundness.refineCheck_transfer hrc
    (insOf ((openIns m).map (·.name)) E ins) hinsFit' hrstIn' hrstZ' (stM := s.st) (stO := s.st)
    (mems := s.mems) (fun _ _ => rfl) hfitR hopen'
  -- 3. the open run of the extracted optimized module as a linked run of `o`
  have hlinked := open_linked_run KS hloc (declWidth m) (declWidth o) children m o (openIns m) (openOuts m) ins E
    hwfM hwfO hndM hndO hOM hMO hnofb hOutM hOutO hXin hXdM hXdO hconn T s s.st envs envsO hrun hE
    hrunO
    (fun j hj hj' w hw => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      exact houtsO p hp j hj hj')
    (fun _ _ _ => rfl)
  refine ⟨envsO, hlinked, hlenO, fun p hp j hj hj' => houtsO p (List.mem_append_left _ hp) j hj hj'⟩

/-- Every step of the child of an instance of `body` keeps its output ports
within their declared widths. -/
def KSBoundedIn {σ : Type} (children : String → Option (Module × WEnv)) (KS : KStep σ)
    (body : List Stmt) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
  children mn = some (child, cwe) →
  ∀ cin env s cres s', KS child cwe cin env s = some (cres, s') →
    ∀ p ∈ child.outputs, cres p.name < 2 ^ p.ty.bitWidth

/-- **The extracted inputs fit along a linked run**: the instance-driven ones
are children's outputs at their ports' widths (`instOutWidthsOk`), the
others are never written and keep their start values. -/
theorem fitX_of_run {σ : Type} (KS : KStep σ)
    (children : String → Option (Module × WEnv)) (m : Module)
    (hKSb : KSBoundedIn children KS m.body) (ins : Nat → String → Nat)
    (hwf : linkedWF children m.body = true) (hnd : (instNames m.body).Nodup)
    (hIW : instOutWidthsOk children (declWidth m) m.body = true) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs →
      (∀ x ∈ (openIns m).map (·.name), x ∉ bodyInstOuts children m.body →
        s.st x < 2 ^ declWidth m x) →
      ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
        (envs[j]'hj) x < 2 ^ declWidth m x
  | 0, _, envs, h, _, j, hj, _, _ => by
    simp only [runModuleTG, Option.some.injEq] at h; subst h; cases hj
  | k + 1, s, envs, h, hst, j, hj, x, hx => by
    have hmf := memFree_of_linkedWF _ hwf
    simp only [runModuleTG] at h
    cases hS : stepModuleTG KS (declWidth m) children m.body (seedIn m ins k s.st) s with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, s'⟩ := r
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG KS (declWidth m) children m.body (seedIn m ins) k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    unfold stepModuleTG at hS
    cases hK : evalAssignsKG KS (declWidth m) children s.kids s.mems m.body
        (seedIn m ins k s.st) s.kids with
    | none => simp [hK] at hS
    | some ek =>
    obtain ⟨envF', kids'⟩ := ek
    cases hN : regNexts (declWidth m) s.mems m.body envF' with
    | none => simp [hK, hN] at hS
    | some nexts =>
    have hM : memNexts (declWidth m) m.body s.mems envF' = some s.mems :=
      Tools.ConeFold.memNexts_memFree _ m.body hmf s.mems envF'
    simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    have hXp := List.mem_map.mp hx
    obtain ⟨px, hpx, hpxn⟩ := hXp
    have hflt := (List.mem_filter.mp hpx).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hflt
    have hxd : x ∉ drivesOf m.body := by
      rw [← hpxn]; simpa [List.contains_eq_mem] using hflt.1.2
    have hxi : x ∉ m.inputs.map (·.name) := by
      rw [← hpxn]; simpa [List.contains_eq_mem] using hflt.2
    cases j with
    | zero =>
      show envF' x < _
      by_cases hO : x ∈ bodyInstOuts children m.body
      · obtain ⟨mn, iname, conns, child, cwe, hmem, hc, hw⟩ := bodyInstOuts_mem hO
        obtain ⟨child', cwe', envAt, cres, hc', hk, -, hout⟩ :=
          linked_consistentKG KS (declWidth m) children s.kids s.mems m.body _ envF' s.kids kids'
            hwf hnd hK mn iname conns hmem
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
        exact hKSb mn iname conns hmem child cwe hc _ _ _ _ _ hk p hp
      · rw [linked_frameKG KS (declWidth m) children s.kids s.mems x m.body _ envF' s.kids kids'
          hwf hK (fun hl => hxd (linkedWrites_drives _ hl hO))]
        simp only [seedIn, List.contains_eq_mem, hxi, decide_false, Bool.false_eq_true, if_false]
        exact hst x hx hO
    | succ j =>
      have := fitX_of_run KS children m hKSb ins hwf hnd hIW k
        ⟨applyNexts s.st nexts, s.mems, kids'⟩ rest hR
        (fun y hy hyO => by
          show applyNexts s.st nexts y < _
          have hyp := List.mem_map.mp hy
          obtain ⟨py, hpy, hpyn⟩ := hyp
          have hf := (List.mem_filter.mp hpy).2
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
          have hyd : y ∉ drivesOf m.body := by
            rw [← hpyn]; simpa [List.contains_eq_mem] using hf.1.2
          rw [applyNexts_out (fun p hp he => hyd (by
            rw [← he]; exact regNexts_names _ s.mems m.body envF' nexts hmf hN p hp))]
          exact hst y hy hyO) j (by simpa using hj) x hx
      simpa using this

end Tools.ShippingHierOptRun
