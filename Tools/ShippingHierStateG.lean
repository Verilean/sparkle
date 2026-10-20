import Tools.ShippingHierState

/-! # Stateful hierarchical semantics, at every depth

`ShippingHierState` steps each instance's child FLAT (`stepModule`): one
level of hierarchy. Here the child's step is a parameter `KS` over an
abstract kid state `σ`; a module's own state is `KState σ` (its registers,
memories and its instances' states). Depth `n + 1` steps every child by the
depth-`n` stateful step of the child's module (`succKS`), so a design of any
depth is run by iterating `succKS` from the flat step (`flatKS`). The bridge
`runModuleTG_of_childRuns` is `runModuleT_of_childRuns` for any `KS` whose
step reads the parent only through its input connections (`KSLocal`). -/
namespace Tools.ShippingHierStateG
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf evalExpr_congr writesOf stmtWrites)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked
open Tools.ShippingHierState

/-- A module's state: its registers, its memories, its instances' states. -/
structure KState (σ : Type) where
  st : String → Nat
  mems : MEnv
  kids : String → σ

/-- A child's step: on its module, width map, input connections and the
parent's environment, from its state, the child's environment and next state. -/
abbrev KStep (σ : Type) :=
  Module → WEnv → List (String × Expr) → Env → σ → Option (Env × σ)

/-- A child's step reads the parent's environment only on the wires of its
input connections. -/
def KSLocal {σ : Type} (KS : KStep σ) : Prop :=
  ∀ child cwe cin env env' s, (∀ c ∈ cin, ∀ w, c.2 = .ref w → env w = env' w) →
    KS child cwe cin env s = KS child cwe cin env' s

/-- One cycle's elaboration, each instance stepping its child by `KS`. -/
def evalAssignsKG {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv) :
    List Stmt → Env → (String → σ) → Option (Env × (String → σ))
  | [], env, acc => some (env, acc)
  | .assign l r :: rest, env, acc => do
    let v ← evalExpr we env r
    evalAssignsKG KS we children kids mems rest (fun n => if n = l then v else env n) acc
  | .inst mn iname conns :: rest, env, acc => do
    let (child, cwe) ← children mn
    let (cres, ks') ← KS child cwe (inConns child.outputs conns) env (kids iname)
    evalAssignsKG KS we children kids mems rest (bindOuts child.outputs conns cres env)
      (fun n => if n = iname then ks' else acc n)
  | .register .. :: rest, env, acc => evalAssignsKG KS we children kids mems rest env acc
  | .memory name aw dw _ _ _ _ ra rd cr _ er :: rest, env, acc =>
    -- as `evalAssigns`: a combinational read port drives its data wire
    if cr then do
      let env' ← comboReads we mems name aw dw ((ra, rd) :: er) env
      evalAssignsKG KS we children kids mems rest env' acc
    else evalAssignsKG KS we children kids mems rest env acc

/-- One cycle of a module with stateful children. -/
def stepModuleTG {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (body : List Stmt) (env0 : Env)
    (s : KState σ) : Option (Env × KState σ) := do
  let (envF, kids') ← evalAssignsKG KS we children s.kids s.mems body env0 s.kids
  let nexts ← regNexts we s.mems body envF
  let mems' ← memNexts we body s.mems envF
  some (envF, ⟨applyNexts s.st nexts, mems', kids'⟩)

/-- The run of a module with stateful children (the seed index counts down). -/
def runModuleTG {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) : Nat → KState σ → Option (List Env)
  | 0, _ => some []
  | k + 1, s => do
    let (envF, s') ← stepModuleTG KS we children body (seed k s.st) s
    let rest ← runModuleTG KS we children body seed k s'
    some (envF :: rest)

/-- A child's own run under `KS`, fed at every cycle with `P`. -/
def runKS {σ : Type} (KS : KStep σ) (child : Module) (cwe : WEnv)
    (cin : List (String × Expr)) (P : Nat → Env) : Nat → σ → Option (List Env)
  | 0, _ => some []
  | k + 1, s => do
    let (cres, s') ← KS child cwe cin (P k) s
    let rest ← runKS KS child cwe cin P k s'
    some (cres :: rest)

/-- The flat step: a child without stateful children of its own. -/
def flatKS : KStep KidState := fun child cwe cin env ks =>
  (stepModule cwe child.body (connEnvS cin env ks.st) ks.mems).map fun r =>
    (r.1, ⟨applyNexts ks.st r.2.1, r.2.2⟩)

/-- The step one level up: the child's own stateful step. -/
def succKS {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv)) :
    KStep (KState σ) := fun child cwe cin env s =>
  stepModuleTG KS cwe children child.body (connEnvS cin env s.st) s

theorem connEnvS_local {cin : List (String × Expr)} {env env' : Env} {cst : String → Nat}
    (h : ∀ c ∈ cin, ∀ w, c.2 = .ref w → env w = env' w) :
    connEnvS cin env cst = connEnvS cin env' cst := by
  funext n
  unfold connEnvS
  cases hl : cin.lookup n with
  | none => rfl
  | some e =>
    cases e with
    | ref w =>
      obtain ⟨c, hc, _, hc2⟩ := lookup_mem _ n (.ref w) hl
      exact h c hc w hc2
    | _ => rfl

theorem flatKS_local : KSLocal flatKS := by
  intro child cwe cin env env' s h
  simp only [flatKS, connEnvS_local h]

theorem succKS_local {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv)) :
    KSLocal (succKS KS children) := by
  intro child cwe cin env env' s h
  simp only [succKS, connEnvS_local h]

/-- A flat child's own run is its module's run. -/
theorem runKS_flat (child : Module) (cwe : WEnv) (cin : List (String × Expr)) (P : Nat → Env) :
    ∀ (k : Nat) (ks : KidState),
      runKS flatKS child cwe cin P k ks =
        runModule cwe child.body (fun t cst => connEnvS cin (P t) cst) k ks.st ks.mems
  | 0, _ => rfl
  | k + 1, ks => by
    simp only [runKS, runModule, flatKS]
    cases hs : stepModule cwe child.body (connEnvS cin (P k) ks.st) ks.mems with
    | none => rfl
    | some r =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rw [runKS_flat child cwe cin P k ⟨applyNexts ks.st r.2.1, r.2.2⟩]

/-- A child one level up runs as its own module with stateful children. -/
theorem runKS_succ {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    (child : Module) (cwe : WEnv) (cin : List (String × Expr)) (P : Nat → Env) :
    ∀ (k : Nat) (s : KState σ),
      runKS (succKS KS children) child cwe cin P k s =
        runModuleTG KS cwe children child.body (fun t cst => connEnvS cin (P t) cst) k s
  | 0, _ => rfl
  | k + 1, s => by
    simp only [runKS, runModuleTG, succKS]
    cases hs : stepModuleTG KS cwe children child.body (connEnvS cin (P k) s.st) s with
    | none => rfl
    | some r =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [runKS_succ KS children child cwe cin P k r.2]

/-! ## The open run is the stateful run -/

/-- The children's states after one cycle: each instance's given next state. -/
def kidsAfterG {σ : Type} (nxs : String → σ) : List Stmt → (String → σ) → (String → σ)
  | [], acc => acc
  | .inst _ iname _ :: rest, acc =>
    kidsAfterG nxs rest (fun n => if n = iname then nxs iname else acc n)
  | _ :: rest, acc => kidsAfterG nxs rest acc

/-- What a child is assumed to do in one cycle: fed with any environment that
agrees with `envF` on the wires of its input connections, it steps to `ks'`
and its output ports carry `envF`'s values on their connected wires. -/
def ChildStepsKG {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    (kids : String → σ) (envF : Env) (mn iname : String) (conns : List (String × Expr))
    (ks' : σ) : Prop :=
  ∃ child cwe, children mn = some (child, cwe) ∧
    ∀ env1 : Env, (∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ instOutWires child.outputs conns →
        env1 w = envF w) →
      ∃ cres, KS child cwe (inConns child.outputs conns) env1 (kids iname) = some (cres, ks') ∧
        ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) → cres p.name = envF w

theorem open_linkedKG {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv) (envF : Env)
    (nxs : String → σ) :
    ∀ (body : List Stmt) (env : Env) (acc : String → σ), linkedWF children body = true →
      evalAssigns we mems body (seedOuts children body envF env) = some envF →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
        ChildStepsKG KS children kids envF mn iname conns (nxs iname)) →
      evalAssignsKG KS we children kids mems body env acc =
        some (envF, kidsAfterG nxs body acc)
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
        evalAssignsKG KS we children kids mems rest (fun m => if m = l then v else env m) acc) =
          some (envF, kidsAfterG nxs rest acc)
      rw [hv]
      apply open_linkedKG KS we children kids mems envF nxs rest _ acc hrest _
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
        (KS cp.1 cp.2 (inConns cp.1.outputs conns) env (kids iname)).bind
          fun r => evalAssignsKG KS we children kids mems rest (bindOuts cp.1.outputs conns r.1 env)
            (fun n => if n = iname then r.2 else acc n)) =
        some (envF, kidsAfterG nxs (.inst mn iname conns :: rest) acc)
    rw [hc]
    show ((KS child cwe (inConns child.outputs conns) env (kids iname)).bind
          fun r => evalAssignsKG KS we children kids mems rest (bindOuts child.outputs conns r.1 env)
            (fun n => if n = iname then r.2 else acc n)) =
        some (envF, kidsAfterG nxs (.inst mn iname conns :: rest) acc)
    rw [hcres]
    show evalAssignsKG KS we children kids mems rest (bindOuts child.outputs conns cres env)
        (fun n => if n = iname then nxs iname else acc n) =
      some (envF, kidsAfterG nxs rest (fun n => if n = iname then nxs iname else acc n))
    apply open_linkedKG KS we children kids mems envF nxs rest _ _ hrest _
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
    show evalAssignsKG KS we children kids mems rest env acc =
      some (envF, kidsAfterG nxs rest acc)
    exact open_linkedKG KS we children kids mems envF nxs rest env acc hwf h
      (fun mn iname conns hm => hch mn iname conns (List.mem_cons_of_mem _ hm))
  | .memory .. :: _, _, _, hwf, _, _ => by simp [linkedWF] at hwf

/-- **The stateful run is the open run** when at every cycle every child steps
to what the open run carries on its outputs. -/
theorem runModuleTG_of_open {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed seed' : Nat → (String → Nat) → Env)
    (hwf : linkedWF children body = true)
    (Kid : Nat → KState σ → Prop) (nxs : Nat → (String → σ) → String → σ)
    (H : ∀ m (s : KState σ) envF nexts mems', Kid (m + 1) s →
      evalAssigns we s.mems body (seed' m s.st) = some envF →
      regNexts we s.mems body envF = some nexts → memNexts we body s.mems envF = some mems' →
      seed' m s.st = seedOuts children body envF (seed m s.st) ∧
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
        ChildStepsKG KS children s.kids envF mn iname conns (nxs m s.kids iname)) ∧
      Kid m ⟨applyNexts s.st nexts, mems', kidsAfterG (nxs m s.kids) body s.kids⟩) :
    ∀ (k : Nat) (s : KState σ) (envs : List Env),
      Kid k s → runModule we body seed' k s.st s.mems = some envs →
      runModuleTG KS we children body seed k s = some envs
  | 0, _, envs, _, h => h
  | k + 1, s, envs, hk, h => by
    have h' : (stepModule we body (seed' k s.st) s.mems).bind (fun r =>
        (runModule we body seed' k (applyNexts s.st r.2.1) r.2.2).bind
          (fun rest => some (r.1 :: rest))) = some envs := h
    cases hS : stepModule we body (seed' k s.st) s.mems with
    | none => rw [hS] at h'; cases h'
    | some r =>
      obtain ⟨envF, nexts, mems', hF, hN, hM, rfl⟩ := stepModule_some hS
      obtain ⟨hseed, hch, hkid⟩ := H k s envF nexts mems' hk hF hN hM
      have hlinked : evalAssignsKG KS we children s.kids s.mems body (seed k s.st) s.kids =
          some (envF, kidsAfterG (nxs k s.kids) body s.kids) := by
        apply open_linkedKG KS we children s.kids s.mems envF (nxs k s.kids) body (seed k s.st)
          s.kids hwf _ hch
        rw [← hseed]; exact hF
      have hstepT : stepModuleTG KS we children body (seed k s.st) s =
          some (envF, ⟨applyNexts s.st nexts, mems', kidsAfterG (nxs k s.kids) body s.kids⟩) := by
        simp [stepModuleTG, hlinked, hN, hM]
      rw [hS] at h'
      simp only [Option.bind_some] at h'
      cases hR : runModule we body seed' k (applyNexts s.st nexts) mems' with
      | none => rw [hR] at h'; cases h'
      | some rest =>
        rw [hR] at h'
        simp only [Option.bind_some, Option.some.injEq] at h'
        show (stepModuleTG KS we children body (seed k s.st) s).bind (fun r =>
          (runModuleTG KS we children body seed k r.2).bind
            (fun rest => some (r.1 :: rest))) = some envs
        rw [hstepT]
        simp only [Option.bind_some]
        rw [runModuleTG_of_open KS we children body seed seed' hwf Kid nxs H k _ rest hkid hR]
        simp [h']

/-! ## From the children's own runs -/

theorem childStepsKG_of_step {σ : Type} {KS : KStep σ} (hloc : KSLocal KS)
    {children : String → Option (Module × WEnv)}
    {kids : String → σ} {envF : Env} {mn iname : String} {conns : List (String × Expr)}
    {child : Module} {cwe : WEnv} {cres : Env} {ks' : σ}
    (hc : children mn = some (child, cwe))
    (hnofb : ∀ c ∈ inConns child.outputs conns, ∀ w, c.2 = .ref w →
      w ∉ instOutWires child.outputs conns)
    (hstep : KS child cwe (inConns child.outputs conns) envF (kids iname) = some (cres, ks'))
    (hout : ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
      cres p.name = envF w) :
    ChildStepsKG KS children kids envF mn iname conns ks' := by
  refine ⟨child, cwe, hc, fun env1 hagree => ⟨cres, ?_, hout⟩⟩
  have h := hloc child cwe (inConns child.outputs conns) env1 envF (kids iname)
    (fun c hcin w hc2 => hagree c (List.mem_filter.mp hcin).1 w hc2 (hnofb c hcin w hc2))
  rw [h]
  exact hstep

theorem kidsAfterG_frame {σ : Type} (nxs : String → σ) :
    ∀ (body : List Stmt) (acc : String → σ) (n : String), n ∉ instNames body →
      kidsAfterG nxs body acc n = acc n
  | [], _, _, _ => rfl
  | .inst _ iname _ :: rest, acc, n, hn => by
    simp only [instNames, List.mem_cons, not_or] at hn
    show kidsAfterG nxs rest _ n = acc n
    rw [kidsAfterG_frame nxs rest _ n hn.2]
    simp [Ne.symm hn.1, hn.1]
  | .assign _ _ :: rest, acc, n, hn => kidsAfterG_frame nxs rest acc n hn
  | .register .. :: rest, acc, n, hn => kidsAfterG_frame nxs rest acc n hn
  | .memory .. :: rest, acc, n, hn => kidsAfterG_frame nxs rest acc n hn

theorem kidsAfterG_inst {σ : Type} (nxs : String → σ) :
    ∀ (body : List Stmt) (acc : String → σ), (instNames body).Nodup →
      ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → kidsAfterG nxs body acc iname = nxs iname
  | [], _, _, _, _, _, h => by cases h
  | .inst mn' iname' conns' :: rest, acc, hnd, mn, iname, conns, h => by
    simp only [instNames, List.nodup_cons] at hnd
    show kidsAfterG nxs rest _ iname = _
    rcases List.mem_cons.mp h with h | h
    · injection h with h1 h2 h3
      subst h2
      rw [kidsAfterG_frame nxs rest _ iname hnd.1]
      simp
    · exact kidsAfterG_inst nxs rest _ hnd.2 mn iname conns h
  | .assign _ _ :: rest, acc, hnd, mn, iname, conns, h =>
    kidsAfterG_inst nxs rest acc hnd mn iname conns (by
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h)
  | .register .. :: rest, acc, hnd, mn, iname, conns, h =>
    kidsAfterG_inst nxs rest acc hnd mn iname conns (by
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h)
  | .memory .. :: rest, acc, hnd, mn, iname, conns, h =>
    kidsAfterG_inst nxs rest acc hnd mn iname conns (by
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact h)

/-- The cycle of instance `iname`'s child under `KS`. -/
def kidStepG {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    (body : List Stmt) (env : Env) (kids : String → σ) (iname : String) : Option (Env × σ) := do
  let (mn, conns) ← instOf body iname
  let (child, cwe) ← children mn
  KS child cwe (inConns child.outputs conns) env (kids iname)

/-- **The stateful run from the children's own runs**, for any child step
reading the parent only through its input connections. -/
theorem runModuleTG_of_childRuns {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) (we : WEnv)
    (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed seed' : Nat → (String → Nat) → Env)
    (hwf : linkedWF children body = true) (hnd : (instNames body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hseed : ∀ t st mems envF, evalAssigns we mems body (seed' t st) = some envF →
      seed' t st = seedOuts children body envF (seed t st))
    (P : Nat → Env) :
    ∀ (k : Nat) (s : KState σ) (envs : List Env),
      runModule we body seed' k s.st s.mems = some envs →
      (∀ j, j < k → envs[j]? = some (P (k - 1 - j))) →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∃ child cwe cenvs,
        children mn = some (child, cwe) ∧
        runKS KS child cwe (inConns child.outputs conns) P k (s.kids iname) = some cenvs ∧
        ∀ j, j < k → ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
          (cenvs[j]?).map (· p.name) = some (P (k - 1 - j) w)) →
      runModuleTG KS we children body seed k s = some envs := by
  intro k s envs hrun hP hk0
  let Kid : Nat → KState σ → Prop := fun m s =>
    (∃ envs', runModule we body seed' m s.st s.mems = some envs' ∧
      ∀ j, j < m → envs'[j]? = some (P (m - 1 - j))) ∧
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∃ child cwe cenvs,
      children mn = some (child, cwe) ∧
      runKS KS child cwe (inConns child.outputs conns) P m (s.kids iname) = some cenvs ∧
      ∀ j, j < m → ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
        (cenvs[j]?).map (· p.name) = some (P (m - 1 - j) w)
  let nxs : Nat → (String → σ) → String → σ := fun m kids iname =>
    match kidStepG KS children body (P m) kids iname with
    | some r => r.2
    | none => kids iname
  apply runModuleTG_of_open KS we children body seed seed' hwf Kid nxs
    _ k s envs ⟨⟨envs, hrun, hP⟩, hk0⟩ hrun
  intro m s envF nexts mems' ⟨⟨envs', hrun', hP'⟩, hkids⟩ hF hN hM
  have hstep : stepModule we body (seed' m s.st) s.mems = some (envF, nexts, mems') := by
    simp [stepModule, hF, hN, hM]
  have h' : (stepModule we body (seed' m s.st) s.mems).bind (fun r =>
      (runModule we body seed' m (applyNexts s.st r.2.1) r.2.2).bind
        (fun rest => some (r.1 :: rest))) = some envs' := hrun'
  rw [hstep] at h'
  simp only [Option.bind_some] at h'
  cases hR : runModule we body seed' m (applyNexts s.st nexts) mems' with
  | none => rw [hR] at h'; cases h'
  | some rest =>
    rw [hR] at h'
    simp only [Option.bind_some, Option.some.injEq] at h'
    subst h'
    have hP0 := hP' 0 (by omega)
    simp only [List.getElem?_cons_zero, Option.some.injEq, Nat.sub_zero] at hP0
    rw [show m + 1 - 1 = m by omega] at hP0
    have hchild : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∃ child cwe cres ctail,
        children mn = some (child, cwe) ∧
        KS child cwe (inConns child.outputs conns) envF (s.kids iname) =
          some (cres, nxs m s.kids iname) ∧
        runKS KS child cwe (inConns child.outputs conns) P m (nxs m s.kids iname) = some ctail ∧
        (∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) → cres p.name = envF w) ∧
        ∀ j, j < m → ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
          (ctail[j]?).map (· p.name) = some (P (m - 1 - j) w) := by
      intro mn iname conns hm
      obtain ⟨child, cwe, cenvs, hc, hcrun, hcobs⟩ := hkids mn iname conns hm
      have hcrun' : (KS child cwe (inConns child.outputs conns) (P m) (s.kids iname)).bind
          (fun r => (runKS KS child cwe (inConns child.outputs conns) P m r.2).bind
            (fun rest => some (r.1 :: rest))) = some cenvs := hcrun
      cases hcs : KS child cwe (inConns child.outputs conns) (P m) (s.kids iname) with
      | none => rw [hcs] at hcrun'; cases hcrun'
      | some r =>
        obtain ⟨cres, ks'⟩ := r
        have hks : kidStepG KS children body (P m) s.kids iname = some (cres, ks') := by
          simp [kidStepG, instOf_mem body hnd mn iname conns hm, hc, hcs]
        have hnx : nxs m s.kids iname = ks' := by simp [nxs, hks]
        rw [hcs] at hcrun'
        simp only [Option.bind_some] at hcrun'
        cases hct : runKS KS child cwe (inConns child.outputs conns) P m ks' with
        | none => rw [hct] at hcrun'; cases hcrun'
        | some ctail =>
          rw [hct] at hcrun'
          simp only [Option.bind_some, Option.some.injEq] at hcrun'
          subst hcrun'
          refine ⟨child, cwe, cres, ctail, hc, by rw [hnx, hP0]; exact hcs, by rw [hnx]; exact hct,
            ?_, ?_⟩
          · intro p hp w hw
            have := hcobs 0 (by omega) p hp w hw
            simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at this
            rw [this, show m + 1 - 1 - 0 = m by omega, hP0]
          · intro j hj p hp w hw
            have := hcobs (j + 1) (by omega) p hp w hw
            simp only [List.getElem?_cons_succ] at this
            rw [this, show m + 1 - 1 - (j + 1) = m - 1 - j by omega]
    refine ⟨hseed m s.st s.mems envF hF, ?_, ⟨⟨rest, hR, ?_⟩, ?_⟩⟩
    · intro mn iname conns hm
      obtain ⟨child, cwe, cres, ctail, hc, hcs, _, hout, _⟩ := hchild mn iname conns hm
      exact childStepsKG_of_step hloc hc (hnofb mn iname conns hm child cwe hc) hcs hout
    · intro j hj
      have := hP' (j + 1) (by omega)
      simp only [List.getElem?_cons_succ] at this
      rw [this, show m + 1 - 1 - (j + 1) = m - 1 - j by omega]
    · intro mn iname conns hm
      obtain ⟨child, cwe, cres, ctail, hc, _, hct, _, hobs⟩ := hchild mn iname conns hm
      refine ⟨child, cwe, ctail, hc, ?_, hobs⟩
      show runKS KS child cwe _ P m (kidsAfterG (nxs m s.kids) body s.kids iname) = some ctail
      rw [kidsAfterG_inst (nxs m s.kids) body s.kids hnd mn iname conns hm]
      exact hct

/-! ## Instance-free modules run flat -/

/-- A body without instance statements. -/
def instFree (body : List Stmt) : Prop := ∀ st ∈ body, Sparkle.IR.Machine.isInst st = false

theorem evalAssignsKG_instFree {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv) :
    ∀ (body : List Stmt) (env : Env) (acc : String → σ), instFree body →
      evalAssignsKG KS we children kids mems body env acc =
        (evalAssigns we mems body env).map fun e => (e, acc)
  | [], _, _, _ => rfl
  | .assign l r :: rest, env, acc, h => by
    simp only [evalAssignsKG, evalAssigns]
    cases hv : evalExpr we env r with
    | none => rfl
    | some v =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      exact evalAssignsKG_instFree KS we children kids mems rest _ acc
        (fun st hs => h st (List.mem_cons_of_mem _ hs))
  | .register .. :: rest, env, acc, h => by
    simp only [evalAssignsKG, evalAssigns]
    exact evalAssignsKG_instFree KS we children kids mems rest _ acc
      (fun st hs => h st (List.mem_cons_of_mem _ hs))
  | .memory name aw dw c wa wd we' ra rd cr ew er :: rest, env, acc, h => by
    simp only [evalAssignsKG, evalAssigns]
    split
    · cases hc : comboReads we mems name aw dw ((ra, rd) :: er) env with
      | none => simp [hc]
      | some env' =>
        simp only [hc, Option.bind_eq_bind, Option.bind_some]
        exact evalAssignsKG_instFree KS we children kids mems rest _ acc
          (fun st hs => h st (List.mem_cons_of_mem _ hs))
    · exact evalAssignsKG_instFree KS we children kids mems rest _ acc
        (fun st hs => h st (List.mem_cons_of_mem _ hs))
  | .inst .. :: _, _, _, h => by
    have := h _ List.mem_cons_self
    simp [Sparkle.IR.Machine.isInst] at this

/-- **An instance-free module's stateful run is its run**, whatever its
children's step: its instances' states never change. -/
theorem runModuleTG_instFree {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (body : List Stmt) (hf : instFree body)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (s : KState σ),
      runModuleTG KS we children body seed k s = runModule we body seed k s.st s.mems
  | 0, _ => rfl
  | k + 1, s => by
    simp only [runModuleTG, runModule, stepModuleTG, stepModule,
      evalAssignsKG_instFree KS we children s.kids s.mems body _ _ hf]
    cases hE : evalAssigns we s.mems body (seed k s.st) with
    | none => rfl
    | some envF =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      cases hN : regNexts we s.mems body envF with
      | none => rfl
      | some nexts =>
        simp only [Option.bind_some]
        cases hM : memNexts we body s.mems envF with
        | none => rfl
        | some mems' =>
          simp only [Option.bind_some]
          rw [runModuleTG_instFree KS we children body hf seed k ⟨applyNexts s.st nexts, mems', s.kids⟩]

/-! ## The depth tower -/

/-- The state of an instance at depth `n`: flat at `0`, a module with
instances of depth `n` one level up. -/
def KT : Nat → Type
  | 0 => KidState
  | n + 1 => KState (KT n)

/-- The children's step at depth `n`. -/
def KSn (children : String → Option (Module × WEnv)) : (n : Nat) → KStep (KT n)
  | 0 => flatKS
  | n + 1 => succKS (KSn children n) children

theorem KSn_local (children : String → Option (Module × WEnv)) :
    ∀ n, KSLocal (KSn children n)
  | 0 => flatKS_local
  | n + 1 => succKS_local (KSn children n) children

/-- An instance's registers at any depth. -/
def stOf : (n : Nat) → KT n → (String → Nat)
  | 0, s => KidState.st s
  | _ + 1, s => KState.st s

/-- An instance's memories at any depth. -/
def memsOf : (n : Nat) → KT n → MEnv
  | 0, s => KidState.mems s
  | _ + 1, s => KState.mems s

/-- **An instance-free child runs flat at every depth.** -/
theorem runKS_instFree (children : String → Option (Module × WEnv)) (child : Module) (cwe : WEnv)
    (hf : instFree child.body) (cin : List (String × Expr)) (P : Nat → Env) :
    ∀ (n k : Nat) (s : KT n),
      runKS (KSn children n) child cwe cin P k s =
        runModule cwe child.body (fun t cst => connEnvS cin (P t) cst) k (stOf n s) (memsOf n s)
  | 0, k, s => runKS_flat child cwe cin P k s
  | n + 1, k, s => by
    show runKS (succKS (KSn children n) children) child cwe cin P k s = _
    rw [runKS_succ, runModuleTG_instFree _ _ _ _ hf]
    rfl

end Tools.ShippingHierStateG
