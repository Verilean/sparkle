import Tools.ShippingHierOptRun
import Tools.ShippingHierSVSoundness

/-! # A module with stateful children, to its emitted Verilog

The emitted Verilog of an instance-bearing module is its continuous
assignments, registers and the instantiations of its children. The SV
semantics of one module (`runModuleSV`) is open: the wires the instances
drive are free. A stateful linked run of the module (`runModuleTG`, each
instance stepping its child) IS the open run seeded, at each cycle, with the
values the children drove (`linked_open_runG`), and the emitted-SV check
carries that open run to the emitted Verilog (`seq_run_to_svI`): the
module's emitted Verilog, with its instance outputs taken from its children,
runs to the linked run's environments (`linked_sv_run`). -/
namespace Tools.ShippingHierSVRun
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierStateG
open Tools.ShippingHierState Tools.ShippingHierOptLinked Tools.ShippingHierOptRun
open Tools.SVParser.EmitSem (seqCheck emitAssigns emitRegs emitMemWrites runModuleSV)
open Tools.ShippingSeqSVSoundness (seqNames)
open Tools.ShippingHierSVSoundness (seqStmtOkI seq_run_to_svI)
open Tools.ShippingSeqOptSoundness (seedIn)

/-- The oracle seeding of a run: at cycle `k`, the instance-driven wires
carry `E k`. -/
def oracle (children : String → Option (Module × WEnv)) (body : List Stmt) (E : Nat → Env)
    (seed : Nat → (String → Nat) → Env) : Nat → (String → Nat) → Env :=
  fun k st => seedOuts children body (E k) (seed k st)

/-- **The linked run is the open run from its oracle seeding.** -/
theorem linked_open_runG {σ : Type} (KS : KStep σ) (W : WEnv)
    (children : String → Option (Module × WEnv)) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) (E : Nat → Env)
    (hwf : linkedWF children body = true) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS W children body seed T s = some envs →
      (∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j)) →
      runModule W body (oracle children body E seed) T s.st s.mems = some envs
  | 0, s, envs, h, _ => by simpa [runModuleTG, runModule] using h
  | k + 1, s, envs, h, hE => by
    simp only [runModuleTG] at h
    cases hS : stepModuleTG KS W children body (seed k s.st) s with
    | none => simp [hS] at h
    | some r =>
      obtain ⟨envF, s'⟩ := r
      simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
      cases hR : runModuleTG KS W children body seed k s' with
      | none => simp [hR] at h
      | some rest =>
        simp only [hR, Option.bind_some, Option.some.injEq] at h
        subst h
        unfold stepModuleTG at hS
        cases hK : evalAssignsKG KS W children s.kids s.mems body (seed k s.st) s.kids with
        | none => simp [hK] at hS
        | some ek =>
          obtain ⟨envF', kids'⟩ := ek
          cases hN : regNexts W s.mems body envF' with
          | none => simp [hK, hN] at hS
          | some nexts =>
            cases hM : memNexts W body s.mems envF' with
            | none => simp [hK, hN, hM] at hS
            | some mems' =>
              simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
                Option.some.injEq, Prod.mk.injEq] at hS
              obtain ⟨rfl, rfl⟩ := hS
              have hE0 : envF' = E k := by
                have := hE 0 (by simp)
                simpa using this
              have hopen := linked_openKG KS W children s.kids s.mems body _ envF' s.kids kids'
                hwf hK
              have ih := linked_open_runG KS W children body seed E hwf k
                ⟨applyNexts s.st nexts, mems', kids'⟩ rest hR (fun j hj => by
                  have := hE (j + 1) (by simp; omega)
                  simp only [List.getElem_cons_succ] at this
                  rw [this]
                  congr 1
                  omega)
              have hopen' : evalAssigns W s.mems body (oracle children body E seed k s.st) =
                  some envF' := by
                simp only [oracle, ← hE0]; exact hopen
              simp only [runModule, stepModule, hopen', hN, hM, Option.bind_eq_bind,
                Option.bind_some]
              rw [ih]
              rfl

/-- **A module with stateful children, to its emitted Verilog.** A linked run
of `o` is the run of `o`'s emitted Verilog from the oracle seeding (its
instance outputs at each cycle the values its children drove), under the
emitted-SV check of `o` and its width agreement, when the oracle seeding
stays within the emitter's widths. -/
theorem linked_sv_run {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    {o : Module} {wof : String → Option Nat}
    (hwf : linkedWF children o.body = true)
    (hok : o.body.all seqStmtOkI = true)
    (hsv : seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwag : ∀ n ∈ seqNames o.body, declWidth o n = Tools.SVParser.EmitSem.weOf wof n)
    {seed : Nat → (String → Nat) → Env} {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth o) children o.body seed T s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      Bounded (Tools.SVParser.EmitSem.weOf wof)
        (oracle children o.body (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) seed k st))
    (hst : Bounded (Tools.SVParser.EmitSem.weOf wof) s.st) :
    ∃ pairs regs mprog,
      emitAssigns wof o.body = some pairs ∧ emitRegs wof o.body = some regs ∧
      emitMemWrites wof o.body = some mprog ∧
      runModuleSV wof pairs regs mprog
        (oracle children o.body (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) seed) T
        s.st s.mems = some envs := by
  have hlen := runModuleTG_length KS _ children o.body seed T s envs hrun
  have hE : ∀ j (hj : j < envs.length),
      envs[j] = (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) (T - 1 - j) := by
    intro j hj
    simp only
    rw [show T - 1 - (T - 1 - j) = j by omega]
    simp [hj]
  have hopen := linked_open_runG KS (declWidth o) children o.body seed
    (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) hwf T s envs hrun hE
  exact seq_run_to_svI hok hsv hwag _ hseedB hst hopen

theorem lookup_mem {k : String} {e : Expr} :
    ∀ {l : List (String × Expr)}, l.lookup k = some e → (k, e) ∈ l
  | [], h => by cases h
  | (a, b) :: rest, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      cases h
      have : k = a := by simpa using hk
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- **Each instance's child runs on its connections.** Along a linked run
with one-level children (`flatKS`), the child of an instance runs its own
module, fed at each cycle with the values `E` of that cycle on its input
connections, and its outputs are the values of the wires they drive. -/
theorem child_run_of_linked (W : WEnv) (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed : Nat → (String → Nat) → Env) (E : Nat → Env)
    (hwf : linkedWF children body = true) (hnd : (instNames body).Nodup)
    {mn iname : String} {conns : List (String × Expr)} {child : Module} {cwe : WEnv}
    (hmem : Stmt.inst mn iname conns ∈ body) (hc : children mn = some (child, cwe))
    (hnofb : ∀ c ∈ inConns child.outputs conns, ∀ w, c.2 = .ref w →
      w ∉ instOutWires child.outputs conns) :
    ∀ (T : Nat) (s : KState KidState) (envs : List Env),
      runModuleTG flatKS W children body seed T s = some envs →
      (∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j)) →
      ∃ cenvs, runModule cwe child.body
          (fun k st => connEnvS (inConns child.outputs conns) (E k) st) T
          (s.kids iname).st (s.kids iname).mems = some cenvs ∧
        cenvs.length = envs.length ∧
        ∀ j (hj : j < envs.length) (hj' : j < cenvs.length), ∀ p ∈ child.outputs, ∀ w,
          conns.lookup p.name = some (.ref w) → (envs[j]'hj) w = (cenvs[j]'hj') p.name
  | 0, s, envs, h, _ => by
    simp only [runModuleTG, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl, fun j hj => by cases hj⟩
  | k + 1, s, envs, h, hE => by
    simp only [runModuleTG] at h
    cases hS : stepModuleTG flatKS W children body (seed k s.st) s with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, s'⟩ := r
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG flatKS W children body seed k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    unfold stepModuleTG at hS
    cases hK : evalAssignsKG flatKS W children s.kids s.mems body (seed k s.st) s.kids with
    | none => simp [hK] at hS
    | some ek =>
    obtain ⟨envF', kids'⟩ := ek
    cases hN : regNexts W s.mems body envF' with
    | none => simp [hK, hN] at hS
    | some nexts =>
    cases hM : memNexts W body s.mems envF' with
    | none => simp [hK, hN, hM] at hS
    | some mems' =>
    simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    have hE0 : envF' = E k := by
      have := hE 0 (by simp)
      simpa using this
    obtain ⟨child', cwe', envAt, cres, hc', hk, hin, hout⟩ :=
      linked_consistentKG flatKS W children s.kids s.mems body _ envF' s.kids kids' hwf hnd hK
        mn iname conns hmem
    rw [hc] at hc'
    cases hc'
    -- the child's step, on the final environment
    have hconn : connEnvS (inConns child.outputs conns) envAt (s.kids iname).st =
        connEnvS (inConns child.outputs conns) (E k) (s.kids iname).st := by
      funext n
      simp only [connEnvS]
      split
      · rename_i w hl
        have hcin := lookup_mem hl
        rw [← hE0]
        exact hin _ (List.mem_filter.mp hcin).1 w rfl (hnofb _ hcin w rfl)
      · rfl
    simp only [flatKS] at hk
    rw [hconn] at hk
    cases hst : stepModule cwe child.body (connEnvS (inConns child.outputs conns) (E k)
        (s.kids iname).st) (s.kids iname).mems with
    | none => simp [hst] at hk
    | some rc =>
    obtain ⟨cres', nexts', cmems⟩ := rc
    simp only [hst, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, hks⟩ := hk
    have ih := child_run_of_linked W children body seed E hwf hnd hmem hc hnofb k
      ⟨applyNexts s.st nexts, mems', kids'⟩ rest hR (fun j hj => by
        have := hE (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [this]
        congr 1
        omega)
    obtain ⟨crest, hcr, hcl, hco⟩ := ih
    refine ⟨cres' :: crest, ?_, by simp [hcl], ?_⟩
    · simp only [runModule, hst, Option.bind_eq_bind, Option.bind_some]
      show (runModule cwe child.body _ k (applyNexts (s.kids iname).st nexts') cmems).bind _ = _
      have hkid : kids' iname = ⟨applyNexts (s.kids iname).st nexts', cmems⟩ := hks.symm
      simp only [hkid] at hcr
      rw [hcr]
      rfl
    · intro j hj hj' p hp w hl
      cases j with
      | zero => exact hout p hp w hl
      | succ j => exact hco j (by simpa using hj) (by simpa using hj') p hp w hl

/-- **A design with one-level children, to its emitted Verilog.** Along a
stateful linked run of the shipped module `o` (children stepping their own
modules), the emitted Verilog of `o` runs, from the oracle seeding, to the
run's environments, and the emitted Verilog of every instance's child,
fed at each cycle with the run's values on its input connections, runs to
environments whose output ports carry exactly the values the oracle
seeding gave the parent: the emitted texts of parent and children,
connected, run as the linked run. -/
theorem design_sv_run (children : String → Option (Module × WEnv))
    (hcwe : ∀ mn child cwe, children mn = some (child, cwe) → cwe = declWidth child)
    {o : Module} {wof : String → Option Nat}
    (hwf : linkedWF children o.body = true) (hnd : (instNames o.body).Nodup)
    (hok : o.body.all seqStmtOkI = true)
    (hsv : seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwag : ∀ n ∈ seqNames o.body, declWidth o n = Tools.SVParser.EmitSem.weOf wof n)
    {seed : Nat → (String → Nat) → Env} {T : Nat} {s : KState KidState} {envs : List Env}
    (hrun : runModuleTG flatKS (declWidth o) children o.body seed T s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      Bounded (Tools.SVParser.EmitSem.weOf wof)
        (oracle children o.body (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) seed k st))
    (hst : Bounded (Tools.SVParser.EmitSem.weOf wof) s.st) :
    (∃ pairs regs mprog,
      emitAssigns wof o.body = some pairs ∧ emitRegs wof o.body = some regs ∧
      emitMemWrites wof o.body = some mprog ∧
      runModuleSV wof pairs regs mprog
        (oracle children o.body (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) seed) T
        s.st s.mems = some envs) ∧
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      children mn = some (child, cwe) →
      (∀ c ∈ inConns child.outputs conns, ∀ w, c.2 = .ref w →
        w ∉ instOutWires child.outputs conns) →
      ∀ wofC : String → Option Nat,
      child.body.all seqStmtOk = true →
      seqCheck wofC (Tools.SVParser.EmitSem.weOf wofC) child.body = true →
      (∀ n ∈ seqNames child.body, declWidth child n = Tools.SVParser.EmitSem.weOf wofC n) →
      (∀ k st, Bounded (Tools.SVParser.EmitSem.weOf wofC) st →
        Bounded (Tools.SVParser.EmitSem.weOf wofC)
          (connEnvS (inConns child.outputs conns) ((envs[T - 1 - k]?).getD (fun _ => 0)) st)) →
      Bounded (Tools.SVParser.EmitSem.weOf wofC) (s.kids iname).st →
      ∃ pairs regs mprog cenvs,
        emitAssigns wofC child.body = some pairs ∧ emitRegs wofC child.body = some regs ∧
        emitMemWrites wofC child.body = some mprog ∧
        runModuleSV wofC pairs regs mprog
          (fun k st => connEnvS (inConns child.outputs conns) ((envs[T - 1 - k]?).getD (fun _ => 0)) st)
          T (s.kids iname).st (s.kids iname).mems = some cenvs ∧
        cenvs.length = envs.length ∧
        ∀ j (hj : j < envs.length) (hj' : j < cenvs.length), ∀ p ∈ child.outputs, ∀ w,
          conns.lookup p.name = some (.ref w) → (envs[j]'hj) w = (cenvs[j]'hj') p.name := by
  refine ⟨linked_sv_run flatKS children hwf hok hsv hwag hrun hseedB hst, ?_⟩
  intro mn iname conns hmem child cwe hc hnofb wofC hokC hsvC hwagC hseedC hstC
  have hlen := runModuleTG_length flatKS _ children o.body seed T s envs hrun
  have hE : ∀ j (hj : j < envs.length),
      envs[j] = (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) (T - 1 - j) := by
    intro j hj
    simp only
    rw [show T - 1 - (T - 1 - j) = j by omega]
    simp [hj]
  obtain ⟨cenvs, hcr, hcl, hco⟩ := child_run_of_linked (declWidth o) children o.body seed
    (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) hwf hnd hmem hc hnofb T s envs hrun hE
  have hcw := hcwe mn child cwe hc
  subst hcw
  have hwagC' : ∀ n ∈ seqNames child.body,
      declWidth child n = Tools.SVParser.EmitSem.weOf wofC n := hwagC
  obtain ⟨pairs, regs, mprog, hA, hRg, hMw, hSV⟩ :=
    Tools.ShippingSeqSVSoundness.seq_run_to_sv hokC hsvC hwagC' _ hseedC hstC hcr
  exact ⟨pairs, regs, mprog, cenvs, hA, hRg, hMw, hSV, hcl, hco⟩

/-- **A shipped module's linked run, to its emitted Verilog, under decidable
facts.** The oracle seeding's bound is derived: the instance-driven wires are
extracted inputs of `o` whose values fit `o`'s widths along the run
(`fitX_of_run`: children within their port widths, `instOutWidthsOk`), no
wider than the emitter's. -/
theorem linked_sv_of_run {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    {o : Module} {wof : String → Option Nat} (Inv : Module → σ → Prop)
    (hKSb : KSBoundedIn children KS o.body Inv)
    (hwf : linkedWF children o.body = true) (hnd : (instNames o.body).Nodup)
    (hIW : instOutWidthsOk children (declWidth o) o.body = true)
    (hOut : ∀ w ∈ bodyInstOuts children o.body, w ∈ (Sparkle.IR.HierCheck.openIns o).map (·.name))
    (hOW : ∀ w ∈ bodyInstOuts children o.body, declWidth o w ≤ Tools.SVParser.EmitSem.weOf wof w)
    (hok : o.body.all seqStmtOkI = true)
    (hsv : seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwag : ∀ n ∈ seqNames o.body, declWidth o n = Tools.SVParser.EmitSem.weOf wof n)
    (ins : Nat → String → Nat)
    (hinsW : ∀ t x, x ∈ o.inputs.map (·.name) → ins t x < 2 ^ Tools.SVParser.EmitSem.weOf wof x)
    {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth o) children o.body (seedIn o ins) T s = some envs)
    (hinv : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      children mn = some (child, cwe) → Inv child (s.kids iname))
    (hstX : ∀ x ∈ (Sparkle.IR.HierCheck.openIns o).map (·.name), x ∉ bodyInstOuts children o.body →
      s.st x < 2 ^ declWidth o x)
    (hst : Bounded (Tools.SVParser.EmitSem.weOf wof) s.st) :
    ∃ pairs regs mprog,
      emitAssigns wof o.body = some pairs ∧ emitRegs wof o.body = some regs ∧
      emitMemWrites wof o.body = some mprog ∧
      runModuleSV wof pairs regs mprog
        (oracle children o.body (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) (seedIn o ins)) T
        s.st s.mems = some envs := by
  have hfit := fitX_of_run KS children o Inv hKSb ins hwf hnd hIW T s envs hrun hinv hstX
  apply linked_sv_run KS children hwf hok hsv hwag hrun _ hst
  intro k st hb n
  simp only [oracle, seedOuts]
  split
  · rename_i hO
    have hO' : n ∈ bodyInstOuts children o.body := by simpa [List.contains_eq_mem] using hO
    cases hj : envs[T - 1 - k]? with
    | none => simp only [Option.getD_none]; exact Nat.two_pow_pos _
    | some e =>
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
      simp only [Option.getD_some]
      exact Nat.lt_of_lt_of_le (hfit _ hlt n (hOut n hO'))
        (Nat.pow_le_pow_right (by omega) (hOW n hO'))
  · exact Tools.ShippingSeqSVSoundness.seedIn_bounded hinsW k st hb n

end Tools.ShippingHierSVRun
