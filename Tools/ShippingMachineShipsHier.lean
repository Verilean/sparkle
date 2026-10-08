import Tools.ShippingHierOptRun
import Tools.ShippingMachineShipsW
import Tools.ShippingMachineCallsLinkedTN

/-! # A machine with instances, at the full entry and the optimizer

The composed theorem of a machine with sequential / memory children
(`machine_linkedT_callsN`, generated as `f.machine_composedT`) states the
stateful linked run of the CORE module. The full entry returns the module
after the zero-width cleanup (the identity on machine modules) and the
checked merge — the identity on an instance-bearing body (its validator
keeps assignments as assignments; `refineCheck` rejects instance
statements) — and the printer is given `checkedOptimize` of it, which on an
instance-bearing module keeps the optimizer's output only when
`hierRefineCheck` accepts it (`hierRefineCheck_linked`). -/
namespace Tools.ShippingMachineShipsHier
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

theorem validateMerge_go_assign {wOf : String → Nat} {allLhs : List String} :
    ∀ (old new : List Stmt) (st : Sparkle.IR.RegDedup.MergeCheck),
      Sparkle.IR.RegDedup.validateMerge.go wOf allLhs st old new = true →
      old.all isAssign = true → new.all isAssign = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hgo, _ => by simp [Sparkle.IR.RegDedup.validateMerge.go] at hgo
  | _ :: _, [], _, hgo, _ => by simp [Sparkle.IR.RegDedup.validateMerge.go] at hgo
  | a :: as, b :: bs, st, hgo, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    cases a with
    | assign l e =>
      simp only [Sparkle.IR.RegDedup.validateMerge.go] at hgo
      split at hgo
      · rename_i st' hstep
        obtain ⟨e', rfl, -⟩ := Tools.ShippingPostSoundness.validateStep_shape hstep
        simp only [List.all_cons, isAssign, Bool.true_and]
        exact validateMerge_go_assign as bs st' hgo hs.2
      · cases hgo
    | _ => simp [isAssign] at hs

/-- A module with an instance statement. -/
def hasInst (m : Sparkle.IR.AST.Module) : Prop := ∃ mn iname conns, Stmt.inst mn iname conns ∈ m.body

theorem hasInst_of_hierBinds {m : Sparkle.IR.AST.Module} (h : hierBinds m = true) : hasInst m := by
  simp only [hierBinds, hierGate, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨st, hst, hi⟩, -⟩, -⟩ := h
  cases st with
  | inst mn iname conns => exact ⟨mn, iname, conns, hst⟩
  | _ => simp at hi

theorem not_all_assign {m : Sparkle.IR.AST.Module} (h : hasInst m) : m.body.all isAssign = false := by
  obtain ⟨mn, iname, conns, hm⟩ := h
  exact List.all_eq_false.mpr ⟨_, hm, by simp [isAssign]⟩

theorem not_all_seqOk {m : Sparkle.IR.AST.Module} (h : hasInst m) : m.body.all seqStmtOk = false := by
  obtain ⟨mn, iname, conns, hm⟩ := h
  exact List.all_eq_false.mpr ⟨_, hm, by simp [seqStmtOk]⟩

/-- **The checked merge keeps an instance-bearing module.** -/
theorem mergeChecked_inst {r b : Sparkle.IR.AST.Module} (hb : b = mergeChecked r) (hI : hasInst b) : b = r := by
  unfold mergeChecked at hb
  dsimp only at hb
  split at hb
  · -- an assignment-only body: the merge's statements are assignments
    rename_i hall
    exfalso
    have hb' : b.body.all isAssign = true := by
      rw [hb]
      unfold Sparkle.IR.RegDedup.mergeDuplicates
      simp only [hall, if_true]
      split
      · rename_i hv
        exact validateMerge_go_assign _ _ _ hv hall
      · exact hall
    rw [not_all_assign hI] at hb'
    cases hb'
  · split at hb
    · rename_i _ hrc
      exfalso
      have := Tools.ShippingMachineShipping.refineCheck_stmtOk_o hrc
      rw [← hb, not_all_seqOk hI] at this
      cases this
    · exact hb

theorem simpleBody_inst {m : Sparkle.IR.AST.Module} (h : hasInst m) : simpleBody m = false := by
  obtain ⟨mn, iname, conns, hm⟩ := h
  unfold simpleBody
  exact List.all_eq_false.mpr ⟨_, hm, by simp⟩

/-- A composed theorem's statement: the stateful linked run (children
stepping by `KS dsn`, from states satisfying `Reset m dsn`) of the core
module `m` in its design `dsn` shows the source. `machine_linkedT_calls`
(`f.machine_composedT`) states it for the one-level step (`composedG_of_T`),
`machine_linkedT_callsN` for depth `n`. -/
def ComposedG {σ : Type} (KS : Design → KStep σ)
    (Reset : Sparkle.IR.AST.Module → Design → (String → σ) → Prop)
    (declName : Name) (d : MachineData) (kD : Nat)
    (m : Sparkle.IR.AST.Module) (dsn : Design) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
      (kids : String → σ),
      (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t))
        (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      Reset m dsn kids →
      ∃ envs, runModuleTG (KS dsn) (Tools.ShippingEntrySoundness.weOf m)
          (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j

/-- **A machine with instances, at the full entry and the optimizer.** From
its wired endpoint (`soundL`, for the cleanup facts) and its composed theorem
(`composed`), a run of the full entry returns a module `b` whose shipped
optimization `checkedOptimize b`, in the stateful linked semantics over the
children of the core design, shows the source — when the optimizer check
binds on `b` (`hierBinds`) and the design facts of `hierRefineCheck_linked`
hold (decidable on the run's modules), and the children's steps keep their
outputs within their ports' widths. -/
theorem machine_ships_hier {σ : Type} (KS : Design → KStep σ) (hloc : ∀ D, KSLocal (KS D))
    (Reset : Sparkle.IR.AST.Module → Design → (String → σ) → Prop)
    (Bnd : Sparkle.IR.AST.Module → Design → Prop)
    {declName : Name} (d : MachineData) {kD : Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceLB declName d m design dom src ext extB lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      Bnd m design → Tools.ConeFold.memFree m.body →
      ComposedG KS Reset declName d kD m design dom src ext extB)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (hierBinds b = true →
        -- the design facts (decidable on the run's modules)
        linkedWF (childMap D.modules) b.body = true →
        linkedWF (childMap D.modules) (checkedOptimize b).body = true →
        (instNames b.body).Nodup → (instNames (checkedOptimize b).body).Nodup →
        (∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → ∀ child cwe,
          childMap D.modules mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
            c.2 = .ref w → w ∉ instOutWires child.outputs conns) →
        (∀ w ∈ bodyInstOuts (childMap D.modules) b.body, w ∈ (openIns b).map (·.name)) →
        instOutWidthsOk (childMap D.modules) (declWidth b) b.body = true →
        "rst" ∈ b.inputs.map (·.name) →
        -- the run boundary of the children
        Bnd raw D →
        -- the children's outputs within their ports' widths
        KSBounded (KS D) →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → σ),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            Reset raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            ∃ envsO, runModuleTG (KS D) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j) := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  have hL := soundL hcore entry closes
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, _, _, _, _, _, hclean⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hclean houtTy
  refine ⟨raw, D, hpost, ?_⟩
  intro hbind hwfB hwfO hndB hndO hnofb hOutM hIW hrstIn hBnd hKSb
  have hI := hasInst_of_hierBinds hbind
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · exact mergeChecked_inst h hI
  have hbB : b.body = raw.body := by rw [hbr]; exact hb
  have hbW : declWidth b = Tools.ShippingEntrySoundness.weOf raw := by rw [hbr]; exact hw
  have hbI : b.inputs = raw.inputs := by rw [hbr]; exact hi
  have hbO : b.outputs = raw.outputs := by rw [hbr]; exact ho
  have hmf : Tools.ConeFold.memFree raw.body := by
    rw [← hbB]; exact memFree_of_linkedWF _ hwfB
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := composed hcore entry closes hBnd hmf
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrstZ hclk hinit hreset hinsFit hstX hstR
  have hrst : ∀ t st, seedIn b ins t st "rst" = 0 := by
    intro t st
    simp only [seedIn, List.contains_eq_mem, decide_eq_true hrstIn, if_true]
    exact hrstZ t
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T (seedIn b ins) st0 mems kids hsrc hpass hrst
    hclk hinit hreset
  have hrunB : runModuleTG (KS D) (declWidth b) (childMap D.modules) b.body
      (seedIn b ins) T ⟨st0, mems, kids⟩ = some envs := by
    rw [hbW, hbB]; exact hrun
  -- the optimizer: checked on the extracted interface, or not applied
  have hopt : checkedOptimize b = (if hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b))
      then deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
    unfold checkedOptimize
    simp only [simpleBody_inst hI, not_all_seqOk hI, hbind, Bool.false_eq_true, if_false, if_true]
  have houtSrc : ∀ (k : Nat) (o : OutField), d.shape.layout.outs[k]? = some o →
      o.name ∈ b.outputs.map (·.name) := by
    intro k o hk
    rw [hbO, houts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩, rfl⟩
  by_cases hacc : hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
  · rw [hopt, if_pos hacc] at hwfO hndO hnofb ⊢
    obtain ⟨-, -, envsO, hrunO, hlenO, hcorr⟩ := hierRefineCheck_linked
      (KS D) (hloc D) (childMap D.modules) hacc
      hwfB hwfO hndB hndO hnofb hOutM ins hinsFit hrstIn hrstZ hrunB
      (fitX_of_run _ hKSb (childMap D.modules) b ins hwfB hndB hIW T _ envs hrunB hstX) hstR
    refine ⟨envsO, hrunO, by omega, ?_⟩
    intro j hj k o f hk hf
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (houtSrc k o hk)
    rw [← hpn, hcorr p hp j hj (by omega), hpn]
    exact hobs j (by omega) k o f hk hf
  · rw [hopt, if_neg hacc]
    exact ⟨envs, hrunB, hlen, hobs⟩

/-! ## The one-level composed theorem in the general form -/

theorem evalAssignsK_flat (we : WEnv) (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (kids : String → KidState) (mems : MEnv) :
    ∀ (body : List Stmt), Tools.ConeFold.memFree body → ∀ (env : Env) (acc : String → KidState),
      evalAssignsK we children kids mems body env acc =
        evalAssignsKG flatKS we children kids mems body env acc
  | [], _, _, _ => rfl
  | .assign l r :: rest, hm, env, acc => by
    simp only [evalAssignsK, evalAssignsKG]
    cases evalExpr we env r with
    | none => rfl
    | some v =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      exact evalAssignsK_flat we children kids mems rest hm _ acc
  | .inst mn iname conns :: rest, hm, env, acc => by
    simp only [evalAssignsK, evalAssignsKG, flatKS]
    cases children mn with
    | none => rfl
    | some cp =>
      obtain ⟨child, cwe⟩ := cp
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases stepModule cwe child.body
          (Tools.ShippingHierarchySoundness.connEnvS (inConns child.outputs conns) env (kids iname).st)
          (kids iname).mems with
      | none => rfl
      | some r =>
        obtain ⟨cres, nexts, cmems⟩ := r
        simp only [Option.map_some, Option.bind_some]
        exact evalAssignsK_flat we children kids mems rest hm _ _
  | .register .. :: rest, hm, env, acc => by
    simp only [evalAssignsK, evalAssignsKG]
    exact evalAssignsK_flat we children kids mems rest hm env acc
  | .memory .. :: _, hm, _, _ => by simp [Tools.ConeFold.memFree] at hm

theorem runModuleT_flat (we : WEnv) (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (body : List Stmt) (hm : Tools.ConeFold.memFree body) (seed : Nat → (String → Nat) → Env) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv) (kids : String → KidState),
      runModuleT we children body seed T st mems kids =
        runModuleTG flatKS we children body seed T ⟨st, mems, kids⟩
  | 0, _, _, _ => rfl
  | k + 1, st, mems, kids => by
    simp only [runModuleT, runModuleTG, stepModuleT, stepModuleTG]
    rw [evalAssignsK_flat we children kids mems body hm]
    cases evalAssignsKG flatKS we children kids mems body (seed k st) kids with
    | none => rfl
    | some ek =>
      obtain ⟨envF, kids'⟩ := ek
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases regNexts we mems body envF with
      | none => rfl
      | some nexts =>
        simp only [Option.bind_some]
        cases memNexts we body mems envF with
        | none => rfl
        | some mems' =>
          simp only [Option.bind_some]
          rw [runModuleT_flat we children body hm seed k]

/-- The children's reset in the one-level composed theorem: memories and
read latches zero, registers at their reset values. -/
def Reset1 (m : Sparkle.IR.AST.Module) (dsn : Design) (kids : String → KidState) : Prop :=
  (∀ iname n a, (kids iname).mems n a = 0) ∧ (∀ iname, (kids iname).st "out_rdata" = 0) ∧
  (∀ (iname : String) (mc : Sparkle.IR.AST.Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
    moduleByName dsn.modules mc.name = some mc →
    ∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body → (kids iname).st r = init.toNat)

/-- `machine_linkedT_calls`'s conclusion (`f.machine_composedT`) is the
general statement at the one-level step, on a memory-free core body. -/
theorem composedG_of_T {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (h : ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
      ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        regs.Nodup ∧ regs.length = d.ss.length ∧
        ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
          (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
          (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
          (kids : String → KidState),
          (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
            (fun j => (extB i bools bits j).val (T - 1 - t))
            (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
          (∀ t st r, r ∈ regs → seed t st r = st r) →
          (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
          (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
            d.shape.layout.slots[k]? = some f → st0 r = f.init) →
          (∀ iname n a, (kids iname).mems n a = 0) → (∀ iname, (kids iname).st "out_rdata" = 0) →
          (∀ (iname : String) (mc : Sparkle.IR.AST.Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
            moduleByName dsn.modules mc.name = some mc →
            ∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body →
              (kids iname).st r = init.toNat) →
          ∃ envs, runModuleT (Tools.ShippingEntrySoundness.weOf m) (childMap dsn.modules) m.body
              seed T st0 mems kids = some envs ∧
            envs.length = T ∧
            ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
              d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
              (envs[j]'hj) o.name = f j)
    (hm : Tools.ConeFold.memFree m.body) :
    ComposedG (fun _ => flatKS) Reset1 declName d kD m dsn dom src ext extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk hinit ⟨h1, h2, h3⟩
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T seed st0 mems kids hin hpass hrst hclk hinit
    h1 h2 h3
  refine ⟨envs, ?_, hlen, hobs⟩
  rw [← runModuleT_flat _ _ _ hm]
  exact hrun

/-- The children's reset for memory-only parents: memories and read latches
zero. -/
def ResetM (_m : Sparkle.IR.AST.Module) (_dsn : Design) (kids : String → KidState) : Prop :=
  (∀ iname n a, (kids iname).mems n a = 0) ∧ (∀ iname, (kids iname).st "out_rdata" = 0)

/-- `machine_linkedT_mem`'s conclusion (`f.machine_composedT` of a parent
whose calls are memory reads) in the general form. -/
theorem composedG_of_Tmem {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (h : ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
      ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        regs.Nodup ∧ regs.length = d.ss.length ∧
        ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
          (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
          (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
          (kids : String → KidState),
          (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
            (fun j => (extB i bools bits j).val (T - 1 - t))
            (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
          (∀ t st r, r ∈ regs → seed t st r = st r) →
          (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
          (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
            d.shape.layout.slots[k]? = some f → st0 r = f.init) →
          (∀ iname n a, (kids iname).mems n a = 0) → (∀ iname, (kids iname).st "out_rdata" = 0) →
          ∃ envs, runModuleT (Tools.ShippingEntrySoundness.weOf m) (childMap dsn.modules) m.body
              seed T st0 mems kids = some envs ∧
            envs.length = T ∧
            ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
              d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
              (envs[j]'hj) o.name = f j)
    (hm : Tools.ConeFold.memFree m.body) :
    ComposedG (fun _ => flatKS) ResetM declName d kD m dsn dom src ext extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk hinit ⟨h1, h2⟩
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T seed st0 mems kids hin hpass hrst hclk hinit
    h1 h2
  refine ⟨envs, ?_, hlen, hobs⟩
  rw [← runModuleT_flat _ _ _ hm]
  exact hrun

end Tools.ShippingMachineShipsHier
