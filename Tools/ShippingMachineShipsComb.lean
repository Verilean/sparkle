import Tools.ShippingMachineShipsW
import Tools.ShippingOptSoundness
import Tools.ShippingPostSoundness

/-! # A combinational machine to its emitted Verilog, from its wiring

`machine_ships_wired` covers machines with registers (the optimizer's
output kept as a `refineCheck` refinement). A machine WITHOUT slots and
calls compiles to an assignment-only module: the full entry's merge is the
self-validating `mergeDuplicates` (`mergeDuplicates_sound`: the same
environment), and on a body of the simple shape `checkedOptimize` keeps the
optimizer's output only when `optCheck` accepts it (`checkedOptimize_sound`:
the same outputs). Each cycle of such a module is one evaluation of its
assignments (no register, no memory), so per-cycle facts lift to the run
(`runModule_assigns`); the emitted Verilog runs as the module
(`seq_run_to_sv`).

A combinational module has no reset port, so the statement seeds every
cycle with the input values and the reset name low (`seedR`); the state is
never written. -/
namespace Tools.ShippingMachineShipsComb
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingPostSoundness Tools.ShippingOptSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Sparkle.IR.RegDedup (declWidth isAssign)

/-- Every cycle's environment: the reset name low, the inputs' values, the
state elsewhere. -/
def seedR (m : Sparkle.IR.AST.Module) (ins : Nat → String → Nat) :
    Nat → (String → Nat) → Env :=
  fun t st n => if n = "rst" then 0
    else if (m.inputs.map (·.name)).contains n then ins t n else st n

theorem regNexts_assigns {we : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all isAssign = true → ∀ env, regNexts we mems body env = some []
  | [], _, _ => rfl
  | st :: rest, h, env => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases st with
    | assign l e => simp only [regNexts]; exact regNexts_assigns h.2 env
    | _ => simp [isAssign] at h

theorem memNexts_assigns {we : WEnv} :
    ∀ {body : List Stmt}, body.all isAssign = true → ∀ mems env, memNexts we body mems env = some mems
  | [], _, _, _ => rfl
  | st :: rest, h, mems, env => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases st with
    | assign l e => simp only [memNexts]; exact memNexts_assigns h.2 mems env
    | _ => simp [isAssign] at h

theorem applyNexts_nil (st : String → Nat) : applyNexts st [] = st := by
  funext n; simp [applyNexts]

/-- **An assignment-only run follows its cycles.** If every cycle's
evaluation of `b₁` (on an environment the seed can give) has a matching
evaluation of `b₂`, agreeing on `P`, then a run of `b₁` has a run of `b₂`
of the same length, agreeing on `P` at every cycle. -/
theorem runModule_assigns {we₁ we₂ : WEnv} {b₁ b₂ : List Stmt}
    (h₁ : b₁.all isAssign = true) (h₂ : b₂.all isAssign = true)
    {seed : Nat → (String → Nat) → Env} {P : String → Prop} (Q : Env → Prop)
    (hQ : ∀ k st, Q (seed k st))
    (hstep : ∀ mems init e, Q init → evalAssigns we₁ mems b₁ init = some e →
      ∃ e', evalAssigns we₂ mems b₂ init = some e' ∧ ∀ x, P x → e' x = e x) :
    ∀ T st mems envs, runModule we₁ b₁ seed T st mems = some envs →
      ∃ envs', runModule we₂ b₂ seed T st mems = some envs' ∧ envs'.length = envs.length ∧
        ∀ j (hj : j < envs'.length) (hj' : j < envs.length) x, P x →
          (envs'[j]'hj) x = (envs[j]'hj') x
  | 0, _, _, envs, h => by
    simp only [runModule, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl, fun j hj => by simp at hj⟩
  | k + 1, st, mems, envs, h => by
    simp only [runModule, stepModule] at h ⊢
    cases he : evalAssigns we₁ mems b₁ (seed k st) with
    | none => simp [he] at h
    | some e =>
      obtain ⟨e', he', hP⟩ := hstep mems (seed k st) e (hQ k st) he
      simp only [he, he', regNexts_assigns h₁, regNexts_assigns h₂, memNexts_assigns h₁,
        memNexts_assigns h₂, Option.bind_eq_bind, Option.bind_some, applyNexts_nil] at h ⊢
      cases hr : runModule we₁ b₁ seed k st mems with
      | none => simp [hr] at h
      | some rest =>
        simp only [hr, Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨rest', hr', hl, hc⟩ :=
          runModule_assigns h₁ h₂ Q hQ hstep k st mems rest hr
        refine ⟨e' :: rest', by simp [hr'], by simp [hl], ?_⟩
        intro j hj hj' x hx
        cases j with
        | zero => exact hP x hx
        | succ j => exact hc j (by simpa using hj) (by simpa using hj') x hx

theorem simpleBody_assigns {m : Sparkle.IR.AST.Module} (h : simpleBody m = true) :
    m.body.all isAssign = true := by
  unfold simpleBody at h
  apply List.all_eq_true.mpr
  intro st hst
  have := List.all_eq_true.mp h st hst
  cases st <;> simp_all [isAssign]

theorem normBody_assigns {we : WEnv} {ins : List String} :
    ∀ (defs : List (String × Sparkle.IR.AST.Expr)) (body : List Stmt) r,
      normBody we ins defs body = some r → body.all isAssign = true
  | _, [], _, _ => rfl
  | defs, st :: rest, r, h => by
    cases st with
    | assign l e =>
      simp only [normBody] at h
      cases he : normE we ins defs e with
      | none => simp [he] at h
      | some e' =>
        simp only [he, Option.bind_eq_bind, Option.bind_some] at h
        simp only [List.all_cons, isAssign, Bool.true_and]
        exact normBody_assigns _ rest r h
    | _ => simp [normBody] at h

theorem optCheck_assigns {m o : Sparkle.IR.AST.Module} (h : optCheck m o = true) :
    o.body.all isAssign = true := by
  have h := (Bool.and_eq_true_iff.mp h).1
  unfold optCheckCore at h
  simp only at h
  split at h
  · rename_i dm dO _ ho
    exact normBody_assigns _ _ _ ho
  · cases h

theorem checkedOptimize_assigns {m : Sparkle.IR.AST.Module} (hs : simpleBody m = true) :
    (checkedOptimize m).body.all isAssign = true := by
  unfold checkedOptimize
  simp only [hs, if_true]
  split
  · rename_i hchk
    simp only [Bool.and_eq_true] at hchk
    exact optCheck_assigns hchk.1
  · exact simpleBody_assigns hs

theorem assigns_seqOk {body : List Stmt} (h : body.all isAssign = true) :
    body.all seqStmtOk = true := by
  apply List.all_eq_true.mpr
  intro st hst
  have := List.all_eq_true.mp h st hst
  cases st <;> simp_all [isAssign, seqStmtOk]

/-- **A combinational machine at the shipped module and its emitted
Verilog.** For every input stream that fits the core module's input widths
and the emitter's, the optimized module `o` runs on `seedR` and its emitted
Verilog runs to the same environments, and every output port shows the
source at every cycle. -/
def MachineShipsComb (declName : Name) (d : MachineData) (raw o : Sparkle.IR.AST.Module)
    (wof : String → Option Nat) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
        (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
        (seedR raw ins t st)) →
      (∀ t x, x ∈ raw.inputs.map (·.name) → ins t x < 2 ^ declWidth raw x) →
      (∀ t x, x ∈ raw.inputs.map (·.name) → ins t x < 2 ^ Tools.SVParser.EmitSem.weOf wof x) →
      Bounded (Tools.SVParser.EmitSem.weOf wof) st0 →
      ∃ envsO,
        runModule (declWidth o) o.body (seedR raw ins) T st0 mems = some envsO ∧
        (∃ pairs regs' mprog,
          Tools.SVParser.EmitSem.emitAssigns wof o.body = some pairs ∧
          Tools.SVParser.EmitSem.emitRegs wof o.body = some regs' ∧
          Tools.SVParser.EmitSem.emitMemWrites wof o.body = some mprog ∧
          Tools.SVParser.EmitSem.runModuleSV wof pairs regs' mprog
            (seedR raw ins) T st0 mems = some envsO) ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
          (envsO[j]'hj) q.name = f j

theorem seedR_bounded {m : Sparkle.IR.AST.Module} {ins : Nat → String → Nat} {we : WEnv}
    (hins : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ we x) :
    ∀ t st, Bounded we st → Bounded we (seedR m ins t st) := by
  intro t st hst n
  simp only [seedR]
  split
  · exact Nat.two_pow_pos _
  · split
    · rename_i hc
      exact hins t n (by simpa [List.contains_eq_mem] using hc)
    · exact hst n

/-- **A combinational machine at the full entry, to the emitted Verilog,
from its wiring.** `soundL` is the machine's wired endpoint
(`machine_traceL_of_comb`). The cleanup is the identity, the merge is
`mergeDuplicates` (self-validating), the optimizer's output is kept only
when `optCheck` accepts it; what remains is that the shipped body is of the
simple shape (the gate `checkedOptimize` reads) and the emitted-Verilog
check. -/
theorem machine_ships_comb {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots = [])
    (hSS : d.ss.length = 0)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        simpleBody b = true →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShipsComb declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
          (checkedOptimize b) wof dom src := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  have hL := soundL hcore entry closes
  have htr := MachineTraceL.toWith hL
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, _, houts, _, hall, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, _⟩ := hclean hnoI houtTy
  have hallR : raw.body.all isAssign = true := hall hnoI hsl
  refine ⟨raw, hpost, ?_⟩
  intro wof hsB hsv hwag
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost ⊢
  have hall0 : r0.body.all isAssign = true := by rw [hb]; exact hallR
  -- the full entry's module: the cleaned module, or its merge (an
  -- assignment-only body: `mergeDuplicates`, the same environment)
  have hstepB : b.inputs = r0.inputs ∧ b.outputs = r0.outputs ∧ declWidth b = declWidth r0 ∧
      ∀ mems init e, evalAssigns (weOf r0) mems r0.body init = some e →
        evalAssigns (weOf b) mems b.body init = some e := by
    rcases hpost with rfl | rfl
    · exact ⟨rfl, rfl, rfl, fun _ _ _ h => h⟩
    · have hmc : mergeChecked r0 = Sparkle.IR.RegDedup.mergeDuplicates r0 := by
        unfold mergeChecked; simp [hall0]
      rw [hmc]
      obtain ⟨hpi, hpo, hpw⟩ := Sparkle.IR.RegDedup.mergeDuplicates_ports r0
      refine ⟨hpi, hpo, ?_, fun mems init e h => (mergeDuplicates_sound r0 mems init e hall0 h).1⟩
      funext x
      unfold declWidth
      rw [hpw]
  obtain ⟨hinB, houtB, hdwB, hevB⟩ := hstepB
  have hallB : b.body.all isAssign = true := simpleBody_assigns hsB
  have hallO : (checkedOptimize b).body.all isAssign = true := checkedOptimize_assigns hsB
  obtain ⟨ids, nd, len, cache, regs, _, rlen, H⟩ := htr
  have hregs : regs = [] := List.eq_nil_of_length_eq_zero (rlen.trans hSS)
  subst hregs
  refine ⟨ids, nd, len, cache, ?_⟩
  intro i bools bits T ins st0 mems inputs hinsRaw hinsW hst
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T (seedR r0 ins) st0 mems inputs
    (fun _ _ r hr => by simp at hr) (fun _ _ => by simp [seedR])
    (fun _ r _ hr => by simp at hr)
  have hrun0 : runModule (weOf r0) r0.body (seedR r0 ins) T st0 mems = some envs := by
    rw [hb, hw]; exact hrun
  -- the merge: the same environments
  obtain ⟨envsB, hrunB, hlB, hcB⟩ := runModule_assigns hall0 hallB (P := fun _ => True)
    (fun _ => True) (fun _ _ => trivial)
    (fun mems init e _ h => ⟨e, hevB mems init e h, fun _ _ => rfl⟩) T st0 mems envs hrun0
  -- the optimizer: the same outputs
  have hdw0 : declWidth r0 = declWidth raw := hw
  have hQ : ∀ k st, ∀ x ∈ b.inputs.map (·.name), seedR r0 ins k st x < 2 ^ declWidth b x := by
    intro k st x hx
    simp only [seedR]
    split
    · exact Nat.two_pow_pos _
    · split
      · rename_i _ hc
        rw [hdwB]
        exact hinsRaw k x (by simpa [List.contains_eq_mem] using hc)
      · rename_i _ hc
        rw [hinB] at hx
        exact absurd (by simpa [List.contains_eq_mem] using hx) hc
  obtain ⟨envsO, hrunO, hlO, hcO⟩ := runModule_assigns (we₁ := declWidth b)
    (we₂ := declWidth (checkedOptimize b)) hallB hallO
    (P := fun x => x ∈ b.outputs.map (·.name))
    (fun init => ∀ x ∈ b.inputs.map (·.name), init x < 2 ^ declWidth b x) hQ
    (fun mems init e hq h => by
      obtain ⟨envO, hevO, heq, _, _⟩ := checkedOptimize_sound hsB hq h
      refine ⟨envO, hevO, fun x hx => ?_⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact heq p hp) T st0 mems envsB hrunB
  -- the emitted Verilog
  have hwag' : ∀ n ∈ seqNames (checkedOptimize b).body,
      declWidth (checkedOptimize b) n = Tools.SVParser.EmitSem.weOf wof n := by
    intro n hn
    have := List.all_eq_true.mp hwag n hn
    simpa using this
  have hSV := seq_run_to_sv (assigns_seqOk hallO) hsv hwag' (seedR r0 ins)
    (seedR_bounded hinsW) hst hrunO
  refine ⟨envsO, hrunO, hSV, by omega, ?_⟩
  intro j hj k q f hq hf
  have hqn : q.name ∈ b.outputs.map (·.name) := by
    rw [houtB, ho, houts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨q, List.mem_of_getElem? hq, rfl⟩, rfl⟩
  rw [hcO j hj (by omega) q.name hqn, hcB j (by omega) (by omega) q.name trivial]
  exact hobs j (by omega) k q f hq hf

end Tools.ShippingMachineShipsComb
