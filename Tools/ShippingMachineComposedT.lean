import Tools.ShippingMachineAuto
import Tools.ShippingHierState

/-! # A state machine composed with stateful children

`MachineTraceLB` is a machine's endpoint in the OPEN view: its instances'
outputs are free inputs, seeded with the calls' source values. This file
turns it into the STATEFUL LINKED run (`runModuleT`, each instance stepping
its own child with its own registers and memories): from the same seed, the
linked run produces the open run's environments — hence the source's
outputs — given that each child's own run, fed with the open run's values
on its input wires, shows the open run's values on its output wires. That
premise is stated over the open run's environments and their known values
(outputs and `let` wires), which is what a child's own theorem discharges. -/
namespace Tools.ShippingMachineComposedT
open Lean Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked
open Tools.ShippingHierState
open Tools.ShippingEntrySoundness (weOf)

/-- **The stateful linked run of a machine with its children.** -/
theorem runT_of_traceLB {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module}
    {dsn : Sparkle.IR.AST.Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (h : MachineTraceLB declName d m dsn dom src ext extB lsrc)
    (hwf : linkedWF (childMap dsn.modules) m.body = true) (hnd : (instNames m.body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body → ∀ child cwe,
      childMap dsn.modules mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      ∃ lets : List String, lets.length = d.letBs.length ∧
      MachineWired declName d.shape ids cache m dsn regs lets ∧
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
        (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KidState),
        (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
          (fun j => (extB i bools bits j).val (T - 1 - t))
          (fun j n => (ext i bools bits j n).val (T - 1 - t))
          (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        -- each child's own run on the open run's values
        (∀ envs : List Env, runModule (weOf m) m.body seed T st0 mems = some envs →
          envs.length = T →
          (∀ j (hj : j < envs.length) (q : Nat) (name : String) (g : Nat → Nat),
            lets[q]? = some name → (lsrc i bools bits)[q]? = some g → q < d.ls.length →
            (envs[j]'hj) name = g j) →
          ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body → ∃ child cwe cenvs,
            childMap dsn.modules mn = some (child, cwe) ∧
            runModule cwe child.body
              (fun t cst => connEnvS (inConns child.outputs conns)
                (envs.getD (T - 1 - t) (fun _ => 0)) cst)
              T (kids iname).st (kids iname).mems = some cenvs ∧
            ∀ j, j < T → ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
              (cenvs[j]?).map (· p.name) = some ((envs.getD j (fun _ => 0)) w)) →
        ∃ envs, runModuleT (weOf m) (childMap dsn.modules) m.body seed T st0 mems kids =
            some envs ∧ envs.length = T ∧
          ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems kids hin hregs hrst hinit hkids
  obtain ⟨envs, hrun, hlen, hobs, hlets⟩ := H i bools bits T seed st0 mems hin hregs hrst hinit
  refine ⟨envs, ?_, hlen, hobs⟩
  let P : Nat → Env := fun t => envs.getD (T - 1 - t) (fun _ => 0)
  apply runModuleT_of_childRuns (weOf m) (childMap dsn.modules) m.body seed seed hwf hnd hnofb
    (fun t st mems envF hF => seed_seedOuts hwf hF) P T st0 mems kids envs hrun
  · intro j hj
    have hj' : j < envs.length := by rw [hlen]; exact hj
    show envs[j]? = some (envs.getD (T - 1 - (T - 1 - j)) (fun _ => 0))
    rw [show T - 1 - (T - 1 - j) = j by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj']
    rfl
  · intro mn iname conns hm
    obtain ⟨child, cwe, cenvs, hc, hcrun, hcobs⟩ := hkids envs hrun hlen hlets mn iname conns hm
    refine ⟨child, cwe, cenvs, hc, hcrun, fun j hj p hp w hw => ?_⟩
    rw [hcobs j hj p hp w hw]
    show some ((envs.getD j (fun _ => 0)) w) = some ((envs.getD (T - 1 - (T - 1 - j)) _) w)
    rw [show T - 1 - (T - 1 - j) = j by omega]

/-! ## The run's conditions from the wiring -/

theorem instNames_eq : ∀ body : List Stmt, instNames body = body.filterMap instNameOf
  | [] => rfl
  | .inst _ i _ :: rest => by simp [instNames, instNameOf, instNames_eq rest]
  | .assign .. :: rest => by simp [instNames, instNameOf, instNames_eq rest]
  | .register .. :: rest => by simp [instNames, instNameOf, instNames_eq rest]
  | .memory .. :: rest => by simp [instNames, instNameOf, instNames_eq rest]

/-- The stateful linked run's conditions, for a machine with structure /
sequential calls, from its wiring. -/
theorem instOutWires_eq (outs : List Port) (conns : List (String × Sparkle.IR.AST.Expr)) :
    instOutWires outs conns = instOutWiresOf outs conns := by
  unfold instOutWires instOutWiresOf
  rfl

theorem wired_runT_conds {declName : Name} {shape : Sparkle.Compiler.Elab.MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Sparkle.IR.AST.Module}
    {dsn : Sparkle.IR.AST.Design} {regs lets : List String}
    (wired : MachineWired declName shape ids cache m dsn regs lets)
    (hfe : shape.instFields ≠ []) :
    linkedWF (childMap dsn.modules) m.body = true ∧ (instNames m.body).Nodup ∧
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body → ∀ child cwe,
      childMap dsn.modules mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns := by
  obtain ⟨_, _, _, _, _, _, hlink, _, _, _, _, _, _, hnames⟩ := wired
  obtain ⟨hnd, hfeed⟩ := hnames hfe
  refine ⟨by rw [← linkedOk_eq]; exact hlink, by rw [instNames_eq]; exact hnd, ?_⟩
  intro mn iname conns hm child cwe hc c hcin w hw
  have hmod : moduleByName dsn.modules mn = some child := by
    unfold childMap at hc
    cases hb : moduleByName dsn.modules mn with
    | none => rw [hb] at hc; cases hc
    | some c' => rw [hb] at hc; simp only [Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hc; rw [hc.1]
  unfold noSelfFeed at hfeed
  have hst := List.all_eq_true.mp hfeed _ hm
  simp only [hmod] at hst
  have hc' := List.all_eq_true.mp hst c hcin
  rw [hw] at hc'
  rw [instOutWires_eq]
  simpa using hc'

end Tools.ShippingMachineComposedT
