import Tools.ShippingShipsDesignSVAll
import Tools.ShippingChildInv

/-! # The final goal of the machine route, as a type

A FIXED TYPE to measure progress against (audit §1, G6). Nothing new is
proved about the compiler here. Existing types only.

* `SVConclusion`: what the strongest SV head concludes of one run — copied
  from the conclusion of
  `Tools.ShippingShipsDesignSVAll.ships_design_svN_all`: for every input
  family, every length `T`, inputs and start states under the USE CONDITIONS,
  a closed run of the shipped design's emitted texts exists and shows the
  source, and EVERY closed run from the same seeding and states shows it.
* `RunGoal`: `SVConclusion` for the module a run returned (the core module
  and design existentially, as the heads have them).
* `MachineGoal`: for EVERY run of the full entry on the declaration, under
  the allowed premises only, `RunGoal`.
* `HeadConclusion`: today's head conclusion (the same with the five
  not-allowed premises in front), and `runGoal_of_head`: the head's
  conclusion gives `RunGoal` from exactly those five, each a named
  hypothesis. That lemma is the definition of the gap, not progress.

## Premises: allowed / not allowed

| Premise (of a generated `f.machine_design_svNR{n}_closed`) | In `MachineGoal`? |
|---|---|
| the run `RunsTo (synthesizeCombinational f) … (b, design) w'` | yes — the subject |
| `MachineDefines … f d.shape` | yes — reflection of the declaration |
| `MachineDefines` / `EntryDefines` of every descendant | yes — reflection (`Kids`) |
| `ChildBnd mref cref w` (runtime laws + start world) | yes — trusted base |
| use conditions inside the conclusion: `SourceInputs`, the registers' seeding, `rst = 0`, `clk = 0`, reset values, `Reset raw D kids`, input / start-state width bounds, `Bounded (weS …) st0`, `InvN … (kids iname)` | yes — the environment's |
| `shipsHierCheck (childMap D.modules) b = true` | NO — obligation (G1) |
| `designCheck (childMap D.modules) n (checkedOptimize b) = true` | NO — obligation (G1) |
| `outsCheck (childMap D.modules) n (checkedOptimize b) = true` | NO — obligation (G1; derived by `core_outsCheck_all` once a head exposes its core run) |
| `Bnd raw D` (the children's run boundary) | NO as a premise — must follow from `ChildBnd` and the reflections |
| `Bd b D` (the children's outputs within their widths) | NO — obligation (a `kids…` check in the generated instances) |
| `MachineClosesAt` / `MachineCloses` | NO — obligation (B1–B3) |
| name conditions on `Name.toString` | NO — obligation (N1; proved where `Tools.ShippingNameSep` applies) |
| data checks (`d.ok`, `callsOk`, the body equation) | NO — obligations of the reader (G3); they are discharged per declaration by the generator, not premises of the endpoint |

What this file does NOT do
* It does not say which `Reset` the goal should have: `Reset` is a
  parameter, as in the heads (the registers' and instances' start values).
* `Kids` (the descendants' reflections) is a parameter: their form depends
  on the hierarchy (`MachineDefines` of each descendant, moved to the
  contexts of its own run by `MachineDefines.ctx`).
* The goal is the machine route's; the legacy route has no goal (G2). -/
namespace Tools.ShippingFinalGoal
open Tools.ShippingShipsDesignSV
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- **What the SV head concludes of one run**: under the use conditions, a
closed run of the shipped design's emitted texts exists and shows the source
on every output port at every cycle, and every closed run does. -/
def SVConclusion (n : Nat)
    (Reset : Sparkle.IR.AST.Module → Design → (String → KT n) → Prop)
    (declName : Name) (d : MachineData) (kD : Nat)
    {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
      (kids : String → KT n),
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
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
      Bounded (weS (checkedOptimize b)) st0 →
      (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
        childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) n gc (kids iname)) →
      (∃ envsO,
        DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envsO[j]'hj) o.name = f j)
      ∧ ∀ envs', DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
          envs'.length = T ∧
          ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs'[j]'hj) o.name = f j

/-- **The goal of one run**: the module the full entry returned is the
cleanup (or its checked merge) of a core module whose design has the SV
conclusion — no check, no closing, no name premise. -/
def RunGoal (n : Nat)
    (Reset : Sparkle.IR.AST.Module → Design → (String → KT n) → Prop)
    (declName : Name) (d : MachineData) (kD : Nat)
    {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (b : Sparkle.IR.AST.Module) : Prop :=
  ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
    SVConclusion n Reset declName d kD dom src ext extB b raw D

/-- **The machine route's goal for a declaration**: every run of the full
entry, under the allowed premises only — the declaration's reflection, the
descendants' reflections (`Kids`), the runtime laws at the start world. -/
def MachineGoal (n : Nat)
    (Reset : Sparkle.IR.AST.Module → Design → (String → KT n) → Prop)
    (Kids : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    (declName : Name) (d : MachineData) (kD : Nat)
    {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design},
    RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w' →
    MachineDefines mctx mref cctx cref declName d.shape →
    Tools.ShippingChildInv.ChildBnd mref cref w →
    Kids mctx mref cctx cref →
    RunGoal n Reset declName d kD dom src ext extB b

/-- **Today's head conclusion** (`ships_design_svN_all`): the SV conclusion
behind five premises that are not allowed in the goal. -/
def HeadConclusion (n : Nat)
    (Reset : Sparkle.IR.AST.Module → Design → (String → KT n) → Prop)
    (Bnd : Sparkle.IR.AST.Module → Design → Prop) (Bd : Sparkle.IR.AST.Module → Design → Prop)
    (declName : Name) (d : MachineData) (kD : Nat)
    {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (b : Sparkle.IR.AST.Module) : Prop :=
  ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
    (Tools.ShippingHierPremisesBase.shipsHierCheck (childMap D.modules) b = true →
      designCheck (childMap D.modules) n (checkedOptimize b) = true →
      Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true →
      Bnd raw D → Bd b D →
      SVConclusion n Reset declName d kD dom src ext extB b raw D)

/-- **The gap between today's head and the goal of one run, as five named
hypotheses.** Each is asked of every core module and design the run's module
could come from (the head's witnesses are existential). -/
theorem runGoal_of_head {n : Nat}
    {Reset : Sparkle.IR.AST.Module → Design → (String → KT n) → Prop}
    {Bnd : Sparkle.IR.AST.Module → Design → Prop} {Bd : Sparkle.IR.AST.Module → Design → Prop}
    {declName : Name} {d : MachineData} {kD : Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {b : Sparkle.IR.AST.Module}
    (H : HeadConclusion n Reset Bnd Bd declName d kD dom src ext extB b)
    (hShips : ∀ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingHierPremisesBase.shipsHierCheck (childMap D.modules) b = true)
    (hDesign : ∀ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      designCheck (childMap D.modules) n (checkedOptimize b) = true)
    (hOuts : ∀ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true)
    (hBnd : ∀ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) → Bnd raw D)
    (hBd : ∀ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) → Bd b D) :
    RunGoal n Reset declName d kD dom src ext extB b := by
  unfold HeadConclusion at H
  unfold RunGoal
  obtain ⟨raw, D, hp, h⟩ := H
  exact ⟨raw, D, hp, h (hShips raw D hp) (hDesign raw D hp) (hOuts raw D hp) (hBnd raw D hp)
    (hBd raw D hp)⟩

end Tools.ShippingFinalGoal
