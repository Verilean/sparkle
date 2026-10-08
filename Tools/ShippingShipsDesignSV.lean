import Tools.ShippingDesignSVBounds
import Tools.ShippingMachineShipsHier
import Tools.ShippingMachineDepthH

/-! # From the source to the closed emitted texts of the design

`machine_ships_hier` (at depth `n`, `KS D = KSn (childMap D.modules) n`)
ends at the shipped module's IR linked run: from the full entry's seeding
`seedIn b ins`, the run of `checkedOptimize b` with its children stepping at
depth `n` shows the source. `ships_design_svN` composes that very run with
the width derivation (`svBounds_of_checks`) and the forward simulation
(`design_sv_runN`): on the SAME design `D`, the SAME shipped module and the
SAME seeding, the emitted texts of the shipped module and of all its
descendants run CLOSED — the children's texts supplying every
instance-output wire — to environments whose output ports carry the
source's values.

Its hypothesis `H` is exactly the conclusion of `machine_ships_hier` at
`KSn`; its added premises are the decidable `designCheck` of the shipped
design and the use conditions of the emitted widths: the inputs within the
shipped module's emitted widths, the start registers within them, and every
instance's start state within its own (`InvN`). It is a forward statement:
the closed relation `DesignSV` is not shown to admit no other run. -/
namespace Tools.ShippingShipsDesignSV
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

/-- A seeding by the full entry's module keeps bounded states bounded when
the inputs fit. -/
theorem seedIn_bound {b o : Sparkle.IR.AST.Module} {ins : Nat → String → Nat}
    (hinsW : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS o x) :
    ∀ k st, Bounded (weS o) st → Bounded (weS o) (seedIn b ins k st) := by
  intro k st hst n
  simp only [seedIn]
  split
  · rename_i h
    exact hinsW k n (by simpa [List.contains_eq_mem] using h)
  · exact hst n

/-- **From the shipped IR run to the closed run of the design's emitted texts.** -/
theorem ships_design_svN (n : Nat)
    (Reset : Sparkle.IR.AST.Module → Design → (String → KT n) → Prop)
    (Bnd : Sparkle.IR.AST.Module → Design → Prop) (Bd : Sparkle.IR.AST.Module → Design → Prop)
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
    (H : ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Tools.ShippingHierPremisesBase.shipsHierCheck (childMap D.modules) b = true →
        Bnd raw D → Bd b D →
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
            ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Tools.ShippingHierPremisesBase.shipsHierCheck (childMap D.modules) b = true →
        -- the shipped design's emitted-text checks
        designCheck (childMap D.modules) n (checkedOptimize b) = true →
        Bnd raw D → Bd b D →
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
            -- the emitted widths' use conditions: inputs, start registers, instance states
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
            Bounded (weS (checkedOptimize b)) st0 →
            (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
              childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) n gc (kids iname)) →
            ∃ envsO,
              DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j) := by
  obtain ⟨raw, D, hpost, H⟩ := H
  refine ⟨raw, D, hpost, ?_⟩
  intro hchk hdc hBnd hBd
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := H hchk hBnd hBd
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hreset hinsFit hstX hstR hinsW hstW hkidsW
  obtain ⟨envsO, hrun, hlen, hobs⟩ := H i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hreset
    hinsFit hstX hstR
  refine ⟨envsO, ?_, hlen, hobs⟩
  exact design_sv_runN D.modules n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO hdc hrun
    (svBounds_of_checks D.modules n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO hdc
      (seedIn_bound hinsW) hstW hkidsW hrun)

/-- **The combinational route, to the closed emitted texts.** The
hypothesis is `machine_ships_hierH`'s conclusion (the shipped module's
combinational linked run, `runModuleH`); with the children assignments-only,
local and fully wired on the SHIPPED body (`kidsComb`), that run is its
depth-0 `flatKS` run from any children's states (`runModuleTG_flat_of_H`), so
the depth-0 forward simulation applies. The children's states are
quantified (each within its emitted widths). -/
theorem ships_design_svH (R : Nat → Sparkle.IR.AST.Module → Prop)
    {declName : Name} {d : MachineData} {kD : Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {b : Sparkle.IR.AST.Module}
    (H : ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Tools.ShippingHierPremises.shipsHierHCheck D.modules b = true →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (bools j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ raw.body →
              Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
                d.shape.layout.slots.length
                ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
              moduleByName D.modules mc.name = some mc →
              R k mc) →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            Tools.ShippingHierTyped.BoundOff (declWidth b) (b.outputs.map (·.name)) st0 →
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            ∃ envsO, runModuleH (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T st0 mems = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Tools.ShippingHierPremises.shipsHierHCheck D.modules b = true →
        -- the shipped body's children are assignments only, local, fully wired
        Tools.ShippingMachineDepthH.kidsComb D.modules (checkedOptimize b).body = true →
        designCheck (childMap D.modules) 0 (checkedOptimize b) = true →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KidState),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (bools j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ raw.body →
              Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
                d.shape.layout.slots.length
                ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
              moduleByName D.modules mc.name = some mc →
              R k mc) →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            Tools.ShippingHierTyped.BoundOff (declWidth b) (b.outputs.map (·.name)) st0 →
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
            Bounded (weS (checkedOptimize b)) st0 →
            (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
              childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname)) →
            ∃ envsO,
              DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j) := by
  obtain ⟨raw, D, hpost, H⟩ := H
  refine ⟨raw, D, hpost, ?_⟩
  intro hchk hcomb hdc
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := H hchk
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hinit hcalls hinsFit hstD hstR hinsW hstW hkidsW
  obtain ⟨envsO, hrunH, hlen, hobs⟩ := H i bools bits T ins st0 mems hsrc hpass hrst hinit hcalls
    hinsFit hstD hstR
  have hF := (Tools.ShippingHierPremises.shipsHierHCheck_sound hchk).1
  have hrun := Tools.ShippingMachineDepthH.runModuleTG_flat_of_H _ D.modules (checkedOptimize b).body
    (seedIn b ins) (Tools.ShippingHierOptRun.memFree_of_linkedWF _ hF.wfO) hcomb T st0 mems kids envsO hrunH
  refine ⟨envsO, ?_, hlen, hobs⟩
  exact design_sv_runN D.modules 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO hdc hrun
    (svBounds_of_checks D.modules 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO hdc
      (seedIn_bound hinsW) hstW hkidsW hrun)

end Tools.ShippingShipsDesignSV
