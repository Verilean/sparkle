import Tools.ShippingShipsDesignSV
import Tools.ShippingDesignSVBack

/-! # From the source to EVERY closed run of the design's emitted texts

`ships_design_svN` / `ships_design_svH` give a closed run of the shipped
design's emitted texts showing the source. With `outsCheck` (every child
assigns its outputs) the closed run is unique (`design_sv_unique`), so
`design_sv_all` carries the source's values to every closed run from the
same seeding and states. The `_all` theorems state both, in one conclusion:
the existence (so the universal part is not vacuous) and the universal part.
Same design `D`, same shipped module `checkedOptimize b`, same seeding
`seedIn b ins`, same states and length `T`; no premise is added but
`outsCheck`. -/
namespace Tools.ShippingShipsDesignSVAll
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

theorem ships_design_svN_all (n : Nat)
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
        -- every child assigns its outputs: the closed run is unique
        Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true →
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
            -- a closed run of the emitted texts showing the source exists ...
            (∃ envsO,
              DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)
            -- ... and EVERY closed run from the same seeding and states shows it
            ∧ ∀ envs', DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                  (envs'[j]'hj) o.name = f j)   := by
  obtain ⟨raw, D, hpost, H'⟩ := ships_design_svN n Reset Bnd Bd H
  refine ⟨raw, D, hpost, ?_⟩
  intro hchk hdc hoc hBnd hBd
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H''⟩ := H' hchk hdc hBnd hBd
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids a1 a2 a3 a4 a5 a6 a7 a8 a9 hinsW hstW hkidsW
  obtain ⟨envsO, hD, hlen, hobs⟩ :=
    H'' i bools bits T ins st0 mems kids a1 a2 a3 a4 a5 a6 a7 a8 a9 hinsW hstW hkidsW
  refine ⟨⟨envsO, hD, hlen, hobs⟩, fun envs' hD' => ?_⟩
  exact Tools.ShippingDesignSVBack.design_sv_all D.modules n (checkedOptimize b) (seedIn b ins) T
    ⟨st0, mems, kids⟩ envsO
    (fun e => e.length = T ∧ ∀ j (hj : j < e.length) (k : Nat) (o : OutField) (f : Nat → Nat),
      d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f → (e[j]'hj) o.name = f j)
    hdc hoc (seedIn_bound hinsW) hstW hkidsW hD ⟨hlen, hobs⟩ envs' hD'

theorem ships_design_svH_all (R : Nat → Sparkle.IR.AST.Module → Prop)
    (Bnd : Sparkle.IR.AST.Module → Design → Prop)
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
        Bnd raw D →
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
        Bnd raw D →
        -- the shipped body's children are assignments only, local, fully wired
        Tools.ShippingMachineDepthH.kidsComb D.modules (checkedOptimize b).body = true →
        designCheck (childMap D.modules) 0 (checkedOptimize b) = true →
        -- every child assigns its outputs: the closed run is unique
        Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) 0 (checkedOptimize b) = true →
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
            -- a closed run of the emitted texts showing the source exists ...
            (∃ envsO,
              DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)
            -- ... and EVERY closed run from the same seeding and states shows it
            ∧ ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                  (envs'[j]'hj) o.name = f j)   := by
  obtain ⟨raw, D, hpost, H'⟩ := ships_design_svH R Bnd H
  refine ⟨raw, D, hpost, ?_⟩
  intro hchk hBnd hcomb hdc hoc
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H''⟩ := H' hchk hBnd hcomb hdc
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids a1 a2 a3 a4 a5 a6 a7 a8 hinsW hstW hkidsW
  obtain ⟨envsO, hD, hlen, hobs⟩ :=
    H'' i bools bits T ins st0 mems kids a1 a2 a3 a4 a5 a6 a7 a8 hinsW hstW hkidsW
  refine ⟨⟨envsO, hD, hlen, hobs⟩, fun envs' hD' => ?_⟩
  exact Tools.ShippingDesignSVBack.design_sv_all D.modules 0 (checkedOptimize b) (seedIn b ins) T
    ⟨st0, mems, kids⟩ envsO
    (fun e => e.length = T ∧ ∀ j (hj : j < e.length) (k : Nat) (o : OutField) (f : Nat → Nat),
      d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f → (e[j]'hj) o.name = f j)
    hdc hoc (seedIn_bound hinsW) hstW hkidsW hD ⟨hlen, hobs⟩ envs' hD'

end Tools.ShippingShipsDesignSVAll
