import Tools.ShippingSrm5Height
import Tools.ShippingShipsFree
-- UNBUILT (unit SRM8): see STATUS-SRM8.md for run names; the final-SHA rebuild is in REPORT-SRM8.md.
-- SCOPE (binding).  `HeightBridge n` is a NAMED PREMISE (a `def : Prop`; NOT proved here, owner SRM6): the height-indexed form of the three CONSUMERS of `designCheck` inside
-- `Tools.ShippingShipsFree.design_at_free`: `design_sv_runN` (+ `svBounds_of_checks`, which it needs) and `design_sv_all`.  Its hypothesis is `HeightPass` (rank table, `rk o.name = some r`, `r ≤ fuel`, `r ≤ n+1`,
-- `hcheck … fuel o = true`) instead of the UNIFORM `designCheck C n o = true`; all other hypotheses are those of the three originals (`outsCheck C n o = true` stays the uniform check of `design_sv_all`).
-- `design_at_free_h` is PROVED: it is `design_at_free` (proof copied, only the tail changed) with `designCheck … = true →` replaced by `HeightPass … →` and the three consumer calls replaced by ONE use of the bridge.
-- Nothing here shows that the bridge is TRUE; nothing here proves any rank supply; the bridge is a premise of the theorem, not a derived fact.  No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.
namespace Tools.ShippingSrm8Bridge
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier
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
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingSrm5Height

/-- The height-indexed analogue of the hypothesis `designCheck C n o = true`: `o` has a rank `r` in the table, with `r ≤ fuel` and `r ≤ n + 1` (the depth `n` covers the tree),
and the height check passes at fuel `fuel` (the shape of `topshareM_hcheck`'s conclusion). -/
def HeightPass (C : String → Option (Sparkle.IR.AST.Module × WEnv)) (rk : String → Option Nat) (n fuel : Nat) (o : Sparkle.IR.AST.Module) : Prop :=
  (∃ r, rk o.name = some r ∧ r ≤ fuel ∧ r ≤ n + 1) ∧ hcheck C rk fuel o = true

/-- **THE BRIDGE (PREMISE, owner SRM6; OPEN).**  For every module list, rank table, fuel, module, seeding, start state and environment list: under `HeightPass`, the width premises and the closed run
of the IR at depth `n` (exactly the hypotheses of `svBounds_of_checks` / `design_sv_runN`), the emitted texts have a closed run (`DesignSV`), and, under the uniform `outsCheck`, every closed run of the
texts shows whatever the one run shows (the content of `design_sv_all`). -/
def HeightBridge (n : Nat) : Prop :=
  ∀ (ms : List Sparkle.IR.AST.Module) (rk : String → Option Nat) (fuel : Nat) (o : Sparkle.IR.AST.Module)
    (seed : Nat → (String → Nat) → Env) (T : Nat) (s : KState (KT n)) (envs : List Env),
    HeightPass (childMap ms) rk n fuel o →
    (∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st)) →
    Bounded (weS o) s.st →
    (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
      childMap ms mn = some (gc, gcwe) → InvN (childMap ms) n gc (s.kids iname)) →
    runModuleTG (KSn (childMap ms) n) (declWidth o) (childMap ms) o.body seed T s = some envs →
    DesignSV (childMap ms) n o seed T s envs ∧
    (Tools.ShippingDesignSVBack.outsCheck (childMap ms) n o = true →
      ∀ (P : List Env → Prop), P envs → ∀ envs', DesignSV (childMap ms) n o seed T s envs' → P envs')

/-- **`design_at_free` with the height check and the bridge in place of the uniform `designCheck`** (PROVED from `HeightBridge n`, which is a hypothesis). -/
theorem design_at_free_h (n : Nat) (rk : String → Option Nat) (fuel : Nat)
    (hbridge : HeightBridge n)
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
    {raw : Sparkle.IR.AST.Module} {D : Design}
      (F :
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
                (envsO[j]'hj) o.name = f j)
    (hoc : Bnd raw D →
      Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true) :
        -- the shipped design's emitted-text checks
        HeightPass (childMap D.modules) rk n fuel (checkedOptimize b) →
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
                  (envs'[j]'hj) o.name = f j := by
  intro hdc hBnd hBd
  have hoc := hoc hBnd
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := F hBnd hBd
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hclk hinit hreset hinsFit hstX hstR
    hinsW hstW hkidsW
  obtain ⟨envsO, hrun, hlen, hobs⟩ := H i bools bits T ins st0 mems kids hsrc hpass hrst hclk
    hinit hreset hinsFit hstX hstR
  have hbr := hbridge D.modules rk fuel (checkedOptimize b) (seedIn b ins) T (⟨st0, mems, kids⟩ : KState (KT n)) envsO
    hdc (seedIn_bound hinsW) hstW hkidsW hrun
  obtain ⟨hD, hall⟩ := hbr
  refine ⟨⟨envsO, hD, hlen, hobs⟩, fun envs' hD' => ?_⟩
  exact hall hoc
    (fun e => e.length = T ∧ ∀ j (hj : j < e.length) (k : Nat) (o : OutField) (f : Nat → Nat),
      d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f → (e[j]'hj) o.name = f j)
    ⟨hlen, hobs⟩ envs' hD'

end Tools.ShippingSrm8Bridge
