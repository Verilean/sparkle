import Tools.ShippingSatAssembly
import Tools.ShippingGateCert2
import Tools.ShippingKidsResetSat
import Tools.ShippingInputWiresRun
import Tools.ShippingMemKidPorts
import Tools.ShippingChecksWidths
-- BUILT by the integrator: sc1 exit 0 (675 jobs, axioms standard; round par/satc, base 87874a82).
-- Writing-time guesses (marked `-- (writing-time guess: …)` at the place):
--   (g1) `of_decide_eq_true` in `satData_of_ok` picks up the instances `satDataOk` elaborated
--        (as `gateParentFacts_of_ok`, built ce1);
--   (g2) `memGate_kidNoRegsS`: `rw [ho] at hy` / `rw [KidT.mem hy (child?_mem cb aw dw)]` /
--        `rw [ho, hn] at hy` behave at generic data as in the per-parent `<p>_kidNoRegs` (built ks1);
--        `gate_real_ports` infers `bpos`/`vpos`/`kb`/`kv`/`vw` from `peel`, `he` and the positions
--        (given explicitly to be safe);
--   (g3) `satOfCert`: the statement is `sat_of_designClosedBW`'s with `Reset := Reset1` and the five
--        run hypotheses removed; the `fun hcore hpost => …` arguments elaborate against the implicit
--        `∀ {raw D w1}` binders as in `MemNameCollisionSatTest` (built sa1/sa2);
--   (g4) the projection `.oi` of `core_closed_typedInMT`'s `TypedIn` (as in the per-parent `<p>_oi`).

/-! # The head's run hypotheses satisfied from the certificate (round par/satc)

`Tests/Compiler/MemNameCollisionSatTest.lean` expands, per parent, `<p>_gate` (`core_hierGateMT`),
`<p>_oi` (`core_closed_typedInMT`, field `oi`), `<p>_inputWires` (`inputWires_runMT`), and uses
`<p>_kidsSat` (`core_kidsSatMT` at the hand-written `<p>_kidNoRegs`) and `<p>_names`, then applies
`Tools.ShippingSatAssembly.sat_of_designClosedBW`. The four expansions differ only in the decl name,
the `MachineData`, the gate child (name, source) and the closing `<p>_closesR`. Here that is ONE
theorem:

* `satDataOk d kD : Bool` — the data conditions of `sat_of_designClosedBW` not already in
  `gateParentCertOk`: `hkD` (`kD ≤ d.nIn`), `hlen`, `hdom`, `hinit` (every slot's reset value is
  `0`), in one Bool (one `decide`); `satData_of_ok` its soundness. (`hsl` is the certificate's
  conjunct `slots.length ≠ 0`, `GateParentFacts.hsl`.)
* `memGate_kidNoRegsS` — `NoRegs` of every `KidT` kid from `memGateOk` and the gate child's facts
  (the per-parent `<p>_kidNoRegs`' proof at generic data; new, no existing theorem states it).
* `satOfCert` — from the head's conclusion `H` (shape exported by `machine_design_noPortsTBW` with
  `Reset := Reset1`; per parent `<p>_designClosedBW hr entry hR0`), its boundary, the parent's
  `machine_ok` / `machine_body`, the THREE Bools `gateParentCertOk` / `memGateOk` / `satDataOk`, the
  gate child's reflection `hR0` and gate facts (`old`, `peel`, `wf`), the closing, `MachineDefines`
  and `ChildBnd`: the conclusion of `sat_of_designClosedBW`. The run facts `hNames`, `hGate`,
  `hOI`, `hIW`, `hKids` are derived inside (`gateParent_names`, `core_hierGateMT`,
  `core_closed_typedInMT`, `inputWires_runMT`, `core_kidsSatMT` + `memGate_kidNoRegsS`).

SCOPE (proved vs premise vs not covered):
* `memGateOk` covers only parents whose instance entries are ONE memory origin `.mem cb aw dw` or
  the `.ord` call of ONE gate child, with the gate's result width ≠ 1. The certificate does NOT
  cover all compiler-accepted inputs (other origins, several gate children, sequential children,
  field calls, result width 1 are outside it; for them the Bools are false or the theorem does not
  apply).
* `hinit` (every slot's reset value is `0`) remains a restriction of `sat_of_designClosedBW`
  (start state `0`), now a conjunct of `satDataOk`; it is not a property of the head.
* Premises, unchanged: the head's conclusion `H` (per parent from the full-entry run `hr`,
  `MachineDefines`, `EntryDefines` through the generated `<p>_designClosedBW`), the boundary, the
  reflection `hR0` of the gate child, the closing `MachineClosesAt` (per parent `<p>_closesR`),
  `MachineDefines`, `ChildBnd`. `<p>_designClosedBW` itself is still produced by
  `generateTopW` from the hand-written run lemmas (`<p>_runFacts`, …); deriving it from the
  certificate as well is OPEN here.
No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingSatCert
open Tools.ShippingShipsFree
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
open Tools.ShippingSatInputs
open Tools.ShippingGateCert (and_split)

/-! ## The data conditions of `sat_of_designClosedBW` as one Bool -/

/-- **The data conditions of `sat_of_designClosedBW` not in `gateParentCertOk`**: `hkD`, `hlen`,
`hdom`, `hinit` (slot inits `0`). -/
def satDataOk (d : MachineData) (kD : Nat) : Bool :=
  decide (kD ≤ d.nIn) &&
  decide (kD + d.shape.insts.length + d.shape.layout.slots.length + d.shape.layout.lets =
    d.shape.binders.length) &&
  decide (∀ x ∈ d.shape.binders.drop kD, x.2 ≠ .domain) &&
  decide (∀ f ∈ d.shape.layout.slots, f.init = 0)

/-- Soundness of `satDataOk`. -/
theorem satData_of_ok {d : MachineData} {kD : Nat} (h : satDataOk d kD = true) :
    kD ≤ d.nIn ∧
    kD + d.shape.insts.length + d.shape.layout.slots.length + d.shape.layout.lets =
      d.shape.binders.length ∧
    (∀ x ∈ d.shape.binders.drop kD, x.2 ≠ .domain) ∧
    (∀ f ∈ d.shape.layout.slots, f.init = 0) := by
  unfold satDataOk at h
  obtain ⟨h, hinit⟩ := and_split h
  obtain ⟨h, hdom⟩ := and_split h
  obtain ⟨hkD, hlen⟩ := and_split h
  -- (writing-time guess g1)
  exact ⟨of_decide_eq_true hkD, of_decide_eq_true hlen, of_decide_eq_true hdom,
    of_decide_eq_true hinit⟩

/-! ## `NoRegs` of every kid from `memGateOk` -/

section KidNoRegs
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

open Sparkle.Compiler.Elab (MixedGateBinder certifiedShape? mixedGatePeel) in
/-- **Per kid, no register statement**, from ONE Bool (`memGateOk`) and the gate child's facts:
the memory entry is the built memory module (`memModule_noRegs`), the `.ord` entry a gate child
(`noRegs_of_gate` of `gate_real_ports`). -/
theorem memGate_kidNoRegsS {value dom : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {bposL vposL vwL : List Nat} {srt : Tools.ShippingUnifiedSource.SType}
    {e : Tools.ShippingUnifiedSource.Term srt}
    (d : MachineData) (cb : Bool) (aw dw : Nat) (c : Name)
    (hok : Tools.ShippingGateCert2.memGateOk d cb aw dw c bs bposL vposL vwL srt.width = true)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c value)
    (old : ∀ dv : DefinitionVal, dv.value = value → certifiedShape? false [] (.defnInfo dv) = none)
    (peel : mixedGatePeel value = some (bs,
      Tools.ShippingUnifiedSource.quote dom (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bposL.getD j 0))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vposL.getD j 0)) e))
    (he : e.WF bposL.length vposL.length (fun j => vwL.getD j 0)) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 y →
      Tools.ShippingKidsResetSat.NoRegs y.1 := by
  obtain ⟨h, _⟩ := and_split hok
  obtain ⟨h, hv⟩ := and_split h
  obtain ⟨hE, hb⟩ := and_split h
  intro k hk y hy
  -- (writing-time guess g2)
  rcases Tools.ShippingGateCert2.memGateEntry_of_ok hE k hk with ho | ⟨ho, hn⟩
  · rw [ho] at hy
    rw [Tools.ShippingInstTagged.KidT.mem hy (Tools.ShippingInstTagged.child?_mem cb aw dw)]
    exact Tools.ShippingKidsResetSat.memModule_noRegs cb aw dw
  · rw [ho, hn] at hy
    exact Tools.ShippingKidsResetSat.noRegs_of_gate
      (Tools.ShippingGatePorts.gate_real_ports (bs := bs) (srt := srt) (e := e)
        (kb := bposL.length) (kv := vposL.length) (vw := fun j => vwL.getD j 0)
        (bpos := fun j => bposL.getD j 0) (vpos := fun j => vposL.getD j 0)
        hR0 old peel he
        (Tools.ShippingGateChild.bool_positions hb) (Tools.ShippingGateChild.bits_positions hv)
        (Tools.ShippingInstTagged.KidT.real hy rfl))

end KidNoRegs

/-! ## The generic satisfaction theorem -/

open Sparkle.Compiler.Elab (MixedGateBinder certifiedShape? mixedGatePeel) in
set_option maxHeartbeats 4000000 in
/-- **The run hypotheses of the TBW head's conclusion, satisfied from the certificate** (see the
header): `sat_of_designClosedBW` with its five run-fact hypotheses derived from
`gateParentCertOk`, `memGateOk`, the gate child's facts and the closing, and its data conditions
from `satDataOk` (and the certificate's `slots ≠ []`). -/
theorem satOfCert
    {declName : Name} {d : MachineData} {kD : Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {Bd : Prop}
    -- the certificate's parameters
    {nDecl : Nat} {kidOuts : Nat → List OutField} {kidIns : Nat → List Nat}
    {cb : Bool} {aw dw : Nat} {c : Name}
    {value gdom : Lean.Expr} {bs : List (Name × MixedGateBinder)} {bposL vposL vwL : List Nat}
    {srt : Tools.ShippingUnifiedSource.SType} {e : Tools.ShippingUnifiedSource.Term srt}
    (H :
      ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
        ((∃ w1 : Void IO.RealWorld,
            RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1) ∧
          (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
            b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))) ∧
        (Bd →
          ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
          ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
            regs.Nodup ∧ regs.length = d.ss.length ∧
            (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
            b.inputs = raw.inputs ∧
            ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
              (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
              (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
              (kids : String → KT 0),
              (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
                (fun j => (extB i bools bits j).val (T - 1 - t))
                (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
              (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
              (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
              (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
                d.shape.layout.slots[k]? = some f → st0 r = f.init) →
              Reset1 raw D kids →
              (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
              (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
                st0 x < 2 ^ declWidth b x) →
              (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
              (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
              Bounded (weS (checkedOptimize b)) st0 →
              (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
                childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname)) →
              (∃ envsO,
                DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
                envsO.length = T ∧
                ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                  (envsO[j]'hj) o.name = f j)
              ∧ ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                  envs'.length = T ∧
                  ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                    d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                    (envs'[j]'hj) o.name = f j))
    (hBd : Bd)
    -- the parent's reader facts
    (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    -- the certificate: three Bools
    (hcert : Tools.ShippingGateCert.gateParentCertOk d nDecl kidOuts kidIns = true)
    (hmg : Tools.ShippingGateCert2.memGateOk d cb aw dw c bs bposL vposL vwL srt.width = true)
    (hdata : satDataOk d kD = true)
    -- the gate child: reflection and gate facts (as `#gate_child` / `gateDefs` write them)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c value)
    (old : ∀ dv : DefinitionVal, dv.value = value → certifiedShape? false [] (.defnInfo dv) = none)
    (peel : mixedGatePeel value = some (bs,
      Tools.ShippingUnifiedSource.quote gdom (fun j => inputExpr bs.length (bposL.getD j 0))
        (fun j => inputExpr bs.length (vposL.getD j 0)) e))
    (he : e.WF bposL.length vposL.length (fun j => vwL.getD j 0))
    -- the closing and the outer premises
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref declName d.shape)
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (kids : String → KT 0),
        ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
          (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (T : Nat),
          (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
            (fun j => (extB i bools bits j).val (T - 1 - t))
            (fun j n => (ext i bools bits j n).val (T - 1 - t))
            (seedIn b (fun t => streamEnv declName (d.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t))) t st)) ∧
          ∀ mems : MEnv,
            (∃ envsO,
              DesignSV (childMap D.modules) 0 (checkedOptimize b)
                (seedIn b (fun t => streamEnv declName (d.bsIn.take kD) ids cache
                  (fun j => (extB i bools bits j).val (T - 1 - t))
                  (fun j n => (ext i bools bits j n).val (T - 1 - t)))) T
                ⟨fun _ => 0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j) ∧
            ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b)
                (seedIn b (fun t => streamEnv declName (d.bsIn.take kD) ids cache
                  (fun j => (extB i bools bits j).val (T - 1 - t))
                  (fun j n => (ext i bools bits j n).val (T - 1 - t)))) T
                ⟨fun _ => 0, mems, kids⟩ envs' →
              envs'.length = T ∧
              ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envs'[j]'hj) o.name = f j := by
  have F := Tools.ShippingGateCert.gateParentFacts_of_ok hcert
  obtain ⟨hkD, hlen, hdom, hinit⟩ := satData_of_ok hdata
  have hkidR := memGate_kidNoRegsS (dom := gdom) d cb aw dw c hmg hR0 old peel he
  -- (writing-time guess g3, g4)
  exact Tools.ShippingSatAssembly.sat_of_designClosedBW (Reset := Reset1) H hBd
    (fun hcore hpost =>
      Tools.ShippingGateCert.gateParent_names d ok hbody hcert closes hcore hpost entry hB)
    (fun hcore hpost =>
      Tools.ShippingMemKid.core_hierGateMT d ok hbody F.hC F.hslots F.hdomB F.hins F.hfne F.outTy
        hB hcore hpost entry closes)
    (fun hcore hpost =>
      (Tools.ShippingMemKid.core_closed_typedInMT d ok hbody F.hC F.hslots F.hdomB F.hins F.outTy
        F.hfne hB hcore hpost entry closes F.hon F.hoty).oi)
    (fun hcore hpost =>
      Tools.ShippingInputWiresRun.inputWires_runMT d ok hbody F.hC F.hslots F.hdomB F.hins F.hfne
        hB hcore hpost entry closes)
    (fun hcore hpost =>
      Tools.ShippingKidsResetSat.core_kidsSatMT d ok hbody F.hC F.hslots F.hdomB F.hins F.hfne
        F.outTy hkidR hB hcore hpost entry closes)
    hkD hlen hdom F.hsl hinit

end Tools.ShippingSatCert
