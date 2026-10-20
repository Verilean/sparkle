import Tools.ShippingSatCert
import Tools.ShippingSatAssemblyS
-- BUILT by the integrator: cs1 exit 0 (562 jobs) (round par/certs, base aa35e8a6); writing-time guesses accepted.
-- Writing-time guesses:
--   (s1) `of_decide_eq_true` in `satDataS_of_ok` picks up the instances `satDataOkS` elaborated
--        (as `satData_of_ok`, built sc1); the `decide` of `∀ f ∈ slots, f.init < 2 ^ f.width` and
--        of `∀ o ∈ outs, outNameOk o.name = true` find `List.decidableBAll`;
--   (s2) `satOfCertS`: the `fun hcore hpost => …` / `fun hcore => …` arguments elaborate against
--        the implicit `∀ {raw D w1}` binders of `sat_of_designClosedBS` (as in `satOfCert` and in
--        `NonzeroInitParentTest`'s `collMixSame5_satS`, built sc1 / ni2);
--   (s3) `gateParent_designP0` accepts `memGate_kidsS`'s conclusion
--        (`outsF (originAt d.shape k)`) for `hkid` at `kidOuts := fun k => outsF (originAt d.shape k)`
--        (beta; the generator `generateCert2W` passes the same pair, built sc2), depth `n := 0`
--        inferred from `memGate_kidsS`;
--   (s4) `slotRegs_runMT`'s `nDecl` inferred from `F.hC`.

/-! # The TBS head's run hypotheses satisfied from the certificate, NONZERO slot inits
(round par/certs)

`Tests/Compiler/NonzeroInitParentTest.lean` applies `Tools.ShippingSatAssemblyS.sat_of_designClosedBS`
to hand-written per-parent run lemmas (`<p>_names`, `_gate`, `_oi`, `_inputWires`, `_kidsSat`,
`_designP0`) and an inline `slotRegs_runMT`. `satOfCert` (`Tools.ShippingSatCert`) did the same for
`sat_of_designClosedBW` (inits `0`). Here, its pattern for the TBS head:

* `satDataOkS d kD : Bool` — `satDataOk` with the conjunct "every slot init is `0`" replaced by
  "every slot init fits its slot's width" (`hinitW`), plus `hon` (`outNameOk` of every output
  name), the data conditions of `sat_of_designClosedBS` not already in `gateParentCertOk`
  (`houtTy` is the certificate's `outTy`); `satDataS_of_ok` its soundness.
* `satOfCertS` — from the head's conclusion `H` (the shape `machine_design_noPortsTBS` exports with
  `Reset := Reset1`), its boundary, the parent's `machine_ok` / `machine_body`, the THREE Bools
  `gateParentCertOk` (at the tables `fun k => outsF (originAt d.shape k)` / `insF …`) /
  `memGateOk` / `satDataOkS`, the four table equations (`rfl` for the tests' tables), the gate
  child's reflection `hR0` and gate facts, the closing, `MachineDefines` and `ChildBnd`: the
  conclusion of `sat_of_designClosedBS`. Its seven run facts are derived inside:
  `hNames` (`gateParent_names`), `hGate` (`core_hierGateMT`), `hOI` (`core_closed_typedInMT .oi`),
  `hIW` (`inputWires_runMT`), `hKids` (`core_kidsSatMT` + `memGate_kidNoRegsS`), `hDesign`
  (`gateParent_designP0` at `memGate_kidsS`), `hRegs` (`slotRegs_runMT`).

SCOPE (proved vs premise vs not covered): as `satOfCert` (one memory origin and one gate child,
gate result width ≠ 1; the certificate does NOT cover all compiler-accepted inputs). The slot
inits are no longer required to be `0`; they must fit their widths (decided). Premises unchanged:
the head's conclusion `H` (per parent the generated `<p>_designClosedCS hr entry hR0`), the
boundary, `hR0`, the closing `MachineClosesAt`, `MachineDefines`, `ChildBnd`. No new fact about
the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingSatCertS
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

open Tools.ShippingSatCert (memGate_kidNoRegsS)
open Tools.ShippingSatAssemblyS (stOf)

/-! ## The data conditions of `sat_of_designClosedBS` as one Bool -/

/-- **The data conditions of `sat_of_designClosedBS` not in `gateParentCertOk`**: `hkD`, `hlen`,
`hdom`, `hinitW` (slot inits fit their widths), `hon` (output names). -/
def satDataOkS (d : MachineData) (kD : Nat) : Bool :=
  decide (kD ≤ d.nIn) &&
  decide (kD + d.shape.insts.length + d.shape.layout.slots.length + d.shape.layout.lets =
    d.shape.binders.length) &&
  decide (∀ x ∈ d.shape.binders.drop kD, x.2 ≠ .domain) &&
  decide (∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width) &&
  decide (∀ o ∈ d.shape.layout.outs, Sparkle.IR.Machine.outNameOk o.name = true)

/-- Soundness of `satDataOkS`. -/
theorem satDataS_of_ok {d : MachineData} {kD : Nat} (h : satDataOkS d kD = true) :
    kD ≤ d.nIn ∧
    kD + d.shape.insts.length + d.shape.layout.slots.length + d.shape.layout.lets =
      d.shape.binders.length ∧
    (∀ x ∈ d.shape.binders.drop kD, x.2 ≠ .domain) ∧
    (∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width) ∧
    (∀ o ∈ d.shape.layout.outs, Sparkle.IR.Machine.outNameOk o.name = true) := by
  unfold satDataOkS at h
  obtain ⟨h, hon⟩ := and_split h
  obtain ⟨h, hinitW⟩ := and_split h
  obtain ⟨h, hdom⟩ := and_split h
  obtain ⟨hkD, hlen⟩ := and_split h
  -- (writing-time guess s1)
  exact ⟨of_decide_eq_true hkD, of_decide_eq_true hlen, of_decide_eq_true hdom,
    of_decide_eq_true hinitW, of_decide_eq_true hon⟩

/-! ## The generic satisfaction theorem (nonzero inits) -/

open Sparkle.Compiler.Elab (MixedGateBinder certifiedShape? mixedGatePeel) in
set_option maxHeartbeats 4000000 in
/-- **The run hypotheses of the TBS head's conclusion, satisfied from the certificate** (see the
header): `sat_of_designClosedBS` (`Reset := Reset1`) with its seven run-fact hypotheses derived
from `gateParentCertOk`, `memGateOk`, the gate child's facts and the closing, and its data
conditions from `satDataOkS` and the certificate (`hsl`, `outTy`). -/
theorem satOfCertS
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
    {nDecl : Nat} {cb : Bool} {aw dw : Nat} {c : Name}
    {outsF : Sparkle.Compiler.MachInstOrigin.InstOrigin → List OutField}
    {insF : Sparkle.Compiler.MachInstOrigin.InstOrigin → List Nat}
    {value gdom : Lean.Expr} {bs : List (Name × MixedGateBinder)} {bposL vposL vwL : List Nat}
    {srt : Tools.ShippingUnifiedSource.SType} {e : Tools.ShippingUnifiedSource.Term srt}
    (H :
      ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
        (-- (par/sat) the core run of THIS raw, D
          (∃ w1 : Void IO.RealWorld,
            RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1) ∧
          (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
            b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))) ∧
        (-- NO checker premise: the boundary is the only antecedent
          Bd →
          ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
          ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
            regs.Nodup ∧ regs.length = d.ss.length ∧
            -- (par/sat) the wiring of the same ids, cache, registers, and the inputs of `b`
            (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
            b.inputs = raw.inputs ∧
            ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
              (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
              (T : Nat) (ins : Nat → String → Nat) (st0 stO : String → Nat) (mems : MEnv)
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
              -- the emitted widths' use conditions: inputs, start registers, instance states
              (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
              Bounded (weS (checkedOptimize b)) stO →
              (∀ n, (n ∉ Sparkle.IR.HierCheck.drivesOf b.body ∨
                n ∈ Sparkle.IR.HierCheck.drivesOf (checkedOptimize b).body) → stO n = st0 n) →
              -- (`BoundOff` unfolded: the generator refuses statements mentioning `BoundOff`)
              (∀ n, n ∉ b.outputs.map (·.name) ++ b.inputs.map (·.name) →
                st0 n < 2 ^ declWidth b n) →
              (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
                childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname)) →
              -- a closed run of the emitted texts showing the source exists ...
              (∃ envsO,
                DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨stO, mems, kids⟩ envsO ∧
                envsO.length = T ∧
                ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                  (envsO[j]'hj) o.name = f j)
              -- ... and EVERY closed run from the same seeding and states shows it
              ∧ ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨stO, mems, kids⟩ envs' →
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
    -- the certificate: three Bools, at the tables keyed by entry
    (hcert : Tools.ShippingGateCert.gateParentCertOk d nDecl
      (fun k => outsF (Tools.ShippingInstTagged.originAt d.shape k))
      (fun k => insF (Tools.ShippingInstTagged.originAt d.shape k)) = true)
    (hmg : Tools.ShippingGateCert2.memGateOk d cb aw dw c bs bposL vposL vwL srt.width = true)
    (hdata : satDataOkS d kD = true)
    -- the tables at the two origins (`rfl` for the tests' `outsG` / `insG`)
    (hmo : outsF (.mem cb aw dw) = Tools.ShippingMemKid.memOuts dw)
    (hmi : insF (.mem cb aw dw) = Tools.ShippingMemKid.memIns aw dw)
    (hgo : outsF .ord = Tools.ShippingMemKid.gateOuts srt.width)
    (hgi : insF .ord = Tools.ShippingMemKid.gateIns bs)
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
      ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
      ∃ kids : String → KT 0,
        ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
          (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (T : Nat),
          -- the seeding carries the stream at the declared inputs
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
                ⟨stOf b regs d.shape.layout.slots, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j) ∧
            ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b)
                (seedIn b (fun t => streamEnv declName (d.bsIn.take kD) ids cache
                  (fun j => (extB i bools bits j).val (T - 1 - t))
                  (fun j n => (ext i bools bits j n).val (T - 1 - t)))) T
                ⟨stOf b regs d.shape.layout.slots, mems, kids⟩ envs' →
              envs'.length = T ∧
              ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envs'[j]'hj) o.name = f j := by
  have F := Tools.ShippingGateCert.gateParentFacts_of_ok hcert
  obtain ⟨hkD, hlen, hdom, hinitW, hon⟩ := satDataS_of_ok hdata
  have hkidR := memGate_kidNoRegsS (dom := gdom) d cb aw dw c hmg hR0 old peel he
  have hkids := Tools.ShippingGateCert2.memGate_kidsS (dom := gdom) d cb aw dw c outsF insF hmg
    hmo hmi hgo hgi hR0 old peel he
  -- (writing-time guesses s2, s3, s4)
  exact Tools.ShippingSatAssemblyS.sat_of_designClosedBS (Reset := Reset1) H hBd
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
    (fun hcore hpost =>
      Tools.ShippingGateCert.gateParent_designP0 d ok hbody hcert hkids closes hcore hpost entry hB)
    (fun hcore =>
      Tools.ShippingSlotRegsRun.slotRegs_runMT d ok hbody F.hC F.hslots F.hdomB hB hcore entry
        closes)
    hkD hlen hdom F.hsl hinitW F.outTy hon

end Tools.ShippingSatCertS
