import Tests.Compiler.SeqDeepGenKeyTest
import Tests.Compiler.SeqDeepGenArgsConclTest
import Tests.Compiler.SeqDeepGenInstConclTest
import Tests.Compiler.SeqDeepGrandEndpointAuditTest
-- BUILT (unit SR3v): k5 exit 0.
-- SCOPE (binding): a HAND-WRITTEN expected conclusion for the generated depth-2 endpoint `tf4.epD2_endpoint` (`tf4 -> wrap3 -> acc`, where the
-- CHILD `wrap3` calls the leaf `acc` TWICE with different arguments: several call instances of the leaf at the C side).  `Tf4Concl n kP` is
-- written by hand; the WHOLE conclusion of the generated endpoint is compared by `isDefEq` (shared binders as the same free variables,
-- `Meta.check`, no mvars / stray fvars).  Altered expectations must be REJECTED; each changes:
--   * `Tf4Concl 2 2`: the number of own inputs read by `SourceInputs`;
--   * `Tf4Concl 1 3`: the depth `n` of `ResetNk`, `KT`, `InvN`, `DesignSV`;
--   * `TopwConcl 2 3`: a DIFFERENT declaration (source, outputs, registers differ);
--   * `GrandConcl 2 3`: another declaration, whose source, boundary and outputs all differ.
-- A statement check on ONE example, not a proof that the boundary holds and not whole-class coverage.
namespace Tests.Compiler.SeqDeepGenKeyConclTest
open Tests.Compiler.SeqDeepGenInstTest Tests.Compiler.SeqDeepGenKeyTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
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


/-- The expected run boundary of the depth-2 endpoint of `tf4`, written by hand: laws `O`, `T` (PREMISES), the admissible contexts,
`MachineDefines` of the callee `wrap` AND of its callee `acc`, and a start world in `JQ` (not `BndAg`, which is for `mid` / `cnt`). -/
def BndTf4 : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenKeyTest.wrap3 wrap3.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape ∧
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))

/-- The expected conclusion of the depth-`n` endpoint of `tf4` (`kP` own inputs read by the source), written out by hand. -/
def Tf4Concl (n kP : Nat) (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State)
    (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State) (w : Void IO.RealWorld)
    (b : Sparkle.IR.AST.Module) (design : Design) : Prop :=
  ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (BndTf4 mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = tf4.machineData.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = tf4.machineData.ss.length ∧
          ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
            (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs ``Tests.Compiler.SeqDeepGenKeyTest.tf4 (tf4.machineData.bsIn.take kP) ids cache
              (fun j => ((fun i bools bits => tf4.machineExtB i bools bits
                (Tools.ShippingMachineSource.stateLoop tf4.machineInits (tf4.machineBody i bools bits))) i bools bits j).val (T - 1 - t))
              (fun j n => ((fun i bools bits => tf4.machineExt i bools bits
                (Tools.ShippingMachineSource.stateLoop tf4.machineInits (tf4.machineBody i bools bits))) i bools bits j n).val (T - 1 - t))
              (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              tf4.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk n raw D kids →
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
                tf4.machineData.shape.layout.outs[k]? = some o → (tf4.machineSource i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)
            ∧ ∀ envs', DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  tf4.machineData.shape.layout.outs[k]? = some o → (tf4.machineSource i bools bits)[k]? = some f →
                  (envs'[j]'hj) o.name = f j)


open Lean Elab Command Meta in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let gen := ``Tests.Compiler.SeqDeepGenKeyTest.tf4.epD2_endpoint
  let gt := (← getConstInfo gen).type
  forallTelescope gt fun xs concl => do
    let names ← xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
    unless names == ["mctx", "mref", "cctx", "cref", "w", "w'", "b", "design", "hr", "entry", "closes"] do
      throwError "SR3v AUDIT FAILED: endpoint binder names are {names}"
    let args := #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[6]!, xs[7]!]
    let mkT (n kP : Nat) : Lean.Expr :=
      mkAppN (mkConst ``Tf4Concl) (#[mkNatLit n, mkNatLit kP] ++ args)
    let mkTopw (n kP : Nat) : Lean.Expr :=
      mkAppN (mkConst ``Tests.Compiler.SeqDeepGenInstConclTest.TopwConcl) (#[mkNatLit n, mkNatLit kP] ++ args)
    let mkOther (n kP : Nat) : Lean.Expr :=
      mkAppN (mkConst ``Tests.Compiler.SeqDeepGrandEndpointAuditTest.GrandConcl) (#[mkNatLit n, mkNatLit kP] ++ args)
    let concl ← instantiateMVars concl
    let exp := mkT 2 3
    let alts := [(mkT 2 2, "kP 2"), (mkT 1 3, "depth 1"), (mkTopw 2 3, "TopwConcl 2 3 (other declaration: source, outputs differ)"), (mkOther 2 3, "GrandConcl 2 3 (other declaration: source, boundary, outputs differ)")]
    for (e, what) in [(concl, "the endpoint's conclusion"), (exp, "the expected conclusion")] ++ alts.map fun (e, w) => (e, s!"alt {w}") do
      if e.hasMVar then throwError "SR3v AUDIT FAILED: unassigned metavariables in {what}"
      for f in (Lean.collectFVars {} e).fvarIds do
        unless xs.any (·.fvarId! == f) do throwError "SR3v AUDIT FAILED: out-of-scope free variable in {what}"
      Meta.check e
    unless (← isDefEq concl exp) do
      throwError "SR3v AUDIT FAILED: the conclusion of the generated tf4 endpoint is not definitionally Tf4Concl 2 3"
    for (e, w) in alts do
      if (← isDefEq concl e) then throwError "SR3v AUDIT FAILED: the altered expectation ({w}) was ACCEPTED"
  logInfo m!"SR3v: the conclusion of the GENERATED tf4.epD2_endpoint is isDefEq to the hand-written Tf4Concl 2 3; kP 2, depth 1, TopwConcl 2 3 and GrandConcl 2 3 are REJECTED"

end Tests.Compiler.SeqDeepGenKeyConclTest
