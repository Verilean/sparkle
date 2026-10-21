import Tests.Compiler.SeqDeepGrandEndpointTest
-- BUILT (unit SR3s): s13 exit 0 (first run exit 1: missing local Inhabited instance). In-test audit THROWS on failure.
-- SCOPE (binding): the whole CONCLUSION of `grand_noShips_noBdA_dcH` is compared by `isDefEq` against an explicitly written
-- expected semantic conclusion `GrandConcl 2 1` (depth 2, kD 1, domain `defaultDomain`, `BndAg`), with the shared arguments as the
-- SAME free variables; no unassigned metavariables / out-of-scope free variables; two deliberately altered expected terms
-- (`GrandConcl 1 1`, `GrandConcl 2 0`, well-typed, `Meta.check`ed) are REJECTED.  This is a statement check, not a proof that `BndAg`
-- holds.  Premises carried inside `BndAg`: `O`, `T : RefLawsATele` (ADDED), `AdmCtx`, `MachineDefines mid` / `cnt`, a `JQ` start
-- world, the cache invariant.  One concrete endpoint, NOT a general depth-2 generator (stays REFUSED).
namespace Tests.Compiler.SeqDeepGrandEndpointAuditTest
open Tests.Compiler.SeqDeepGrandEndpointTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
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

attribute [local instance] Tests.Compiler.SeqDeepGrandEndpointTest.grandInhabHL

/-- The expected conclusion of the depth-`n` endpoint of `grand` (call arguments `kD`), written out: a core run `(raw, D)` whose
post-processing is `b`, and, under `BndAg`, the closed emitted texts (`DesignSV` of `checkedOptimize b` at depth `n`) show the source. -/
def GrandConcl (n kD : Nat) (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State)
    (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State) (w : Void IO.RealWorld)
    (b : Sparkle.IR.AST.Module) (design : Design) : Prop :=
  ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (BndAg mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = grand.machineData.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = grand.machineData.ss.length ∧
          ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
            (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs ``grand (grand.machineData.bsIn.take kD) ids cache
              (fun j => ((fun i bools bits => grand.machineExtB i bools bits
                (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits))) i bools bits j).val (T - 1 - t))
              (fun j n => ((fun i bools bits => grand.machineExt i bools bits
                (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits))) i bools bits j n).val (T - 1 - t))
              (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              grand.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
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
                grand.machineData.shape.layout.outs[k]? = some o → (grand.machineSource i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)
            ∧ ∀ envs', DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  grand.machineData.shape.layout.outs[k]? = some o → (grand.machineSource i bools bits)[k]? = some f →
                  (envs'[j]'hj) o.name = f j)

open Lean Elab Command Meta in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let new := `Tests.Compiler.SeqDeepGrandEndpointTest.grand_noShips_noBdA_dcH
  let ty := (← getConstInfo new).type
  forallTelescope ty fun xs concl => do
    unless xs.size == 11 do throwError "SR3s AUDIT FAILED: the endpoint has {xs.size} binders, expected 11 (mctx mref cctx cref w w' b design hr entry closes)"
    let mk (n kD : Nat) : Lean.Expr :=
      mkAppN (mkConst ``GrandConcl) #[mkNatLit n, mkNatLit kD, xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[6]!, xs[7]!]
    let exp := mk 2 1
    let alt1 := mk 1 1
    let alt2 := mk 2 0
    let concl ← instantiateMVars concl
    for (e, what) in [(concl, "the endpoint's conclusion"), (exp, "the expected conclusion"), (alt1, "alt n=1"), (alt2, "alt kD=0")] do
      if e.hasMVar then throwError "SR3s AUDIT FAILED: unassigned metavariables in {what}"
      for f in (Lean.collectFVars {} e).fvarIds do
        unless xs.any (·.fvarId! == f) do throwError "SR3s AUDIT FAILED: out-of-scope free variable in {what}"
    Meta.check exp; Meta.check alt1; Meta.check alt2
    unless (← isDefEq concl exp) do
      throwError "SR3s AUDIT FAILED: the conclusion of {new} is not definitionally the expected GrandConcl 2 1"
    if (← isDefEq concl alt1) then throwError "SR3s AUDIT FAILED: the altered expected term (n = 1) was ACCEPTED"
    if (← isDefEq concl alt2) then throwError "SR3s AUDIT FAILED: the altered expected term (kD = 0) was ACCEPTED"
  logInfo m!"SR3s STATEMENT AUDIT OK: the whole conclusion of {new} is isDefEq to the explicit GrandConcl 2 1 (shared binders as the same fvars; no mvars / stray fvars); GrandConcl 1 1 and GrandConcl 2 0 are well typed and REJECTED"

end Tests.Compiler.SeqDeepGrandEndpointAuditTest
