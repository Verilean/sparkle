import Tests.Compiler.SeqDeepGenDiffTest
import Tests.Compiler.SeqDeepGenDiffConclTest
import Tests.Compiler.SeqDeepGrandEndpointTest
import Tests.Compiler.ChildVertAuditTest
import Tools.ShippingSeqOldPieces
import Tools.ShippingSeqChildDeepRunA
import Tools.ShippingSeqParentGenD2MS
-- BUILT/UNBUILT: see REPORT-SR13.md (unit SR13, commit 2 of 2; dev runs and the final-SHA rebuild are recorded there).
-- SCOPE (binding, ledger L8as): the shared-leaf CANDIDATE `Tools/ShippingSeqParentGenD2MS.lean` (opt-in `set_option sparkle.sharedLeafCandidate true`) on a SECOND
-- example whose structure differs from `topshare`: the parent `topshare2` calls `wrapQ` (ONE call of the leaf, argument `x + y`) and then `wrapP` (TWO calls of the
-- leaf, arguments `x` and `y`), both calling the SAME 16-bit leaf `leaf16` (`Acc16Out`: a 16-bit and a Bool output; `topshare`: 8-bit `acc`, one leaf call per callee);
-- the call list is `[wrapQ, wrapQ, wrapP, wrapP]`, i.e. the callee that is DEFINED first is called second in the source of its sibling, the callees have 2 and 4 leaf instances
-- (`topshare`: 2 and 2) and different groups of arguments.  CONCRETE example, not whole-class coverage; the class is the one stated in the module header.
--   * with the option OFF `topshare2` is REFUSED with the existing SR3x text (asserted, nothing generated);
--   * with the option ON the endpoint `topshare2.epD2M_endpoint` is generated, with the generator's own audit (`SR13 AUDIT OK`); its WHOLE statement is compared by `isDefEq`
--     with the independent hand-written `ShareConclWith ShareBnd 2 3`; 8 type-correct mutations are REJECTED; a closure audit follows;
--   * OUT-OF-CLASS refusals with the option ON (message asserted, no `epD2M_*` declaration): three callees sharing the leaf (Q1), an interleaved call list (Q2); and the
--     existing path's refusals are untouched: `topd3` (depth 3), a memory in a callee, a memory in the shared leaf.
-- NOT claimed: the other shared-leaf parents; that the generated template is correct for any further example; `RealChildA` is a history of past results; `O`, `T`, `AdmCtx`,
-- `MachineDefines` and the start world `JQC O 0 w` stay inside the conclusion (`epD2M_Bnd`).
namespace Tests.Compiler.SharedLeafGenTest
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingChildBoundaryTest
open Tests.Compiler.SeqDeepGenInstTest

structure Acc16Out (dom : DomainConfig) where
  s : Signal dom (BitVec 16)
  odd : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Acc16Out dom) dom := ⟨⟩

/-- the shared 16-bit leaf -/
@[hardware_module] def leaf16 {dom : DomainConfig} (x : Signal dom (BitVec 16)) : Acc16Out dom :=
  circuit do
    let a ← Signal.reg 0#16
    let as := (a : Signal dom (BitVec 16))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 5#16 : Signal dom (BitVec 16)) } : Acc16Out dom)

/-- a callee with ONE call of the leaf -/
@[hardware_module] def wrapQ {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : Acc16Out dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leaf16 (x + y)
    r <~ a.s + x
    return ({ s := rs, odd := a.odd } : Acc16Out dom)

/-- a callee with TWO calls of the leaf (different arguments) -/
@[hardware_module] def wrapP {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : Acc16Out dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leaf16 x
    let b := leaf16 y
    r <~ a.s + b.s
    return ({ s := rs, odd := a.odd &&& b.odd } : Acc16Out dom)

def topshare2 (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapQ v w
    let m2 := wrapP w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topshare2

/-- the call structure is ASSERTED by kernel-checked equations -/
theorem topshare2_callees : topshare2.machineData.shape.insts.map (·.1) = [``wrapQ, ``wrapQ, ``wrapP, ``wrapP] := by decide
theorem wrapQ_leaf : wrapQ.machineData.shape.insts.map (·.1) = [``leaf16, ``leaf16] := by decide
theorem wrapP_leaf : wrapP.machineData.shape.insts.map (·.1) = [``leaf16, ``leaf16, ``leaf16, ``leaf16] := by decide
theorem leaf16_nocalls : leaf16.machineData.shape.insts = [] := by decide

set_option maxHeartbeats 0 in
#machine_design_svNR Tests.Compiler.SharedLeafGenTest.topshare2 2

/-! ## out-of-class SHARED-leaf parents (for the refusals) -/

/-- a THIRD callee of the same leaf -/
@[hardware_module] def wrapR {dom : DomainConfig} (x y : Signal dom (BitVec 16)) : Acc16Out dom :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal dom (BitVec 16))
    let a := leaf16 y
    r <~ a.s + x
    return ({ s := rs, odd := a.odd } : Acc16Out dom)

/-- (Q1) THREE callees share the leaf -/
def topthree (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapQ v w
    let m2 := wrapP w v
    let m3 := wrapR v w
    r <~ Signal.mux (m.odd &&& m2.odd &&& m3.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topthree

/-- (Q2) the call list is not `[C₀, C₀, C₁, C₁]`: the first callee is called again after the second -/
def topinter (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  circuit do
    let r ← Signal.reg 0#16
    let rs := (r : Signal defaultDomain (BitVec 16))
    let m := wrapQ v w
    let m2 := wrapP w v
    let m3 := wrapQ w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& m3.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topinter

/-- a second callee with a MEMORY read that calls the 8-bit leaf `acc` (shared with `wrapM`) -/
@[hardware_module] def wrapM2 {dom : DomainConfig} (x y : Signal dom (BitVec 8)) (wa : Signal dom (BitVec 4)) (en : Signal dom Bool) :
    AccOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := acc x
    let rd := Signal.memoryComboRead wa y en wa
    r <~ a.s + rd
    return ({ s := rs, odd := a.odd } : AccOut dom)

#machine_endpoint wrapM2

/-- two callees with a memory read share the leaf `acc` -/
def topmemcallee (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) (wa : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrapM v w wa en
    let m2 := wrapM2 w v wa en
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topmemcallee

/-- a second callee of the memory-reading leaf `accM` -/
@[hardware_module] def wrapG2 {dom : DomainConfig} (x y : Signal dom (BitVec 8)) (wa : Signal dom (BitVec 4)) (en : Signal dom Bool) :
    AccOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := accM x wa en
    r <~ a.s + y
    return ({ s := rs, odd := a.odd } : AccOut dom)

#machine_endpoint wrapG2

/-- two callees share a leaf that reads a MEMORY -/
def topmemleaf (en : Signal defaultDomain Bool) (v w : Signal defaultDomain (BitVec 8)) (wa : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrapG v w wa en
    let m2 := wrapG2 w v wa en
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint topmemleaf

open Lean Meta Elab Command in
def refusedS (decl : Name) (needles : List String) (marker : String) : CommandElabM Unit := do
  let saved := (← get).messages
  elabCommand (← `(command| #machine_seq_parent_endpoint $(mkIdent decl)))
  let ms := (← get).messages
  let errs ← ms.toList.filterM fun m => pure (m.severity == .error)
  let txts ← errs.mapM fun m => m.data.toString
  modify fun s => { s with messages := saved }
  unless txts.length == 1 do throwError "SR13 AUDIT FAILED: expected exactly one refusal for {decl}, got {txts}"
  unless (txts.head!.splitOn marker).length > 1 do throwError "SR13 AUDIT FAILED: the refusal of {decl} does not come from `{marker}`: {txts.head!}"
  for n in needles do
    unless (txts.head!.splitOn n).length > 1 do throwError "SR13 AUDIT FAILED: the refusal of {decl} does not mention `{n}`: {txts.head!}"
  let n := (← getEnv).constants.fold (init := (0 : Nat)) fun (n : Nat) c _ =>
    if decl.isPrefixOf c && ((c.toString.splitOn ".epD2M").length > 1 || (c.toString.splitOn ".epD2_").length > 1) then n + 1 else n
  unless n == 0 do throwError "SR13 AUDIT FAILED: {n} epD2M_*/epD2_* declaration(s) exist for the refused {decl}"
  logInfo m!"SR13: {decl} REFUSED as expected: {txts.head!.take 400}…"

/-! ## option OFF: the existing refusal is unchanged -/

open Lean Meta Elab Command in
run_cmd do
  Tests.Compiler.SeqDeepGenDiffTest.refusedM ``Tests.Compiler.SharedLeafGenTest.topshare2
    ["REFUSED", "SAME leaf", "hdisjD", "leaf16", "wrapP", "unit SR3x", "RealChildA"]
  -- the parent of the second example creates nothing with the option off; the original `topshare` too
  Tests.Compiler.SeqDeepGenDiffTest.refusedM ``Tests.Compiler.SeqDeepGenDiffTest.topshare
    ["REFUSED", "SAME leaf", "hdisjD", "acc", "wrap3", "unit SR3x", "RealChildA"]

/-! ## option ON: out-of-class declarations are refused, with the failed condition named -/

set_option sparkle.sharedLeafCandidate true in
open Lean Meta Elab Command in
run_cmd do
  refusedS ``Tests.Compiler.SharedLeafGenTest.topthree ["REFUSED", "Q1", "exactly two different callees", "wrapR"] "unit SR13"
  refusedS ``Tests.Compiler.SharedLeafGenTest.topinter ["REFUSED", "Q2", "call list", "wrapQ", "wrapP"] "unit SR13"
  -- the existing path's refusals are untouched (this elaborator defers): depth 3, a memory in a callee, a memory in the shared leaf
  Tests.Compiler.SeqDeepGenDiffTest.refusedM ``Tests.Compiler.SeqDeepGenDiffTest.topd3 ["REFUSED", "depth 3", "wrap4", "wrap"]
  Tests.Compiler.SeqDeepGenDiffTest.refusedM ``Tests.Compiler.SeqDeepGenDiffTest.topdmem ["REFUSED", "memory in P", "topdmem"]
  Tests.Compiler.SeqDeepGenDiffTest.refusedM ``Tests.Compiler.SeqDeepGenDiffTest.topmix ["REFUSED", "LEAF", "cnt"]
  Tests.Compiler.SeqDeepGenDiffTest.refusedM ``Tests.Compiler.SharedLeafGenTest.topmemcallee ["REFUSED", "memory in C", "wrapM"]
  Tests.Compiler.SeqDeepGenDiffTest.refusedM ``Tests.Compiler.SharedLeafGenTest.topmemleaf ["REFUSED", "memory in G", "accM"]

/-! ## option ON: the second example is generated -/

set_option sparkle.sharedLeafCandidate true in
#machine_seq_parent_endpoint Tests.Compiler.SharedLeafGenTest.topshare2

#print axioms Tests.Compiler.SharedLeafGenTest.topshare2.epD2M_endpoint

/-! ## the expected WHOLE conclusion, written by hand (independent of the generator), compared by `isDefEq` -/

section
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

/-- The expected run boundary: laws `O`, `T` (PREMISES), the admissible contexts, `MachineDefines` of the callee `wrapQ` AND the leaf, then of `wrapP` AND the SAME leaf,
and a start world `JQC O 0 w` (the outermost entry's world). -/
def ShareBnd : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leaf16 leaf16.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leaf16 leaf16.machineData.shape ∧
    JQC O 0 w

/-- ALTERED boundary: the start world of the non-shared class (`JQ …` with a cache invariant instead of `JQC O 0 w`). -/
def ShareBndJQ : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leaf16 leaf16.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leaf16 leaf16.machineData.shape ∧
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))

/-- ALTERED boundary: start world `JQC O 1 w` -/
def ShareBndD1 : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leaf16 leaf16.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leaf16 leaf16.machineData.shape ∧
    JQC O 1 w

/-- ALTERED boundary: only ONE callee chain -/
def ShareBndOne : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leaf16 leaf16.machineData.shape ∧
    JQC O 0 w

/-- ALTERED boundary: the leaf's `MachineDefines` only ONCE -/
def ShareBndLeafOnce : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``leaf16 leaf16.machineData.shape ∧
    JQC O 0 w

/-- The expected conclusion of the depth-`n` endpoint of `topshare2` (`kP` own inputs read by the source), written out by hand. -/
def ShareConclWith (B : Tools.ShippingMachineShipsHier.CtxBnd) (n kP : Nat) (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State)
    (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State) (w : Void IO.RealWorld)
    (b : Sparkle.IR.AST.Module) (design : Design) : Prop :=
  ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (B mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = topshare2.machineData.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = topshare2.machineData.ss.length ∧
          ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool)
            (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs ``Tests.Compiler.SharedLeafGenTest.topshare2 (topshare2.machineData.bsIn.take kP) ids cache
              (fun j => ((fun i bools bits => topshare2.machineExtB i bools bits
                (Tools.ShippingMachineSource.stateLoop topshare2.machineInits (topshare2.machineBody i bools bits))) i bools bits j).val (T - 1 - t))
              (fun j n => ((fun i bools bits => topshare2.machineExt i bools bits
                (Tools.ShippingMachineSource.stateLoop topshare2.machineInits (topshare2.machineBody i bools bits))) i bools bits j n).val (T - 1 - t))
              (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              topshare2.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
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
                topshare2.machineData.shape.layout.outs[k]? = some o → (topshare2.machineSource i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)
            ∧ ∀ envs', DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  topshare2.machineData.shape.layout.outs[k]? = some o → (topshare2.machineSource i bools bits)[k]? = some f →
                  (envs'[j]'hj) o.name = f j)

end

open Lean Elab Command Meta in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let gen := ``Tests.Compiler.SharedLeafGenTest.topshare2.epD2M_endpoint
  let gt := (← getConstInfo gen).type
  forallTelescope gt fun xs concl => do
    let names ← xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
    unless names == ["mctx", "mref", "cctx", "cref", "w", "w'", "b", "design", "hr", "entry", "closes"] do
      throwError "SR13 AUDIT FAILED: endpoint binder names are {names}"
    let args := #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[6]!, xs[7]!]
    let mkW (B : Name) (n kP : Nat) : Lean.Expr :=
      mkAppN (mkConst ``ShareConclWith) (#[mkConst B, mkNatLit n, mkNatLit kP] ++ args)
    let mkC (c : Name) (n kP : Nat) : Lean.Expr := mkAppN (mkConst c) (#[mkNatLit n, mkNatLit kP] ++ args)
    let concl ← instantiateMVars concl
    let exp := mkW ``ShareBnd 2 3
    let alts := [(mkW ``ShareBnd 2 2, "kP 2"), (mkW ``ShareBnd 1 3, "depth 1"),
      (mkW ``ShareBndJQ 2 3, "start world JQ … ∧ (D₀ = 0 ∨ CacheInvA …) of the non-shared class"),
      (mkW ``ShareBndD1 2 3, "start world JQC O 1 w"),
      (mkW ``ShareBndOne 2 3, "boundary with ONE callee chain"),
      (mkW ``ShareBndLeafOnce 2 3, "boundary with the shared leaf's MachineDefines only ONCE"),
      (mkC ``Tests.Compiler.SeqDeepGenDiffConclTest.DiffConcl 2 3, "DiffConcl 2 3 (other declaration: topdiff2, other boundary)"),
      (mkC ``Tests.Compiler.SeqDeepGenArgsConclTest.ToptwoConcl 2 3, "ToptwoConcl 2 3 (other declaration: source, one callee)")]
    for (e, what) in [(concl, "the endpoint's conclusion"), (exp, "the expected conclusion")] ++ alts.map fun (e, w) => (e, s!"alt {w}") do
      if e.hasMVar then throwError "SR13 AUDIT FAILED: unassigned metavariables in {what}"
      for f in (Lean.collectFVars {} e).fvarIds do
        unless xs.any (·.fvarId! == f) do throwError "SR13 AUDIT FAILED: out-of-scope free variable in {what}"
      Meta.check e
    unless (← isDefEq concl exp) do
      throwError "SR13 AUDIT FAILED: the conclusion of the generated topshare2 endpoint is not definitionally ShareConclWith ShareBnd 2 3"
    for (e, w) in alts do
      if (← isDefEq concl e) then throwError "SR13 AUDIT FAILED: the altered expectation ({w}) was ACCEPTED"
  logInfo m!"SR13: the conclusion of the GENERATED topshare2.epD2M_endpoint is isDefEq to the hand-written ShareConclWith ShareBnd 2 3; kP 2, depth 1, the non-shared start world, JQC O 1, one-chain boundary, leaf-once boundary, DiffConcl 2 3 and ToptwoConcl 2 3 are REJECTED"

/-! ## closure audit (independent of the generator's own) -/

open Lean Elab Command Meta in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ep := ``Tests.Compiler.SharedLeafGenTest.topshare2.epD2M_endpoint
  stdAxioms ep
  let cl ← depClosure ep
  let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
    `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
    `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SR13 AUDIT FAILED: the forbidden name {f} does not exist (the audit would check nothing)"
  let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR13 AUDIT FAILED: old boundary / old child predicate in closure: {bad}"
  let oldGen : List Name := [`Tests.Compiler.SharedLeafGenTest.topshare2.machine_composedNR2, `Tests.Compiler.SharedLeafGenTest.topshare2.machine_design_svNR2,
    `Tests.Compiler.SharedLeafGenTest.wrapQ.machine_composedNR1, `Tests.Compiler.SharedLeafGenTest.wrapQ.seq_child_runN_ofR1,
    `Tests.Compiler.SharedLeafGenTest.wrapP.machine_composedNR1, `Tests.Compiler.SharedLeafGenTest.wrapP.seq_child_runN_ofR1]
  for f in oldGen do
    unless (← getEnv).contains f do throwError "SR13 AUDIT FAILED: the old generated name {f} does not exist (the audit would check nothing)"
    if cl.contains f then throwError "SR13 AUDIT FAILED: the old generated theorem {f} is in the closure"
  -- the hdisjD-needing pieces are NOT used, the generic shared-leaf pieces ARE
  for no in [`Tests.Compiler.SharedLeafGenTest.topshare2.epD2M_closesA, `Tests.Compiler.SharedLeafGenTest.topshare2.epD2M_disj] do
    if (← getEnv).contains no then throwError "SR13 AUDIT FAILED: {no} exists (it must not be generated for a shared leaf)"
  for must in [``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingQuadLeafGeneric.quad_machineRun,
      ``Tools.ShippingQuadLeafGeneric.leafCallee_ifaceP, ``Tools.ShippingQuadLeafGeneric.leafCallee_calleeOK,
      ``Tools.ShippingTopShareRun.machineSynth_ne_none4, ``Tools.ShippingTopShareRun.topshare_closing4,
      ``Tools.ShippingTopShareRan.machineRanA_start0, ``Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc] do
    unless cl.contains must do throwError "SR13 AUDIT FAILED: {must} not in the closure of {ep}"
  logInfo m!"SR13 CLOSURE AUDIT: {ep}: standard axioms; closure {cl.size} constants; none of ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/machineRunNC_of_real/seqChildRunN_of_composedC, no RefLaws/RefLawsCore/toAOps/toA; the old generated composed theorems are not in it; epD2M_closesA / epD2M_disj do not exist; quad_closes0, machineSynth_ne_none4, topshare_closing4, machineRanA_start0 are in it"

end Tests.Compiler.SharedLeafGenTest
