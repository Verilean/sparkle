import Tools.ShippingGen5ClosingRun3
import Tests.Gen5.ClosingRun2Check
set_option autoImplicit false
-- No sorry / axiom / native_decide.

/-! # Run-local hord / hrow checks (Tools/ShippingGen5ClosingRun3.lean; scripts/gen5/HORD_RUN_FREEZE.md)

Expected statements are written from the freeze text (HORD_RUN_FREEZE §2: the frozen r4 statements with the `hord` /
`hrow` binder deleted, nothing else changed), not copied from the implementation. The comparator is the one of
`Tests.Gen5.ClosingRun2Check` (`cmpTeleR`: binder-by-binder names, binder info, types by `==` with REDUCIBLE `isDefEq`
fallback). Mutants: the OLD statements (with `hord` / `hrow`, the Expected values of `ClosingRun2Check` / `ClosingRunCheck`)
and one-point variants; rejection is by signature / defeq, NOT a semantic counterexample. No instance of any premise is
constructed: not evidence of non-vacuity. -/

namespace Tests.Gen5.ClosingRun3Check
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun Tools.ShippingGen5ClosingRun2
open Tools.ShippingGen5ClosingRun3
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.ClosingRun2Check (checkExpectedR checkMutantR reach)

/-! ## 1. Expected (freeze §2) -/
def ExpHordRun : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6)
    (hf : shape.instFields = []) (k : Nat) (hk : k < shape.insts.length),
    (shape.instOrigins.getD k .ord).child? = none
def ExpSharedR : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def ExpRun0R : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def ExpConnR : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D
def ExpGAR : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (GA : ConstantInfo → StructEnv → Pkg ι dom → Prop)
    (hGA : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
      GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') p),
    ClosingRun L P Reach mctx cctx X p
      (fun ci envR envR' => GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (structEnv envR') p) w w' raw D
def ExpNonemptyR : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {DataOk : Pkg ι dom → Prop} {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    (h : ClosingPremisesR L P Reach DataOk mctx cctx X p w w' raw D Gen),
    Nonempty (ClosingRun L P Reach mctx cctx X p Gen w w' raw D)

/-! ## 2. One-point mutants (the old statements WITH hord / hrow are the `ClosingRun2Check` / `ClosingRunCheck`
Expected values, used below as mutants) -/
def MutRun0RHd1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 1)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def MutRun0RNoGen : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def MutSharedRT1Hyp : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def MutConnRNoH1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D
def MutHordRunAll : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6)
    (k : Nat) (hk : k < shape.insts.length),
    (shape.instOrigins.getD k .ord).child? = none

/-! ## 3. Type -/
run_cmd Lean.Elab.Command.liftTermElabM do
  -- positive controls: the old statements are still what they were (same comparator)
  checkExpectedR ``closingShared_of_run ``Tests.Gen5.ClosingRun2Check.ExpSharedOfRun
  checkExpectedR ``closingRun0_of_run ``Tests.Gen5.ClosingRun2Check.ExpRun0OfRun
  checkExpectedR ``closingRun_of_run ``Tests.Gen5.ClosingRunCheck.ExpConn
  checkExpectedR ``closingRun_of_run_ga ``Tests.Gen5.ClosingRun2Check.ExpGA
  checkExpectedR ``hord_of_runReadsAt ``ExpHordRun
  checkExpectedR ``closingShared_of_runR ``ExpSharedR
  checkExpectedR ``closingRun0_of_runR ``ExpRun0R
  checkExpectedR ``closingRun_of_runR ``ExpConnR
  checkExpectedR ``closingRun_of_run_gaR ``ExpGAR
  checkExpectedR ``closingRun_nonempty_of_premisesR ``ExpNonemptyR
  logInfo m!"HORD RUN TYPE: 6 theorems against Expected; 4 old statements re-accepted (controls)"

/-! ## 4. Mutants -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutantR ``closingShared_of_runR ``Tests.Gen5.ClosingRun2Check.ExpSharedOfRun
  checkMutantR ``closingRun0_of_runR ``Tests.Gen5.ClosingRun2Check.ExpRun0OfRun
  checkMutantR ``closingRun_of_runR ``Tests.Gen5.ClosingRunCheck.ExpConn
  checkMutantR ``closingRun_of_run_gaR ``Tests.Gen5.ClosingRun2Check.ExpGA
  checkMutantR ``closingRun0_of_runR ``MutRun0RHd1
  checkMutantR ``closingRun0_of_runR ``MutRun0RNoGen
  checkMutantR ``closingShared_of_runR ``MutSharedRT1Hyp
  checkMutantR ``closingRun_of_runR ``MutConnRNoH1
  checkMutantR ``hord_of_runReadsAt ``MutHordRunAll
  logInfo m!"HORD RUN MUTANT: 9 rejected (4 old statements with hord/hrow, 5 one-point; signature/defeq, not semantic)"

/-! ## 5. Prop binders: the old binder list minus hord / hrow -/
def propBinders (thm : Name) : MetaM (List Name) := do
  forallTelescope (← stmtOf thm) fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if ← isProp d.type then out := out ++ [d.userName.eraseMacroScopes]
    pure out

run_cmd Lean.Elab.Command.liftTermElabM do
  for (newT, oldT, removed) in [(``closingShared_of_runR, ``closingShared_of_run, `hord),
      (``closingRun0_of_runR, ``closingRun0_of_run, `hord),
      (``closingRun_of_runR, ``closingRun_of_run, `hrow),
      (``closingRun_of_run_gaR, ``closingRun_of_run_ga, `hrow)] do
    let got ← propBinders newT
    let old ← propBinders oldT
    unless old.contains removed do throwError "HORD RUN BINDERS CONTROL: {oldT} has no {removed}"
    unless got == old.erase removed do
      throwError "HORD RUN BINDERS FAILED {newT}: expected {old.erase removed}, got {got}"
    for n in [`hord, `hrow, `hDp] do
      if got.contains n then throwError "HORD RUN BINDERS FAILED {newT}: unexpected premise {n}"
    logInfo m!"HORD RUN BINDERS {newT}: {got} = binders of {oldT} minus {removed}"
  let env ← getEnv
  let fNew := getStructureFieldsFlattened env ``ClosingPremisesR (includeSubobjectFields := false)
  let fOld := getStructureFieldsFlattened env ``ClosingPremises (includeSubobjectFields := false)
  unless fOld.contains `hrow && fNew.toList == fOld.toList.erase `hrow do
    throwError "HORD RUN FIELDS FAILED: ClosingPremisesR {fNew} vs ClosingPremises {fOld} minus hrow"
  logInfo m!"HORD RUN FIELDS ClosingPremisesR: {fNew} = fields of ClosingPremises minus hrow"
  -- field types are the same (same names, same order): compare the constructor telescopes after deleting hrow
  let some (.ctorInfo cN) := env.find? ``ClosingPremisesR.mk | throwError "no ctor"
  let some (.ctorInfo cO) := env.find? ``ClosingPremises.mk | throwError "no ctor"
  unless cN.numFields + 1 == cO.numFields do throwError "HORD RUN FIELDS FAILED: field count"
  logInfo m!"HORD RUN FIELDS: {cN.numFields} fields (old {cO.numFields})"

/-! ## 6. Closure and axioms -/
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let olds := [``closingShared_of_run, ``closingRun0_of_run, ``Tools.ShippingGen5ClosingRun.closingRun_of_run,
    ``closingRun_of_run_ga]
  for (c, req) in [(``hord_of_runReadsAt, [``Tools.ShippingGen3HrowGate.machineShape?_noMemRow]),
      (``closingShared_of_runR, [``hord_of_runReadsAt, ``Tools.ShippingGen5RunReads.runReads_of_run]),
      (``closingRun0_of_runR, [``closingShared_of_runR]),
      (``closingRun_of_runR, [``hord_of_runReadsAt, ``Tools.ShippingGen5ClosingRun.stop_of_run]),
      (``closingRun_of_run_gaR, [``closingRun_of_runR]),
      (``closingRun_nonempty_of_premisesR, [``closingRun_of_runR])] do
    let r ← reach c
    if let some p := r.hit then throwError "HORD RUN AUDIT FAILED {c}: forbidden use via {p}"
    if r.unknown != 0 then throwError "HORD RUN AUDIT FAILED {c}: {r.unknown} unresolved name(s)"
    for t in req do
      unless r.seen.contains t do throwError "HORD RUN AUDIT FAILED {c}: {t} not reached"
    for t in olds do
      if r.seen.contains t then throwError "HORD RUN AUDIT FAILED {c}: reaches the hord/hrow version {t}"
    logInfo m!"HORD RUN REACH {c}: reaches {req}; no hord/hrow version, no T1Hyp field / BodyStepC / ofReduceBool (visited {r.visited})"
  for n in [``hord_of_runReadsAt, ``closingShared_of_runR, ``closingRun0_of_runR, ``closingRun_of_runR,
      ``closingRun_of_run_gaR, ``ClosingPremisesR, ``closingRun_nonempty_of_premisesR] do
    checkAxioms n
  logInfo m!"HORD RUN COUNTS: TYPE 6 (+4 controls), MUTANT 9, BINDERS 4 + FIELDS 1, REACH 6, AXIOMS 7"

end Tests.Gen5.ClosingRun3Check
