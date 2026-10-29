import Tools.ShippingGen5RunReads
import Tools.ShippingGen5T1ND
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: written without running Lean. No sorry / axiom / native_decide.

/-! # DG-RUNREADS checks (Tools/ShippingGen5RunReads.lean; scripts/gen5/DG_RUNREADS_FREEZE.md b8f9cd7a + notes ce3f7e2c)

1. `RunReadsAt`: its constructor telescope against an independently written `ExpRunReadsAt` (same parameter fvars;
   field names, order, `binderInfo`, types by `isDefEq`, no extra field); the negative structure
   `MutRunReadsAtEnvR` (translator env `envR'` in `chain`) must be rejected by the same comparison.
2. Expected types of RR1-RR3: the freeze §1 statements (fully bound). Mutants (signature / defeq rejections, not
   semantic counterexamples): RR3 without `closes`; RR3 with `JQC` at the chain world `w3` (bound inside the
   conclusion by its `getEnv` link to `w5`); RR2 with `JQC O n w₂` after the machine run (the `htr`-requiring claim);
   RR1 with `JQ` (no cache half).
3. Closure audit (full reachable closure, explicit bodies): RR1-RR3 reach none of `synthesizeFromConst_machine_split2A`,
   `BodyStepC`, `MachineRunJQC`, any `T1Hyp`/`T1HypND` field (named projection, raw `.proj`, recursor). Positive reach:
   `core_chain`, `keepsA_framed`, `MachineClosesAtA`, RR1, RR2 (RR3). Controls: split2A direct, `BodyStepC` through
   two helpers, `T1Hyp.dec`, `T1HypND.casesOn`, raw `.proj` (unit), unrelated (not flagged).
4. Axioms. -/

/-! ## 0. Fixtures -/
namespace Tests.Gen5.RunReadsHelperA
theorem helperA : True := (fun _ => trivial) @Tools.ShippingChildDepthC.BodyStepC
end Tests.Gen5.RunReadsHelperA
namespace Tests.Gen5.RunReadsHelperB
theorem helperB : True := Tests.Gen5.RunReadsHelperA.helperA
end Tests.Gen5.RunReadsHelperB
namespace Tests.Gen5.RunReadsFixture
theorem badSplit : True := (fun _ => trivial) @Tools.ShippingMachineOutcomeA.synthesizeFromConst_machine_split2A
theorem badBodyStep : True := Tests.Gen5.RunReadsHelperB.helperB
theorem badDec : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.dec
theorem badNDCases : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.casesOn.{0}
theorem unrelated : True := trivial
end Tests.Gen5.RunReadsFixture

namespace Tests.Gen5.RunReadsCheck
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Sparkle.IR.Builder
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC
open Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA
open Tools.ShippingChildRunAMain
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids (MachineClosesAtA)

open Sparkle.IR.AST (Design)
open Tools.ShippingGen5RunReads
open Tests.Gen3.ExpectedType

/-! ## 1. `RunReadsAt` -/

structure ExpRunReadsAt (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (X : Name) (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module)
    (D : Sparkle.IR.AST.Design) (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (shape : MachineShape)
    (w5 w6 : Void IO.RealWorld) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  chain : ∃ (s : Tools.ShippingEntryReadsLinked.CoreSaved) (w1 w2 w3 w4 wl : Void IO.RealWorld),
    s.profile = b ∧
    RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1 ∧
    RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 ∧
    RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire envR e h t n) (profLogIO b) X shape)
      mctx mref cctx cref w5 (some (raw, D)) w6 ∧
    RunsTo (show MetaM Unit from profLogIO b
      s!"[profile] synthesizeCombinational {X} machine certified front end") mctx mref cctx cref w6 () wl ∧
    RunsTo (sparkleSubModuleCache.modify (·.insert X (raw, D)) : MetaM Unit) mctx mref cctx cref wl () w4 ∧
    RunsTo (Tools.ShippingMachineOutcomeA3.coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg)
      mctx mref cctx cref w4 () w'
  gates : certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (instancePredicate envR) = none
  shapeEq : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape


structure MutRunReadsAtEnvR (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (X : Name) (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module)
    (D : Sparkle.IR.AST.Design) (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (shape : MachineShape)
    (w5 w6 : Void IO.RealWorld) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  chain : ∃ (s : Tools.ShippingEntryReadsLinked.CoreSaved) (w1 w2 w3 w4 wl : Void IO.RealWorld),
    s.profile = b ∧
    RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1 ∧
    RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 ∧
    RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire envR' e h t n) (profLogIO b) X shape)
      mctx mref cctx cref w5 (some (raw, D)) w6 ∧
    RunsTo (show MetaM Unit from profLogIO b
      s!"[profile] synthesizeCombinational {X} machine certified front end") mctx mref cctx cref w6 () wl ∧
    RunsTo (sparkleSubModuleCache.modify (·.insert X (raw, D)) : MetaM Unit) mctx mref cctx cref wl () w4 ∧
    RunsTo (Tools.ShippingMachineOutcomeA3.coreFinally s.depth s.sf s.sw s.sl s.sp s.sc s.ss s.sg)
      mctx mref cctx cref w4 () w'
  gates : certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (instancePredicate envR) = none
  shapeEq : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape


/-- Constructor telescope comparison of two structures on the same parameter fvars. -/
def structPair (a b : Name) : MetaM Nat := do
  let env ← getEnv
  let some (.inductInfo i1) := env.find? a | throwError "no {a}"
  let some (.inductInfo i2) := env.find? b | throwError "no {b}"
  unless i1.numParams == i2.numParams do throwError "RR STRUCT FAILED: numParams"
  let c1 ← getConstInfo (a ++ `mk)
  let c2 ← getConstInfo (b ++ `mk)
  forallTelescope c1.type fun xs _ => do
    let ps := xs[:i1.numParams].toArray
    let mut t2 ← instantiateForall c2.type ps
    let mut j : Nat := 0
    for x in xs[i1.numParams:].toArray do
      let ld ← x.fvarId!.getDecl
      match t2 with
      | .forallE n ty bd bi =>
        unless n == ld.userName do throwError "RR STRUCT FAILED: field {j}: {n} ≠ {ld.userName}"
        unless bi == ld.binderInfo do throwError "RR STRUCT FAILED: binderInfo of {n}"
        unless ← isDefEq ty ld.type do throwError "RR STRUCT FAILED: type of {n}"
        t2 := bd.instantiate1 x
        j := j + 1
      | _ => throwError "RR STRUCT FAILED: {b}.mk has fewer fields (at {ld.userName})"
    if t2.isForall then throwError "RR STRUCT FAILED: {b}.mk has an EXTRA field"
    return j

run_cmd Lean.Elab.Command.liftTermElabM do
  let j ← structPair ``RunReadsAt ``Tests.Gen5.RunReadsCheck.ExpRunReadsAt
  logInfo m!"RR STRUCT OK RunReadsAt: {j} fields = ExpRunReadsAt (names, order, binderInfo, types), no extra field"
  let acc ← try
      let _ ← structPair ``RunReadsAt ``Tests.Gen5.RunReadsCheck.MutRunReadsAtEnvR
      pure true
    catch e => do
      logInfo m!"RR STRUCT NEGATIVE REJECTED MutRunReadsAtEnvR: {e.toMessageData}"
      pure false
  if acc then throwError "RR STRUCT NEGATIVE ACCEPTED: MutRunReadsAtEnvR"

/-! ## 2. Expected types and mutants -/

def ExpRR1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {X : Name} {D : Nat}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1),
    JQC O (D + 1) w1

def ExpRR2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {tenv : Environment} {b : Bool} {X : Name} {n : Nat} {ci : ConstantInfo} {isInst : Lean.Expr → Bool}
    {m : Sparkle.IR.AST.Module} {d : Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none) (miss : mixedCertifiedShape? false [] ci isInst = none)
    (hw : JQC O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false true
      ci isInst) mctx mref cctx cref w (m, d) w'),
    ∃ (envR' : Environment) (w₁ : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR' w₁ ∧ JQC O n w₁ ∧
      ∀ shape, machineShape? false [] ci (structEnv envR') = some shape →
        ∃ (r : Option Res) (w₂ : Void IO.RealWorld),
          RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X shape)
            mctx mref cctx cref w₁ r w₂ ∧
          ((∃ res, r = some res ∧ res = (m, d) ∧ ∃ wl : Void IO.RealWorld,
              RunsTo (show MetaM Unit from profLogIO b
                s!"[profile] synthesizeCombinational {X} machine certified front end") mctx mref cctx cref w₂ () wl ∧
              RunsTo (sparkleSubModuleCache.modify (·.insert X res) : MetaM Unit) mctx mref cctx cref wl () w') ∨
           (r = none ∧ RunsTo (legacyTail (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false ci)
              mctx mref cctx cref w₂ (m, d) w'))

def ExpRR3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {X : Name}
    {shape : MachineShape} {D₀ : Nat} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6 ∧ JQC O (D₀ + 1) w5

def MutRR3NoCloses : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {X : Name}
    {shape : MachineShape} {D₀ : Nat} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (entry : MachineDefines mctx mref cctx cref X shape),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6 ∧ JQC O (D₀ + 1) w5

def MutRR3JqcW3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {X : Name}
    {shape : MachineShape} {D₀ : Nat} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6 ∧ ∃ w3 : Void IO.RealWorld,
        RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 ∧ JQC O (D₀ + 1) w3

def MutRR2JqcAfter : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {tenv : Environment} {b : Bool} {X : Name} {n : Nat} {ci : ConstantInfo} {isInst : Lean.Expr → Bool}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none) (miss : mixedCertifiedShape? false [] ci isInst = none)
    (hw : JQC O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false true
      ci isInst) mctx mref cctx cref w (m, d) w'),
    ∃ (envR' : Environment) (w₁ : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR' w₁ ∧ JQC O n w₁ ∧
      ∀ shape, machineShape? false [] ci (structEnv envR') = some shape →
        ∃ (r : Option Res) (w₂ : Void IO.RealWorld),
          RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X shape)
            mctx mref cctx cref w₁ r w₂ ∧ JQC O n w₂ ∧
          ((∃ res, r = some res ∧ res = (m, d) ∧ ∃ wl : Void IO.RealWorld,
              RunsTo (show MetaM Unit from profLogIO b
                s!"[profile] synthesizeCombinational {X} machine certified front end") mctx mref cctx cref w₂ () wl ∧
              RunsTo (sparkleSubModuleCache.modify (·.insert X res) : MetaM Unit) mctx mref cctx cref wl () w') ∨
           (r = none ∧ RunsTo (legacyTail (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false ci)
              mctx mref cctx cref w₂ (m, d) w'))

def MutRR1JQ : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {X : Name} {D : Nat}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1),
    JQ O.quiet (D + 1) w1

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``coreHead_jqcA ``ExpRR1
  checkExpected ``fromConst_machine_linkA ``ExpRR2
  checkExpected ``runReads_of_run ``ExpRR3
  checkMutant ``runReads_of_run ``MutRR3NoCloses
  checkMutant ``runReads_of_run ``MutRR3JqcW3
  checkMutant ``fromConst_machine_linkA ``MutRR2JqcAfter
  checkMutant ``coreHead_jqcA ``MutRR1JQ

/-! ## 3. Closure audit -/

def forbidConsts : List Name :=
  [``Tools.ShippingMachineOutcomeA.synthesizeFromConst_machine_split2A, ``Tools.ShippingChildDepthC.BodyStepC,
   ``Tools.ShippingServedRealA.MachineRunJQC,
   ``Tools.ShippingGen2.T1Hyp.rec, ``Tools.ShippingGen2.T1Hyp.casesOn, ``Tools.ShippingGen2.T1Hyp.recOn,
   ``Tools.ShippingGen2.T1HypND.rec, ``Tools.ShippingGen2.T1HypND.casesOn, ``Tools.ShippingGen2.T1HypND.recOn] ++
  (["pkg", "defines", "closes", "dec", "closed"].map fun f => (``Tools.ShippingGen2.T1Hyp).str f) ++
  (["pkg", "defines", "closes", "closed"].map fun f => (``Tools.ShippingGen2.T1HypND).str f)

def badProj (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .proj s _ _ => s == ``Tools.ShippingGen2.T1Hyp || s == ``Tools.ShippingGen2.T1HypND
    | _ => false).isSome

def body? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure AReach where
  hit : Option (List Name) := none
  seen : NameSet := {}
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Nat := 0

def reach (root : Name) (cap : Nat := 3000000) : MetaM AReach := do
  let env ← getEnv
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "RR AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | continue
    let body := body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques + 1 }
    if badProj ci.type || (body.map badProj).getD false then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if forbidConsts.contains u then return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  unless badProj (.proj ``Tools.ShippingGen2.T1Hyp 3 (.bvar 0)) do throwError "RR AUDIT FAILED: raw T1Hyp proj missed"
  unless badProj (.proj ``Tools.ShippingGen2.T1HypND 1 (.bvar 0)) do throwError "RR AUDIT FAILED: raw T1HypND proj missed"
  if badProj (.proj ``Prod 0 (.bvar 0)) then throwError "RR AUDIT FAILED: unrelated raw proj flagged"
  logInfo "RR CONTROL rawProj: T1Hyp/T1HypND flagged, Prod not flagged"
  let F := `Tests.Gen5.RunReadsFixture
  for (c, bad) in [(F ++ `badSplit, true), (F ++ `badBodyStep, true), (F ++ `badDec, true),
      (F ++ `badNDCases, true), (F ++ `unrelated, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "RR AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "RR AUDIT FAILED: detector flags {c}"
    logInfo m!"RR CONTROL {c}: {toString r.hit}"
  let base := [``Tools.ShippingChildVCA.keepsA_framed]
  for (c, req) in [(``coreHead_jqcA, base), (``fromConst_machine_linkA, base),
      (``runReads_of_run, base ++ [``Tools.ShippingEntryReadsLinked.core_chain, ``MachineClosesAtA,
        ``coreHead_jqcA, ``fromConst_machine_linkA])] do
    let r ← reach c
    if let some p := r.hit then throwError "RR AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RR AUDIT FAILED {c}: {t} not reached"
    logInfo m!"RR REACH {c}: no split2A / BodyStepC / MachineRunJQC / T1Hyp / T1HypND (named, raw proj, recursor); reaches {req} (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques})"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``coreHead_jqcA, ``fromConst_machine_linkA, ``runReads_of_run] do
    checkAxioms n

end Tests.Gen5.RunReadsCheck
