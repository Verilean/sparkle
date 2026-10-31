import Tools.ShippingGen4FbFin0
import Tools.ShippingMemoInv
import Tools.ShippingLegacySemMemoWalk
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- BUILT (unit FB-11): kjob lake build Tests.Gen4.FbFin0Check exit 0, 810 jobs (Pod build, NOT a clean issue-linked build; that is the coder's). Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §19.5/§19.7 (rev11, scoped approved at 23682b7b); Expected types typed again from §19.5.
-- Checks: TYPE (independent Expected typed again from §17.3), MUTANT (signature/defeq rejections, NOT semantic counterexamples),
-- AXIOMS, value-closure audit with a `missing` list that FAILS when non-zero (an unknown constant is not "clean"), and controls.

namespace Tests.Gen4.FbFin0Fixture
theorem helperA : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
end Tests.Gen4.FbFin0Fixture
namespace Tests.Gen4.FbFin0FixtureB
theorem helperB : True := Tests.Gen4.FbFin0Fixture.helperA
end Tests.Gen4.FbFin0FixtureB
namespace Tests.Gen4.FbFin0FixtureC
theorem badDirect : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
theorem badOuterMiss : True := (fun _ => trivial) @Tools.ShippingLegacySem.outer_miss
theorem badIndirect : True := Tests.Gen4.FbFin0FixtureB.helperB
theorem goodUnrelated : True := trivial
theorem goodFb3 : True := (fun _ => trivial) @Tools.ShippingGen4FbInv.a4_inv_machine_or_R4RunInv
end Tests.Gen4.FbFin0FixtureC

namespace Tests.Gen4.FbFin0Check
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
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingMachineOutcomeA Tools.ShippingMachineOutcomeA3 Tools.ShippingMachineOutcomeA4
open Tools.ShippingGen4FbR4
open Tools.ShippingGen2 Tools.ShippingGen4FbInv Tools.ShippingGen4FbTailInv Tools.ShippingGen4FbFin0
open Tests.Gen3.ExpectedType


/-- independent copy of the `R4RunInvT` body (typed again from §19.5 / FB-4; `ExpR4RunInvT` of FbTailInvCheck is NOT reused). -/
def ExpR4RunInvT4 {{ι : Type}} {{dom : ι → Sparkle.Core.Domain.DomainConfig}}
    {{mref : ST.Ref IO.RealWorld Meta.State}} {{cref : ST.Ref IO.RealWorld Core.State}}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (D : Nat)
    (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ (tenv : Lean.Environment) (pb : Bool) (ci : ConstantInfo) (envR' : Lean.Environment)
    (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
    InvAt L P Reach (D + 1) w₄ ∧ InvAt L P Reach (D + 1) w₆ ∧ InvAt L P Reach (D + 1) w₅ ∧
    RunsTo (getConstInfo declName) mctx mref cctx cref w₁ ci w₂ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₂ tenv w₃ ∧
    JQC L.O (D + 1) w₃ ∧
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w₃ envR' w₄ ∧
    machineShape? false [] (entryConst true false [] ci (instancePredicate tenv)
      (userInliner tenv) (structEnv tenv)) (structEnv envR') = some shape ∧
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName shape) mctx mref cctx cref w₄ none w₆ ∧
    JQC L.O (D + 1) w₄ ∧ JQC L.O (D + 1) w₆ ∧
    (∃ (sf : Std.HashMap Name Expr) (sw : Std.HashMap String Nat)
      (sl sp sc : Std.HashMap String String) (ss : Std.HashMap (UInt64 × String) String)
      (sg : Std.HashMap String String),
      RunsTo (coreFinally D sf sw sl sp sc ss sg) mctx mref cctx cref w₅ () w' ∧
      FinallyRestores (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref) D sf sw sl sp sc ss sg w₅ w' ∧
      (D = 0 → sf = {} ∧ sw = {} ∧ sl = {} ∧ sp = {} ∧ sc = {} ∧ ss = {} ∧ sg = {}) ∧
      (D ≠ 0 → StartReadsN (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
        declName pb D w sf sw sl sp sc ss sg)) ∧
    JQC L.O D w' ∧
    RunsTo (legacyTail
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
      declName [] false
      (entryConst true false [] ci (instancePredicate tenv) (userInliner tenv)
        (structEnv tenv))) mctx mref cctx cref w₆ (m, d) w₅ ∧
    ∃ (t : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design) (w₇ : Void IO.RealWorld),
      RunsTo (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO pb)
        declName shape.binders shape.body) mctx mref cctx cref w₄ (t, d₀) w₇ ∧
      JQC L.O (D + 1) w₇ ∧
      ((Sparkle.IR.Machine.closeLets shape.layout.lets t = none ∧ w₆ = w₇) ∨
       (∃ t', Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧ shape.insts ≠ [] ∧
         ((shape.instFields.isEmpty = true ∧
            RunsTo (closeInstsM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆) ∨
          (shape.instFields.isEmpty = false ∧
            RunsTo (closeInstsGM shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀)
              mctx mref cctx cref w₇ none w₆))))

def ExpFin0 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpR4RunInvT4 L P Reach mctx cctx 0 declName shape m d w w'),
    InvAt L P Reach 0 w'

def ExpFin0Companion : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    A4MachineSideA L.O mctx cctx 0 declName shape m d w w' ∨
      (ExpR4RunInvT4 L P Reach mctx cctx 0 declName shape m d w w' ∧ InvAt L P Reach 0 w')

def MutDepth1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpR4RunInvT4 L P Reach mctx cctx 0 declName shape m d w w'),
    InvAt L P Reach 1 w'

def MutStartWorld : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpR4RunInvT4 L P Reach mctx cctx 0 declName shape m d w w'),
    InvAt L P Reach 0 w

def MutJQCOnly : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpR4RunInvT4 L P Reach mctx cctx 0 declName shape m d w w'),
    JQC L.O 0 w'

def MutNoHA : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpR4RunInvT4 L P Reach mctx cctx 0 declName shape m d w w'),
    InvAt L P Reach 0 w'

def MutHypDepth1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : ExpR4RunInvT4 L P Reach mctx cctx 1 declName shape m d w w'),
    InvAt L P Reach 0 w'

def MutSideInv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    (A4MachineSideA L.O mctx cctx 0 declName shape m d w w' ∧ InvAt L P Reach 0 w') ∨
      (ExpR4RunInvT4 L P Reach mctx cctx 0 declName shape m d w w' ∧ InvAt L P Reach 0 w')

def MutInrNoConcl : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 1)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    A4MachineSideA L.O mctx cctx 0 declName shape m d w w' ∨
      ExpR4RunInvT4 L P Reach mctx cctx 0 declName shape m d w w'

def MutHCDepth0 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach 0 w) (hC : ChildKeepsInv L P Reach 0)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    A4MachineSideA L.O mctx cctx 0 declName shape m d w w' ∨
      (ExpR4RunInvT4 L P Reach mctx cctx 0 declName shape m d w w' ∧ InvAt L P Reach 0 w')

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``tFin0_of_r4RunInvT ``ExpFin0
  checkExpected ``a4_inv_tail_fin0 ``ExpFin0Companion
  checkMutant ``tFin0_of_r4RunInvT ``MutDepth1
  checkMutant ``tFin0_of_r4RunInvT ``MutStartWorld
  checkMutant ``tFin0_of_r4RunInvT ``MutJQCOnly
  checkMutant ``tFin0_of_r4RunInvT ``MutNoHA
  checkMutant ``tFin0_of_r4RunInvT ``MutHypDepth1
  checkMutant ``a4_inv_tail_fin0 ``MutSideInv
  checkMutant ``a4_inv_tail_fin0 ``MutInrNoConcl
  checkMutant ``a4_inv_tail_fin0 ``MutHCDepth0

/-! ## Value-closure audit (§14.4): `missing` constants make the audit FAIL ("not established") -/
def fbNew : List Name :=
  [``tFin0_of_r4RunInvT, ``a4_inv_tail_fin0]
def fbForbidden (n : Name) : Bool := (`Tools.ShippingMemo).isPrefixOf n
def fbBody? : ConstantInfo → Option Lean.Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none
partial def fbConsts (e : Lean.Expr) : Array Name :=
  let rec go (e : Lean.Expr) (seen : Std.HashSet Lean.Expr) (acc : Array Name) :
      Std.HashSet Lean.Expr × Array Name :=
    if seen.contains e then (seen, acc) else
    let seen := seen.insert e
    match e with
    | .const c _ => (seen, acc.push c)
    | .proj s _ b => go b seen (acc.push s)
    | .app f a => let (s, r) := go f seen acc; go a s r
    | .lam _ t b _ => let (s, r) := go t seen acc; go b s r
    | .forallE _ t b _ => let (s, r) := go t seen acc; go b s r
    | .letE _ t v b _ => let (s, r) := go t seen acc; let (s, r) := go v s r; go b s r
    | .mdata _ b => go b seen acc
    | _ => (seen, acc)
  (go e {} #[]).2
structure FbReach where
  hit : Option (List Name) := none
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Array Name := #[]
  missing : Array Name := #[]
  deriving Inhabited
def fbReach (root : Name) (cap : Nat := 3000000) : MetaM FbReach := do
  let env ← getEnv
  let mut out : FbReach := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then
      throwError "FB11 AUDIT INCOMPLETE at {root}: more than {cap} constants; non-reference NOT established"
    let some ci := env.find? c | do
      out := { out with missing := out.missing.push c }
      continue
    let body := fbBody? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques.push c }
    let used := fbConsts ci.type ++ (body.map fbConsts).getD #[]
    for u in used do
      if fbForbidden u then
        return { out with hit := some (path ++ [u]) }
      unless seen.contains u do
        seen := seen.insert u
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- control (a): a root that is not in the environment is reported as missing, and the audit assertion fails
  let r0 ← fbReach `Tests.Gen4.FbFin0FixtureC.doesNotExist
  if r0.missing.isEmpty then throwError "FB11 AUDIT FAILED: the detector does not report an absent root as missing"
  let failed ← try
      (if r0.missing.size != 0 then throwError "FB11 missing constants: {r0.missing}" else pure false)
    catch _ => pure true
  unless failed do throwError "FB11 AUDIT FAILED: the missing-assertion did not fail on an absent root"
  logInfo m!"FB11 REACH CONTROL absent root: missing {r0.missing.size}, assertion failed as expected"
  -- control (b): raw proj and fixtures
  let rawProj := Lean.Expr.proj ``Tools.ShippingMemo.RefLawsM 0 (Lean.mkBVar 0)
  unless (fbConsts rawProj).any fbForbidden do
    throwError "FB11 AUDIT FAILED: the detector misses a raw Expr.proj of RefLawsM"
  logInfo m!"FB11 REACH CONTROL raw proj: flagged"
  for (c, bad) in [(``Tests.Gen4.FbFin0FixtureC.badDirect, true), (``Tests.Gen4.FbFin0FixtureC.badOuterMiss, true), (``Tests.Gen4.FbFin0FixtureC.badIndirect, true),
      (``Tests.Gen4.FbFin0FixtureC.goodUnrelated, false), (``Tests.Gen4.FbFin0FixtureC.goodFb3, false), (``Tools.ShippingGen4FbFin.a4_inv_tail_fin, false)] do
    let r ← fbReach c
    if bad && r.hit.isNone then throwError "FB11 AUDIT FAILED: the closure detector misses {c}"
    if !bad && r.hit.isSome then throwError "FB11 AUDIT FAILED: the closure detector flags {c}: {toString r.hit}"
    if !bad && !r.missing.isEmpty then throwError "FB11 AUDIT FAILED: control {c} has missing constants {r.missing}"
    logInfo m!"FB11 REACH CONTROL {c}: {toString r.hit} (missing {r.missing.size})"
  for c in fbNew do
    let r ← fbReach c
    if let some p := r.hit then
      throwError "FB11 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do
      throwError "FB11 AUDIT NOT ESTABLISHED {c}: {r.missing.size} reached constants not in the environment: {r.missing}"
    logInfo m!"FB11 REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, no-body {r.noBody}, opaque {r.opaques.size})"
  for c in fbNew do
    checkAxioms c
