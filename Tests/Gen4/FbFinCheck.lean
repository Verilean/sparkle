import Tools.ShippingGen4FbFin
import Tools.ShippingMemoInv
import Tests.Gen4.FbTailInvCheck
set_option autoImplicit false
-- BUILT (unit FB-7) at b103bd90 (header-sync 8c7e5ff6): kjob lake build Tests.Gen4.FbFinCheck exit 0 (764 jobs, Pod build); clean issue-linked build: fb7w-8c7e5ff6 exit 0, 1090 jobs, scoped approved at 8c7e5ff6: TYPE OK x2 (companion via logged isDefEq), MUTANT REJECTED x8, REACH missing 0 + stop_of_run reached, AXIOMS OK x4. Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §14.4/§14.5/§15 (rev8/rev9).
-- Checks: TYPE (independent Expected, `h1` at the §15.2 position), MUTANT (signature/defeq rejections, NOT semantic counterexamples),
-- projections as theorems, AXIOMS, value-closure audit with a `missing` list that FAILS when non-zero, and controls.

namespace Tests.Gen4.FbFinFixture
theorem helperA : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
end Tests.Gen4.FbFinFixture
namespace Tests.Gen4.FbFinFixtureB
theorem helperB : True := Tests.Gen4.FbFinFixture.helperA
end Tests.Gen4.FbFinFixtureB
namespace Tests.Gen4.FbFinFixtureC
theorem badDirect : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
theorem badIndirect : True := Tests.Gen4.FbFinFixtureB.helperB
theorem goodUnrelated : True := trivial
theorem goodFb3 : True := (fun _ => trivial) @Tools.ShippingGen4FbInv.a4_inv_machine_or_R4RunInv
/-- consumes `stop_of_run` -/
theorem usesStop : True := (fun _ => trivial) @Tools.ShippingGen5ClosingRun.stop_of_run
end Tests.Gen4.FbFinFixtureC

namespace Tests.Gen4.FbFinCheck
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
open Tools.ShippingGen2 Tools.ShippingGen4FbInv Tools.ShippingGen4FbTailInv Tools.ShippingGen4FbFin
open Tests.Gen3.ExpectedType

/-- independent copy of the `R4RunInvT` body (typed again from §15.1; `ExpR4RunInvT` of FbTailInvCheck is NOT reused). -/
def ExpR4RunInvT2 {{ι : Type}} {{dom : ι → Sparkle.Core.Domain.DomainConfig}}
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

def ExpTFinStop : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {D : Nat} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D) (hC : ChildKeepsInv L P Reach (D + 1)) (hI : InvAt L P Reach D w)
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, dsg) w'),
    InvAt L P Reach D w'

def ExpA4InvTailFin : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D)
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    (A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
       ExpR4RunInvT2 L P Reach mctx cctx D declName shape m d w w') ∧ InvAt L P Reach D w'

/-! mutants (signature level; NOT semantic counterexamples) -/
def MutFinNoH1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {D : Nat} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    (hC : ChildKeepsInv L P Reach (D + 1)) (hI : InvAt L P Reach D w)
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, dsg) w'),
    InvAt L P Reach D w'

def MutFinHCAtD : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {D : Nat} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D) (hC : ChildKeepsInv L P Reach D) (hI : InvAt L P Reach D w)
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, dsg) w'),
    InvAt L P Reach D w'

def MutFinConclSucc : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {D : Nat} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D) (hC : ChildKeepsInv L P Reach (D + 1)) (hI : InvAt L P Reach D w)
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, dsg) w'),
    InvAt L P Reach (D + 1) w'

def MutFinConclAtW : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {D : Nat} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D) (hC : ChildKeepsInv L P Reach (D + 1)) (hI : InvAt L P Reach D w)
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, dsg) w'),
    InvAt L P Reach D w

def MutFinH1AfterHI : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {D : Nat} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    (hC : ChildKeepsInv L P Reach (D + 1)) (hI : InvAt L P Reach D w) (h1 : 1 ≤ D)

    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, dsg) w'),
    InvAt L P Reach D w'

def MutCompNoInv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D)
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    (A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
       ExpR4RunInvT2 L P Reach mctx cctx D declName shape m d w w')

def MutCompNoH1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    (A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
       ExpR4RunInvT2 L P Reach mctx cctx D declName shape m d w w') ∧ InvAt L P Reach D w'

def MutCompH1AfterHI : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1)) (h1 : 1 ≤ D)

    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape),
    (A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
       ExpR4RunInvT2 L P Reach mctx cctx D declName shape m d w w') ∧ InvAt L P Reach D w'

/-- projection: the companion yields the K-RUNT statement (theorem, not defeq). -/
theorem fin_projects_to_krunt {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D) (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
      R4RunInvT L P Reach mctx cctx D declName shape m d w w' :=
  (a4_inv_tail_fin L P Reach hA h1 hI hC hr entry).1

/-- projection: the companion yields `tFin_stop`'s conclusion. -/
theorem fin_projects_to_tfin {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D) (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    InvAt L P Reach D w' :=
  (a4_inv_tail_fin L P Reach hA h1 hI hC hr entry).2

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``tFin_stop ``ExpTFinStop
  checkExpected ``a4_inv_tail_fin ``ExpA4InvTailFin
  checkMutant ``tFin_stop ``MutFinNoH1
  checkMutant ``tFin_stop ``MutFinHCAtD
  checkMutant ``tFin_stop ``MutFinConclSucc
  checkMutant ``tFin_stop ``MutFinConclAtW
  checkMutant ``tFin_stop ``MutFinH1AfterHI
  checkMutant ``a4_inv_tail_fin ``MutCompNoInv
  checkMutant ``a4_inv_tail_fin ``MutCompNoH1
  checkMutant ``a4_inv_tail_fin ``MutCompH1AfterHI

/-! ## Value-closure audit (§14.4): `missing` constants make the audit FAIL ("not established") -/
def fbNew : List Name :=
  [``tFin_stop, ``a4_inv_tail_fin, ``fin_projects_to_krunt, ``fin_projects_to_tfin]
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
  reachedStop : Bool := false
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
    if c == ``Tools.ShippingGen5ClosingRun.stop_of_run then out := { out with reachedStop := true }
    if out.visited > cap then
      throwError "FB7 AUDIT INCOMPLETE at {root}: more than {cap} constants; non-reference NOT established"
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
  let r0 ← fbReach `Tests.Gen4.FbFinFixtureC.doesNotExist
  if r0.missing.isEmpty then throwError "FB7 AUDIT FAILED: the detector does not report an absent root as missing"
  let failed ← try
      (if r0.missing.size != 0 then throwError "FB7 missing constants: {r0.missing}" else pure false)
    catch _ => pure true
  unless failed do throwError "FB7 AUDIT FAILED: the missing-assertion did not fail on an absent root"
  logInfo m!"FB7 REACH CONTROL absent root: missing {r0.missing.size}, assertion failed as expected"
  -- control (b): raw proj and fixtures
  let rawProj := Lean.Expr.proj ``Tools.ShippingMemo.RefLawsM 0 (Lean.mkBVar 0)
  unless (fbConsts rawProj).any fbForbidden do
    throwError "FB7 AUDIT FAILED: the detector misses a raw Expr.proj of RefLawsM"
  logInfo m!"FB7 REACH CONTROL raw proj: flagged"
  for (c, bad) in [(``Tests.Gen4.FbFinFixtureC.badDirect, true), (``Tests.Gen4.FbFinFixtureC.badIndirect, true),
      (``Tests.Gen4.FbFinFixtureC.goodUnrelated, false), (``Tests.Gen4.FbFinFixtureC.goodFb3, false)] do
    let r ← fbReach c
    if bad && r.hit.isNone then throwError "FB7 AUDIT FAILED: the closure detector misses {c}"
    if !bad && r.hit.isSome then throwError "FB7 AUDIT FAILED: the closure detector flags {c}: {toString r.hit}"
    if !bad && !r.missing.isEmpty then throwError "FB7 AUDIT FAILED: control {c} has missing constants {r.missing}"
    logInfo m!"FB7 REACH CONTROL {c}: {toString r.hit} (missing {r.missing.size})"
  -- control (c): stop_of_run detection
  let rs ← fbReach ``Tests.Gen4.FbFinFixtureC.usesStop
  unless rs.reachedStop do throwError "FB7 AUDIT FAILED: the detector does not see stop_of_run in a consumer"
  let rn ← fbReach ``Tools.ShippingGen4FbInv.a4_inv_machine_or_R4RunInv
  if rn.reachedStop then throwError "FB7 AUDIT FAILED: FB-3 extraction is reported as reaching stop_of_run"
  logInfo m!"FB7 REACH CONTROL stop_of_run: consumer sees it, FB-3 theorem does not"
  for c in fbNew do
    let r ← fbReach c
    if let some p := r.hit then
      throwError "FB7 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do
      throwError "FB7 AUDIT NOT ESTABLISHED {c}: {r.missing.size} reached constants not in the environment: {r.missing}"
    if c == ``tFin_stop && !r.reachedStop then
      throwError "FB7 AUDIT FAILED: tFin_stop does not reach stop_of_run (not consumed)"
    logInfo m!"FB7 REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, no-body {r.noBody}, opaque {r.opaques.size}, stop_of_run {r.reachedStop})"
  for c in fbNew do
    checkAxioms c
end Tests.Gen4.FbFinCheck
