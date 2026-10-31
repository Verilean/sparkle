import Tools.ShippingGen4FbPP
import Tools.ShippingGen4FbMachInv
import Tools.ShippingMemoInv
import Tools.ShippingLegacySemMemoWalk
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- BUILT (unit FB-14): kjob lake build Tests.Gen4.FbPPCheck exit 0 (812 jobs); clean issue-linked build fb14v-67756b3c exit 0 (approved at 67756b3c, scope-limited); the FB-15 type-only-helper fixture (`fxRootViaTypeHelper`) was added later and is covered by clean build fb16v-43b31a15 exit 0 (814 jobs, approved at 43b31a15). Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §23.3/§23.5 (rev13, committed 3d58fd03).
-- Expected definitions are typed again here (`ExpPPRel`, `ExpSeqPortFacts`, `ExpCombPortFacts`); theorem Expecteds use the
-- definitions under test only after their VALUES were compared with the independent copies.
-- Checks: TYPE (3 definition values, 5 theorems), MUTANT (well-typed single changes; signature/defeq rejections, NOT semantic
-- counterexamples), value-closure audit (root judged itself; `missing` fails the audit), controls (invalid fixtures are added
-- inside `withoutModifyingEnv`), AXIOMS.

namespace Tests.Gen4.FbPPFixture
theorem helperA : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
end Tests.Gen4.FbPPFixture
namespace Tests.Gen4.FbPPFixtureB
theorem helperB : True := Tests.Gen4.FbPPFixture.helperA
end Tests.Gen4.FbPPFixtureB
namespace Tests.Gen4.FbPPFixtureC
theorem badDirect : True := (fun _ => trivial) @Tools.ShippingMemo.memoInv_hit
theorem badOuterMiss : True := (fun _ => trivial) @Tools.ShippingLegacySem.outer_miss
theorem badIndirect : True := Tests.Gen4.FbPPFixtureB.helperB
theorem goodUnrelated : True := trivial
theorem goodFb13 : True := (fun _ => trivial) @Tools.ShippingGen4FbMachInv.a4_inv_tail_fin0_both
end Tests.Gen4.FbPPFixtureC

namespace Tests.Gen4.FbPPCheck
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingGen2 Tools.ShippingGen4FbPP
open Tests.Gen3.ExpectedType

def ExpPPRel (raw : Sparkle.IR.AST.Module) (dsg : Sparkle.IR.AST.Design)
    (out : Sparkle.IR.AST.Module) (dout : Sparkle.IR.AST.Design) : Prop :=
  let top : (Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) → Sparkle.IR.AST.Design →
      Sparkle.IR.AST.Design := fun f d =>
    { d with modules := d.modules.map fun x => if x.name == raw.name then f x else x }
  let m' := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
  let d₁ := top Sparkle.IR.ZeroWidth.dropZeroWidthModule dsg
  (out = m' ∧ dout = d₁) ∨
  (out = Sparkle.IR.RefineCheck.mergeChecked m' ∧ dout = top Sparkle.IR.RefineCheck.mergeChecked d₁)

def MutPP1 (raw : Sparkle.IR.AST.Module) (dsg : Sparkle.IR.AST.Design)
    (out : Sparkle.IR.AST.Module) (dout : Sparkle.IR.AST.Design) : Prop :=
  let top : (Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) → Sparkle.IR.AST.Design →
      Sparkle.IR.AST.Design := fun f d =>
    { d with modules := d.modules.map fun x => if x.name != raw.name then f x else x }
  let m' := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
  let d₁ := top Sparkle.IR.ZeroWidth.dropZeroWidthModule dsg
  (out = m' ∧ dout = d₁) ∨
  (out = Sparkle.IR.RefineCheck.mergeChecked m' ∧ dout = top Sparkle.IR.RefineCheck.mergeChecked d₁)

def MutPP2 (raw : Sparkle.IR.AST.Module) (dsg : Sparkle.IR.AST.Design)
    (out : Sparkle.IR.AST.Module) (dout : Sparkle.IR.AST.Design) : Prop :=
  let top : (Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) → Sparkle.IR.AST.Design →
      Sparkle.IR.AST.Design := fun f d =>
    { d with modules := d.modules.map fun x => if x.name == raw.name then f x else x }
  let m' := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
  let d₁ := top Sparkle.IR.ZeroWidth.dropZeroWidthModule dsg
  (out = m' ∧ dout = d₁) ∨
  (out = Sparkle.IR.RefineCheck.mergeChecked m' ∧ dout = d₁)

def MutPP3 (raw : Sparkle.IR.AST.Module) (dsg : Sparkle.IR.AST.Design)
    (out : Sparkle.IR.AST.Module) (dout : Sparkle.IR.AST.Design) : Prop :=
  let top : (Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) → Sparkle.IR.AST.Design →
      Sparkle.IR.AST.Design := fun f d =>
    { d with modules := d.modules.map fun x => if x.name == raw.name then f x else x }
  let m' := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
  let d₁ := top Sparkle.IR.ZeroWidth.dropZeroWidthModule dsg
  (out = m' ∧ dout = d₁) ∨
  (out = m' ∧ dout = top Sparkle.IR.RefineCheck.mergeChecked d₁)

def ExpSeqPortFacts (mc : Sparkle.IR.AST.Module)
    (bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)) (outsC : List OutField) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧ "clk" ∈ mc.inputs.map (·.name) ∧
  "rst" ∈ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (Tools.ShippingMachineCompose.argPorts mc).length =
    (bsC.filter fun b => b.2 != .domain).length

def MutSeqNoRst (mc : Sparkle.IR.AST.Module)
    (bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)) (outsC : List OutField) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧ "clk" ∈ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (Tools.ShippingMachineCompose.argPorts mc).length =
    (bsC.filter fun b => b.2 != .domain).length

def ExpCombPortFacts (mc : Sparkle.IR.AST.Module)
    (bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)) (outsC : List OutField) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧
  "clk" ∉ mc.inputs.map (·.name) ∧ "rst" ∉ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (Tools.ShippingMachineCompose.argPorts mc).length =
    (bsC.filter fun b => b.2 != .domain).length

def MutCombClkIn (mc : Sparkle.IR.AST.Module)
    (bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)) (outsC : List OutField) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧
  "clk" ∈ mc.inputs.map (·.name) ∧ "rst" ∉ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (Tools.ShippingMachineCompose.argPorts mc).length =
    (bsC.filter fun b => b.2 != .domain).length

def ExpPorts : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    (h : PPRel raw dsg out dout),
    out.name = raw.name ∧ out.inputs = raw.inputs ∧ out.outputs = raw.outputs

def MutPortsNoOut : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    (h : PPRel raw dsg out dout),
    out.name = raw.name ∧ out.inputs = raw.inputs

def MutPortsSwap : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    (h : PPRel raw dsg out dout),
    out.name = raw.name ∧ out.inputs = raw.inputs ∧ out.outputs = raw.inputs

def ExpNames : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    (h : PPRel raw dsg out dout),
    dout.topModule = dsg.topModule ∧ dout.modules.map (·.name) = dsg.modules.map (·.name)

def MutNamesNoTop : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    (h : PPRel raw dsg out dout),
    dout.modules.map (·.name) = dsg.modules.map (·.name)

def ExpSeqT : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    (h : PPRel raw dsg out dout) (hs : SeqPortFacts raw bsC outsC), SeqPortFacts out bsC outsC

def MutSeqToComb : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    (h : PPRel raw dsg out dout) (hs : SeqPortFacts raw bsC outsC), CombPortFacts out bsC outsC

def ExpCombT : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    (h : PPRel raw dsg out dout) (hs : CombPortFacts raw bsC outsC), CombPortFacts out bsC outsC

def MutCombSeqHyp : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    (h : PPRel raw dsg out dout) (hs : SeqPortFacts raw bsC outsC), CombPortFacts out bsC outsC

def ExpRun : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Sparkle.IR.AST.Design} {n : Nat}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : PPRel raw dsg out dout) (hr : ChildRunN children dsn n raw bsC outsC S),
    SeqPortFacts out bsC outsC ∨ CombPortFacts out bsC outsC

def MutRunSeqOnly : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design}
    {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Sparkle.IR.AST.Design} {n : Nat}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : PPRel raw dsg out dout) (hr : ChildRunN children dsn n raw bsC outsC S),
    SeqPortFacts out bsC outsC

def MutRunNoPP : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {out : Sparkle.IR.AST.Module}
    {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Sparkle.IR.AST.Design} {n : Nat}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hr : ChildRunN children dsn n raw bsC outsC S),
    SeqPortFacts out bsC outsC ∨ CombPortFacts out bsC outsC

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``PPRel ``ExpPPRel
  checkExpected ``SeqPortFacts ``ExpSeqPortFacts
  checkExpected ``CombPortFacts ``ExpCombPortFacts
  checkExpected ``ppRel_ports ``ExpPorts
  checkExpected ``ppRel_design_names ``ExpNames
  checkExpected ``ppRel_seqPortFacts ``ExpSeqT
  checkExpected ``ppRel_combPortFacts ``ExpCombT
  checkExpected ``ppRel_childRunN_portFacts ``ExpRun
  -- definition-value mutants
  checkMutant ``PPRel ``MutPP1
  checkMutant ``PPRel ``MutPP2
  checkMutant ``PPRel ``MutPP3
  checkMutant ``SeqPortFacts ``MutSeqNoRst
  checkMutant ``CombPortFacts ``MutCombClkIn
  -- theorem mutants
  checkMutant ``ppRel_ports ``MutPortsNoOut
  checkMutant ``ppRel_ports ``MutPortsSwap
  checkMutant ``ppRel_design_names ``MutNamesNoTop
  checkMutant ``ppRel_seqPortFacts ``MutSeqToComb
  checkMutant ``ppRel_combPortFacts ``MutCombSeqHyp
  checkMutant ``ppRel_childRunN_portFacts ``MutRunSeqOnly
  checkMutant ``ppRel_childRunN_portFacts ``MutRunNoPP

/-! ## Value-closure audit (common checker form): the root is judged itself; `missing` makes the audit FAIL -/
def fbNew : List Name :=
  [``PPRel, ``SeqPortFacts, ``CombPortFacts, ``ppRel_ports, ``ppRel_design_names, ``ppRel_seqPortFacts,
   ``ppRel_combPortFacts, ``ppRel_childRunN_portFacts, ``dropZW_outputs]
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
  -- the root is judged itself (a forbidden root is a hit with the one-element path)
  if fbForbidden root then return { hit := some [root] }
  let mut out : FbReach := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then
      throwError "FB14 AUDIT INCOMPLETE at {root}: more than {cap} constants; non-reference NOT established"
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

/-- An unchecked fixture declaration, added only inside `withoutModifyingEnv`. -/
def addFixture (n : Name) (type value : Lean.Expr) : MetaM Unit := do
  let decl := Declaration.defnDecl
    { name := n, levelParams := [], type, value, hints := .opaque, safety := .safe }
  withOptions (fun o => debug.skipKernelTC.set o true) (addDecl decl)

/-- the audit verdict on one root: `ok` only if no forbidden constant is reached and `missing` is empty. -/
def auditOk (root : Name) : MetaM Bool := do
  let r ← fbReach root
  return r.hit.isNone && r.missing.isEmpty

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let absent : Name := `Tests.Gen4.FbPPFixtureC.doesNotExist
  -- control (a): an absent root is reported as missing and the audit does not pass
  let r0 ← fbReach absent
  if r0.missing.isEmpty then throwError "FB14 AUDIT FAILED: the walker does not report an absent root as missing"
  if (← auditOk absent) then throwError "FB14 AUDIT FAILED: an absent root passed the audit"
  logInfo m!"FB14 CONTROL absent root: missing {r0.missing.size}, audit not passed"
  -- control (b): the root itself is forbidden
  let rf ← fbReach ``Tools.ShippingMemo.memoInv_hit
  unless rf.hit == some [``Tools.ShippingMemo.memoInv_hit] do
    throwError "FB14 AUDIT FAILED: a forbidden root is not judged itself: {toString rf.hit}"
  logInfo m!"FB14 CONTROL forbidden root: flagged by the root rule"
  -- control (c): unknown names in invalid fixtures (declarations added without kernel checking; environment restored)
  let ty0 : Lean.Expr := mkConst ``True
  let ghost : Lean.Expr := mkConst `Tests.Gen4.FbPPFixtureC.ghostName
  let v ← withoutModifyingEnv do
    addFixture `Tests.Gen4.FbPPFixtureC.fxValueUnknown ty0 ghost
    addFixture `Tests.Gen4.FbPPFixtureC.fxTypeUnknown ghost (mkConst ``True.intro)
    -- `fxViaHelper` reaches an unknown name only through another (added) helper's VALUE;
    -- `fxTypeHelper` / `fxRootViaTypeHelper` (FB-15 supplement): the helper's TYPE alone is the unknown name and the
    -- root mentions the ghost nowhere (not in its type, value or λ-binder type), only the helper constant:
    addFixture `Tests.Gen4.FbPPFixtureC.fxTypeHelper ghost (mkConst ``True.intro)
    addFixture `Tests.Gen4.FbPPFixtureC.fxRootViaTypeHelper ty0
      (Lean.mkApp (Lean.mkLambda `_x .default ty0 (mkConst ``True.intro))
        (mkConst `Tests.Gen4.FbPPFixtureC.fxTypeHelper))
    addFixture `Tests.Gen4.FbPPFixtureC.fxViaHelper ty0 (mkConst `Tests.Gen4.FbPPFixtureC.fxValueUnknown)
    addFixture `Tests.Gen4.FbPPFixtureC.fxClean ty0 (mkConst ``True.intro)
    let a ← fbReach `Tests.Gen4.FbPPFixtureC.fxValueUnknown
    let b ← fbReach `Tests.Gen4.FbPPFixtureC.fxTypeUnknown
    let c ← fbReach `Tests.Gen4.FbPPFixtureC.fxViaHelper
    let d ← fbReach `Tests.Gen4.FbPPFixtureC.fxClean
    let oka ← auditOk `Tests.Gen4.FbPPFixtureC.fxValueUnknown
    let okb ← auditOk `Tests.Gen4.FbPPFixtureC.fxTypeUnknown
    let okc ← auditOk `Tests.Gen4.FbPPFixtureC.fxViaHelper
    let okd ← auditOk `Tests.Gen4.FbPPFixtureC.fxClean
    let e ← fbReach `Tests.Gen4.FbPPFixtureC.fxRootViaTypeHelper
    let oke ← auditOk `Tests.Gen4.FbPPFixtureC.fxRootViaTypeHelper
    let ghostSeen := e.missing.contains `Tests.Gen4.FbPPFixtureC.ghostName
    pure (a.missing.size, b.missing.size, c.missing.size, d.missing.size, oka, okb, okc, okd, e.missing.size, oke, ghostSeen)
  let (ma, mb, mc, md, oka, okb, okc, okd, me, oke, ghostSeen) := v
  unless ma ≥ 1 && !oka do throwError "FB14 AUDIT FAILED: unknown name in a helper VALUE not reported (missing {ma}, ok {oka})"
  unless mb ≥ 1 && !okb do throwError "FB14 AUDIT FAILED: unknown name in a helper TYPE not reported (missing {mb}, ok {okb})"
  unless mc ≥ 1 && !okc do throwError "FB14 AUDIT FAILED: unknown name through a helper not reported (missing {mc}, ok {okc})"
  unless md == 0 && okd do throwError "FB14 AUDIT FAILED: the clean fixture is not clean (missing {md}, ok {okd})"
  unless ghostSeen && !oke do
    throwError "FB15 AUDIT FAILED: root -> type-only helper: ghostName not in missing (missing {me}, ghostSeen {ghostSeen}, ok {oke})"
  logInfo m!"FB15 CONTROL root -> helper with TYPE-only unknown: ghostName in missing (missing {me}), audit not passed"
  logInfo m!"FB14 CONTROL unknown-name fixtures: helper value missing {ma}, helper type missing {mb}, via helper missing {mc}; clean fixture missing {md} (not flagged)"
  if (← getEnv).contains `Tests.Gen4.FbPPFixtureC.fxClean then
    throwError "FB14 AUDIT FAILED: withoutModifyingEnv did not restore the environment"
  -- control (d): raw Expr.proj and real fixtures
  let rawProj := Lean.Expr.proj ``Tools.ShippingMemo.RefLawsM 0 (Lean.mkBVar 0)
  unless (fbConsts rawProj).any fbForbidden do
    throwError "FB14 AUDIT FAILED: the walker misses a raw Expr.proj of RefLawsM"
  logInfo m!"FB14 CONTROL raw proj: flagged"
  for (c, bad) in [(``Tests.Gen4.FbPPFixtureC.badDirect, true), (``Tests.Gen4.FbPPFixtureC.badOuterMiss, true),
      (``Tests.Gen4.FbPPFixtureC.badIndirect, true), (``Tests.Gen4.FbPPFixtureC.goodUnrelated, false),
      (``Tests.Gen4.FbPPFixtureC.goodFb13, false), (``Tools.ShippingGen4FbMachInv.a4_inv_tail_fin0_both, false)] do
    let r ← fbReach c
    if bad && r.hit.isNone then throwError "FB14 AUDIT FAILED: the walker misses {c}"
    if !bad && r.hit.isSome then throwError "FB14 AUDIT FAILED: the walker flags {c}: {toString r.hit}"
    if !bad && !r.missing.isEmpty then throwError "FB14 AUDIT FAILED: control {c} has missing constants {r.missing}"
    logInfo m!"FB14 CONTROL {c}: {toString r.hit} (missing {r.missing.size})"
  -- the intended names exist and are audited
  for c in fbNew do
    unless (← getEnv).contains c do throwError "FB14 AUDIT FAILED: intended name {c} is not in the environment"
    let r ← fbReach c
    if let some p := r.hit then
      throwError "FB14 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do
      throwError "FB14 AUDIT NOT ESTABLISHED {c}: {r.missing.size} reached constants not in the environment: {r.missing}"
    logInfo m!"FB14 REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, no-body {r.noBody}, opaque {r.opaques.size})"
  for c in fbNew do
    checkAxioms c

end Tests.Gen4.FbPPCheck
