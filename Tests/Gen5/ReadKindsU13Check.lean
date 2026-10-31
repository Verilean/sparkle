import Tools.ShippingGen5ReadKindsU13
import Tests.Gen5.ReadKindsCheck
import Tests.Gen5.ReadKindsU5Check
import Tests.Gen5.ReadKindsU7Check
set_option autoImplicit false
-- Built: kjob lake build Tests.Gen5.ReadKindsU13Check exit 0 (827 jobs), clean issue-linked build rk22v-25540b18 (dirty=false), approved at 25540b18 (U13 only; conditional intermediate, M5/FG not complete). Check log counts: TYPE 3 comparisons (1 theorem + positive control + U12b-type negative control), propositional mutants 6. Freeze: scripts/gen5/DG_READKINDS_U13_FREEZE.md (approved e6d56e4a). No sorry / axiom / native_decide.

/-! # DG-READKINDS U13 checks (Tools/ShippingGen5ReadKindsU13.lean)

1. TYPE: U13 against the independently written `ExpU13` (freeze §3; reducible comparator `Tests.Gen3.ExpectedType`);
   positive control (copy); negative control: U12b's own type is NOT accepted as `ExpU13`. Count: 1 theorem + 2 controls.
2. MUTANT: signature/defeq rejections of well-typed single-change statements, NOT semantic counterexamples.
3. COUNT: conjunct counts (auxiliary, necessary condition only).
4. CLOSURE: `reach2` (root tested against the forbid set; unknown constant = throw); negatives inside `withoutModifyingEnv`.
   Required suppliers reached: U12b and `readsAt_self`. `ReadKeeps`/`EnvFrame` recorded as FACTs (premise use), not forbidden.
5. AXIOMS: propext / Classical.choice / Quot.sound only. -/

namespace Tests.Gen5.ReadKindsU13Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU13
open Tests.Gen3.ExpectedType
open Tests.Gen5.ReadKindsCheck (reach forbidConsts AReach body? badProj)
open Tests.Gen5.ReadKindsU7Check (conjCount)

/-! ## 1. Expected statements and mutants (freeze §3) -/

/-- freeze §3 U13 -/
def ExpU13 : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- positive control: separately written copy of the U13 statement -/
def CopyOfU13 : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U13: drop the r.shape = shape conjunct -/
def MutNoShape : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)

/-- U13: drop hX -/
def MutNoHX : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U13: drop h0s -/
def MutNoH0s : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U13: h0s at w instead of ws -/
def MutH0sAtW : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref w)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U13: h0s environment envAt cref ws instead of envAt cref w -/
def MutEnvAtWs : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref ws) cref ws)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U13: drop hHead -/
def MutNoHHead : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``readMachine_agrees_runReads_of_head_self ``ExpU13
  checkExpected ``CopyOfU13 ``ExpU13
  checkMutant ``Tools.ShippingGen5ReadKindsU12.readMachine_agrees_runReads_of_head ``ExpU13
  logInfo "RK-U13 TYPE OK: 3 comparisons (1 theorem + 1 comparator positive control + 1 negative control: U12b's type is not accepted as ExpU13)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``readMachine_agrees_runReads_of_head_self ``MutNoShape
  checkMutant ``readMachine_agrees_runReads_of_head_self ``MutNoHX
  checkMutant ``readMachine_agrees_runReads_of_head_self ``MutNoH0s
  checkMutant ``readMachine_agrees_runReads_of_head_self ``MutH0sAtW
  checkMutant ``readMachine_agrees_runReads_of_head_self ``MutEnvAtWs
  checkMutant ``readMachine_agrees_runReads_of_head_self ``MutNoHHead
  logInfo "RK-U13 MUTANT REJECTED 6 (NoShape (conjunct drop), NoHX, NoH0s, H0sAtW, EnvAtWs, NoHHead; each a single well-typed change; signature/defeq rejection, not semantic counterexamples)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let cnt (n : Name) : Lean.Elab.TermElabM Nat := do
    let some ci := env.find? n | throwError "RK-U13 COUNT: {n} missing"
    let some v := ci.value? | throwError "RK-U13 COUNT: {n} has no value"
    return conjCount env [] v
  let e ← cnt ``ExpU13
  let ns ← cnt ``MutNoShape
  let others ← [``MutNoHX, ``MutNoH0s, ``MutH0sAtW, ``MutEnvAtWs, ``MutNoHHead].mapM cnt
  if ns + 1 != e || others.any (· != e) then
    throwError "RK-U13 COUNT FAILED: Exp {e}, NoShape {ns}, others {others}"
  logInfo m!"RK-U13 COUNT OK (rule: And/Exists/∀-body leaves; premises not counted): Exp {e}, NoShape {ns} = -1, others equal"

/-! ## 2. Closure -/

def reach2 (root : Name) (forbid : List Name) (cap : Nat := 3000000) : MetaM AReach := do
  let env ← getEnv
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  if forbid.contains root then return { out with hit := some [root] }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "RK-U13 AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | throwError "RK-U13 CLOSURE unknown constant {c} reached via {path}"
    let body := body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1, noBodyNames := out.noBodyNames.push c }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques + 1, opaqueNames := out.opaqueNames.push c }
    if badProj ci.type || (body.map badProj).getD false then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if forbid.contains u then return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

def forbidU13 : List Name := forbidConsts.filter fun n => n != ``Lean.Expr.equal && n != ``Lean.Expr.eqv

/-- add a declaration whose type/value may name constants that do not exist (kernel check skipped; the env is restored by the caller) -/
def addFx (n : Name) (ty val : Expr) : MetaM Unit :=
  withOptions (fun o => o.setBool `debug.skipKernelTC true) <|
    addDecl (.defnDecl { name := n, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe })

def failsWith (what : String) (act : MetaM Unit) (needles : List Name) : MetaM Unit := do
  let r ← try act; pure none catch e => pure (some (← e.toMessageData.toString))
  match r with
  | none => throwError "RK-U13 CLOSURE NEGATIVE ACCEPTED: {what}"
  | some msg =>
    for n in needles do
      unless (msg.splitOn n.toString).length > 1 do
        throwError "RK-U13 CLOSURE NEGATIVE {what}: message does not name {n}: {msg}"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``readMachine_agrees_runReads_of_head_self
  let req := [``Tools.ShippingGen5ReadKindsU12.readMachine_agrees_runReads_of_head, ``Tools.ShippingGen5Env.readsAt_self]
  for _ in [0] do
    let r ← reach2 c forbidU13
    if let some p := r.hit then throwError "RK-U13 AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RK-U13 AUDIT FAILED {c}: {t} not reached"
    logInfo m!"RK-U13 REACH {c}: no T1Hyp / T1HypND (name, raw proj, rec) / Laws; reaches {req} (visited {r.visited}, unknown 0 (throws otherwise), opaque {r.opaqueNames}, no-value count {r.noBodyNames.size})"
    let rf ← reach2 c forbidConsts
    logInfo m!"RK-U13 FACT full forbid set (incl. Expr.equal/eqv) on {c}: {toString rf.hit}"
    logInfo m!"RK-U13 FACT premise use on {c}: ReadKeeps reached {r.seen.contains ``Tools.ShippingStRefCorrespondence.ReadKeeps}; GetEnvFrame reached {r.seen.contains ``Tools.ShippingEnvSnapshot.GetEnvFrame}; EnvFrame reached {r.seen.contains ``Tools.ShippingEnvSnapshot.EnvFrame} (premises, not supplied laws)"
  let r ← reach2 ``Lean.Expr.equal forbidConsts
  unless r.hit == some [``Lean.Expr.equal] do throwError "RK-U13 AUDIT FAILED: a forbidden root is not flagged"
  let r ← reach2 ``Tools.ShippingGen2.Laws forbidConsts
  unless r.hit == some [``Tools.ShippingGen2.Laws] do throwError "RK-U13 AUDIT FAILED: Laws as root is not flagged"
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.viaHelper2 forbidConsts
  if r.hit.isNone then throwError "RK-U13 AUDIT FAILED: scanner control misses the fixture"
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.cleanHelper forbidConsts
  if r.hit.isSome then throwError "RK-U13 AUDIT FAILED: scanner control flags the clean helper"
  let nm := fun (s : String) => (`Tests.Gen5.U13Fx).str s
  failsWith "unknown root" (do let _ ← reach2 (nm "noSuchRoot") forbidU13; pure ()) [nm "noSuchRoot"]
  withoutModifyingEnv do
    addFx (nm "vBad") (mkConst ``True) (mkConst (nm "unkV"))
    addFx (nm "vTop") (mkConst ``True) (mkConst (nm "vBad"))
    failsWith "helper value" (do let _ ← reach2 (nm "vTop") forbidU13; pure ()) [nm "unkV", nm "vBad"]
    addFx (nm "tBad") (mkConst (nm "unkT")) (mkConst ``True.intro)
    addFx (nm "tTop") (mkConst ``True) (mkConst (nm "tBad"))
    failsWith "helper type" (do let _ ← reach2 (nm "tTop") forbidU13; pure ()) [nm "unkT", nm "tBad"]
    addFx (nm "cHelp") (mkConst ``True) (mkConst ``True.intro)
    addFx (nm "cTop") (mkConst ``True) (mkConst (nm "cHelp"))
    let r ← reach2 (nm "cTop") forbidU13
    unless r.hit.isNone && r.seen.contains (nm "cHelp") do throwError "RK-U13 CLOSURE CONTROL FAILED: clean fixture"
    let r ← reach2 (nm "cTop") [nm "cTop"]
    unless r.hit == some [nm "cTop"] do throwError "RK-U13 CLOSURE: forbidden root fixture not flagged"
  if (← getEnv).contains (nm "vBad") then throwError "RK-U13 CLOSURE: fixture leaked out of withoutModifyingEnv"
  logInfo "RK-U13 CLOSURE NEGATIVES OK: unknown root, helper value, helper type; clean control; forbidden root; fixtures restored"

/-! ## 3. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``readMachine_agrees_runReads_of_head_self

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo "RK-U13 STATUS: U13 is a CONDITIONAL intermediate (U12b with h0 and the free env₀ removed: env₀ := envAt cref w, h0 := readsAt_self cref w; h0s remains as ReadsAt (envAt cref w) cref ws; a reduction by one premise, not a supply of the rest). hk, hHead, h0s, the two runs and hX remain premises. NOT supplied: ReadKeeps / EnvFrame (coreHead X) of the runtime, h0s (env tie / C0), hall, ReadWorld, existence of runs, envR = envR', ci in envR, hag, hK, hq, coverage, FG."

end Tests.Gen5.ReadKindsU13Check
