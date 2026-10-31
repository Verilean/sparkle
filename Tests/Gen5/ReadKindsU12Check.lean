import Tools.ShippingGen5ReadKindsU12
import Tests.Gen5.ReadKindsCheck
import Tests.Gen5.ReadKindsU5Check
import Tests.Gen5.ReadKindsU7Check
set_option autoImplicit false
-- NOT BUILT: no pod build of this tree yet. Freeze: scripts/gen5/DG_READKINDS_U12_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U12 checks (Tools/ShippingGen5ReadKindsU12.lean)

1. TYPE: U12a/U12b against independently written `ExpU12a`/`ExpU12b` (from freeze §2; reducible comparator `Tests.Gen3.ExpectedType`); positive control (copy of U12b). Count: 2 theorems + 1 control.
2. MUTANT: signature/defeq rejections of well-typed single-change statements (U12b x5, U12a x1), NOT semantic counterexamples.
3. COUNT: conjunct counts (auxiliary, necessary condition only).
4. CLOSURE: `reach2` (root tested against the forbid set; unknown constant = throw); negatives inside `withoutModifyingEnv`.
   `ReadKeeps`/`GetEnvFrame`/`EnvFrame` are recorded as FACTs (premise use), not forbidden.
5. AXIOMS: propext / Classical.choice / Quot.sound only. -/

namespace Tests.Gen5.ReadKindsU12Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU12
open Tests.Gen3.ExpectedType
open Tests.Gen5.ReadKindsCheck (reach forbidConsts AReach body? badProj)
open Tests.Gen5.ReadKindsU7Check (conjCount)

/-! ## 1. Expected statements and mutants (freeze §2) -/

/-- freeze §2 U12a -/
def ExpU12a : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name}
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {env₀ : Lean.Environment} {ws w1 w2 w3 w5 : Void IO.RealWorld}
    {s : Tools.ShippingEntryReadsLinked.CoreSaved} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws)
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref ws s w1)
    (hget : RunsTo (Lean.getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5),
    Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
      Tools.ShippingGen5Env.ReadsAt env₀ cref w3

/-- freeze §2 U12b -/
def ExpU12b : Prop :=
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
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- positive control: separately written copy of the U12b statement -/
def CopyOfU12b : Prop :=
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
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U12b: drop the r.shape = shape conjunct -/
def MutNoShapeB : Prop :=
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
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)

/-- U12b: drop hX -/
def MutNoHXB : Prop :=
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
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U12b: drop h0 -/
def MutNoH0B : Prop :=
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
    {env₀ : Lean.Environment}
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U12b: drop h0s -/
def MutNoH0sB : Prop :=
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
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U12b: h0s at w instead of ws -/
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
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U12a: drop h0s -/
def MutNoH0sA : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name}
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {env₀ : Lean.Environment} {ws w1 w2 w3 w5 : Void IO.RealWorld}
    {s : Tools.ShippingEntryReadsLinked.CoreSaved} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref ws s w1)
    (hget : RunsTo (Lean.getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5),
    Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
      Tools.ShippingGen5Env.ReadsAt env₀ cref w3

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``readsAt_chain_of_head ``ExpU12a
  checkExpected ``readMachine_agrees_runReads_of_head ``ExpU12b
  checkExpected ``CopyOfU12b ``ExpU12b
  logInfo "RK-U12 TYPE OK: 3 comparisons (2 theorems + 1 comparator positive control)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``readMachine_agrees_runReads_of_head ``MutNoShapeB
  checkMutant ``readMachine_agrees_runReads_of_head ``MutNoHXB
  checkMutant ``readMachine_agrees_runReads_of_head ``MutNoH0B
  checkMutant ``readMachine_agrees_runReads_of_head ``MutNoH0sB
  checkMutant ``readMachine_agrees_runReads_of_head ``MutH0sAtW
  checkMutant ``readsAt_chain_of_head ``MutNoH0sA
  logInfo "RK-U12 MUTANT REJECTED 6 (U12b: NoShape (conjunct drop), NoHX, NoH0, NoH0s, H0sAtW; U12a: NoH0s; each a single change; signature/defeq rejection, not semantic counterexamples; 5 against a single theorem U12b + 1 against U12a)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let cnt (n : Name) : Lean.Elab.TermElabM Nat := do
    let some ci := env.find? n | throwError "RK-U12 COUNT: {n} missing"
    let some v := ci.value? | throwError "RK-U12 COUNT: {n} has no value"
    return conjCount env [] v
  let e ← cnt ``ExpU12b
  let ns ← cnt ``MutNoShapeB
  let nx ← cnt ``MutNoHXB
  let n0 ← cnt ``MutNoH0B
  let ns' ← cnt ``MutNoH0sB
  let nw ← cnt ``MutH0sAtW
  let ea ← cnt ``ExpU12a
  let na ← cnt ``MutNoH0sA
  if ns + 1 != e || nx != e || n0 != e || ns' != e || nw != e || na != ea then
    throwError "RK-U12 COUNT FAILED: ExpB {e}, NoShape {ns}, NoHX {nx}, NoH0 {n0}, NoH0s {ns'}, H0sAtW {nw}, ExpA {ea}, NoH0sA {na}"
  logInfo m!"RK-U12 COUNT OK (rule: And/Exists/∀-body leaves; premises not counted): U12b {e}, NoShape {ns} = -1, others equal; U12a {ea}, NoH0sA {na} equal"

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
    if out.visited > cap then throwError "RK-U12 AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | throwError "RK-U12 CLOSURE unknown constant {c} reached via {path}"
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

def forbidU12 : List Name := forbidConsts.filter fun n => n != ``Lean.Expr.equal && n != ``Lean.Expr.eqv

/-- add a declaration whose type/value may name constants that do not exist (kernel check skipped; the env is restored by the caller) -/
def addFx (n : Name) (ty val : Expr) : MetaM Unit :=
  withOptions (fun o => o.setBool `debug.skipKernelTC true) <|
    addDecl (.defnDecl { name := n, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe })

def failsWith (what : String) (act : MetaM Unit) (needles : List Name) : MetaM Unit := do
  let r ← try act; pure none catch e => pure (some (← e.toMessageData.toString))
  match r with
  | none => throwError "RK-U12 CLOSURE NEGATIVE ACCEPTED: {what}"
  | some msg =>
    for n in needles do
      unless (msg.splitOn n.toString).length > 1 do
        throwError "RK-U12 CLOSURE NEGATIVE {what}: message does not name {n}: {msg}"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let cb := ``readMachine_agrees_runReads_of_head
  let ca := ``readsAt_chain_of_head
  let rb := [ca, ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps]
  let ra := [``Tools.ShippingGen5Env.ReadsAt.of_frame, ``Tools.ShippingEnvSnapshot.envFrame_getConstInfo]
  for (c, req) in [(cb, rb), (ca, ra)] do
    let r ← reach2 c forbidU12
    if let some p := r.hit then throwError "RK-U12 AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RK-U12 AUDIT FAILED {c}: {t} not reached"
    logInfo m!"RK-U12 REACH {c}: no T1Hyp / T1HypND (name, raw proj, rec) / Laws; reaches {req} (visited {r.visited}, unknown 0 (throws otherwise), opaque {r.opaqueNames}, no-value count {r.noBodyNames.size})"
    let rf ← reach2 c forbidConsts
    logInfo m!"RK-U12 FACT full forbid set (incl. Expr.equal/eqv) on {c}: {toString rf.hit}"
    logInfo m!"RK-U12 FACT premise use on {c}: ReadKeeps reached {r.seen.contains ``Tools.ShippingStRefCorrespondence.ReadKeeps}; GetEnvFrame reached {r.seen.contains ``Tools.ShippingEnvSnapshot.GetEnvFrame}; EnvFrame reached {r.seen.contains ``Tools.ShippingEnvSnapshot.EnvFrame} (premises, not supplied laws)"
  let r ← reach2 ``Lean.Expr.equal forbidConsts
  unless r.hit == some [``Lean.Expr.equal] do throwError "RK-U12 AUDIT FAILED: a forbidden root is not flagged"
  let r ← reach2 ``Tools.ShippingGen2.Laws forbidConsts
  unless r.hit == some [``Tools.ShippingGen2.Laws] do throwError "RK-U12 AUDIT FAILED: Laws as root is not flagged"
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.viaHelper2 forbidConsts
  if r.hit.isNone then throwError "RK-U12 AUDIT FAILED: scanner control misses the fixture"
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.cleanHelper forbidConsts
  if r.hit.isSome then throwError "RK-U12 AUDIT FAILED: scanner control flags the clean helper"
  let nm := fun (s : String) => (`Tests.Gen5.U12Fx).str s
  failsWith "unknown root" (do let _ ← reach2 (nm "noSuchRoot") forbidU12; pure ()) [nm "noSuchRoot"]
  withoutModifyingEnv do
    addFx (nm "vBad") (mkConst ``True) (mkConst (nm "unkV"))
    addFx (nm "vTop") (mkConst ``True) (mkConst (nm "vBad"))
    failsWith "helper value" (do let _ ← reach2 (nm "vTop") forbidU12; pure ()) [nm "unkV", nm "vBad"]
    addFx (nm "tBad") (mkConst (nm "unkT")) (mkConst ``True.intro)
    addFx (nm "tTop") (mkConst ``True) (mkConst (nm "tBad"))
    failsWith "helper type" (do let _ ← reach2 (nm "tTop") forbidU12; pure ()) [nm "unkT", nm "tBad"]
    addFx (nm "cHelp") (mkConst ``True) (mkConst ``True.intro)
    addFx (nm "cTop") (mkConst ``True) (mkConst (nm "cHelp"))
    let r ← reach2 (nm "cTop") forbidU12
    unless r.hit.isNone && r.seen.contains (nm "cHelp") do throwError "RK-U12 CLOSURE CONTROL FAILED: clean fixture"
    let r ← reach2 (nm "cTop") [nm "cTop"]
    unless r.hit == some [nm "cTop"] do throwError "RK-U12 CLOSURE: forbidden root fixture not flagged"
  if (← getEnv).contains (nm "vBad") then throwError "RK-U12 CLOSURE: fixture leaked out of withoutModifyingEnv"
  logInfo "RK-U12 CLOSURE NEGATIVES OK: unknown root, helper value, helper type; clean control; forbidden root; fixtures restored"

/-! ## 3. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``readsAt_chain_of_head
  checkAxioms ``readMachine_agrees_runReads_of_head

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo "RK-U12 STATUS: U12 is a CONDITIONAL intermediate (the forall-triple premise hw1 of U10/U11 is replaced by hHead : EnvFrame (coreHead X) and h0s : ReadsAt env₀ cref ws; a change of premise, not a supply; hk, hHead, h0, h0s, the two runs and hX remain premises). NOT supplied: ReadKeeps / EnvFrame (coreHead X) of the runtime, ReadsAt env₀ cref ws, env tie / C0, hall, ReadWorld, existence of runs, envR = envR', ci in envR, hag, hK, hq, coverage, FG."

end Tests.Gen5.ReadKindsU12Check
