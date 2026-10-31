import Tools.ShippingGen5ReadKindsU11
import Tests.Gen5.ReadKindsCheck
import Tests.Gen5.ReadKindsU5Check
import Tests.Gen5.ReadKindsU7Check
set_option autoImplicit false
-- NOT BUILT: no pod build yet for this file. Freeze: scripts/gen5/DG_READKINDS_U11_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U11 checks (Tools/ShippingGen5ReadKindsU11.lean)

1. TYPE: the theorem against an independently written `ExpU11` (from freeze §2; same reducible comparator `Tests.Gen3.ExpectedType`); positive control.
2. MUTANT: signature/defeq rejections of well-typed single-change statements, NOT semantic counterexamples.
3. COUNT: conjunct counts (auxiliary, necessary condition only).
4. CLOSURE: `reach2` (root tested against the forbid set; unknown constant = throw); negatives inside `withoutModifyingEnv`.
   `ReadKeeps`/`GetEnvFrame` are recorded as FACTs (premise use), not forbidden.
5. AXIOMS: propext / Classical.choice / Quot.sound only. -/

namespace Tests.Gen5.ReadKindsU11Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU11
open Tests.Gen3.ExpectedType
open Tests.Gen5.ReadKindsCheck (reach forbidConsts AReach body? badProj)
open Tests.Gen5.ReadKindsU7Check (conjCount)

/-! ## 1. Expected statements and mutants (freeze §2) -/

/-- freeze §2 U11 -/
def ExpU11 : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- positive control: separately written copy of the U11 statement -/
def CopyOfU11 : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U11: drop the r.shape = shape conjunct -/
def MutNoShape : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)

/-- U11: drop hX -/
def MutNoHX : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U11: drop h0 -/
def MutNoH0 : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U11: hw1 conclusion ReadsAt … w1 becomes ReadsAt … w2 (keeps ∀ w1 w2 w3 and the three RunsTo) -/
def MutHw1W2 : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w2)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U11: premise hk : ReadKeeps cref becomes hk : ReadWorld cref (well-typed, different statement) -/
def MutHkWorld : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadWorld cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``readMachine_agrees_runReads_of_readKeeps ``ExpU11
  checkExpected ``CopyOfU11 ``ExpU11
  logInfo "RK-U11 TYPE OK: 2 comparisons (1 theorem + 1 comparator positive control)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``readMachine_agrees_runReads_of_readKeeps ``MutNoShape
  checkMutant ``readMachine_agrees_runReads_of_readKeeps ``MutNoHX
  checkMutant ``readMachine_agrees_runReads_of_readKeeps ``MutNoH0
  checkMutant ``readMachine_agrees_runReads_of_readKeeps ``MutHw1W2
  checkMutant ``readMachine_agrees_runReads_of_readKeeps ``MutHkWorld
  logInfo "RK-U11 MUTANT REJECTED 5 (conclusion-conjunct drop: NoShape; premise changes: NoHX, NoH0, Hw1W2, HkWorld (ReadKeeps -> ReadWorld, one premise changed); signature/defeq rejection, not semantic counterexamples)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let cnt (n : Name) : Lean.Elab.TermElabM Nat := do
    let some ci := env.find? n | throwError "RK-U11 COUNT: {n} missing"
    let some v := ci.value? | throwError "RK-U11 COUNT: {n} has no value"
    return conjCount env [] v
  let e ← cnt ``ExpU11
  let ns ← cnt ``MutNoShape
  let nx ← cnt ``MutNoHX
  let n0 ← cnt ``MutNoH0
  let nw ← cnt ``MutHw1W2
  let nk ← cnt ``MutHkWorld
  if ns + 1 != e || nx != e || n0 != e || nw != e || nk != e then
    throwError "RK-U11 COUNT FAILED: Expected {e}, NoShape {ns}, NoHX {nx}, NoH0 {n0}, Hw1W2 {nw}, HkWorld {nk}"
  logInfo m!"RK-U11 COUNT OK (rule: And/Exists/∀-body leaves; premises not counted): Expected {e}, NoShape {ns} = -1, NoHX/NoH0/Hw1W2/HkWorld equal"

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
    if out.visited > cap then throwError "RK-U11 AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | throwError "RK-U11 CLOSURE unknown constant {c} reached via {path}"
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

def forbidU11 : List Name := forbidConsts.filter fun n => n != ``Lean.Expr.equal && n != ``Lean.Expr.eqv

/-- add a declaration whose type/value may name constants that do not exist (kernel check skipped; the env is restored by the caller) -/
def addFx (n : Name) (ty val : Expr) : MetaM Unit :=
  withOptions (fun o => o.setBool `debug.skipKernelTC true) <|
    addDecl (.defnDecl { name := n, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe })

def failsWith (what : String) (act : MetaM Unit) (needles : List Name) : MetaM Unit := do
  let r ← try act; pure none catch e => pure (some (← e.toMessageData.toString))
  match r with
  | none => throwError "RK-U11 CLOSURE NEGATIVE ACCEPTED: {what}"
  | some msg =>
    for n in needles do
      unless (msg.splitOn n.toString).length > 1 do
        throwError "RK-U11 CLOSURE NEGATIVE {what}: message does not name {n}: {msg}"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``readMachine_agrees_runReads_of_readKeeps
  let req := [``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps,
    ``Tools.ShippingGen5ReadKindsU10.readMachine_agrees_runReads_framed]
  let r ← reach2 c forbidU11
  if let some p := r.hit then throwError "RK-U11 AUDIT FAILED {c}: forbidden use via {p}"
  for t in req do
    unless r.seen.contains t do throwError "RK-U11 AUDIT FAILED {c}: {t} not reached"
  logInfo m!"RK-U11 REACH {c}: no T1Hyp / T1HypND (name, raw proj, rec) / Laws; reaches {req} (visited {r.visited}, unknown 0 (throws otherwise), opaque {r.opaqueNames}, no-value count {r.noBodyNames.size})"
  let rf ← reach2 c forbidConsts
  logInfo m!"RK-U11 FACT full forbid set (incl. Expr.equal/eqv) on {c}: {toString rf.hit}"
  logInfo m!"RK-U11 FACT ReadKeeps reached (premise hk, not a supplied law): {r.seen.contains ``Tools.ShippingStRefCorrespondence.ReadKeeps}; GetEnvFrame reached (via the existing lemma / U10c premise): {r.seen.contains ``Tools.ShippingEnvSnapshot.GetEnvFrame}"
  let r ← reach2 ``Lean.Expr.equal forbidConsts
  unless r.hit == some [``Lean.Expr.equal] do throwError "RK-U11 AUDIT FAILED: a forbidden root is not flagged"
  let r ← reach2 ``Tools.ShippingGen2.Laws forbidConsts
  unless r.hit == some [``Tools.ShippingGen2.Laws] do throwError "RK-U11 AUDIT FAILED: Laws as root is not flagged"
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.viaHelper2 forbidConsts
  if r.hit.isNone then throwError "RK-U11 AUDIT FAILED: scanner control misses the fixture"
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.cleanHelper forbidConsts
  if r.hit.isSome then throwError "RK-U11 AUDIT FAILED: scanner control flags the clean helper"
  let nm := fun (s : String) => (`Tests.Gen5.U11Fx).str s
  failsWith "unknown root" (do let _ ← reach2 (nm "noSuchRoot") forbidU11; pure ()) [nm "noSuchRoot"]
  withoutModifyingEnv do
    addFx (nm "vBad") (mkConst ``True) (mkConst (nm "unkV"))
    addFx (nm "vTop") (mkConst ``True) (mkConst (nm "vBad"))
    failsWith "helper value" (do let _ ← reach2 (nm "vTop") forbidU11; pure ()) [nm "unkV", nm "vBad"]
    addFx (nm "tBad") (mkConst (nm "unkT")) (mkConst ``True.intro)
    addFx (nm "tTop") (mkConst ``True) (mkConst (nm "tBad"))
    failsWith "helper type" (do let _ ← reach2 (nm "tTop") forbidU11; pure ()) [nm "unkT", nm "tBad"]
    addFx (nm "cHelp") (mkConst ``True) (mkConst ``True.intro)
    addFx (nm "cTop") (mkConst ``True) (mkConst (nm "cHelp"))
    let r ← reach2 (nm "cTop") forbidU11
    unless r.hit.isNone && r.seen.contains (nm "cHelp") do throwError "RK-U11 CLOSURE CONTROL FAILED: clean fixture"
    let r ← reach2 (nm "cTop") [nm "cTop"]
    unless r.hit == some [nm "cTop"] do throwError "RK-U11 CLOSURE: forbidden root fixture not flagged"
  if (← getEnv).contains (nm "vBad") then throwError "RK-U11 CLOSURE: fixture leaked out of withoutModifyingEnv"
  logInfo "RK-U11 CLOSURE NEGATIVES OK: unknown root, helper value, helper type; clean control; forbidden root; fixtures restored"

/-! ## 3. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``readMachine_agrees_runReads_of_readKeeps

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo "RK-U11 STATUS: U11 is a CONDITIONAL intermediate (premise hk : ReadKeeps cref replaces hg : GetEnvFrame via getEnvFrame_of_readKeeps; ReadKeeps is a sufficient condition, converse/equivalence unproved; hw1, h0, hX, two runs remain premises). NOT supplied: ReadKeeps of the runtime, hw1, env tie / C0, hall, ReadWorld, existence of runs, envR = envR', ci in envR, hag, hK, hq, coverage, FG."

end Tests.Gen5.ReadKindsU11Check
