import Tools.ShippingGen5ReadKindsU10
import Tests.Gen5.ReadKindsCheck
import Tests.Gen5.ReadKindsU5Check
import Tests.Gen5.ReadKindsU7Check
set_option autoImplicit false
-- Built: kjob lake build Tests.Gen5.ReadKindsU10Check exit 0 (823 jobs) in the pod (job g5rk-r16) on the uncommitted working tree whose Lean+lakefile content equals commit 0da94331 (conditional intermediate, M5/FG not complete; clean build is the coder's). Freeze: scripts/gen5/DG_READKINDS_U10_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U10 checks (Tools/ShippingGen5ReadKindsU10.lean)

1. TYPE: each theorem against an independently written `Exp…` statement (written from freeze §2, not copied from the Lean; same reducible
   comparator `Tests.Gen3.ExpectedType`); positive control: the comparator accepts a separately written copy.
2. MUTANT: signature/defeq rejections of well-typed single-change statements, NOT semantic counterexamples.
3. COUNT: conjunct counts (auxiliary, necessary condition only).
4. CLOSURE: `reach2` (root tested against the forbid set; unknown constant = immediate throwError); negatives inside `withoutModifyingEnv`.
   `GetEnvFrame` is recorded as a FACT (premise use), not forbidden; `Expr.equal`/`eqv` excluded from the forbid set as in U8/U9 (not a supply of a soundness law).
5. AXIOMS: propext / Classical.choice / Quot.sound only. -/

namespace Tests.Gen5.ReadKindsU10Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU10
open Tests.Gen3.ExpectedType
open Tests.Gen5.ReadKindsCheck (reach forbidConsts AReach body? badProj)
open Tests.Gen5.ReadKindsU7Check (conjCount)

/-! ## 1. Expected statements and mutants (freeze §2) -/

/-- freeze §2 U10a -/
def ExpHR : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {w5 : Void IO.RealWorld}
    {env₀ : Lean.Environment}
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1),
    ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3

/-- positive control: separately written copy of the U10a statement -/
def CopyOfHR : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {w5 : Void IO.RealWorld}
    {env₀ : Lean.Environment}
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1),
    ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3

/-- freeze §2 U10b -/
def ExpH1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {env₀ : Lean.Environment} {w : Void IO.RealWorld}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w),
    ∀ (env : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env v1 → Tools.ShippingGen5Env.ReadsAt env₀ cref v1

/-- freeze §2 U10c -/
def ExpFramed : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
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

/-- U10a: drop the w3 conjunct -/
def MutHRNoW3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {w5 : Void IO.RealWorld}
    {env₀ : Lean.Environment}
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1),
    ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2

/-- U10a: drop the w2 conjunct -/
def MutHRNoW2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {w5 : Void IO.RealWorld}
    {env₀ : Lean.Environment}
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1),
    ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w3

/-- U10a: hw1 keeps ∀ w1 w2 w3 and the three RunsTo premises, only its conclusion ReadsAt … w1 becomes ReadsAt … w2 -/
def MutHRHw1W2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {w5 : Void IO.RealWorld}
    {env₀ : Lean.Environment}
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w2),
    ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3

/-- U10b: conclusion ReadsAt … v1 becomes ReadsAt … w -/
def MutH1AtW : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {env₀ : Lean.Environment} {w : Void IO.RealWorld}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w),
    ∀ (env : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env v1 → Tools.ShippingGen5Env.ReadsAt env₀ cref w

/-- U10c: drop hX -/
def MutFramedNoHX : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
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

/-- U10c: drop h0 -/
def MutFramedNoH0 : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
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

/-- U10c: drop the r.shape = shape conjunct -/
def MutFramedEntryOnly : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
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

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``hR_of_w1 ``ExpHR
  checkExpected ``h1_of_h0 ``ExpH1
  checkExpected ``readMachine_agrees_runReads_framed ``ExpFramed
  checkExpected ``CopyOfHR ``ExpHR
  logInfo "RK-U10 TYPE OK: 4 comparisons (3 theorems + 1 comparator positive control)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``hR_of_w1 ``MutHRNoW3
  checkMutant ``hR_of_w1 ``MutHRNoW2
  checkMutant ``hR_of_w1 ``MutHRHw1W2
  checkMutant ``h1_of_h0 ``MutH1AtW
  checkMutant ``readMachine_agrees_runReads_framed ``MutFramedNoHX
  checkMutant ``readMachine_agrees_runReads_framed ``MutFramedNoH0
  checkMutant ``readMachine_agrees_runReads_framed ``MutFramedEntryOnly
  logInfo "RK-U10 MUTANT REJECTED 7 (hR_of_w1 3, h1_of_h0 1, readMachine_agrees_runReads_framed 3; conclusion-conjunct drops: NoW3, NoW2, EntryOnly; premise/conclusion changes: Hw1W2 (hw1 keeps forall w1 w2 w3 and 3 RunsTo, ends at w2), H1AtW, NoHX, NoH0; signature/defeq rejection, not semantic counterexamples)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let cnt (n : Name) : Lean.Elab.TermElabM Nat := do
    let some ci := env.find? n | throwError "RK-U10 COUNT: {n} missing"
    let some v := ci.value? | throwError "RK-U10 COUNT: {n} has no value"
    return conjCount env [] v
  let a ← cnt ``ExpHR
  let a3 ← cnt ``MutHRNoW3
  let a2 ← cnt ``MutHRNoW2
  let aw ← cnt ``MutHRHw1W2
  if a3 + 1 != a || a2 + 1 != a || aw != a then
    throwError "RK-U10 COUNT FAILED hR: Expected {a}, NoW3 {a3}, NoW2 {a2}, Hw1W2 {aw}"
  let b ← cnt ``ExpH1
  let bw ← cnt ``MutH1AtW
  if bw != b then throwError "RK-U10 COUNT FAILED h1: Expected {b}, AtW {bw}"
  let c ← cnt ``ExpFramed
  let ch ← cnt ``MutFramedNoHX
  let c0 ← cnt ``MutFramedNoH0
  let ce ← cnt ``MutFramedEntryOnly
  if ch != c || c0 != c || ce + 1 != c then
    throwError "RK-U10 COUNT FAILED framed: Expected {c}, NoHX {ch}, NoH0 {c0}, EntryOnly {ce}"
  logInfo m!"RK-U10 COUNT OK (rule: And/Exists/∀-body leaves; premises not counted, so premise-change mutants equal Expected): hR Expected {a} (NoW3 {a3} = -1, NoW2 {a2} = -1, Hw1W2 {aw} = equal); h1 Expected {b} (AtW {bw} equal); framed Expected {c} (NoHX {ch}, NoH0 {c0} equal, EntryOnly {ce} = -1)"

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
    if out.visited > cap then throwError "RK-U10 AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | throwError "RK-U10 CLOSURE unknown constant {c} reached via {path}"
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

def forbidU10 : List Name := forbidConsts.filter fun n => n != ``Lean.Expr.equal && n != ``Lean.Expr.eqv

/-- add a declaration whose type/value may name constants that do not exist (kernel check skipped; the env is restored by the caller) -/
def addFx (n : Name) (ty val : Expr) : MetaM Unit :=
  withOptions (fun o => o.setBool `debug.skipKernelTC true) <|
    addDecl (.defnDecl { name := n, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe })

def failsWith (what : String) (act : MetaM Unit) (needles : List Name) : MetaM Unit := do
  let r ← try act; pure none catch e => pure (some (← e.toMessageData.toString))
  match r with
  | none => throwError "RK-U10 CLOSURE NEGATIVE ACCEPTED: {what}"
  | some msg =>
    for n in needles do
      unless (msg.splitOn n.toString).length > 1 do
        throwError "RK-U10 CLOSURE NEGATIVE {what}: message does not name {n}: {msg}"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (c, req) in [(``hR_of_w1, [``Tools.ShippingGen5Env.ReadsAt.of_frame, ``Tools.ShippingEnvSnapshot.envFrame_getConstInfo]),
      (``h1_of_h0, [``Tools.ShippingGen5Env.ReadsAt.of_frame]),
      (``readMachine_agrees_runReads_framed, [``Tools.ShippingGen5ReadKindsU10.hR_of_w1, ``Tools.ShippingGen5ReadKindsU10.h1_of_h0,
        ``Tools.ShippingGen5ReadKindsU9.readMachine_agrees_runReads_at])] do
    let r ← reach2 c forbidU10
    if let some p := r.hit then throwError "RK-U10 AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RK-U10 AUDIT FAILED {c}: {t} not reached"
    logInfo m!"RK-U10 REACH {c}: no T1Hyp / T1HypND (name, raw proj, rec) / Laws; reaches {req} (visited {r.visited}, unknown 0 (throws otherwise), opaque {r.opaqueNames}, no-value count {r.noBodyNames.size})"
  for c in [``hR_of_w1, ``h1_of_h0, ``readMachine_agrees_runReads_framed] do
    let r ← reach2 c forbidConsts
    logInfo m!"RK-U10 FACT full forbid set (incl. Expr.equal/eqv) on {c}: {toString r.hit}"
    let r2 ← reach2 c forbidU10
    logInfo m!"RK-U10 FACT GetEnvFrame reached by {c} (premise hg, not a supplied law): {r2.seen.contains ``Tools.ShippingEnvSnapshot.GetEnvFrame}"
  let r ← reach2 ``Lean.Expr.equal forbidConsts
  unless r.hit == some [``Lean.Expr.equal] do throwError "RK-U10 AUDIT FAILED: a forbidden root is not flagged"
  let r ← reach2 ``Tools.ShippingGen2.Laws forbidConsts
  unless r.hit == some [``Tools.ShippingGen2.Laws] do throwError "RK-U10 AUDIT FAILED: Laws as root is not flagged"
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.viaHelper2 forbidConsts
  if r.hit.isNone then throwError "RK-U10 AUDIT FAILED: scanner control misses the fixture"
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.cleanHelper forbidConsts
  if r.hit.isSome then throwError "RK-U10 AUDIT FAILED: scanner control flags the clean helper"
  let nm := fun (s : String) => (`Tests.Gen5.U10Fx).str s
  failsWith "unknown root" (do let _ ← reach2 (nm "noSuchRoot") forbidU10; pure ()) [nm "noSuchRoot"]
  withoutModifyingEnv do
    addFx (nm "vBad") (mkConst ``True) (mkConst (nm "unkV"))
    addFx (nm "vTop") (mkConst ``True) (mkConst (nm "vBad"))
    failsWith "helper value" (do let _ ← reach2 (nm "vTop") forbidU10; pure ()) [nm "unkV", nm "vBad"]
    addFx (nm "tBad") (mkConst (nm "unkT")) (mkConst ``True.intro)
    addFx (nm "tTop") (mkConst ``True) (mkConst (nm "tBad"))
    failsWith "helper type" (do let _ ← reach2 (nm "tTop") forbidU10; pure ()) [nm "unkT", nm "tBad"]
    addFx (nm "cHelp") (mkConst ``True) (mkConst ``True.intro)
    addFx (nm "cTop") (mkConst ``True) (mkConst (nm "cHelp"))
    let r ← reach2 (nm "cTop") forbidU10
    unless r.hit.isNone && r.seen.contains (nm "cHelp") do throwError "RK-U10 CLOSURE CONTROL FAILED: clean fixture"
    let r ← reach2 (nm "cTop") [nm "cTop"]
    unless r.hit == some [nm "cTop"] do throwError "RK-U10 CLOSURE: forbidden root fixture not flagged"
  if (← getEnv).contains (nm "vBad") then throwError "RK-U10 CLOSURE: fixture leaked out of withoutModifyingEnv"
  logInfo "RK-U10 CLOSURE NEGATIVES OK: unknown root, helper value, helper type (each names the intended unknown constant and the helper on the path); clean control; forbidden root; fixtures restored"

/-! ## 3. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``hR_of_w1, ``h1_of_h0, ``readMachine_agrees_runReads_framed] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo "RK-U10 STATUS: U10a/b/c are CONDITIONAL intermediates (premises hg = GetEnvFrame used as an existing definition, not a proof of the runtime law; hw1 quantified over all matching triples, not a single post-coreHead world; h0; hX). NOT supplied: hw1 (ioEnv class D), env tie / DG-ENV C0, hall, ReadWorld, existence of the runs, envR = envR', ci ∈ envR, hag, hK, hq, coverage, FG."

end Tests.Gen5.ReadKindsU10Check
