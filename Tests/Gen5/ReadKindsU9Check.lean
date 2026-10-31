import Tools.ShippingGen5ReadKindsU9
import Tests.Gen5.ReadKindsCheck
import Tests.Gen5.ReadKindsU5Check
import Tests.Gen5.ReadKindsU7Check
set_option autoImplicit false
-- NOT BUILT (header to be synced with the clean build SHA). Freeze: scripts/gen5/DG_READKINDS_U9_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U9 checks (Tools/ShippingGen5ReadKindsU9.lean)

1. TYPE: each theorem against an independently written `Exp…` statement (written from freeze §1-§3, not copied from the Lean; same reducible
   comparator `Tests.Gen3.ExpectedType`); positive control: the comparator accepts a separately written copy.
2. MUTANT: signature/defeq rejections of well-typed single-change statements, NOT semantic counterexamples. An ill-typed mutant is not counted.
3. COUNT: conjunct counts (auxiliary, necessary condition only).
4. CLOSURE: `reach2` (defined here; the shared `reach` is unchanged): the root itself is tested against the forbid set; an unknown constant
   is an immediate `throwError`. Negatives (fixtures built inside `withoutModifyingEnv`): unknown root, a helper VALUE naming an unknown constant,
   an existing helper whose TYPE only names an unknown constant; clean control. `Expr.equal`/`eqv` is excluded from the forbid set as in U8: that is
   NOT a supply of a soundness law. `ReflExprAgree` in U9b is recorded as a FACT, not forbidden.
5. AXIOMS: propext / Classical.choice / Quot.sound only. -/

namespace Tests.Gen5.ReadKindsU9Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand Tools.Prototype.DGenProv
open Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5 Tools.ShippingGen5ReadKindsU7
open Tools.ShippingGen5ReadKindsU9
open Tests.Gen3.ExpectedType
open Tests.Gen5.ReadKindsCheck (reach forbidConsts AReach body? badProj)
open Tests.Gen5.ReadKindsU7Check (conjCount)

/-! ## 1. Expected statements (freeze §1-§3) -/

/-- freeze §1: a successful `dataE r` run: the three reflections succeed and the result is `dataPure` of them -/
def ExpDataERun : Prop :=
  ∀ {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (h : RunsTo (dataE r) mctx mref cctx cref w e w'),
    ∃ body dom lay : Lean.Expr,
      reflExpr r.shape.body = .ok body ∧ reflExpr r.dom = .ok dom ∧
      layoutE r.shape.layout = some lay ∧ e = dataPure r body dom lay

/-- freeze §2 -/
def ExpStoredRun : Prop :=
  ∀ (hag : Tools.Prototype.DGenStored2.ReflExprAgree)
    {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (hrun : RunsTo (dataE r) mctx mref cctx cref w e w') (d : MachineData),
    ∃ body lay : Lean.Expr, reflExpr r.shape.body = .ok body ∧ layoutE r.shape.layout = some lay ∧
      (Tools.Prototype.DGenStored2.ShapeDenotes (dataShapeE r.shape body lay) d.shape →
        Tools.Prototype.DGenProv.StoredFromRead d r)

/-- freeze §3 -/
def ExpAgreesAt : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h1 : ∀ (env : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env v1 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref v1)
    (hR : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- positive control: a separately written copy of the `dataE_run` statement is accepted -/
def CopyOfDataERun : Prop :=
  ∀ {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (h : RunsTo (dataE r) mctx mref cctx cref w e w'),
    ∃ body dom lay : Lean.Expr,
      reflExpr r.shape.body = .ok body ∧ reflExpr r.dom = .ok dom ∧
      layoutE r.shape.layout = some lay ∧ e = dataPure r body dom lay

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``dataE_run ``ExpDataERun
  checkExpected ``storedFromRead_of_dataE_run ``ExpStoredRun
  checkExpected ``readMachine_agrees_runReads_at ``ExpAgreesAt
  checkExpected ``CopyOfDataERun ``ExpDataERun
  logInfo "RK-U9 TYPE OK: 4 comparisons (3 theorems + 1 comparator positive control)"

/-! ## 2. Mutants (signature / defeq rejections of well-typed single changes, not semantic counterexamples) -/

/-- U9a: drop the `layoutE` conjunct -/
def MutDataENoLayout : Prop :=
  ∀ {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (h : RunsTo (dataE r) mctx mref cctx cref w e w'),
    ∃ body dom lay : Lean.Expr,
      reflExpr r.shape.body = .ok body ∧ reflExpr r.dom = .ok dom ∧ e = dataPure r body dom lay
/-- U9a: drop `e = dataPure …` -/
def MutDataENoPure : Prop :=
  ∀ {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (h : RunsTo (dataE r) mctx mref cctx cref w e w'),
    ∃ body dom lay : Lean.Expr,
      reflExpr r.shape.body = .ok body ∧ reflExpr r.dom = .ok dom ∧ layoutE r.shape.layout = some lay
/-- U9a: the `dom` reflection is applied to the body instead of `r.dom` -/
def MutDataEDomBody : Prop :=
  ∀ {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (h : RunsTo (dataE r) mctx mref cctx cref w e w'),
    ∃ body dom lay : Lean.Expr,
      reflExpr r.shape.body = .ok body ∧ reflExpr r.shape.body = .ok dom ∧
      layoutE r.shape.layout = some lay ∧ e = dataPure r body dom lay
/-- U9b: drop `hag` -/
def MutStoredNoHag : Prop :=
  ∀ {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (hrun : RunsTo (dataE r) mctx mref cctx cref w e w') (d : MachineData),
    ∃ body lay : Lean.Expr, reflExpr r.shape.body = .ok body ∧ layoutE r.shape.layout = some lay ∧
      (Tools.Prototype.DGenStored2.ShapeDenotes (dataShapeE r.shape body lay) d.shape →
        Tools.Prototype.DGenProv.StoredFromRead d r)
/-- U9b: drop the `ShapeDenotes` antecedent -/
def MutStoredNoK : Prop :=
  ∀ (hag : Tools.Prototype.DGenStored2.ReflExprAgree)
    {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (hrun : RunsTo (dataE r) mctx mref cctx cref w e w') (d : MachineData),
    ∃ body lay : Lean.Expr, reflExpr r.shape.body = .ok body ∧ layoutE r.shape.layout = some lay ∧
      Tools.Prototype.DGenProv.StoredFromRead d r
/-- U9b: drop the conjunct `reflExpr r.shape.body = .ok body` -/
def MutStoredNoBody : Prop :=
  ∀ (hag : Tools.Prototype.DGenStored2.ReflExprAgree)
    {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (hrun : RunsTo (dataE r) mctx mref cctx cref w e w') (d : MachineData),
    ∃ body lay : Lean.Expr, layoutE r.shape.layout = some lay ∧
      (Tools.Prototype.DGenStored2.ShapeDenotes (dataShapeE r.shape body lay) d.shape →
        Tools.Prototype.DGenProv.StoredFromRead d r)
/-- U9c: drop `hX` -/
def MutAgreesNoHX : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h1 : ∀ (env : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env v1 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref v1)
    (hR : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape
/-- U9c: drop the `h1` premise -/
def MutAgreesNoH1 : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hR : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape
/-- U9c: conclusion keeps only the entry conjunct -/
def MutAgreesEntryOnly : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h1 : ∀ (env : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env v1 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref v1)
    (hR : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3)
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``dataE_run ``MutDataENoLayout
  checkMutant ``dataE_run ``MutDataENoPure
  checkMutant ``dataE_run ``MutDataEDomBody
  checkMutant ``storedFromRead_of_dataE_run ``MutStoredNoHag
  checkMutant ``storedFromRead_of_dataE_run ``MutStoredNoK
  checkMutant ``storedFromRead_of_dataE_run ``MutStoredNoBody
  checkMutant ``readMachine_agrees_runReads_at ``MutAgreesNoHX
  checkMutant ``readMachine_agrees_runReads_at ``MutAgreesNoH1
  checkMutant ``readMachine_agrees_runReads_at ``MutAgreesEntryOnly
  logInfo "RK-U9 MUTANT REJECTED 9 (dataE_run 3, storedFromRead_of_dataE_run 3, readMachine_agrees_runReads_at 3; 4 of them drop a conclusion conjunct (NoLayout, NoPure, NoBody, EntryOnly); NoK drops the denotation antecedent; signature/defeq rejection, not semantic counterexamples)"

/-! ### 2b. Conjunct-count auxiliary check (necessary condition only, not proof of a single change) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let cnt (n : Name) : Lean.Elab.TermElabM Nat := do
    let some ci := env.find? n | throwError "RK-U9 COUNT: {n} missing"
    let some v := ci.value? | throwError "RK-U9 COUNT: {n} has no value"
    return conjCount env [] v
  let a ← cnt ``ExpDataERun
  let al ← cnt ``MutDataENoLayout
  let ap ← cnt ``MutDataENoPure
  let ad ← cnt ``MutDataEDomBody
  if al + 1 != a || ap + 1 != a || ad != a then
    throwError "RK-U9 COUNT FAILED dataE_run: Expected {a}, NoLayout {al}, NoPure {ap}, DomBody {ad}"
  let b ← cnt ``ExpStoredRun
  let bh ← cnt ``MutStoredNoHag
  let bk ← cnt ``MutStoredNoK
  let bb ← cnt ``MutStoredNoBody
  if bh != b || bk != b || bb + 1 != b then
    throwError "RK-U9 COUNT FAILED stored: Expected {b}, NoHag {bh}, NoK {bk}, NoBody {bb}"
  let c ← cnt ``ExpAgreesAt
  let ch ← cnt ``MutAgreesNoHX
  let c1 ← cnt ``MutAgreesNoH1
  let ce ← cnt ``MutAgreesEntryOnly
  if ch != c || c1 != c || ce + 1 != c then
    throwError "RK-U9 COUNT FAILED agrees: Expected {c}, NoHX {ch}, NoH1 {c1}, EntryOnly {ce}"
  logInfo m!"RK-U9 COUNT OK (rule: And/Exists/∀-body leaves; premises not counted, so premise-drop mutants equal Expected): dataE_run Expected {a} (NoLayout {al} = -1, NoPure {ap} = -1, DomBody {ad} = equal); stored Expected {b} (NoHag {bh}, NoK {bk} equal, NoBody {bb} = -1); agrees Expected {c} (NoHX {ch}, NoH1 {c1} equal, EntryOnly {ce} = -1)"

/-! ## 3. Closure: `reach2` (root tested against the forbid set; unknown constant = immediate throwError) -/

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
    if out.visited > cap then throwError "RK-U9 AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | throwError "RK-U9 CLOSURE unknown constant {c} reached via {path}"
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

def forbidU9 : List Name := forbidConsts.filter fun n => n != ``Lean.Expr.equal && n != ``Lean.Expr.eqv

/-- add a declaration whose type/value may name constants that do not exist (kernel check skipped; the env is restored by the caller) -/
def addFx (n : Name) (ty val : Expr) : MetaM Unit :=
  withOptions (fun o => o.setBool `debug.skipKernelTC true) <|
    addDecl (.defnDecl { name := n, levelParams := [], type := ty, value := val, hints := .abbrev, safety := .safe })

def failsWith (what : String) (act : MetaM Unit) (needles : List Name) : MetaM Unit := do
  let r ← try act; pure none catch e => pure (some (← e.toMessageData.toString))
  match r with
  | none => throwError "RK-U9 CLOSURE NEGATIVE ACCEPTED: {what}"
  | some msg =>
    for n in needles do
      unless (msg.splitOn n.toString).length > 1 do
        throwError "RK-U9 CLOSURE NEGATIVE {what}: message does not name {n}: {msg}"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (c, req) in [(``dataE_run, [``Tools.ShippingEntrySoundness.RunsTo.bind, ``Tools.ShippingMachineEntry.RunsTo.pure_eq, ``Tools.ShippingChildInv.throwError_not_runs]),
      (``storedFromRead_of_dataE_run, [``Tools.ShippingGen5ReadKindsU9.dataE_run, ``Tools.Prototype.DGenStored2.storedFromRead_of_kernelRead]),
      (``readMachine_agrees_runReads_at, [``Tools.Prototype.DGenProv.readMachine_run, ``Tools.ShippingGen5Env.ci_of_readsAt, ``Tools.ShippingGen5Env.envR_of_readsAt])] do
    let r ← reach2 c forbidU9
    if let some p := r.hit then throwError "RK-U9 AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RK-U9 AUDIT FAILED {c}: {t} not reached"
    logInfo m!"RK-U9 REACH {c}: no T1Hyp / T1HypND (name, raw proj, rec) / Laws; reaches {req} (visited {r.visited}, unknown 0 (throws otherwise), opaque {r.opaqueNames}, no-value count {r.noBodyNames.size})"
  for c in [``dataE_run, ``storedFromRead_of_dataE_run, ``readMachine_agrees_runReads_at] do
    let r ← reach2 c forbidConsts
    logInfo m!"RK-U9 FACT full forbid set (incl. Expr.equal/eqv) on {c}: {toString r.hit}"
  let r ← reach2 ``storedFromRead_of_dataE_run forbidU9
  logInfo m!"RK-U9 FACT ReflExprAgree reached by storedFromRead_of_dataE_run (it is the premise hag): {r.seen.contains ``Tools.Prototype.DGenStored2.ReflExprAgree}"
  -- root itself is tested against the forbid set
  let r ← reach2 ``Lean.Expr.equal forbidConsts
  unless r.hit == some [``Lean.Expr.equal] do throwError "RK-U9 AUDIT FAILED: a forbidden root is not flagged"
  let r ← reach2 ``Tools.ShippingGen2.Laws forbidConsts
  unless r.hit == some [``Tools.ShippingGen2.Laws] do throwError "RK-U9 AUDIT FAILED: Laws as root is not flagged"
  -- fixture detection controls (existing shared fixtures)
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.viaHelper2 forbidConsts
  if r.hit.isNone then throwError "RK-U9 AUDIT FAILED: scanner control misses the fixture"
  let r ← reach2 `Tests.Gen5.ReadKindsFixtureOther.cleanHelper forbidConsts
  if r.hit.isSome then throwError "RK-U9 AUDIT FAILED: scanner control flags the clean helper"
  -- unknown-name negatives (fixtures inside withoutModifyingEnv)
  let nm := fun (s : String) => (`Tests.Gen5.U9Fx).str s
  failsWith "unknown root" (do let _ ← reach2 (nm "noSuchRoot") forbidU9; pure ()) [nm "noSuchRoot"]
  withoutModifyingEnv do
    -- helper VALUE names an unknown constant
    addFx (nm "vBad") (mkConst ``True) (mkConst (nm "unkV"))
    addFx (nm "vTop") (mkConst ``True) (mkConst (nm "vBad"))
    failsWith "helper value" (do let _ ← reach2 (nm "vTop") forbidU9; pure ()) [nm "unkV", nm "vBad"]
    -- an EXISTING helper whose TYPE alone names an unknown constant (its value is `True.intro`)
    addFx (nm "tBad") (mkConst (nm "unkT")) (mkConst ``True.intro)
    addFx (nm "tTop") (mkConst ``True) (mkConst (nm "tBad"))
    failsWith "helper type" (do let _ ← reach2 (nm "tTop") forbidU9; pure ()) [nm "unkT", nm "tBad"]
    -- clean control built the same way
    addFx (nm "cHelp") (mkConst ``True) (mkConst ``True.intro)
    addFx (nm "cTop") (mkConst ``True) (mkConst (nm "cHelp"))
    let r ← reach2 (nm "cTop") forbidU9
    unless r.hit.isNone && r.seen.contains (nm "cHelp") do throwError "RK-U9 CLOSURE CONTROL FAILED: clean fixture"
    -- a forbidden ROOT (the root itself is in the forbid set)
    let r ← reach2 (nm "cTop") [nm "cTop"]
    unless r.hit == some [nm "cTop"] do throwError "RK-U9 CLOSURE: forbidden root fixture not flagged"
  if (← getEnv).contains (nm "vBad") then throwError "RK-U9 CLOSURE: fixture leaked out of withoutModifyingEnv"
  logInfo "RK-U9 CLOSURE NEGATIVES OK: unknown root, helper value, helper type (each names the intended unknown constant and the helper on the path); clean control; forbidden root; fixtures restored"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``dataE_run, ``storedFromRead_of_dataE_run, ``readMachine_agrees_runReads_at] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo "RK-U9 STATUS: readMachine_agrees_runReads_at (U9c, named-world ReadsAt h0/h1/hR + hX) and storedFromRead_of_dataE_run (U9b, conditional on hag and the ShapeDenotes antecedent) are CONDITIONAL intermediates; dataE_run (U9a) has no extra premise. NOT supplied: hag, hK, hall / DG-ENV C0, existence of the two runs, envR = envR', ci ∈ envR, GateDefines, srcDom, ls/outs/nexts, hq, coverage, FG."

end Tests.Gen5.ReadKindsU9Check
