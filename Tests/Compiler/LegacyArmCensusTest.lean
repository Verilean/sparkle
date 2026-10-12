import Sparkle
import IP.Net.IPv4
import IP.Net.TCP
import IP.Net.Ethernet
import IP.Net.HTTP
import IP.BitNet.SignalHelpers
import IP.Crypto.SHA256
import IP.Video.H264.Quant
import IP.RV32.SoC

/-! # A census of the legacy route's top leaves (logs only; never throws)

Purpose (G2, rounds 19–20): choose where the proof effort goes from a
MEASUREMENT instead of a guess.

**Pass 1 (round 19) — syntactic.** Over the definitions of the imported `IP`
/ `Examples` / `Tests` modules whose result type is syntactically a `Signal`
(after the binders), in name order, at most `cap` of them:

1. the ROUTE the shipping entry gives the declaration, from the entry's own
   pure gates on the entry's own constant
   (`entryConst true false [] ci …`, then `certifiedShape?`,
   `mixedCertifiedShape?`, `machineShape?`): `certified` / `mixed` /
   `machine` / `legacy`;
2. for the `legacy` ones, the TOP LEAF: the body after `openRecordInputs`,
   `stripMemoizeWrappers` and `lambdaTelescope` (the entry's own steps), and
   of it the head, `fallbackKind`, and for a map head the head of the mapped
   function's body.

**Pass 2 (round 20) — the real entry is RUN.** The population of pass 1 is
every Signal-valued definition, not the declarations the entry RETURNS for.
So each legacy-route candidate is handed to the shipping entry itself
(`synthesizeCombinationalCore n [] false`: the certified front end on, no
parameters, not symbolic — what `#synthesize…` runs before its cleanup), and
the outcome is recorded: `RETURNED`, `THREW` (first line of the message),
`TIMEOUT` (the per-declaration heartbeat bound), `RUNTIME` (another runtime
exception, e.g. the recursion depth), or `NOT RUN` (the test's wall-clock
budget was used up). For the RETURNED ones only: the head / `fallbackKind`
tables again, and per declaration

* the binders: how many are scalar Signals (`BitVec` / `Bool` payload),
  structured Signals, domain binders, others (parameters, instances);
* the payload of the result type;
* for a `<lambda>` head (a beta-redex at the top of the leaf): the head after
  `headBeta`;
* the combined class `head | binders | result payload`.

**Isolation of the runs.** Each run is between `Meta.saveState` and its
`restore` (environment, messages, metavariables); the entry resets its own
`IO.Ref` caches at depth 0, and `sparkleSynthDepth` is set to 0 before each
run in case an earlier one was cut off. Runtime exceptions (heartbeats,
recursion depth) are caught with `tryCatchRuntimeEx`: plain `try … catch`
does not catch them.

**What is still NOT measured.** Which handler accepts each node at run time;
sub-expressions of the leaf; structure- / product-valued declarations (their
leaves need `splitReturnLeaves`); declarations outside the imports. A
declaration the gates route to `machine` whose machine synthesis then
declines also ends in the legacy arm; those are not run here.

**Pass 3 (round 22) — the projection class.** For each RETURNED declaration
with a `<lambda>` head (the 45 structure projection functions), the
OBSERVABLE premises of the generic theorem `proj_entry_output`
(`Tools/ShippingLegacySemProj.lean`) are checked on the real constant
(`projCheck`), in this order — the first one that fails is reported:

1. the three gates decline on the entry's constant (`old`, `mixed`, `hmach`);
2. the stripped value has as many nested lambdas as the telescope opens
   variables (`hbody`: `lams sp b`, `b` not a lambda);
3. each declared type and the leaf equal the `instantiateRevRange` results
   over the variables opened before (`TypesOkFrom`'s types, the leaf
   equation);
4. the telescope's variables are distinct (`LamTelescopeND`'s extra
   conjunct, observed on this run);
5. the leaf is an application with a lambda head (`hshape`);
6. its `fallbackKind` is `other` (`hkind`);
7. its reducible `whnf` is the variable at some index `i` (`hwhnf`);
8. the type oracle THROWS on a domain binder and on no other, and returns
   `bit` on a `Bool` payload / `bitVector n` (`n ≠ 1`) on a `BitVec` payload
   (`TypesOkFrom`'s oracle facts; a returning or throwing run is one
   observation, not the universally quantified premise). A `bit` port on a
   `BitVec` payload is a WIDTH-ONE field: reported as non-fitting;
9. the binder at index `i` is not the domain binder (`hk`);
10. the `whnf` of the leaf's inferred type is Signal-headed (`hres`).

Log lines: `PROJ CLASS: fits N of M`, the fitting ones by
`binders | index | kind`, and each non-fitting declaration with its first
failing observation.

One run in this environment: an observation. The whole block is inside
`try … catch`, each declaration in its own; the outer heartbeat limit is
lifted. -/

open Lean Meta Sparkle.Compiler.Elab

namespace Sparkle.Tests.Compiler.LegacyArmCensusTest

/-- At most this many candidate declarations are examined (pass 1). -/
def cap : Nat := 400

/-- Heartbeat bound of ONE run of the entry in pass 2 (in the units of the
`maxHeartbeats` option). -/
def runHeartbeats : Nat := 200000

/-- Wall-clock budget of pass 2, in milliseconds; declarations not reached
are reported as `NOT RUN`. -/
def runBudgetMs : Nat := 240000

/-- The head of an expression, as a label. -/
def headOf (e : Lean.Expr) : String :=
  match e.getAppFn with
  | .const n _ => n.toString
  | .fvar _ => "<fvar>"
  | .lam .. => "<lambda>"
  | .letE .. => "<let>"
  | .proj s _ _ => s!"<proj {s}>"
  | .mdata .. => "<mdata>"
  | _ => "<other>"

/-- The arm `translateFallback` dispatches to, as a label. -/
def kindOf (e : Lean.Expr) : String :=
  match fallbackKind e with
  | .boolControl => "boolControl"
  | .vectorMux .. => "vectorMux"
  | .setWidth .. => "setWidth"
  | .register .. => "register"
  | .registerEnable .. => "registerEnable"
  | .loopRegister .. => "loopRegister"
  | .circuitDo .. => "circuitDo"
  | .circuitDo2 .. => "circuitDo2"
  | .memory .. => "memory"
  | .slice .. => "slice"
  | .concat .. => "concat"
  | .concatLit .. => "concatLit"
  | .zextMap .. => "zextMap"
  | .sliceF .. => "sliceF"
  | .other => "other"

/-- For a map head: the head of the mapped function's body. -/
def mapBodyOf (e : Lean.Expr) : Option String :=
  let args := e.getAppArgs
  if args.size < 2 then none
  else
    match args[args.size - 2]! with
    | .lam _ _ b _ => some (headOf b)
    | f => some ("non-lambda " ++ headOf f)

/-- One more occurrence of `k`; the first declaration seen is kept as the
example. -/
def bump (m : Std.HashMap String (Nat × String)) (k ex : String) :
    Std.HashMap String (Nat × String) :=
  match m.get? k with
  | some (c, e) => m.insert k (c + 1, e)
  | none => m.insert k (1, ex)

/-- A count table, largest first. -/
def render (m : Std.HashMap String (Nat × String)) : String :=
  let l := m.toList.toArray.qsort (fun a b => decide (a.2.1 > b.2.1))
  String.intercalate "; " (l.toList.map fun p => s!"{p.1}: {p.2.1} (e.g. {p.2.2})")

/-- The payload of a Signal type `Signal dom α`, as a label. -/
def payloadOf (ty : Lean.Expr) : String :=
  match ty.getAppArgs.back? with
  | some p =>
    if p.getAppFn.isConstOf ``BitVec then "BitVec"
    else if p.isConstOf ``Bool then "Bool"
    else headOf p
  | none => "?"

/-- The binders of a telescope, by kind. -/
def binderKey (xs : Array Lean.Expr) : MetaM String := do
  let mut sc : Nat := 0
  let mut st : Nat := 0
  let mut dm : Nat := 0
  let mut ot : Nat := 0
  for x in xs do
    let ty ← inferType x
    if ty.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal then
      let p := payloadOf ty
      if p == "BitVec" || p == "Bool" then sc := sc + 1 else st := st + 1
    else if ty.isConstOf ``Sparkle.Core.Domain.DomainConfig then dm := dm + 1
    else ot := ot + 1
  return s!"{xs.size} binders = {sc} scalar Signal + {st} structured Signal + {dm} domain + {ot} other"

/-- What pass 1 records of a legacy-route declaration. -/
structure Info where
  name : Name
  head : String
  kind : String
  binders : String
  payload : String
  betaHead : String

/-- The first line of a message, at most sixty characters. -/
def prefixOf (msg : String) : String :=
  let line := (msg.splitOn "\n").headD ""
  String.join ((line.toList.take 60).map fun c => c.toString)

/-- ONE run of the shipping entry on `n`, isolated and bounded. -/
def runEntry (n : Name) : MetaM String := do
  let saved ← Meta.saveState
  sparkleSynthDepth.set 0
  -- the translator's call counter is never reset by the entry; its limit is
  -- per process, so it is reset here between declarations
  sparkleCallCounter.set 0
  let r ← tryCatchRuntimeEx
    (do
      let _ ← withTheReader Core.Context
        (fun c => { c with maxHeartbeats := runHeartbeats * 1000 }) <|
        withCurrHeartbeats <| synthesizeCombinationalCore n [] false
      pure "RETURNED")
    (fun ex => do
      if ex.isMaxHeartbeat then pure "TIMEOUT"
      else if ex.isRuntime then pure "RUNTIME"
      else
        let msg ← ex.toMessageData.toString
        pure ("THREW: " ++ prefixOf msg))
  saved.restore
  sparkleSynthDepth.set 0
  pure r

/-- The binder types and the body of nested lambdas (loose bound variables,
as in the constant's value). -/
def lamParts : Lean.Expr → List Lean.Expr × Lean.Expr
  | .lam _ T b _ =>
    let r := lamParts b
    (T :: r.1, r.2)
  | e => ([], e)

/-- The hardware-type oracle on a type; `none` when it throws. -/
def hwOf? (T : Lean.Expr) : MetaM (Option Sparkle.IR.Type.HWType) := do
  let cache ← IO.mkRef ({} : ExprStructMap String)
  try
    let (h, _) ←
      ((inferHWTypeFromSignal T).run (entryCompilerState false cache)).run
        (Sparkle.IR.Builder.CircuitM.init "evidence")
    pure (some h)
  catch _ => pure none

/-- The kind of a binder as `proj_entry_output` needs it, from the oracle's
outcome on its declared type; or the failing observation. -/
def binderKindOf (nm : Name) (isDom : Bool) (payload : String)
    (hw : Option Sparkle.IR.Type.HWType) : Except String String :=
  match hw with
  | none =>
    if isDom then .ok "domain"
    else .error s!"the type oracle throws on the non-domain binder {nm}"
  | some h =>
    if isDom then .error s!"the type oracle returns on the domain binder {nm}"
    else
      match h with
      | .bit =>
        if payload == "Bool" then .ok "bool"
        else if payload == "BitVec" then
          .error s!"width-one BitVec field {nm} (the oracle gives bit)"
        else .error s!"bit port for the binder {nm} of payload {payload}"
      | .bitVector w =>
        if w == 1 then .error s!"bitVector 1 for the binder {nm}"
        else if payload == "BitVec" then .ok s!"bits {w}"
        else .error s!"bitVector {w} port for the binder {nm} of payload {payload}"
      | _ => .error s!"another hardware type for the binder {nm}"

/-- The observable premises of `proj_entry_output` on the declaration `n`:
`(true, binders | index | kind)` when all hold, `(false, the first failing
observation)` otherwise. -/
def projCheckCore (n : Name) : MetaM (Bool × String) := do
  let env ← getEnv
  let ci ← getConstInfo n
  let ec := entryConst true false [] ci (instancePredicate env) (userInliner env)
    (structEnv env)
  let gatesDecline : Bool :=
    (certifiedShape? false [] ec).isNone &&
      (mixedCertifiedShape? false [] ec (instancePredicate env)).isNone &&
      (machineShape? false [] ec (structEnv env)).isNone
  if !gatesDecline then
    return (false, "a gate accepts the entry's constant")
  let body0 ← openRecordInputs ec.value!
  let body := stripMemoizeWrappers body0
  let parts := lamParts body
  let tys : List Lean.Expr := parts.1
  let rawLeaf : Lean.Expr := parts.2
  lambdaTelescope body fun xs inner => do
    if xs.size != tys.length then
      return (false, s!"{tys.length} nested lambdas but {xs.size} telescope variables")
    -- the declared types and the leaf, as the premise `hbody` states them
    let mut pre : Array Lean.Expr := #[]
    let mut rawOk : Bool := true
    for T in tys do
      let x := xs[pre.size]!
      let d ← x.fvarId!.getDecl
      if !(T.instantiateRevRange 0 pre.size pre == d.type) then
        rawOk := false
      pre := pre.push x
    if !(rawLeaf.instantiateRevRange 0 xs.size xs == inner) then
      rawOk := false
    if !rawOk then
      return (false, "a declared type or the leaf differs from its instantiateRevRange form")
    if xs.toList.eraseDups.length != xs.size then
      return (false, "the telescope's variables are not distinct")
    if !(inner.isApp && inner.getAppFn.isLambda) then
      return (false, s!"the leaf is not a lambda-headed application (head {headOf inner})")
    if kindOf inner != "other" then
      return (false, s!"the leaf's fallbackKind is {kindOf inner}")
    let wh ← withTransparency TransparencyMode.reducible (whnf inner)
    let mut idx : Option Nat := none
    let mut j : Nat := 0
    for x in xs do
      if x == wh then
        idx := some j
      j := j + 1
    let some i := idx
      | return (false, s!"the leaf's reducible whnf is not one of the variables (its head: {headOf wh})")
    -- the type oracle on every declared type
    let mut fieldKind : String := "?"
    let mut pos : Nat := 0
    let mut bad : Option String := none
    for x in xs do
      let ty ← inferType x
      let d ← x.fvarId!.getDecl
      let hw ← hwOf? ty
      match binderKindOf d.userName (ty.isConstOf ``Sparkle.Core.Domain.DomainConfig)
          (payloadOf ty) hw with
      | .ok kd =>
        if pos == i then
          fieldKind := kd
      | .error msg =>
        if bad.isNone then
          bad := some msg
      pos := pos + 1
    if let some msg := bad then
      return (false, msg)
    if fieldKind == "domain" then
      return (false, "the leaf reduces to the domain variable")
    let ty ← inferType inner
    let tyN ← whnf ty
    if !(tyN.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal) then
      return (false, "the whnf of the leaf's inferred type is not Signal-headed")
    return (true, s!"{xs.size} binders | index {i} | {fieldKind}")

/-- `projCheckCore`, isolated; an exception is a failing observation. -/
def projCheck (n : Name) : MetaM (Bool × String) := do
  let saved ← Meta.saveState
  let r ← tryCatchRuntimeEx (projCheckCore n)
    (fun ex => do
      let msg ← ex.toMessageData.toString
      pure (false, "harness error: " ++ prefixOf msg))
  saved.restore
  pure r

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let env ← getEnv
    let roots : List Name := [`IP, `Examples, `Tests]
    -- candidates: imported definitions of those modules with a Signal result
    let all : Array Name := env.constants.fold (fun acc n ci =>
      match ci with
      | .defnInfo _ =>
        let root : Option Name :=
          (env.getModuleIdxFor? n).bind fun idx =>
            (env.header.moduleNames[idx.toNat]?).map (·.getRoot)
        let inRoots : Bool := match root with
          | some r => roots.contains r
          | none => false
        if inRoots && !n.isInternal &&
            ci.type.getForallBody.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal then
          acc.push n
        else acc
      | _ => acc) #[]
    let sorted := all.qsort (fun a b => decide (a.toString < b.toString))
    let cands := sorted.extract 0 cap
    let mut routes : Std.HashMap String (Nat × String) := {}
    let mut heads : Std.HashMap String (Nat × String) := {}
    let mut kinds : Std.HashMap String (Nat × String) := {}
    let mut otherHeads : Std.HashMap String (Nat × String) := {}
    let mut maps : Std.HashMap String (Nat × String) := {}
    let mut errors : Nat := 0
    let mut legacy : Array Info := #[]
    -- pass 1
    for n in cands do
      try
        let ci ← getConstInfo n
        let ec := entryConst true false [] ci (instancePredicate env) (userInliner env)
          (structEnv env)
        let route : String :=
          if (certifiedShape? false [] ec).isSome then "certified"
          else if (mixedCertifiedShape? false [] ec (instancePredicate env)).isSome then "mixed"
          else if (machineShape? false [] ec (structEnv env)).isSome then "machine"
          else "legacy"
        routes := bump routes route n.toString
        if route == "legacy" then
          let body0 ← openRecordInputs ec.value!
          let body := stripMemoizeWrappers body0
          let (hd, kd, mb, bk, bh) ← lambdaTelescope body fun xs inner => do
            let bk ← binderKey xs
            pure (headOf inner, kindOf inner, mapBodyOf inner, bk, headOf inner.headBeta)
          heads := bump heads hd n.toString
          kinds := bump kinds kd n.toString
          if kd == "other" then
            otherHeads := bump otherHeads hd n.toString
          if hd == (``Sparkle.Core.Signal.Signal.map : Name).toString ||
              hd == (``Functor.map : Name).toString then
            match mb with
            | some b => maps := bump maps b n.toString
            | none => pure ()
          legacy := legacy.push
            { name := n, head := hd, kind := kd, binders := bk,
              payload := payloadOf ci.type.getForallBody, betaHead := bh }
      catch _ =>
        errors := errors + 1
    logInfo m!"LEGACY ARM CENSUS: {all.size} Signal-valued definitions in the imported IP / Examples / Tests modules, {cands.size} examined (cap {cap}), {errors} errors. ROUTES: {render routes}"
    logInfo m!"LEGACY ARM CENSUS, top leaf of the legacy-route declarations, by fallbackKind: {render kinds}"
    logInfo m!"LEGACY ARM CENSUS, top leaf of the legacy-route declarations, by head: {render heads}"
    logInfo m!"LEGACY ARM CENSUS, legacy-route leaves of fallbackKind other, by head: {render otherHeads}"
    logInfo m!"LEGACY ARM CENSUS, map leaves, by the head of the mapped function's body: {render maps}"
    -- pass 2: the real entry on every legacy-route candidate
    let t0 ← IO.monoMsNow
    let mut outcomes : Std.HashMap String (Nat × String) := {}
    let mut thrown : Std.HashMap String (Nat × String) := {}
    let mut rHeads : Std.HashMap String (Nat × String) := {}
    let mut rKinds : Std.HashMap String (Nat × String) := {}
    let mut rBinders : Std.HashMap String (Nat × String) := {}
    let mut rPayloads : Std.HashMap String (Nat × String) := {}
    let mut rBeta : Std.HashMap String (Nat × String) := {}
    let mut rClasses : Std.HashMap String (Nat × String) := {}
    let mut tHeads : Std.HashMap String (Nat × String) := {}
    let mut projNames : Array Name := #[]
    for i in legacy do
      let now ← IO.monoMsNow
      if now - t0 > runBudgetMs then
        outcomes := bump outcomes "NOT RUN (time budget)" i.name.toString
      else
        let r ← try runEntry i.name catch _ => pure "HARNESS ERROR"
        if r == "RETURNED" then
          outcomes := bump outcomes "RETURNED" i.name.toString
          rHeads := bump rHeads i.head i.name.toString
          rKinds := bump rKinds i.kind i.name.toString
          rBinders := bump rBinders i.binders i.name.toString
          rPayloads := bump rPayloads i.payload i.name.toString
          if i.head == "<lambda>" then
            rBeta := bump rBeta i.betaHead i.name.toString
            projNames := projNames.push i.name
          rClasses := bump rClasses s!"{i.head} | {i.binders} | result {i.payload}"
            i.name.toString
        else if r == "TIMEOUT" || r == "RUNTIME" || r == "HARNESS ERROR" then
          outcomes := bump outcomes r i.name.toString
        else
          outcomes := bump outcomes "THREW" i.name.toString
          thrown := bump thrown r i.name.toString
          tHeads := bump tHeads i.head i.name.toString
    let t1 ← IO.monoMsNow
    logInfo m!"LEGACY ENTRY RUNS: the shipping entry (synthesizeCombinationalCore, certified front end on) on the {legacy.size} legacy-route candidates, {t1 - t0} ms, heartbeat bound {runHeartbeats} per declaration. OUTCOMES: {render outcomes}"
    logInfo m!"LEGACY ENTRY RUNS, THREW by first line of the message: {render thrown}"
    logInfo m!"LEGACY ENTRY RUNS, THREW by the leaf's head: {render tHeads}"
    logInfo m!"LEGACY ENTRY RUNS, RETURNED by the leaf's head: {render rHeads}"
    logInfo m!"LEGACY ENTRY RUNS, RETURNED by fallbackKind: {render rKinds}"
    logInfo m!"LEGACY ENTRY RUNS, RETURNED by binders: {render rBinders}"
    logInfo m!"LEGACY ENTRY RUNS, RETURNED by the result type's payload: {render rPayloads}"
    logInfo m!"LEGACY ENTRY RUNS, RETURNED with a <lambda> head, by the head after headBeta: {render rBeta}"
    logInfo m!"LEGACY ENTRY RUNS, RETURNED by class (head | binders | result payload): {render rClasses}"
    -- pass 3: the observable premises of `proj_entry_output` on the projections
    let mut fitN : Nat := 0
    let mut fitTable : Std.HashMap String (Nat × String) := {}
    let mut misfits : Array String := #[]
    for n in projNames do
      let r ← projCheck n
      if r.1 then
        fitN := fitN + 1
        fitTable := bump fitTable r.2 n.toString
      else
        misfits := misfits.push s!"{n}: {r.2}"
    logInfo m!"PROJ CLASS: fits {fitN} of {projNames.size} (the RETURNED declarations with a <lambda> head; observable premises of proj_entry_output: gates decline, nested lambdas = telescope variables, declared types and leaf in instantiateRevRange form, distinct variables, lambda-headed application of kind other, reducible whnf = the variable at an index, type oracle throws exactly on the domain binder and gives bit on Bool / bitVector n (n ≠ 1) on BitVec, Signal-headed result)"
    logInfo m!"PROJ CLASS, fitting, by binders | index of the field's variable | kind: {render fitTable}"
    let misText : String := String.intercalate "; " misfits.toList
    logInfo m!"PROJ CLASS, NOT fitting ({misfits.size}), declaration and first failing observation: {misText}"
  catch ex =>
    logInfo m!"LEGACY ARM CENSUS: harness error: {ex.toMessageData}"

/-! ## Evidence for the premises of `SHA256Out_done_output`
(`Tests/Compiler/LegacySemInstanceTest.lean`) on the REAL constant (logs
only; one run in this environment — an observation, not a proof) -/

/-- The hardware-type oracle on a type, as a label. -/
def hwOf (T : Lean.Expr) : MetaM String := do
  let cache ← IO.mkRef ({} : ExprStructMap String)
  try
    let (h, _) ←
      ((inferHWTypeFromSignal T).run (entryCompilerState false cache)).run
        (Sparkle.IR.Builder.CircuitM.init "evidence")
    pure (match h with
      | .bit => "bit"
      | .bitVector n => s!"bitVector {n}"
      | _ => "another hardware type")
  catch ex => do
    let msg ← ex.toMessageData.toString
    pure ("THREW (" ++ prefixOf msg ++ ")")

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let env ← getEnv
    let n : Name := ``Sparkle.IP.Crypto.SHA256.SHA256Out.done
    let ci ← getConstInfo n
    let ec := entryConst true false [] ci (instancePredicate env) (userInliner env)
      (structEnv env)
    let gatesDecline : Bool :=
      (certifiedShape? false [] ec).isNone &&
        (mixedCertifiedShape? false [] ec (instancePredicate env)).isNone &&
        (machineShape? false [] ec (structEnv env)).isNone
    let body0 ← openRecordInputs ec.value!
    let body := stripMemoizeWrappers body0
    let shape : String :=
      match body with
      | .lam n1 _ (.lam n2 _ (.lam n3 _ b _) _) _ =>
        s!"three nested lambdas, binder names {n1}, {n2}, {n3}, the inner body is a lambda: {b.isLambda}"
      | _ => "NOT three nested lambdas"
    lambdaTelescope body fun xs inner => do
      let x1 := xs[0]!
      let x2 := xs[1]!
      let x3 := xs[2]!
      let d1 ← x1.fvarId!.getDecl
      let d2 ← x2.fvarId!.getDecl
      let d3 ← x3.fvarId!.getDecl
      let a1 : Array Lean.Expr := (#[] : Array Lean.Expr).push x1
      let a2 : Array Lean.Expr := a1.push x2
      let a3 : Array Lean.Expr := #[x1, x2, x3]
      let rawOk : Bool :=
        match body with
        | .lam _ T1 (.lam _ T2 (.lam _ T3 b _) _) _ =>
          T1.instantiateRevRange 0 (#[] : Array Lean.Expr).size #[] == d1.type &&
            T2.instantiateRevRange 0 a1.size a1 == d2.type &&
            T3.instantiateRevRange 0 a2.size a2 == d3.type &&
            b.instantiateRevRange 0 a3.size a3 == inner
        | _ => false
      let namesOk : Bool :=
        d1.userName == `dom && d2.userName == `hash && d3.userName == `done
      let wh ← withTransparency TransparencyMode.reducible (whnf inner)
      let whOk : Bool := xs.size == 3 && wh == x3
      let hw1 ← hwOf d1.type
      let hw2 ← hwOf d2.type
      let hw3 ← hwOf d3.type
      let ty ← inferType inner
      let tyN ← whnf ty
      let headOk : Bool := tyN.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal
      logInfo m!"LEGACY ENTRY, PROJECTION EVIDENCE for {n}: the three gates decline on the entry's constant: {gatesDecline}; the stripped value is {shape}; the three declared types and the leaf equal the premise's instantiateRevRange results: {rawOk}; the declared user names are dom, hash, done: {namesOk}. LEAF: is an application: {inner.isApp}, its head is a lambda: {inner.getAppFn.isLambda}, fallbackKind: {kindOf inner}; its reducible whnf is the third variable: {whOk} (the whnf returned: {wh}). ORACLES: inferHWTypeFromSignal on the three declared types: {hw1} | {hw2} | {hw3} (expected: THREW | bitVector 256 | bit); the whnf of the leaf's inferred type is headed by Signal: {headOk}"
  catch ex =>
    logInfo m!"LEGACY ENTRY, PROJECTION EVIDENCE: harness error: {ex.toMessageData}"

end Sparkle.Tests.Compiler.LegacyArmCensusTest
