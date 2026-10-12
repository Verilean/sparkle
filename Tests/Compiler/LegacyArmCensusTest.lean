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
