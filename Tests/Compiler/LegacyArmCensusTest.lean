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

Purpose (G2, round 19): choose the next arm of the fallback to walk from a
MEASUREMENT instead of a guess.

**What is measured.** Over the definitions of the imported `IP` / `Examples`
/ `Tests` modules whose result type is syntactically a `Signal` (after the
binders), in name order, at most `cap` of them:

1. the ROUTE the shipping entry gives the declaration, from the entry's own
   pure gates on the entry's own constant
   (`entryConst true false [] ci …`, then `certifiedShape?`,
   `mixedCertifiedShape?`, `machineShape?`): `certified` / `mixed` /
   `machine` / `legacy`;
2. for the `legacy` ones, the TOP LEAF: the body after `openRecordInputs`,
   `stripMemoizeWrappers` and `lambdaTelescope` (the entry's own steps), and
   of it
   * the head (a constant's name, or `<fvar>` / `<lambda>` / `<let>` / …),
   * `fallbackKind` (the arm `translateFallback` dispatches to),
   * for a `Signal.map` / `Functor.map` head: the head of the mapped
     function's body.

**What is NOT measured.** Which handler ACCEPTS the leaf at run time: that
needs instrumenting the translator (a compiler file). The classification is
syntactic, on the expression the translator is handed; `fallbackKind` is the
compiler's own function, so that column is exact; the head tells which
name-guarded arm or handler the body's chain will stop at. Sub-expressions
of the leaf are not counted: only the top node of each declaration.

**Limits.** Only the listed imports are in the environment (eight `IP`
modules already imported by other tests, and whatever they import);
structure- and product-valued declarations are skipped (their leaves need
`splitReturnLeaves`); `cap` bounds the work. One run in this environment:
an observation.

The whole block is inside `try … catch`, and each declaration in its own;
the heartbeat limit is lifted (a heartbeat exception is not catchable). -/

open Lean Meta Sparkle.Compiler.Elab

namespace Sparkle.Tests.Compiler.LegacyArmCensusTest

/-- At most this many candidate declarations are examined. -/
def cap : Nat := 400

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
          let (hd, kd, mb) ← lambdaTelescope body fun _ inner =>
            pure (headOf inner, kindOf inner, mapBodyOf inner)
          heads := bump heads hd n.toString
          kinds := bump kinds kd n.toString
          if kd == "other" then
            otherHeads := bump otherHeads hd n.toString
          if hd == (``Sparkle.Core.Signal.Signal.map : Name).toString ||
              hd == (``Functor.map : Name).toString then
            match mb with
            | some b => maps := bump maps b n.toString
            | none => pure ()
      catch _ =>
        errors := errors + 1
    logInfo m!"LEGACY ARM CENSUS: {all.size} Signal-valued definitions in the imported IP / Examples / Tests modules, {cands.size} examined (cap {cap}), {errors} errors. ROUTES: {render routes}"
    logInfo m!"LEGACY ARM CENSUS, top leaf of the legacy-route declarations, by fallbackKind: {render kinds}"
    logInfo m!"LEGACY ARM CENSUS, top leaf of the legacy-route declarations, by head: {render heads}"
    logInfo m!"LEGACY ARM CENSUS, legacy-route leaves of fallbackKind other, by head: {render otherHeads}"
    logInfo m!"LEGACY ARM CENSUS, map leaves, by the head of the mapped function's body: {render maps}"
  catch ex =>
    logInfo m!"LEGACY ARM CENSUS: harness error: {ex.toMessageData}"

end Sparkle.Tests.Compiler.LegacyArmCensusTest
