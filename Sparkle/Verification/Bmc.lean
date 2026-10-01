/-
  Bounded model checking and k-induction over the SMT bridge
  (`Sparkle.Backend.Smt`), with counterexample rendering.

  A property is a module whose `assertions` must be 1 in every cycle.
  `checkBmc` searches cycles 0..k from the reset state; `checkInduction`
  adds the inductive step, which turns a bounded result into "holds in
  every reachable cycle".  A violation comes back as a trace (every
  signal, every cycle) that can be printed as a table or written as a
  VCD waveform.

  The solver is z3 (`SPARKLE_Z3`, or `z3` on PATH), run as a separate
  process; see docs/SmtBridge-design.md for the trust story.
-/
import Sparkle.Backend.Smt

namespace Sparkle.Verification.Bmc

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.Smt

/-- Per cycle, the value of each signal (by model name). -/
abbrev Trace := Array (List (String × Nat))

inductive Verdict where
  /-- No assertion fails in cycles 0..k from reset (bounded). -/
  | holds (k : Nat)
  /-- k-induction succeeded: no assertion fails in any reachable cycle. -/
  | proved (k : Nat)
  /-- An assertion fails at `cycle`; the trace starts at reset. -/
  | violated (cycle : Nat) (assertion : String) (trace : Trace)
  /-- No violation within k-1 cycles of reset, but the inductive step
      fails: `trace` starts in an ARBITRARY state (possibly unreachable),
      satisfies the assertions for k cycles and breaks one in the last. -/
  | notInductive (k : Nat) (assertion : String) (trace : Trace)
  | unknown (why : String)
  /-- No solver available; the query was only written to `queryPath`. -/
  | noSolver (queryPath : String)

def findZ3 : IO (Option String) := do
  match ← IO.getEnv "SPARKLE_Z3" with
  | some p => return some p
  | none =>
    let r ← IO.Process.output { cmd := "which", args := #["z3"] }
    return if r.exitCode == 0 then some r.stdout.trim else none

def queryDir : String := ".lake/build/gen/smt"

/-- Write `query` to `<queryDir>/<tag>.smt2` and run z3 on it.
    `none` = no solver. -/
def runQuery (tag query : String) (k : Nat) :
    IO (String × Option (Except String BmcOutcome)) := do
  IO.FS.createDirAll queryDir
  let path := s!"{queryDir}/{tag}.smt2"
  IO.FS.writeFile path query
  let some z3 ← findZ3 | return (path, none)
  let r ← IO.Process.output { cmd := z3, args := #["-smt2", path] }
  return (path, some (parseZ3Output r.stdout k))

/-- First failing assertion of a trace: `(cycle, assertionName)`. -/
def firstViolation (m : Module) (trace : Trace) : Option (Nat × String) :=
  (List.range trace.size).findSome? fun c =>
    m.assertions.findSome? fun (aname, _) =>
      match trace[c]!.find? (·.1 == modelName s!"_assert_{aname}") with
      | some (_, 0) => some (c, aname)
      | _ => none

/-- Bounded model checking of `m.assertions` for cycles 0..k. -/
def checkBmc (m : Module) (k : Nat) (tag : String := m.name) : IO Verdict := do
  match toSmtBmcQuery m k (traceAll := true) with
  | .error e => return .unknown e
  | .ok q =>
    match ← runQuery s!"{tag}.bmc" q k with
    | (path, none) => return .noSolver path
    | (_, some (.error e)) => return .unknown e
    | (_, some (.ok .unknown)) => return .unknown "the solver answered `unknown`"
    | (_, some (.ok .unsat)) => return .holds k
    | (_, some (.ok (.sat trace))) =>
      match firstViolation m trace with
      | none => return .unknown "the solver reported a violation but the model shows none"
      | some (c, a) =>
        -- The solver's model need not be the earliest violation.  Re-ask
        -- with the bound just below the current one until nothing is
        -- found: the result is a SHORTEST counterexample.
        let mut best := (c, a, trace)
        let mut searching := true
        while searching && best.1 > 0 do
          let bound := best.1 - 1
          match toSmtBmcQuery m bound (traceAll := true) with
          | .error _ => searching := false
          | .ok q' =>
            match ← runQuery s!"{tag}.bmc" q' bound with
            | (_, some (.ok (.sat t'))) =>
              match firstViolation m t' with
              | some (c', a') => best := (c', a', t')
              | none => searching := false
            | _ => searching := false
        let (c, a, trace) := best
        return .violated c a (trace.extract 0 (c + 1))

/-- k-induction (k ≥ 1): base case = BMC for cycles 0..k-1, then the
    inductive step. -/
def checkInduction (m : Module) (k : Nat) (tag : String := m.name) : IO Verdict := do
  if k == 0 then return .unknown "k-induction needs k ≥ 1"
  match ← checkBmc m (k - 1) tag with
  | .holds _ =>
    match toSmtInductionQuery m k with
    | .error e => return .unknown e
    | .ok q =>
      match ← runQuery s!"{tag}.step" q k with
      | (path, none) => return .noSolver path
      | (_, some (.error e)) => return .unknown e
      | (_, some (.ok .unknown)) => return .unknown "the solver answered `unknown`"
      | (_, some (.ok .unsat)) => return .proved k
      | (_, some (.ok (.sat trace))) =>
        let a := (firstViolation m trace).map (·.2) |>.getD "?"
        return .notInductive k a trace
  | other => return other

/-! ### Rendering -/

private def hex (v : Nat) : String := String.ofList (Nat.toDigits 16 v)

/-- Signals worth showing in a text trace: inputs, registers, outputs and
    user-named wires — not `clk`, and not compiler temporaries. -/
def displaySignals (m : Module) : List (String × String) :=
  let regs := m.body.filterMap fun s => match s with
    | .register out .. => some out | _ => none
  let outs := m.outputs.map (·.name)
  let ins := (bmcInputs m).map (·.name)
  (traceSignals m).filterMap fun (n, _) =>
    if ins.contains n then some (n, "in")
    else if outs.contains n then some (n, "out")
    else if regs.contains n then some (n, "reg")
    else if n.startsWith "_tmp_" then none
    -- `_gen_out` is the wire behind the output `out`: one row is enough
    else if n.startsWith "_gen_" && outs.contains (n.drop 5).toString then none
    else some (n, "")

/-- A table: one row per signal, one column per cycle, values in hex. -/
def renderTrace (m : Module) (trace : Trace) : String :=
  let rows := (displaySignals m).map fun (n, kind) =>
    -- the elaborator prefixes user names with `_gen_`
    let shown := if n.startsWith "_gen_" then (n.drop 5).toString else n
    let label := if kind == "" then shown else s!"{shown} ({kind})"
    let vals := trace.toList.map fun frame =>
      match frame.find? (·.1 == modelName n) with
      | some (_, v) => hex v
      | none => "-"
    (label, vals)
  let header := ("cycle", (List.range trace.size).map toString)
  let all := header :: rows
  let labelW := all.foldl (fun w (l, _) => max w l.length) 0
  let colW := all.foldl (fun w (_, vs) => vs.foldl (fun w v => max w v.length) w) 1
  let pad := fun (s : String) (w : Nat) => s ++ String.ofList (List.replicate (w - s.length) ' ')
  let lpad := fun (s : String) (w : Nat) => String.ofList (List.replicate (w - s.length) ' ') ++ s
  String.intercalate "\n" (all.map fun (l, vs) =>
    "  " ++ pad l labelW ++ "  " ++ String.intercalate " " (vs.map (lpad · colW)))

private def vcdId (i : Nat) : String := Id.run do
  let mut n := i
  let mut cs : List Char := []
  repeat
    cs := Char.ofNat (33 + n % 94) :: cs
    n := n / 94
    if n == 0 then break
  return String.ofList cs

private def vcdValue (w v : Nat) (id : String) : String :=
  if w ≤ 1 then s!"{v % 2}{id}"
  else
    let bits := (List.range w).reverse.map fun i => if (v >>> i) % 2 == 1 then '1' else '0'
    s!"b{String.ofList bits} {id}"

/-- The trace as a VCD waveform: every trace signal plus a synthetic
    `clk` (10 time units per cycle, values sampled at the rising edge). -/
def toVcd (m : Module) (trace : Trace) : String := Id.run do
  let sigs := (traceSignals m).filter (·.1 != "clk")
  let ids := (List.range sigs.length).map fun i => vcdId (i + 1)
  let clkId := vcdId 0
  let mut lines : List String :=
    [ "$date Sparkle HDL counterexample $end", "$timescale 1ns $end"
    , s!"$scope module {modelName m.name} $end", s!"$var wire 1 {clkId} clk $end" ]
  for ((n, w), id) in sigs.zip ids do
    lines := lines ++ [s!"$var wire {max w 1} {id} {n} $end"]
  lines := lines ++ ["$upscope $end", "$enddefinitions $end"]
  let mut prev : List (Option Nat) := sigs.map fun _ => none
  for c in [0:trace.size] do
    lines := lines ++ [s!"#{10 * c}", s!"1{clkId}"]
    let mut next : List (Option Nat) := []
    for (((n, w), id), old) in (sigs.zip ids).zip prev do
      let v := (trace[c]!.find? (·.1 == modelName n)).map (·.2) |>.getD (old.getD 0)
      if old != some v then lines := lines ++ [vcdValue w v id]
      next := next ++ [some v]
    prev := next
    lines := lines ++ [s!"#{10 * c + 5}", s!"0{clkId}"]
  lines := lines ++ [s!"#{10 * trace.size}"]
  return String.intercalate "\n" lines ++ "\n"

/-- Write the trace next to the queries; returns the path. -/
def writeVcd (m : Module) (trace : Trace) (tag : String := m.name) : IO String := do
  IO.FS.createDirAll queryDir
  let path := s!"{queryDir}/{tag}.cex.vcd"
  IO.FS.writeFile path (toVcd m trace)
  return path

end Sparkle.Verification.Bmc
