import Sparkle.Backend.Smt
import Sparkle.Verification.Bmc
import Tests.TestSmt

/-  SMT bridge Layer 2: run the real solver, then close the trust loop.

    For every fixture the query is EMITTED unconditionally (a generation
    regression fails even without a solver).  If `z3` is present (PATH, or
    `SPARKLE_Z3=/path/to/z3`), each query runs and the outcome is compared
    against the expectation; every `sat` outcome's counterexample is then
    REPLAYED on the CSim C reference (gcc): the assertion — exported as an
    extra output port so it is a struct field — must actually read 0 at some
    cycle ≤ k.  A counterexample that fails replay means a solver bug or an
    emitter bug; either way the test fails.  Without z3 the run half skips
    cleanly. -/

open Sparkle.Backend.Smt
open Sparkle.Backend.CSim
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Test.Smt

/-- Generated C main: memset + reset, then per cycle poke the
    counterexample's inputs (missing = 0), eval, check every `_assert_*`
    output field, tick.  Exit 0 iff some assertion read 0 at a cycle ≤ k. -/
def emitReplayC (m : Module) (k : Nat) (cex : Array (List (String × Nat))) :
    Except String String := do
  let m' := withAssertOutputs m
  let cls := sanitizeName m.name
  let mut lines : List String := [
    toC m',
    "#include <stdio.h>",
    "int main(void) {",
    s!"  struct {cls} s;",
    "  memset(&s, 0, sizeof s);",
    s!"  sparkle_{cls}_reset(&s);",
    "  int found = 0;" ]
  for c in [0:k+1] do
    lines := lines ++ [s!"  // cycle {c}"]
    for p in bmcInputs m do
      let v := ((cex.getD c []).find? (·.1 == sanitizeName p.name)).map (·.2) |>.getD 0
      let field := sanitizeName p.name
      match p.ty with
      | .bit =>
        lines := lines ++ [s!"  s.{field} = {v}ULL;"]
      | .bitVector width =>
        if width ≤ 64 then
          lines := lines ++ [s!"  s.{field} = {v}ULL;"]
        else
          let wordCount := (width + 31) / 32
          for wordIndex in List.range wordCount do
            let word := (v / (2 ^ (32 * wordIndex))) % (2 ^ 32)
            lines := lines ++ [s!"  s.{field}[{wordIndex}] = {word}U;"]
      | _ =>
        throw s!"replay supports only concrete packed bit-vector inputs ('{p.name}')"
    lines := lines ++ [s!"  sparkle_{cls}_eval(&s);"]
    for (aname, _) in m.assertions do
      lines := lines ++
        [s!"  if (s._assert_{sanitizeName aname} == 0) \{ printf(\"VIOLATION cycle={c} assert={aname}\\n\"); found = 1; }"]
    lines := lines ++ [s!"  sparkle_{cls}_tick(&s);"]
  lines := lines ++ [
    "  if (!found) printf(\"NOT-REPRODUCED\\n\");",
    "  return found ? 0 : 1;",
    "}" ]
  return String.intercalate "\n" lines

def findExe (name : String) (envOverride : String) : IO (Option String) := do
  match ← IO.getEnv envOverride with
  | some p => return some p
  | none =>
    let r ← IO.Process.output { cmd := "which", args := #[name] }
    return if r.exitCode == 0 then some (r.stdout.trim) else none

inductive Expect where | unsat | sat
  deriving BEq

def main : IO Unit := do
  let dir := ".lake/build/gen/smt"
  IO.FS.createDirAll dir

  let cases : List (String × Module × Nat × Expect) :=
    [ ("good-counter",  goodCounter,  20, .unsat)
    , ("buggy-counter", buggyCounter, 14, .sat)
    , ("mem-good",      memGood,      10, .unsat)
    , ("mem-buggy",     memBuggy,      8, .sat) ]

  let parameterizedCases :
      List (String × Module × Sparkle.IR.Specialize.Bindings × Nat × Expect) :=
    [ ("param-zero-w3", parameterizedZeroAssertion, [("W", 3)], 0, .sat)
    , ("param-zero-w17", parameterizedZeroAssertion, [("W", 17)], 0, .sat)
    , ("param-zero-w65", parameterizedZeroAssertion, [("W", 65)], 0, .sat)
    , ("param-derived-w65", parameterizedDerivedSlice, [("W", 65)], 0, .unsat) ]

  -- Layer 2a: always emit (generation regressions fail without a solver).
  let mut queries : List (String × Module × Nat × Expect × String) := []
  for (name, m, k, expect) in cases do
    match toSmtBmcQuery m k with
    | .error e => IO.eprintln s!"[smt] emit error ({name}): {e}"; IO.Process.exit 1
    | .ok q =>
      let path := s!"{dir}/{name}.smt2"
      IO.FS.writeFile path q
      IO.println s!"[smt] emitted {path} ({q.length} chars)"
      queries := queries ++ [(name, m, k, expect, path)]

  for (name, symbolic, bindings, k, expect) in parameterizedCases do
    match Sparkle.IR.Specialize.specializeModule symbolic bindings with
    | .error e =>
      IO.eprintln s!"[smt] specialization error ({name}): {e}"
      IO.Process.exit 1
    | .ok concrete =>
      match toSmtBmcQueryWithParameters symbolic bindings k with
      | .error e =>
        IO.eprintln s!"[smt] parameterized emit error ({name}): {e}"
        IO.Process.exit 1
      | .ok q =>
        let path := s!"{dir}/{name}.smt2"
        IO.FS.writeFile path q
        IO.println s!"[smt] emitted {path} ({q.length} chars)"
        queries := queries ++ [(name, concrete, k, expect, path)]

  -- Layer 2b: run z3 if present.
  let some z3 ← findExe "z3" "SPARKLE_Z3"
    | IO.println "[smt] z3 not found (set SPARKLE_Z3 or add z3 to PATH) — emit-only\n\nALL PASS (emit-only)"
  let some cc ← findExe "gcc" "SPARKLE_CC"
    | IO.println "[smt] no C compiler for replay — emit-only\n\nALL PASS (emit-only)"

  for (name, m, k, expect, path) in queries do
    let r ← IO.Process.output { cmd := z3, args := #["-smt2", path] }
    match parseZ3Output r.stdout k with
    | .error e =>
      IO.eprintln s!"[smt] {name}: cannot parse z3 output: {e}\n{r.stdout.take 300}"
      IO.Process.exit 1
    | .ok .unknown =>
      IO.eprintln s!"[smt] {name}: solver returned unknown"; IO.Process.exit 1
    | .ok .unsat =>
      if expect == .unsat then
        IO.println s!"[smt] {name}: unsat (property holds up to k={k}) ✓"
      else
        IO.eprintln s!"[smt] {name}: expected sat, got unsat"; IO.Process.exit 1
    | .ok (.sat cex) =>
      if expect == .unsat then
        IO.eprintln s!"[smt] {name}: expected unsat, got sat"; IO.Process.exit 1
      -- close the trust loop: replay the counterexample on CSim
      match emitReplayC m k cex with
      | .error e => IO.eprintln s!"[smt] {name}: replay gen error: {e}"; IO.Process.exit 1
      | .ok csrc =>
        let cpath := s!"{dir}/{name}_replay.c"
        let bin := s!"{dir}/{name}_replay"
        IO.FS.writeFile cpath csrc
        let cr ← IO.Process.output { cmd := cc, args := #["-O1", "-o", bin, cpath] }
        if cr.exitCode != 0 then
          IO.eprintln s!"[smt] {name}: replay compile failed:\n{cr.stderr}"
          IO.Process.exit 1
        let rr ← IO.Process.output { cmd := bin, args := #[] }
        if rr.exitCode == 0 then
          IO.println s!"[smt] {name}: sat + counterexample CONFIRMED by CSim replay ({rr.stdout.trim}) ✓"
        else
          IO.eprintln s!"[smt] {name}: counterexample did NOT reproduce on CSim — solver or emitter bug!\n{rr.stdout}"
          IO.Process.exit 1

  -- Layer 2c: k-induction and counterexample traces (Sparkle.Verification.Bmc).
  let kind (v : Sparkle.Verification.Bmc.Verdict) : String := match v with
    | .holds _ => "holds" | .proved _ => "proved" | .violated .. => "violated"
    | .notInductive .. => "notInductive" | .unknown w => s!"unknown: {w}"
    | .noSolver _ => "noSolver"
  let inductionCases : List (String × Module × Nat × String) :=
    [ -- count ≤ 5 on a counter that sticks at 5: 1-inductive
      ("good-counter-k1", goodCounter, 1, "proved")
      -- read-back equals the registered input: 1-inductive, with a free array
    , ("mem-good-k1", memGood, 1, "proved")
      -- count < 12 on a wrapping counter: nothing within 4 cycles of reset,
      -- but the step fails from the (reachable, here) state 11
    , ("buggy-counter-k5", buggyCounter, 5, "notInductive")
      -- with k past the bug the BASE case finds the real violation
    , ("buggy-counter-k14", buggyCounter, 14, "violated") ]
  for (name, m, k, expect) in inductionCases do
    let v ← Sparkle.Verification.Bmc.checkInduction m k name
    if kind v != expect then
      IO.eprintln s!"[smt] k-induction {name}: expected {expect}, got {kind v}"
      IO.Process.exit 1
    IO.println s!"[smt] k-induction {name}: {kind v} ✓"
    match v with
    | .violated c a tr =>
      -- the base-case trace starts at reset and ends in the violation
      if c != 12 || a != "count_lt_12" || tr.size != 13 then
        IO.eprintln s!"[smt] {name}: wrong violation (cycle {c}, {a}, {tr.size} frames)"
        IO.Process.exit 1
      let counts := tr.toList.map fun frame =>
        (frame.find? (·.1 == "count")).map (·.2) |>.getD 999
      if counts != List.range 13 then
        IO.eprintln s!"[smt] {name}: trace does not show count = 0..12: {counts}"
        IO.Process.exit 1
      let path ← Sparkle.Verification.Bmc.writeVcd m tr name
      IO.println s!"[smt] {name}: trace shows count 0..12; waveform {path}\n{Sparkle.Verification.Bmc.renderTrace m tr}"
    | .notInductive _ _ tr =>
      -- the step trace must end in a violating state reached from a good one
      let last := (tr[tr.size - 1]!.find? (·.1 == "count")).map (·.2)
      if last != some 12 then
        IO.eprintln s!"[smt] {name}: step trace does not end in count = 12: {last}"
        IO.Process.exit 1
    | _ => pure ()

  -- Shortest counterexample: `count < 3` on the enabled counter cannot
  -- fail before cycle 3, and the returned trace must be exactly that long
  -- with `en` high in cycles 0..2.
  match ← Sparkle.Verification.Bmc.checkBmc enCounter 12 "en-counter" with
  | .violated c _ tr =>
    let ens := (tr.toList.take 3).map fun frame =>
      (frame.find? (·.1 == "en")).map (·.2) |>.getD 0
    if c != 3 || tr.size != 4 || ens != [1, 1, 1] then
      IO.eprintln s!"[smt] en-counter: not the shortest counterexample (cycle {c}, en = {ens})"
      IO.Process.exit 1
    IO.println s!"[smt] en-counter: shortest counterexample at cycle 3 ✓"
  | v =>
    IO.eprintln s!"[smt] en-counter: expected a violation, got {kind v}"
    IO.Process.exit 1

  IO.println "\nALL PASS"
