/-
  CI gate for the silent-wire fixes (notes/compiler/silent-wire-audit.md).

  The probes in `SilentWireProbe{,Symbolic}.lean` synthesize tiny modules at
  elaboration time; this file compares each probe's verdict class with the
  expected one and fails (exit 1) on any difference:
    (c) wiring probes and controls: the observed point has the expected structure
    (b) pw02, pr01, sy01-sy04: the elaborator must REFUSE with an error
  (a) "silently wrong" or (d) "unclear" never match an expected class.
  The probe set itself is checked too (a vanished probe must not make the test pass).
-/
namespace Sparkle.Tests.Compiler.SilentWireRegression

/-- Probes that must be refused (class `b`); every other probe must be `c`. -/
def expectedRefused : List String :=
  ["pw02_fvar_width_unresolved", "pr01_match_unbundle2_snd",
   "sy01_symbolic_Signal_fst", "sy02_symbolic_Signal_snd",
   "sy03_symbolic_map_Prod_fst", "sy04_symbolic_map_lambda"]

/-- Number of probes in the audit; fewer verdicts means a probe disappeared. -/
def expectedProbeCount : Nat := 36

/-- Verdict lines look like `tag: (c) correct: ...`; return `(tag, class char)`. -/
def parseVerdict (line : String) : Option (String × Char) :=
  match line.splitOn ": (" with
  | tag :: rest :: _ => (rest.get? 0).map fun c => (tag, c)
  | _ => none

def expectedClass (refused : List String) (tag : String) : Char :=
  if refused.contains tag then 'b' else 'c'

/-- Returns the failure messages (empty = pass). -/
def failures (refused : List String) (count : Nat) (verdicts : List String) : List String :=
  let perProbe := verdicts.filterMap fun line =>
    match parseVerdict line with
    | none => some s!"unparseable verdict: {line}"
    | some (tag, got) =>
      let want := expectedClass refused tag
      if got == want then none else some s!"{tag}: expected ({want}), got: {line}"
  let missing := refused.filter fun t => !(verdicts.any fun l => (parseVerdict l).any (·.1 == t))
  let countMsg := if verdicts.length < count
    then [s!"only {verdicts.length} probes ran, expected at least {count}"] else []
  perProbe ++ missing.map (s!"expected-refused probe did not run: " ++ ·) ++ countMsg

def run (verdicts : List String) : IO UInt32 := do
  IO.println "silent-wire regression (expected: (c) for wiring probes/controls, (b) for pw02, pr01, sy01-sy04)"
  for v in verdicts do IO.println s!"  {v}"
  let fs := failures expectedRefused expectedProbeCount verdicts
  if fs.isEmpty then
    IO.println s!"PASS: {verdicts.length} probes match their expected class"
    return 0
  else
    for f in fs do IO.eprintln s!"FAIL: {f}"
    return 1

end Sparkle.Tests.Compiler.SilentWireRegression
