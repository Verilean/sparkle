/-
  CI gate for the silent-wire fixes (notes/compiler/silent-wire-audit.md).

  The probes in `SilentWireProbe{,Symbolic}.lean` synthesize tiny modules at
  elaboration time; this file compares each probe's verdict class with the
  expected one and fails (exit 1) on any difference:
    (c) wiring probes and controls: the observed point has the expected structure
    (b) pw02, pr01, sy01-sy04: the elaborator must REFUSE with an error
  (a) "silently wrong" or (d) "unclear" never match an expected class.
  The probe set is fixed as a manifest of names and classes: a missing, repeated or unknown
  name fails, so a vanished probe cannot be hidden by another one (controls below).
-/
namespace Sparkle.Tests.Compiler.SilentWireRegression

/-- The audit's probe set, fixed: every probe name with its expected class.
    `b` = the elaborator must refuse, `c` = the observed point has the expected structure.
    A verdict whose name is not listed, a listed name that did not run, and a name that ran
    twice are all failures, so a probe cannot vanish behind a renamed or repeated one. -/
def manifest : List (String × Char) :=
  [("pd01_two_calls_two_instances", 'c'), ("pe01_extends_done", 'c'), ("pe02_extends_extra", 'c'),
   ("pj01_hwmod_id_done", 'c'), ("pj02_hwmod_id_val", 'c'), ("pj03_plain2_direct_flag", 'c'),
   ("pj04_plain2_let_flag", 'c'), ("pj05_plain2_id_flag", 'c'), ("pj06_plain2_id_a", 'c'),
   ("pj07_plain3_id_flag", 'c'), ("pj08_plain3_id_a", 'c'), ("pj09_plain3_id_b", 'c'),
   ("pj10_ctor_flag", 'c'), ("pj11_ctor_a", 'c'), ("pj12_update_done", 'c'), ("pj13_update_val", 'c'),
   ("pn01_user_mux_swapped", 'c'), ("pn02_user_register_adds_one", 'c'),
   ("pn03_signal_register_adds_one_control", 'c'), ("pr01_match_unbundle2_snd", 'b'),
   ("ps01_Signal_fst_8x1", 'c'), ("ps02_Signal_snd_8x1", 'c'), ("ps03_map_Prod_fst_8x1", 'c'),
   ("ps04_map_Prod_snd_8x1", 'c'), ("ps05_nested_fst", 'c'), ("ps06_nested_snd_fst", 'c'),
   ("ps07_nested_snd_snd", 'c'), ("ps08_fst_1x8", 'c'), ("ps09_bundle2_snd", 'c'),
   ("pw01_irreducible_width_input", 'c'), ("pw02_fvar_width_unresolved", 'b'),
   ("pw03_concrete_width_control", 'c'), ("sy01_symbolic_Signal_fst", 'b'),
   ("sy02_symbolic_Signal_snd", 'b'), ("sy03_symbolic_map_Prod_fst", 'b'),
   ("sy04_symbolic_map_lambda", 'b')]

/-- Verdict lines look like `tag: (c) correct: ...`; return `(tag, class char)`. -/
def parseVerdict (line : String) : Option (String × Char) :=
  match line.splitOn ": (" with
  | tag :: rest :: _ => (rest.get? 0).map fun c => (tag, c)
  | _ => none

/-- Returns the failure messages (empty = pass): unparseable lines, class mismatches,
    names outside the manifest, names that ran more than once, manifest names that did not run. -/
def failures (man : List (String × Char)) (verdicts : List String) : List String :=
  let parsed := verdicts.filterMap parseVerdict
  let unparseable := (verdicts.filter fun l => (parseVerdict l).isNone).map
    (s!"unparseable verdict: " ++ ·)
  let perProbe := parsed.filterMap fun (tag, got) =>
    match man.lookup tag with
    | none => some s!"{tag}: not in the manifest (got ({got}))"
    | some want => if got == want then none else some s!"{tag}: expected ({want}), got ({got})"
  let tags := parsed.map (·.1)
  let dups := (tags.eraseDups.filter fun t => (tags.filter (· == t)).length > 1).map
    (s!"ran more than once: " ++ ·)
  let missing := (man.filter fun (t, _) => !tags.contains t).map
    (fun (t, _) => s!"manifest probe did not run: {t}")
  unparseable ++ perProbe ++ dups ++ missing

/-! Checker controls: a verdict list built from the manifest passes; every way of keeping the
    count at 36 while losing a probe, or changing a class, fails. -/

def synth (l : List (String × Char)) : List String := l.map fun (t, c) => s!"{t}: ({c}) synthetic"

#guard (failures manifest (synth manifest)).isEmpty
-- a probe replaced by an unknown name (count unchanged)
#guard !(failures manifest (synth ((manifest.drop 1) ++ [("pj99_unknown", 'c')]))).isEmpty
-- a probe replaced by a duplicate of another probe (count unchanged)
#guard !(failures manifest (synth ((manifest.drop 1) ++ [manifest[1]!]))).isEmpty
-- a refused probe replaced by a duplicate correct probe (count unchanged)
#guard !(failures manifest (synth ((manifest.filter (·.1 != "pr01_match_unbundle2_snd")) ++
    [("pj01_hwmod_id_done", 'c')]))).isEmpty
-- a class flipped
#guard !(failures manifest (synth (manifest.map fun (t, c) =>
    if t == "pj01_hwmod_id_done" then (t, 'a') else (t, c)))).isEmpty
-- a probe missing
#guard !(failures manifest (synth (manifest.drop 1))).isEmpty
#guard manifest.length == 36 && (manifest.map (·.1)).eraseDups.length == 36

def run (verdicts : List String) : IO UInt32 := do
  IO.println s!"silent-wire regression ({manifest.length} probes in the manifest; (b) for pw02, pr01, sy01-sy04, (c) for the rest)"
  for v in verdicts do IO.println s!"  {v}"
  let fs := failures manifest verdicts
  if fs.isEmpty then
    IO.println s!"PASS: {verdicts.length} probes match the manifest (names, classes, no duplicates)"
    return 0
  else
    for f in fs do IO.eprintln s!"FAIL: {f}"
    return 1

end Sparkle.Tests.Compiler.SilentWireRegression
