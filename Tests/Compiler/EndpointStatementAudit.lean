import Lean.Elab.Command
import Tests.AllTests

/-! # Endpoint statements, described — a companion audit for TWO trees

WRITTEN, NOT BUILT, NOT RUN (`fix/env-capture-a`). TARGET-ONLY (not for
`Tests/AllTests.lean`). LOGS ONLY: it asserts nothing and never throws. It
uses no declaration of the environment-capture unit, so it builds on poc
(`80745d94`) and on the candidate; the integrator runs it on both and DIFFS
the `ENDPOINTAUDIT` lines.

For every THEOREM of the `Tests.AllTests` environment whose last name
component is an endpoint name (it starts with `machine_`, `gate_`, `leaf_`,
`design_`, `oneout_`, `noports_`, `ships_`, or is `entry_ok`, `closes_deep`,
`closes_prov`), one line:

    ENDPOINTAUDIT <name>: binders=<n> env=<k> premises=[<head>*<count>, …] concl=<head> translator=<T|F> hash=<h>

* `binders` — the number of leading `∀` binders of the statement, as written
  (no unfolding);
* `env` — how many of them have type `Lean.Environment`;
* `premises` — the binders whose type is a proposition, classified by the
  head constant of their conclusion (after their own `∀`s), with
  multiplicity, sorted;
* `concl` — the head constant of the statement's conclusion;
* `translator` — whether the statement mentions the constant
  `translateExprToWire` at all (as written, no unfolding);
* `hash` — a hash of the statement with every `Lean.Environment` binder
  REMOVED is not attempted (that would hide exactly what is asked); instead
  the hash is of the statement AS IT IS, so a line whose only difference is
  `hash` has a difference inside a premise or the conclusion that the other
  fields do not show, and must be looked at.

What the environment-capture unit predicts (docs/parallel/M-env-capture-a.md,
"The endpoint audit"): a line with `translator=F` on poc is IDENTICAL on the
candidate, hash included — the definitions it names (`MachineClosesAt`,
`MachineCloses`, `MachineRan`, `HarnessStill`, …) changed their BODIES, not
their parameters, and the statement only names them. A line with
`translator=T` gains one binder of type `Lean.Environment` (`binders` +1,
`env` +1) or an `∀ {tenv}` inside a premise, and its hash differs; nothing
else of the line changes. Any other difference is a finding. -/
namespace Tests.Compiler.EndpointStatementAudit
open Lean Meta

def isEndpointName (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s.startsWith "machine_" || s.startsWith "gate_" || s.startsWith "leaf_" ||
    s.startsWith "design_" || s.startsWith "oneout_" || s.startsWith "noports_" ||
    s.startsWith "ships_" || s == "entry_ok" || s == "closes_deep" || s == "closes_prov"
  | _ => false

/-- The head constant of a statement's conclusion (its own `∀`s peeled). -/
def conclHead (e : Lean.Expr) : String :=
  match e.getForallBody.getAppFn with
  | .const n _ => toString n
  | .fvar _ => "<variable>"
  | .bvar _ => "<variable>"
  | .sort _ => "<sort>"
  | .forallE .. => "<forall>"
  | _ => "<other>"

def isEnvType (e : Lean.Expr) : Bool := e.isConstOf ``Lean.Environment

def mentionsTranslator (e : Lean.Expr) : Bool :=
  (e.find? fun x => x.isConstOf ``Sparkle.Compiler.Elab.translateExprToWire).isSome

/-- binders, environment binders, premise heads, conclusion head. -/
def describe (type : Lean.Expr) : MetaM (Nat × Nat × List String × String) :=
  forallBoundedTelescope type none fun xs body => do
    let mut envs := 0
    let mut heads : Array String := #[]
    for x in xs do
      let t ← inferType x
      if isEnvType t then envs := envs + 1
      if (← isProp t) then heads := heads.push (conclHead t)
    return (xs.size, envs, heads.toList, conclHead body)

def counted (hs : List String) : List String :=
  let sorted := hs.toArray.qsort (· < ·) |>.toList
  let rec go : List String → List (String × Nat) → List (String × Nat)
    | [], acc => acc.reverse
    | h :: t, (h', k) :: acc => if h == h' then go t ((h', k + 1) :: acc) else go t ((h, 1) :: (h', k) :: acc)
    | h :: t, [] => go t [(h, 1)]
  (go sorted []).map fun p => s!"{p.1}*{p.2}"

def bs (b : Bool) : String := if b then "T" else "F"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if isEndpointName n then
      match ci with
      | .thmInfo _ => names := names.push n
      | _ => pure ()
  let sorted := names.qsort (fun a b => toString a < toString b)
  let mut withT := 0
  for n in sorted do
    let some ci := env.find? n | continue
    let line ←
      try
        let (k, e, hs, c) ← describe ci.type
        let t := mentionsTranslator ci.type
        pure s!"ENDPOINTAUDIT {n}: binders={k} env={e} premises={counted hs} concl={c} translator={bs t} hash={hash ci.type}"
      catch _ => pure s!"ENDPOINTAUDIT {n}: NOT DESCRIBED"
    if mentionsTranslator ci.type then withT := withT + 1
    IO.eprintln line
    logInfo m!"{line}"
  let summary := s!"ENDPOINTAUDIT SUMMARY: {sorted.size} endpoint theorems, {withT} mention the translator"
  IO.eprintln summary
  logInfo m!"{summary}"

end Tests.Compiler.EndpointStatementAudit
