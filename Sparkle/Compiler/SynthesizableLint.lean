/-
  SynthesizableLint — `#check_synthesizable <name>` conservative early-warning
  linter for Signal DSL constants intended for `#writeDesign` /
  `#synthesizeVerilog` / `#sim`.

  The linter walks the definition body as a `Lean.Expr` (WITHOUT reducing it)
  and flags patterns that are known to break the Verilog backend:

  - N1  `Id.run` / pure-Lean `let mut` / `do`-block mutation
  - N2  `match` / `X.rec` on an inductive that is not `BitVec`, `Bool`, or a
        `Signal`-level primitive — *unless* it is applied to a literal that
        reduces away (we don't try to reduce; we only flag when the scrutinee
        is not syntactically a known-good form, so users see a warning they
        can dismiss).
  - N3  `ite` / `dite` (pure `if … then … else …`) whose condition is not a
        `Signal _ (BitVec _)` — i.e. a compile-time `Bool`/`Decidable`
        branch that the backend cannot lower.
  - N4  `Signal.val` appearing inside the synthesis path.

  Design notes:

  - CONSERVATIVE: we emit warnings, not errors, and we err on the side of
    false positives that the user can triage with the N1-N7 catalog in
    `docs/KnownIssues.md`. A clean `#check_synthesizable` is a strong
    signal; a dirty one is a prompt to inspect, not a hard stop.

  - LEAN-VERSION-ROBUST: we only use stable `Lean.Expr` pattern-matching
    (`Expr.app`, `Expr.const`, `Expr.letE`, etc.) and the long-stable
    `Environment.find?` / `ConstantInfo.value?` accessors. No reliance on
    `Meta.whnf`, elaboration hints, or quotation metadata that churns
    across point releases.

  Usage:

      #check_synthesizable myIP
-/

import Lean
import Lean.Elab.Command

namespace Sparkle.Compiler.SynthesizableLint

open Lean Lean.Elab Lean.Elab.Command

/-- A single finding. `tag` is the N-number from docs/KnownIssues.md. -/
structure Finding where
  tag     : String
  message : String
  deriving Inhabited

/-- Inductives whose `match` / `.rec` is safe in the synthesis path. -/
def synthesizableInductives : Array Name := #[
  ``BitVec, ``Bool, ``Prod, ``PUnit, ``Unit, ``Nat, ``Fin
]

/-- Heads whose presence in the body is a direct red flag (N1/N4). -/
def bannedHeads : Array (Name × String × String) := #[
  (``Id.run,      "N1", "`Id.run` (pure-Lean do-block / `let mut`) is not synthesizable"),
  (``StateT,      "N1", "`StateT` in a synthesis path is not synthesizable"),
  (``ReaderT,     "N1", "`ReaderT` in a synthesis path is not synthesizable")
]

/-- `Signal.val` fully-qualified name — flagged as N4 when it leaks into a
    synthesizable definition. We match by suffix to stay robust across
    namespace reshuffles. -/
def isSignalVal (n : Name) : Bool :=
  n.getString! == "val" && (n.getPrefix.toString.endsWith "Signal")

/-- `ite` / `dite` constants — N3 candidates. -/
def isIte (n : Name) : Bool := n == ``ite || n == ``dite

/-- `X.rec` / `X.casesOn` / `X.brecOn` on a non-synthesizable inductive → N2. -/
def matchRecSuspect (n : Name) : Option Name :=
  let s := n.getString!
  if s == "rec" || s == "casesOn" || s == "brecOn" || s == "recAux" then
    some n.getPrefix
  else
    none

/-- Auxiliary match-compilation const (`_foo.match_1`, `Foo.match_2`, …).
    Lean compiles `match` statements into these. We conservatively flag
    any reference to a match-aux whose name is not in our safe list
    (BitVec/Bool/Nat/Fin). -/
def isMatchAux (n : Name) : Bool :=
  n.getString!.startsWith "match_"

/-- Heuristic: does a match-aux look like it is scrutinizing a safe
    inductive? We look at the prefix and match it against the safe list. -/
def matchAuxIsSafe (_ : Name) : Bool :=
  -- Conservative: we cannot cheaply recover the scrutinee type from the
  -- aux name alone, so we always flag. Users can dismiss false positives.
  false

/-- Walk an expression and collect findings. Does NOT reduce; purely
    syntactic. Visits under lambdas and lets; does not descend into
    types (those are often full of meta noise that is not synthesized). -/
partial def scanExpr (e : Expr) : StateM (Array Finding) Unit := do
  let push (f : Finding) : StateM (Array Finding) Unit := modify (·.push f)
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const name _ =>
      -- Banned heads (N1/N4 direct)
      for (bad, tag, msg) in bannedHeads do
        if name == bad then
          push { tag, message := msg }
      -- Signal.val leak (N4)
      if isSignalVal name then
        push { tag := "N4", message := s!"`{name}` appears in the synthesis path — proof/simulation helper leaked in" }
      -- ite / dite (N3)
      if isIte name then
        push { tag := "N3", message := "`if-then-else` on a pure `Bool`/`Decidable` — use `Signal.mux` for runtime choice, or make the condition a compile-time literal" }
      -- match / rec on non-synthesizable inductive (N2)
      if let some indName := matchRecSuspect name then
        unless synthesizableInductives.contains indName do
          push { tag := "N2", message := s!"`{name}` — pattern-match on `{indName}` does not lower to Verilog; either make the scrutinee a compile-time literal, or encode the choice as a `BitVec` and use `Signal.mux`" }
      if isMatchAux name && !matchAuxIsSafe name then
        push { tag := "N2", message := s!"`{name}` — `match` auxiliary; if it scrutinizes anything other than `BitVec`/`Bool`/`Nat`/`Fin` (or a compile-time literal that reduces), it will not lower to Verilog. Use `Signal.mux` for runtime choice." }
    | _ => pure ()
    args.forM scanExpr
  | .lam _ _ body _ => scanExpr body
  | .forallE _ _ body _ => scanExpr body
  | .letE _ _ value body _ => scanExpr value; scanExpr body
  | .mdata _ inner => scanExpr inner
  | .proj _ _ inner => scanExpr inner
  | .const name _ =>
    for (bad, tag, msg) in bannedHeads do
      if name == bad then push { tag, message := msg }
    if isSignalVal name then
      push { tag := "N4", message := s!"`{name}` appears in the synthesis path" }
  | _ => pure ()

/-- Run the scanner on a constant's body and return unique findings. -/
def lintConstant (name : Name) : MetaM (Array Finding) := do
  let env ← getEnv
  let some ci := env.find? name
    | throwError m!"#check_synthesizable: unknown constant `{name}`"
  let some body := ci.value?
    | throwError m!"#check_synthesizable: `{name}` has no body (is it an `opaque` or `axiom`?)"
  let (_, findings) := (scanExpr body).run #[]
  -- Deduplicate by (tag, message).
  let mut seen : Std.HashSet String := {}
  let mut out : Array Finding := #[]
  for f in findings do
    let key := f.tag ++ "|" ++ f.message
    unless seen.contains key do
      seen := seen.insert key
      out := out.push f
  return out

/-- `#check_synthesizable foo` — conservative lint pass. -/
syntax (name := checkSynthCmd) "#check_synthesizable " ident : command

@[command_elab checkSynthCmd]
def elabCheckSynth : CommandElab := fun stx => do
  match stx with
  | `(#check_synthesizable $f:ident) => do
    let name ← liftCoreM (Lean.Elab.realizeGlobalConstNoOverloadWithInfo f)
    let findings ← liftTermElabM (lintConstant name)
    if findings.isEmpty then
      logInfoAt f m!"✅ `{name}` passes the conservative synthesizability lint ({findings.size} findings). See docs/KnownIssues.md § Non-synthesizable Signal DSL patterns if `#writeDesign` still fails."
    else
      let mut msg := m!"⚠  `{name}` has {findings.size} synthesizability finding(s):"
      for f in findings do
        msg := msg ++ m!"\n  [{f.tag}] {f.message}"
      msg := msg ++ m!"\nSee docs/KnownIssues.md § Non-synthesizable Signal DSL patterns (N1-N7) for fixes. Note: this linter is conservative — false positives are possible; use judgement."
      logWarningAt f msg
  | _ => throwUnsupportedSyntax

end Sparkle.Compiler.SynthesizableLint
