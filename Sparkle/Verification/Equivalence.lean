/-
  Equivalence — Fast equivalence-check commands built on `bv_decide`.

  This module exposes two commands:

  1. `#verify_eq f g` — for pure `BitVec a → … → BitVec z` functions.
     Generates `theorem {f}_eq_{g} : f = g := by funext …; unfold f g; bv_decide`.

  2. `#verify_eq_at (cycles := N) (latency := L) impl spec` — for
     Signal DSL functions built from `register`, `pure`, `map`, `ap`, and
     the hardware operators (`+`, `*`, `^^^`, `&&&`, etc.). Checks that
     for every input stream, `(impl …).val t = (spec …).val (t - L)`
     at every time `t ∈ [L, L + N)`. `latency := 0` is the default (pure
     refactoring check); `latency > 0` lets you prove that a multi-cycle
     pipeline is functionally equivalent to a single-cycle reference
     modulo the pipeline's own delay.

  Intended for small widths — `bv_decide` SAT-scales with `cycles ×
  arity × bitwidth`. 4-bit inputs and 4-8 cycles are the sweet spot.

  ⚠  KNOWN ISSUE (docs/KnownIssues.md Issue 2): `bv_decide` hangs in
  `lake build` compilation mode on Lean 4.28.0-rc1, but works in the
  interpreter (`lake env lean`) and in VSCode. This module itself never
  calls `bv_decide` — it only defines elaborators and a handful of
  `rfl`-proved helper lemmas — so it is always safe to `lake build`.
  Files that CALL `#verify_eq` / `#verify_eq_at` should NOT be imported
  from the default build target; run them interactively.

  Usage:

      -- Pure BitVec identity
      def pure_alu (a b : BitVec 8) : BitVec 8 := a + b
      def fast_alu (a b : BitVec 8) : BitVec 8 :=
        (a ^^^ b) + ((a &&& b) <<< 1)
      #verify_eq fast_alu pure_alu

      -- Layer 2: pipeline vs single-cycle MAC, latency = 2
      def macSingle (a b c : Signal dom (BitVec 4)) : Signal dom (BitVec 4) :=
        a * b + c
      def macPipe (a b c : Signal dom (BitVec 4)) : Signal dom (BitVec 4) :=
        let prod2 := Signal.register 0 (Signal.register 0 a * Signal.register 0 b)
        let c2    := Signal.register 0 (Signal.register 0 c)
        prod2 + c2
      #verify_eq_at (cycles := 4) (latency := 2) macPipe macSingle
-/

import Lean
import Lean.Meta
import Lean.Elab.Command
import Sparkle.Core.Signal

-- ========================================================================
-- Signal DSL unfolding lemmas (used by the `#verify_eq_at` generated
-- tactic). Each is `rfl` and exists only to give `simp only` a stable set
-- of rewrite rules that pushes `.val t` through the hardware operators
-- and register primitives.
-- ========================================================================

namespace Sparkle.Verification.Equivalence.SignalLemmas

open Sparkle.Core.Domain Sparkle.Core.Signal

-- Arithmetic: the Signal+Signal hardware operators all desugar to
-- `(· op ·) <$> a <*> b`, which reduces via Functor.map + Applicative.seq.
-- `bv_decide` cannot see through those layers on its own; these lemmas
-- supply the single-step rewrite it needs.

theorem val_add {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a + b).val t = a.val t + b.val t := rfl

theorem val_sub {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a - b).val t = a.val t - b.val t := rfl

theorem val_mul {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a * b).val t = a.val t * b.val t := rfl

theorem val_and {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a &&& b).val t = a.val t &&& b.val t := rfl

theorem val_or {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a ||| b).val t = a.val t ||| b.val t := rfl

theorem val_xor {dom : DomainConfig} {n : Nat}
    (a b : Signal dom (BitVec n)) (t : Nat) :
    (a ^^^ b).val t = a.val t ^^^ b.val t := rfl

-- Register is the only stateful primitive we unfold (Signal.loop is
-- opaque and outside layer 2 scope — see KnownIssues Issue 3.3).
theorem val_register_zero {dom : DomainConfig} {α : Type}
    (init : α) (x : Signal dom α) :
    (Signal.register init x).val 0 = init := rfl

theorem val_register_succ {dom : DomainConfig} {α : Type}
    (init : α) (x : Signal dom α) (n : Nat) :
    (Signal.register init x).val (n + 1) = x.val n := rfl

-- Constant signal
theorem val_pure {dom : DomainConfig} {α : Type}
    (x : α) (t : Nat) :
    (Signal.pure (dom := dom) x).val t = x := rfl

end Sparkle.Verification.Equivalence.SignalLemmas

namespace Sparkle.Verification.Equivalence

open Lean Elab Command Meta

/-- Count the number of leading `∀` / Pi binders in a function type.
    Used to decide how many `funext`s to emit in the generated proof. -/
private def arityOfType (t : Expr) : MetaM Nat := do
  forallTelescopeReducing t fun args _ => pure args.size

/-- Elaborate a generated theorem command and report ✅/❌.

    `bv_decide` failures do NOT propagate as exceptions out of
    `elabCommand`; they surface as deferred error messages AND either
    leave the theorem missing or taint its value with `sorry`. So we
    detect failure via (a) try/catch, (b) new error messages in the
    log, (c) environment lookup + `hasSorry` on the stored theorem.

    Prints the success line at the position of `atStx` (usually the
    `ident` the user wrote). -/
private def elabAndReport (atStx : Syntax) (cmd : Syntax)
    (thmName : Name) (label : MessageData) : CommandElabM Unit := do
  let msgsBefore := (← get).messages
  let thrown ← try elabCommand cmd; pure false
               catch _ => pure true
  let msgsAfter := (← get).messages
  let newErrors :=
    (msgsAfter.toList.drop msgsBefore.toList.length).filter
      (·.severity == .error)
  let tainted :=
    match (← getEnv).find? thmName with
    | none => true
    | some ci => ci.type.hasSorry || (ci.value?.map (·.hasSorry)).getD false
  if thrown || !newErrors.isEmpty || tainted then
    logInfoAt atStx m!"❌ {label} — see error(s) above for `{thmName}`"
  else
    logInfoAt atStx m!"✅ verified: `{thmName}` — {label}"

/-- `#verify_eq f g` — prove `f = g` via `funext; unfold; bv_decide`. -/
syntax (name := verifyEqCmd) "#verify_eq " ident ident : command

@[command_elab verifyEqCmd]
def elabVerifyEq : CommandElab := fun stx => do
  match stx with
  | `(#verify_eq $f:ident $g:ident) => do
    -- 1. Resolve both idents to fully-qualified names.
    let fName ← liftCoreM (Lean.Elab.realizeGlobalConstNoOverloadWithInfo f)
    let gName ← liftCoreM (Lean.Elab.realizeGlobalConstNoOverloadWithInfo g)

    -- 2. Introspect types, verify they match, compute arity.
    let (arity, _) ← liftTermElabM do
      let fInfo ← getConstInfo fName
      let gInfo ← getConstInfo gName
      let fT := fInfo.type
      let gT := gInfo.type
      unless (← isDefEq fT gT) do
        throwErrorAt g
          m!"#verify_eq: type mismatch{indentD m!"{f} : {fT}"}{indentD m!"{g} : {gT}"}"
      let n ← arityOfType fT
      pure (n, fT)

    -- 3. Fresh theorem name. Reject if it already exists to avoid
    --    surprising shadowing.
    let thmBase := Name.mkSimple s!"{fName.toString}_eq_{gName.toString}"
    let thmName := thmBase.replacePrefix .anonymous .anonymous
    if (← getEnv).contains thmName then
      throwError m!"#verify_eq: theorem `{thmName}` already exists; \
                    delete it or rename one of `{fName}` / `{gName}`"
    let thmIdent := mkIdent thmName

    -- 4. Build fresh binder idents `x_1, …, x_n`.
    let binders : Array (TSyntax `ident) :=
      (Array.range arity).map fun i =>
        mkIdent (Name.mkSimple s!"x_{i + 1}")

    -- 5. Build the theorem via quotation. Zero arity → skip funext.
    let cmd ← if arity == 0 then
      `(command|
        theorem $thmIdent : $f = $g := by
          unfold $f:ident $g:ident
          bv_decide)
    else
      `(command|
        theorem $thmIdent : $f = $g := by
          funext $binders*
          unfold $f:ident $g:ident
          bv_decide)

    -- 6. Elaborate + report.
    elabAndReport f cmd thmName m!"`{fName}` ≡ `{gName}`"

  | _ => throwUnsupportedSyntax

-- ========================================================================
-- Layer 2: Signal DSL equivalence at N cycles, with optional latency.
--
-- `#verify_eq_at (cycles := N) (latency := L) impl spec`
--
-- Generates
--
--     theorem {impl}_eq_{spec}_at_N_lat_L :
--         ∀ (a_1 … a_k : Signal dom α_i),
--           (impl a_1 … a_k).val L       = (spec a_1 … a_k).val 0 ∧
--           (impl a_1 … a_k).val (L+1)   = (spec a_1 … a_k).val 1 ∧
--           …
--           (impl a_1 … a_k).val (L+N-1) = (spec a_1 … a_k).val (N-1)
--       := by
--         intros
--         refine ⟨?_, …, ?_⟩
--         all_goals
--           simp only [impl, spec, Signal.val_add, Signal.val_mul, …,
--                      Signal.val_register_zero, Signal.val_register_succ]
--           <;> bv_decide
--
-- The generated goal at each time is a pure BitVec equality at the given
-- cycle, which `bv_decide` discharges. Uses the `Sparkle.Verification
-- .Equivalence.SignalLemmas.*` `rfl`-lemmas as its `simp only` lemma set
-- so the user's own `def` bodies are the only things that need to be
-- expanded by `simp only [impl, spec]`.
--
-- Non-goals (v1): `Signal.loop` / `loopMemo` / feedback circuits, memory
-- primitives, unbounded-t equivalence.
-- ========================================================================

/-- `#verify_eq_at (cycles := N) (latency := L)? impl spec` -/
syntax (name := verifyEqAtCmd)
  "#verify_eq_at " "(" &"cycles" ":=" num ")"
  (" (" &"latency" ":=" num ")")?
  ident ident : command

/-- Build the theorem command for `#verify_eq_at` with a given
    theorem name, cycle count, latency, and argument arity. Returns a
    fully-elaborated command syntax that the caller can feed to
    `elabCommand`. Does NOT touch the environment or message log. -/
private def buildVerifyEqAtCmd
    (thmName : Name) (cycles latency arity : Nat)
    (impl spec : Ident) : CommandElabM (TSyntax `command) := do
  let thmIdent := mkIdent thmName
  let binders : Array (TSyntax `ident) :=
    (Array.range arity).map fun i =>
      mkIdent (Name.mkSimple s!"_eq_at_arg_{i + 1}")
  let args : Array (TSyntax `term) := binders.map fun b => ⟨b.raw⟩

  -- One conjunct per cycle t ∈ [0, cycles): (impl args).val (t+L) = (spec args).val t
  let mkConjunct (t : Nat) : CommandElabM (TSyntax `term) := do
    let tLit : TSyntax `term := ⟨Syntax.mkNumLit (toString t)⟩
    let lhsLit : TSyntax `term := ⟨Syntax.mkNumLit (toString (t + latency))⟩
    `(($impl $args*).val $lhsLit = ($spec $args*).val $tLit)
  let mut conjuncts : Array (TSyntax `term) := #[]
  for t in [:cycles] do
    conjuncts := conjuncts.push (← mkConjunct t)
  let mut goalBody : TSyntax `term := conjuncts[conjuncts.size - 1]!
  for i in (List.range (conjuncts.size - 1)).reverse do
    let head := conjuncts[i]!
    goalBody ← `($head ∧ $goalBody)

  -- ⟨?_, ?_, …⟩ with `cycles` holes
  let holeStx : TSyntax `term ← `(?_)
  let mut holes : Array (TSyntax `term) := #[]
  for _ in [:cycles] do
    holes := holes.push holeStx
  let refineTerm : TSyntax `term ← `(⟨$holes,*⟩)

  -- Fixed Signal.val_* lemma set
  let lemL1 := mkIdent ``Sparkle.Verification.Equivalence.SignalLemmas.val_add
  let lemL2 := mkIdent ``Sparkle.Verification.Equivalence.SignalLemmas.val_sub
  let lemL3 := mkIdent ``Sparkle.Verification.Equivalence.SignalLemmas.val_mul
  let lemL4 := mkIdent ``Sparkle.Verification.Equivalence.SignalLemmas.val_and
  let lemL5 := mkIdent ``Sparkle.Verification.Equivalence.SignalLemmas.val_or
  let lemL6 := mkIdent ``Sparkle.Verification.Equivalence.SignalLemmas.val_xor
  let lemR0 := mkIdent ``Sparkle.Verification.Equivalence.SignalLemmas.val_register_zero
  let lemRS := mkIdent ``Sparkle.Verification.Equivalence.SignalLemmas.val_register_succ
  let lemPu := mkIdent ``Sparkle.Verification.Equivalence.SignalLemmas.val_pure

  `(command|
    set_option linter.unusedSimpArgs false in
    theorem $thmIdent : ∀ $binders*, $goalBody := by
      intros
      refine $refineTerm
      all_goals
        (first
          | (simp only [$impl:ident, $spec:ident,
                        $lemL1:ident, $lemL2:ident, $lemL3:ident,
                        $lemL4:ident, $lemL5:ident, $lemL6:ident,
                        $lemR0:ident, $lemRS:ident, $lemPu:ident];
             done)
          | (simp only [$impl:ident, $spec:ident,
                        $lemL1:ident, $lemL2:ident, $lemL3:ident,
                        $lemL4:ident, $lemL5:ident, $lemL6:ident,
                        $lemR0:ident, $lemRS:ident, $lemPu:ident];
             bv_decide)))

/-- Silent probe: try to prove `impl ≡ spec` at `(cycles, latency)` using
    a fresh throwaway theorem name. Rolls back both the environment and
    the message log on exit, so the probe is invisible to the user.
    Returns `true` iff the probe succeeded. -/
private def probeLatency
    (cycles latency arity : Nat) (impl spec : Ident) : CommandElabM Bool := do
  let savedEnv := (← getEnv)
  let savedState ← get
  -- Unique probe theorem name derived from the user idents and the
  -- latency-under-test. The savedEnv rollback deletes it either way.
  let probeName := Name.mkSimple
    s!"_verify_eq_at_probe_{impl.getId}_{spec.getId}_c{cycles}_l{latency}"
  let ok : Bool ← try
    let cmd ← buildVerifyEqAtCmd probeName cycles latency arity impl spec
    let thrown ← try elabCommand cmd; pure false catch _ => pure true
    let newMsgsHaveError :=
      ((← get).messages.toList.drop savedState.messages.toList.length).any
        (·.severity == .error)
    let tainted :=
      match (← getEnv).find? probeName with
      | none => true
      | some ci => ci.type.hasSorry || (ci.value?.map (·.hasSorry)).getD false
    pure (!thrown && !newMsgsHaveError && !tainted)
  catch _ => pure false
  -- Roll back EVERYTHING the probe touched: environment (removes the
  -- probe theorem and any downstream elab state), and message log
  -- (removes probe errors / counterexample spam).
  setEnv savedEnv
  modify fun s => { s with messages := savedState.messages }
  pure ok

@[command_elab verifyEqAtCmd]
def elabVerifyEqAt : CommandElab := fun stx => do
  match stx with
  | `(#verify_eq_at (cycles := $cyclesLit:num) $impl:ident $spec:ident) =>
      runVerifyEqAt cyclesLit 0 impl spec
  | `(#verify_eq_at (cycles := $cyclesLit:num) (latency := $latLit:num) $impl:ident $spec:ident) =>
      runVerifyEqAt cyclesLit latLit.getNat impl spec
  | _ => throwUnsupportedSyntax
where
  runVerifyEqAt (cyclesLit : TSyntax `num) (latency : Nat)
      (impl : Ident) (spec : Ident) : CommandElabM Unit := do
    let cycles := cyclesLit.getNat
    if cycles == 0 then
      throwErrorAt cyclesLit "#verify_eq_at: `cycles` must be ≥ 1"

    -- 1. Resolve names.
    let implName ← liftCoreM (Lean.Elab.realizeGlobalConstNoOverloadWithInfo impl)
    let specName ← liftCoreM (Lean.Elab.realizeGlobalConstNoOverloadWithInfo spec)

    -- 2. Introspect types, require them to match, compute arity.
    let arity ← liftTermElabM do
      let iT := (← getConstInfo implName).type
      let sT := (← getConstInfo specName).type
      unless (← isDefEq iT sT) do
        throwErrorAt spec
          m!"#verify_eq_at: type mismatch{indentD m!"{impl} : {iT}"}{indentD m!"{spec} : {sT}"}"
      arityOfType iT

    -- 3. Fresh user-visible theorem name.
    let latencyTag := if latency == 0 then "" else s!"_lat_{latency}"
    let thmName := Name.mkSimple
      s!"{implName.toString}_eq_{specName.toString}_at_{cycles}{latencyTag}"
    if (← getEnv).contains thmName then
      throwError m!"#verify_eq_at: theorem `{thmName}` already exists"

    -- 4. Build the user's theorem command and run it.
    let cmd ← buildVerifyEqAtCmd thmName cycles latency arity impl spec
    let label :=
      if latency == 0 then
        m!"`{implName}` ≡ `{specName}` at cycles 0..{cycles}"
      else
        m!"`{implName}` ≡ `{specName}` at cycles {latency}..{latency + cycles} (latency {latency})"

    let msgsBefore := (← get).messages
    let thrown ← try elabCommand cmd; pure false catch _ => pure true
    let msgsAfter := (← get).messages
    let newErrors :=
      (msgsAfter.toList.drop msgsBefore.toList.length).filter (·.severity == .error)
    let tainted :=
      match (← getEnv).find? thmName with
      | none => true
      | some ci => ci.type.hasSorry || (ci.value?.map (·.hasSorry)).getD false

    if thrown || !newErrors.isEmpty || tainted then
      -- Failed — run latency probes at a REDUCED cycle count to keep the
      -- hint fast, then surface the first matching latency. The probes
      -- are silent: they save/restore the env and message log so the
      -- user only sees the original failure + the hint line.
      let probeCycles := min cycles 2   -- 2 is usually enough to distinguish
      let maxProbe := cycles + 4        -- search 0..cycles+3
      let mut matchedLat : Option Nat := none
      for L in [:maxProbe] do
        if L == latency then continue    -- the user's choice already failed
        if ← probeLatency probeCycles L arity impl spec then
          matchedLat := some L
          break
      logInfoAt impl m!"❌ {label} — see error(s) above for `{thmName}`"
      match matchedLat with
      | some L =>
        logInfoAt impl
          m!"💡 Hint: the circuit DOES match at latency := {L}. \
             Re-run as  #verify_eq_at (cycles := {cycles}) (latency := {L}) \
             {implName} {specName}  \
             — if that is not the latency you designed for, \
             either the pipeline has too many/few register stages \
             or the spec is wrong."
      | none =>
        logInfoAt impl
          m!"💡 No nearby latency (0..{maxProbe - 1}) makes `{implName}` \
             match `{specName}`. The implementation is likely functionally \
             incorrect, not just mis-timed — see the counterexample above."
    else
      logInfoAt impl m!"✅ verified: `{thmName}` — {label}"

end Sparkle.Verification.Equivalence
