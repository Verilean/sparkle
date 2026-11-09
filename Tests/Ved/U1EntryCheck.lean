import Tools.VedU1Entry

/-!
# Checks for the U1 entry slice (`Tools/VedU1Entry.lean`)

Records, kept apart:
* ENTRY RUNS: `#ved_u1 d` (one `synthesizeCombinational` call per run, kernel,
  strict audit), pinned with `#guard_msgs`;
* CONTROLS through the checker `checkU1` (the entry's own checker with ONE
  piece substituted: the statement's constant, the module, or the proof),
  each pinned as a refusal at a named stage through ONE helper
  (`expectRefused stage absent act`), which after EVERY refusal also checks
  that the names in `absent` (the checker's four constants for that base) are
  not in the environment;
* KERNEL FACTS: `theorem`s refuting the substituted statements (closed
  witness runs, `decide`/`rfl`, no `native_decide`).

Declarations are written the way the corpus writes such circuits
(`Signal.register init x`, cf. Tests/TestCircuits.lean).
-/

namespace Tests.Ved.U1EntryCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

/-! ## Declarations -/

/-- The slice's declaration: a one-register delay of an 8-bit input. -/
def delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x

/-- Same type, a different meaning: the identity. -/
def ident8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := x

/-- Same type, another init (another declaration's artifact for the reuse controls). -/
def delay8k (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 5#8 x

/-- Same type and the SAME meaning as `delay8`, another name. -/
def delay8b (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x

/-- A one-register machine whose output is NOT the register (`reg + 1`):
outside the slice's proof script. -/
def inc8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (· + 1#8) <$> Signal.register 0#8 x

/-- Two output projections (refused: multi-output naming unconfirmed). -/
def pair8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) :=
  (fun v => (v, v)) <$> Signal.register 0#8 x

/-! ## 1. Entry runs (accepted) -/

/--
info: VED U1 OK Tests.Ved.U1EntryCheck.delay8.ved_u1: [Classical.choice, Quot.sound, propext]
{ name := "Tests.Ved.U1EntryCheck.delay8",
  parameters := [],
  inputs := [{ name := "_gen_x", ty := Sparkle.IR.Type.HWType.bitVector 8 },
             { name := "clk", ty := Sparkle.IR.Type.HWType.bit },
             { name := "rst", ty := Sparkle.IR.Type.HWType.bit }],
  outputs := [{ name := "out", ty := Sparkle.IR.Type.HWType.bitVector 8 }],
  wires := [{ name := "_gen_x", ty := Sparkle.IR.Type.HWType.bitVector 8 },
            { name := "_gen_out", ty := Sparkle.IR.Type.HWType.bitVector 8 }],
  body := [Sparkle.IR.AST.Stmt.register
             "_gen_out"
             "clk"
             ("rst", Sparkle.IR.Type.ResetKind.synchronous)
             (Sparkle.IR.AST.Expr.ref "_gen_x")
             0,
           Sparkle.IR.AST.Stmt.assign "out" (Sparkle.IR.AST.Expr.ref "_gen_out")],
  assertions := [],
  isPrimitive := false }
-/
#guard_msgs in
#ved_u1 delay8

-- the registered statement is over the ORIGINAL constant `delay8`
example : U1Stmt delay8.ved_contract delay8.ved_mod delay8 := delay8.ved_u1

/-- info: statement constant: Tests.Ved.U1EntryCheck.delay8 -/
#guard_msgs in
run_meta do
  let ty := (← getConstInfo ``delay8.ved_u1).type
  match ty.getAppFn, ty.getAppArgs with
  | .const ``U1Stmt _, #[.const c _, .const mo _, .const f _] =>
    unless c == ``delay8.ved_contract && mo == ``delay8.ved_mod do throwError "unexpected {ty}"
    logInfo m!"statement constant: {f}"
  | _, _ => throwError "unexpected {ty}"

-- the other declarations of the same type, each with ITS OWN module (accepted:
-- the identity's own module is the identity, so its statement is true)
#guard_msgs (drop info) in
#ved_u1 ident8
#guard_msgs (drop info) in
#ved_u1 delay8k
#guard_msgs (drop info) in
#ved_u1 delay8b

/-! ## Control helpers -/

/-- The module a previous entry run registered (its closed term evaluated). -/
def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

/-- The constants the checker registers for `base` (they must be absent
after a refusal: `checkU1` restores the state it saved at its own start). -/
def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

/-- None of `absent` is in the environment. -/
def assertClean (absent : List Name) : TermElabM Unit := do
  let env ← getEnv
  for n in absent do
    if env.contains n then throwError "left behind: {n}"

/-- THE refusal helper, used for every refusal control: `act` must be refused
at `stage` (a `VED U1 REFUSED … [stage]` error), and afterwards none of
`absent` may be in the environment.  Logs `refused [stage], clean`. -/
def expectRefused (stage : String) (absent : List Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  assertClean absent
  logInfo m!"refused [{stage}], clean"

/-! ## 2. Same type, different meaning (the identity into the delay's statement) -/

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlIdentIntoDelay) do
  discard <| checkU1 ``delay8 `ctlIdentIntoDelay ``ident8 (← modOf ``delay8) .generated

-- … and the delay into the identity's statement
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlDelayIntoIdent) do
  discard <| checkU1 ``ident8 `ctlDelayIntoIdent ``delay8 (← modOf ``ident8) .generated

/-- An input stream: `x` is 1 at every cycle, everything else 0. -/
def ones : Nat → String → Nat := fun _ n => if n = "_gen_x" then 1 else 0

theorem ones_ok : InputsOk delay8.ved_contract delay8.ved_mod ones := by
  refine ⟨fun t p hp => ?_, fun t kr hkr => ?_⟩
  · have h : delay8.ved_contract.dataInputs = [⟨"_gen_x", .bitVector 8⟩] := by decide
    rw [h] at hp
    simp only [List.mem_singleton] at hp
    subst hp
    have hw : declWidth delay8.ved_mod "_gen_x" = 8 := by decide
    show ones t "_gen_x" < 2 ^ declWidth delay8.ved_mod "_gen_x"
    rw [hw]; simp [ones]
  · have h : delay8.ved_contract.clkRst = some ("clk", "rst") := by decide
    rw [h] at hkr
    cases hkr
    show ones t "rst" = 0
    simp [ones]

theorem out_mem (c : Contract) (h : c.outputs = [⟨"out", .bitVector 8⟩]) :
    (⟨"out", .bitVector 8⟩ : Port) ∈ c.outputs := by
  rw [h]; exact List.mem_singleton_self _

/-- KERNEL: the full expected statement with the delay's module and contract
does NOT hold for the identity (cycle 0: the register gives 0, `x` is 1). -/
theorem ident_not_delay : ¬ U1Stmt delay8.ved_contract delay8.ved_mod ident8 :=
  not_u1_of_not_outputs <|
    not_outputs_of_witness _ _ _ delay8.ved_mod.body (by decide) (by decide) ones ones_ok 1 0 (by decide) ⟨"out", .bitVector 8⟩
      (out_mem _ (by decide))
      _ rfl _ rfl (by decide)

/-! ## 3. Mutated modules against the real declaration -/

/-- The delay's module with the register init changed to 5. -/
def mutInit (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r i _ => .register o c r i 5
      | s => s }

/-- The delay's module with the output reading the INPUT instead of the
register (main's delay8 has no concat; the poc-era mutation, the concat's low
field, would be a no-op here). -/
def mutOut (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign "out" _ => .assign "out" (.ref "_gen_x")
      | s => s }

/-- The delay's module with the output port widened to 9 bits. -/
def mutWidth (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with outputs := m.outputs.map fun p => { p with ty := .bitVector 9 } }

/-- The delay's module with the concat's constant-free shape changed: the
register fed from a constant 3 instead of `x`. -/
def mutConst (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r _ i => .register o c r (.const 3 8) i
      | s => s }

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlInit) do
  discard <| checkU1 ``delay8 `ctlInit ``delay8 (mutInit (← modOf ``delay8)) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlOut) do
  discard <| checkU1 ``delay8 `ctlOut ``delay8 (mutOut (← modOf ``delay8)) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlWidth) do
  discard <| checkU1 ``delay8 `ctlWidth ``delay8 (mutWidth (← modOf ``delay8)) .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlConst) do
  discard <| checkU1 ``delay8 `ctlConst ``delay8 (mutConst (← modOf ``delay8)) .generated

/-- The init mutation as a constant (the same value `mutInit` gives). -/
def mInit5 : Sparkle.IR.AST.Module :=
  { name := "Tests.Ved.U1EntryCheck.delay8",
    inputs := [⟨"_gen_x", .bitVector 8⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩],
    outputs := [⟨"out", .bitVector 8⟩],
    wires := [⟨"_gen_x", .bitVector 8⟩, ⟨"_gen_out", .bitVector 8⟩],
    body := [.register "_gen_out" "clk" ("rst", .synchronous) (.ref "_gen_x") 5,
             .assign "out" (.ref "_gen_out")] }

/-- info: mInit5 = mutInit delay8's module -/
#guard_msgs in
run_cmd liftTermElabM do
  unless decide (mInit5 = mutInit (← modOf ``delay8)) do throwError "differs"
  logInfo "mInit5 = mutInit delay8's module"

def cInit5 : Contract := contractOf (ved_table% delay8) ["out"] (some ("clk", "rst")) mInit5

/-- An input stream: everything 0. -/
def zeros : Nat → String → Nat := fun _ _ => 0

theorem zeros_ok : InputsOk cInit5 mInit5 zeros :=
  ⟨fun _ _ _ => Nat.two_pow_pos _, fun _ _ _ => rfl⟩

/-- KERNEL: the init-5 module does not implement `delay8` (cycle 0: 5 ≠ 0). -/
theorem init5_not_delay : ¬ U1Stmt cInit5 mInit5 delay8 :=
  not_u1_of_not_outputs <|
    not_outputs_of_witness _ _ _ mInit5.body (by decide) (by decide) zeros zeros_ok 1 0 (by decide) ⟨"out", .bitVector 8⟩
      (out_mem _ (by decide))
      _ rfl _ rfl (by decide)

/-! ## 4. Another declaration's proof or artifact -/

-- another declaration's theorem as the proof of delay8's statement
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlProofK) do
  discard <| checkU1 ``delay8 `ctlProofK ``delay8 (← modOf ``delay8) (.term (mkCIdent ``delay8k.ved_u1))

-- … even of a declaration with the same meaning (its module name differs)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlProofB) do
  discard <| checkU1 ``delay8 `ctlProofB ``delay8 (← modOf ``delay8) (.term (mkCIdent ``delay8b.ved_u1))

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlProofI) do
  discard <| checkU1 ``delay8 `ctlProofI ``delay8 (← modOf ``delay8) (.term (mkCIdent ``ident8.ved_u1))

-- another declaration's ARTIFACT (delay8k's module, init 5) for delay8
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlArtK) do
  discard <| checkU1 ``delay8 `ctlArtK ``delay8 (← modOf ``delay8k) .generated

-- the identity's artifact for delay8
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames `ctlArtI) do
  discard <| checkU1 ``delay8 `ctlArtI ``delay8 (← modOf ``ident8) .generated

-- NOT a refusal, and NOT a defect (reviewer's naming ruling): the artifact of
-- `delay8b` (same meaning, another module name) with a NEW generated proof is
-- accepted for `delay8`.  `checkU1` verifies "this `m` has this declaration's
-- meaning"; the contract reads the module name from `m`, and no
-- module-name = declaration-name condition is part of the IR meaning contract
-- (a naming rule is a separate specification for file-output / hierarchy
-- consumers).  Three things are recorded separately:
--   (a) an OLD proof reused for another declaration is refused
--       (`ctlProofB` / `ctlProofK` / `ctlProofI` above);
--   (b) a NEW correct proof for a same-meaning artifact is accepted (here);
--   (c) the production entry `vedU1Entry` keeps the artifact of the same run:
--       it passes the `m` its one `synthesizeCombinational` call returned to `checkU1`
--       unsubstituted and returns that `m` (by construction; `checkU1`'s
--       `artifact` stage checks the registered `ved_mod` denotes it).  That is a
--       property of the entry, separate from what `checkU1` verifies.
/-- info: accepted ctlArtB.ved_u1 -/
#guard_msgs in
run_cmd liftTermElabM do
  let t ← checkU1 ``delay8 `ctlArtB ``delay8 (← modOf ``delay8b) .generated
  logInfo m!"accepted {t}"

/-! ## 5. Multi-output: refused before synthesis -/

/--
error: VED U1 REFUSED Tests.Ved.U1EntryCheck.pair8 [multi-output]: 2 output projections; the synthesizer's multi-output port naming is unconfirmed, refused (v1: one output)
-/
#guard_msgs in
#ved_u1 pair8

-- the same refusal through the shared helper (checks the names after it)
/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" (checkerNames ``pair8) do
  discard <| vedU1Entry ``pair8

/-! ## 6. Scope: a body outside the slice's script is refused (not accepted) -/

-- `inc8`'s statement may well be true; the refusal is a COVERAGE limit of the
-- slice's generated script (no invariant for a register that is not the
-- output), not a counterexample.  What is checked: no fallback, and none of
-- the checker's constants for `inc8` is left (the helper).  Side effects of
-- `synthesizeCombinational` itself (which ran before `checkU1`) are not rolled back and
-- not checked here.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" (checkerNames ``inc8) do
  discard <| vedU1Entry ``inc8

/-! ## 7. Strict audit: a `native_decide` proof is refused -/

-- A proof of the FULL statement that is correct and kernel-accepted, but whose
-- term carries a `native_decide` fact (`Lean.ofReduceBool` in the reachable
-- closure).  (`native_decide` cannot run on the contract's own clauses here:
-- `ved_mod` / `ved_contract` are kernel-only definitions, not compiled.)
/-- info: refused [audit], clean -/
#guard_msgs in
run_cmd expectRefused "audit" (checkerNames `ctlNative) do
  let stx ← `((fun (_ : (2 : Nat) + 2 = 4) => delay8.ved_u1) (by native_decide))
  discard <| checkU1 ``delay8 `ctlNative ``delay8 (← modOf ``delay8) (.term stx)

end Tests.Ved.U1EntryCheck
