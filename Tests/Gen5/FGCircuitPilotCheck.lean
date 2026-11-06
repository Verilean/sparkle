import Tools.ShippingFGCircuitRoots
set_option autoImplicit false
-- FG circuit pilot S1 check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md.

/-! # FGCircuitPilotCheck

1. structural match of the conclusion types and of the root theorems' statements;
2. non-vacuity / negative controls (a reverse-defined denotation is refused structurally; observations distinguish meanings; unknown constants and
   parameters are refused; `Post := False` is refuted);
3. meta checks that tie the quoted source to the actual environment (the one non-kernel link, named `RootInEnv`) and the boundary row `bvAbbrevRow`
   to the declarations;
4. every primitive-table proof exists; `#print axioms` and an axiom audit (standard axioms only);
5. the list of remaining named hypotheses. -/
namespace Tests.Gen5.FGCircuitPilotCheck
open Lean Meta Elab Command Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Sparkle.Tests.SignalLoopTest

/-! ## 1. Structural match -/

-- `SourceDenotes` is defined from the environment's declaration and `CD` ONLY: it has no package / module / IR argument.
example : @SourceDenotes = fun env source params sh m =>
    params = [] ∧ ∃ ci : ConstantInfo, env.find? source = some ci ∧ shapeOf ci = some sh ∧ CircCV env source sh.Ty m := rfl
example : @CircCV = fun env X α v =>
    ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CD [] d.value α v := rfl
-- the conclusion: Post-witness, then (for every raw) source meaning, package from the generated table, the TopShips contract, the observation equality
example {ι : Type} {dom : ι → DomainConfig} : @FGCircuitConclusion ι dom = fun env P Post declName parameters b D =>
    (∃ raw, Post b raw) ∧
    ∀ raw, Post b raw → ∃ (sh : SigShape) (m : sh.Ty) (p : Pkg ι dom) (n : Nat),
      P declName = some p ∧ SourceDenotes env declName parameters sh m ∧ (p.decl = declName ∧ TopShips p n declName b raw D) ∧
        (ShapeMatches sh p.d p.kD ∧ ∀ i bools bits, sh.obs (dom := dom) m i bools bits = p.src i bools bits) := rfl
-- the roots' statements: the source meaning is `X` itself; the trace's source is the observation of THAT meaning
example : @counterLoop_root = @counterLoop_root := rfl
#check @counterLoop_root
#check @shift4Loop_root
#check @counterEnableLoop_root
#check @arbiterSignal_root
#check @counterLoop_ships
#check @arbiterSignal_ships
#check @fgCircuit_of_H
-- the denoted value is the Lean constant (statement shape of the three kernel derivations)
example : CD [] counterLoopValue (Signal defaultDomain (BitVec 8)) counterLoop := counterLoop_cd
example : CD [] shift4LoopValue (Signal defaultDomain (BitVec 8) → Signal defaultDomain (BitVec 8)) shift4Loop := shift4Loop_cd
example : CD [] counterEnableLoopValue (Signal defaultDomain Bool → Signal defaultDomain (BitVec 8)) counterEnableLoop := counterEnableLoop_cd
example : CD [] arbiterValue ((D : DomainConfig) → Signal D Bool → Signal D Bool → Signal D (BitVec 2))
    (fun D => @Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D) := arbiterSignal_cd

/-! ## 2. Negative controls -/

-- (a) a parametric source is refused at S1 (`params = []`)
example (env : Environment) (X : Name) (sh : SigShape) (m : MonoTy sh) (p : String × Nat) (ps : List (String × Nat)) :
    ¬ SourceDenotesMono env X (p :: ps) sh m := fun h => by cases h.1
example (env : Environment) (X : Name) (sh : SigShape) (m : sh.Ty) (p : String × Nat) (ps : List (String × Nat)) :
    ¬ SourceDenotes env X (p :: ps) sh m := fun h => by cases h.1
-- (b) `Post := False` cannot satisfy the conclusion
example {ι : Type} {dom : ι → DomainConfig} (env : Environment) (P : Pkgs ι dom) (X : Name) (ps : List (String × Nat))
    (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) :
    ¬ FGCircuitConclusion env P (fun _ _ => False) X ps b D := fun h => by obtain ⟨raw, hr⟩ := h.1; exact hr
-- (c) the observation equality is selective: a wrong meaning (a constant zero stream) is NOT observationally equal to the shift register on a
--     non-zero input, so an `ObservationsEqualMono` for the real meaning refuses it for the same package
private def bools0 : Nat → Signal defaultDomain Bool := fun _ => Signal.pure false
private def bits1 : (j n : Nat) → Signal defaultDomain (BitVec n) := fun _ n => Signal.pure (BitVec.ofNat n 1)
private theorem shift4_obs_ne :
    monoObs shShift4 shift4Loop bools0 bits1 ≠ monoObs shShift4 (fun _ => Signal.pure 0#8) bools0 bits1 := by
  intro h
  have h4 : ((shift4Loop (Signal.pure (BitVec.ofNat 8 1))).val 4).toNat = ((Signal.pure 0#8 : Signal defaultDomain (BitVec 8)).val 4).toNat :=
    congrFun (List.cons.inj h).1 4
  revert h4
  decide
theorem wrong_meaning_refused {ι : Type} (i : ι) (p : Pkg ι (fun _ => defaultDomain))
    (h : ObservationsEqualMono shShift4 shift4Loop p) : ¬ ObservationsEqualMono shShift4 (fun _ => Signal.pure 0#8) p :=
  fun h' => shift4_obs_ne ((h.2 i bools0 bits1).trans (h'.2 i bools0 bits1).symm)
-- (d) `CD` refuses a constant that is not a row (no rule, in particular no unfolding of an unknown name)
example (α : Type) (v : α) : ¬ CD [] (.const `Nat.add []) α v := by
  intro h
  cases h
  case domDefault he => exact absurd (Expr.const.inj he).1 (by decide)
  case boolInhabited he => exact absurd (Expr.const.inj he).1 (by decide)
  case bvAbbrev c n v hrow he =>
    have hc : `Nat.add = c := (Expr.const.inj he).1
    subst hc
    have hn : bvAbbrevRow `Nat.add = none := by rfl
    rw [hn] at hrow
    cases hrow
  all_goals contradiction
-- (e) a reverse-defined denotation would be satisfiable for ANY package, so it carries no information: `ObservationsEqualMono` alone (no `CD`) holds
--     for the meaning read off the package's own streams whenever it is a function of the inputs; `SourceDenotes` additionally demands `CD` on the
--     declaration's value, which the wrong meaning above cannot satisfy together with the observation equality (it needs `CD` functionality, S2).

/-! ## 3. Meta checks: the quoted source IS the environment's value (the link behind `RootInEnv`), the boundary rows are the literals -/

run_cmd liftTermElabM do
  let chk (n : Name) (ty val : Lean.Expr) : MetaM Unit := do
    let ci ← getConstInfo n
    unless ci.levelParams.isEmpty do throwError "{n}: has level parameters"
    unless ci.type == ty do throwError "{n}: quoted type differs from the environment"
    unless ci.value! == val do throwError "{n}: quoted value differs from the environment"
  chk ``counterLoop counterLoopType counterLoopValue
  chk ``shift4Loop shift4LoopType shift4LoopValue
  chk ``counterEnableLoop counterEnableLoopType counterEnableLoopValue
  chk ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue
  -- boundary rows: each abbreviation is the literal `k#2`
  for (nm, k) in [(`stIdle, 0), (`stGrantA, 1), (`stGrantB, 2)] do
    let ci ← getConstInfo (privAbbrev nm)
    unless ci.value! == eBVLit 2 k do throwError "{nm}: not the literal {k}#2"
    unless ci.type == eBV 2 do throwError "{nm}: type is not BitVec 2"
  logInfo "FGCIRCUIT META: 4 quoted roots equal the environment; 3 abbreviation rows equal their literals"

/-! ## 4. Primitive table: every listed proof exists; axiom audit -/

run_cmd liftTermElabM do
  let env ← getEnv
  let mut n : Nat := 0
  for row in primTable do
    unless env.contains row.decl do throwError "primitive {row.decl} does not exist"
    for pr in row.proofs do
      unless env.contains pr do throwError "{row.decl}: proof {pr} does not exist"
      n := n + 1
  logInfo m!"FGCIRCUIT PRIMS: {primTable.length} rows, {n} proof references, all exist"

run_cmd liftTermElabM do
  let names : List Name := [``counterLoop_cd, ``shift4Loop_cd, ``counterEnableLoop_cd, ``arbiterSignal_cd,
    ``counterLoop_root, ``shift4Loop_root, ``counterEnableLoop_root, ``arbiterSignal_root,
    ``counterLoop_ships, ``shift4Loop_ships, ``counterEnableLoop_ships, ``arbiterSignal_ships, ``fgCircuit_of_H, ``conclusion_of_declConnect,
    ``ir_const_agrees, ``ir_add_agrees, ``ir_mux_agrees, ``ir_register_step_rst0, ``ir_register_reset_value,
    ``loop_val_zero, ``loop_register_map_succ, ``register_val_zero, ``register_val_succ, ``mux_val, ``addBV_val, ``pure_val,
    ``wrong_meaning_refused,
    ``Sparkle.Tests.SignalLoopTest.counterLoop.machine_sound, ``Sparkle.Tests.SignalLoopTest.shift4Loop.machine_sound,
    ``Sparkle.Tests.SignalLoopTest.counterEnableLoop.machine_sound, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machine_sound]
  for nm in names do
    let axs ← Lean.collectAxioms nm
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT AXIOMS: {names.length} names, standard axioms only (propext, Classical.choice, Quot.sound)"

#print axioms counterLoop_root
#print axioms shift4Loop_root
#print axioms counterEnableLoop_root
#print axioms arbiterSignal_root
#print axioms arbiterSignal_ships
#print axioms fgCircuit_of_H
#print axioms wrong_meaning_refused

end Tests.Gen5.FGCircuitPilotCheck
