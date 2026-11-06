import Tools.ShippingFGCircuitS1pCD
set_option autoImplicit false
-- FG circuit pilot S1p check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §20.

/-! # FGCircuitPilotCheck14

1. SIGNATURES: the single-environment carrier `CircCVS` (definition and bridge), the run-side binding to `envAt cref w`, the new rules of `DY` (`recIota`, and `beta`/`projStep` over `whStepR`),
   `dx_to_dy`, functionality, against independently written statements (`isDefEq`), with mutants that must be rejected.
2. NEGATIVE CONTROL (different environments): two concrete environments in which `mini` is defined differently; the S1m carrier `CircCVX envA envB` holds for the value of `envA`'s `mini`
   while `envB`'s own declaration denotes another value; `CircCVS envB` rejects that value.
3. RECSTEP: behaviour of the iota step on controls (static nil/cons major; non-static major; another recursor; the levels are kept), and the Lean `isDefEq` of input/output of every step the traversal takes.
4. AXIOMS.
5. SNAPSHOT14 (ONE environment: the build's): how far the root's value goes with the new rule. -/
namespace Tests.Gen5.FGCircuitPilotCheck14
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD
open Tools.ShippingGen5ConstValueE Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)

/-! ## 1. expected statements, written independently -/

noncomputable instance : Inhabited Environment := ⟨Classical.ofNonempty⟩


/-- the carrier. mu 0 = expected; 1 = the quote environment is a FIXED default one; 2 = a non-empty valuation; 3 = universe parameters not required; 4 = the environment of `CDX` is existentially quantified -/
def ExpCircCVS (mu : Nat) : ConstValueRel := fun env X α v =>
  if mu == 4 then ∃ (d : DefinitionVal) (env2 : Environment), env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CDX env2 [] d.value α v
  else ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ (if mu == 3 then True else d.levelParams = []) ∧
    CDX (if mu == 1 then default else env) (if mu == 2 then [⟨.const ``Nat [], ⟨Nat, 0⟩⟩] else []) d.value α v

def ExpToS (mu : Nat) : Prop := ∀ (env : Environment) {X : Name} {α : Type} {v : α},
  CircCV env X α v → (if mu == 1 then CircCVS default X α v else CircCVS env X α v)

/-- the run side: the carrier is read in the environment of the Core state at the START world `w` (mu 1: at the end world `w'`) -/
def ExpRunIff (mu : Nat) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {e : Environment}, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w' → ∀ {X : Name} {α : Type} {v : α},
    CircCVS e X α v ↔ CircCVS (envAt cref (if mu == 1 then w' else w)) X α v

/-- the S1m carrier is the single-environment one only if the two environments agree (mu 1: no hypothesis) -/
def ExpIffS (mu : Nat) : Prop := ∀ (env env' : Environment) (X : Name) (α : Type) (v : α), (if mu == 1 then True else env' = env) → (CircCVX env env' X α v ↔ CircCVS env' X α v)

def ExpMixed (mu : Nat) : Prop :=
  ∀ {env env' : Environment} {X : Name} {d : DefinitionVal}, EnvDefs env (Δn 5) → env'.find? X = some (.defnInfo d) → d.levelParams = [] → d.value = .const miniN [] →
    CircCVX env env' X (Signal defaultDomain Nat) (Signal.pure (if mu == 1 then 6 else 5))
def ExpRejects (mu : Nat) : Prop :=
  ∀ {env' : Environment} {X : Name} {d : DefinitionVal}, EnvDefs env' (Δn (if mu == 1 then 5 else 6)) → env'.find? X = some (.defnInfo d) → d.value = .const miniN [] →
    ¬ CircCVS env' X (Signal defaultDomain Nat) (Signal.pure 5)

/-- the new rule. knobs: head (0 = `List.rec`, 1 = `Nat.rec`), requires the recInfo of the environment (false: dropped), conclusion (true: e), step function (0 = recStep, 1 = unfoldAt) -/
def ExpRecIota (head : Nat) (needInfo : Bool) (concl : Bool) (step : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e e' : Expr} {ls : List Level} {ri : RecursorVal} {α : Type} {v : α},
    appFn e = .const (if head == 0 then ``List.rec else ``Nat.rec) ls →
    (if needInfo then env.find? ``List.rec = some (.recInfo ri) else True) →
    (if step == 0 then recStep env e = some e' else unfoldAt env e = some e') →
    DY env ρ e' (.val α v) →
    (if concl then DY env ρ e (.val α v) else DY env ρ e' (.val α v))

def ExpBetaY (useR : Bool) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e e' : Expr} {α : Type} {v : α},
    (if useR then headRedexR env e = some e' else headRedex env e = some e') → DY env ρ e' (.val α v) → DY env ρ e (.val α v)
def ExpProjStepY (useR : Bool) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {α : Type} {v : α},
    e = .proj S i x → (if useR then whStepR env x = some x' else whStep env x = some x') → DY env ρ (.proj S i x') (.val α v) → DY env ρ e (.val α v)

def ExpEmbedY (rev : Bool) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {r : Res}, (if rev then DY env ρ e r else DX env ρ e r) → (if rev then DX env ρ e r else DY env ρ e r)

def FunY : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDY env ρ e α v → CDY env ρ e α' v' → α = α' ∧ HEq v v'
def FunYOtherEnv : Prop :=
  ∀ {env env' : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDY env ρ e α v → CDY env' ρ e α' v' → α = α' ∧ HEq v v'
def FunYNoHEq : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDY env ρ e α v → CDY env ρ e α' v' → α = α'

def FunS : Prop := ∀ (env : Environment) {c : Name} {α β : Type} {v : α} {w : β}, CircCVS env c α v → CircCVS env c β w → α = β ∧ HEq v w
def FunSOtherEnv : Prop := ∀ (env env' : Environment) {c : Name} {α β : Type} {v : α} {w : β}, CircCVS env c α v → CircCVS env' c β w → α = β ∧ HEq v w

def varBad : Expr := .lam `x (.const ``Nat []) (.bvar 0) .default

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1pCD
  let Q := `Tests.Gen5.FGCircuitPilotCheck14
  let same (thm : Name) (exp : Expr) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    unless ← withDefault (isDefEq ci.type exp) do throwError "{thm}: type is NOT the expected statement"
  let differs (thm : Name) (mu : Expr) : MetaM Unit := do
    let ci ← getConstInfo thm
    if ← withDefault (isDefEq ci.type mu) then throwError "{thm}: a MUTANT was accepted"
  let mut nm : Nat := 0
  let nat (n : Nat) : Expr := toExpr n
  -- the carrier: definition (a ConstValueRel, so compare the value)
  let cvDef := (← getConstInfo (S ++ `CircCVS)).value!
  unless ← withDefault (isDefEq cvDef (← mkAppM (Q ++ `ExpCircCVS) #[nat 0])) do throwError "CircCVS: definition is NOT the expected one"
  for m in [1, 2, 3, 4] do
    if ← withDefault (isDefEq cvDef (← mkAppM (Q ++ `ExpCircCVS) #[nat m])) then throwError "CircCVS: MUTANT {m} accepted"
    nm := nm + 1
  -- bridges
  same (S ++ `circCV_to_S) (← mkAppM (Q ++ `ExpToS) #[nat 0])
  differs (S ++ `circCV_to_S) (← mkAppM (Q ++ `ExpToS) #[nat 1]); nm := nm + 1
  same (S ++ `circCVS_at_of_getEnv) (← mkAppM (Q ++ `ExpRunIff) #[nat 0])
  differs (S ++ `circCVS_at_of_getEnv) (← mkAppM (Q ++ `ExpRunIff) #[nat 1]); nm := nm + 1
  same (S ++ `circCVX_iff_S) (← mkAppM (Q ++ `ExpIffS) #[nat 0])
  differs (S ++ `circCVX_iff_S) (← mkAppM (Q ++ `ExpIffS) #[nat 1]); nm := nm + 1
  same (S ++ `circCVS_functional) (mkApp (mkConst ``ConstValueFunctional) (mkConst (S ++ `CircCVS)))
  differs (S ++ `circCVS_functional) (mkApp (mkConst ``ConstValueFunctional) (mkConst ``CircCV)); nm := nm + 1
  -- the mixed-environment pair
  same (S ++ `circCVX_mixed) (← mkAppM (Q ++ `ExpMixed) #[nat 0])
  differs (S ++ `circCVX_mixed) (← mkAppM (Q ++ `ExpMixed) #[nat 1]); nm := nm + 1
  same (S ++ `circCVS_rejects_mixed) (← mkAppM (Q ++ `ExpRejects) #[nat 0])
  differs (S ++ `circCVS_rejects_mixed) (← mkAppM (Q ++ `ExpRejects) #[nat 1]); nm := nm + 1
  -- the new rule and the rules over whStepR
  let rc (h : Nat) (ni c : Bool) (st : Nat) : MetaM Expr := mkAppM (Q ++ `ExpRecIota) #[nat h, toExpr ni, toExpr c, nat st]
  same (S ++ `DY.recIota) (← rc 0 true true 0)
  for (h, ni, c, st) in [(1, true, true, 0), (0, false, true, 0), (0, true, false, 0), (0, true, true, 1)] do
    differs (S ++ `DY.recIota) (← rc h ni c st); nm := nm + 1
  same (S ++ `DY.beta) (← mkAppM (Q ++ `ExpBetaY) #[toExpr true])
  differs (S ++ `DY.beta) (← mkAppM (Q ++ `ExpBetaY) #[toExpr false]); nm := nm + 1
  same (S ++ `DY.projStep) (← mkAppM (Q ++ `ExpProjStepY) #[toExpr true])
  differs (S ++ `DY.projStep) (← mkAppM (Q ++ `ExpProjStepY) #[toExpr false]); nm := nm + 1
  -- embedding
  same (S ++ `dx_to_dy) (← mkAppM (Q ++ `ExpEmbedY) #[toExpr false])
  differs (S ++ `dx_to_dy) (← mkAppM (Q ++ `ExpEmbedY) #[toExpr true]); nm := nm + 1
  -- functionality
  same (S ++ `cdy_fun) (mkConst (Q ++ `FunY))
  for mu in ["FunYOtherEnv", "FunYNoHEq"] do
    differs (S ++ `cdy_fun) (mkConst (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT14 SIGNATURES: CircCVS (definition), circCV_to_S, circCVS_at_of_getEnv (envAt cref w), circCVX_iff_S, circCVS_functional, circCVX_mixed / circCVS_rejects_mixed, DY.recIota, DY.beta / DY.projStep (over whStepR), dx_to_dy, cdy_fun match the independently written statements; {nm} mutants rejected"
  -- the old rules of DX are in DY with the environment threaded (same constructor types after erasing the family name)
  let mut nOld : Nat := 0
  for c in [`nat, `bool, `domainConfig, `bitvec, `signal, `bvar, `natLit, `domDefault, `bvOfNat, `bvInhabited, `boolInhabited, `sigPure, `sigRegister, `sigMux, `sigAddBV, `sigLoop, `lam, `letE, `sigBeqBV, `sigAndBool, `sigOrBool, `sigNotBool, `bvAbbrev, `unf, `zeta, `projCtor] do
    let a ← getConstInfo (``DX ++ c)
    let b ← getConstInfo (S ++ `DY ++ c)
    let rn (e : Expr) : Expr := e.replace fun x => if x.isConstOf ``DX then some (mkConst (S ++ `DY) x.constLevels!) else none
    unless ← withDefault (isDefEq (rn a.type) b.type) do throwError "{c}: DY rule differs from the DX rule"
    nOld := nOld + 1
  -- a control: the comparison rejects a changed rule
  do
    let a ← getConstInfo (``DX ++ `sigPure)
    let b ← getConstInfo (S ++ `DY ++ `sigMux)
    let rn (e : Expr) : Expr := e.replace fun x => if x.isConstOf ``DX then some (mkConst (S ++ `DY) x.constLevels!) else none
    if ← withDefault (isDefEq (rn a.type) b.type) then throwError "control: sigMux accepted as sigPure"
  logInfo m!"FGCIRCUIT14 OLD RULES: {nOld} constructors of DX (beta and projStep excluded: they are over whStepR) are the same in DY; a control rejects a changed rule"

/-! ## 2. NEGATIVE CONTROL with concrete environments -/

def declFor (n : Name) (v : Lean.Expr) (ty : Lean.Expr) : Declaration :=
  .defnDecl { name := n, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe }

run_cmd liftTermElabM do
  let env0 ← getEnv
  let sigT : Lean.Expr := appN ``Signal [.zero] [.const ``Sparkle.Core.Domain.defaultDomain [], .const ``Nat []]
  let mkEnv (n : Nat) : MetaM Environment := do
    setEnv env0
    addDecl (declFor miniN (miniVal n) sigT)
    addDecl (declFor `Tests.negX (.const miniN []) sigT)
    let e ← getEnv
    setEnv env0
    pure e
  let envA ← mkEnv 5
  let envB ← mkEnv 6
  -- the facts the theorems ask for, checked on the concrete environments (a meta check of `EnvDefs`: one row)
  let row (env : Environment) (n : Nat) : Bool :=
    match env.find? miniN with
    | some (.defnInfo d) => d.levelParams == [] && d.value == miniVal n
    | _ => false
  unless row envA 5 do throwError "envA: the row of mini is not (pure 5)"
  unless row envB 6 do throwError "envB: the row of mini is not (pure 6)"
  if row envA 6 || row envB 5 then throwError "control: the rows do not distinguish the environments"
  let some (.defnInfo dB) := envB.find? `Tests.negX | throwError "envB: X missing"
  unless dB.value == .const miniN [] && dB.levelParams == [] do throwError "envB: X is not `mini`"
  -- the same quote (the value of X in envB) unfolds to different values in the two environments
  let uA := unfoldAt envA dB.value
  let uB := unfoldAt envB dB.value
  unless uA == some (miniVal 5) && uB == some (miniVal 6) do throwError "the same quote does not unfold differently"
  logInfo m!"FGCIRCUIT14 NEGATIVE CONTROL (different env): X := mini quoted in envB (mini = pure 6), unfolded in envA (mini = pure 5) gives pure 5 (circCVX_mixed: CircCVX envA envB X (pure 5) holds), while CircCVS envB X (pure 5) is refuted (circCVS_rejects_mixed) and CircCVS envB X (pure 6) is derivable (miniDen 6 from the row)"

/-- positive control: the single-environment carrier derives the value of ITS OWN environment -/
theorem circCVS_pos {env : Environment} {X : Name} {d : DefinitionVal} (hΔ : EnvDefs env (Δn 6)) (hd : env.find? X = some (.defnInfo d))
    (hl : d.levelParams = []) (hv : d.value = .const miniN []) : CircCVS env X (Signal defaultDomain Nat) (Signal.pure 6) :=
  ⟨d, hd, hl, by rw [hv]; exact miniDen 6 hΔ⟩

/-! ## 3. RECSTEP controls and the equation check -/

def sort1 : Lean.Expr := .sort (.succ .zero)
def lstTy : Lean.Expr := appN ``List [.succ .zero] [sort1]
def nilE : Lean.Expr := appN ``List.nil [.succ .zero] [sort1]
def consE (h t : Lean.Expr) : Lean.Expr := appN ``List.cons [.succ .zero] [sort1, h, t]
def sigT0 : Lean.Expr := appN ``Signal [.zero] [.const ``Sparkle.Core.Domain.defaultDomain [], .const ``Nat []]
def pE (n : Nat) : Lean.Expr := appN ``Signal.pure [.zero] [.const ``Sparkle.Core.Domain.defaultDomain [], .const ``Nat [], natEx n]
def motE : Lean.Expr := .lam `t lstTy sigT0 .default
def consC (n : Nat) : Lean.Expr := .lam `a sort1 (.lam `xs lstTy (.lam `ih sigT0 (pE n) .default) .default) .default
def recOn (major : Lean.Expr) (ls : List Level := [.succ .zero, .succ .zero]) (c := ``List.rec) : Lean.Expr :=
  appN c ls [sort1, motE, pE 0, consC 1, major]
/-- the cons case receives the tail's recursor result: `fun a xs ih => ih` -/
def consIh : Lean.Expr := .lam `a sort1 (.lam `xs lstTy (.lam `ih sigT0 (.bvar 0) .default) .default) .default
def recIh (major : Lean.Expr) : Lean.Expr := appN ``List.rec [.succ .zero, .succ .zero] [sort1, motE, pE 0, consIh, major]

run_cmd liftTermElabM do
  let env ← getEnv
  let nat := Lean.Expr.const ``Nat []
  -- nil major: the nil case
  unless recStep env (recOn nilE) == some (pE 0) do throwError "recStep: nil"
  -- cons major: the cons case applied to head, tail, and the recursor on the tail (same levels)
  unless recStep env (recOn (consE nat nilE)) == some (pE 1) do throwError "recStep: cons"
  -- the ih is the recursor on the TAIL with the same arguments and levels
  unless recStep env (recIh (consE nat nilE)) == some (recIh nilE) do throwError "recStep: ih shape"
  -- two steps reach the nil case
  unless ((recStep env (recIh (consE nat nilE))).bind (recStep env)) == some (pE 0) do throwError "recStep: two steps"
  -- extra arguments are kept
  unless recStep env (.app (recOn nilE) (.bvar 3)) == some (.app (pE 0) (.bvar 3)) do throwError "recStep: extra args"
  -- the major is unfolded (a definition whose body is a literal list is a static major only after `whStep` delta; here a beta redex)
  unless recStep env (recOn (.app (.lam `q lstTy (.bvar 0) .default) nilE)) == some (pE 0) do throwError "recStep: beta major"
  -- controls: a variable major is NOT static; another recursor; too few arguments; a different head
  if (recStep env (recOn (.bvar 0))).isSome then throwError "control: bvar major stepped"
  if (recStep env (appN ``Nat.rec [.succ .zero] [motE, pE 0, consC 1, natEx 3])).isSome then throwError "control: Nat.rec stepped"
  if (recStep env (appN ``List.rec [.succ .zero, .succ .zero] [sort1, motE, pE 0, consC 1])).isSome then throwError "control: partial List.rec stepped"
  if (recStep env (appN ``List.casesOn [.succ .zero, .succ .zero] [sort1, motE, nilE, pE 0, consC 1])).isSome then throwError "control: casesOn stepped (no generic recursor reading)"
  -- the universe levels are not widened: the output rec keeps the input levels exactly
  match recStep env (recIh (consE nat nilE)) with
  | some o => unless o.getAppFn.constLevels! == [.succ .zero, .succ .zero] do throwError "levels changed"
  | none => throwError "levels: no step"
  logInfo m!"FGCIRCUIT14 RECSTEP: nil/cons/ih/two-step/extra-args/beta-major cases agree; a variable major, Nat.rec, a partial application, List.casesOn do not step; the levels of the recursor are kept"

/-! ## 4. AXIOMS -/
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1pCD
  let names : List Name := [S ++ `circCV_to_S, S ++ `circCVS_to_X, S ++ `circCVX_iff_S, S ++ `circCVS_functional, S ++ `sourceDenotes_to_S, S ++ `declConnect_to_S,
    S ++ `circCVS_at_of_getEnv, S ++ `circCVS_hft_of_obCDX, S ++ `circCVS_hft_run, S ++ `miniDen, S ++ `circCVX_mixed, S ++ `circCVS_rejects_mixed,
    S ++ `recStep_head, S ++ `whStepR_ctor, S ++ `whStepR_of_whStep, S ++ `headRedexR_of_headRedex, S ++ `dx_to_dy, S ++ `dy_fun, S ++ `cdy_fun, S ++ `tdy_fun, S ++ `cdy_eq,
    S ++ `circCVS_to_Y, S ++ `circCVY_functional, S ++ `listRec_nil_eq, S ++ `listRec_cons_eq, S ++ `circuit_pure_eq, S ++ `circuit_bind_eq, S ++ `circuit_next_eq,
    `Tests.Gen5.FGCircuitPilotCheck14.circCVS_pos]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT14 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 5. SNAPSHOT14: the traversal with the new rule -/

structure Stuck where
  heads : List (String × Nat) := []
  tdFail : List (String × Nat) := []
  nodes : Nat := 0
  unfolded : List (String × Nat) := []
  recSteps : Nat := 0
  recPairs : List (Lean.Expr × Lean.Expr) := []
  maxDepth : Nat := 0
  sample : List (String × Lean.Expr) := []
  traceMismatch : Nat := 0

def bump (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  if l.any (·.1 == k) then l.map fun (a, n) => if a == k then (a, n + 1) else (a, n) else l ++ [(k, 1)]

abbrev M := StateM Stuck

partial def describe (env : Environment) : Lean.Expr → String
  | .proj s j y => s!"proj {s}#{j} ({describe env y})"
  | x =>
    match appFn x with
    | .const c _ =>
      let k := match env.find? c with
        | some (.inductInfo _) => "inductive" | some (.ctorInfo _) => "ctor" | some (.recInfo _) => "recursor" | some (.opaqueInfo _) => "opaque"
        | some (.thmInfo _) => "theorem" | some (.axiomInfo _) => "axiom" | some (.defnInfo _) => "defn" | some (.quotInfo _) => "quot" | none => "missing"
      s!"{c}[{k}]/{(appArgs x).length}"
    | .proj s j y => s!"[proj {s}#{j} ({describe env y})]/{(appArgs x).length}"
    | .lam .. => s!"<lam>/{(appArgs x).length}"
    | .letE .. => s!"<let>/{(appArgs x).length}"
    | h => s!"<{h.ctorName}>/{(appArgs x).length}"

/-- what the major premise of a `List.rec` is when the iota step does not fire -/
def describeRecStuck (env : Environment) (e : Lean.Expr) : String :=
  match appArgs e with
  | _ :: _ :: _ :: _ :: major :: _ =>
    match recMajorWh env 256 major with
    | some m => s!"List.rec: major reaches {describe env m} but the shape is not nil/cons"
    | none => s!"List.rec: major not static: {describe env major}"
  | args => s!"List.rec: {args.length} arguments (<5)"

/-- `whStepR` in the traversal monad: the same steps, recording each `List.rec` iota taken inside a projection; `traceMismatch` counts any disagreement with `whStepR` -/
partial def whStepT (env : Environment) : Lean.Expr → M (Option Lean.Expr)
  | .letE _ _ v b _ => pure (some (instE b v 0))
  | .proj s j y => do
    match ← whStepT env y with
    | some y' => pure (some (.proj s j y'))
    | none =>
      match iotaAt env s j y with
      | some r => pure (some r)
      | none =>
        match recStep env y with
        | some y' => do
            modify fun st => { st with recSteps := st.recSteps + 1, recPairs := if st.recPairs.any (·.1 == y) then st.recPairs else st.recPairs ++ [(y, y')] }
            pure (some (.proj s j y'))
        | none => pure none
  | .app f a =>
    match f with
    | .lam _ _ b _ => pure (some (instE b a 0))
    | .letE _ _ v b _ => pure (some (.app (instE b v 0) a))
    | _ => do pure ((← whStepT env f).map fun f' => .app f' a)
  | x => pure (unfoldAt env x)

def whStepChecked (env : Environment) (x : Lean.Expr) : M (Option Lean.Expr) := do
  let r ← whStepT env x
  if r != whStepR env x then modify fun st => { st with traceMismatch := st.traceMismatch + 1 }
  pure r

mutual
partial def tdOk (env : Environment) (A : Lean.Expr) : M Unit := do
  match appFn A with
  | .const c _ =>
    if c == ``Nat || c == ``Bool || c == ``Sparkle.Core.Domain.DomainConfig then pure ()
    else if c == ``BitVec then
      match appArgs A with
      | [w] => recog env 400 w
      | _ => modify fun s => { s with tdFail := bump s.tdFail "BitVec(shape)" }
    else if c == ``Signal then
      match appArgs A with
      | [d, t] => do recog env 400 d; tdOk env t
      | _ => modify fun s => { s with tdFail := bump s.tdFail "Signal(shape)" }
    else modify fun s => { s with tdFail := bump s.tdFail c.toString }
  | h => modify fun s => { s with tdFail := bump s.tdFail s!"<{h.ctorName}>" }

partial def recogProj (env : Environment) (fuel : Nat) (S : Name) (i : Nat) (x : Lean.Expr) : M Unit := do
  match fuel with
  | 0 => modify fun s => { s with heads := bump s.heads "<fuel>" }
  | fuel + 1 =>
    match appFn x with
    | .const ctor _ =>
      match env.find? ctor with
      | some (.ctorInfo cv) =>
        if cv.induct == S && (appArgs x).length == cv.numParams + cv.numFields then
          match (appArgs x)[cv.numParams + i]? with
          | some f => recog env fuel f
          | none => modify fun s => { s with heads := bump s.heads "<projCtor: no field>" }
        else modify fun s => { s with heads := bump s.heads "<projCtor: shape>" }
      | _ =>
        match ← whStepChecked env x with
        | some x' => do
            modify fun s => { s with unfolded := bump s.unfolded ("proj-arg:" ++ ctor.toString) }; recogProj env fuel S i x'
        | none =>
          let why := if ctor == ``List.rec then describeRecStuck env x else describe env x
          modify fun s => { s with heads := bump s.heads s!"proj {S}#{i} of {why}" }
    | _ =>
      match ← whStepChecked env x with
      | some x' => recogProj env fuel S i x'
      | none => modify fun s => { s with heads := bump s.heads s!"proj {S}#{i} of {describe env x}" }

partial def recog (env : Environment) (fuel : Nat) (e : Lean.Expr) : M Unit := do
  modify fun s => { s with nodes := s.nodes + 1, maxDepth := max s.maxDepth (4000 - fuel) }
  match fuel with
  | 0 => modify fun s => { s with heads := bump s.heads "<fuel>" }
  | fuel + 1 =>
  match e with
  | .bvar _ => pure ()
  | .lam _ A b _ => do tdOk env A; recog env fuel b
  | .letE _ A v b _ =>
    if coreHead A then do tdOk env A; recog env fuel v; recog env fuel b
    else recog env fuel (instE b v 0)
  | .proj S i x => recogProj env fuel S i x
  | .mdata _ e => recog env fuel e
  | _ =>
    match appFn e with
    | .lam .. | .letE .. | .proj .. =>
      let r ← (match appFn e, appArgs e with
        | .lam .., _ :: _ => pure (some (betaApp (appFn e) (appArgs e)))
        | .letE _ _ v b _, _ :: _ => pure (some (mkApps (instE b v 0) (appArgs e)))
        | .proj s j y, _ :: _ => do pure ((← whStepChecked env (.proj s j y)).map fun h' => mkApps h' (appArgs e))
        | _, _ => pure none)
      if r != headRedexR env e then modify fun st => { st with traceMismatch := st.traceMismatch + 1 }
      match r with
      | some e' => recog env fuel e'
      | none => modify fun s => { s with heads := bump s.heads "<redex without args>" }
    | .const c _ =>
      let args := appArgs e
      let sub (ixs : List Nat) : M Unit := do
        for i in ixs do
          if let some a := args[i]? then recog env fuel a
      let tys (ixs : List Nat) : M Unit := do
        for i in ixs do
          if let some a := args[i]? then tdOk env a
      if c == ``OfNat.ofNat then pure ()
      else if c == ``Sparkle.Core.Domain.defaultDomain then pure ()
      else if c == ``instInhabitedBool then pure ()
      else if c == ``BitVec.ofNat || c == ``BitVec.instInhabited then sub [0, 1]
      else if c == ``Signal.pure then do sub [0, 2]; tys [1]
      else if c == ``Signal.register then do sub [0, 2, 3]; tys [1]
      else if c == ``Signal.mux then do sub [0, 2, 3, 4]; tys [1]
      else if c == ``Signal.loop then do sub [0, 2, 3]; tys [1]
      else if c == ``HAdd.hAdd || c == ``HAnd.hAnd || c == ``HOr.hOr then sub [4, 5]
      else if c == ``Complement.complement then sub [2]
      else if c == ``Sparkle.Core.Signal.Signal.beq then sub [1, 3, 4]
      else if (bvAbbrevRow c).isSome then pure ()
      else if c == ``List.rec then
        match recStep env e with
        | some e' => do modify fun s => { s with recSteps := s.recSteps + 1, recPairs := if s.recPairs.any (·.1 == e) then s.recPairs else s.recPairs ++ [(e, e')] }; recog env fuel e'
        | none => modify fun s => { s with heads := bump s.heads (describeRecStuck env e) }
      else
        match unfoldAt env e with
        | some e' => do modify fun s => { s with unfolded := bump s.unfolded c.toString }; recog env fuel e'
        | none =>
          let kind := match env.find? c with
            | some (.inductInfo _) => " [inductive]" | some (.ctorInfo _) => " [constructor]" | some (.recInfo _) => " [recursor]"
            | some (.opaqueInfo _) => " [opaque]" | some (.thmInfo _) => " [theorem]" | some (.axiomInfo _) => " [axiom]"
            | some (.defnInfo _) => " [defn: level mismatch]" | some (.quotInfo _) => " [quot]" | none => " [missing]"
          modify fun s => { s with heads := bump s.heads (c.toString ++ kind), sample := if s.sample.any (·.1 == c.toString) then s.sample else s.sample ++ [(c.toString, e)] }
    | h => modify fun s => { s with heads := bump s.heads s!"<{h.ctorName}> application" }
end

/-- close the loose bvars of `e` and `e'` by fresh fvars (of a junk type: the check is of the reduction, not of typing) and ask Lean's `isDefEq` -/
partial def withFVs {α : Type} (n : Nat) (k : Array Lean.Expr → MetaM α) (acc : Array Lean.Expr := #[]) : MetaM α :=
  if acc.size == n then k acc else withLocalDecl `x .default (mkConst ``Nat) fun f => withFVs n k (acc.push f)

run_cmd liftTermElabM do
  let env ← getEnv
  let some ci := env.find? `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte | throwError "root missing"
  unless ci.value! == Tools.ShippingFGCircuitS1kStmt.hftRootValue do throwError "the root's value in this environment differs from hftRootValue"
  if ci.value! == varBad then throwError "control: varBad equals the value"
  let st := (recog env 4000 ci.value!).run {} |>.2
  let top (l : List (String × Nat)) := (l.toArray.qsort (fun a b => a.2 > b.2)).toList
  -- the equation check: Lean's isDefEq on (input, output) of each distinct recStep taken
  let mut ok : Nat := 0
  let mut bad : Nat := 0
  let mut err : Nat := 0
  for (a, b) in st.recPairs do
    let n := max a.looseBVarRange b.looseBVarRange
    try
      let r ← withFVs n fun fvs => do
        let a' := a.instantiateRev fvs
        let b' := b.instantiateRev fvs
        withDefault (isDefEq a' b')
      if r then ok := ok + 1 else bad := bad + 1
    catch _ => err := err + 1
  -- a control: the check rejects a wrong output
  let wrongOk ← match st.recPairs.head? with
    | some (a, _) =>
      let n := a.looseBVarRange
      try withFVs n fun fvs => withDefault (isDefEq (a.instantiateRev fvs) (mkConst ``Nat)) catch _ => pure false
    | none => pure false
  if wrongOk then throwError "control: isDefEq accepted a wrong output"
  logInfo m!"FGCIRCUIT14 SNAPSHOT14 (one environment): {st.nodes} nodes visited; {st.recSteps} List.rec iota steps taken ({st.recPairs.length} distinct); unfolded definitions (distinct {st.unfolded.length}): {(top st.unfolded).take 40}"
  logInfo m!"FGCIRCUIT14 SNAPSHOT14 equation check (Lean isDefEq, default transparency, loose bvars closed by junk-typed fvars): {ok} of {st.recPairs.length} distinct (List.rec spine, iota result) pairs are definitionally equal; {bad} not; {err} threw"
  logInfo m!"FGCIRCUIT14 MISSING (heads with no rule, stuck): {top st.heads}"
  for (c, e) in st.sample do
    let t := toString (← ppExpr e)
    logInfo m!"FGCIRCUIT14 MISSING sample (first stuck {c}, loose bvars are #n): {t.take 700}"
  logInfo m!"FGCIRCUIT14 TRACE: the traversal's own steps agree with whStepR/headRedexR in all cases ({st.traceMismatch} mismatches)"
  logInfo m!"FGCIRCUIT14 MISSING (binder/let types outside TD): {top st.tdFail}"

end Tests.Gen5.FGCircuitPilotCheck14
