import Tools.ShippingFGCircuitS1rCD
set_option autoImplicit false
-- FG circuit pilot S1r check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §22.

/-! # FGCircuitPilotCheck16

1. SIGNATURES: the new rules of `DZ` (`mapFst`, `mapSnd`, `prodMk`, `unitVal`, `prodTy`, `punitTy`, and `unf`/`letE` after the change), the embedding `dy_to_dz`, functionality, the carriers and the consumer
   statements, against independently written statements (`isDefEq`), with mutants that must be rejected.
2. PATTERN: the rule patterns for `Signal.map Prod.fst/snd` equal the Expr Lean's elaborator produces for the source term (the audit that the head constant, universe levels and argument order are right).
3. EQUATIONS: `signal_map_*` hold for every signal and every time (kernel theorems).
4. AUDIT (fail closed): the equation audit (`isDefEq` of every step the traversal takes) is a function with a verdict; the build FAILS if any pair is not defeq, any threw, the traversal disagrees with
   `whStepR`/`headRedexR`, or the target pair set is empty. Negative controls: a wrong pair, an empty set, a trace mismatch, a thrown pair must all be rejected by the same verdict function.
   `isDefEq` with junk-typed fvars is an AUDIT of a reduction, not a typed derivation: it is not "meaning preserving".
5. SNAPSHOT16 (ONE environment: the build's): how far `hftRootValue` goes with the new rules, and the next stuck point.
6. AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck16
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingGen5ConstValueE Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)

/-! ## 1. expected statements, written independently -/

noncomputable instance : Inhabited Environment := ⟨Classical.ofNonempty⟩

/-- `mapFst`. mu: 0 expected; 1 the function is `Prod.snd`; 2 the type argument `ta` is judged as `B`; 3 no `MapStuck`; 4 the value is `Signal.map Prod.snd` at type `Signal D B` -/
def ExpMapFst (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e d tp ta a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)},
    e = appN ``Signal.map [.zero] [d, tp, ta, appN (if mu == 1 then ``Prod.snd else ``Prod.fst) [.zero, .zero] [a, b], s] →
    DZ env ρ d (.val DomainConfig D) → DZ env ρ tp (.ty (A × B)) → DZ env ρ ta (.ty (if mu == 2 then B else A)) → DZ env ρ a (.ty A) → DZ env ρ b (.ty B) →
    DZ env ρ s (.val (Signal D (A × B)) sv) → (if mu == 3 then True else MapStuck env e) →
    (if mu == 4 then DZ env ρ e (.val (Signal D B) (Signal.map Prod.snd sv)) else DZ env ρ e (.val (Signal D A) (Signal.map Prod.fst sv)))

def ExpMapSnd (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e d tp tb a b s : Expr} {D : DomainConfig} {A B : Type} {sv : Signal D (A × B)},
    e = appN ``Signal.map [.zero] [d, tp, tb, appN (if mu == 1 then ``Prod.fst else ``Prod.snd) [.zero, .zero] [a, b], s] →
    DZ env ρ d (.val DomainConfig D) → DZ env ρ tp (.ty (A × B)) → DZ env ρ tb (.ty (if mu == 2 then A else B)) → DZ env ρ a (.ty A) → DZ env ρ b (.ty B) →
    DZ env ρ s (.val (Signal D (A × B)) sv) → (if mu == 3 then True else MapStuck env e) →
    (if mu == 4 then DZ env ρ e (.val (Signal D A) (Signal.map Prod.fst sv)) else DZ env ρ e (.val (Signal D B) (Signal.map Prod.snd sv)))

/-- `prodMk`. mu: 1 no constructor condition; 2 the value is swapped; 3 the component types are not judged -/
def ExpProdMk (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e a b x y : Expr} {A B : Type} {xv : A} {yv : B} {cv : ConstructorVal},
    e = appN ``Prod.mk [.zero, .zero] [a, b, x, y] → (if mu == 1 then True else env.find? ``Prod.mk = some (.ctorInfo cv)) →
    (if mu == 3 then True else DZ env ρ a (.ty A)) → (if mu == 3 then True else DZ env ρ b (.ty B)) → DZ env ρ x (.val A xv) → DZ env ρ y (.val B yv) →
    (if mu == 2 then DZ env ρ e (.val (A × B) (xv, yv)) else DZ env ρ e (.val (A × B) (xv, yv)))

def ExpUnitVal (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {cv : ConstructorVal},
    e = .const ``PUnit.unit [if mu == 2 then .zero else .succ .zero] → (if mu == 1 then True else env.find? ``PUnit.unit = some (.ctorInfo cv)) → DZ env ρ e (.val Unit ())

def ExpProdTy (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e a b : Expr} {A B : Type},
    e = appN ``Prod [.zero, .zero] [a, b] → DZ env ρ a (.ty A) → (if mu == 1 then True else DZ env ρ b (.ty B)) → DZ env ρ e (.ty (A × B))

def ExpPunitTy (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr}, e = .const ``PUnit [if mu == 1 then .zero else .succ .zero] → DZ env ρ e (.ty Unit)

/-- the generalised `unf`. mu: 1 the stop condition is the value one for every result; 2 the branches are swapped; 3 no stop condition -/
def ExpUnfZ (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e e' : Expr} {r : Res},
    (if mu == 1 then headStop e = false else if mu == 2 then (if r.kind then tyHeadStop e else headStop e) = false else if mu == 3 then True else (if r.kind then headStop e else tyHeadStop e) = false) →
    unfoldAt env e = some e' → DZ env ρ e' r → DZ env ρ e r

/-- `letE` with the new premise `coreHead A = true`. mu: 1 the premise is dropped; 2 it is `= false` -/
def ExpLetZ (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {TA T : Type} {a : TA} {r : T},
    e = .letE n A v body nd → DZ env ρ A (.ty TA) → (if mu == 1 then True else coreHead A = (mu != 2)) → DZ env ρ v (.val TA a) →
    DZ env (⟨A, ⟨TA, a⟩⟩ :: ρ) body (.val T r) → DZ env ρ e (.val T r)

/-- `projRec`. mu: 1 no recInfo condition; 2 the step is on the projection itself (`e`) -/
def ExpProjRec (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {ls : List Level} {ri : RecursorVal} {r : Res},
    e = .proj S i x → appFn x = .const ``List.rec ls → (if mu == 1 then True else env.find? ``List.rec = some (.recInfo ri)) →
    (if mu == 2 then recStep env e = some x' else recStep env x = some x') → DZ env ρ (.proj S i x') r → DZ env ρ e r

def ExpEmbedZ (rev : Bool) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {r : Res}, (if rev then DZ env ρ e r else DY env ρ e r) → (if rev then DY env ρ e r else DZ env ρ e r)

def FunZ : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDZ env ρ e α v → CDZ env ρ e α' v' → α = α' ∧ HEq v v'
def FunZOtherEnv : Prop :=
  ∀ {env env' : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDZ env ρ e α v → CDZ env' ρ e α' v' → α = α' ∧ HEq v v'
def FunZNoHEq : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDZ env ρ e α v → CDZ env ρ e α' v' → α = α'

/-- the single-environment carrier over `DZ`. mu: 1 the environment of `DZ` is a fixed default one; 2 a non-empty valuation; 3 the levels are not required to be empty -/
def ExpCircCVZ (mu : Nat) : ConstValueRel := fun env X α v =>
  ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ (if mu == 3 then True else d.levelParams = []) ∧
    DZ (if mu == 1 then default else env) (if mu == 2 then [⟨.const ``Nat [], ⟨Nat, 0⟩⟩] else []) d.value (.val α v)

def ExpHftObZ (mu : Nat) : Environment → Prop := fun env =>
  DZ env (if mu == 1 then [⟨.const ``Nat [], ⟨Nat, 0⟩⟩] else []) Tools.ShippingFGCircuitS1kStmt.hftRootValue
    (.val (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte)
def ExpHftObY (mu : Nat) : Environment → Prop := fun env =>
  (if mu == 1 then DX env else DY env) [] Tools.ShippingFGCircuitS1kStmt.hftRootValue
    (.val (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte)

def ExpRunIffZ (mu : Nat) : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {e : Environment}, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w' → ∀ {X : Name} {α : Type} {v : α},
    CircCVZ e X α v ↔ CircCVZ (envAt cref (if mu == 1 then w' else w)) X α v

def ExpMapAt (fst : Bool) (mu : Nat) : Prop :=
  ∀ {D : DomainConfig} {A B : Type} (sv : Signal D (A × B)) (t : Nat),
    (if fst then (Signal.map Prod.fst sv).val t = (sv.val t).1 else (Signal.map Prod.snd sv).val t = (if mu == 1 then (sv.val (t + 1)).2 else (sv.val t).2))

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1rCD
  let Q := `Tests.Gen5.FGCircuitPilotCheck16
  let same (thm : Name) (exp : Expr) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    unless ← withDefault (isDefEq ci.type exp) do throwError "{thm}: type is NOT the expected statement"
  let differs (thm : Name) (mu : Expr) : MetaM Unit := do
    let ci ← getConstInfo thm
    if ← withDefault (isDefEq ci.type mu) then throwError "{thm}: a MUTANT was accepted"
  let mut nm : Nat := 0
  let nat (n : Nat) : Expr := toExpr n
  let q (n : Name) (args : Array Expr) : MetaM Expr := mkAppM (Q ++ n) args
  -- the new rules
  same (S ++ `DZ.mapFst) (← q `ExpMapFst #[nat 0])
  for m in [1, 2, 3, 4] do differs (S ++ `DZ.mapFst) (← q `ExpMapFst #[nat m]); nm := nm + 1
  same (S ++ `DZ.mapSnd) (← q `ExpMapSnd #[nat 0])
  for m in [1, 2, 3, 4] do differs (S ++ `DZ.mapSnd) (← q `ExpMapSnd #[nat m]); nm := nm + 1
  same (S ++ `DZ.prodMk) (← q `ExpProdMk #[nat 0])
  for m in [1, 3] do differs (S ++ `DZ.prodMk) (← q `ExpProdMk #[nat m]); nm := nm + 1
  same (S ++ `DZ.unitVal) (← q `ExpUnitVal #[nat 0])
  for m in [1, 2] do differs (S ++ `DZ.unitVal) (← q `ExpUnitVal #[nat m]); nm := nm + 1
  same (S ++ `DZ.prodTy) (← q `ExpProdTy #[nat 0])
  differs (S ++ `DZ.prodTy) (← q `ExpProdTy #[nat 1]); nm := nm + 1
  same (S ++ `DZ.punitTy) (← q `ExpPunitTy #[nat 0])
  differs (S ++ `DZ.punitTy) (← q `ExpPunitTy #[nat 1]); nm := nm + 1
  same (S ++ `DZ.unf) (← q `ExpUnfZ #[nat 0])
  for m in [1, 2, 3] do differs (S ++ `DZ.unf) (← q `ExpUnfZ #[nat m]); nm := nm + 1
  same (S ++ `DZ.projRec) (← q `ExpProjRec #[nat 0])
  for m in [1, 2] do differs (S ++ `DZ.projRec) (← q `ExpProjRec #[nat m]); nm := nm + 1
  same (S ++ `DZ.letE) (← q `ExpLetZ #[nat 0])
  for m in [1, 2] do differs (S ++ `DZ.letE) (← q `ExpLetZ #[nat m]); nm := nm + 1
  -- embedding, functionality
  same (S ++ `dy_to_dz) (← q `ExpEmbedZ #[toExpr false])
  differs (S ++ `dy_to_dz) (← q `ExpEmbedZ #[toExpr true]); nm := nm + 1
  same (S ++ `cdz_fun) (Lean.mkConst (Q ++ `FunZ))
  for mu in ["FunZOtherEnv", "FunZNoHEq"] do
    differs (S ++ `cdz_fun) (Lean.mkConst (Q ++ Name.mkSimple mu)); nm := nm + 1
  -- carrier and obligations
  let cvDef := (← getConstInfo (S ++ `CircCVZ)).value!
  unless ← withDefault (isDefEq cvDef (← q `ExpCircCVZ #[nat 0])) do throwError "CircCVZ: definition is NOT the expected one"
  for m in [1, 2, 3] do
    if ← withDefault (isDefEq cvDef (← q `ExpCircCVZ #[nat m])) then throwError "CircCVZ: MUTANT {m} accepted"
    nm := nm + 1
  let obZ := (← getConstInfo (S ++ `HftObCDZ)).value!
  unless ← withDefault (isDefEq obZ (← q `ExpHftObZ #[nat 0])) do throwError "HftObCDZ: definition is NOT the expected one"
  if ← withDefault (isDefEq obZ (← q `ExpHftObZ #[nat 1])) then throwError "HftObCDZ: MUTANT accepted"
  nm := nm + 1
  let obY := (← getConstInfo (S ++ `HftObCDY)).value!
  unless ← withDefault (isDefEq obY (← q `ExpHftObY #[nat 0])) do throwError "HftObCDY: definition is NOT the expected one"
  if ← withDefault (isDefEq obY (← q `ExpHftObY #[nat 1])) then throwError "HftObCDY: MUTANT (DX) accepted"
  nm := nm + 1
  -- HftObCDY is not HftObCDX: the S1p obligation is over DX and the new ones are not definitionally it
  let obX := (← getConstInfo (`Tools.ShippingFGCircuitS1pCD ++ `HftObCDX)).value!
  if ← withDefault (isDefEq obX obY) then throwError "HftObCDX and HftObCDY are the same"
  same (S ++ `circCVZ_at_of_getEnv) (← q `ExpRunIffZ #[nat 0])
  differs (S ++ `circCVZ_at_of_getEnv) (← q `ExpRunIffZ #[nat 1]); nm := nm + 1
  -- the equations of the wiring at every time
  same (S ++ `signal_map_fst_at) (← q `ExpMapAt #[toExpr true, nat 0])
  same (S ++ `signal_map_snd_at) (← q `ExpMapAt #[toExpr false, nat 0])
  differs (S ++ `signal_map_snd_at) (← q `ExpMapAt #[toExpr false, nat 1]); nm := nm + 1
  logInfo m!"FGCIRCUIT16 SIGNATURES: DZ.mapFst/mapSnd/prodMk/unitVal/prodTy/punitTy/unf/letE, dy_to_dz, cdz_fun, CircCVZ, HftObCDY/HftObCDZ (and HftObCDX is not HftObCDY), circCVZ_at_of_getEnv (envAt cref w), signal_map_fst_at/snd_at match the independently written statements; {nm} mutants rejected"
  -- the old rules are unchanged except unf (stop over Res), beta/projStep/projCtor/recIota (over Res), letE (hc): the value-rules of DY map to DZ one to one
  let mut nOld : Nat := 0
  for c in [`nat, `bool, `domainConfig, `bitvec, `signal, `bvar, `natLit, `domDefault, `bvOfNat, `bvInhabited, `boolInhabited, `sigPure, `sigRegister, `sigMux, `sigAddBV, `sigLoop, `lam, `sigBeqBV, `sigAndBool, `sigOrBool, `sigNotBool, `bvAbbrev, `zeta] do
    let a ← getConstInfo (`Tools.ShippingFGCircuitS1pCD ++ `DY ++ c)
    let b ← getConstInfo (S ++ `DZ ++ c)
    let rn (e : Expr) : Expr := e.replace fun x => if x.isConstOf `Tools.ShippingFGCircuitS1pCD.DY then some (Lean.mkConst (S ++ `DZ) x.constLevels!) else none
    unless ← withDefault (isDefEq (rn a.type) b.type) do throwError "{c}: DZ rule differs from the DY rule"
    nOld := nOld + 1
  do
    let a ← getConstInfo (`Tools.ShippingFGCircuitS1pCD ++ `DY ++ `sigPure)
    let b ← getConstInfo (S ++ `DZ ++ `sigMux)
    let rn (e : Expr) : Expr := e.replace fun x => if x.isConstOf `Tools.ShippingFGCircuitS1pCD.DY then some (Lean.mkConst (S ++ `DZ) x.constLevels!) else none
    if ← withDefault (isDefEq (rn a.type) b.type) then throwError "control: sigMux accepted as sigPure"
  logInfo m!"FGCIRCUIT16 OLD RULES: {nOld} constructors of DY are the same in DZ (unf, letE, beta, projStep, projCtor, recIota changed on purpose and compared above or by dy_to_dz); a control rejects a changed rule"

/-! ## 2. PATTERN: the rule patterns are the Expr Lean's elaborator produces for the source terms -/

run_cmd liftTermElabM do
  let natE := Lean.mkConst ``Nat
  let boolE := Lean.mkConst ``Bool
  let dT := Lean.mkConst ``Sparkle.Core.Domain.DomainConfig
  let pairT := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natE boolE
  let sigT (d t : Expr) := mkApp2 (Lean.mkConst ``Signal [.zero]) d t
  withLocalDecl `D .default dT fun D => withLocalDecl `s .default (sigT D pairT) fun s => do
    let stx1 ← `(Sparkle.Core.Signal.Signal.map Prod.fst $(← Term.exprToSyntax s))
    let stx2 ← `(Sparkle.Core.Signal.Signal.map Prod.snd $(← Term.exprToSyntax s))
    let e1 ← instantiateMVars (← Term.elabTerm stx1 none)
    let e2 ← instantiateMVars (← Term.elabTerm stx2 none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e1 ← instantiateMVars e1
    let e2 ← instantiateMVars e2
    let pat1 := appN ``Signal.map [.zero] [D, pairT, natE, appN ``Prod.fst [.zero, .zero] [natE, boolE], s]
    let pat2 := appN ``Signal.map [.zero] [D, pairT, boolE, appN ``Prod.snd [.zero, .zero] [natE, boolE], s]
    unless e1 == pat1 do throwError "PATTERN: the elaborated `Signal.map Prod.fst s` is not the rule's pattern: {e1} vs {pat1}"
    unless e2 == pat2 do throwError "PATTERN: the elaborated `Signal.map Prod.snd s` is not the rule's pattern: {e2} vs {pat2}"
    -- controls: a swapped pattern differs
    if e1 == pat2 then throwError "PATTERN control: fst equals snd"
    -- MapStuck holds in this build's environment for them (the unfolding reaches the constructor `Signal.mk`)
    let env ← getEnv
    let some u1 := unfoldAt env e1 | throwError "PATTERN: Signal.map does not unfold"
    unless (appFn u1).isConstOf ``Signal.mk do throwError "PATTERN: the unfolding of Signal.map is not headed by Signal.mk: {appFn u1}"
    unless (env.find? ``Signal.mk).any (fun c => match c with | .ctorInfo _ => true | _ => false) do throwError "PATTERN: Signal.mk is not a constructor"
    -- a control: the unfolding of `Signal.pure` is not constructor-headed by Signal.mk? (`Signal.pure` is a stop constant in the rules; this only checks the test is not vacuous)
    let pu := appN ``Signal.pure [.zero] [D, natE, toExpr (0 : Nat)]
    match unfoldAt env pu with
    | some u => if (appFn u).isConstOf ``Signal.pure then throwError "PATTERN control: unfolding returned itself"
    | none => pure ()
    logInfo m!"FGCIRCUIT16 PATTERN: the elaborated `Signal.map Prod.fst s` / `Signal.map Prod.snd s` are exactly the rules' patterns (Signal.map at level 0, D, Nat × Bool, Nat, Prod.fst at levels 0 0, s); unfolding them in this environment reaches the constructor Signal.mk (MapStuck holds); a swapped pattern is rejected"

/-! ## 3. AUDIT: the fail-closed verdict -/

structure Audit where
  total : Nat := 0
  ok : Nat := 0
  bad : Nat := 0
  err : Nat := 0
  traceMismatch : Nat := 0

/-- the verdict of the equation audit: it ACCEPTS only if the target pair set is non-empty, every pair is defeq, none threw, and the traversal agrees with `whStepR`/`headRedexR` -/
def Audit.verdict (a : Audit) : Except String Unit :=
  if a.total == 0 then .error "the target pair set is EMPTY"
  else if a.bad != 0 then .error s!"{a.bad} pairs are NOT defeq"
  else if a.err != 0 then .error s!"{a.err} pairs threw"
  else if a.traceMismatch != 0 then .error s!"{a.traceMismatch} trace mismatches"
  else if a.ok != a.total then .error "ok ≠ total"
  else .ok ()

partial def withFVs {α : Type} (n : Nat) (k : Array Lean.Expr → MetaM α) (acc : Array Lean.Expr := #[]) : MetaM α :=
  if acc.size == n then k acc else withLocalDecl `x .default (Lean.mkConst ``Nat) fun f => withFVs n k (acc.push f)

/-- close the loose bvars of `a`, `b` by fresh fvars (a junk type: the check is of the reduction, not of typing) and ask Lean's `isDefEq` (default transparency) -/
def auditPairs (pairs : List (Lean.Expr × Lean.Expr)) (traceMismatch : Nat) : MetaM Audit := do
  let mut a : Audit := { total := pairs.length, traceMismatch }
  for (x, y) in pairs do
    let n := max x.looseBVarRange y.looseBVarRange
    try
      let r ← withFVs n fun fvs => do withDefault (isDefEq (x.instantiateRev fvs) (y.instantiateRev fvs))
      if r then a := { a with ok := a.ok + 1 } else a := { a with bad := a.bad + 1 }
    catch _ => a := { a with err := a.err + 1 }
  pure a

run_cmd liftTermElabM do
  let natE := Lean.mkConst ``Nat
  let boolE := Lean.mkConst ``Bool
  let dT := Lean.mkConst ``Sparkle.Core.Domain.DomainConfig
  let pairT := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natE natE
  let sigT (d t : Expr) := mkApp2 (Lean.mkConst ``Signal [.zero]) d t
  -- negative controls: the verdict function REJECTS each failure mode
  let expectReject (what : String) (a : Audit) : MetaM Unit :=
    match a.verdict with
    | .error _ => pure ()
    | .ok _ => throwError "AUDIT control: {what} was ACCEPTED"
  -- (1) a mismatching pair: `Signal.map Prod.fst p` against `Signal.map Prod.snd p`, a different signal (typed, both `Signal D Nat`)
  withLocalDecl `D .default dT fun D => withLocalDecl `p .default (sigT D pairT) fun p => do
    let mf := appN ``Signal.map [.zero] [D, pairT, natE, appN ``Prod.fst [.zero, .zero] [natE, natE], p]
    let ms := appN ``Signal.map [.zero] [D, pairT, natE, appN ``Prod.snd [.zero, .zero] [natE, natE], p]
    -- the correct step is accepted (the unfolding of `mf`)
    let env ← getEnv
    let some uf := unfoldAt env mf | throwError "control: Signal.map does not unfold"
    let good ← auditPairs [(mf, uf)] 0
    unless good.ok == 1 && good.verdict matches .ok _ do throwError "AUDIT control: the correct step (map fst, its unfolding) was not accepted ({good.ok}/{good.total}, bad {good.bad}, err {good.err})"
    let wrong ← auditPairs [(mf, ms)] 0
    unless wrong.bad == 1 do throwError "AUDIT control: the mismatch (fst vs snd) was not detected as bad (bad {wrong.bad}, ok {wrong.ok}, err {wrong.err})"
    expectReject "a mismatching pair" wrong
    -- (2) the same wrong pair together with correct ones is still rejected
    expectReject "a mismatching pair among correct ones" (← auditPairs [(mf, uf), (mf, ms), (ms, ms)] 0)
  -- (3) an empty target set
  expectReject "an empty target pair set" (← auditPairs [] 0)
  -- (4) a trace mismatch
  expectReject "a trace mismatch" { total := 1, ok := 1, traceMismatch := 1 }
  -- (5) a pair that throws (an ill-formed term the checker cannot process is counted as err, which rejects)
  expectReject "a thrown pair" { total := 1, ok := 0, err := 1 }
  -- (6) ok ≠ total
  expectReject "ok ≠ total" { total := 2, ok := 1 }
  -- (7) a pair set that is all correct is accepted (the verdict is not constant-false)
  unless ({ total := 2, ok := 2 } : Audit).verdict matches .ok _ do throwError "AUDIT control: the verdict rejects an all-ok audit"
  -- (8) a clearly non-defeq pair of constants
  expectReject "Nat vs Bool" (← auditPairs [(natE, boolE)] 0)
  logInfo m!"FGCIRCUIT16 AUDIT CONTROLS: the verdict rejects a mismatching pair (map fst vs map snd; also among correct ones), an empty target set, a trace mismatch, a thrown pair, ok ≠ total, Nat vs Bool, and accepts the correct step and an all-ok audit"

/-! ## 4. AXIOMS -/
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1rCD
  let names : List Name := [S ++ `signal_map_eq, S ++ `signal_map_fst_at, S ++ `signal_map_snd_at, S ++ `signal_mk_fst_eq, S ++ `signal_mk_snd_eq, S ++ `signal_ext', S ++ `signal_map_pair_at,
    S ++ `signal_map_fst_pure, S ++ `signal_map_snd_pure, S ++ `dy_to_dz, S ++ `dx_to_dz, S ++ `dz_signalMk_false, S ++ `whStepR_listRec, S ++ `mapStuck_unf_false, S ++ `dz_fun, S ++ `cdz_fun, S ++ `tdz_fun, S ++ `cdz_eq,
    S ++ `cdz_of_cdy, S ++ `cdz_of_cdx, S ++ `circCVY_to_Z, S ++ `circCVS_to_Z, S ++ `circCVZ_functional, S ++ `sourceDenotesS_to_Y, S ++ `sourceDenotesY_to_Z, S ++ `declConnect_of_cv,
    S ++ `declConnect_S_to_Y, S ++ `declConnect_Y_to_Z, S ++ `hftObCDY_of_X, S ++ `hftObCDZ_of_Y, S ++ `circCVY_hft_of_obCDY, S ++ `circCVZ_hft_of_obCDZ, S ++ `circCVZ_at_of_getEnv,
    S ++ `circCVY_at_of_getEnv, S ++ `circCVZ_hft_run, S ++ `circCVY_hft_run, S ++ `hftFinalStmtWith_const]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT16 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 5. SNAPSHOT16: the traversal with the new rules (a recognizer that uses the rules' own functions; not a proof) -/

structure Stuck where
  heads : List (String × Nat) := []
  nodes : Nat := 0
  unfolded : List (String × Nat) := []
  recSteps : Nat := 0
  recPairs : List (Lean.Expr × Lean.Expr) := []
  mapFstSites : Nat := 0
  mapSndSites : Nat := 0
  mapStuckFail : Nat := 0
  mapPairs : List (Lean.Expr × Lean.Expr) := []
  prodMkSites : Nat := 0
  projRecSteps : Nat := 0
  unitSites : Nat := 0
  prodTySites : Nat := 0
  tyUnfolds : Nat := 0
  maxDepth : Nat := 0
  sample : List (String × Lean.Expr) := []
  traceMismatch : Nat := 0

def bump (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  if l.any (·.1 == k) then l.map fun (a, n) => if a == k then (a, n + 1) else (a, n) else l ++ [(k, 1)]

abbrev M := StateM Stuck

def pre0 (ty : Bool) : String := if ty then "ty:" else ""

def kindOf (env : Environment) (c : Name) : String :=
  match env.find? c with
  | some (.inductInfo _) => "inductive" | some (.ctorInfo _) => "ctor" | some (.recInfo _) => "recursor" | some (.opaqueInfo _) => "opaque"
  | some (.thmInfo _) => "theorem" | some (.axiomInfo _) => "axiom" | some (.defnInfo _) => "defn" | some (.quotInfo _) => "quot" | none => "missing"

partial def describe (env : Environment) : Lean.Expr → String
  | .proj s j y => s!"proj {s}#{j} ({describe env y})"
  | x =>
    match appFn x with
    | .const c _ => s!"{c}[{kindOf env c}]/{(appArgs x).length}"
    | .proj s j y => s!"[proj {s}#{j} ({describe env y})]/{(appArgs x).length}"
    | .lam .. => s!"<lam>/{(appArgs x).length}"
    | .letE .. => s!"<let>/{(appArgs x).length}"
    | h => s!"<{h.ctorName}>/{(appArgs x).length}"

def describeRecStuck (env : Environment) (e : Lean.Expr) : String :=
  match appArgs e with
  | _ :: _ :: _ :: _ :: major :: _ =>
    match recMajorWh env 256 major with
    | some m => s!"List.rec: major reaches {describe env m} but the shape is not nil/cons"
    | none => s!"List.rec: major not static: {describe env major}"
  | args => s!"List.rec: {args.length} arguments (<5)"

/-- `MapStuck` as a Boolean (the premise of `mapFst`/`mapSnd`) -/
def mapStuckB (env : Environment) (e : Lean.Expr) : Bool :=
  match unfoldAt env e with
  | some e' => (match appFn e' with | .const c _ => c == ``Signal.mk | _ => false) && (match env.find? ``Signal.mk with | some (.ctorInfo _) => true | _ => false)
  | none => false

/-- the `Prod.fst`/`Prod.snd` function argument of `Signal.map`: `(isFst, a, b)` -/
def projFn? (f : Lean.Expr) : Option (Bool × Lean.Expr × Lean.Expr) :=
  match appFn f, appArgs f with
  | .const c [.zero, .zero], [a, b] => if c == ``Prod.fst then some (true, a, b) else if c == ``Prod.snd then some (false, a, b) else none
  | _, _ => none

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
/-- `ty = true`: the expression is judged as a TYPE (`DZ … (Res.ty _)`); `ty = false`: as a VALUE -/
partial def recogProj (ty : Bool) (env : Environment) (fuel : Nat) (S : Name) (i : Nat) (x : Lean.Expr) : M Unit := do
  match fuel with
  | 0 => modify fun s => { s with heads := bump s.heads "<fuel>" }
  | fuel + 1 =>
    match appFn x with
    | .const ctor _ =>
      if ctor == ``List.rec && (recStep env x).isSome then
        -- the new rule `projRec`
        match recStep env x with
        | some x' => do
            modify fun s => { s with recSteps := s.recSteps + 1, recPairs := if s.recPairs.any (·.1 == x) then s.recPairs else s.recPairs ++ [(x, x')], projRecSteps := s.projRecSteps + 1 }
            recogProj ty env fuel S i x'
        | none => pure ()
      else
      match env.find? ctor with
      | some (.ctorInfo cv) =>
        if cv.induct == S && (appArgs x).length == cv.numParams + cv.numFields then
          match (appArgs x)[cv.numParams + i]? with
          | some f => recog ty env fuel f
          | none => modify fun s => { s with heads := bump s.heads "<projCtor: no field>" }
        else modify fun s => { s with heads := bump s.heads "<projCtor: shape>" }
      | _ =>
        match ← whStepChecked env x with
        | some x' => do
            modify fun s => { s with unfolded := bump s.unfolded ("proj-arg:" ++ ctor.toString) }; recogProj ty env fuel S i x'
        | none =>
          let why := if ctor == ``List.rec then describeRecStuck env x else describe env x
          modify fun s => { s with heads := bump s.heads s!"{pre0 ty}proj {S}#{i} of {why}" }
    | _ =>
      match ← whStepChecked env x with
      | some x' => recogProj ty env fuel S i x'
      | none => modify fun s => { s with heads := bump s.heads s!"{pre0 ty}proj {S}#{i} of {describe env x}" }

partial def recog (ty : Bool) (env : Environment) (fuel : Nat) (e : Lean.Expr) : M Unit := do
  modify fun s => { s with nodes := s.nodes + 1, maxDepth := max s.maxDepth (4000 - fuel) }
  match fuel with
  | 0 => modify fun s => { s with heads := bump s.heads "<fuel>" }
  | fuel + 1 =>
  let pre := if ty then "ty:" else ""
  match e with
  | .bvar _ => if ty then modify fun s => { s with heads := bump s.heads "ty:<bvar as a type>" } else pure ()
  | .lam _ A b _ =>
    if ty then modify fun s => { s with heads := bump s.heads "ty:<lam>" }
    else do recog true env fuel A; recog false env fuel b
  | .letE _ A v b _ =>
    if ty then modify fun s => { s with heads := bump s.heads "ty:<let>" }
    else if coreHead A then do recog true env fuel A; recog false env fuel v; recog false env fuel b
    else recog false env fuel (instE b v 0)
  | .proj S i x => recogProj ty env fuel S i x
  | .mdata _ e => recog ty env fuel e
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
      | some e' => recog ty env fuel e'
      | none => modify fun s => { s with heads := bump s.heads s!"{pre}<redex without args>" }
    | .const c ls =>
      let args := appArgs e
      let sub (ixs : List Nat) : M Unit := do
        for i in ixs do
          if let some a := args[i]? then recog false env fuel a
      let tys (ixs : List Nat) : M Unit := do
        for i in ixs do
          if let some a := args[i]? then recog true env fuel a
      let generic : M Unit :=
        if c == ``List.rec then
          match recStep env e with
          | some e' => do modify fun s => { s with recSteps := s.recSteps + 1, recPairs := if s.recPairs.any (·.1 == e) then s.recPairs else s.recPairs ++ [(e, e')] }; recog ty env fuel e'
          | none => modify fun s => { s with heads := bump s.heads (pre ++ describeRecStuck env e) }
        else
          match unfoldAt env e with
          | some e' => do
              modify fun s => { s with unfolded := bump s.unfolded (pre ++ c.toString), tyUnfolds := if ty then s.tyUnfolds + 1 else s.tyUnfolds }
              recog ty env fuel e'
          | none =>
            let kind := match env.find? c with
              | some (.inductInfo _) => " [inductive]" | some (.ctorInfo _) => " [constructor]" | some (.recInfo _) => " [recursor]"
              | some (.opaqueInfo _) => " [opaque]" | some (.thmInfo _) => " [theorem]" | some (.axiomInfo _) => " [axiom]"
              | some (.defnInfo _) => " [defn: level mismatch]" | some (.quotInfo _) => " [quot]" | none => " [missing]"
            modify fun s => { s with heads := bump s.heads (pre ++ c.toString ++ kind), sample := if s.sample.any (·.1 == pre ++ c.toString) then s.sample else s.sample ++ [(pre ++ c.toString, e)] }
      if ty then
        -- the type judgements: nat, bool, domainConfig, bitvec, signal, prodTy, punitTy; else the delta/beta/proj/iota steps (`stopR` for a type: these heads are never unfolded)
        if c == ``Nat || c == ``Bool || c == ``Sparkle.Core.Domain.DomainConfig then pure ()
        else if c == ``BitVec then sub [0]
        else if c == ``Signal then do sub [0]; tys [1]
        else if c == ``Prod && ls == [.zero, .zero] && args.length == 2 then do tys [0, 1]; modify fun s => { s with prodTySites := s.prodTySites + 1 }
        else if c == ``PUnit && ls == [.succ .zero] && args.length == 0 then pure ()
        else generic
      else
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
        else if c == ``Signal.map && ls == [.zero] && args.length == 5 && (projFn? args[3]!).isSome && mapStuckB env e then
          -- the new rules `mapFst`/`mapSnd`
          let some (isFst, a, b) := projFn? args[3]! | pure ()
          let pr : List (Lean.Expr × Lean.Expr) := match unfoldAt env e with | some u => [(e, u)] | none => []
          modify fun s => { s with mapFstSites := (if isFst then s.mapFstSites + 1 else s.mapFstSites), mapSndSites := (if isFst then s.mapSndSites else s.mapSndSites + 1), mapPairs := (if s.mapPairs.any (·.1 == e) then s.mapPairs else s.mapPairs ++ pr) }
          sub [0]; tys [1, 2]; recog true env fuel a; recog true env fuel b; sub [4]
        else if c == ``Signal.map && ls == [.zero] && args.length == 5 && (projFn? args[3]!).isSome then
          modify fun s => { s with mapStuckFail := s.mapStuckFail + 1 }
          generic
        else if c == ``Prod.mk && ls == [.zero, .zero] && args.length == 4 && (match env.find? ``Prod.mk with | some (.ctorInfo _) => true | _ => false) then do
          modify fun s => { s with prodMkSites := s.prodMkSites + 1 }
          tys [0, 1]; sub [2, 3]
        else if c == ``PUnit.unit && ls == [.succ .zero] && args.length == 0 && (match env.find? ``PUnit.unit with | some (.ctorInfo _) => true | _ => false) then
          modify fun s => { s with unitSites := s.unitSites + 1 }
        else generic
    | h => modify fun s => { s with heads := bump s.heads s!"{pre}<{h.ctorName}> application" }
end

run_cmd liftTermElabM do
  let env ← getEnv
  let some ci := env.find? `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte | throwError "root missing"
  unless ci.value! == Tools.ShippingFGCircuitS1kStmt.hftRootValue do throwError "the root's value in this environment differs from hftRootValue"
  let st := (recog false env 4000 ci.value!).run {} |>.2
  let top (l : List (String × Nat)) := (l.toArray.qsort (fun a b => a.2 > b.2)).toList
  -- the equation audit over EVERY step the traversal took (List.rec iota pairs and Signal.map unfolding pairs); the build fails unless the verdict accepts
  let pairs := st.recPairs ++ st.mapPairs
  let a ← auditPairs pairs st.traceMismatch
  logInfo m!"FGCIRCUIT16 SNAPSHOT16 (one environment): {st.nodes} nodes visited; List.rec iota steps {st.recSteps} ({st.recPairs.length} distinct); mapFst sites {st.mapFstSites}, mapSnd sites {st.mapSndSites} ({st.mapPairs.length} distinct), MapStuck failed {st.mapStuckFail}; projRec {st.projRecSteps}, prodMk {st.prodMkSites}, unit {st.unitSites}, prodTy {st.prodTySites}; type-level unfoldings {st.tyUnfolds}; unfolded definitions (distinct {st.unfolded.length}): {(top st.unfolded).take 40}"
  logInfo m!"FGCIRCUIT16 EQUATION AUDIT (Lean isDefEq, default transparency, loose bvars closed by junk-typed fvars; an audit of the reduction, NOT a typed derivation): total {a.total}, ok {a.ok}, bad {a.bad}, err {a.err}, traceMismatch {a.traceMismatch}"
  match a.verdict with
  | .error msg => throwError "FGCIRCUIT16 EQUATION AUDIT FAILED (fail closed): {msg}"
  | .ok _ => pure ()
  logInfo m!"FGCIRCUIT16 EQUATION AUDIT: accepted (bad = err = traceMismatch = 0, {a.total} target pairs, non-empty)"
  logInfo m!"FGCIRCUIT16 MISSING (heads with no rule, stuck): {top st.heads}"
  for (c, e) in st.sample do
    let t := toString (← ppExpr e)
    logInfo m!"FGCIRCUIT16 MISSING sample (first stuck {c}, loose bvars are #n): {t.take 900}"
  logInfo m!"FGCIRCUIT16 TRACE: the traversal's own steps agree with whStepR/headRedexR in all cases ({st.traceMismatch} mismatches)"

end Tests.Gen5.FGCircuitPilotCheck16
