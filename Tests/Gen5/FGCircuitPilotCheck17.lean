import Tools.ShippingFGCircuitS1sCD
set_option autoImplicit false
-- FG circuit pilot S1s check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §23.

/-! # FGCircuitPilotCheck17

1. SIGNATURES: the new rules of `DW` (`bundle2`, `inhMk`, `inhDefault`), the changed `unf`, functionality, the carrier/obligation, the derived rules, the Lean equations, against independently written
   statements (`isDefEq`), with mutants (other function, swapped left/right, missing domain, instance erased / canonical default, ...) that must be rejected.
2. OLD RULES: every other constructor of `DZ` is the same in `DW`.
3. PATTERN: the rule patterns equal the Expr Lean's elaborator produces for `bundle2 a b` and `default`.
4. AUDIT (fail closed): equation pairs of the new rules; a verdict function with negative controls.
5. SNAPSHOT17 (ONE environment: the build's): the traversal with the new rules, where it stops next.
6. AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck17
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1sCD
open Tools.ShippingGen5ConstValueE Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)

/-! ## 1. expected statements, written independently -/

/-- `bundle2`. mu: 1 other function (`Signal.map`); 2 the left/right arguments are swapped in the pattern; 3 no domain judgement; 4 no left type judgement; 5 level `1`; 6 the right signal is judged at the LEFT type -/
def ExpBundle2 (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e d ta tb a b : Expr} {D : DomainConfig} {A B : Type} {av : Signal D A} {bv : Signal D B},
    e = (if mu == 1 then appN ``Signal.map [.zero] [d, ta, tb, a, b]
         else if mu == 2 then appN ``Sparkle.Core.Signal.bundle2 [.zero] [d, tb, ta, b, a]
         else appN ``Sparkle.Core.Signal.bundle2 [if mu == 5 then .succ .zero else .zero] [d, ta, tb, a, b]) →
    (if mu == 3 then True else DW env ρ d (.val DomainConfig D)) → (if mu == 4 then True else DW env ρ ta (.ty A)) → DW env ρ tb (.ty B) →
    DW env ρ a (.val (Signal D A) av) → DW env ρ b (.val (Signal D B) bv) → DW env ρ e (.val (Signal D (A × B)) (Sparkle.Core.Signal.bundle2 av bv))

/-- mutant 6 separately: the pair is built in the other order (types forced equal) -/
def ExpBundle2Swapped : Prop :=
  ∀ {env : Environment} {ρ : Val} {e d ta tb a b : Expr} {D : DomainConfig} {A : Type} {av bv : Signal D A},
    e = appN ``Sparkle.Core.Signal.bundle2 [.zero] [d, ta, tb, a, b] → DW env ρ d (.val DomainConfig D) → DW env ρ ta (.ty A) → DW env ρ tb (.ty A) →
    DW env ρ a (.val (Signal D A) av) → DW env ρ b (.val (Signal D A) bv) → DW env ρ e (.val (Signal D (A × A)) (Sparkle.Core.Signal.bundle2 bv av))
/-- the real rule specialised to equal types is NOT the swapped one -/
def ExpBundle2Spec : Prop :=
  ∀ {env : Environment} {ρ : Val} {e d ta tb a b : Expr} {D : DomainConfig} {A : Type} {av bv : Signal D A},
    e = appN ``Sparkle.Core.Signal.bundle2 [.zero] [d, ta, tb, a, b] → DW env ρ d (.val DomainConfig D) → DW env ρ ta (.ty A) → DW env ρ tb (.ty A) →
    DW env ρ a (.val (Signal D A) av) → DW env ρ b (.val (Signal D A) bv) → DW env ρ e (.val (Signal D (A × A)) (Sparkle.Core.Signal.bundle2 av bv))

/-- `inhMk`. mu: 1 the head is `Inhabited.default`; 2 level `0`; 3 no constructor condition; 4 the field type is not judged -/
def ExpInhMk (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e t x : Expr} {T : Type} {v : T} {cv : ConstructorVal},
    e = appN (if mu == 1 then ``Inhabited.default else ``Inhabited.mk) [if mu == 2 then .zero else .succ .zero] [t, x] →
    (if mu == 3 then True else env.find? ``Inhabited.mk = some (.ctorInfo cv)) → (if mu == 4 then True else DW env ρ t (.ty T)) →
    DW env ρ x (.val T v) → DW env ρ e (.val (Inhabited T) ⟨v⟩)

/-- mutant: the instance value is a CANONICAL default (an unrelated instance) instead of the one built from `v` -/
def ExpInhMkCanon : Prop :=
  ∀ {env : Environment} {ρ : Val} {e t x : Expr} {T : Type} {v : T} {cv : ConstructorVal} (d0 : Inhabited T),
    e = appN ``Inhabited.mk [.succ .zero] [t, x] → env.find? ``Inhabited.mk = some (.ctorInfo cv) → DW env ρ t (.ty T) →
    DW env ρ x (.val T v) → DW env ρ e (.val (Inhabited T) d0)

/-- `inhDefault`. mu: 1 the head is `Inhabited.mk`; 2 the instance argument is erased from the pattern; 3 no type judgement; 4 the value is the default of a DIFFERENT instance -/
def ExpInhDefault (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e t inst : Expr} {T : Type} {iv iv' : Inhabited T},
    e = appN (if mu == 1 then ``Inhabited.mk else ``Inhabited.default) [.succ .zero] (if mu == 2 then [t] else [t, inst]) →
    (if mu == 3 then True else DW env ρ t (.ty T)) → DW env ρ inst (.val (Inhabited T) iv) →
    DW env ρ e (.val T (if mu == 4 then iv'.default else iv.default))

/-- the real `inhDefault` has no second instance `iv'` (the shape above has one unused binder); this is the one without it -/
def ExpInhDefault0 : Prop :=
  ∀ {env : Environment} {ρ : Val} {e t inst : Expr} {T : Type} {iv : Inhabited T},
    e = appN ``Inhabited.default [.succ .zero] [t, inst] → DW env ρ t (.ty T) → DW env ρ inst (.val (Inhabited T) iv) → DW env ρ e (.val T iv.default)
def ExpInhDefaultCanon : Prop :=
  ∀ {env : Environment} {ρ : Val} {e t inst : Expr} {T : Type} {iv : Inhabited T} (d0 : T),
    e = appN ``Inhabited.default [.succ .zero] [t, inst] → DW env ρ t (.ty T) → DW env ρ inst (.val (Inhabited T) iv) → DW env ρ e (.val T d0)

/-- the stop condition of `unf` in DW. mu: 1 only the DZ stop condition; 2 only the new stop heads -/
def ExpUnfW (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e e' : Expr} {r : Res},
    (if mu == 1 then (if r.kind then headStop e else tyHeadStop e) = false
     else if mu == 2 then newStop e = false
     else ((if r.kind then headStop e else tyHeadStop e) || newStop e) = false) →
    unfoldAt env e = some e' → DW env ρ e' r → DW env ρ e r

def FunW : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDW env ρ e α v → CDW env ρ e α' v' → α = α' ∧ HEq v v'
def FunWOtherEnv : Prop :=
  ∀ {env env' : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDW env ρ e α v → CDW env' ρ e α' v' → α = α' ∧ HEq v v'
def FunWNoHEq : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDW env ρ e α v → CDW env ρ e α' v' → α = α'

noncomputable instance : Inhabited Environment := ⟨Classical.ofNonempty⟩

def ExpCircCVW (mu : Nat) : ConstValueRel := fun env X α v =>
  ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ (if mu == 3 then True else d.levelParams = []) ∧
    DW (if mu == 1 then default else env) (if mu == 2 then [⟨.const ``Nat [], ⟨Nat, 0⟩⟩] else []) d.value (.val α v)
def ExpHftObW (mu : Nat) : Environment → Prop := fun env =>
  DW env (if mu == 1 then [⟨.const ``Nat [], ⟨Nat, 0⟩⟩] else []) Tools.ShippingFGCircuitS1kStmt.hftRootValue
    (.val (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte)

/-- `dw_default_of_mk`. mu: 1 the outer head is `Inhabited.mk`; 2 the outer level is `0`; 3 the inner field is the type `t` (not `x`); 4 the type judgement `t` is dropped -/
def ExpDefaultOfMk (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {t x : Expr} {T : Type} {v : T} {cv : ConstructorVal},
    env.find? ``Inhabited.mk = some (.ctorInfo cv) → (if mu == 4 then True else DW env ρ t (.ty T)) → DW env ρ x (.val T v) →
    DW env ρ (appN (if mu == 1 then ``Inhabited.mk else ``Inhabited.default) [if mu == 2 then .zero else .succ .zero] [t, appN ``Inhabited.mk [.succ .zero] [t, if mu == 3 then t else x]]) (.val T v)
/-- mutant: the conclusion's value is an arbitrary `d0` -/
def ExpDefaultOfMkCanon : Prop :=
  ∀ {env : Environment} {ρ : Val} {t x : Expr} {T : Type} {v : T} {cv : ConstructorVal} (d0 : T),
    env.find? ``Inhabited.mk = some (.ctorInfo cv) → DW env ρ t (.ty T) → DW env ρ x (.val T v) →
    DW env ρ (appN ``Inhabited.default [.succ .zero] [t, appN ``Inhabited.mk [.succ .zero] [t, x]]) (.val T d0)

def ExpBundle2At (mu : Nat) : Prop :=
  ∀ {D : DomainConfig} {A B : Type} (a : Signal D A) (b : Signal D B) (t : Nat),
    (Sparkle.Core.Signal.bundle2 a b).val t = (if mu == 1 then (a.val (t + 1), b.val t) else (a.val t, b.val t))

/-- the swapped pair is only well-typed at one type `A`; `ExpBundle2AtSpec` is the correct statement at that shape (a control: the two differ) -/
def ExpBundle2Swap : Prop :=
  ∀ {D : DomainConfig} {A : Type} (a b : Signal D A) (t : Nat),
    (Sparkle.Core.Signal.bundle2 a b).val t = (b.val t, a.val t)
def ExpBundle2AtSpec : Prop :=
  ∀ {D : DomainConfig} {A : Type} (a b : Signal D A) (t : Nat),
    (Sparkle.Core.Signal.bundle2 a b).val t = (a.val t, b.val t)

def ExpProdInh (mu : Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {a b x y : Expr} {A B : Type} {xv : A} {yv : B} {cv cp : ConstructorVal},
    env.find? ``Inhabited.mk = some (.ctorInfo cv) → env.find? ``Prod.mk = some (.ctorInfo cp) → DW env ρ a (.ty A) → DW env ρ b (.ty B) → DW env ρ x (.val A xv) → DW env ρ y (.val B yv) →
    DW env ρ (appN ``Inhabited.mk [.succ .zero] [appN ``Prod [.zero, .zero] [a, b], appN ``Prod.mk [.zero, .zero] [a, b, x, y]]) (.val (Inhabited (A × B)) ⟨(xv, yv)⟩)

/-- the expected side is normalised first: this file's `Exp*` definitions are unfolded and the closed knob conditions `if mu == k then ..` are decided, so that `isDefEq` compares two concrete statements -/
def iteStep? (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars && !(e.getArg! 1).hasFVar then
    let r ← withDefault (whnf (e.getArg! 2))
    if r.isAppOf ``isTrue then return some (e.getArg! 3)
    if r.isAppOf ``isFalse then return some (e.getArg! 4)
  return none

def normExp (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let some e' ← iteStep? e then return .visit e'
    if let .const c _ := e.getAppFn then
      if (`Tests.Gen5.FGCircuitPilotCheck17).isPrefixOf c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

def sameT (thm : Name) (exp : Expr) : MetaM Unit := do
  let ci ← getConstInfo thm
  unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
  unless ← withDefault (isDefEq ci.type (← normExp exp)) do throwError "{thm}: type is NOT the expected statement"
def differsT (thm : Name) (mu : Expr) : MetaM Unit := do
  let ci ← getConstInfo thm
  let m ← normExp mu
  if ci.type == m then throwError "{thm}: the MUTANT is the same expression"
  if ← withDefault (isDefEq ci.type m) then throwError "{thm}: a MUTANT was accepted"
def qT (n : Name) (args : Array Expr) : MetaM Expr := mkAppM (`Tests.Gen5.FGCircuitPilotCheck17 ++ n) args
def natT (n : Nat) : Expr := toExpr n

-- Each SIGNATURES block is its own run_cmd (the single block timed out at 880 s); each counts its own successful checks (`same` = statement equal, `rej` = mutant rejected) and logs them; a failed check throws (fail closed).
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  let Q := `Tests.Gen5.FGCircuitPilotCheck17
  let mut nm : Nat := 0
  let mut ns : Nat := 0
  sameT (S ++ `DW.bundle2) (← qT `ExpBundle2 #[natT 0]); ns := ns + 1
  for m in [1, 2, 3, 4, 5] do differsT (S ++ `DW.bundle2) (← qT `ExpBundle2 #[natT m]); nm := nm + 1
  differsT (S ++ `DW.bundle2) (Lean.mkConst (Q ++ `ExpBundle2Swapped)); nm := nm + 1
  if ← withDefault (isDefEq (Lean.mkConst (Q ++ `ExpBundle2Swapped)) (Lean.mkConst (Q ++ `ExpBundle2Spec))) then throwError "control: swapped value equals the specialised rule"
  nm := nm + 1
  logInfo m!"FGCIRCUIT17 SIG-bundle2: {ns} statement equal, {nm} mutants rejected"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  let Q := `Tests.Gen5.FGCircuitPilotCheck17
  let mut nm : Nat := 0
  let mut ns : Nat := 0
  sameT (S ++ `DW.inhMk) (← qT `ExpInhMk #[natT 0]); ns := ns + 1
  for m in [1, 2, 3, 4] do differsT (S ++ `DW.inhMk) (← qT `ExpInhMk #[natT m]); nm := nm + 1
  differsT (S ++ `DW.inhMk) (Lean.mkConst (Q ++ `ExpInhMkCanon)); nm := nm + 1
  sameT (S ++ `DW.inhDefault) (Lean.mkConst (Q ++ `ExpInhDefault0)); ns := ns + 1
  differsT (S ++ `DW.inhDefault) (Lean.mkConst (Q ++ `ExpInhDefaultCanon)); nm := nm + 1
  for m in [1, 2, 3, 4] do
    -- the mutants carry one more (unused) instance binder, so they differ from the real rule at once; that alone proves nothing, therefore the real rule is compared to the 0-shape above
    differsT (S ++ `DW.inhDefault) (← qT `ExpInhDefault #[natT m]); nm := nm + 1
  logInfo m!"FGCIRCUIT17 SIG-inh: {ns} statements equal, {nm} mutants rejected"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  sameT (S ++ `DW.unf) (← qT `ExpUnfW #[natT 0])
  logInfo m!"FGCIRCUIT17 SIG-unf: DW.unf statement equal (0 mutants here)"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  let mut nm : Nat := 0
  differsT (S ++ `DW.unf) (← qT `ExpUnfW #[natT 1]); nm := nm + 1
  logInfo m!"FGCIRCUIT17 SIG-unf-mutant1: {nm} mutant rejected"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  let mut nm : Nat := 0
  differsT (S ++ `DW.unf) (← qT `ExpUnfW #[natT 2]); nm := nm + 1
  logInfo m!"FGCIRCUIT17 SIG-unf-mutant2: {nm} mutant rejected"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  let Q := `Tests.Gen5.FGCircuitPilotCheck17
  let mut nm : Nat := 0
  sameT (S ++ `cdw_fun) (Lean.mkConst (Q ++ `FunW))
  for mu in ["FunWOtherEnv", "FunWNoHEq"] do
    differsT (S ++ `cdw_fun) (Lean.mkConst (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT17 SIG-fun: cdw_fun statement equal, {nm} mutants rejected"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  let mut nm : Nat := 0
  let cvDef := (← getConstInfo (S ++ `CircCVW)).value!
  unless ← withDefault (isDefEq cvDef (← qT `ExpCircCVW #[natT 0])) do throwError "CircCVW: definition is NOT the expected one"
  for m in [1, 2, 3] do
    if ← withDefault (isDefEq cvDef (← qT `ExpCircCVW #[natT m])) then throwError "CircCVW: MUTANT {m} accepted"
    nm := nm + 1
  logInfo m!"FGCIRCUIT17 SIG-circcvw: definition equal, {nm} mutants rejected"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  let mut nm : Nat := 0
  let obW := (← getConstInfo (S ++ `HftObCDW)).value!
  unless ← withDefault (isDefEq obW (← qT `ExpHftObW #[natT 0])) do throwError "HftObCDW: definition is NOT the expected one"
  if ← withDefault (isDefEq obW (← qT `ExpHftObW #[natT 1])) then throwError "HftObCDW: MUTANT accepted"
  nm := nm + 1
  -- HftObCDW is a different obligation from HftObCDZ (new family)
  let obZ := (← getConstInfo (`Tools.ShippingFGCircuitS1rCD ++ `HftObCDZ)).value!
  if ← withDefault (isDefEq obW obZ) then throwError "HftObCDW and HftObCDZ are the same"
  nm := nm + 1
  -- the final consumer is the S1k statement with hcd replaced by HftObCDW (explicit connection)
  let cons := (← getConstInfo (S ++ `HftFinalStmtW)).value!
  let expCons ← mkAppM `Tools.ShippingFGCircuitS1rCD.Stmt.HftFinalStmtWith #[Lean.mkConst (S ++ `HftObCDW)]
  unless ← withDefault (isDefEq cons expCons) do throwError "HftFinalStmtW is NOT HftFinalStmtWith HftObCDW"
  logInfo m!"FGCIRCUIT17 SIG-ob: HftObCDW definition equal, HftFinalStmtW = HftFinalStmtWith HftObCDW, {nm} mutants/controls rejected"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  let Q := `Tests.Gen5.FGCircuitPilotCheck17
  let mut nm : Nat := 0
  sameT (S ++ `bundle2_val_at) (← qT `ExpBundle2At #[natT 0])
  differsT (S ++ `bundle2_val_at) (← qT `ExpBundle2At #[natT 1]); nm := nm + 1
  differsT (S ++ `bundle2_val_at) (Lean.mkConst (Q ++ `ExpBundle2Swap)); nm := nm + 1
  if ← withDefault (isDefEq (Lean.mkConst (Q ++ `ExpBundle2Swap)) (Lean.mkConst (Q ++ `ExpBundle2AtSpec))) then throwError "control: swapped bundle2_val_at equals the correct statement"
  nm := nm + 1
  sameT (S ++ `dw_default_of_mk) (← qT `ExpDefaultOfMk #[natT 0])
  for m in [1, 2, 3, 4] do differsT (S ++ `dw_default_of_mk) (← qT `ExpDefaultOfMk #[natT m]); nm := nm + 1
  differsT (S ++ `dw_default_of_mk) (Lean.mkConst (Q ++ `ExpDefaultOfMkCanon)); nm := nm + 1
  sameT (S ++ `dw_prod_inhabited) (← qT `ExpProdInh #[natT 0])
  logInfo m!"FGCIRCUIT17 SIG-derived: bundle2_val_at, dw_default_of_mk, dw_prod_inhabited statements equal, {nm} mutants rejected"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  -- OLD RULES: every DZ constructor other than `unf` is the same in DW
  let mut nOld : Nat := 0
  let rn (e : Expr) : Expr := e.replace fun x => if x.isConstOf `Tools.ShippingFGCircuitS1rCD.DZ then some (Lean.mkConst (S ++ `DW) x.constLevels!) else none
  for c in [`nat, `bool, `domainConfig, `bitvec, `signal, `bvar, `natLit, `domDefault, `bvOfNat, `bvInhabited, `boolInhabited, `sigPure, `sigRegister, `sigMux, `sigAddBV, `sigLoop, `lam, `letE, `sigBeqBV,
      `sigAndBool, `sigOrBool, `sigNotBool, `bvAbbrev, `beta, `zeta, `projStep, `projCtor, `recIota, `projRec, `prodTy, `punitTy, `unitVal, `prodMk, `mapFst, `mapSnd] do
    let a ← getConstInfo (`Tools.ShippingFGCircuitS1rCD ++ `DZ ++ c)
    let b ← getConstInfo (S ++ `DW ++ c)
    unless ← withDefault (isDefEq (rn a.type) b.type) do throwError "{c}: DW rule differs from the DZ rule"
    nOld := nOld + 1
  do
    let a ← getConstInfo (`Tools.ShippingFGCircuitS1rCD ++ `DZ ++ `sigPure)
    let b ← getConstInfo (S ++ `DW ++ `sigMux)
    if ← withDefault (isDefEq (rn a.type) b.type) then throwError "control: sigMux accepted as sigPure"
  -- the number of constructors: DZ + 3
  let some (.inductInfo iz) := (← getEnv).find? `Tools.ShippingFGCircuitS1rCD.DZ | throwError "DZ"
  let some (.inductInfo iw) := (← getEnv).find? (S ++ `DW) | throwError "DW"
  unless iw.ctors.length == iz.ctors.length + 3 do throwError "DW has {iw.ctors.length} constructors, DZ {iz.ctors.length}"
  logInfo m!"FGCIRCUIT17 OLD RULES: {nOld} constructors of DZ are the same in DW (only `unf` changed, compared above); DW has exactly 3 more constructors than DZ ({iz.ctors.length} → {iw.ctors.length}); a control rejects a changed rule"

/-! ## 2. PATTERN: the rule patterns are the Expr Lean's elaborator produces -/

run_cmd liftTermElabM do
  let natE := Lean.mkConst ``Nat
  let boolE := Lean.mkConst ``Bool
  let dT := Lean.mkConst ``Sparkle.Core.Domain.DomainConfig
  let sigT (d t : Expr) := mkApp2 (Lean.mkConst ``Signal [.zero]) d t
  withLocalDecl `D .default dT fun D => withLocalDecl `a .default (sigT D natE) fun a => withLocalDecl `b .default (sigT D boolE) fun b => do
    let stx ← `(Sparkle.Core.Signal.bundle2 $(← Term.exprToSyntax a) $(← Term.exprToSyntax b))
    let e1 ← instantiateMVars (← Term.elabTerm stx none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e1 ← instantiateMVars e1
    let pat := appN ``Sparkle.Core.Signal.bundle2 [.zero] [D, natE, boolE, a, b]
    unless e1 == pat do throwError "PATTERN: the elaborated `bundle2 a b` is not the rule's pattern: {e1} vs {pat}"
    let pat2 := appN ``Sparkle.Core.Signal.bundle2 [.zero] [D, boolE, natE, b, a]
    if e1 == pat2 then throwError "PATTERN control: swapped pattern equals"
    let env ← getEnv
    -- `bundle2` unfolds (so `unf` would apply to it without the stop head)
    unless (unfoldAt env e1).isSome do throwError "PATTERN: bundle2 does not unfold"
    unless newStop e1 do throwError "PATTERN: bundle2 is not a stop head"
    logInfo m!"FGCIRCUIT17 PATTERN: the elaborated `bundle2 a b` is exactly the rule's pattern (bundle2 at level 0, D, Nat, Bool, a, b); it is a stop head of unf; a swapped pattern is rejected"
  -- `default` at a pair type is `Inhabited.default.{1} (Nat × Bool) inst` and `instInhabitedProd` unfolds to `Inhabited.mk`
  let stx ← `((default : Nat × Bool))
  let e2 ← instantiateMVars (← Term.elabTerm stx none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e2 ← instantiateMVars e2
  let args := appArgs e2
  unless (appFn e2).isConstOf ``Inhabited.default && args.length == 2 do throwError "PATTERN: `default` is not Inhabited.default T inst: {e2}"
  unless (appFn e2).constLevels! == [.succ .zero] do throwError "PATTERN: Inhabited.default level"
  let env ← getEnv
  let inst := args[1]!
  match unfoldAt env inst with
  | some u =>
    unless (appFn u).isConstOf ``Inhabited.mk do logInfo m!"FGCIRCUIT17 PATTERN: note: the first unfolding of the instance is headed by {appFn u}"
    pure ()
  | none => throwError "PATTERN: the instance does not unfold"
  logInfo m!"FGCIRCUIT17 PATTERN: `default : Nat × Bool` elaborates to `Inhabited.default.\{1} T inst` (2 arguments, level 1): the rule's pattern; the instance argument is kept"

/-! ## 3. AUDIT: the fail-closed verdict (copy of the Check16 verdict) -/

structure Audit where
  total : Nat := 0
  ok : Nat := 0
  bad : Nat := 0
  err : Nat := 0
  traceMismatch : Nat := 0

def Audit.verdict (a : Audit) : Except String Unit :=
  if a.total == 0 then .error "the target pair set is EMPTY"
  else if a.bad != 0 then .error s!"{a.bad} pairs are NOT defeq"
  else if a.err != 0 then .error s!"{a.err} pairs threw"
  else if a.traceMismatch != 0 then .error s!"{a.traceMismatch} trace mismatches"
  else if a.ok != a.total then .error "ok ≠ total"
  else .ok ()

partial def withFVs {α : Type} (n : Nat) (k : Array Lean.Expr → MetaM α) (acc : Array Lean.Expr := #[]) : MetaM α :=
  if acc.size == n then k acc else withLocalDecl `x .default (Lean.mkConst ``Nat) fun f => withFVs n k (acc.push f)

/-- close the loose bvars of the pairs by fresh fvars (a junk type: for the traversal pairs this is an AUDIT of the reduction, not a typed derivation; the typed controls are closed terms) and ask `isDefEq` (default transparency) -/
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
  let sigT (d t : Expr) := mkApp2 (Lean.mkConst ``Signal [.zero]) d t
  let expectReject (what : String) (a : Audit) : MetaM Unit :=
    match a.verdict with
    | .error _ => pure ()
    | .ok _ => throwError "AUDIT control: {what} was ACCEPTED"
  withLocalDecl `D .default dT fun D => withLocalDecl `a .default (sigT D natE) fun a => withLocalDecl `b .default (sigT D natE) fun b => do
    let mk (x y : Expr) := mkAppM ``Sparkle.Core.Signal.bundle2 #[x, y]
    let bab ← mk a b
    let bba ← mk b a
    -- (1) the rule's equations at the signal level: `bundle2 a b` is the `Signal.mk` pairing, the `seq`/`map` form and the `ap` form
    let stxP ← `((⟨fun t => (Signal.val $(← Term.exprToSyntax a) t, Signal.val $(← Term.exprToSyntax b) t)⟩ : Signal $(← Term.exprToSyntax D) (Nat × Nat)))
    let mkPair ← instantiateMVars (← Term.elabTerm stxP none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let mkPair ← instantiateMVars mkPair
    let good ← auditPairs [(bab, bab), (bab, mkPair)] 0
    unless good.verdict matches .ok _ do throwError "AUDIT control: the correct pairs were not accepted ({good.ok}/{good.total}, bad {good.bad}, err {good.err})"
    -- (2) the swapped pair is rejected
    expectReject "the swapped bundle2 (left/right)" (← auditPairs [(bab, bba)] 0)
    expectReject "the swapped bundle2 among correct ones" (← auditPairs [(bab, bab), (bab, bba)] 0)
  expectReject "an empty target pair set" (← auditPairs [] 0)
  expectReject "a trace mismatch" { total := 1, ok := 1, traceMismatch := 1 }
  expectReject "a thrown pair" { total := 1, ok := 0, err := 1 }
  expectReject "ok ≠ total" { total := 2, ok := 1 }
  unless ({ total := 2, ok := 2 } : Audit).verdict matches .ok _ do throwError "AUDIT control: the verdict rejects an all-ok audit"
  expectReject "Nat vs Bool" (← auditPairs [(natE, boolE)] 0)
  -- (3) Inhabited: two instances of the same type with different defaults give different defaults (typed, closed)
  let i0 ← mkAppM ``Inhabited.mk #[toExpr (0 : Nat)]
  let i5 ← mkAppM ``Inhabited.mk #[toExpr (5 : Nat)]
  let d0 ← mkAppM ``Inhabited.default #[i0]
  let d5 ← mkAppM ``Inhabited.default #[i5]
  expectReject "default of ⟨0⟩ vs default of ⟨5⟩" (← auditPairs [(d0, d5)] 0)
  unless (← auditPairs [(d0, toExpr (0 : Nat)), (d5, toExpr (5 : Nat))] 0).verdict matches .ok _ do throwError "AUDIT control: default of ⟨v⟩ is not v"
  logInfo m!"FGCIRCUIT17 AUDIT CONTROLS: the verdict rejects a swapped bundle2 (also among correct ones), an empty target set, a trace mismatch, a thrown pair, ok ≠ total, Nat vs Bool, default of ⟨0⟩ vs ⟨5⟩; accepts the Signal.mk pairing of bundle2, and `default ⟨v⟩ = v`"

/-! ## 4. SNAPSHOT17 -/

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
  bundle2Sites : Nat := 0
  inhMkSites : Nat := 0
  inhDefSites : Nat := 0

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
        else if c == ``Sparkle.Core.Signal.bundle2 && ls == [.zero] && args.length == 5 then do
          -- the new rule `bundle2`
          modify fun s => { s with bundle2Sites := s.bundle2Sites + 1 }
          sub [0, 3, 4]; tys [1, 2]
        else if c == ``Inhabited.mk && ls == [.succ .zero] && args.length == 2 && (match env.find? ``Inhabited.mk with | some (.ctorInfo _) => true | _ => false) then do
          modify fun s => { s with inhMkSites := s.inhMkSites + 1 }
          tys [0]; sub [1]
        else if c == ``Inhabited.default && ls == [.succ .zero] && args.length == 2 then do
          modify fun s => { s with inhDefSites := s.inhDefSites + 1 }
          tys [0]; sub [1]
        else if c == ``Prod.mk && ls == [.zero, .zero] && args.length == 4 && (match env.find? ``Prod.mk with | some (.ctorInfo _) => true | _ => false) then do
          modify fun s => { s with prodMkSites := s.prodMkSites + 1 }
          tys [0, 1]; sub [2, 3]
        else if c == ``PUnit.unit && ls == [.succ .zero] && args.length == 0 && (match env.find? ``PUnit.unit with | some (.ctorInfo _) => true | _ => false) then
          modify fun s => { s with unitSites := s.unitSites + 1 }
        else generic
    | h => modify fun s => { s with heads := bump s.heads s!"{pre}<{h.ctorName}> application" }
end

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let env ← getEnv
  let some ci := env.find? `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte | throwError "root missing"
  unless ci.value! == Tools.ShippingFGCircuitS1kStmt.hftRootValue do throwError "the root's value in this environment differs from hftRootValue"
  let st := (recog false env 4000 ci.value!).run {} |>.2
  let top (l : List (String × Nat)) := (l.toArray.qsort (fun a b => a.2 > b.2)).toList
  let a ← auditPairs (st.recPairs ++ st.mapPairs) st.traceMismatch
  logInfo m!"FGCIRCUIT17 SNAPSHOT17 (one environment): {st.nodes} nodes visited; List.rec iota steps {st.recSteps} ({st.recPairs.length} distinct); mapFst {st.mapFstSites}, mapSnd {st.mapSndSites}; bundle2 sites {st.bundle2Sites}; Inhabited.mk sites {st.inhMkSites}; Inhabited.default sites {st.inhDefSites}; projRec {st.projRecSteps}, prodMk {st.prodMkSites}, unit {st.unitSites}, prodTy {st.prodTySites}; unfolded definitions (distinct {st.unfolded.length}): {(top st.unfolded).take 60}"
  logInfo m!"FGCIRCUIT17 EQUATION AUDIT (Lean isDefEq on the traversal's rewrite pairs; an audit, NOT a typed derivation): total {a.total}, ok {a.ok}, bad {a.bad}, err {a.err}, traceMismatch {a.traceMismatch}"
  match a.verdict with
  | .error msg => throwError "FGCIRCUIT17 EQUATION AUDIT FAILED (fail closed): {msg}"
  | .ok _ => pure ()
  logInfo m!"FGCIRCUIT17 MISSING (heads with no rule, stuck): {top st.heads}"
  for (c, e) in st.sample do
    let t := toString (← ppExpr e)
    logInfo m!"FGCIRCUIT17 MISSING sample (first stuck {c}, loose bvars are #n): {t.take 900}"
  logInfo m!"FGCIRCUIT17 TRACE: {st.traceMismatch} mismatches with whStepR/headRedexR"

/-! ## 5. AXIOMS -/
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1sCD
  let names : List Name := [S ++ `bundle2_val_at, S ++ `bundle2_eq_mk, S ++ `bundle2_eq_seq, S ++ `bundle2_eq_ap, S ++ `seq_val_at, S ++ `ap_val_at, S ++ `bundle2_fst_at, S ++ `bundle2_snd_at,
    S ++ `bundle2_swap_ne, S ++ `inhabited_default_mk, S ++ `inhabited_prod_mk, S ++ `inhabited_inst_prod, S ++ `inhabited_instances_differ, S ++ `loop_val_eq, S ++ `dw_signalMk_false,
    S ++ `mapStuckW_unf_false, S ++ `dw_fun, S ++ `cdw_fun, S ++ `tdw_fun, S ++ `cdw_eq, S ++ `dw_default_of_mk, S ++ `dw_prod_inhabited, S ++ `circCVW_functional, S ++ `circCVW_hft_of_obCDW,
    S ++ `circCVW_at_of_getEnv, S ++ `circCVW_hft_run]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT17 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck17
