import Tools.ShippingFGCircuitS1mCD
import Tools.ShippingFGCircuitS1kStmt
set_option autoImplicit false
-- FG circuit pilot S1m check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §17.

/-! # FGCircuitPilotCheck11

1. SIGNATURES: the complete types of the four new rules of `CDX`, of the embedding `cdx_of_cd`/`tdx_of_td`, and of the functionality theorems `cdx_fun`/`tdx_fun`, against independently written
   statements (`isDefEq`), with mutants that must be rejected. The 14 old rules of `CDX` are the rules of `CD` with the environment threaded (structural comparison).
2. OPS: the own substitution (`instE`, `betaApp`, `instLE`) agrees with Lean's `instantiate`/`beta`/`instantiateLevelParams` on the declarations in the closure of the root, and on unit controls.
3. AXIOMS.
4. SNAPSHOT11 (ONE environment: the build's): the first reduction steps of the root's body by the rules' own functions, and the precise list of subterms (stuck heads) for which `CDX` still has no rule. -/
namespace Tests.Gen5.FGCircuitPilotCheck11
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingGen5ConstValueE

/-! ## 1. expected statements, written independently (knobs: one per mutant) -/

def ExpUnf (stopKnob : Nat) (keepRho : Bool) (concl : Bool) (swapUnf : Bool) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e e' : Expr} {α : Type} {v : α},
    (if stopKnob == 0 then headStop e = false else if stopKnob == 1 then headStop e = true else True) →
    (if swapUnf then unfoldAt env e' = some e else unfoldAt env e = some e') →
    CDX env (if keepRho then ρ else []) e' α v →
    (if concl then CDX env ρ e α v else CDX env ρ e' α v)

def ExpBeta (useBeta : Bool) (concl : Bool) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e e' : Expr} {α : Type} {v : α},
    (if useBeta then headRedex env e = some e' else unfoldAt env e = some e') →
    CDX env ρ e' α v →
    (if concl then CDX env ρ e α v else CDX env ρ e' α v)

def ExpZeta (needCore : Bool) (substBody : Bool) (coreVal : Bool) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {α : Type} {r : α},
    e = .letE n A v body nd →
    (if needCore then coreHead A = coreVal else True) →
    CDX env ρ (if substBody then instE body v 0 else body) α r →
    CDX env ρ e α r

def ExpProjStep (useWh : Bool) (keepProj : Bool) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {α : Type} {v : α},
    e = .proj S i x →
    (if useWh then whStep env x = some x' else unfoldAt env x = some x') →
    CDX env ρ (if keepProj then .proj S i x' else x') α v →
    CDX env ρ e α v

def ExpProjCtor (needInd needCount : Bool) (fieldIdx : Nat → Nat → Nat) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e x fld : Expr} {S ctor : Name} {ls : List Level} {cv : ConstructorVal} {i : Nat} {α : Type} {v : α},
    e = .proj S i x →
    appFn x = .const ctor ls →
    env.find? ctor = some (.ctorInfo cv) →
    (if needInd then cv.induct = S else True) →
    (if needCount then (appArgs x).length = cv.numParams + cv.numFields else True) →
    (appArgs x)[fieldIdx cv.numParams i]? = some fld →
    CDX env ρ fld α v →
    CDX env ρ e α v

def UnfTrue := ExpUnf 0 true true false
def UnfNoStop := ExpUnf 2 true true false
def UnfStopTrue := ExpUnf 1 true true false
def UnfResetRho := ExpUnf 0 false true false
def UnfConclE' := ExpUnf 0 true false false
def UnfSwapped := ExpUnf 0 true true true

def BetaTrue := ExpBeta true true
def BetaUnfoldInstead := ExpBeta false true
def BetaConclE' := ExpBeta true false

def ZetaTrue := ExpZeta true true false
def ZetaNoCore := ExpZeta false true false
def ZetaNoSubst := ExpZeta true false false
def ZetaCoreTrue := ExpZeta true true true

def StepTrue := ExpProjStep true true
def StepUnfoldOnly := ExpProjStep false true
def StepDropsProj := ExpProjStep true false

def CtorTrue := ExpProjCtor true true (fun np i => np + i)
def CtorNoInd := ExpProjCtor false true (fun np i => np + i)
def CtorNoCount := ExpProjCtor true false (fun np i => np + i)
def CtorFieldI := ExpProjCtor true true (fun _ i => i)
def CtorParamsOnly := ExpProjCtor true true (fun np _ => np)

/-- the embedding. Knobs: the direction, the valuation of the conclusion, the environment threaded -/
def ExpEmbedCD (rev : Bool) (resetRho : Bool) : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v : α},
    (if rev then CDX env ρ e α v else CD ρ e α v) → CDX env (if resetRho then [] else ρ) e α v
def ExpEmbedTD : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {T : Type}, TD ρ e T → TDX env ρ e T

/-- functionality, and mutants: the second derivation in another environment / valuation, no `HEq` of the values -/
def FunTrue : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDX env ρ e α v → CDX env ρ e α' v' → α = α' ∧ HEq v v'
def FunOtherEnv : Prop :=
  ∀ {env env' : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDX env ρ e α v → CDX env' ρ e α' v' → α = α' ∧ HEq v v'
def FunOtherRho : Prop :=
  ∀ {env : Environment} {ρ ρ' : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDX env ρ e α v → CDX env ρ' e α' v' → α = α' ∧ HEq v v'
def FunNoHEq : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'}, CDX env ρ e α v → CDX env ρ e α' v' → α = α'
def FunTDTrue : Prop :=
  ∀ {env : Environment} {ρ : Val} {e : Expr} {T T' : Type}, TDX env ρ e T → TDX env ρ e T' → T = T'
def FunTDOtherEnv : Prop :=
  ∀ {env env' : Environment} {ρ : Val} {e : Expr} {T T' : Type}, TDX env ρ e T → TDX env' ρ e T' → T = T'

def varBad : Expr := .lam `x (.const ``Nat []) (.bvar 0) .default

/-- erase the environment and the result index of `DX` to get `TD`/`CD` -/
def eraseEnv (e : Lean.Expr) : MetaM Lean.Expr :=
  Core.transform e (post := fun e => do
    if e.getAppFn.isConstOf ``DX && e.getAppNumArgs == 4 then
      let a := e.getAppArgs
      let r := a[3]!
      if r.getAppFn.isConstOf ``Res.val && r.getAppNumArgs == 2 then
        return .done (mkAppN (mkConst ``CD) #[a[1]!, a[2]!, r.getAppArgs[0]!, r.getAppArgs[1]!])
      else if r.getAppFn.isConstOf ``Res.ty && r.getAppNumArgs == 1 then
        return .done (mkAppN (mkConst ``TD) #[a[1]!, a[2]!, r.getAppArgs[0]!])
      else return .done e
    else return .done e)

set_option maxHeartbeats 16000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    unless ← withDefault (isDefEq ci.type (mkConst exp)) do throwError "{thm}: type is NOT the expected statement {exp}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    if ← withDefault (isDefEq ci.type (mkConst mu0)) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let S := `Tools.ShippingFGCircuitS1mCD
  let Q := `Tests.Gen5.FGCircuitPilotCheck11
  let mut nm : Nat := 0
  -- the four new rules
  same (S ++ `DX.unf) (Q ++ `UnfTrue)
  same (S ++ `DX.beta) (Q ++ `BetaTrue)
  for mu in ["BetaUnfoldInstead", "BetaConclE'"] do
    differs (S ++ `DX.beta) (Q ++ Name.mkSimple mu); nm := nm + 1
  same (S ++ `DX.zeta) (Q ++ `ZetaTrue)
  same (S ++ `DX.projStep) (Q ++ `StepTrue)
  same (S ++ `DX.projCtor) (Q ++ `CtorTrue)
  for mu in ["UnfNoStop", "UnfStopTrue", "UnfResetRho", "UnfConclE'", "UnfSwapped"] do
    differs (S ++ `DX.unf) (Q ++ Name.mkSimple mu); nm := nm + 1
  for mu in ["ZetaNoCore", "ZetaNoSubst", "ZetaCoreTrue"] do
    differs (S ++ `DX.zeta) (Q ++ Name.mkSimple mu); nm := nm + 1
  for mu in ["StepUnfoldOnly", "StepDropsProj"] do
    differs (S ++ `DX.projStep) (Q ++ Name.mkSimple mu); nm := nm + 1
  for mu in ["CtorNoInd", "CtorNoCount", "CtorFieldI", "CtorParamsOnly"] do
    differs (S ++ `DX.projCtor) (Q ++ Name.mkSimple mu); nm := nm + 1
  -- the embedding
  let e1 ← mkAppM ``ExpEmbedCD #[mkConst ``false, mkConst ``false]
  let ci ← getConstInfo (S ++ `cdx_of_cd)
  unless ← withDefault (isDefEq ci.type e1) do throwError "cdx_of_cd: type is NOT the expected statement"
  for (r, z) in [(true, false), (false, true)] do
    let m ← mkAppM ``ExpEmbedCD #[toExpr r, toExpr z]
    if ← withDefault (isDefEq ci.type m) then throwError "cdx_of_cd: a MUTANT (rev {r}, reset {z}) was accepted"
    nm := nm + 1
  let ciT ← getConstInfo (S ++ `tdx_of_td)
  unless ← withDefault (isDefEq ciT.type (mkConst (Q ++ `ExpEmbedTD))) do throwError "tdx_of_td: type is NOT the expected statement"
  -- functionality
  same (S ++ `cdx_fun) (Q ++ `FunTrue)
  for mu in ["FunOtherEnv", "FunOtherRho", "FunNoHEq"] do
    differs (S ++ `cdx_fun) (Q ++ Name.mkSimple mu); nm := nm + 1
  same (S ++ `tdx_fun) (Q ++ `FunTDTrue)
  differs (S ++ `tdx_fun) (Q ++ `FunTDOtherEnv); nm := nm + 1
  -- the 14 old rules of CDX (+ 5 of TDX) are the old rules with the environment threaded
  let mut nOld : Nat := 0
  for (oldT, newT, ctors) in [(``CD, ``DX, [`bvar, `natLit, `domDefault, `bvOfNat, `bvInhabited, `boolInhabited, `sigPure, `sigRegister, `sigMux, `sigAddBV, `sigLoop, `lam, `letE, `sigBeqBV, `sigAndBool, `sigOrBool, `sigNotBool, `bvAbbrev]),
      (``TD, ``DX, [`nat, `bool, `domainConfig, `bitvec, `signal])] do
    for c in ctors do
      let oi ← getConstInfo (oldT ++ c)
      let ni ← getConstInfo (newT ++ c)
      let er ← eraseEnv ni.type
      let some body := (match er with | .forallE _ _ b _ => some b | _ => none) | throwError "{newT ++ c}: not a forall"
      let body := body.instantiate1 (mkConst ``Nat)
      unless ← withDefault (isDefEq body oi.type) do throwError "{newT ++ c}: is not the rule {oldT ++ c} with the environment threaded"
      nOld := nOld + 1
  -- a control: the comparison rejects a changed rule (CDX.sigMux against CD.sigPure)
  do
    let oi ← getConstInfo (``CD ++ `sigPure)
    let ni ← getConstInfo (``DX ++ `sigMux)
    let er ← eraseEnv ni.type
    let some body := (match er with | .forallE _ _ b _ => some b | _ => none) | throwError "x"
    if ← withDefault (isDefEq (body.instantiate1 (mkConst ``Nat)) oi.type) then throwError "control: sigMux accepted as sigPure"
    nm := nm + 1
  logInfo m!"FGCIRCUIT11 SIGNATURES: the five new rules (DX.unf/beta/zeta/projStep/projCtor), the embeddings cdx_of_cd/tdx_of_td, the functionality theorems cdx_fun/tdx_fun match the independently written statements; {nOld} old rules of CD/TD are in CDX unchanged (environment threaded); {nm} mutants rejected"

/-! ## 2. OPS: the own Expr operations against Lean's -/

example : instE (.bvar 0) (.bvar 7) 0 = .bvar 7 := rfl
example : instE (.lam `x (.const ``Nat []) (.bvar 1) .default) (.bvar 7) 0 = .lam `x (.const ``Nat []) (.bvar 8) .default := rfl
example : instE (.app (.bvar 1) (.bvar 0)) (.const ``Nat []) 0 = .app (.bvar 0) (.const ``Nat []) := rfl
example : betaApp (.lam `x (.const ``Nat []) (.lam `y (.const ``Nat []) (.app (.bvar 1) (.bvar 0)) .default) .default) [.bvar 3, .bvar 4] = .app (.bvar 3) (.bvar 4) := rfl
example : betaApp (.const ``Nat []) [.bvar 3] = .app (.const ``Nat []) (.bvar 3) := rfl
example : appFn (appN ``Signal.pure [.zero] [.bvar 0, .bvar 1, .bvar 2]) = .const ``Signal.pure [.zero] := appFn_appN _ _ _
example : appArgs (appN ``Signal.pure [.zero] [.bvar 0, .bvar 1, .bvar 2]) = [.bvar 0, .bvar 1, .bvar 2] := rfl

/-! ## 2b. the new rules are usable: small derivations from table facts (not vacuous) -/

def natE (n : Nat) : Lean.Expr := appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]
def pairE : Lean.Expr := appN ``Prod.mk [.zero, .zero] [.const ``Nat [], .const ``Nat [], natE 3, natE 4]
def Γp : Name → Option CtorRow := fun c => if c == ``Prod.mk then some ⟨``Prod, 2, 2⟩ else none
def miniName : Name := `Tests.mini
def miniValue : Lean.Expr := appN ``Signal.pure [.zero] [.const ``Sparkle.Core.Domain.defaultDomain [], .const ``Nat [], natE 5]
def Δm : Name → Option DefRow := fun c => if c == miniName then some ⟨[], miniValue⟩ else none

/-- `(3, 4).1` denotes `3`: `projCtor` from the constructor row of `Prod.mk` -/
theorem ex_projCtor (env : Environment) (hΓ : EnvCtors env Γp) : CDX env [] (.proj ``Prod 0 pairE) Nat 3 :=
  cdx_projCtor_tbl hΓ (r := ⟨``Prod, 2, 2⟩) (i := 0) rfl (appFn_appN _ _ _) rfl rfl (by decide) rfl (.natLit rfl)

/-- a user definition `mini := Signal.pure 5` denotes `Signal.pure 5`: `unf` from the definition row -/
theorem ex_unf (env : Environment) (hΔ : EnvDefs env Δm) :
    CDX env [] (.const miniName []) (Signal defaultDomain Nat) (Signal.pure 5) :=
  cdx_unf_tbl hΔ (r := ⟨[], miniValue⟩) rfl (by decide) rfl rfl rfl (.sigPure rfl (.domDefault rfl) (.nat rfl) (.natLit rfl))

/-- a `let` of a non-core type is substituted: `let p : Prod Nat Nat := (3,4); p.1` denotes `3` (`zeta`, then `projCtor`) -/
theorem ex_zeta (env : Environment) (hΓ : EnvCtors env Γp) :
    CDX env [] (.letE `p (appN ``Prod [.zero, .zero] [.const ``Nat [], .const ``Nat []]) pairE (.proj ``Prod 0 (.bvar 0)) false) Nat 3 :=
  .zeta rfl (by decide) (cdx_projCtor_tbl hΓ (r := ⟨``Prod, 2, 2⟩) (i := 0) (x := pairE) rfl (appFn_appN _ _ _) rfl rfl (by decide) rfl (.natLit rfl))

/-! ## 3. AXIOMS -/
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS1mCD
  let names : List Name := [S ++ `tdx_of_td, S ++ `cdx_of_cd, S ++ `circCV_to_X, S ++ `tdx_fun, S ++ `cdx_fun, S ++ `cdx_eq, S ++ `circCVX_functional,
    S ++ `cdx_unf_tbl, S ++ `cdx_projCtor_tbl, S ++ `appFn_appN, S ++ `coreHead_td, S ++ `dx_fun, S ++ `whStep_ctor, `Tests.Gen5.FGCircuitPilotCheck11.ex_projCtor, `Tests.Gen5.FGCircuitPilotCheck11.ex_unf, `Tests.Gen5.FGCircuitPilotCheck11.ex_zeta]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT11 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT11 -/

/-- a recognizer that follows the rules' own shapes and functions (`CDX`'s premises) and collects what has no rule. It is NOT a proof; it reports where a derivation cannot continue. -/
structure Stuck where
  heads : List (String × Nat) := []
  tdFail : List (String × Nat) := []
  nodes : Nat := 0
  unfolded : List (String × Nat) := []
  names : List Name := []

def bump (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  if l.any (·.1 == k) then l.map fun (a, n) => if a == k then (a, n + 1) else (a, n) else l ++ [(k, 1)]

abbrev M := StateM Stuck

/-- a short description of a stuck term: heads of nested projections, the head constant with its kind -/
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
        match whStep env x with
        | some x' => do modify fun s => { s with unfolded := bump s.unfolded ("proj-arg:" ++ ctor.toString), names := ctor :: s.names }; recogProj env fuel S i x'
        | none => modify fun s => { s with heads := bump s.heads s!"proj {S}#{i} of {describe env x}" }
    | h =>
      match whStep env x with
      | some x' => recogProj env fuel S i x'
      | none => modify fun s => { s with heads := bump s.heads s!"proj {S}#{i} of {describe env x}" }

partial def recog (env : Environment) (fuel : Nat) (e : Lean.Expr) : M Unit := do
  modify fun s => { s with nodes := s.nodes + 1 }
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
      match headRedex env e with
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
      else
        match unfoldAt env e with
        | some e' => do modify fun s => { s with unfolded := bump s.unfolded c.toString, names := c :: s.names }; recog env fuel e'
        | none => modify fun s => { s with heads := bump s.heads (c.toString ++ (match env.find? c with
            | some (.inductInfo _) => " [inductive]" | some (.ctorInfo _) => " [constructor]" | some (.recInfo _) => " [recursor]"
            | some (.opaqueInfo _) => " [opaque]" | some (.thmInfo _) => " [theorem]" | some (.axiomInfo _) => " [axiom]"
            | some (.defnInfo _) => " [defn: level mismatch]" | some (.quotInfo _) => " [quot]" | none => " [missing]")) }
    | h => modify fun s => { s with heads := bump s.heads s!"<{h.ctorName}> application" }
end

run_cmd liftTermElabM do
  let env ← getEnv
  let some ci := env.find? `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte | throwError "root missing"
  unless ci.value! == Tools.ShippingFGCircuitS1kStmt.hftRootValue do throwError "the root's value in this environment differs from hftRootValue"
  if ci.value! == varBad then throwError "control: varBad equals the value"
  -- OPS against Lean's own operations, on the declarations of the root's body
  let mut checked : Nat := 0
  let body := Lean.Expr.instantiate1 ((((ci.value!.bindingBody!.bindingBody!.bindingBody!.bindingBody!).bindingBody!)) ) (.bvar 9)
  let mut seen : List Name := []
  for c in body.getUsedConstants do
    if let some (.defnInfo d) := env.find? c then
      if d.levelParams.isEmpty then
        seen := seen ++ [c]
        -- level instantiation on an empty list is the identity; beta/instantiate agree on loose-bvar arguments
        unless instLE [] [] d.value == d.value do throwError "{c}: instLE [] changes the value"
        let args := [Lean.Expr.bvar 0, .bvar 3, .bvar 5]
        let mine := betaApp d.value args
        let lean := (Lean.Expr.beta d.value args.toArray)
        unless mine == lean do throwError "{c}: betaApp differs from Expr.beta"
        checked := checked + 1
  -- a control: a wrong substitution is detected
  let c0 := ``Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte
  let some d0 := env.find? c0 | throwError "x"
  if betaApp d0.value! [.bvar 0] == Lean.Expr.beta d0.value! #[.bvar 1] then throwError "control: betaApp ignores its argument"
  -- the first reduction steps of the body, by the rules' own functions
  let mut cur := body
  let mut trace : List String := []
  for _ in [0:12] do
    match appFn cur with
    | .const c _ =>
      match unfoldAt env cur with
      | some e' => trace := trace ++ [s!"unf {c}"]; cur := e'
      | none => break
    | _ => break
  let steps := trace
  -- the recognizer on the whole value (5 lambdas, then the body)
  let st := (recog env 4000 ci.value!).run {} |>.2
  -- OPS on every definition the recognizer unfolded (with universe parameters instantiated at sample levels)
  let mut checkedU : Nat := 0
  let mut seenU : List Name := []
  for c in st.names do
    unless seenU.contains c do
      seenU := c :: seenU
      if let some (.defnInfo d) := env.find? c then
        let ls : List Level := d.levelParams.map fun _ => Level.succ Level.zero
        unless instLE d.levelParams ls d.value == d.value.instantiateLevelParams d.levelParams ls do throwError "{c}: instLE differs from instantiateLevelParams"
        let v := instLE d.levelParams ls d.value
        let args := [Lean.Expr.bvar 0, .bvar 3, .bvar 5]
        unless betaApp v args == (Lean.Expr.beta v args.toArray) do throwError "{c}: betaApp differs from Expr.beta"
        if let .lam _ _ b _ := v then
          for sarg in [Lean.Expr.bvar 2, .app (.bvar 1) (.bvar 0), .lam `x (.const ``Nat []) (.bvar 1) .default] do
            unless instE b sarg 0 == b.instantiate1 sarg do throwError "{c}: instE differs from instantiate1"
        checkedU := checkedU + 1
  if checkedU == 0 then throwError "OPS: nothing was checked"
  let top (l : List (String × Nat)) := (l.toArray.qsort (fun a b => a.2 > b.2)).toList
  logInfo m!"FGCIRCUIT11 OPS: betaApp agrees with Expr.beta on {checked} user definitions in the body of the root, and betaApp / instE / instLE agree with Expr.beta / instantiate1 / instantiateLevelParams on all {checkedU} definitions the recognizer unfolded (loose-bvar arguments, sample levels); a control rejects a wrong substitution"
  logInfo m!"FGCIRCUIT11 SNAPSHOT11 (one environment): the first steps of the root body by unfoldAt: {steps}"
  logInfo m!"FGCIRCUIT11 SNAPSHOT11 recognizer: {st.nodes} nodes visited; unfolded definitions (distinct {st.unfolded.length}): {(top st.unfolded).take 40}"
  logInfo m!"FGCIRCUIT11 MISSING (heads with no rule, stuck): {top st.heads}"
  logInfo m!"FGCIRCUIT11 MISSING (binder/let types outside TD): {top st.tdFail}"

end Tests.Gen5.FGCircuitPilotCheck11
