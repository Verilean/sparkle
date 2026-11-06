import Tools.ShippingFGCircuitS2gGates
set_option autoImplicit false
-- FG circuit pilot S2g check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §33.

/-! # FGCircuitPilotCheck27 (light: each part is a small `run_cmd`)

1. SIGNATURES-A: `KidGateFacts` / `HftKidsGateFacts` against independently written structures (constructor types, isDefEq); mutants: swapped callees, one callee twice, the instance-predicate point at the whole value instead of the peeled body, a dropped query, a dropped root fact.
2. SIGNATURES-B: `synth_hftPcieOutByte_finalOffLNKKG_Z` (14 hypotheses, `hkgfacts` last, no all-world reflection reachable from it).
3. QUOTES / ENV: the closed quotes equal the declarations; the named facts evaluated in two environment points (observation only); controls: swapped callees, another declaration whose gate fails, an instance-predicate-sensitive wrapper.
4. REMAINING, AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck27
open Lean Meta Elab Command Term
open Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS1kStmt
open Sparkle.Compiler.Elab

/-! ## 1. the facts, independently -/

/-- the five facts one callee's `EntryGates` asks of the environment, written again -/
structure ExpKGF (env : Environment) (X : Name) (T V Vi : Lean.Expr) : Prop where
  r : ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = T ∧ d.value = V
  a : userInliner env V = Vi
  b : userInliner env T = T
  c : instancePredicate env (peeled V) = false
  e : instancePredicate env (peeled Vi) = false

/-- mutant: the instance predicate asked at the whole value -/
structure MuWhole (env : Environment) (X : Name) (T V Vi : Lean.Expr) : Prop where
  r : ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = T ∧ d.value = V
  a : userInliner env V = Vi
  b : userInliner env T = T
  c : instancePredicate env V = false
  e : instancePredicate env Vi = false
/-- mutant: the inlined point dropped -/
structure MuNoInl (env : Environment) (X : Name) (T V Vi : Lean.Expr) : Prop where
  r : ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = T ∧ d.value = V
  a : userInliner env V = Vi
  b : userInliner env T = T
  c : instancePredicate env (peeled V) = false
/-- mutant: the root fact dropped -/
structure MuNoRoot (env : Environment) (X : Name) (T V Vi : Lean.Expr) : Prop where
  a : userInliner env V = Vi
  b : userInliner env T = T
  c : instancePredicate env (peeled V) = false
  e : instancePredicate env (peeled Vi) = false
/-- mutant: the inliner's type fact dropped -/
structure MuNoTy (env : Environment) (X : Name) (T V Vi : Lean.Expr) : Prop where
  r : ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = T ∧ d.value = V
  a : userInliner env V = Vi
  c : instancePredicate env (peeled V) = false
  e : instancePredicate env (peeled Vi) = false
/-- mutant: the value is not tied to the declaration -/
structure MuNoVal (env : Environment) (X : Name) (T V Vi : Lean.Expr) : Prop where
  r : ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ d.type = T
  a : userInliner env V = Vi
  b : userInliner env T = T
  c : instancePredicate env (peeled V) = false
  e : instancePredicate env (peeled Vi) = false

def ExpHK (e : Environment) : Prop :=
  ExpKGF e hftHttp httpType httpValue httpInlValue ∧ ExpKGF e hftTlp tlpType tlpValue tlpInlValue
def MuSwap (e : Environment) : Prop :=
  ExpKGF e hftHttp tlpType tlpValue tlpInlValue ∧ ExpKGF e hftTlp httpType httpValue httpInlValue
def MuSwapName (e : Environment) : Prop :=
  ExpKGF e hftTlp httpType httpValue httpInlValue ∧ ExpKGF e hftHttp tlpType tlpValue tlpInlValue
def MuHttpTwice (e : Environment) : Prop :=
  ExpKGF e hftHttp httpType httpValue httpInlValue ∧ ExpKGF e hftHttp httpType httpValue httpInlValue
def MuTlpTwice (e : Environment) : Prop :=
  ExpKGF e hftTlp tlpType tlpValue tlpInlValue ∧ ExpKGF e hftTlp tlpType tlpValue tlpInlValue
def MuHttpOnly (e : Environment) : Prop := ExpKGF e hftHttp httpType httpValue httpInlValue
def MuTlpOnly (e : Environment) : Prop := ExpKGF e hftTlp tlpType tlpValue tlpInlValue
def MuWholeBoth (e : Environment) : Prop :=
  MuWhole e hftHttp httpType httpValue httpInlValue ∧ MuWhole e hftTlp tlpType tlpValue tlpInlValue
def MuTrue (_ : Environment) : Prop := True

def normOnce (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if c == ``HftKidsGateFacts || c == ``Tools.ShippingFGCircuitRoots.RootInEnv || (`Tests.Gen5.FGCircuitPilotCheck27).isPrefixOf c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:5] do
    e ← normOnce e
  -- `ExpKGF` was proved to have the constructor type of `KidGateFacts` (SIGNATURES-A, first check); here it is read as that structure
  return e.replace fun x => if x.isConstOf `Tests.Gen5.FGCircuitPilotCheck27.ExpKGF then some (mkConst `Tools.ShippingFGCircuitS2gGates.KidGateFacts) else none
def sameTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  unless ← withDefault (isDefEq a e) do throwError "{what}: type is NOT the expected statement"
def diffTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  if a == e then throwError "{what}: the MUTANT is the same expression"
  if ← withReducible (isDefEq a e) then throwError "{what}: the MUTANT was accepted"
def tyOf (n : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo n
  unless ci.levelParams.isEmpty do throwError "{n}: level parameters"
  pure ci.type
/-- the constructor's type of a structure (the five facts as a telescope) -/
def ctorTy (n : Name) : MetaM Lean.Expr := do
  let .inductInfo i := (← getConstInfo n) | throwError "{n}: not an inductive"
  let [c] := i.ctors | throwError "{n}: not one constructor"
  -- the structure name in the conclusion is replaced by KidGateFacts, only the five fields are compared
  pure ((← tyOf c).replace fun e => if e.isConstOf n then some (mkConst `Tools.ShippingFGCircuitS2gGates.KidGateFacts) else none)

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS2gGates
  let Q := `Tests.Gen5.FGCircuitPilotCheck27
  let kc ← ctorTy (X ++ `KidGateFacts)
  sameTy "KidGateFacts" kc (← ctorTy (Q ++ `ExpKGF))
  let mut nm : Nat := 0
  for mu in ["MuWhole", "MuNoInl", "MuNoRoot", "MuNoTy", "MuNoVal"] do
    diffTy s!"KidGateFacts vs {mu}" kc (← ctorTy (Q ++ Name.mkSimple mu)); nm := nm + 1
  let hk := C (X ++ `HftKidsGateFacts)
  sameTy "HftKidsGateFacts" hk (C (Q ++ `ExpHK))
  for mu in ["MuSwap", "MuSwapName", "MuHttpTwice", "MuTlpTwice", "MuHttpOnly", "MuTlpOnly", "MuWholeBoth", "MuTrue"] do
    diffTy s!"HftKidsGateFacts vs {mu}" hk (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT27 SIGNATURES-A: KidGateFacts (5 fields: root, ui_val, ui_ty, ip at peeled V, ip at peeled Vi) and HftKidsGateFacts (http ∧ tlp at their own closed quotes) match the independently written ExpKGF / ExpHK; {nm} mutants rejected (point at the whole value, inlined point dropped, root dropped, inliner type fact dropped, value not tied to the declaration; callees swapped by quote, swapped by name, one callee twice, one callee only, whole-value points, True)"

/-! ## 2. the final statement -/

partial def binderNames : Lean.Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- the constants reachable from the value of `n` through definitions of this development (bounded) -/
partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        if (`Tools).isPrefixOf n || (`Sparkle).isPrefixOf n then reach env (d.value.getUsedConstants.toList ++ d.type.getUsedConstants.toList ++ rest) seen
        else reach env rest seen
      | some (.inductInfo i) =>
        if (`Tools).isPrefixOf n then reach env (i.ctors ++ rest) seen else reach env rest seen
      | some (.ctorInfo c) => reach env (c.type.getUsedConstants.toList ++ rest) seen
      | _ => reach env rest seen

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2gGates
  let mut nm : Nat := 0
  let t2 ← tyOf (X ++ `synth_hftPcieOutByte_finalOffLNKKG_Z)
  let some ty2 ← unfoldDefinition? t2 | throwError "the instance's type is not a definition"
  let hs ← forallTelescope ty2 fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, ← instantiateMVars d.type)]
    return hs
  let expected := ["hlink", "L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "htop", "hkenv", "hkgfacts"]
  unless hs.map (·.1) == expected do throwError "hypotheses are {hs.map (·.1)}, expected {expected}"
  for gone in ["hkids", "hkgates", "hclL", "hcl", "hgate", "hnoraw", "hdRun", "hsrc", "hhead"] do
    if (hs.map (·.1)).contains gone then throwError "{gone} is a hypothesis"
  let some (_, hkf) := hs.find? (·.1 == "hkgfacts") | throwError "hkgfacts missing"
  unless hkf.getUsedConstants.contains ``HftKidsGateFacts do throwError "hkgfacts is not HftKidsGateFacts"
  let some (_, hke) := hs.find? (·.1 == "hkenv") | throwError "hkenv missing"
  unless hke.getUsedConstants.contains ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv do throwError "hkenv changed"
  -- the readers are still hypotheses (the supply of the gates does not replace them)
  for n in ["hreadH", "hreadT"] do
    let some (_, h) := hs.find? (·.1 == n) | throwError "{n} missing"
    unless h.getUsedConstants.contains ``Tools.ShippingFGCircuitCover.RootReader do throwError "{n} is not a RootReader"
  nm := nm + 6
  let env ← getEnv
  let r := reach env [``HftKidsGateFacts] {}
  for bad in [``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine, ``Tools.ShippingMachineEntry.MachineCloses,
      ``Tools.ShippingGen2.Start, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingGen5Env.ReadsAt, ``Tools.ShippingFGCircuitS1iEnv.CheckedStart] do
    if r.contains bad then throwError "{bad} is reachable from hkgfacts (an all-world / run statement)"
  for need in [``Tools.ShippingFGCircuitRoots.RootInEnv, ``instancePredicate, ``userInliner] do
    unless r.contains need do throwError "hkgfacts does not reach {need}"
  nm := nm + 10
  let t0 ← tyOf (`Tools.ShippingFGCircuitS2dKids ++ `synth_hftPcieOutByte_finalOffLNKK_Z)
  unless (← norm t0) != (← norm t2) do throwError "finalOffLNKKG_Z is the finalOffLNKK_Z statement"
  nm := nm + 1
  logInfo m!"FGCIRCUIT27 SIGNATURES-B: synth_hftPcieOutByte_finalOffLNKKG_Z: {nm} structural checks; hkgates is replaced by hkgfacts (last of {hs.length}), hkenv/hreadH/hreadT unchanged; no MachineDefines / HftKidsDefine / MachineCloses / Start / ReadsAt / CheckedStart reachable from hkgfacts (reach set {r.size})"
  logInfo m!"FGCIRCUIT27 HYPS: HftFinalStmtOffLNKKG Ob CV = {expected}: {hs.length} explicit hypotheses"

/-! ## 3. the quotes and the environment points -/

unsafe def evalQuoteU (n : Name) : MetaM Lean.Expr := evalExpr Lean.Expr (mkConst ``Lean.Expr) (mkConst n)
@[implemented_by evalQuoteU] opaque evalQuote (n : Name) : MetaM Lean.Expr

/-- a declaration whose gate PASSES (a certified combinational body): `GatesOn` fails for it -/
def gateFail (x : Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec 8)) :
    Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec 8) := x + x
/-- a wrapper that is a designated call: its mixed gate depends on the instance predicate -/
def kidWrap (c : Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec 6)) :
    Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec 8) := Sparkle.IP.Net.HTTP.httpGetByte c

/-- the five facts of `KidGateFacts`, evaluated (an OBSERVATION in `MetaM`, not a kernel supply) -/
def evalFacts (env : Environment) (X : Name) (T V Vi : Lean.Expr) : List (String × Bool) :=
  let root := match env.find? X with
    | some (.defnInfo d) => d.levelParams.isEmpty && d.type == T && d.value == V
    | _ => false
  [("root", root), ("ui_val", userInliner env V == Vi), ("ui_ty", userInliner env T == T),
   ("ip_val", instancePredicate env (peeled V) == false), ("ip_inl", instancePredicate env (peeled Vi) == false)]

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2gGates
  let mut nm : Nat := 0
  let mut qs : Array Lean.Expr := #[]
  for (n, c) in [(`httpType, hftHttp), (`httpValue, hftHttp), (`tlpType, hftTlp), (`tlpValue, hftTlp)] do
    let q ← evalQuote (X ++ n)
    qs := qs.push q
    let some (.defnInfo d) := (← getEnv).find? c | throwError "{c} missing"
    let want := if n.toString.endsWith "Type" then d.type else d.value
    unless q == want && Lean.Expr.equal q want do throwError "{X ++ n} is not the declaration's {n}"
    nm := nm + 1
  -- the two callees are distinct closed terms
  unless qs[1]! != qs[3]! && qs[0]! != qs[2]! do throwError "http and tlp quotes coincide"
  nm := nm + 1
  let env ← getEnv
  let allOk (env : Environment) : MetaM (List (String × Bool) × List (String × Bool)) := do
    let h := evalFacts env hftHttp (← evalQuote (X ++ `httpType)) (← evalQuote (X ++ `httpValue)) (← evalQuote (X ++ `httpInlValue))
    let t := evalFacts env hftTlp (← evalQuote (X ++ `tlpType)) (← evalQuote (X ++ `tlpValue)) (← evalQuote (X ++ `tlpInlValue))
    pure (h, t)
  -- environment point 1: this build's environment
  let (h1, t1) ← allOk env
  for (k, b) in h1 ++ t1 do unless b do throwError "env point 1: fact {k} fails"
  -- environment point 2: after adding an unrelated declaration
  addAndCompile (.defnDecl { name := `Tests.Gen5.FGCircuitPilotCheck27.unrelatedMark, levelParams := [], type := mkConst ``Nat, value := mkNatLit 7, hints := .abbrev, safety := .safe })
  let env2 ← getEnv
  let (h2, t2) ← allOk env2
  for (k, b) in h2 ++ t2 do unless b do throwError "env point 2: fact {k} fails"
  nm := nm + 20
  logInfo m!"FGCIRCUIT27 QUOTES: the four closed quotes (type and value of httpGetByte, tlpCplByte) equal the declarations' own type and value (evaluated, Expr.equal), http ≠ tlp; the {h1.length + t1.length} named facts hold at environment point 1 (this build) and point 2 (after adding an unrelated declaration): {nm} checks (an OBSERVATION; the facts stay named hypotheses)"
  -- controls: swapped callees
  let ht ← evalQuote (X ++ `httpType)
  let hv ← evalQuote (X ++ `httpValue)
  let hiv ← evalQuote (X ++ `httpInlValue)
  let tv ← evalQuote (X ++ `tlpValue)
  let tiv ← evalQuote (X ++ `tlpInlValue)
  let tt ← evalQuote (X ++ `tlpType)
  let sw1 := evalFacts env hftHttp tt tv tiv
  let sw2 := evalFacts env hftTlp ht hv hiv
  unless sw1.any (!·.2) && sw2.any (!·.2) do throwError "swapped callees satisfy the facts"
  unless (sw1.find? (·.1 == "root")).map (·.2) == some false do throwError "swapped root fact holds"
  -- a callee whose gate fails: `gateFail` is certified, so `GatesOn` does not hold for it
  let some (.defnInfo g) := env.find? `Tests.Gen5.FGCircuitPilotCheck27.gateFail | throwError "gateFail missing"
  let certG := (certifiedShape? false [] (.defnInfo g)).isSome
  unless certG do throwError "CONTROL: gateFail is not certified (the gate would pass)"
  let some (.defnInfo k) := env.find? `Tests.Gen5.FGCircuitPilotCheck27.kidWrap | throwError "kidWrap missing"
  let mixF := (mixedCertifiedShape? false [] (.defnInfo k) (fun _ => false)).isSome
  let mixI := (mixedCertifiedShape? false [] (.defnInfo k) (instancePredicate env)).isSome
  unless mixI && !mixF do throwError "CONTROL: kidWrap is not instance-predicate sensitive ({mixI}, {mixF})"
  -- the real callees: their gates hold under the real instance predicate
  let some (.defnInfo hd) := env.find? hftHttp | throwError "http missing"
  let some (.defnInfo td) := env.find? hftTlp | throwError "tlp missing"
  let ent1 := entryConst true false [] (.defnInfo hd) (instancePredicate env) (userInliner env) (structEnv env)
  let ent2 := entryConst true false [] (.defnInfo td) (instancePredicate env) (userInliner env) (structEnv env)
  for (ci, w) in [(ent1, "http"), (ent2, "tlp")] do
    unless (certifiedShape? false [] ci).isNone && (mixedCertifiedShape? false [] ci (instancePredicate env)).isNone do throwError "{w}: the entry constant's gates do not pass"
  -- the entry constant of the gate-failing declaration is refused by the real gate
  let entG := entryConst true false [] (.defnInfo g) (instancePredicate env) (userInliner env) (structEnv env)
  unless (certifiedShape? false [] entG).isSome do throwError "CONTROL: gateFail's entry constant passes the gate"
  logInfo m!"FGCIRCUIT27 CONTROLS: swapped callees violate the facts (root fact false both ways); a callee whose gate fails (gateFail: certifiedShape? isSome, so EntryGates would be false) is detected; the instance predicate is query-sensitive (kidWrap: mixed gate some with the real predicate, none with the constant-false one); the real entry constants of both callees pass both gates at point 1: 7 controls"

/-! ## 4. REMAINING, AXIOMS -/

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2gGates
  let a ← getConstInfo (X ++ `KidGateFacts)
  let _ := a
  logInfo m!"FGCIRCUIT27 REMAINING hkgfacts : HftKidsGateFacts (envAt cref w) [FG D.T-4g, finite]: per callee, ∃ d, RootInEnv e X T V d; userInliner e V = Vi; userInliner e T = T; instancePredicate e (peeled V) = false; instancePredicate e (peeled Vi) = false (Vi = the build's inlined value, a SNAPSHOT named by ui_val). 10 named environment facts at named points, no all-world law. REMAINING also (unchanged by S2g): hkenv (D.T-4k), HftRootLink, hcd(Ob), htop, hreadH/T, hchk, CellPrem, Laws/Start/hr"

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2gGates
  let names : List Name := [X ++ `http_gates_V, X ++ `http_gates_Vi, X ++ `tlp_gates_V, X ++ `tlp_gates_Vi, X ++ `entryGates_of_two,
    X ++ `httpGate_of_facts, X ++ `tlpGate_of_facts, X ++ `hftKidsGates_of_facts,
    X ++ `synth_hftPcieOutByte_finalOffLNKKG, X ++ `synth_hftPcieOutByte_finalOffLNKKG_Z, X ++ `synth_hftPcieOutByte_finalOffLNKKG_Y, X ++ `synth_hftPcieOutByte_finalOffLNKKG_X]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT27 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck27
