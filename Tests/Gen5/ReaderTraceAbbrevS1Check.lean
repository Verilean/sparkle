import Tools.ShippingGen5ReaderTraceAbbrevS1
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT: Check for Tools/ShippingGen5ReaderTraceAbbrevS1.lean (written against scripts/gen5/RT_ABBREV_S1_FREEZE.md rev2).

/-! # RT abbrev S1 checks (Tools/Assume/AbbrevExtern.lean, Tools/ShippingGen5ReaderTraceAbbrevS1.lean)

TYPE: the 9 theorems are compared by `checkExpected` against `Exp…` statements written here (own spelling), independently of the freeze `#check` text;
`ReplaceAgrees` / `HeadBetaAgrees0` (Prop definitions) are compared against their expected statements the same way.
MUTANT: well-typed single changes of the `Exp…` statements, rejected by signature / defeq (NOT semantic counterexamples).
AXIOMS: standard only. CLOSURE: no sorryAx / ofReduceBool / trustCompiler in the closure. DEPENDENCY table: which theorem takes which assumption.
RUNTIME: finite comparisons (NOT a proof, and a small sample is no evidence): `headBeta` vs `headBetaSpec`, `replace` vs `replaceNoCache`, on hand-written
terms and on subterms / values / types of the constants of the imported environment (modules `Sparkle.*` and `Tools.*`).
Not claimed: that `ReplaceAgrees` / `HeadBetaAgrees0` hold (the runtime comparison found no mismatch only on the counted inputs). -/

namespace Tests.Gen5.ReaderTraceAbbrevS1Check
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tests.Gen3.ExpectedType Tools.Assume.AbbrevExtern Tools.ShippingGen5ReaderTraceAbbrevS1

section Expected

def ExpReplace : Prop := ∀ (f : Lean.Expr → Option Lean.Expr) (e : Lean.Expr), e.replace f = e.replaceNoCache f
def ExpHeadBeta : Prop := ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true → e.headBeta = headBetaSpec e
def ExpZero : Prop := ∀ (h : Tools.Assume.AbbrevExtern.ReplaceAgrees), Tools.Assume.N3Extern.ZeroLitAgrees0
def ExpInstNoPh : Prop := ∀ (subst : Array Lean.Expr), (∀ a ∈ subst, NoPh a = true ∧ BvarLt 0 a = true) →
  ∀ (b e : Nat) (x : Lean.Expr) (off : Nat), NoPh x = true → NoPh (instSpec subst b e x off) = true
def ExpInstBvar : Prop := ∀ (subst : Array Lean.Expr), (∀ a ∈ subst, NoPh a = true ∧ BvarLt 0 a = true) →
  ∀ (b e : Nat) (x : Lean.Expr) (off m : Nat),
    BvarLt (m + (e - b) + off) x = true → BvarLt (m + off) (instSpec subst b e x off) = true
def ExpBetaGo : Prop := ∀ (revArgs : Array Lean.Expr), (∀ a ∈ revArgs, NoPh a = true ∧ BvarLt 0 a = true) →
  ∀ (sz : Nat), sz = revArgs.size →
    ∀ (x : Lean.Expr) (i : Nat), i < sz → NoPh x = true → BvarLt i x = true →
      NoPh (betaGo revArgs sz x i) = true ∧ BvarLt 0 (betaGo revArgs sz x i) = true
def ExpHeadBetaSpecGood : Prop := ∀ (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
  NoPh (headBetaSpec e) = true ∧ BvarLt 0 (headBetaSpec e) = true
def ExpHeadBetaGood : Prop := HeadBetaAgrees0 → ∀ (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
  NoPh e.headBeta = true ∧ BvarLt 0 e.headBeta = true
def ExpRnc : Prop := ∀ (f : Lean.Expr → Option Lean.Expr),
  (∀ (x v : Lean.Expr), f x = some v → NoPh v = true ∧ BvarLt 0 v = true) →
  ∀ (e : Lean.Expr) (L : Nat), NoPh e = true → BvarLt L e = true →
    NoPh (e.replaceNoCache f) = true ∧ BvarLt L (e.replaceNoCache f) = true
def ExpAbbrevFn : Prop := ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env →
  ∀ (x v : Lean.Expr), Tools.ShippingInlCand.abbrevFn env x = some v → NoPh v = true ∧ BvarLt 0 v = true
def ExpInlAbbrevs : Prop := ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env →
  Tools.Assume.AbbrevExtern.ReplaceAgrees → HeadBetaAgrees0 →
  ∀ (n : Nat) (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    NoPh (Sparkle.Compiler.Elab.inlAbbrevs env n e) = true ∧ BvarLt 0 (Sparkle.Compiler.Elab.inlAbbrevs env n e) = true

-- mutants (single changes of the Exp… statements)
def MutReplace : Prop := ∀ (f : Lean.Expr → Option Lean.Expr) (e : Lean.Expr), e.replace f = e.replaceNoCache (fun _ => none)
def MutHeadBeta : Prop := ∀ e : Lean.Expr, BvarLt 0 e = true → e.headBeta = headBetaSpec e
def MutZero : Prop := Tools.Assume.N3Extern.ZeroLitAgrees0 → Tools.Assume.AbbrevExtern.ReplaceAgrees
def MutInstBvar : Prop := ∀ (subst : Array Lean.Expr), (∀ a ∈ subst, NoPh a = true ∧ BvarLt 0 a = true) →
  ∀ (b e : Nat) (x : Lean.Expr) (off m : Nat),
    BvarLt (m + off) x = true → BvarLt (m + off) (instSpec subst b e x off) = true
def MutBetaGo : Prop := ∀ (revArgs : Array Lean.Expr), (∀ a ∈ revArgs, NoPh a = true ∧ BvarLt 0 a = true) →
  ∀ (sz : Nat), sz = revArgs.size →
    ∀ (x : Lean.Expr) (i : Nat), i ≤ sz → NoPh x = true → BvarLt i x = true →
      NoPh (betaGo revArgs sz x i) = true ∧ BvarLt 0 (betaGo revArgs sz x i) = true
def MutHeadBetaGoodNoHyp : Prop := ∀ (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
  NoPh e.headBeta = true ∧ BvarLt 0 e.headBeta = true
def MutRnc : Prop := ∀ (f : Lean.Expr → Option Lean.Expr),
  (∀ (x v : Lean.Expr), f x = some v → NoPh v = true ∧ BvarLt 1 v = true) →
  ∀ (e : Lean.Expr) (L : Nat), NoPh e = true → BvarLt L e = true →
    NoPh (e.replaceNoCache f) = true ∧ BvarLt L (e.replaceNoCache f) = true
def MutInlAbbrevs : Prop := ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env →
  HeadBetaAgrees0 →
  ∀ (n : Nat) (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    NoPh (Sparkle.Compiler.Elab.inlAbbrevs env n e) = true ∧ BvarLt 0 (Sparkle.Compiler.Elab.inlAbbrevs env n e) = true

end Expected

-- positive controls (evaluation of the models; #guard, no native_decide)
example : BvarLt 0 (.bvar 0) = false := by decide
example : BvarLt (0 + 1) (.bvar 0) = true := by decide
/-! ## Runtime comparison (NOT a proof) -/

def sameE (a b : Lean.Expr) : Bool := Lean.Expr.equal a b

def lamId : Lean.Expr := .lam `x (.const `T []) (.bvar 0) .default
def lamK : Lean.Expr := .lam `x (.const `T []) (.lam `y (.const `U []) (.bvar 1) .default) .default
def cA : Lean.Expr := .const `a []
def cB : Lean.Expr := .const `b []
/-- hand-written terms: partial / exact / over application, mdata between lambdas, letE and mdata heads, nested redexes, binders under the argument -/
def handTerms : List Lean.Expr :=
  [ .app lamId cA, .app (.app lamK cA) cB, .app (.app (.app lamK cA) cB) (.const `c []), .app lamK cA,
    .app (.mdata {} lamId) cA, .app (.lam `x (.const `T []) (.mdata {} (.lam `y (.const `U []) (.bvar 1) .default)) .default) cA,
    .app (.app (.lam `x (.const `T []) (.lam `y (.const `U []) (.app (.bvar 1) (.bvar 0)) .default) .default) lamId) cB,
    .app (.letE `z (.const `T []) cA (.lam `x (.const `T []) (.bvar 1) .default) false) cB,
    .app (.lam `x (.const `T []) (.lam `y (.const `U []) (.lam `z (.const `V []) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) .default) .default) .default)
      (.lam `w (.const `T []) (.bvar 0) .default),
    .app lamId (.lam `w (.const `T []) (.app (.bvar 0) (.proj `P 0 (.bvar 0))) .default),
    .app (.lam `x (.const `T []) (.forallE `y (.bvar 0) (.app (.bvar 1) (.bvar 0)) .default) .default) cA,
    .mdata {} (.app lamId cA), cA, .lam `x (.const `T []) (.bvar 0) .default ]

#guard sameE (headBetaSpec (.app lamId cA)) cA
#guard sameE (headBetaSpec cA) cA
#guard sameE (betaGo #[cA] 1 (.bvar 0) 0) (.app (.bvar 0) cA)
#guard sameE (betaGo #[cA] 1 lamId 0) cA

/-- all subterms (with their own shape) -/
partial def subterms (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let acc := acc.push e
  match e with
  | .app f a => subterms a (subterms f acc)
  | .lam _ t b _ => subterms b (subterms t acc)
  | .forallE _ t b _ => subterms b (subterms t acc)
  | .letE _ t v b _ => subterms b (subterms v (subterms t acc))
  | .mdata _ b => subterms b acc
  | .proj _ _ b => subterms b acc
  | _ => acc

/-- the replacement functions compared: the production `abbrevFn`, the `zeroLit` function, and three generic ones -/
def fnNatInt : Lean.Expr → Option Lean.Expr
  | .const ``Nat [] => some (.const ``Int [])
  | _ => none
def fnNotElim : Lean.Expr → Option Lean.Expr
  | .app (.const ``Not []) x => some x
  | _ => none
def fnAppConst : Lean.Expr → Option Lean.Expr
  | .app (.const n us) x => some (.app (.const n us) (.app (.const ``id [.zero]) x))
  | _ => none

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- corpus: constants of the `Sparkle` / `Tools` modules in the imported environment (sorted, capped)
  let names := (env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if ((`Sparkle).isPrefixOf n || (`Tools).isPrefixOf n) && !n.isInternal && (ci.isDefinition || ci.isTheorem) then acc.push n else acc)
    |>.qsort (fun a b => a.toString < b.toString)
  let cap := 6000
  let names := names.extract 0 cap
  let mut exprs : Array Lean.Expr := #[]
  for n in names do
    match env.find? n with
    | some ci =>
      exprs := exprs.push ci.type
      match ci with
      | .defnInfo v => exprs := exprs.push v.value
      | .thmInfo v => exprs := exprs.push v.value
      | _ => pure ()
    | none => pure ()
  -- (1) headBeta vs headBetaSpec on every beta-redex-shaped subterm in the domain
  let mut hbHand : Nat := 0
  let mut hbHandBad : Nat := 0
  for e in handTerms do
    if NoPh e && BvarLt 0 e then
      hbHand := hbHand + 1
      unless sameE e.headBeta (headBetaSpec e) do hbHandBad := hbHandBad + 1
  let mut hbCorpus : Nat := 0
  let mut hbCorpusReal : Nat := 0
  let mut hbCorpusBad : Nat := 0
  let mut hbOut : Nat := 0
  let mut hbOutBad : Nat := 0
  for e0 in exprs do
    for e in subterms e0 #[] do
      if e.isApp && e.getAppFn.isHeadBetaTargetFn false then
        if NoPh e && BvarLt 0 e then
          hbCorpus := hbCorpus + 1
          let r := e.headBeta
          unless sameE r e do hbCorpusReal := hbCorpusReal + 1
          unless sameE r (headBetaSpec e) do hbCorpusBad := hbCorpusBad + 1
        else
          hbOut := hbOut + 1
          unless sameE e.headBeta (headBetaSpec e) do hbOutBad := hbOutBad + 1
  logInfo m!"RT ABBREVS1CHECK RUNTIME headBeta: hand {hbHand} terms ({hbHandBad} mismatch); corpus {names.size} constants / {exprs.size} types+values: {hbCorpus} in-domain redex subterms ({hbCorpusReal} actually reduce, {hbCorpusBad} mismatch); outside the domain (loose bvars, informational) {hbOut} ({hbOutBad} mismatch)"
  if hbHandBad + hbCorpusBad > 0 then throwError "RT ABBREVS1CHECK RUNTIME MISMATCH in headBeta vs headBetaSpec"
  -- (2) replace vs replaceNoCache
  let fns : List (String × (Lean.Expr → Option Lean.Expr)) :=
    [("abbrevFn env", Tools.ShippingInlCand.abbrevFn env), ("zeroLitF", Tools.Assume.N3Extern.zeroLitF), ("Nat->Int", fnNatInt),
     ("Not-elim", fnNotElim), ("app-wrap", fnAppConst)]
  let mut total : Nat := 0
  let mut changed : Nat := 0
  let mut bad : Nat := 0
  for (nm, f) in fns do
    let mut tot : Nat := 0
    let mut chg : Nat := 0
    let mut bd : Nat := 0
    for e in handTerms ++ exprs.toList do
      tot := tot + 1
      let a := e.replace f
      let b := e.replaceNoCache f
      unless sameE a b do bd := bd + 1
      unless sameE a e do chg := chg + 1
    logInfo m!"RT ABBREVS1CHECK RUNTIME replace [{nm}]: {tot} terms, {chg} changed by the replacement, {bd} mismatch"
    total := total + tot
    changed := changed + chg
    bad := bad + bd
  logInfo m!"RT ABBREVS1CHECK RUNTIME replace total: {total} comparisons ({changed} changed), {bad} mismatch"
  if bad > 0 then throwError "RT ABBREVS1CHECK RUNTIME MISMATCH in replace vs replaceNoCache"
  logInfo m!"RT ABBREVS1CHECK RUNTIME COUNTS: headBeta {hbHand + hbCorpus} in-domain comparisons / replace {total} comparisons / 0 mismatch (a finite comparison, not a proof)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``ReplaceAgrees ``ExpReplace
  checkExpected ``HeadBetaAgrees0 ``ExpHeadBeta
  checkExpected ``zeroLitAgrees0_of_replace ``ExpZero
  checkExpected ``instSpec_noPh ``ExpInstNoPh
  checkExpected ``instSpec_bvarLt ``ExpInstBvar
  checkExpected ``betaGo_good ``ExpBetaGo
  checkExpected ``headBetaSpec_good ``ExpHeadBetaSpecGood
  checkExpected ``headBeta_good ``ExpHeadBetaGood
  checkExpected ``rnc_ph ``ExpRnc
  checkExpected ``abbrevFn_ph ``ExpAbbrevFn
  checkExpected ``inlAbbrevs_ph ``ExpInlAbbrevs
  logInfo m!"RT ABBREVS1CHECK TYPE 11 declarations compared (9 theorems, 2 assumption Props)"
  checkMutant ``ReplaceAgrees ``MutReplace
  checkMutant ``HeadBetaAgrees0 ``MutHeadBeta
  checkMutant ``zeroLitAgrees0_of_replace ``MutZero
  checkMutant ``instSpec_bvarLt ``MutInstBvar
  checkMutant ``betaGo_good ``MutBetaGo
  checkMutant ``headBeta_good ``MutHeadBetaGoodNoHyp
  checkMutant ``rnc_ph ``MutRnc
  checkMutant ``inlAbbrevs_ph ``MutInlAbbrevs
  logInfo m!"RT ABBREVS1CHECK MUTANT 8 statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``zeroLitAgrees0_of_replace, ``instSpec_noPh, ``instSpec_bvarLt, ``betaGo_good, ``headBetaSpec_good,
  ``headBeta_good, ``rnc_ph, ``abbrevFn_ph, ``inlAbbrevs_ph]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"RT ABBREVS1CHECK AXIOMS {newThms.length} declarations checked (standard axioms only)"

/-! ## Dependency table: which theorem takes `ReplaceAgrees` / `HeadBetaAgrees0` / `DeclValuePh` as a hypothesis (in its type) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let expect : List (Name × Bool × Bool × Bool) :=
    [(``zeroLitAgrees0_of_replace, true, false, false), (``instSpec_noPh, false, false, false), (``instSpec_bvarLt, false, false, false),
     (``betaGo_good, false, false, false), (``headBetaSpec_good, false, false, false), (``headBeta_good, false, true, false),
     (``rnc_ph, false, false, false), (``abbrevFn_ph, false, false, true), (``inlAbbrevs_ph, true, true, true)]
  for (n, r, h, d) in expect do
    let some ci := env.find? n | throwError "missing {n}"
    let cs := ci.type.getUsedConstants
    let r' := cs.contains ``Tools.Assume.AbbrevExtern.ReplaceAgrees
    let h' := cs.contains ``Tools.Assume.AbbrevExtern.HeadBetaAgrees0
    let d' := cs.contains ``Tools.Assume.EnvDeclValue.DeclValuePh
    unless r == r' && h == h' && d == d' do throwError "RT ABBREVS1CHECK DEPENDENCY MISMATCH for {n}: {r'} {h'} {d'}"
    logInfo m!"RT ABBREVS1CHECK DEP {n}: ReplaceAgrees={r'} HeadBetaAgrees0={h'} DeclValuePh={d'}"
  logInfo m!"RT ABBREVS1CHECK DEPENDENCY table OK: ReplaceAgrees taken by zeroLitAgrees0_of_replace, inlAbbrevs_ph; HeadBetaAgrees0 by headBeta_good, inlAbbrevs_ph; DeclValuePh by abbrevFn_ph, inlAbbrevs_ph"

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"RT ABBREVS1CHECK COUNTS: TYPE 11 / MUTANT 8 / AXIOMS 9 / DEPENDENCY 9 / POSITIVE 6 (2 decide + 4 guard) / RUNTIME see lines above"

def closureRoots : List Name := newThms

/-! ## Closure audit -/

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (NameSet × NameSet × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (closureOf env)).run ({}, {})
  pure (seen, unk, forbiddenConsts.filter seen.contains)

-- Negative controls (built in memory, no `sorry` token in this file): each must be detected; clean controls must not be.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    let ok := mkConst ``True.intro
    addDecl (.thmDecl { name := `ReaderTraceAbbrevS1Check.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceAbbrevS1Check.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceAbbrevS1Check.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceAbbrevS1Check.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceAbbrevS1Check.direct, `ReaderTraceAbbrevS1Check.viaHelper, `ReaderTraceAbbrevS1Check.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 ABBREVS1CHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 ABBREVS1CHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceAbbrevS1Check.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 ABBREVS1CHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 ABBREVS1CHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceAbbrevS1Check.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceAbbrevS1Check.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceAbbrevS1Check.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceAbbrevS1Check.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceAbbrevS1Check.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceAbbrevS1Check.Missing.nowhere do throwError "GEN5 ABBREVS1CHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceAbbrevS1Check.viaHelperU, `ReaderTraceAbbrevS1Check.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceAbbrevS1Check.Missing.nowhere do throwError "GEN5 ABBREVS1CHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceAbbrevS1Check.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 ABBREVS1CHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 ABBREVS1CHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 9 do throwError "GEN5 ABBREVS1CHECK CLOSURE FAILED: expected 9 declarations"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 ABBREVS1CHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 ABBREVS1CHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 ABBREVS1CHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 ABBREVS1CHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 ABBREVS1CHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (9 declarations); all 9 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceAbbrevS1Check
