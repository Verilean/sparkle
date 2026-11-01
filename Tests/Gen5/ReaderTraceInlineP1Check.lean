import Tools.ShippingGen5ReaderTraceInlineP1
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT (header to be replaced by a comment-only commit with the built SHA). Clean build is the coder's.

/-! # RT inline P1 checks (Tools/ShippingGen5ReaderTraceInlineP1.lean)

TYPE: the 15 theorems are compared by `checkExpected` against `Exp…` statements written here (own spelling and binder names), independently of the freeze `#check` text.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples).
Positive controls: kernel evaluation of the budgeted rewrites on concrete terms; one concrete witness (`inlDropBinder 1 (.bvar 0)`) that the side condition `c ≤ M` of `inlDropBinder_ph` cannot be dropped.
`userDefinition?_ph` / `inlineDefs_user_ph` are compared with `DeclValuePh` spelled out (accepted by isDefEq, reported by the checker as NOT syntactic) and `inlineDefs_user_ph` with a `let r := match …` conclusion (zeta).
The hypothesis `DeclValuePh` is not claimed true for accepted sources and is not registered in Tools/Assume. -/

namespace Tests.Gen5.ReaderTraceInlineP1Check
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tests.Gen3.ExpectedType Sparkle.Compiler.Elab

section Expected

def ExpFoldl : Prop := ∀ (L : Nat) (h : Lean.Expr) (args : List Lean.Expr)
  (hh : NoPh h = true ∧ BvarLt L h = true) (ha : ∀ x ∈ args, NoPh x = true ∧ BvarLt L x = true),
  NoPh (args.foldl Lean.Expr.app h) = true ∧ BvarLt L (args.foldl Lean.Expr.app h) = true
def ExpLift : Prop := ∀ (k c : Nat) (e : Lean.Expr) (b L : Nat) (e' : Lean.Expr) (b' : Nat),
  NoPh e = true → BvarLt L e = true → inlLift k c e b = some (e', b') → NoPh e' = true ∧ BvarLt (L + k) e' = true
def ExpSubst : Prop := ∀ (xs : Array Lean.Expr) (L : Nat) (hxs : ∀ x ∈ xs, NoPh x = true ∧ BvarLt L x = true)
  (d : Nat) (e : Lean.Expr) (b : Nat) (e' : Lean.Expr) (b' : Nat),
  NoPh e = true → BvarLt (d + xs.size + L) e = true → inlSubst xs d e b = some (e', b') →
  NoPh e' = true ∧ BvarLt (d + L) e' = true
def ExpBeta : Prop := ∀ (L : Nat) (v : Lean.Expr) (acc : Array Lean.Expr) (args : List Lean.Expr) (b : Nat) (e' : Lean.Expr) (b' : Nat),
  (∀ x ∈ acc, NoPh x = true ∧ BvarLt L x = true) → (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) →
  NoPh v = true → BvarLt (acc.size + L) v = true → inlBeta acc v args b = some (e', b') →
  NoPh e' = true ∧ BvarLt L e' = true
def ExpSpine : Prop := ∀ (L : Nat) (e : Lean.Expr) (acc : List Lean.Expr) (h : Lean.Expr) (args : List Lean.Expr),
  NoPh e = true → BvarLt L e = true → (∀ a ∈ acc, NoPh a = true ∧ BvarLt L a = true) →
  inlSpine e acc = (h, args) → (NoPh h = true ∧ BvarLt L h = true) ∧ ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true
def ExpMap : Prop := ∀ (f : Lean.Expr → Nat → Option (Lean.Expr × Nat)) (L : Nat)
  (hf : ∀ (a : Lean.Expr) (b : Nat) (a' : Lean.Expr) (b' : Nat),
    NoPh a = true → BvarLt L a = true → f a b = some (a', b') → NoPh a' = true ∧ BvarLt L a' = true)
  (xs : List Lean.Expr) (b : Nat) (xs' : List Lean.Expr) (b' : Nat),
  (∀ x ∈ xs, NoPh x = true ∧ BvarLt L x = true) → inlMap f xs b = some (xs', b') →
  ∀ x ∈ xs', NoPh x = true ∧ BvarLt L x = true
def ExpDrop : Prop := ∀ (e : Lean.Expr) (c M : Nat) (e' : Lean.Expr),
  c ≤ M → NoPh e = true → BvarLt (M + 1) e = true → inlDropBinder c e = some e' → NoPh e' = true ∧ BvarLt M e' = true
def ExpCanonLam : Prop := ∀ (e : Lean.Expr) (k L : Nat),
  NoPh e = true → BvarLt L e = true → NoPh (inlCanonLam k e) = true ∧ BvarLt L (inlCanonLam k e) = true
def ExpCanonPi : Prop := ∀ (e : Lean.Expr) (L : Nat),
  NoPh e = true → BvarLt L e = true → NoPh (inlCanonPi e) = true ∧ BvarLt L (inlCanonPi e) = true
def ExpMapOfFunctor : Prop := ∀ (L : Nat) (e e' : Lean.Expr),
  NoPh e = true → BvarLt L e = true → inlSignalMapOfFunctor e = some e' → NoPh e' = true ∧ BvarLt L e' = true
def ExpApplicative : Prop := ∀ (L : Nat) (n : Lean.Name) (ls : List Lean.Level) (args : List Lean.Expr) (e' : Lean.Expr),
  (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) → inlSignalApplicative n ls args = some e' →
  NoPh e' = true ∧ BvarLt L e' = true
def ExpHeadCtor : Prop := ∀ (defs : Lean.Name → Option Lean.Expr)
  (hd : ∀ (n : Lean.Name) (v : Lean.Expr), defs n = some v → NoPh v = true ∧ BvarLt 0 v = true)
  (ctor : Lean.Name) (fuel : Nat) (e : Lean.Expr) (b L : Nat) (as : List Lean.Expr) (b' : Nat),
  NoPh e = true → BvarLt L e = true → inlHeadCtor defs ctor fuel e b = some (as, b') →
  ∀ a ∈ as, NoPh a = true ∧ BvarLt L a = true
def ExpInlineDefs : Prop := ∀ (defs : Lean.Name → Option Lean.Expr) (projs : Lean.Name → Option (Lean.Name × Nat × Nat))
  (hd : ∀ (n : Lean.Name) (v : Lean.Expr), defs n = some v → NoPh v = true ∧ BvarLt 0 v = true)
  (fuel : Nat) (e : Lean.Expr) (b L : Nat) (e' : Lean.Expr) (b' : Nat),
  NoPh e = true → BvarLt L e = true → inlineDefs defs projs fuel e b = some (e', b') →
  NoPh e' = true ∧ BvarLt L e' = true
def ExpUserDef : Prop := ∀ (env : Lean.Environment)
  (hv : ∀ (n : Lean.Name) (d : Lean.DefinitionVal), env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true)
  (n : Lean.Name) (v : Lean.Expr) (h : userDefinition? env n = some v), NoPh v = true ∧ BvarLt 0 v = true
def ExpUserInl : Prop := ∀ (env : Lean.Environment)
  (hv : ∀ (n : Lean.Name) (d : Lean.DefinitionVal), env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true)
  (L : Nat) (e : Lean.Expr) (hn : NoPh e = true) (hb : BvarLt L e = true),
  let r := match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
    | some (e', _) => e'
    | none => e
  NoPh r = true ∧ BvarLt L r = true

-- mutants (single changes of the Exp… statements)
def MutLift : Prop := ∀ (k c : Nat) (e : Lean.Expr) (b L : Nat) (e' : Lean.Expr) (b' : Nat),
  NoPh e = true → BvarLt L e = true → inlLift k c e b = some (e', b') → NoPh e' = true ∧ BvarLt L e' = true
def MutSubst : Prop := ∀ (xs : Array Lean.Expr) (L : Nat) (hxs : ∀ x ∈ xs, NoPh x = true ∧ BvarLt L x = true)
  (d : Nat) (e : Lean.Expr) (b : Nat) (e' : Lean.Expr) (b' : Nat),
  NoPh e = true → BvarLt (d + xs.size + L) e = true → inlSubst xs d e b = some (e', b') →
  NoPh e' = true ∧ BvarLt L e' = true
def MutBeta : Prop := ∀ (L : Nat) (v : Lean.Expr) (acc : Array Lean.Expr) (args : List Lean.Expr) (b : Nat) (e' : Lean.Expr) (b' : Nat),
  (∀ x ∈ acc, NoPh x = true ∧ BvarLt L x = true) → (∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true) →
  NoPh v = true → BvarLt L v = true → inlBeta acc v args b = some (e', b') →
  NoPh e' = true ∧ BvarLt L e' = true
def MutDrop : Prop := ∀ (e : Lean.Expr) (c M : Nat) (e' : Lean.Expr),
  NoPh e = true → BvarLt (M + 1) e = true → inlDropBinder c e = some e' → NoPh e' = true ∧ BvarLt M e' = true
def MutHeadCtor : Prop := ∀ (defs : Lean.Name → Option Lean.Expr)
  (hd : ∀ (n : Lean.Name) (v : Lean.Expr), defs n = some v → NoPh v = true ∧ BvarLt 1 v = true)
  (ctor : Lean.Name) (fuel : Nat) (e : Lean.Expr) (b L : Nat) (as : List Lean.Expr) (b' : Nat),
  NoPh e = true → BvarLt L e = true → inlHeadCtor defs ctor fuel e b = some (as, b') →
  ∀ a ∈ as, NoPh a = true ∧ BvarLt L a = true
def MutInlineDefs : Prop := ∀ (defs : Lean.Name → Option Lean.Expr) (projs : Lean.Name → Option (Lean.Name × Nat × Nat))
  (hd : ∀ (n : Lean.Name) (v : Lean.Expr), defs n = some v → NoPh v = true ∧ BvarLt 0 v = true)
  (fuel : Nat) (e : Lean.Expr) (b L : Nat) (e' : Lean.Expr) (b' : Nat),
  NoPh e = true → BvarLt L e = true → inlineDefs defs projs fuel e b = some (e', b') →
  NoPh e' = true ∧ BvarLt 0 e' = true
def MutUserDef : Prop := ∀ (env : Lean.Environment)
  (hv : ∀ (n : Lean.Name) (d : Lean.DefinitionVal), env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true)
  (n : Lean.Name) (v : Lean.Expr) (h : userDefinition? env n = some v), NoPh v = true ∧ BvarLt 1 v = true
def MutUserInlNoHyp : Prop := ∀ (env : Lean.Environment)
  (L : Nat) (e : Lean.Expr) (hn : NoPh e = true) (hb : BvarLt L e = true),
  let r := match inlineDefs (userDefinition? env) (userProjection? env) inlineDepth e inlineBudget with
    | some (e', _) => e'
    | none => e
  NoPh r = true ∧ BvarLt L r = true

end Expected

-- positive controls (kernel evaluation)
example : (inlineDefs (fun _ => none) (fun _ => none) 4 (.app (.const `f []) (.bvar 0)) 10).map (·.1) =
    some (.app (.const `f []) (.bvar 0)) := rfl
example : (inlineDefs (fun n => if n == `g then some (.lam `x (.const `T []) (.bvar 0) .default) else none)
    (fun _ => none) 8 (.app (.const `g []) (.const `c [])) 100).map (·.1) = some (.const `c []) := rfl
example : (inlSubst #[.bvar 0] 1 (.bvar 1) 5).map (·.1) = some (.bvar 1) := rfl
example : (inlSubst #[.bvar 0] 0 (.mdata {} (.bvar 0)) 5).isNone = true := rfl
-- the side condition `c ≤ M` of `inlDropBinder_ph` is needed: here c = 1 > M = 0
example : inlDropBinder 1 (.bvar 0) = some (.bvar 0) := rfl
example : BvarLt (0 + 1) (.bvar 0) = true := by decide
example : BvarLt 0 (.bvar 0) = false := by decide

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``foldl_app_ph ``ExpFoldl
  checkExpected ``inlLift_ph ``ExpLift
  checkExpected ``inlSubst_ph ``ExpSubst
  checkExpected ``inlBeta_ph ``ExpBeta
  checkExpected ``inlSpineAll_ph ``ExpSpine
  checkExpected ``inlMap_ph ``ExpMap
  checkExpected ``inlDropBinder_ph ``ExpDrop
  checkExpected ``inlCanonLam_ph ``ExpCanonLam
  checkExpected ``inlCanonPi_ph ``ExpCanonPi
  checkExpected ``inlSignalMapOfFunctor_ph ``ExpMapOfFunctor
  checkExpected ``inlSignalApplicative_ph ``ExpApplicative
  checkExpected ``inlHeadCtor_ph ``ExpHeadCtor
  checkExpected ``inlineDefs_ph ``ExpInlineDefs
  checkExpected ``userDefinition?_ph ``ExpUserDef
  checkExpected ``inlineDefs_user_ph ``ExpUserInl
  logInfo m!"RT INLINEP1CHECK TYPE 15 declarations compared"
  checkMutant ``inlLift_ph ``MutLift
  checkMutant ``inlSubst_ph ``MutSubst
  checkMutant ``inlBeta_ph ``MutBeta
  checkMutant ``inlDropBinder_ph ``MutDrop
  checkMutant ``inlHeadCtor_ph ``MutHeadCtor
  checkMutant ``inlineDefs_ph ``MutInlineDefs
  checkMutant ``userDefinition?_ph ``MutUserDef
  checkMutant ``inlineDefs_user_ph ``MutUserInlNoHyp
  logInfo m!"RT INLINEP1CHECK MUTANT 8 statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"
  logInfo m!"RT INLINEP1CHECK COUNTS: TYPE 15 / MUTANT 8 / AXIOMS 15 / POSITIVE 7"

def newThms : List Name := [``foldl_app_ph, ``inlLift_ph, ``inlSubst_ph, ``inlBeta_ph, ``inlSpineAll_ph, ``inlMap_ph,
  ``inlDropBinder_ph, ``inlCanonLam_ph, ``inlCanonPi_ph, ``inlSignalMapOfFunctor_ph, ``inlSignalApplicative_ph,
  ``inlHeadCtor_ph, ``inlineDefs_ph, ``userDefinition?_ph, ``inlineDefs_user_ph]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"RT INLINEP1CHECK AXIOMS {newThms.length} declarations checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceInlineP1Check.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceInlineP1Check.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceInlineP1Check.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceInlineP1Check.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceInlineP1Check.direct, `ReaderTraceInlineP1Check.viaHelper, `ReaderTraceInlineP1Check.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 INLINEP1CHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 INLINEP1CHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceInlineP1Check.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 INLINEP1CHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 INLINEP1CHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceInlineP1Check.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceInlineP1Check.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceInlineP1Check.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceInlineP1Check.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceInlineP1Check.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceInlineP1Check.Missing.nowhere do throwError "GEN5 INLINEP1CHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceInlineP1Check.viaHelperU, `ReaderTraceInlineP1Check.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceInlineP1Check.Missing.nowhere do throwError "GEN5 INLINEP1CHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceInlineP1Check.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 INLINEP1CHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 INLINEP1CHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 15 do throwError "GEN5 INLINEP1CHECK CLOSURE FAILED: expected 15 declarations"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 INLINEP1CHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 INLINEP1CHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 INLINEP1CHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 INLINEP1CHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 INLINEP1CHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (15 declarations); all 15 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceInlineP1Check
