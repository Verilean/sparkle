import Tools.ShippingGen5ReaderTraceIota
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceIotaCheck, exit 0; TYPE 6 theorems; MUTANT 13 theorem-statement mutants (signature/defeq rejections, not semantic counterexamples); AXIOMS 12 (standard only); CLOSURE OK 1858 constants from 12 roots, 12 targets seen; 3 intended in-memory sorry negatives print warnings) on the tree of c7e641ff982b816588e1d48891590bb83fe50199 (Lean content identical; this header is comment-only). Written against freeze `scripts/gen5/DG_READERTRACE_FREEZE_REV7.md` §1; clean issue-linked build pending (coder). No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R4c part 1 checks (Tools/ShippingGen5ReaderTraceIota.lean)

TYPE: the frozen theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); helpers are checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples); ill-typed variants are not counted.
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceIotaCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv 

section Expected

def ExpQGetAppArgs : Prop := ∀ (Q : Lean.Expr → Prop) (happ : ∀ f a, Q (.app f a) ↔ Q f ∧ Q a) {e : Lean.Expr} (he : Q e),
    ∀ a ∈ e.getAppArgs, Q a
def ExpBundleIotaPres : Prop := ∀ (Q : Lean.Expr → Prop) (happ : ∀ f a, Q (.app f a) ↔ Q f ∧ Q a)
    (hconst : ∀ c ls, Q (.const c ls)) (e : Lean.Expr) (he : Q e), Q (Sparkle.Compiler.MachRawSurface.bundleIota e)
def ExpProjIotaPres : Prop := ∀ (Q : Lean.Expr → Prop) (happ : ∀ f a, Q (.app f a) ↔ Q f ∧ Q a)
    (projs : Name → Option (Name × Nat × Nat)) (e : Lean.Expr) (he : Q e), Q (machProjIota projs e)
def ExpQAppIN : Prop := ∀ (nDecl : Nat) (st : MachRead) (k d : Nat),
    QApp (fun e => InRange nDecl st k e ∧ NoLoose d e)
def ExpQConstIN : Prop := ∀ (nDecl : Nat) (st : MachRead) (k d : Nat),
    QConst (fun e => InRange nDecl st k e ∧ NoLoose d e)
def ExpBundleProjPh : Prop := ∀ {nDecl : Nat} {st : MachRead} {k d : Nat} (proj : Name → Option (Name × Nat × Nat))
    {f' a' : Lean.Expr} (hf : InRange nDecl st k f' ∧ NoLoose d f') (ha : InRange nDecl st k a' ∧ NoLoose d a'),
    InRange nDecl st k (Sparkle.Compiler.MachRawSurface.bundleIota (machProjIota proj (.app f' a'))) ∧
    NoLoose d (Sparkle.Compiler.MachRawSurface.bundleIota (machProjIota proj (.app f' a')))

-- theorem mutants (well-typed single changes)

def MutGetAppArgsEx : Prop := ∀ (Q : Lean.Expr → Prop) (happ : ∀ f a, Q (.app f a) ↔ Q f ∧ Q a) {e : Lean.Expr} (he : Q e),
    ∃ a ∈ e.getAppArgs, Q a
def MutGetAppArgsNoHapp : Prop := ∀ (Q : Lean.Expr → Prop) {e : Lean.Expr} (he : Q e), ∀ a ∈ e.getAppArgs, Q a
def MutBundleNoHconst : Prop := ∀ (Q : Lean.Expr → Prop) (happ : ∀ f a, Q (.app f a) ↔ Q f ∧ Q a)
    (e : Lean.Expr) (he : Q e), Q (Sparkle.Compiler.MachRawSurface.bundleIota e)
def MutBundleConclE : Prop := ∀ (Q : Lean.Expr → Prop) (happ : ∀ f a, Q (.app f a) ↔ Q f ∧ Q a)
    (hconst : ∀ c ls, Q (.const c ls)) (e : Lean.Expr) (he : Q e), Q e
def MutBundleNoHe : Prop := ∀ (Q : Lean.Expr → Prop) (happ : ∀ f a, Q (.app f a) ↔ Q f ∧ Q a)
    (hconst : ∀ c ls, Q (.const c ls)) (e : Lean.Expr), Q (Sparkle.Compiler.MachRawSurface.bundleIota e)
def MutProjNoHapp : Prop := ∀ (Q : Lean.Expr → Prop)
    (projs : Name → Option (Name × Nat × Nat)) (e : Lean.Expr) (he : Q e), Q (machProjIota projs e)
def MutProjConclE : Prop := ∀ (Q : Lean.Expr → Prop) (happ : ∀ f a, Q (.app f a) ↔ Q f ∧ Q a)
    (projs : Name → Option (Name × Nat × Nat)) (e : Lean.Expr) (he : Q e), Q e
def MutQAppOnlyIR : Prop := ∀ (nDecl : Nat) (st : MachRead) (k d : Nat),
    QApp (fun e => InRange nDecl st k e)
def MutQAppOnlyNL : Prop := ∀ (nDecl : Nat) (st : MachRead) (k d : Nat),
    QApp (fun e => NoLoose d e)
def MutQConstOnlyIR : Prop := ∀ (nDecl : Nat) (st : MachRead) (k d : Nat),
    QConst (fun e => InRange nDecl st k e)
def MutBundleProjOnlyIR : Prop := ∀ {nDecl : Nat} {st : MachRead} {k d : Nat} (proj : Name → Option (Name × Nat × Nat))
    {f' a' : Lean.Expr} (hf : InRange nDecl st k f' ∧ NoLoose d f') (ha : InRange nDecl st k a' ∧ NoLoose d a'),
    InRange nDecl st k (Sparkle.Compiler.MachRawSurface.bundleIota (machProjIota proj (.app f' a')))
def MutBundleProjNoHa : Prop := ∀ {nDecl : Nat} {st : MachRead} {k d : Nat} (proj : Name → Option (Name × Nat × Nat))
    {f' a' : Lean.Expr} (hf : InRange nDecl st k f' ∧ NoLoose d f'),
    InRange nDecl st k (Sparkle.Compiler.MachRawSurface.bundleIota (machProjIota proj (.app f' a'))) ∧
    NoLoose d (Sparkle.Compiler.MachRawSurface.bundleIota (machProjIota proj (.app f' a')))
def MutBundleProjConclArg : Prop := ∀ {nDecl : Nat} {st : MachRead} {k d : Nat} (proj : Name → Option (Name × Nat × Nat))
    {f' a' : Lean.Expr} (hf : InRange nDecl st k f' ∧ NoLoose d f') (ha : InRange nDecl st k a' ∧ NoLoose d a'),
    InRange nDecl st k a' ∧ NoLoose d a'

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``q_getAppArgs ``ExpQGetAppArgs
  checkExpected ``bundleIota_pres ``ExpBundleIotaPres
  checkExpected ``projIota_pres ``ExpProjIotaPres
  checkExpected ``qApp_inRangeNoLoose ``ExpQAppIN
  checkExpected ``qConst_inRangeNoLoose ``ExpQConstIN
  checkExpected ``bundleProj_ph ``ExpBundleProjPh
  logInfo m!"GEN5 IOTACHECK TYPE 6 theorems compared"
  checkMutant ``q_getAppArgs ``MutGetAppArgsEx
  checkMutant ``q_getAppArgs ``MutGetAppArgsNoHapp
  checkMutant ``bundleIota_pres ``MutBundleNoHconst
  checkMutant ``bundleIota_pres ``MutBundleConclE
  checkMutant ``bundleIota_pres ``MutBundleNoHe
  checkMutant ``projIota_pres ``MutProjNoHapp
  checkMutant ``projIota_pres ``MutProjConclE
  checkMutant ``qApp_inRangeNoLoose ``MutQAppOnlyNL
  checkMutant ``qApp_inRangeNoLoose ``MutQAppOnlyIR
  checkMutant ``qConst_inRangeNoLoose ``MutQConstOnlyIR
  checkMutant ``bundleProj_ph ``MutBundleProjOnlyIR
  checkMutant ``bundleProj_ph ``MutBundleProjNoHa
  checkMutant ``bundleProj_ph ``MutBundleProjConclArg
  logInfo m!"GEN5 IOTACHECK MUTANT 13 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``q_argsAcc, ``q_getAppArgs, ``q_spine, ``getD_q, ``Tools.ShippingGen5ReaderTrace.bundleIota_key1, ``Tools.ShippingGen5ReaderTrace.bundleIota_key2, ``Tools.ShippingGen5ReaderTrace.bundleIota_key3, ``bundleIota_pres, ``projIota_pres, ``qApp_inRangeNoLoose, ``qConst_inRangeNoLoose, ``bundleProj_ph]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 IOTACHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceIotaCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceIotaCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceIotaCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceIotaCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceIotaCheck.direct, `ReaderTraceIotaCheck.viaHelper, `ReaderTraceIotaCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 IOTACHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 IOTACHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceIotaCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 IOTACHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 IOTACHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceIotaCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceIotaCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceIotaCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceIotaCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceIotaCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceIotaCheck.Missing.nowhere do throwError "GEN5 IOTACHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceIotaCheck.viaHelperU, `ReaderTraceIotaCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceIotaCheck.Missing.nowhere do throwError "GEN5 IOTACHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceIotaCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 IOTACHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 IOTACHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 12 do throwError "GEN5 IOTACHECK CLOSURE FAILED: expected 12 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 IOTACHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 IOTACHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 IOTACHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 IOTACHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 IOTACHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (12 theorems); all 12 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceIotaCheck
