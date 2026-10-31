import Tools.ShippingGen5ReaderTraceArms
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT yet (U-R3a checks, written against freeze rev3 `scripts/gen5/DG_READERTRACE_FREEZE_REV3.md`, approved at 730c8fa8). No sorry / axiom / native_decide in source; the intended sorry-based negatives of the closure controls are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R3a checks (Tools/ShippingGen5ReaderTraceArms.lean)

TYPE: each declaration of `DG_READERTRACE_FREEZE_REV3.md` §1 is compared by `checkExpected` (`Tests/Gen3/ExpectedType.lean`) against an `Exp…` statement written here from the freeze text (own spelling).
Match defs (`IsAtom`, `ConvBasic`): independent `Exp` match version + a FULL-argument agreement theorem (`cases e <;> exact Iff.rfl`), plus a per-constructor comparer `exprAgree`
(the SAME comparer for the real def and for mutants). Theorem mutants use `checkMutant` (the comparer of TYPE). Mutants are well-typed single changes, rejected by signature / defeq
(NOT semantic counterexamples); ill-typed variants are not counted.
`conv_basic_trace` is stated under `hT : TraceGood senv nDecl (readF senv n)` and `hv`; `readF_traceGood_of_step` under `hstep`: both conditions are explicit in the statements compared here.
CLOSURE: value-closure walk from all 10 declarations (plus the two agreement theorems), forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceArmsCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpIsAtom : Lean.Expr → Prop
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | .bvar _ => False
  | .app _ _ => False
  | .lam _ _ _ _ => False
  | .forallE _ _ _ _ => False
  | .letE _ _ _ _ _ => False
  | .mdata _ _ => False
  | .proj _ _ _ => False

def ExpConvBasic : Lean.Expr → Prop
  | .bvar _ => True
  | .lam _ _ _ _ => True
  | .forallE _ _ _ _ => True
  | .mdata _ _ => True
  | .proj _ _ _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | .app _ _ => False
  | .letE _ _ _ _ _ => False

theorem isAtom_eq_exp : ∀ e : Lean.Expr, IsAtom e ↔ ExpIsAtom e := by intro e; cases e <;> exact Iff.rfl
theorem convBasic_eq_exp : ∀ e : Lean.Expr, ConvBasic e ↔ ExpConvBasic e := by intro e; cases e <;> exact Iff.rfl

def ExpInRangeAtom : Prop := ∀ {nDecl k : Nat} {st : MachRead} {e : Lean.Expr}
    (ha : IsAtom e) (hn : NoPh e = true), InRange nDecl st k e
def ExpNoLooseAtom : Prop := ∀ {d : Nat} {e : Lean.Expr} (ha : IsAtom e), NoLoose d e
def ExpInRangeLam : Prop := ∀ {nDecl k : Nat} {st : MachRead} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : InRange nDecl st k t) (hb : InRange nDecl st k b), InRange nDecl st k (.lam nm t b bi)
def ExpInRangeForallE : Prop := ∀ {nDecl k : Nat} {st : MachRead} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : InRange nDecl st k t) (hb : InRange nDecl st k b), InRange nDecl st k (.forallE nm t b bi)
def ExpNoLooseLam : Prop := ∀ {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : NoLoose d t) (hb : NoLoose (d + 1) b), NoLoose d (.lam nm t b bi)
def ExpNoLooseForallE : Prop := ∀ {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo}
    (ht : NoLoose d t) (hb : NoLoose (d + 1) b), NoLoose d (.forallE nm t b bi)
def ExpConvBasicTrace : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead)
    (hb : ConvBasic e)
    (hpre : TracePre senv nDecl (Call.conv env d e st))
    (v : (Call.conv env d e st).Res)
    (hv : (convStep senv env d e st).run (readF senv n) = some (some v)),
    FReachC nDecl st (callOut (Call.conv env d e st) v) ∧ PhPost senv nDecl (Call.conv env d e st) v
def ExpReadFTraceGoodOfStep : Prop := ∀ (senv : StructEnv) (F : PureFacts senv) (nDecl : Nat)
    (hstep : ∀ n : Nat, TraceGood senv nDecl (readF senv n) →
      ∀ c : Call, TracePre senv nDecl c → ∀ v : c.Res,
        (step senv c).run (readF senv n) = some (some v) →
        FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v),
    ∀ n : Nat, TraceGood senv nDecl (readF senv n)

-- theorem mutants (well-typed single changes)
def MutNoLooseLam : Prop := ∀ {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo},
    NoLoose d t → NoLoose d b → NoLoose d (.lam nm t b bi)
def MutNoLooseForallE : Prop := ∀ {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo},
    NoLoose d t → NoLoose d b → NoLoose d (.forallE nm t b bi)
def MutInRangeLamNoHb : Prop := ∀ {nDecl k : Nat} {st : MachRead} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo},
    InRange nDecl st k t → InRange nDecl st k (.lam nm t b bi)
def MutInRangeAtomNoHn : Prop := ∀ {nDecl k : Nat} {st : MachRead} {e : Lean.Expr},
    IsAtom e → InRange nDecl st k e
def MutConvBasicTraceNoHb : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (n : Nat),
    TraceGood senv nDecl (readF senv n) →
    ∀ (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead),
      TracePre senv nDecl (Call.conv env d e st) →
      ∀ (v : (Call.conv env d e st).Res),
        (convStep senv env d e st).run (readF senv n) = some (some v) →
        FReachC nDecl st (callOut (Call.conv env d e st) v) ∧ PhPost senv nDecl (Call.conv env d e st) v
def MutConvBasicTraceNoReach : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (n : Nat),
    TraceGood senv nDecl (readF senv n) →
    ∀ (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead),
      ConvBasic e →
      TracePre senv nDecl (Call.conv env d e st) →
      ∀ (v : (Call.conv env d e st).Res),
        (convStep senv env d e st).run (readF senv n) = some (some v) →
        PhPost senv nDecl (Call.conv env d e st) v
def MutConvBasicTraceNoPhPost : Prop := ∀ (senv : StructEnv) (nDecl : Nat) (n : Nat),
    TraceGood senv nDecl (readF senv n) →
    ∀ (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead),
      ConvBasic e →
      TracePre senv nDecl (Call.conv env d e st) →
      ∀ (v : (Call.conv env d e st).Res),
        (convStep senv env d e st).run (readF senv n) = some (some v) →
        FReachC nDecl st (callOut (Call.conv env d e st) v)
def MutStepNoPhPost : Prop := ∀ (senv : StructEnv), PureFacts senv → ∀ (nDecl : Nat),
    (∀ n : Nat, TraceGood senv nDecl (readF senv n) →
      ∀ c : Call, TracePre senv nDecl c → ∀ v : c.Res,
        (step senv c).run (readF senv n) = some (some v) →
        FReachC nDecl (callSt c) (callOut c v)) →
    ∀ n : Nat, TraceGood senv nDecl (readF senv n)
def MutStepNoIH : Prop := ∀ (senv : StructEnv), PureFacts senv → ∀ (nDecl : Nat),
    (∀ n : Nat,
      ∀ c : Call, TracePre senv nDecl c → ∀ v : c.Res,
        (step senv c).run (readF senv n) = some (some v) →
        FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v) →
    ∀ n : Nat, TraceGood senv nDecl (readF senv n)

-- match-def mutants (well-typed single changes; compared by `exprAgree`)
def MutConvBasicApp : Lean.Expr → Prop
  | .bvar _ => True
  | .lam _ _ _ _ => True
  | .forallE _ _ _ _ => True
  | .mdata _ _ => True
  | .proj _ _ _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | .app _ _ => True
  | .letE _ _ _ _ _ => False
def MutConvBasicLetE : Lean.Expr → Prop
  | .bvar _ => True
  | .lam _ _ _ _ => True
  | .forallE _ _ _ _ => True
  | .mdata _ _ => True
  | .proj _ _ _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | .app _ _ => False
  | .letE _ _ _ _ _ => True
def MutConvBasicNoBvar : Lean.Expr → Prop
  | .bvar _ => False
  | .lam _ _ _ _ => True
  | .forallE _ _ _ _ => True
  | .mdata _ _ => True
  | .proj _ _ _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | .app _ _ => False
  | .letE _ _ _ _ _ => False
def MutIsAtomNoSort : Lean.Expr → Prop
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => False
  | .const _ _ => True
  | .lit _ => True
  | .bvar _ => False
  | .app _ _ => False
  | .lam _ _ _ _ => False
  | .forallE _ _ _ _ => False
  | .letE _ _ _ _ _ => False
  | .mdata _ _ => False
  | .proj _ _ _ => False
def MutIsAtomBvar : Lean.Expr → Prop
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lit _ => True
  | .bvar _ => True
  | .app _ _ => False
  | .lam _ _ _ _ => False
  | .forallE _ _ _ _ => False
  | .letE _ _ _ _ _ => False
  | .mdata _ _ => False
  | .proj _ _ _ => False

end Expected

/-- The SAME per-constructor comparer for the real match def `f` and for every mutant `g`: both applied to a `Lean.Expr` built from fresh constructor arguments;
all 12 constructors must be defeq. Returns the failing constructors. -/
def exprAgree (f g : Name) : MetaM (List Name) := do
  let ctors : List Name := [``Lean.Expr.bvar, ``Lean.Expr.fvar, ``Lean.Expr.mvar, ``Lean.Expr.sort, ``Lean.Expr.const, ``Lean.Expr.app,
    ``Lean.Expr.lam, ``Lean.Expr.forallE, ``Lean.Expr.letE, ``Lean.Expr.lit, ``Lean.Expr.mdata, ``Lean.Expr.proj]
  let fTy ← inferType (mkConst f)
  let gTy ← inferType (mkConst g)
  unless (← isDefEq fTy gTy) do throwError "GEN5 ARMSCHECK exprAgree: signatures of {f} and {g} differ"
  let mut bad : List Name := []
  for ctor in ctors do
    let ok ← forallTelescope (← inferType (mkConst ctor)) fun cargs _ => do
      let c := mkAppN (mkConst ctor) cargs
      withoutModifyingState (isDefEq (mkApp (mkConst f) c) (mkApp (mkConst g) c))
    unless ok do bad := bad ++ [ctor]
  pure bad

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``inRange_atom ``ExpInRangeAtom
  checkExpected ``noLoose_atom ``ExpNoLooseAtom
  checkExpected ``inRange_lam ``ExpInRangeLam
  checkExpected ``inRange_forallE ``ExpInRangeForallE
  checkExpected ``noLoose_lam ``ExpNoLooseLam
  checkExpected ``noLoose_forallE ``ExpNoLooseForallE
  checkExpected ``conv_basic_trace ``ExpConvBasicTrace
  checkExpected ``readF_traceGood_of_step ``ExpReadFTraceGoodOfStep
  logInfo m!"GEN5 ARMSCHECK TYPE 8 theorems compared (inRange_atom, noLoose_atom, inRange_lam, inRange_forallE, noLoose_lam, noLoose_forallE, conv_basic_trace, readF_traceGood_of_step)"
  -- match defs: real vs independent Exp, per constructor, same comparer
  for (f, g) in [(``IsAtom, ``ExpIsAtom), (``ConvBasic, ``ExpConvBasic)] do
    let bad ← exprAgree f g
    unless bad.isEmpty do throwError "GEN5 ARMSCHECK CHECK FAILED: {f} disagrees with {g} at {bad}"
  logInfo m!"GEN5 ARMSCHECK TYPE 2 match defs (IsAtom, ConvBasic) x 12 constructors agree with the independent versions; whole-domain agreement is the 2 theorems isAtom_eq_exp, convBasic_eq_exp"
  -- theorem mutants (same comparer as TYPE)
  checkMutant ``noLoose_lam ``MutNoLooseLam
  checkMutant ``noLoose_forallE ``MutNoLooseForallE
  checkMutant ``inRange_lam ``MutInRangeLamNoHb
  checkMutant ``inRange_atom ``MutInRangeAtomNoHn
  checkMutant ``conv_basic_trace ``MutConvBasicTraceNoHb
  checkMutant ``conv_basic_trace ``MutConvBasicTraceNoReach
  checkMutant ``conv_basic_trace ``MutConvBasicTraceNoPhPost
  checkMutant ``readF_traceGood_of_step ``MutStepNoPhPost
  checkMutant ``readF_traceGood_of_step ``MutStepNoIH
  logInfo m!"GEN5 ARMSCHECK MUTANT 9 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"
  -- match-def mutants through exprAgree against the independent version
  let mm : List (Name × Name × List Name) :=
    [ (``MutConvBasicApp, ``ExpConvBasic, [``Lean.Expr.app]),
      (``MutConvBasicLetE, ``ExpConvBasic, [``Lean.Expr.letE]),
      (``MutConvBasicNoBvar, ``ExpConvBasic, [``Lean.Expr.bvar]),
      (``MutIsAtomNoSort, ``ExpIsAtom, [``Lean.Expr.sort]),
      (``MutIsAtomBvar, ``ExpIsAtom, [``Lean.Expr.bvar]) ]
  let mut nm : Nat := 0
  for (g, ex, expectBad) in mm do
    let bad ← exprAgree g ex
    unless bad == expectBad do throwError "GEN5 ARMSCHECK MATCHDEF MUTANT ACCEPTED/UNEXPECTED: {g} disagrees at {bad}, expected {expectBad}"
    nm := nm + 1
  logInfo m!"GEN5 ARMSCHECK MATCHDEF MUTANT {nm} well-typed match-def mutants each rejected at exactly the changed constructor (signature/defeq rejection, not a semantic counterexample); with the 9 theorem mutants: 14"

def newThms : List Name := [``inRange_atom, ``noLoose_atom, ``inRange_lam, ``inRange_forallE, ``noLoose_lam, ``noLoose_forallE,
  ``conv_basic_trace, ``readF_traceGood_of_step]
def newDefs : List Name := [``IsAtom, ``ConvBasic]
def allThms : List Name := newThms ++ [``isAtom_eq_exp, ``convBasic_eq_exp]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in allThms do checkAxioms n
  logInfo m!"GEN5 ARMSCHECK AXIOMS {allThms.length} theorems checked (standard axioms only)"

-- closure roots = the 2 new defs + the 8 new theorems + the 2 agreement theorems; the 10 freeze declarations must all be in `seen`
def closureRoots : List Name := newDefs ++ allThms

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
    addDecl (.thmDecl { name := `ReaderTraceArms.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceArms.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceArms.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceArms.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceArms.direct, `ReaderTraceArms.viaHelper, `ReaderTraceArms.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 ARMSCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 ARMSCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceArms.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 ARMSCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 ARMSCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceArms.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceArms.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceArms.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceArms.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceArms.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceArms.Missing.nowhere do throwError "GEN5 ARMSCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceArms.viaHelperU, `ReaderTraceArms.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceArms.Missing.nowhere do throwError "GEN5 ARMSCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceArms.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 ARMSCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 ARMSCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newDefs.length == 2 && newThms.length == 8 do throwError "GEN5 ARMSCHECK CLOSURE FAILED: expected 2 defs + 8 theorems"
  for n in newDefs ++ newThms do
    unless seen.contains n do throwError "GEN5 ARMSCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 ARMSCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 ARMSCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 ARMSCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 ARMSCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (2 defs + 8 theorems + 2 agreement theorems); all 10 target declarations (2 defs + 8 theorems) in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceArmsCheck
