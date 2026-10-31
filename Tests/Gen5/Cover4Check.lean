import Tools.ShippingGen5Cover4
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in g5cv-r9 at d75f5b18 (Pod `kjob lake build Tests.Gen5.Cover4Check`, exit 0; TYPE 5, MUTANT 5, AXIOMS 5 standard, CLOSURE OK 4098 constants with 3 negative / 2 clean controls, UNKNOWN 3 negative / 1 clean; 3 intended sorry negatives print 3 "declaration uses `sorry`" warnings). Clean build is the coder's. No sorry / axiom / native_decide in source.
/-! # DG-COVER rev5 U-E1 (Tools/ShippingGen5Cover4.lean) checks

TYPE: each theorem is compared by the SAME comparer (`checkExpected`: binder names / binder info / `==` then `isDefEq` fallback, logged) with an `Exp…` statement
written here from the freeze text `scripts/gen5/DG_COVER_FREEZE_REV5.md` §3 and from the `MachineData.ok` rows as read in `Tools/ShippingMachineAuto.lean`,
without the Tools file's definitions (only `MachineData` projections, `ShapeAgree`/`FullInv`/`LetQuoteEq`/`LetsNoLoose` structure names, `callArgs`/`cleanLets` are shared).
Counting rule: one compared declaration = 1. TYPE = 5 theorems (`checkExpected`); MUTANT = 5 (`checkMutant`); AXIOMS = 5 theorems.
MUTANT: one-place changes, each well-typed, rejected by the same comparer — a signature / defeq rejection, NOT a semantic counterexample.
CLOSURE: value-closure walk over `getUsedConstants`; unknown names throw; negative controls built in memory inside `withoutModifyingEnv`
(3 intended `sorry`-based negatives, so the build prints 3 "declaration uses `sorry`" warnings). -/

namespace Tests.Gen5.Cover4Check
open Lean Meta Elab
open Tools.ShippingGen5Cover4 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingMachineAuto Tools.ShippingGen5Cover3
open Tools.ShippingGen5Sem (kDOf callArgs cleanLets)

section Expected

def ExpRowKb : Prop := ∀ {d : MachineData} (hok : d.ok = true),
    ∀ j, j < d.kb → d.K (d.bpos j) = some .bool ∧ d.bpos j < d.nIn + d.ss.length + d.ls.length

def ExpRowKv : Prop := ∀ {d : MachineData} (hok : d.ok = true),
    ∀ j, j < d.kv → d.K (d.vpos j) = some (.bits (d.vw j)) ∧ d.vpos j < d.nIn + d.ss.length + d.ls.length

def ExpBpos : Prop := ∀ {d : MachineData} (hok : d.ok = true) (hpos : 0 < d.nIn + d.ss.length + d.ls.length),
    ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length

def ExpVpos : Prop := ∀ {d : MachineData} (hok : d.ok = true) (hpos : 0 < d.nIn + d.ss.length + d.ls.length),
    ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length

def ExpRowCOk : Prop := ∀ {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hq : LetQuoteEq d st) (hnl : LetsNoLoose st) (hok : d.ok = true),
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

/-- Mutant: `≤` for `<`. -/
def MutBposLe : Prop := ∀ {d : MachineData} (hok : d.ok = true) (hpos : 0 < d.nIn + d.ss.length + d.ls.length),
    ∀ j, d.bpos j ≤ d.nIn + d.ss.length + d.ls.length

/-- Mutant: no `hpos`. -/
def MutBposNoPos : Prop := ∀ {d : MachineData} (hok : d.ok = true),
    ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length

def MutVposNoPos : Prop := ∀ {d : MachineData} (hok : d.ok = true),
    ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length

/-- Mutant: the conclusion's conjunction is cut to its first conjunct. -/
def MutRowKbNoBound : Prop := ∀ {d : MachineData} (hok : d.ok = true),
    ∀ j, j < d.kb → d.K (d.bpos j) = some .bool

/-- Mutant: no `hok`. -/
def MutRowCNoOk : Prop := ∀ {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hq : LetQuoteEq d st) (hnl : LetsNoLoose st),
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``ok_row_kb ``ExpRowKb
  checkExpected ``ok_row_kv ``ExpRowKv
  checkExpected ``bpos_lt_of_ok ``ExpBpos
  checkExpected ``vpos_lt_of_ok ``ExpVpos
  checkExpected ``rowC_of_reader_ok ``ExpRowCOk
  -- mutants (same comparer; signature / defeq rejection, not semantic counterexamples)
  checkMutant ``bpos_lt_of_ok ``MutBposLe
  checkMutant ``bpos_lt_of_ok ``MutBposNoPos
  checkMutant ``vpos_lt_of_ok ``MutVposNoPos
  checkMutant ``ok_row_kb ``MutRowKbNoBound
  checkMutant ``rowC_of_reader_ok ``MutRowCNoOk
  logInfo m!"GEN5 COVER4 TYPE 5 / MUTANT 5 (declarations compared, one each)"

def allThms : List Name := [``ok_row_kb, ``ok_row_kv, ``bpos_lt_of_ok, ``vpos_lt_of_ok, ``rowC_of_reader_ok]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in allThms do checkAxioms n

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
    addDecl (.thmDecl { name := `Cover4Ctl.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `Cover4Ctl.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `Cover4Ctl.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `Cover4Ctl.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`Cover4Ctl.direct, `Cover4Ctl.viaHelper, `Cover4Ctl.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 COVER4 CLOSURE CONTROL FAILED: {n} not detected"
    for n in [`Cover4Ctl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 COVER4 CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 COVER4 CLOSURE CONTROLS OK: 3 negative controls detected, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `Cover4Ctl.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `Cover4Ctl.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `Cover4Ctl.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `Cover4Ctl.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`Cover4Ctl.Missing.nowhere]
    unless unkRoot.contains `Cover4Ctl.Missing.nowhere do throwError "GEN5 COVER4 UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`Cover4Ctl.viaHelperU, `Cover4Ctl.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `Cover4Ctl.Missing.nowhere do throwError "GEN5 COVER4 UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`Cover4Ctl.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 COVER4 UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 COVER4 UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env allThms
  unless hits.isEmpty do throwError "GEN5 COVER4 CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "native").length > 1 then
      throwError "GEN5 COVER4 CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 COVER4 CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 COVER4 CLOSURE OK: {seen.toList.length} constants, no forbidden constant"

#print axioms rowC_of_reader_ok

end Tests.Gen5.Cover4Check
