import Tools.ShippingGen5Cover6
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in g5cv-r13 at ef0612b5 (Pod `kjob lake build Tests.Gen5.Cover6Check`, exit 0; TYPE 7 theorems + 1 def, INDUCTIVE 1, MUTANT 6 statement + 2 inductive, AXIOMS 7 standard, CLOSURE OK 2062 constants with 3 negative / 2 clean controls, UNKNOWN 3 negative / 1 clean; 3 intended sorry negatives print 3 warnings). Clean build is the coder's. No sorry / axiom / native_decide in source.
/-! # DG-COVER rev7 U-E3a (Tools/ShippingGen5Cover6.lean) checks

TYPE: every declaration is compared by the SAME comparer (`checkExpected`: binder names / binder info / `==` then `isDefEq` fallback, logged) with an `Exp…` statement
written here from the freeze text `scripts/gen5/DG_COVER_FREEZE_REV7.md` §2.1 (own spelling; the Tools file is not copied).
Counting rule: one compared declaration = 1. TYPE = 7 theorems (the 6 frozen: `reachC_of_reach`, `reachC_trans`, `fullInv_reachC`, `reachC_sizes_mono`, `fullInv_empty`, `reserved_reachC`;
plus the unfrozen helper `fullInv_ctrl`) + 1 `def` (`CtrlEq`, value compared) = 8 compared non-inductive declarations.
`FReachC` (inductive) is compared separately (INDUCTIVE = 1): type, numParams/numIndices, constructor names, and every constructor's type against `ExpFReachC`'s (the own-spelling inductive below), via the same `cmpTele`.
MUTANT: well-typed single changes only, rejected by the same comparer (signature / defeq rejection, NOT a semantic counterexample):
statement mutants 6 (5 theorem + 1 def) + inductive mutants 2 (one constructor changed each) = 8. AXIOMS = 7 theorems.
CLOSURE: value-closure walk over `getUsedConstants`; unknown names throw; negative controls built in memory inside `withoutModifyingEnv`
(3 intended `sorry`-based negatives, so the build prints 3 "declaration uses `sorry`" warnings). -/

namespace Tests.Gen5.Cover6Check
open Lean Meta Elab
open Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingReaderLenOk

section Expected

/-- Expected body of `CtrlEq` (own spelling; reads the freeze: seven fields of `st'` equal those of `st`). -/
def ExpCtrlEq : MachRead → MachRead → Prop := fun st st' =>
  st'.lets = st.lets ∧ st'.insts = st.insts ∧ st'.instOrigins = st.instOrigins ∧
  st'.kinds = st.kinds ∧ st'.inits = st.inits ∧ st'.names = st.names ∧ st'.ws = st.ws

/-- Expected constructors of `FReachC` (own spelling, same constructor names; compared constructor by constructor). -/
inductive ExpFReachC (nDecl : Nat) : MachRead → MachRead → Prop
  | refl (st : MachRead) : ExpFReachC nDecl st st
  | tail {a b c : MachRead} : ExpFReachC nDecl a b → FStep nDecl b c → ExpFReachC nDecl a c
  | ctrl {a b c : MachRead} : ExpFReachC nDecl a b → Tools.ShippingGen5Cover6.CtrlEq b c → ExpFReachC nDecl a c

def ExpOfReach : Prop := ∀ {nDecl : Nat} {a b : MachRead} (h : FReach nDecl a b), FReachC nDecl a b

def ExpTrans : Prop := ∀ {nDecl : Nat} {a b c : MachRead} (h1 : FReachC nDecl a b) (h2 : FReachC nDecl b c), FReachC nDecl a c

def ExpCtrlInv : Prop := ∀ {nDecl : Nat} {b c : MachRead} (h : FullInv nDecl b) (hc : Tools.ShippingGen5Cover6.CtrlEq b c), FullInv nDecl c

def ExpFullInvReachC : Prop := ∀ {nDecl : Nat} {st0 st : MachRead} (h : FullInv nDecl st0) (hr : FReachC nDecl st0 st), FullInv nDecl st

def ExpSizes : Prop := ∀ {nDecl : Nat} {a b : MachRead} (hr : FReachC nDecl a b),
    a.lets.size ≤ b.lets.size ∧ a.insts.size ≤ b.insts.size ∧ a.kinds.size ≤ b.kinds.size

def ExpEmpty : Prop := ∀ {nDecl : Nat}, FullInv nDecl ({} : MachRead)

def ExpReserved : Prop := ∀ {nDecl : Nat} {st : MachRead} {dom' body : Lean.Expr} {kinds : List MixedGateBinder} {inits : List Nat},
    FReachC nDecl st (reserved st dom' body kinds inits)

/-- Mutant: `reserved_reachC` with the weaker closure `FReach` (the `machReserve` step is not an `FStep` chain). -/
def MutReservedFReach : Prop := ∀ {nDecl : Nat} {st : MachRead} {dom' body : Lean.Expr} {kinds : List MixedGateBinder} {inits : List Nat},
    FReach nDecl st (reserved st dom' body kinds inits)

/-- Mutant: `fullInv_reachC` without the premise `h`. -/
def MutFullInvNoH : Prop := ∀ {nDecl : Nat} {st0 st : MachRead} (hr : FReachC nDecl st0 st), FullInv nDecl st

/-- Mutant: `reachC_sizes_mono` with `<` on `kinds` (single change). -/
def MutSizesLt : Prop := ∀ {nDecl : Nat} {a b : MachRead} (hr : FReachC nDecl a b),
    a.lets.size ≤ b.lets.size ∧ a.insts.size ≤ b.insts.size ∧ a.kinds.size < b.kinds.size

/-- Mutant: `reachC_sizes_mono` with the last conjunct dropped (conclusion-conjunct drop). -/
def MutSizesDrop : Prop := ∀ {nDecl : Nat} {a b : MachRead} (hr : FReachC nDecl a b),
    a.lets.size ≤ b.lets.size ∧ a.insts.size ≤ b.insts.size

/-- Mutant: `reachC_trans` with the conclusion endpoints swapped (`z x` for `x z`). -/
def MutTransSwap : Prop := ∀ {nDecl : Nat} {a b c : MachRead} (h1 : FReachC nDecl a b) (h2 : FReachC nDecl b c), FReachC nDecl c a

/-- Mutant `CtrlEq`: the `ws` conjunct dropped. -/
def MutCtrlNoWs : MachRead → MachRead → Prop := fun st st' =>
  st'.lets = st.lets ∧ st'.insts = st.insts ∧ st'.instOrigins = st.instOrigins ∧
  st'.kinds = st.kinds ∧ st'.inits = st.inits ∧ st'.names = st.names

/-- Mutant inductive: `ctrl` with `CtrlEq` arguments reversed. -/
inductive MutFReachCRev (nDecl : Nat) : MachRead → MachRead → Prop
  | refl (st : MachRead) : MutFReachCRev nDecl st st
  | tail {a b c : MachRead} : MutFReachCRev nDecl a b → FStep nDecl b c → MutFReachCRev nDecl a c
  | ctrl {a b c : MachRead} : MutFReachCRev nDecl a b → Tools.ShippingGen5Cover6.CtrlEq c b → MutFReachCRev nDecl a c

/-- Mutant inductive: `tail` with the `FStep` premise taken from `a` instead of `b` (`FStep nDecl a c`). -/
inductive MutFReachCStep (nDecl : Nat) : MachRead → MachRead → Prop
  | refl (st : MachRead) : MutFReachCStep nDecl st st
  | tail {a b c : MachRead} : MutFReachCStep nDecl a b → FStep nDecl a c → MutFReachCStep nDecl a c
  | ctrl {a b c : MachRead} : MutFReachCStep nDecl a b → Tools.ShippingGen5Cover6.CtrlEq b c → MutFReachCStep nDecl a c

end Expected

/-- Inductive comparison: same type, parameter/index counts and constructor names, and each constructor type compared by `cmpTele`
after renaming the expected inductive to the tested one. Throws on any difference. -/
def cmpInductive (tested exp : Name) : MetaM Unit := do
  let .inductInfo t ← getConstInfo tested | throwError "GEN6 CHECK FAILED: {tested} is not an inductive"
  let .inductInfo e ← getConstInfo exp | throwError "GEN6 CHECK FAILED: {exp} is not an inductive"
  unless t.numParams == e.numParams && t.numIndices == e.numIndices && t.ctors.length == e.ctors.length do
    throwError "GEN6 CHECK FAILED {tested}: numParams/numIndices/ctor count differ"
  let rn (x : Expr) : Expr := x.replace fun
    | .const c ls => if c == exp then some (.const tested ls) else none
    | _ => none
  cmpTele s!"{tested} type" t.type (rn e.type)
  for (ct, ce) in t.ctors.zip e.ctors do
    unless ct.getString! == ce.getString! do
      throwError "GEN6 CHECK FAILED {tested}: constructor {ct} vs {ce}"
    let cit ← getConstInfo ct
    let cie ← getConstInfo ce
    cmpTele s!"{ct}" cit.type (rn cie.type)

def checkIndMutant (tested mt : Name) : MetaM Unit := do
  let ok ← withoutModifyingState do
    try cmpInductive tested mt; pure true catch _ => pure false
  if ok then throwError "GEN6 MUTANT ACCEPTED: {mt} matches {tested}"
  logInfo m!"GEN6 INDUCTIVE MUTANT REJECTED {mt} (against {tested})"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``reachC_of_reach ``ExpOfReach
  checkExpected ``reachC_trans ``ExpTrans
  checkExpected ``fullInv_ctrl ``ExpCtrlInv
  checkExpected ``fullInv_reachC ``ExpFullInvReachC
  checkExpected ``reachC_sizes_mono ``ExpSizes
  checkExpected ``fullInv_empty ``ExpEmpty
  checkExpected ``reserved_reachC ``ExpReserved
  checkExpected ``CtrlEq ``ExpCtrlEq
  cmpInductive ``FReachC ``ExpFReachC
  logInfo m!"GEN5 COVER6 TYPE 7 theorems + 1 def (CtrlEq) / INDUCTIVE 1 (FReachC, 3 constructors)"
  -- mutants (same comparer; signature / defeq rejection, not semantic counterexamples)
  checkMutant ``reserved_reachC ``MutReservedFReach
  checkMutant ``fullInv_reachC ``MutFullInvNoH
  checkMutant ``reachC_sizes_mono ``MutSizesLt
  checkMutant ``reachC_sizes_mono ``MutSizesDrop
  checkMutant ``reachC_trans ``MutTransSwap
  checkMutant ``CtrlEq ``MutCtrlNoWs
  checkIndMutant ``FReachC ``MutFReachCRev
  checkIndMutant ``FReachC ``MutFReachCStep
  logInfo m!"GEN5 COVER6 MUTANT 6 statement (5 theorem + 1 def) + 2 inductive"

def allThms : List Name := [``reachC_of_reach, ``reachC_trans, ``fullInv_ctrl, ``fullInv_reachC, ``reachC_sizes_mono, ``fullInv_empty, ``reserved_reachC]

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
    addDecl (.thmDecl { name := `Cover6Ctl.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `Cover6Ctl.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `Cover6Ctl.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `Cover6Ctl.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`Cover6Ctl.direct, `Cover6Ctl.viaHelper, `Cover6Ctl.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 COVER6 CLOSURE CONTROL FAILED: {n} not detected"
    for n in [`Cover6Ctl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 COVER6 CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 COVER6 CLOSURE CONTROLS OK: 3 negative controls detected, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `Cover6Ctl.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `Cover6Ctl.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `Cover6Ctl.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `Cover6Ctl.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`Cover6Ctl.Missing.nowhere]
    unless unkRoot.contains `Cover6Ctl.Missing.nowhere do throwError "GEN5 COVER6 UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`Cover6Ctl.viaHelperU, `Cover6Ctl.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `Cover6Ctl.Missing.nowhere do throwError "GEN5 COVER6 UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`Cover6Ctl.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 COVER6 UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 COVER6 UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env allThms
  unless hits.isEmpty do throwError "GEN5 COVER6 CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 COVER6 CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 COVER6 CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 COVER6 CLOSURE OK: {seen.toList.length} constants, no forbidden constant"

#print axioms reserved_reachC

end Tests.Gen5.Cover6Check
