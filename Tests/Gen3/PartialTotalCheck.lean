import Tools.PartialTotal.Agree
import Tools.Assume.N3Extern
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT: K1 skeleton check (built OK at 6e3739fd, exit 0) (the four roots still carry `sorry`; the axiom report below logs `sorryAx` instead of throwing).

/-! # Partial-total agreement checks (scripts/gen3/PARTIAL_TOTAL_FREEZE.md §3)

1. **Expected types.** The four theorems of `Tools/PartialTotal/Agree.lean` and the three premise definitions they prove
   (`BoolMapCorr`, `LiftScalarCorr`, `RootFloatAgrees`, unchanged) are compared MECHANICALLY
   (`Tests.Gen3.ExpectedType.checkExpected`, run under `withReducible`) against `Exp…` statements written below from the
   freeze text, with the premise definitions spelled out. The SAME comparator is used for the negative controls.
   The three compiler definitions are checked to be total (`defnInfo`, not `opaque`) with the expected type.
2. **Mutants** (statement variants): each must be REJECTED by the same comparator. These are rejections by signature /
   (reducible) defeq of the statements; they are NOT semantic counterexamples.
3. **Closure.** The constants occurring in each statement must all be in an explicit allow-list; an unknown name FAILS
   (a negative control with a name removed from the list checks that the closure test can fail).
4. **Axioms.** The report logs the axioms of every root and of the three compiler definitions. Standard axioms are accepted;
   `sorryAx` is only LOGGED for the roots (skeleton); any other axiom throws. -/

namespace Tests.Gen3.PartialTotalCheck
open Lean Meta
open Tests.Gen3.ExpectedType

/-! ## 1. Expected statements (independent text) -/

def ExpBoolMapEq : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv) (dom a : Lean.Expr) (wa : Nat) (body : Lean.Expr),
    Sparkle.Compiler.Elab.machBoolMap senv dom a wa body =
      Tools.Prototype.BoolMapModelLetOk.boolMapModel
        (Sparkle.Compiler.Elab.machLiftScalarN senv dom [(wa, a)]) dom body

def ExpBoolMapCorr : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv), Tools.Prototype.BoolMapModelLetOk.BoolMapCorr senv

def ExpLiftScalarCorr : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv), Tools.Prototype.LiftScalarModelLetOk.LiftScalarCorr senv

def ExpRootFloatAgrees : Prop :=
  ∀ (hl : Tools.ShippingLetsReaderInv.LiftAgrees), Tools.ShippingLetsReaderInv.RootFloatAgrees

-- the premise definitions, spelled out (they are the statements the theorems prove)
def ExpBoolMapCorrDef (senv : Sparkle.Compiler.Elab.StructEnv) : Prop :=
  ∀ (dom a : Lean.Expr) (wa : Nat) (body r : Lean.Expr),
    Sparkle.Compiler.Elab.machBoolMap senv dom a wa body = some r →
      Tools.Prototype.BoolMapModelLetOk.boolMapModel
        (Sparkle.Compiler.Elab.machLiftScalarN senv dom [(wa, a)]) dom body = some r

def ExpLiftScalarCorrDef (senv : Sparkle.Compiler.Elab.StructEnv) : Prop :=
  ∀ (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) (w : Nat) (r : Lean.Expr),
    Sparkle.Compiler.Elab.machLiftScalarN senv dom vars e = some (w, r) →
      ∃ fuel, Tools.Prototype.LiftScalarModelLetOk.liftN senv dom vars fuel e = some (w, r)

def ExpRootFloatAgreesDef : Prop :=
  ∀ (e : Lean.Expr), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    Sparkle.Compiler.MachRawSurface.rootFloat e = Tools.ShippingLetsReaderInv.rootFloatS e

def ExpLiftAgreesDef : Prop :=
  ∀ (e : Lean.Expr), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    e.liftLooseBVars 0 1 = Tools.ShippingLetsReaderInv.liftSpec e 0 1 ∧
      e.liftLooseBVars 1 1 = Tools.ShippingLetsReaderInv.liftSpec e 1 1

-- the compiler definitions are total and have the old types
def ExpMachBoolMapTy : Type :=
  Sparkle.Compiler.Elab.StructEnv → Lean.Expr → Lean.Expr → Nat → Lean.Expr → Option Lean.Expr
def ExpMachLiftScalarNTy : Type :=
  Sparkle.Compiler.Elab.StructEnv → Lean.Expr → List (Nat × Lean.Expr) → Lean.Expr → Option (Nat × Lean.Expr)
def ExpRootFloatTy : Type := Lean.Expr → Lean.Expr

/-! ## 2. Mutants (rejected by signature / defeq of the statements; NOT semantic counterexamples) -/

-- the lifted variable list is changed (`wa` replaced by `0`)
def MutBoolMapEq_vars : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv) (dom a : Lean.Expr) (wa : Nat) (body : Lean.Expr),
    Sparkle.Compiler.Elab.machBoolMap senv dom a wa body =
      Tools.Prototype.BoolMapModelLetOk.boolMapModel
        (Sparkle.Compiler.Elab.machLiftScalarN senv dom [(0, a)]) dom body

-- the compiler's own `dom` replaced by `a` in the lift
def MutBoolMapEq_dom : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv) (dom a : Lean.Expr) (wa : Nat) (body : Lean.Expr),
    Sparkle.Compiler.Elab.machBoolMap senv dom a wa body =
      Tools.Prototype.BoolMapModelLetOk.boolMapModel
        (Sparkle.Compiler.Elab.machLiftScalarN senv a [(wa, a)]) dom body

-- the one-direction `→` (the old premise shape) in place of the equation
def MutBoolMapEq_arrow : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv) (dom a : Lean.Expr) (wa : Nat) (body r : Lean.Expr),
    Sparkle.Compiler.Elab.machBoolMap senv dom a wa body = some r →
      Tools.Prototype.BoolMapModelLetOk.boolMapModel
        (Sparkle.Compiler.Elab.machLiftScalarN senv dom [(wa, a)]) dom body = some r

-- corr for the wrong premise (the other Corr)
def MutBoolMapCorr_wrong : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv), Tools.Prototype.LiftScalarModelLetOk.LiftScalarCorr senv

-- the corr with an extra conjunct (a different statement)
def MutBoolMapCorr_extra : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv),
    Tools.Prototype.BoolMapModelLetOk.BoolMapCorr senv ∧ Tools.Prototype.LiftScalarModelLetOk.LiftScalarCorr senv

-- the fuel at 0
def MutLiftScalarCorr_fuel0 : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr)
    (w : Nat) (r : Lean.Expr),
    Sparkle.Compiler.Elab.machLiftScalarN senv dom vars e = some (w, r) →
      Tools.Prototype.LiftScalarModelLetOk.liftN senv dom vars 0 e = some (w, r)

-- the converse direction
def MutLiftScalarCorr_converse : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr)
    (w : Nat) (r : Lean.Expr),
    (∃ fuel, Tools.Prototype.LiftScalarModelLetOk.liftN senv dom vars fuel e = some (w, r)) →
      Sparkle.Compiler.Elab.machLiftScalarN senv dom vars e = some (w, r)

-- the lift on an empty variable list
def MutLiftScalarCorr_vars : Prop :=
  ∀ (senv : Sparkle.Compiler.Elab.StructEnv) (dom : Lean.Expr) (e : Lean.Expr) (w : Nat) (r : Lean.Expr),
    Sparkle.Compiler.Elab.machLiftScalarN senv dom [] e = some (w, r) →
      ∃ fuel, Tools.Prototype.LiftScalarModelLetOk.liftN senv dom [] fuel e = some (w, r)

-- rootFloat agrees without its `LiftAgrees` premise
def MutRootFloatAgrees_noPremise : Prop := Tools.ShippingLetsReaderInv.RootFloatAgrees

-- rootFloat agrees with the identity
def MutRootFloatAgrees_id : Prop :=
  ∀ (hl : Tools.ShippingLetsReaderInv.LiftAgrees), ∀ (e : Lean.Expr), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    Sparkle.Compiler.MachRawSurface.rootFloat e = e

-- premise `LiftAgrees` replaced by the N3 extern one
def MutRootFloatAgrees_wrongPremise : Prop :=
  ∀ (hl : Tools.Assume.N3Extern.LiftAgrees0), Tools.ShippingLetsReaderInv.RootFloatAgrees

/-! ## 3. Closure allow-list -/

/-- Every constant occurring in the statement of `n` must be in `allowed` (an unknown name fails). -/
def checkClosure (n : Name) (allowed : List Name) : MetaM Unit := do
  let t ← stmtOf n
  let cs := t.getUsedConstants
  for c in cs do
    unless allowed.contains c do
      throwError "PTOT CLOSURE FAILED {n}: unknown constant {c}"
  logInfo m!"PTOT CLOSURE OK {n}"

def allowedNames : List Name :=
  [``Nat, ``Option, ``Option.some, ``Eq, ``Lean.Expr, ``List, ``List.cons, ``List.nil, ``Prod, ``Prod.mk,
   ``Exists, ``And, ``Bool, ``Bool.true, ``OfNat.ofNat, ``instOfNatNat,
   ``Sparkle.Compiler.Elab.StructEnv, ``Sparkle.Compiler.Elab.machBoolMap, ``Sparkle.Compiler.Elab.machLiftScalarN,
   ``Sparkle.Compiler.MachRawSurface.rootFloat,
   ``Tools.Prototype.BoolMapModelLetOk.boolMapModel, ``Tools.Prototype.BoolMapModelLetOk.BoolMapCorr,
   ``Tools.Prototype.LiftScalarModelLetOk.liftN, ``Tools.Prototype.LiftScalarModelLetOk.LiftScalarCorr,
   ``Tools.ShippingLetsReaderInv.LetOk, ``Tools.ShippingLetsReaderInv.liftSpec,
   ``Tools.ShippingLetsReaderInv.rootFloatS, ``Tools.ShippingLetsReaderInv.LiftAgrees,
   ``Tools.ShippingLetsReaderInv.RootFloatAgrees, ``Lean.Expr.liftLooseBVars]

/-- Axioms: standard ones accepted; `sorryAx` only logged when `lenient`; anything else throws. -/
def reportAxioms (n : Name) (lenient : Bool) : MetaM Bool := do
  let ax ← Lean.collectAxioms n
  let mut sorry? := false
  for a in ax do
    if a == ``sorryAx && lenient then sorry? := true
    else unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "PTOT CHECK FAILED {n}: uses the axiom {a}"
  logInfo m!"PTOT AXIOMS {n}: {ax}"
  return sorry?

/-- A compiler definition is a total `def` (not `opaque`, not `partial`) with the expected type. -/
def checkTotalDef (n tyName : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  match ci with
  | .defnInfo d =>
    if d.safety != .safe then throwError "PTOT CHECK FAILED {n}: not a safe def"
    let ty ← stmtOf tyName
    unless (← withReducible (isDefEq d.type ty)) do
      throwError "PTOT CHECK FAILED {n}: type{indentExpr d.type}\nexpected{indentExpr ty}"
    logInfo m!"PTOT TOTAL DEF OK {n}"
  | _ => throwError "PTOT CHECK FAILED {n}: not a definition (a `partial def` is an opaque constant)"

/-! ## 4. Run -/

run_meta do
  let P := `Tools.PartialTotal.Agree
  let B := `Tools.Prototype.BoolMapModelLetOk
  let L := `Tools.Prototype.LiftScalarModelLetOk
  let S := `Tools.ShippingLetsReaderInv
  let types : List (Name × Name) :=
    [(P ++ `boolMap_eq, ``ExpBoolMapEq), (P ++ `boolMapCorr, ``ExpBoolMapCorr),
     (P ++ `liftScalarCorr, ``ExpLiftScalarCorr), (P ++ `rootFloatAgrees, ``ExpRootFloatAgrees),
     (B ++ `BoolMapCorr, ``ExpBoolMapCorrDef), (L ++ `LiftScalarCorr, ``ExpLiftScalarCorrDef),
     (S ++ `RootFloatAgrees, ``ExpRootFloatAgreesDef), (S ++ `LiftAgrees, ``ExpLiftAgreesDef)]
  let mut nT : Nat := 0
  for (t, e) in types do
    withReducible (checkExpected t e)
    nT := nT + 1
  -- the compiler definitions are total
  let defs : List (Name × Name) :=
    [(`Sparkle.Compiler.Elab.machBoolMap, ``ExpMachBoolMapTy), (`Sparkle.Compiler.Elab.machLiftScalarN, ``ExpMachLiftScalarNTy),
     (`Sparkle.Compiler.MachRawSurface.rootFloat, ``ExpRootFloatTy)]
  let mut nD : Nat := 0
  for (d, ty) in defs do
    checkTotalDef d ty
    nD := nD + 1
  -- negative control for the comparator
  let mutants : List (Name × Name) :=
    [(P ++ `boolMap_eq, ``MutBoolMapEq_vars), (P ++ `boolMap_eq, ``MutBoolMapEq_dom),
     (P ++ `boolMap_eq, ``MutBoolMapEq_arrow), (P ++ `boolMapCorr, ``MutBoolMapCorr_wrong),
     (P ++ `boolMapCorr, ``MutBoolMapCorr_extra),
     (P ++ `liftScalarCorr, ``MutLiftScalarCorr_fuel0), (P ++ `liftScalarCorr, ``MutLiftScalarCorr_converse),
     (P ++ `liftScalarCorr, ``MutLiftScalarCorr_vars),
     (P ++ `rootFloatAgrees, ``MutRootFloatAgrees_noPremise), (P ++ `rootFloatAgrees, ``MutRootFloatAgrees_id),
     (P ++ `rootFloatAgrees, ``MutRootFloatAgrees_wrongPremise)]
  let mut nM : Nat := 0
  for (t, m) in mutants do
    withReducible (checkMutant t m)
    nM := nM + 1
  -- closure
  for (t, _) in types do
    checkClosure t allowedNames
  let failed ← withoutModifyingState do
    try
      checkClosure (P ++ `rootFloatAgrees) (allowedNames.erase ``Tools.ShippingLetsReaderInv.LiftAgrees)
      pure false
    catch _ => pure true
  unless failed do throwError "PTOT CLOSURE negative control: an unknown name was accepted"
  logInfo m!"PTOT CLOSURE negative control OK (unknown name rejected)"
  -- axioms (skeleton: sorryAx is logged for the four roots, not thrown; the compiler definitions must be standard-only)
  let mut sorries : Nat := 0
  for t in [P ++ `boolMap_eq, P ++ `boolMapCorr, P ++ `liftScalarCorr, P ++ `rootFloatAgrees] do
    if (← reportAxioms t true) then sorries := sorries + 1
  for (d, _) in defs do
    discard <| reportAxioms d false
  logInfo m!"PTOT SORRY-DEPENDENT ROOTS: {sorries} (skeleton: expected 4; 0 after the candidate)"
  logInfo m!"PTOT COUNTS: TYPE {nT} / TOTALDEF {nD} / MUTANT {nM}"
  logInfo m!"PTOT NOTE: mutants are rejections by signature/defeq of statements, not semantic counterexamples."

end Tests.Gen3.PartialTotalCheck
