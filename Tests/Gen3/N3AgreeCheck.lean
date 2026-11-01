import Tools.ShippingN3ExternAgree
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT: C1 skeleton check (the roots still carry `sorry`; the axiom report below logs `sorryAx` instead of throwing).

/-! # N3 extern agreement checks (scripts/gen3/N3_EXTERN_MIN.md rev2 §3.4.2)

1. **Expected types.** Every root and every premise/range definition of `Tools/ShippingN3ExternAgree.lean` is compared
   MECHANICALLY (`Tests.Gen3.ExpectedType.checkExpected`, run under `withReducible`) against an independent `Exp…`
   statement written below from the §3.4.2 text. The SAME comparator is used for the negative controls.
2. **Mutants** (equality-version mutants of the premises and of the derivations): each must be REJECTED by the same
   comparator. These are rejections by signature / (reducible) defeq of the statements; they are NOT semantic
   counterexamples and say nothing about whether the premises match the C++ behaviour.
3. **Closure.** The constants occurring in each statement must all be in an explicit allow-list; an unknown name FAILS
   (a negative control with a name removed from the list checks that the closure test can fail).
4. **Axioms.** The report logs the axioms of every root. Standard axioms are accepted; `sorryAx` is only LOGGED (skeleton),
   any other axiom throws. -/

namespace Tests.Gen3.N3AgreeCheck
open Lean Meta
open Tests.Gen3.ExpectedType

/-! ## 1. Expected statements (independent text) -/

def ExpLiftAgrees0 : Prop :=
  ∀ (e : Lean.Expr) (d : Nat), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    e.liftLooseBVars 0 d = Tools.ShippingLetsReaderInv.liftSpec e 0 d

def ExpLowerAgreesEq : Prop :=
  ∀ (e : Lean.Expr) (i : Nat), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    e.lowerLooseBVars i i = Tools.Assume.N3Extern.lowerSpec e i i

def ExpZeroLitAgrees0 : Prop :=
  ∀ (e : Lean.Expr), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    Sparkle.Compiler.MachRawSurface.zeroLit Sparkle.Compiler.Elab.inlNatLit Sparkle.Compiler.Elab.canonicalNatLitValue? e =
      e.replaceNoCache Tools.Assume.N3Extern.zeroLitF

def ExpLiftLooseRange0 : Prop :=
  ∀ (e : Lean.Expr) (d : Nat), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    Tools.ShippingLetsReaderInv.LetOk 0 (e.liftLooseBVars 0 d) = true

def ExpLowerLooseRangeEq : Prop :=
  ∀ (e : Lean.Expr) (i : Nat), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    Tools.ShippingLetsReaderInv.LetOk 0 (e.lowerLooseBVars i i) = true

def ExpZeroLitRange0 : Prop :=
  ∀ (e : Lean.Expr), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    Tools.ShippingLetsReaderInv.LetOk 0
      (Sparkle.Compiler.MachRawSurface.zeroLit Sparkle.Compiler.Elab.inlNatLit Sparkle.Compiler.Elab.canonicalNatLitValue? e) = true

def ExpLowerGoOk : Prop :=
  ∀ (n : Nat) (e : Lean.Expr) (s d : Nat), Tools.ShippingLetsReaderInv.LetOk n e = true →
    Tools.ShippingLetsReaderInv.LetOk n (Tools.Assume.N3Extern.lowerGo e s d) = true

def ExpLowerSpecOk : Prop :=
  ∀ (n : Nat) (e : Lean.Expr) (s d : Nat), Tools.ShippingLetsReaderInv.LetOk n e = true →
    Tools.ShippingLetsReaderInv.LetOk n (Tools.Assume.N3Extern.lowerSpec e s d) = true

def ExpR1 : Prop :=
  ∀ (h : Tools.Assume.N3Extern.LiftAgrees0), Tools.ShippingN3ExternAgree.LiftLooseRange0

def ExpR2 : Prop :=
  ∀ (h : Tools.Assume.N3Extern.LowerAgreesEq), Tools.ShippingN3ExternAgree.LowerLooseRangeEq

def ExpR3 : Prop :=
  ∀ (h : Tools.Assume.N3Extern.ZeroLitAgrees0), Tools.ShippingN3ExternAgree.ZeroLitRange0

def ExpRawNodeOkOfAgrees : Prop :=
  ∀ (hl : Tools.Assume.N3Extern.LiftAgrees0) (hlo : Tools.Assume.N3Extern.LowerAgreesEq)
    (hb : Tools.Prototype.RawNodeRangeLetOk.BetaRange) (pm : Lean.Name → Option Nat) (e e' : Lean.Expr),
    Tools.ShippingLetsReaderInv.LetOk 0 e = true → Sparkle.Compiler.MachRawSurface.rawNode pm e = some e' →
      Tools.ShippingLetsReaderInv.LetOk 0 e' = true

/-! ## 2. Mutants (rejected by signature / defeq of the statements; NOT semantic counterexamples) -/

-- equality version: premise on `LetOk 1` instead of `LetOk 0`
def MutLiftAgrees0_LetOk1 : Prop :=
  ∀ (e : Lean.Expr) (d : Nat), Tools.ShippingLetsReaderInv.LetOk 1 e = true →
    e.liftLooseBVars 0 d = Tools.ShippingLetsReaderInv.liftSpec e 0 d

-- equality version: lift at s = 1
def MutLiftAgrees0_s1 : Prop :=
  ∀ (e : Lean.Expr) (d : Nat), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    e.liftLooseBVars 1 d = Tools.ShippingLetsReaderInv.liftSpec e 1 d

-- equality version: lower i j with i ≠ j (an extra independent offset)
def MutLowerAgreesEq_ij : Prop :=
  ∀ (e : Lean.Expr) (i j : Nat), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    e.lowerLooseBVars i j = Tools.Assume.N3Extern.lowerSpec e i j

-- equality version: premise on `LetOk 1`
def MutLowerAgreesEq_LetOk1 : Prop :=
  ∀ (e : Lean.Expr) (i : Nat), Tools.ShippingLetsReaderInv.LetOk 1 e = true →
    e.lowerLooseBVars i i = Tools.Assume.N3Extern.lowerSpec e i i

-- equality version: right-hand side is liftSpec (wrong model)
def MutLowerAgreesEq_liftRhs : Prop :=
  ∀ (e : Lean.Expr) (i : Nat), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    e.lowerLooseBVars i i = Tools.ShippingLetsReaderInv.liftSpec e i i

-- equality version: zeroLit premise without the domain restriction
def MutZeroLitAgrees0_noDomain : Prop :=
  ∀ (e : Lean.Expr),
    Sparkle.Compiler.MachRawSurface.zeroLit Sparkle.Compiler.Elab.inlNatLit Sparkle.Compiler.Elab.canonicalNatLitValue? e =
      e.replaceNoCache Tools.Assume.N3Extern.zeroLitF

-- derivation reversed: range gives the equality
def MutR1_reversed : Prop :=
  ∀ (h : Tools.ShippingN3ExternAgree.LiftLooseRange0), Tools.Assume.N3Extern.LiftAgrees0

-- derivation from the wrong premise
def MutR2_fromLift : Prop :=
  ∀ (h : Tools.Assume.N3Extern.LiftAgrees0), Tools.ShippingN3ExternAgree.LowerLooseRangeEq

-- connection theorem keeping the range premise (the thing it is supposed to replace)
def MutRawNodeOkOfAgrees_keepsRange : Prop :=
  ∀ (hl : Tools.Prototype.RawNodeRangeLetOk.LiftLooseRange) (hlo : Tools.Assume.N3Extern.LowerAgreesEq)
    (hb : Tools.Prototype.RawNodeRangeLetOk.BetaRange) (pm : Lean.Name → Option Nat) (e e' : Lean.Expr),
    Tools.ShippingLetsReaderInv.LetOk 0 e = true → Sparkle.Compiler.MachRawSurface.rawNode pm e = some e' →
      Tools.ShippingLetsReaderInv.LetOk 0 e' = true

-- connection theorem with BetaRange dropped
def MutRawNodeOkOfAgrees_noBeta : Prop :=
  ∀ (hl : Tools.Assume.N3Extern.LiftAgrees0) (hlo : Tools.Assume.N3Extern.LowerAgreesEq)
    (pm : Lean.Name → Option Nat) (e e' : Lean.Expr),
    Tools.ShippingLetsReaderInv.LetOk 0 e = true → Sparkle.Compiler.MachRawSurface.rawNode pm e = some e' →
      Tools.ShippingLetsReaderInv.LetOk 0 e' = true

-- conclusion weakened to `LetOk 1`... on the output
def MutRawNodeOkOfAgrees_concl : Prop :=
  ∀ (hl : Tools.Assume.N3Extern.LiftAgrees0) (hlo : Tools.Assume.N3Extern.LowerAgreesEq)
    (hb : Tools.Prototype.RawNodeRangeLetOk.BetaRange) (pm : Lean.Name → Option Nat) (e e' : Lean.Expr),
    Tools.ShippingLetsReaderInv.LetOk 0 e = true → Sparkle.Compiler.MachRawSurface.rawNode pm e = some e' →
      Tools.ShippingLetsReaderInv.LetOk 1 e' = true

-- lowerSpec_ok at a fixed n
def MutLowerSpecOk_n0 : Prop :=
  ∀ (e : Lean.Expr) (s d : Nat), Tools.ShippingLetsReaderInv.LetOk 0 e = true →
    Tools.ShippingLetsReaderInv.LetOk 0 (Tools.Assume.N3Extern.lowerSpec e s d) = true

/-! ## 3. Closure allow-list -/

/-- Every constant occurring in the statement of `n` must be in `allowed` (an unknown name fails). -/
def checkClosure (n : Name) (allowed : List Name) : MetaM Unit := do
  let t ← stmtOf n
  let cs := t.getUsedConstants
  for c in cs do
    unless allowed.contains c do
      throwError "N3AGREE CLOSURE FAILED {n}: unknown constant {c}"
  logInfo m!"N3AGREE CLOSURE OK {n}"

def allowedNames : List Name :=
  [``Nat, ``Bool, ``Bool.true, ``Option, ``Option.some, ``Eq, ``Lean.Expr, ``Lean.Name,
   ``OfNat.ofNat, ``instOfNatNat, ``instOfNat, ``Lean.Expr.liftLooseBVars, ``Lean.Expr.lowerLooseBVars,
   ``Lean.Expr.replaceNoCache, ``Tools.ShippingLetsReaderInv.LetOk, ``Tools.ShippingLetsReaderInv.liftSpec,
   ``Tools.Assume.N3Extern.lowerSpec, ``Tools.Assume.N3Extern.lowerGo,
   ``Tools.Assume.N3Extern.zeroLitF, ``Tools.Assume.N3Extern.LiftAgrees0,
   ``Tools.Assume.N3Extern.LowerAgreesEq, ``Tools.Assume.N3Extern.ZeroLitAgrees0,
   ``Tools.ShippingN3ExternAgree.LiftLooseRange0, ``Tools.ShippingN3ExternAgree.LowerLooseRangeEq,
   ``Tools.ShippingN3ExternAgree.ZeroLitRange0, ``Tools.Prototype.RawNodeRangeLetOk.BetaRange,
   ``Sparkle.Compiler.MachRawSurface.zeroLit, ``Sparkle.Compiler.MachRawSurface.rawNode,
   ``Sparkle.Compiler.Elab.inlNatLit, ``Sparkle.Compiler.Elab.canonicalNatLitValue?]

/-- Axioms: standard ones accepted; `sorryAx` only logged (skeleton); anything else throws. -/
def reportAxioms (n : Name) : MetaM Bool := do
  let ax ← Lean.collectAxioms n
  let mut sorry? := false
  for a in ax do
    if a == ``sorryAx then sorry? := true
    else unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "N3AGREE CHECK FAILED {n}: uses the axiom {a}"
  logInfo m!"N3AGREE AXIOMS {n}: {ax}"
  return sorry?

/-! ## 4. Run -/

run_meta do
  let N := `Tools.ShippingN3ExternAgree
  let A := `Tools.Assume.N3Extern
  let types : List (Name × Name) :=
    [(A ++ `LiftAgrees0, ``ExpLiftAgrees0), (A ++ `LowerAgreesEq, ``ExpLowerAgreesEq),
     (A ++ `ZeroLitAgrees0, ``ExpZeroLitAgrees0), (N ++ `LiftLooseRange0, ``ExpLiftLooseRange0),
     (N ++ `LowerLooseRangeEq, ``ExpLowerLooseRangeEq), (N ++ `ZeroLitRange0, ``ExpZeroLitRange0),
     (N ++ `lowerGo_ok, ``ExpLowerGoOk), (N ++ `lowerSpec_ok, ``ExpLowerSpecOk),
     (N ++ `r1, ``ExpR1), (N ++ `r2, ``ExpR2), (N ++ `r3, ``ExpR3),
     (N ++ `rawNode_ok_of_agrees, ``ExpRawNodeOkOfAgrees)]
  let mut nT : Nat := 0
  for (t, e) in types do
    withReducible (checkExpected t e)
    nT := nT + 1
  -- negative control for the comparator: an expected statement against a different expected statement must fail
  let mutants : List (Name × Name) :=
    [(A ++ `LiftAgrees0, ``MutLiftAgrees0_LetOk1), (A ++ `LiftAgrees0, ``MutLiftAgrees0_s1),
     (A ++ `LowerAgreesEq, ``MutLowerAgreesEq_ij), (A ++ `LowerAgreesEq, ``MutLowerAgreesEq_LetOk1),
     (A ++ `LowerAgreesEq, ``MutLowerAgreesEq_liftRhs), (A ++ `ZeroLitAgrees0, ``MutZeroLitAgrees0_noDomain),
     (N ++ `r1, ``MutR1_reversed), (N ++ `r2, ``MutR2_fromLift),
     (N ++ `rawNode_ok_of_agrees, ``MutRawNodeOkOfAgrees_keepsRange),
     (N ++ `rawNode_ok_of_agrees, ``MutRawNodeOkOfAgrees_noBeta),
     (N ++ `rawNode_ok_of_agrees, ``MutRawNodeOkOfAgrees_concl),
     (N ++ `lowerSpec_ok, ``MutLowerSpecOk_n0)]
  let mut nM : Nat := 0
  for (t, m) in mutants do
    withReducible (checkMutant t m)
    nM := nM + 1
  -- closure: all statements stay inside the allow-list; a name removed from the list must make it fail
  for (t, _) in types do
    checkClosure t allowedNames
  let failed ← withoutModifyingState do
    try
      checkClosure (N ++ `r1) (allowedNames.erase (A ++ `LiftAgrees0))
      pure false
    catch _ => pure true
  unless failed do throwError "N3AGREE CLOSURE negative control: an unknown name was accepted"
  logInfo m!"N3AGREE CLOSURE negative control OK (unknown name rejected)"
  -- axioms (skeleton: sorryAx is logged, not thrown)
  let mut sorries : Nat := 0
  for (t, _) in types do
    if (← reportAxioms t) then sorries := sorries + 1
  logInfo m!"N3AGREE SORRY-DEPENDENT ROOTS: {sorries} (skeleton: expected 6 theorems: lowerGo_ok, lowerSpec_ok, r1, r2, r3, rawNode_ok_of_agrees; 0 after the candidate)"
  -- which assumption of Tools/Assume each root's statement takes (by name; the module holds only these three)
  let assumes : List Name := [A ++ `LiftAgrees0, A ++ `LowerAgreesEq, A ++ `ZeroLitAgrees0]
  for (t, _) in types do
    let cs := (← stmtOf t).getUsedConstants
    logInfo m!"N3AGREE ASSUME-DEPS {t}: {assumes.filter cs.contains}"
  logInfo m!"N3AGREE COUNTS: TYPE {nT} / MUTANT {nM}"
  logInfo m!"N3AGREE NOTE: mutants are rejections by signature/defeq of statements, not semantic counterexamples."

end Tests.Gen3.N3AgreeCheck
