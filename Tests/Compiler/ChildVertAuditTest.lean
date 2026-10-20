import Tools.ShippingChildVertA

/-! # Audit: the vertical path does not use the old boundary (round par/vert)

BUILT by the integrator: vt3 exit 0 (audit passed: no RefLaws / RefLawsCore / toAOps / toA in the closures; axioms standard) (round par/vert, base 777630e9). Not registered in Tests/AllTests.lean.

For each audited theorem of the vertical migration
(`Tools/ShippingChildVertA.lean`, `Tools/ShippingChildVCA.lean`,
`Tools/ShippingChildFresh.lean`) this file:

* prints its axioms (`#print axioms`) and THROWS unless they are standard;
* walks the TRANSITIVE closure of the constants its type and value mention
  (a worklist over `ConstantInfo.type` / `ConstantInfo.value?` with a visited
  set; inductive types also contribute their constructors' types) and THROWS
  if the closure contains `Tools.ShippingChildInv.RefLaws` (or any constant
  under that name, e.g. its fields), `Tools.ShippingChildBndCore.RefLawsCore`
  (or under it), `Tools.ShippingChildInvA.RefLawsCore.toAOps` or
  `Tools.ShippingChildInvA.RefLawsCore.toA`.

Positive control: the closure of `Tools.ShippingChildInvA.RefLawsCore.toAOps`
MUST contain `Tools.ShippingChildBndCore.RefLawsCore` (else the walker is
broken and the file throws).

Writing-time guesses: `Expr.getUsedConstants` (Lean core) returns the
constants of an expression; `InductiveVal.ctors`; `Name.isPrefixOf`. -/

namespace Tests.Compiler.ChildVertAuditTest
open Lean Meta

/-- Standard axioms only, an error otherwise. -/
def stdAxioms (n : Name) : MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

/-- The transitive closure of the constants `n` depends on (type, value,
constructors of inductives), `n` included. -/
partial def depClosure (n : Name) : MetaM NameSet := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n]
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | none => pure ()
    | some ci =>
      let mut used := ci.type.getUsedConstants
      if let some v := ci.value? then
        used := used ++ v.getUsedConstants
      if let .inductInfo iv := ci then
        used := used ++ iv.ctors.toArray
      for u in used do
        unless seen.contains u do
          todo := todo.push u
  return seen

/-- The old-boundary names: any constant equal to or under these. -/
def forbiddenRoots : List Name :=
  [`Tools.ShippingChildInv.RefLaws, `Tools.ShippingChildBndCore.RefLawsCore,
   `Tools.ShippingChildInvA.RefLawsCore.toAOps, `Tools.ShippingChildInvA.RefLawsCore.toA]

def hits (s : NameSet) : List Name :=
  s.toList.filter fun c => forbiddenRoots.any fun r => r.isPrefixOf c

/-- The audited theorems. -/
def audited : List Name :=
  [``Tools.ShippingChildVertA.core_tripleA, ``Tools.ShippingChildVertA.certified_keepsA,
   ``Tools.ShippingChildVertA.finA,
   ``Tools.ShippingChildVCA.keepsA_mkExprCache_bind, ``Tools.ShippingChildVCA.keepsA_exprCacheGet,
   ``Tools.ShippingChildFresh.runsTo_mkRef_bind, ``Tools.ShippingChildFresh.runsTo_mkRefIO_bind]

end Tests.Compiler.ChildVertAuditTest

open Tests.Compiler.ChildVertAuditTest

#print axioms Tools.ShippingChildVertA.core_tripleA
#print axioms Tools.ShippingChildVertA.certified_keepsA

open Lean Elab Command in
run_cmd liftTermElabM do
  -- positive control: the walker sees the old bundle where it IS used
  let ctl ← depClosure ``Tools.ShippingChildInvA.RefLawsCore.toAOps
  unless ctl.contains ``Tools.ShippingChildBndCore.RefLawsCore do
    throwError "VERT AUDIT FAILED: walker broken (toAOps closure lacks RefLawsCore)"
  for n in audited do
    stdAxioms n
    let s ← depClosure n
    let hs := hits s
    unless hs.isEmpty do
      throwError "VERT AUDIT FAILED: {n} depends on the old boundary: {hs}"
    logInfo m!"{n}: closure {s.size} constants, no RefLaws / RefLawsCore / toAOps / toA"
