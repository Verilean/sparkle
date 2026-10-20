import Tools.ShippingChildVertA
import Tools.ShippingChildPathA

/-! # Audit: the vertical path does not use the old boundary (round par/vert)

BUILT by the integrator: vt3 exit 0 (audit passed: no RefLaws / RefLawsCore / toAOps / toA in the closures; axioms standard) (round par/vert, base 777630e9); revised round par/audit2 (opaque bodies read, boundary report, hidden-wrapper controls). Registered in `Tests.AllTests` (all9).

For each audited theorem of the vertical migration
(`Tools/ShippingChildVertA.lean`, `Tools/ShippingChildVCA.lean`,
`Tools/ShippingChildFresh.lean`) this file:

* prints its axioms (`#print axioms`) and THROWS unless they are standard;
* walks the TRANSITIVE closure of the constants its type and value mention
  (a worklist over `ConstantInfo.type` / `ConstantInfo.value? (allowOpaque := true)`
  with a visited set; inductive types also contribute their constructors' types)
  and THROWS if the closure contains `Tools.ShippingChildInv.RefLaws` (or any
  constant under that name, e.g. its fields), `Tools.ShippingChildBndCore.RefLawsCore`
  (or under it), `Tools.ShippingChildInvA.RefLawsCore.toAOps` or
  `Tools.ShippingChildInvA.RefLawsCore.toA`.

**What the walk reads, and its boundary.** `value? (allowOpaque := true)` reads
the bodies of definitions, theorems AND `opaque` constants (the default
`value?` skips `opaque` bodies; the first version of this file used the default,
so a body hidden behind `opaque` was not read — control (c) below). What it
CANNOT read, and REPORTS per theorem (`boundary`): axioms (here only the
standard ones, checked), `opaque` constants whose stored value is the default
inhabitant (e.g. `@[extern]` primitives such as `ST.Prim.Ref.get`: the stored
value is not the runtime behaviour), constants with `@[extern]`, and
`@[implemented_by]` targets (the compiled code is NOT part of the kernel term;
the walk follows the logical value of the attributed constant, not the
implementation; the implementation names are listed). Inductives, constructors,
recursors and quotients have no body to read. In this project the
opaque constants of the closures are `partial def`s (e.g. `machNorm`,
`stripMemoizeWrappers`: the kernel sees an opaque constant, not the recursive
code) and the `initialize` refs (`sparkleSynthDepth`, …); they are logged as
`PROJECT OPAQUE`. So "the closure contains no old
boundary" is a statement about the KERNEL terms; it says nothing about what the
extern / implemented_by code does at runtime (that is the runtime-fit item).

Positive controls (each THROWS if the walker misses it):
(a) the closure of `Tools.ShippingChildInvA.RefLawsCore.toAOps` contains
    `Tools.ShippingChildBndCore.RefLawsCore`;
(b) a theorem whose TYPE mentions only a local wrapper definition whose VALUE
    mentions `RefLawsCore` (`hiddenWrap`) is flagged;
(c) a theorem whose PROOF mentions only a local `opaque` constant whose stored
    value mentions `RefLawsCore` (`hiddenOpaque`) is flagged — and the default
    `value?` walk (opaque bodies skipped) does NOT flag it (logged: the gap the
    revision closes).

Writing-time guesses: `Expr.getUsedConstants` (Lean core) returns the
constants of an expression; `InductiveVal.ctors`; `Name.isPrefixOf`;
`Lean.isExtern`; `Lean.Compiler.implementedByAttr.getParam?`. -/

namespace Tests.Compiler.ChildVertAuditTest
open Lean Meta

/-- Standard axioms only, an error otherwise. -/
def stdAxioms (n : Name) : MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

/-- The transitive closure of the constants `n` depends on (type, value —
opaque bodies included when `readOpaque := true` — constructors of inductives),
`n` included. -/
partial def depClosureWith (readOpaque : Bool) (n : Name) : MetaM NameSet := do
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
      if let some v := ci.value? (allowOpaque := readOpaque) then
        used := used ++ v.getUsedConstants
      if let .inductInfo iv := ci then
        used := used ++ iv.ctors.toArray
      for u in used do
        unless seen.contains u do
          todo := todo.push u
  return seen

def depClosure (n : Name) : MetaM NameSet := depClosureWith true n

/-- The constants of a closure whose behaviour the walk cannot read from a
kernel body: axioms, `opaque` constants, `@[extern]` constants, and
`@[implemented_by]`-attributed constants (with their implementation names). -/
def boundary (s : NameSet) : MetaM (List Name × List Name × List Name × List (Name × Name)) := do
  let env ← getEnv
  let mut axs : List Name := []
  let mut ops : List Name := []
  let mut exts : List Name := []
  let mut impls : List (Name × Name) := []
  for c in s.toList do
    match env.find? c with
    | some (.axiomInfo _) => axs := c :: axs
    | some (.opaqueInfo _) => ops := c :: ops
    | _ => pure ()
    if Lean.isExtern env c then exts := c :: exts
    if let some i := Lean.Compiler.implementedByAttr.getParam? env c then impls := (c, i) :: impls
  return (axs, ops, exts, impls)

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
   ``Tools.ShippingChildFresh.runsTo_mkRef_bind, ``Tools.ShippingChildFresh.runsTo_mkRefIO_bind,
   ``Tools.ShippingChildPathA.certRest_keepsA, ``Tools.ShippingChildPathA.emitLeavesA,
   ``Tools.ShippingChildPathA.bindCertifiedInputsA, ``Tools.ShippingChildPathA.finishSynthA,
   ``Tools.ShippingChildPathA.certified_keepsA_of_translate,
   ``Tools.ShippingChildPathA.fromConst_certified_keepsA,
   ``Tools.ShippingChildPathA.fromConst_certified_keepsJQ,
   ``Tools.ShippingChildPathA.fromConst_certified_hbody]

end Tests.Compiler.ChildVertAuditTest

open Tests.Compiler.ChildVertAuditTest

#print axioms Tools.ShippingChildVertA.core_tripleA
#print axioms Tools.ShippingChildVertA.certified_keepsA

/-! ## Controls (b) and (c): the old boundary hidden behind a wrapper -/

namespace Tests.Compiler.ChildVertAuditTest.Hidden

/-- A wrapper whose VALUE (not its type) mentions the old bundle. -/
def hiddenWrap : Prop :=
  ∀ (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State),
    Nonempty (Tools.ShippingChildBndCore.RefLawsCore mref cref)

theorem usesWrap : hiddenWrap → True := fun _ => trivial

/-- An `opaque` constant whose stored value mentions the old bundle. -/
opaque hiddenOpaque : Prop :=
  ∀ (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State),
    Nonempty (Tools.ShippingChildBndCore.RefLawsCore mref cref)

theorem usesOpaque : True := (fun (_ : hiddenOpaque → True) => trivial) (fun _ => trivial)

end Tests.Compiler.ChildVertAuditTest.Hidden

open Lean Elab Command in
run_cmd liftTermElabM do
  -- (a) the walker sees the old bundle where it IS used
  let ctl ← depClosure ``Tools.ShippingChildInvA.RefLawsCore.toAOps
  unless ctl.contains ``Tools.ShippingChildBndCore.RefLawsCore do
    throwError "VERT AUDIT FAILED: walker broken (toAOps closure lacks RefLawsCore)"
  -- (b) through a wrapper's value
  let cb ← depClosure ``Tests.Compiler.ChildVertAuditTest.Hidden.usesWrap
  if (hits cb).isEmpty then
    throwError "VERT AUDIT FAILED: control (b) not flagged (wrapper value not followed)"
  -- (c) through an opaque body
  let cc ← depClosure ``Tests.Compiler.ChildVertAuditTest.Hidden.usesOpaque
  if (hits cc).isEmpty then
    throwError "VERT AUDIT FAILED: control (c) not flagged (opaque body not read)"
  let ccOld ← depClosureWith false ``Tests.Compiler.ChildVertAuditTest.Hidden.usesOpaque
  logInfo m!"VERT AUDIT CONTROLS: (a) ok; (b) flagged {hits cb}; (c) flagged {hits cc}; (c) with opaque bodies skipped (the first version's walk) flags {hits ccOld}"
  for n in audited do
    stdAxioms n
    let s ← depClosure n
    let hs := hits s
    unless hs.isEmpty do
      throwError "VERT AUDIT FAILED: {n} depends on the old boundary: {hs}"
    let (axs, ops, exts, impls) ← boundary s
    let proj := ops.filter fun c => (`Sparkle).isPrefixOf c || (`Tools).isPrefixOf c
    logInfo m!"{n}: PROJECT OPAQUE {proj.length} (`partial def`s and `initialize` refs: kernel body not the code): {proj}"
    logInfo m!"{n}: closure {s.size} constants (opaque bodies read), no RefLaws / RefLawsCore / toAOps / toA. BOUNDARY (not readable as kernel behaviour): axioms {axs}; opaque {ops.length}: {ops}; extern {exts.length}: {exts}; implemented_by {impls.length}: {impls}"
