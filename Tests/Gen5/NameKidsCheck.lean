import Tools.ShippingGen5NameKids
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Last clean issue-linked build: ba2v-d68b0f47 (exit 0, 500 jobs) of d68b0f47, i.e. the version of this file BEFORE the R1/R2 closure-control rewrite below; its counts were: TYPE 6 (5 theorems + 1 comparator sanity), MUTANT 10 (8 single-point + 2 cross-statement), use-site examples 2, closure controls negative 6 + clean 1, REACH 5 (one per theorem), AXIOMS 5 (one per theorem). Counts are per run_cmd/logInfo line of each class. THIS version (R1/R2): Pod build exit 0, 500 jobs, of 454bce14 (not a clean issue-linked build): closure controls negative 8 + clean 1 (each asserts the intended hit/unknown path), other counts unchanged.
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U1 checks

Every `Exp…` statement below is written from the Lean text of freeze §1.3, not from the implementation's signature; the
implementation file is imported only so the theorem NAMES resolve. ONE comparator (`cmpTeleR`, names with macro scopes
erased, binder info, types by `==` with a REDUCIBLE `isDefEq` fallback) is used for the positive controls and for the mutants.
Mutants are single-point, well-typed variants of an Expected statement; a rejection is by signature / defeq of a changed
statement, NOT a semantic counterexample.
Closure: the walker visits the value and the type of every constant reachable from a root, over ALL namespaces
(project and Lean core; no namespace is excluded, so there is no unexplored boundary other than the 3,000,000-visit cap, which throws);
a name the resolver cannot resolve is counted and the audit throws. -/

namespace Tests.Gen5.NameKidsFixture
theorem helperV : True := (fun _ => trivial) @Lean.ofReduceBool
theorem helperTy : @Lean.ofReduceBool = @Lean.ofReduceBool := rfl
-- `auxT` occurs only in the TYPE of `helperTyU` (the checker replaces `helperTyU` by an axiom, dropping its value)
-- `helperTy` is the same kind of helper for the forbidden-constant case
def auxT : Nat := 0
theorem helperTyU : auxT = auxT := rfl
-- NB: an elaborated application such as `(fun _ => trivial) @helperTy` copies the helper's type into the root's own value, so type-only
-- reachability cannot be built from the elaborated fixtures; the checker synthesizes the roots below (`synthRoot`) instead.
-- `badRoot` is an EDGE test (a non-forbidden theorem whose value uses a forbidden constant); it does not test a forbidden root itself
theorem badRoot : True := (fun _ => trivial) @Lean.ofReduceBool
theorem badViaValue : True := helperV
theorem cleanRoot : True := (fun _ => trivial) @Tools.ShippingModuleName.ofDecl_injective
end Tests.Gen5.NameKidsFixture

namespace Tests.Gen5.NameKidsCheck
open Lean Meta
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingSrm7Rank (kidModName)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGen5NameKids
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)

/-! ## 1. Independent Expected statements (from freeze §1.3 text) -/
def ExpOfDeclNeOfMem : Prop := ∀ (n : Name) (c : Bool) (a d : Nat), ofDecl n ≠ ofMem c a d

def ExpInjNonmem : Prop :=
  ∀ {c c' : Name} {o o' : InstOrigin}
    (h : memKey o = none) (h' : memKey o' = none)
    (e : kidModName (c, o) = kidModName (c', o')), c = c'
def ExpNeMem : Prop :=
  ∀ {c c' : Name} {o o' : InstOrigin} (h : memKey o = none) (h' : memKey o' ≠ none),
    kidModName (c, o) ≠ kidModName (c', o')
def ExpInjMem : Prop :=
  ∀ {c c' : Name} {o o' : InstOrigin} {k k' : Bool × Nat × Nat}
    (h : memKey o = some k) (h' : memKey o' = some k')
    (e : kidModName (c, o) = kidModName (c', o')), k = k'
def ExpHsep : Prop :=
  ∀ {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hmemSame : ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length),
      memKey (org k) ≠ none → memKey (org k) = memKey (org k') → (insts[k]'hk).1 = (insts[k']'hk').1),
    ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length), nameK k = nameK k' →
      (insts[k]'hk).1 = (insts[k']'hk').1 ∧ memKey (org k) = memKey (org k')
def ExpHparent : Prop :=
  ∀ {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (declName : Name)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hself : ∀ (k : Nat) (hk : k < insts.length), memKey (org k) = none → (insts[k]'hk).1 ≠ declName),
    ∀ (k : Nat), k < insts.length → nameK k ≠ ofDecl declName
/-! ## 2. Mutants (single change each; rejection by signature, not a semantic counterexample) -/
def MutInjNe : Prop :=
  ∀ {c c' : Name} {o o' : InstOrigin}
    (h : memKey o = none) (h' : memKey o' = none)
    (e : kidModName (c, o) = kidModName (c', o')), c ≠ c'
def MutInjHypFlip : Prop :=
  ∀ {c c' : Name} {o o' : InstOrigin}
    (h : memKey o ≠ none) (h' : memKey o' = none)
    (e : kidModName (c, o) = kidModName (c', o')), c = c'
def MutHsepNoMemKey : Prop :=
  ∀ {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hmemSame : ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length),
      memKey (org k) ≠ none → memKey (org k) = memKey (org k') → (insts[k]'hk).1 = (insts[k']'hk').1),
    ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length), nameK k = nameK k' →
      (insts[k]'hk).1 = (insts[k']'hk').1
def MutHsepNoCallee : Prop :=
  ∀ {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hmemSame : ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length),
      memKey (org k) ≠ none → memKey (org k) = memKey (org k') → (insts[k]'hk).1 = (insts[k']'hk').1),
    ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length), nameK k = nameK k' →
      memKey (org k) = memKey (org k')
def MutHsepNoMemSame : Prop :=
  ∀ {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k)),
    ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length), nameK k = nameK k' →
      (insts[k]'hk).1 = (insts[k']'hk').1 ∧ memKey (org k) = memKey (org k')
def MutHsepNe : Prop :=
  ∀ {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hmemSame : ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length),
      memKey (org k) ≠ none → memKey (org k) = memKey (org k') → (insts[k]'hk).1 = (insts[k']'hk').1),
    ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length), nameK k ≠ nameK k' →
      (insts[k]'hk).1 = (insts[k']'hk').1 ∧ memKey (org k) = memKey (org k')
def MutHparNoSelf : Prop :=
  ∀ {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (declName : Name)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k)),
    ∀ (k : Nat), k < insts.length → nameK k ≠ ofDecl declName
def MutHparMem : Prop :=
  ∀ {β : Type} (insts : List (Name × β)) (org : Nat → InstOrigin) (nameK : Nat → String)
    (declName : Name)
    (hn : ∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k))
    (hself : ∀ (k : Nat) (hk : k < insts.length), memKey (org k) = none → (insts[k]'hk).1 ≠ declName),
    ∀ (k : Nat), k < insts.length → nameK k ≠ ofMem true 0 0

/-! ## 3. Consumer-shape use sites: the binder types of `machineClosesAtA_of_memKids'` (a type check, not a semantic claim) -/

section Use
open Tools.ShippingMachineAuto
example (d : MachineData) (nameK : Nat → String)
    (hn : ∀ (k : Nat) (hk : k < d.shape.insts.length), nameK k = kidModName ((d.shape.insts[k]'hk).1, originAt d.shape k))
    (hmemSame : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat) (hk' : k' < d.shape.insts.length),
      memKey (originAt d.shape k) ≠ none → memKey (originAt d.shape k) = memKey (originAt d.shape k') →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), nameK k = nameK k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k') :=
  hsep_of_kidNames d.shape.insts (originAt d.shape) nameK hn hmemSame
example (d : MachineData) (nameK : Nat → String) (declName : Name)
    (hn : ∀ (k : Nat) (hk : k < d.shape.insts.length), nameK k = kidModName ((d.shape.insts[k]'hk).1, originAt d.shape k))
    (hself : ∀ (k : Nat) (hk : k < d.shape.insts.length), memKey (originAt d.shape k) = none →
      (d.shape.insts[k]).1 ≠ declName) :
    ∀ (k : Nat), k < d.shape.insts.length → nameK k ≠ (Sparkle.IR.ModuleName.ofDecl declName) :=
  hparent_of_kidNames d.shape.insts (originAt d.shape) nameK declName hn hself
end Use

/-! ## 4. The single comparator -/

def cmpEqR (what : String) (a e : Lean.Expr) : MetaM Unit := do
  let a ← instantiateMVars a
  let e ← instantiateMVars e
  if a == e then return
  unless (← withReducible (isDefEq a e)) do
    throwError "NK CHECK FAILED {what}"

partial def cmpTeleR (what : String) (a e : Lean.Expr) (i : Nat := 0) : MetaM Unit := do
  match a, e with
  | .forallE na ta ba bia, .forallE ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "NK CHECK FAILED {what}: binder {i} name {na} vs {ne}"
    unless bia == bie do throwError "NK CHECK FAILED {what}: binder {i} info"
    cmpEqR s!"{what} binder {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpTeleR what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .forallE na .., _ => throwError "NK CHECK FAILED {what}: extra binder {i} ({na})"
  | _, .forallE ne .. => throwError "NK CHECK FAILED {what}: missing binder {i} ({ne})"
  | _, _ => cmpEqR s!"{what} conclusion" a e

def checkExpectedR (thm exp : Name) : MetaM Unit := do
  let a ← stmtOf thm
  let e ← stmtOf exp
  cmpTeleR s!"{thm}" a e
  logInfo m!"NK TYPE OK {thm} against {exp} (reducible comparator)"

def checkMutantR (thm mt : Name) : MetaM Unit := do
  let a ← stmtOf thm
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try
      cmpTeleR s!"{thm} vs mutant {mt}" a e
      pure true
    catch _ => pure false
  if accepted then throwError "NK MUTANT ACCEPTED: {mt} matches {thm}"
  logInfo m!"NK MUTANT REJECTED {mt} (against {thm}; same comparator)"

/-! ## 5. Positive controls, then mutants -/

run_cmd Lean.Elab.Command.liftTermElabM do
  -- comparator sanity: an existing consumer-side statement vs its own text
  checkExpectedR ``Tools.ShippingModuleName.ofDecl_ne_ofMem ``ExpOfDeclNeOfMem
  checkExpectedR ``kidModName_inj_nonmem ``ExpInjNonmem
  checkExpectedR ``kidModName_ne_mem ``ExpNeMem
  checkExpectedR ``kidModName_inj_mem ``ExpInjMem
  checkExpectedR ``hsep_of_kidNames ``ExpHsep
  checkExpectedR ``hparent_of_kidNames ``ExpHparent
  checkMutantR ``kidModName_inj_nonmem ``MutInjNe
  checkMutantR ``kidModName_inj_nonmem ``MutInjHypFlip
  checkMutantR ``hsep_of_kidNames ``MutHsepNoMemKey
  checkMutantR ``hsep_of_kidNames ``MutHsepNoCallee
  checkMutantR ``hsep_of_kidNames ``MutHsepNoMemSame
  checkMutantR ``hsep_of_kidNames ``MutHsepNe
  checkMutantR ``hparent_of_kidNames ``MutHparNoSelf
  checkMutantR ``hparent_of_kidNames ``MutHparMem
  -- cross-statement negative controls (the comparator must not equate different Expected statements)
  checkMutantR ``hsep_of_kidNames ``ExpHparent
  checkMutantR ``kidModName_inj_mem ``ExpInjNonmem

/-! ## 6. Closure audit -/

def forbidConsts : List Name := [``Lean.ofReduceBool, ``sorryAx, ``Lean.trustCompiler]

def body? : ConstantInfo → Option Lean.Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure AReach where
  hit : Option (List Name) := none
  seen : NameSet := {}
  visited : Nat := 0
  unknown : Nat := 0
  unknownFirst : Option (List Name) := none

def reachWith (resolve : Name → Option ConstantInfo) (root : Name) (cap : Nat := 3000000) : MetaM AReach := do
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "NK AUDIT INCOMPLETE at {root}"
    if forbidConsts.contains c then return { out with hit := some path }
    let some ci := resolve c | do
      out := { out with unknown := out.unknown + 1, unknownFirst := out.unknownFirst <|> some path }
      continue
    let body := body? ci
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

/-- the audit of one root: forbidden use or any unresolved name is a failure. -/
def auditRoot (resolve : Name → Option ConstantInfo) (root : Name) : MetaM AReach := do
  let r ← reachWith resolve root
  if let some p := r.hit then throwError "NK AUDIT FAILED {root}: forbidden use via {p}"
  if r.unknown != 0 then throwError "NK AUDIT FAILED {root}: {r.unknown} unresolved name(s), first via {toString r.unknownFirst}"
  return r

def failsAudit (resolve : Name → Option ConstantInfo) (root : Name) : MetaM Bool := do
  try
    let _ ← auditRoot resolve root
    pure false
  catch _ => pure true

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let F := `Tests.Gen5.NameKidsFixture
  -- negative controls; each asserts the intended path/name, not merely that the audit failed
  let expectHit := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (path : List Name) => do
    let r ← reachWith resolve root
    unless r.hit == some path do throwError "NK AUDIT CONTROL {what}: expected hit {path}, got {toString r.hit} (unknown {r.unknown})"
    unless ← failsAudit resolve root do throwError "NK AUDIT FAILED: {what} accepted"
  let expectUnknown := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (first : List Name) => do
    let r ← reachWith resolve root
    unless r.hit.isNone && r.unknown > 0 && r.unknownFirst == some first do
      throwError "NK AUDIT CONTROL {what}: expected unknown via {first}, got hit {toString r.hit}, unknown {r.unknown}, first {toString r.unknownFirst}"
    unless ← failsAudit resolve root do throwError "NK AUDIT FAILED: {what} accepted"
  -- (1) forbidden constant used by the root's value; (2) by a helper's value; (3) by a helper's TYPE only (value removed)
  expectHit "edge root->forbidden" env.find? (F ++ `badRoot) [F ++ `badRoot, ``Lean.ofReduceBool]
  expectHit "helper value" env.find? (F ++ `badViaValue) [F ++ `badViaValue, F ++ `helperV, ``Lean.ofReduceBool]
  -- synthetic roots: type `True`, value = a bare reference to the helper (so the helper is reached through the value edge only,
  -- and whatever occurs in the helper's TYPE is reachable only by walking that type). The walker is syntactic; the roots need not be well-typed.
  let asAxiom := fun (ci : ConstantInfo) => ConstantInfo.axiomInfo { name := ci.name, levelParams := ci.levelParams, type := ci.type, isUnsafe := false }
  let synthRoot := fun (root helper : Name) =>
    ConstantInfo.thmInfo { name := root, levelParams := [], type := mkConst ``True, value := mkConst helper, all := [root] }
  let SR := F ++ `synthRoot
  let tyOnly := fun n =>
    if n == SR then some (synthRoot SR (F ++ `helperTy))
    else if n == F ++ `helperTy then (env.find? n).map asAxiom
    else env.find? n
  expectHit "helper type" tyOnly SR [SR, F ++ `helperTy, ``Lean.ofReduceBool]
  -- (4) the root itself is a forbidden constant
  expectHit "forbidden root ofReduceBool" env.find? ``Lean.ofReduceBool [``Lean.ofReduceBool]
  expectHit "forbidden root sorryAx" env.find? ``sorryAx [``sorryAx]
  -- (5)-(7) unresolved names: root, helper value, and a name reachable ONLY through a helper's type
  expectUnknown "unknown root" (fun n => if n == F ++ `badRoot then none else env.find? n) (F ++ `badRoot) [F ++ `badRoot]
  expectUnknown "unknown helper value" (fun n => if n == F ++ `helperV then none else env.find? n) (F ++ `badViaValue) [F ++ `badViaValue, F ++ `helperV]
  -- helperTyU stays resolvable but is an axiom (type only); auxT, which occurs in that type alone, is unresolvable
  let tyOnlyU := fun n =>
    if n == SR then some (synthRoot SR (F ++ `helperTyU))
    else if n == F ++ `auxT then none
    else if n == F ++ `helperTyU then (env.find? n).map asAxiom
    else env.find? n
  expectUnknown "unknown name via helper type" tyOnlyU SR [SR, F ++ `helperTyU, F ++ `auxT]
  -- clean control
  let rc ← auditRoot env.find? (F ++ `cleanRoot)
  logInfo m!"NK CONTROLS closure: negative 8 (edge root->forbidden, helper value, helper type, forbidden root ofReduceBool, forbidden root sorryAx, unknown root, unknown helper value, unknown name via helper type) all rejected with the intended path; clean 1 accepted (visited {rc.visited})"
  for r in [``kidModName_inj_nonmem, ``kidModName_ne_mem, ``kidModName_inj_mem, ``hsep_of_kidNames, ``hparent_of_kidNames] do
    let a ← auditRoot env.find? r
    logInfo m!"NK REACH {r}: no ofReduceBool / sorryAx / trustCompiler, no unresolved name; visited {a.visited} constants (all namespaces)"

/-! ## 7. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``kidModName_inj_nonmem, ``kidModName_ne_mem, ``kidModName_inj_mem, ``hsep_of_kidNames, ``hparent_of_kidNames] do
    checkAxioms n

end Tests.Gen5.NameKidsCheck
