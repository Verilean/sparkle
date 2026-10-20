import Tools.ShippingCoreFromMPorts

/-! # Audit: the first slice of the `core_*` / `core_*M` consolidation (round par/b-24)

Round par/b-24 MOVED four `…M` theorems out of `Tools/ShippingMemKidCore.lean`
into the files of the old theorems they generalise, moved `Kid` and its
bridge into the early file `Tools/ShippingKid.lean`, and replaced the proof
bodies of THREE old theorems (`core_raw_facts`, `core_hierGate`,
`core_callPorts`) by calls of their `…M` forms. No statement was meant to
change. This file THROWS unless, for each of the three:

* the old constant's TYPE is `isDefEq` the type of its `_fromM` twin
  (`Tools/ShippingCoreFromM.lean`, unchanged since it was built against the
  OLD proof's statement — `Tests/Compiler/CoreFromMAuditTest.lean` checks the
  same equation from the other side; here it is the old NAME that was
  re-proved, so the equation says its statement did not move);
* the old constant, its `…M` form and the twin are on standard axioms;
* the old constant's proof term NAMES its `…M` form (the replacement is what
  was built) and the `…M` proof does not name the old constant;
* the `…M` constant is declared in the OLD theorem's module (it was moved,
  the name kept) and the old constant is still declared there.

It also THROWS unless the seven moved declarations of `Tools/ShippingKid.lean`
and `core_kids_factsM` are declared in the modules this round put them in,
on standard axioms.

LOGGED only: the number of `Expr` objects (`Lean.Expr.numObjs`, shared
subterms counted once) of the proof term of the old-name constant AFTER the
replacement, of its `_fromM` twin (the same body, so about the same size) and
of the `…M` form. The size BEFORE the replacement is not obtainable in this
build (the old proof is gone); the `…M` proof is the scripted copy of it, so
its size is the stand-in that is logged, and it is named as such.

What this is NOT: a statement about endpoints; a check that no OTHER
declaration changed (the moved blocks were compared byte for byte outside
Lean — `docs/parallel/B-core-dedup-slice1.md`).

UNVERIFIED at the time of writing: this file was not built. -/

namespace Tests.Compiler.CoreDedupAuditTest
open Lean Meta

/-- Standard axioms only, an error otherwise. -/
def stdAxioms (n : Name) : MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

/-- The module a constant is declared in (`none`: the current file). -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun idx => env.header.moduleNames[idx.toNat]?

/-- An error unless `n` is declared in module `m`. -/
def declaredIn (n m : Name) : MetaM Unit := do
  let env ← getEnv
  unless env.contains n do throwError "{n}: not in the imports"
  match moduleOf env n with
  | Option.some k =>
    unless k == m do throwError "{n}: declared in {k}, expected {m}"
  | Option.none => throwError "{n}: declared in no imported module"

/-- The proof term of a theorem. -/
def proofOf (n : Name) : MetaM Expr := do
  match (← getConstInfo n) with
  | Lean.ConstantInfo.thmInfo v => pure v.value
  | _ => throwError "{n}: not a theorem"

/-- The three old theorems re-proved this round: old name, its `…M` form, the
`_fromM` twin, the module of the old theorem. -/
def touched : List (Name × Name × Name × Name) :=
  [ (``Tools.ShippingChecksRaw.core_raw_facts,
      ``Tools.ShippingMemKid.core_raw_factsM,
      ``Tools.ShippingCoreFromM.core_raw_facts_fromM,
      `Tools.ShippingChecksRaw),
    (``Tools.ShippingChecksWidths.core_hierGate,
      ``Tools.ShippingMemKid.core_hierGateM,
      ``Tools.ShippingCoreFromM.core_hierGate_fromM,
      `Tools.ShippingChecksWidths),
    (``Tools.ShippingChecksWidths.core_callPorts,
      ``Tools.ShippingMemKid.core_callPortsM,
      ``Tools.ShippingCoreFromM.core_callPorts_fromM,
      `Tools.ShippingChecksWidths) ]

/-- Declarations moved without a change of proof: name, the module it is in now. -/
def moved : List (Name × Name) :=
  [ (``Tools.ShippingMemKid.Kid, `Tools.ShippingKid),
    (``Tools.ShippingMemKid.kid_of, `Tools.ShippingKid),
    (``Tools.ShippingMemKid.Kid.real, `Tools.ShippingKid),
    (``Tools.ShippingMemKid.Kid.mem, `Tools.ShippingKid),
    (``Tools.ShippingCoreFromM.kid_iff_real_of_nomem, `Tools.ShippingKid),
    (``Tools.ShippingCoreFromM.real_of_kid, `Tools.ShippingKid),
    (``Tools.ShippingCoreFromM.kid_of_real, `Tools.ShippingKid),
    (``Tools.ShippingMemKid.core_kids_factsM, `Tools.ShippingChecksCore) ]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let mut rows : Array MessageData := #[]
  let mut nOk : Nat := 0
  for (n, modN) in moved do
    declaredIn n modN
    stdAxioms n
  for (old, mN, fm, modN) in touched do
    declaredIn old modN
    declaredIn mN modN
    declaredIn fm `Tools.ShippingCoreFromM
    stdAxioms old
    stdAxioms mN
    stdAxioms fm
    let a ← getConstInfo old
    let b ← getConstInfo fm
    unless a.levelParams.length == b.levelParams.length do
      throwError "{fm}: {b.levelParams.length} universe parameters, {old} has {a.levelParams.length}"
    let bt := b.type.instantiateLevelParams b.levelParams (a.levelParams.map mkLevelParam)
    unless ← isDefEq a.type bt do
      throwError "{old}: its statement is NOT the statement of {fm}:{indentExpr a.type}\nnot{indentExpr bt}"
    let same : Bool := a.type == bt
    let vOld ← proofOf old
    let vM ← proofOf mN
    let vFm ← proofOf fm
    -- Since the split over `MachineRan` (2026-10-14) the old theorem is a
    -- corollary of its `_ran` form, and it is the `_ran` forms that are tied:
    -- `old` names `old_ran`, whose proof names `mN_ran`. Either tie is accepted.
    let direct : Bool := (vOld.find? (·.isConstOf mN)).isSome
    let oldRan := old.appendAfter "_ran"
    let mRan := mN.appendAfter "_ran"
    let env ← getEnv
    let viaRan : Bool ←
      if env.contains oldRan && env.contains mRan then do
        let vOldRan ← proofOf oldRan
        pure ((vOld.find? (·.isConstOf oldRan)).isSome && (vOldRan.find? (·.isConstOf mRan)).isSome)
      else pure false
    unless direct || viaRan do
      throwError "{old}: its proof names neither {mN} nor (through {oldRan}) {mRan} — the old proof body was not replaced"
    if (vM.find? (·.isConstOf old)).isSome then
      throwError "{mN}: its proof names {old}"
    if (vFm.find? (·.isConstOf old)).isSome then
      throwError "{fm}: its proof names {old}"
    let sOld : Nat ← (vOld.numObjs : IO Nat)
    let sM : Nat ← (vM.numObjs : IO Nat)
    let sFm : Nat ← (vFm.numObjs : IO Nat)
    nOk := nOk + 1
    rows := rows.push m!"{old} — statement defEq {fm} (syntactically equal: {same}); proof names {mN}; proof-term objects: old name AFTER {sOld}, _fromM twin {sFm}, {mN} {sM} (the scripted copy of the old proof: stand-in for BEFORE, not a measurement of it)"
  unless nOk == 3 do throwError "audited {nOk} theorems, expected 3"
  let tbl : MessageData := MessageData.joinSep rows.toList (MessageData.ofFormat Format.line)
  Lean.logInfo m!"COREDEDUP AUDIT TABLE:{indentD tbl}"
  Lean.logInfo m!"COREDEDUP AUDIT: {nOk} old core_* theorems are now corollaries of their M forms (statement defEq the _fromM twin's, standard axioms, proof names the M form); the M forms and core_kids_factsM are declared in the old theorems' modules, Kid and its bridge in Tools.ShippingKid ({moved.length} moved declarations checked). The _fromM twins are KEPT (independent re-derivations, read by CoreFromMAuditTest). Still duplicated: the 7 non-corollaries and the other 7 corollaries."

end Tests.Compiler.CoreDedupAuditTest
