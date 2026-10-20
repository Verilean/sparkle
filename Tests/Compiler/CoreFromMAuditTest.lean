import Tools.ShippingCoreFromMPorts

/-! # Audit: the old `core_*` statements re-derived from the `M` copies (round par/b-16)

For each of the 17 pairs (old theorem, scripted copy `…M`) of
`Tools/ShippingMemKidCore.lean` and `Tools/ShippingMemKidPorts.lean`:

* a pair marked RE-DERIVED has a theorem `Tools.ShippingCoreFromM.<old>_fromM`.
  This file THROWS unless its statement is definitionally the statement of
  the old theorem (`isDefEq` on the two constants' types), unless it is on
  standard axioms, and if its proof term mentions the old theorem itself
  (that would be a restatement, not a re-derivation);
* a pair marked NOT A COROLLARY has none. This file THROWS unless the reason
  recorded in the inventory is what the two statements say: the old one has
  the binder `hnomem` and NO binder `hfne`, the `M` one has `hfne`
  (`d.shape.instFields ≠ []`), so the old theorem also speaks of the
  one-output closing, where the `M` one says nothing.

LOGGED: a table, old name — re-derived (T/F) — lines of the old declaration
(statement and proof, from the declaration's recorded range) — lines of the
re-derivation.

What this is NOT: a replacement of any old proof (no existing file is
changed; nothing consumes the `_fromM` theorems), and no statement about
endpoints.

UNVERIFIED at the time of writing: this file was not built. -/

namespace Tests.Compiler.CoreFromMAuditTest
open Lean Meta

/-- Standard axioms only, an error otherwise. -/
def stdAxioms (n : Name) : MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

/-- The names of the leading binders of a statement. -/
def binderNames : Expr → List Name
  | Expr.forallE n _ b _ => n :: binderNames b
  | _ => []

/-- Lines of a declaration (its recorded range), if recorded. -/
def declLines (n : Name) : MetaM (Option Nat) := do
  let r? ← Lean.findDeclarationRanges? n
  return r?.map (fun r => r.range.endPos.line - r.range.pos.line + 1)

/-- The inventory: old theorem, its `M` copy, the re-derivation (if the old
statement is a corollary of the `M` one). -/
def pairs : List (Name × Name × Option Name) :=
  [ (``Tools.ShippingChecksCore.core_kids_facts,
      ``Tools.ShippingMemKid.core_kids_factsM, none),
    (``Tools.ShippingChecksRaw.core_raw_facts,
      ``Tools.ShippingMemKid.core_raw_factsM,
      some ``Tools.ShippingCoreFromM.core_raw_facts_fromM),
    (``Tools.ShippingLinkedFresh.core_linkedWF,
      ``Tools.ShippingMemKid.core_linkedWFM, none),
    (``Tools.ShippingLinkedFresh.core_instOuts_not_assigned,
      ``Tools.ShippingMemKid.core_instOuts_not_assignedM, none),
    (``Tools.ShippingChecksOuts.core_outsExtracted,
      ``Tools.ShippingMemKid.core_outsExtractedM,
      some ``Tools.ShippingCoreFromM.core_outsExtracted_fromM),
    (``Tools.ShippingChecksWidths.core_callPorts,
      ``Tools.ShippingMemKid.core_callPortsM,
      some ``Tools.ShippingCoreFromM.core_callPorts_fromM),
    (``Tools.ShippingChecksWidths.core_instOutWidthsOk,
      ``Tools.ShippingMemKid.core_instOutWidthsOkM,
      some ``Tools.ShippingCoreFromM.core_instOutWidthsOk_fromM),
    (``Tools.ShippingChecksWidths.core_hierGate,
      ``Tools.ShippingMemKid.core_hierGateM,
      some ``Tools.ShippingCoreFromM.core_hierGate_fromM),
    (``Tools.ShippingChecksRunFacts.core_runFacts,
      ``Tools.ShippingMemKid.core_runFactsM,
      some ``Tools.ShippingCoreFromM.core_runFacts_fromM),
    (``Tools.ShippingChecksCoreGate.core_outsCheck_all_gate,
      ``Tools.ShippingMemKid.core_outsCheck_all_gateM, none),
    (``Tools.ShippingClosedTyped.core_closed_typedIn,
      ``Tools.ShippingMemKid.core_closed_typedInM, none),
    (``Tools.ShippingCoreClk.core_clk,
      ``Tools.ShippingMemKid.core_clkM, none),
    (``Tools.ShippingPortsMatchRaw.core_callConns,
      ``Tools.ShippingMemKid.core_callConnsM,
      some ``Tools.ShippingCoreFromM.core_callConns_fromM),
    (``Tools.ShippingPortsMatchRaw.core_portsMatch_raw,
      ``Tools.ShippingMemKid.core_portsMatch_rawM,
      some ``Tools.ShippingCoreFromM.core_portsMatch_raw_fromM),
    (``Tools.ShippingKidsSelf.core_kids_self,
      ``Tools.ShippingMemKid.core_kids_selfM, none),
    (``Tools.ShippingKidsSelf.core_kidsPass_deep,
      ``Tools.ShippingMemKid.core_kidsPass_deepM,
      some ``Tools.ShippingCoreFromM.core_kidsPass_deep_fromM),
    (``Tools.ShippingTextShipped.core_designCheck_run,
      ``Tools.ShippingMemKid.core_designCheck_runM,
      some ``Tools.ShippingCoreFromM.core_designCheck_run_fromM) ]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut nYes : Nat := 0
  let mut nNo : Nat := 0
  let mut oldLines : Nat := 0
  let mut newLines : Nat := 0
  let mut keptLines : Nat := 0
  let mut rows : Array MessageData := #[]
  unless pairs.length == 17 do throwError "the inventory has {pairs.length} pairs, expected 17"
  for n in [``Tools.ShippingCoreFromM.kid_iff_real_of_nomem,
      ``Tools.ShippingCoreFromM.real_of_kid, ``Tools.ShippingCoreFromM.kid_of_real] do
    stdAxioms n
  for (old, mN, fm?) in pairs do
    unless env.contains old do throwError "{old}: not in the imports"
    unless env.contains mN do throwError "{mN}: not in the imports"
    stdAxioms old
    stdAxioms mN
    let a ← getConstInfo old
    let mI ← getConstInfo mN
    let oldB := binderNames a.type
    let mB := binderNames mI.type
    unless oldB.contains `hnomem do
      throwError "{old}: no binder hnomem (the inventory is wrong)"
    if mB.contains `hnomem then
      throwError "{mN}: still has the binder hnomem (the inventory is wrong)"
    unless mB.contains `hfne do
      throwError "{mN}: no binder hfne (the inventory is wrong)"
    let ol ← declLines old
    let olM : MessageData := match ol with
      | Option.some k => m!"{k}"
      | Option.none => m!"?"
    match fm? with
    | Option.some fm =>
      unless env.contains fm do throwError "{fm}: missing"
      -- the reason it IS a corollary: the old statement already asks hfne
      unless oldB.contains `hfne do
        throwError "{old}: no binder hfne, so {mN} (which asks it) cannot give it — {fm} cannot be its statement (the inventory is wrong)"
      let b ← getConstInfo fm
      unless a.levelParams.length == b.levelParams.length do
        throwError "{fm}: {b.levelParams.length} universe parameters, {old} has {a.levelParams.length}"
      let bt := b.type.instantiateLevelParams b.levelParams (a.levelParams.map mkLevelParam)
      unless ← isDefEq a.type bt do
        throwError "{fm}: its statement is NOT the statement of {old}:{indentExpr bt}\nnot{indentExpr a.type}"
      let same := a.type == bt
      stdAxioms fm
      let val ← match b with
        | Lean.ConstantInfo.thmInfo v => pure v.value
        | _ => throwError "{fm}: not a theorem"
      if (val.find? (·.isConstOf old)).isSome then
        throwError "{fm}: its proof mentions {old} — a restatement, not a re-derivation"
      let usesM := (val.find? (·.isConstOf mN)).isSome
      let nl ← declLines fm
      let nlM : MessageData := match nl with
        | Option.some k => m!"{k}"
        | Option.none => m!"?"
      nYes := nYes + 1
      oldLines := oldLines + ol.getD 0
      newLines := newLines + nl.getD 0
      rows := rows.push m!"{old} — re-derived T ({fm}; statement defEq, syntactically equal: {same}; proof term names {mN}: {usesM}) — old declaration {olM} lines — re-derivation {nlM} lines"
    | Option.none =>
      -- the reason it is NOT a corollary: the old statement does not ask hfne
      if oldB.contains `hfne then
        throwError "{old}: has the binder hfne — it may be a corollary of {mN} (the inventory is wrong)"
      nNo := nNo + 1
      keptLines := keptLines + ol.getD 0
      rows := rows.push m!"{old} — re-derived F (old statement: hnomem, NO hfne; {mN}: hfne in its place — the one-output closing instFields = [] is in the old statement only) — old declaration {olM} lines"
  unless nYes == 10 && nNo == 7 do
    throwError "re-derived {nYes}, not corollaries {nNo}; expected 10 and 7"
  let tbl : MessageData := MessageData.joinSep rows.toList (MessageData.ofFormat Format.line)
  Lean.logInfo m!"COREFROMM AUDIT TABLE (old name — re-derived — lines):{indentD tbl}"
  Lean.logInfo m!"COREFROMM AUDIT: {nYes} of 17 old core_* statements re-derived from their M copies (statements defEq the old ones, standard axioms, no proof names the old theorem); {nNo} are NOT corollaries (old statement without hfne) and have no _fromM. Declaration lines, statement included: the {nYes} old declarations {oldLines}, their re-derivations {newLines} (difference {oldLines - newLines}: what a replacement of the old proofs would remove, before import restructuring); the {nNo} old declarations that stay duplicated: {keptLines}. Since the first de-duplication slice (docs/parallel/B-core-dedup-slice1.md) three old theorems — core_raw_facts, core_hierGate, core_callPorts — ARE proved from their M forms in their own files; the other old theorems are unchanged; no declaration name or statement changed"

end Tests.Compiler.CoreFromMAuditTest
