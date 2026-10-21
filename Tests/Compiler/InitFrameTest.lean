import Tools.ShippingInitFrame
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit RT2): rt2b exit 1, rt2c exit 0; RT3 review edit (set-body check): rt3b exit 1 only because of InitSessionTest, InitFrameTest part passed. EVIDENCE only.

/-! Unit RT2 (L9d). EVIDENCE about the structure of the loaded environment; it does NOT prove `InitOrder`,
`OthersFrameRefs` or `InitHeapRelXfer`.
(1) Source order: the declaration ranges of the three `initialize`d refs and of the `set` initialiser are in the
order 954 < 1028 < 1036 < 8934 (declaration-range start lines, including doc comments) (matches `InitOrder`'s shape). This is source position, not execution order.
(2) Direct-mention scan: over every `[init]` entry of every imported module, the init function bodies that
mention a tracked ref constant DIRECTLY (one level, no unfolding of called functions). Expected: exactly the
`set` initialiser. Indirect writes through called functions are NOT excluded by this scan.
(3) Closure audit of the new theorems and the Prop-binder list. -/

open Lean Meta Elab Sparkle.Compiler.Elab in
run_meta do
  let env ← getEnv
  let line (n : Name) : MetaM Nat := do
    let some r ← findDeclarationRanges? n | throwError "no range for {n}"
    return r.range.pos.line
  let l1 ← line ``sparkleSynthDepth
  let l2 ← line ``sparkleChildCache
  let l3 ← line ``sparkleChildSynth
  unless l1 < l2 && l2 < l3 do throwError "source order of the three refs unexpected: {l1} {l2} {l3}"
  let refs := [``sparkleSynthDepth, ``sparkleChildCache, ``sparkleChildSynth]
  -- (2) scan all [init] entries with an IO-Unit init decl (anonymous initDecl) and ref-initialisers
  let mut hits : Array (Name × Name) := #[]   -- (module, decl)
  let mut nEntries : Nat := 0
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    for (decl, initDecl) in regularInitAttr.ext.getModuleEntries env i do
      nEntries := nEntries + 1
      let body? := (env.find? (if initDecl.isAnonymous then decl else initDecl)).bind (·.value?)
      if let some b := body? then
        if refs.any (b.getUsedConstants.contains ·) then hits := hits.push (m, decl)
  logInfo m!"init entries scanned: {nEntries}; decls whose init body directly mentions a tracked ref: {hits.map (·.2)}"
  unless hits.size == 1 do throwError "expected exactly the set initialiser, got {hits}"
  let (m, d) := hits[0]!
  unless m == `Sparkle.Compiler.Elab do throwError "set initialiser not in Sparkle.Compiler.Elab: {m}"
  -- review RT3: the classification is only precise if the body performs the write the proof assumes
  let some bodyD := (env.find? d).bind (·.value?) | throwError "no body for {d}"
  let usedD := bodyD.getUsedConstants
  unless usedD.contains ``Sparkle.Compiler.Elab.synthesizeChild && usedD.contains ``Option.some do
    throwError "set initialiser body does not mention `some synthesizeChild`: {usedD}"
  let setLike := usedD.filter fun c => c.components.getLast?.any (fun x => x == `set || x == `modify || x == `swap)
  if setLike.isEmpty then throwError "set initialiser body mentions no Ref write primitive: {usedD}"
  logInfo m!"set initialiser body mentions synthesizeChild, Option.some and write primitive(s) {setLike} (constant occurrence only; not a proof that the write is `set (some synthesizeChild)` on sparkleChildSynth)"
  let l4 ← line d
  unless l3 < l4 do throwError "set initialiser line {l4} not after sparkleChildSynth {l3}"
  logInfo m!"INIT ORDER SOURCE EVIDENCE OK: lines {l1} < {l2} < {l3} < {l4}; the only init body directly mentioning a tracked ref is the set initialiser (direct mention only; no claim about indirect writes, execution order, or runtime fit)"

open Lean Meta Elab in
run_meta do
  for n in [``Tools.ShippingInitFrame.startAtLoad_of_initOrder, ``Tools.ShippingInitFrame.frame_chain,
      ``Tools.ShippingInitFrame.initOrder_false_iff] do
    Tests.Compiler.ChildVertAuditTest.stdAxioms n
    let cl ← Tests.Compiler.ChildVertAuditTest.depClosure n
    let bad := Tests.Compiler.ChildVertAuditTest.hits cl ++ cl.toList.filter fun c =>
      [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV,
       `Tools.ShippingChildInvA.RefLawsATele].any (·.isPrefixOf c)
    unless bad.isEmpty do throwError "{n}: old-boundary dependencies {bad}"
    logInfo m!"INIT-FRAME AUDIT OK: {n}: standard axioms; closure {cl.size} constants"

open Lean Meta Elab in
def propHeadsRT2 (n : Name) : MetaM (List String) := do
  let some ci := (← getEnv).find? n | throwError "{n} unknown"
  forallTelescope ci.type fun xs _ => do
    let mut out := []
    for x in xs do
      if (← isProp (← inferType x)) then
        out := out ++ [((← inferType x).getAppFn.constName?.map (·.toString)).getD "?"]
    return out

open Lean Meta Elab in
run_meta do
  let hs ← propHeadsRT2 ``Tools.ShippingInitFrame.startAtLoad_of_initOrder
  let P := "Tools.ShippingStartWorldA2.Chain"
  let S := "Tools.ShippingStartAtLoad."
  let exp := [P, P, P, P, P, "Tools.ShippingInitFrame.InitHeapRelXfer", "Tools.ShippingInitFrame.OthersFrameRefs",
    S ++ "InitHeapRel", S ++ "GetSpec", S ++ "SetSynthSpec", S ++ "QuietSpec", "?"]
  unless hs == exp do throwError "BINDER AUDIT FAILED: {hs}"
  logInfo m!"binder audit startAtLoad_of_initOrder (exact Prop-binder head list): {hs}"
