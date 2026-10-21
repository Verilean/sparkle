import Tools.ShippingInitSession
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit RT3): rt3b exit 1 (String.Slice.splitOn), rt3c exit 0. EVIDENCE + audit; proves none of the premises.

/-! Unit RT3 (L9e).
(1) Audit of `startContents_session_init`: closure, exact Prop-binder head list, and a conclusion +
hypothesis-type `isDefEq` comparison against L9b's `startContents_session` at the SAME end world `w0` of the
interleaved load (scope: the conclusion and the type of the chain hypothesis `hs`, plus the outer Prop head list;
NOT a whole forall-type identity). Mutations (start world `loadW wS`, different `O'`, dropped quiet, different end
world) must be rejected.
(2) Loader-trace SOURCE evidence (see ledger L9e): (a) which init path ran in THIS elaborating process
(`interpretedModInits` ∌ `Sparkle.Compiler.Elab` ⇒ the interpreter did not run that module's `[init]` entries, i.e.
the native `initialize_<Module>` path ran); (b) the emitted C `initialize_sparkle_Sparkle_Compiler_Elab` of THIS
package: textual order of the three ref assignments and the call of the `set` initialiser. A textual order of
generated C is NOT an executed trace of a run and NOT `InitOrder` for the `Other`-steps. -/

open Lean Meta Elab in
run_meta do
  let n := ``Tools.ShippingInitSession.startContents_session_init
  Tests.Compiler.ChildVertAuditTest.stdAxioms n
  let cl ← Tests.Compiler.ChildVertAuditTest.depClosure n
  let bad := Tests.Compiler.ChildVertAuditTest.hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV,
     `Tools.ShippingChildInvA.RefLawsATele].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{n}: old-boundary dependencies {bad}"
  logInfo m!"INIT-SESSION AUDIT OK: {n}: standard axioms; closure {cl.size} constants"

open Lean Meta Elab in
def propHeadsRT3 (n : Name) : MetaM (List String) := do
  let some ci := (← getEnv).find? n | throwError "{n} unknown"
  forallTelescope ci.type fun xs _ => do
    let mut out := []
    for x in xs do
      let t ← inferType x
      if (← isProp t) then
        out := out ++ [(t.getAppFn.constName?.map (·.toString)).getD "?"]
    return out

open Lean Meta Elab in
run_meta do
  let n := ``Tools.ShippingInitSession.startContents_session_init
  let hs ← propHeadsRT3 n
  let exp := ["Tools.ShippingChildInvA.AdmCtx", "Tools.ShippingChildDepthC.BodyStepC",
    "Tools.ShippingStartWorldA2.OtherCodeKeeps",
    "Tools.ShippingInitFrame.InitOrder", "Tools.ShippingInitFrame.InitHeapRelXfer",
    "Tools.ShippingInitFrame.OthersFrameRefs",
    "Tools.ShippingStartAtLoad.InitHeapRel", "Tools.ShippingStartAtLoad.GetSpec",
    "Tools.ShippingStartAtLoad.SetSynthSpec", "Tools.ShippingStartAtLoad.QuietSpec", "?",
    "Tools.ShippingStartWorldA2.Chain"]
  unless hs == exp do throwError "BINDER AUDIT FAILED: {hs}"
  logInfo m!"binder audit {n} (exact Prop-binder head list): {hs}"

open Lean Meta Elab Term in
run_elab do
  let n := ``Tools.ShippingInitSession.startContents_session_init
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs concl => do
    let fv (nm : Name) : MetaM Expr := do
      for x in xs do
        if (← x.fvarId!.getUserName) == nm then return x
      throwError "binder {nm} not found"
    let O ← fv `O
    let hs ← fv `hs
    let hsT ← inferType hs
    let mk (src : String) : TermElabM Expr := do
      let stx ← match Parser.runParserCategory (← getEnv) `term src with
        | .ok s => pure s | .error e => throwError e
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let ch (start : String) (stop : String) := s!"(Tools.ShippingStartWorldA2.Chain (fun a b => Tools.ShippingStartWorldA2.EntryStep mctx mref cctx cref a b ∨ Other a b) {start} {stop})"
    let good ← mk "(O.quiet w ∧ Tools.ShippingStartWorldA.StartContents w)"
    unless ← isDefEq concl good do throwError "AUDIT FAILED: conclusion {concl}"
    -- the start world of L9b's session chain is the SAME w0 that `InitOrder Other₀ wS w0` ends in
    unless ← isDefEq hsT (← mk (ch "w0" "w")) do throwError "AUDIT FAILED: chain {hsT}"
    let hI ← fv `hI
    let hIT ← inferType hI
    unless ← isDefEq hIT (← mk "(Tools.ShippingInitFrame.InitOrder Other₀ wS w0)") do
      throwError "AUDIT FAILED: hI {hIT}"
    if ← isDefEq hsT (← mk (ch "(Tools.ShippingStartAtLoad.loadW wS)" "w")) then throwError "ALTERED START (loadW) ACCEPTED"
    if ← isDefEq hsT (← mk (ch "(Tools.ShippingStartAtLoad.mkRefsW wS)" "w")) then throwError "ALTERED START (mkRefsW) ACCEPTED"
    if ← isDefEq hsT (← mk (ch "w0" "w0")) then throwError "ALTERED END ACCEPTED"
    if ← isDefEq concl (← mk "(O.quiet w ∧ Tools.ShippingStartWorldA.StartContents w0)") then throwError "ALTERED CONCLUSION ACCEPTED"
    if ← isDefEq concl (← mk "(Tools.ShippingStartWorldA.StartContents w)") then throwError "DROPPED QUIET ACCEPTED"
    withLocalDeclD `O' (← inferType O) fun O' => do
      let lam ← mkLambdaFVars #[O] good
      if ← isDefEq concl (lam.beta #[O']) then throwError "ALTERED O ACCEPTED"
    logInfo m!"INIT-SESSION CONCLUSION/CHAIN AUDIT OK (conclusion, type of hs and type of hI compared by isDefEq with the L9b statement at the same w0, plus the Prop head list; not a whole forall-type identity); altered start world, end world, conclusion, dropped quiet, different O rejected"

/-! ## (2a) which init path ran in this process -/
open Lean Meta Elab in
run_meta do
  let interp ← Lean.interpretedModInits.get
  let m := `Sparkle.Compiler.Elab
  logInfo m!"interpretedModInits ∋ {m}: {interp.contains m}; |interpretedModInits| = {interp.toList.length}"
  if interp.contains m then
    logInfo m!"INIT PATH: interpreted path ran `Sparkle.Compiler.Elab`'s [init] entries in this process (order = getModuleEntries)"
  else
    logInfo m!"INIT PATH: `Sparkle.Compiler.Elab` NOT in interpretedModInits: its initialisers were not run by the interpreter in this process (so the native `runModInit`/`initialize_<Module>` path, or none; this observation does not itself show which)"

/-! ## (2b) emitted C of this package: order inside `initialize_sparkle_Sparkle_Compiler_Elab` -/
open Lean Meta Elab in
def posOf? (s p : String) : Option Nat :=
  let parts := s.splitOn p
  if parts.length < 2 then none else some parts[0]!.length

open Lean Meta Elab in
run_meta do
  let path : System.FilePath := ".lake/build/ir/Sparkle/Compiler/Elab.c"
  unless ← path.pathExists do
    logInfo m!"EMITTED-C ORDER CHECK SKIPPED: {path} not present (nothing checked)"
    return
  let src ← IO.FS.readFile path
  let marker := "lean_object* initialize_sparkle_Sparkle_Compiler_Elab(uint8_t builtin) {"
  let some i0 := posOf? src marker | throwError "initializer not found in {path}"
  let body := (src.drop i0).toString
  let env ← getEnv
  let some midx := env.header.moduleNames.findIdx? (· == `Sparkle.Compiler.Elab) | throwError "module not imported"
  let refs := [``Sparkle.Compiler.Elab.sparkleSynthDepth, ``Sparkle.Compiler.Elab.sparkleChildCache,
    ``Sparkle.Compiler.Elab.sparkleChildSynth]
  let mut setDecl? : Option Name := none
  for (decl, initDecl) in regularInitAttr.ext.getModuleEntries env midx do
    let some ci := env.find? (if initDecl.isAnonymous then decl else initDecl) | continue
    if let some b := ci.value? then
      if initDecl.isAnonymous && refs.any (b.getUsedConstants.contains ·) then setDecl? := some decl
  let some setDecl := setDecl? | throwError "set initialiser not found"
  let some bodyD := (env.find? setDecl).bind (·.value?) | throwError "no body for {setDecl}"
  let usedD := bodyD.getUsedConstants
  unless usedD.contains ``Sparkle.Compiler.Elab.synthesizeChild && usedD.contains ``Option.some do
    throwError "set initialiser body does not mention `some synthesizeChild`"
  let mut ps : Array Nat := #[]
  for r in refs do
    let pat := s!"{r.mangle "lp_sparkle_"} = lean_io_result_get_value(res);"
    let some p := posOf? body pat | throwError "assignment of {r} not found in the C initializer ({pat})"
    ps := ps.push p
  let callPat := s!"res = {setDecl.mangle "lp_sparkle_"}();"
  let some pSet := posOf? body callPat | throwError "call of the set initialiser not found ({callPat})"
  unless ps[0]! < ps[1]! && ps[1]! < ps[2]! && ps[2]! < pSet do
    throwError "C ORDER UNEXPECTED: {ps} {pSet}"
  logInfo m!"EMITTED-C ORDER OK (textual order in the generated initializer of this build, NOT an executed trace; Other-steps between not analysed): depth-ref assignment < cache-ref assignment < synth-ref assignment < call of {setDecl}; offsets {ps} < {pSet}"
