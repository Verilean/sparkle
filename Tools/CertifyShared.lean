import Tools.DeepElab
import Tools.CertifiedRoundtrip

/-!
Strict, proof-carrying roundtrip acceptance on top of the shared generator.
`#certify_shared_roundtrip f => result` generates the chain then seals it.
`#seal_shared_roundtrip f => result` seals an already generated chain (invoke
it in the same namespace, or open the namespace containing those declarations).

Unlike #verify_elab_deep's diagnostic PROVEN messages, acceptance requires
original, optimized, and reparsed replay AND the parse equality. A missing
forward-SV theorem is permitted: this API is explicitly roundtrip-only.
No certificate is emitted on a missing link, proof error, or failed axiom audit.
-/

namespace Tools.CertifyShared

open Lean Meta Elab Command

private def audit (n traceName parseName : Name) : CommandElabM Unit := do
  let info ← getConstInfo n
  let some value := info.value? (allowOpaque := true)
    | throwError "roundtrip certification: {n} has no proof body"
  if value.hasMVar then
    throwError "roundtrip certification: {n} has unresolved metavariables"
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  for a in (← liftCoreM <| collectAxioms n) do
    let allowed := std.contains a || a == ``Lean.ofReduceBool ||
      match a with
      | .str (.str (.str owner "_native") kind) ax =>
        let digits := ax.drop 3
        ax.startsWith "ax_" && !digits.isEmpty && digits.all Char.isDigit &&
          ((owner == traceName && kind == "bv_decide") ||
           (owner == parseName && kind == "native_decide"))
      | _ => false
    unless allowed do
      throwError "roundtrip certification: {n} depends on disallowed axiom {a}"

private def sealCertificate (id result : Ident) : CommandElabM Unit := do
  if (← get).messages.hasErrors then
    throwError "roundtrip certification: earlier elaboration errors; no certificate emitted"
  let declName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo id
  let base := declName.componentsRev.headD Name.anonymous |>.toString
  let resolve (suffix : String) : CommandElabM Name := do
    let candidate := mkIdent (Name.mkSimple s!"{base}_sdeep_{suffix}")
    try
      liftTermElabM <| realizeGlobalConstNoOverloadWithInfo candidate
    catch _ =>
      throwError "roundtrip certification: missing required link {candidate.getId}; a partial PROVEN chain is not accepted"
  let traceName ← resolve "trace"
  let parseName ← resolve "text_parses"
  let irName ← resolve "signal_run"
  let optName ← resolve "signal_runOpt"
  let rtName ← resolve "signal_runRT"
  let textName ← resolve "text"
  for n in [traceName, parseName, irName, optName, rtName] do
    audit n traceName parseName
  let (value, type) ← liftTermElabM do
    let rtInfo ← getConstInfo rtName
    forallTelescope rtInfo.type fun xs _ => do
      if xs.isEmpty then throwError "roundtrip certification: replay has no horizon binder"
      -- Generated replay binders are the source parameters followed by K.
      let params := xs.pop
      let mut source := mkConst declName
      let mut sourceTy := (← getConstInfo declName).type
      let mut index := 0
      for _ in [0:64] do
        sourceTy ← whnf sourceTy
        match sourceTy with
        | .forallE _ ty body _ =>
          let arg ← if ty.isConstOf ``Sparkle.Core.Domain.DomainConfig then
              pure (mkConst ``Sparkle.Core.Domain.defaultDomain)
            else do
              if index ≥ params.size then
                throwError "roundtrip certification: unsupported source parameter signature"
              let p := params[index]!
              index := index + 1
              pure p
          source := mkApp source arg
          sourceTy := body.instantiate1 arg
        | _ => break
      if index != params.size || sourceTy.isForall then
        throwError "roundtrip certification: source/replay parameter mismatch"
      if !sourceTy.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal then
        let .const structName _ := sourceTy.getAppFn
          | throwError "roundtrip certification: unsupported source result type"
        let some info := getStructureInfo? (← getEnv) structName
          | throwError "roundtrip certification: source must return a BitVec Signal or a single-field output structure"
        unless info.fieldNames.size == 1 do
          throwError "roundtrip certification: multiple output fields are outside this contract"
        source ← mkAppM (structName ++ info.fieldNames[0]!) #[source]
      let observation ← mkAppM ``Tools.CertifiedRoundtrip.observe #[source]
      let cert ← mkAppM ``Tools.CertifiedRoundtrip.ofReplay
        #[mkConst textName, mkConst parseName,
          mkAppN (mkConst irName) params, mkAppN (mkConst optName) params,
          mkAppN (mkConst rtName) params]
      let expected ← mkAppM ``Tools.CertifiedRoundtrip.Certificate #[observation]
      unless ← isDefEq (← inferType cert) expected do
        throwError "roundtrip certification: replay does not certify the requested source {declName}"
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars (← mkLambdaFVars params cert)
      let type ← instantiateMVars (← inferType value)
      if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar then
        throwError "roundtrip certification: certificate is not closed"
      pure (value, type)
  let full := (← getCurrNamespace) ++ result.getId
  -- addAndCompile submits the complete definition to the kernel. The proof
  -- fields cannot be omitted even if a generator reported a partial success.
  liftCoreM <| addAndCompile <| .defnDecl {
    name := full, levelParams := [], type, value, hints := .regular 0, safety := .safe }
  audit full traceName parseName
  if (← get).messages.hasErrors then
    throwError "roundtrip certification: elaboration failed; certification command failed"
  logInfo m!"CERTIFIED_ROUNDTRIP {declName}: {full} (original + optimized + parsed text; parser-relative semantics)"

elab "#seal_shared_roundtrip " id:ident " => " result:ident : command =>
  sealCertificate id result

elab "#certify_shared_roundtrip " id:ident " => " result:ident : command => do
  elabCommand (← `(set_option sparkle.deepShare true in #verify_elab_deep $id))
  sealCertificate id result

end Tools.CertifyShared
