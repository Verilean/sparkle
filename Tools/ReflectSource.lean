import Tools.VerifiedSource

/-! A bounded, unverified Lean-expression reader with kernel-checked output.
It proposes a typed Source and accepts it only with a definitional equality to
the requested Lean definition. It is NOT a universally proved Lean reifier.
v1: one BitVec register, BitVec Signal parameters, optional outer Bool reset,
single BitVec Signal output; arithmetic/bitwise expressions and 1-bit muxes.
The reader inlines lets and imposes a work budget; it is not the sharing route. -/

namespace Tools.ReflectSource

open Lean Meta Elab Command

private def refuse (message : MessageData) : TermElabM α :=
  throwError "verified source reader: {message}"

private def width (e : Expr) : TermElabM Nat := do
  let ty ← whnf (← inferType e)
  let ty := if ty.isAppOf ``Sparkle.Core.Signal.Signal then ty.getAppArgs.back! else ty
  unless ty.isAppOf ``BitVec do refuse m!"expected BitVec, got {ty}"
  let n ← (Lean.Meta.evalNat ty.getAppArgs.back!).run
  match n with
  | some n => return n
  | none => refuse "width must reduce to a numeral"

private def spend (budget : IO.Ref Nat) : TermElabM Unit := do
  let n ← budget.get
  if n == 0 then refuse "expression budget exceeded (2048 steps); sharing is required"
  budget.set (n - 1)

private def lastTwo (e : Expr) : Expr × Expr :=
  let args := e.getAppArgs
  (args[args.size - 2]!, args.back!)

/-- Candidate construction only. Final source equality, not this reader's
pattern matching or numeral evaluation, justifies the emitted representation. -/
private partial def readSignal (ctx : Expr) (atoms : Array Expr) (budget : IO.Ref Nat)
    (term : Expr) : TermElabM Expr := do
  spend budget
  for i in [:atoms.size] do
    if ← isDefEq term atoms[i]! then
      let finTy ← mkAppM ``Fin #[mkNatLit atoms.size]
      let idx ← Term.elabTerm (← `(⟨$(quote i), by decide⟩)) (some finTy)
      return ← mkAppOptM ``CExpr.var #[some ctx, some idx]
  let n := term.getAppFn.constName?
  if n == some ``Sparkle.Core.Signal.Signal.register ||
      n == some ``Sparkle.Core.Signal.Signal.loop then
    refuse "additional register or nested loop"
  if n == some ``Sparkle.Core.Signal.Signal.mux then
    let args := term.getAppArgs
    let c := args[args.size - 3]!
    let c ← readCondition ctx atoms budget c
    let (a, b) := lastTwo term
    return ← mkAppM ``CExpr.mux #[c, ← readSignal ctx atoms budget a,
      ← readSignal ctx atoms budget b]
  let binaries := [( ``HAdd.hAdd, ``CExpr.add), (``HSub.hSub, ``CExpr.sub),
    (``HMul.hMul, ``CExpr.mul), (``HAnd.hAnd, ``CExpr.and),
    (``HOr.hOr, ``CExpr.or), (``HXor.hXor, ``CExpr.xor)]
  for (head, ctor) in binaries do
    if n == some head then
      let (a, b) := lastTwo term
      return ← mkAppM ctor #[← readSignal ctx atoms budget a, ← readSignal ctx atoms budget b]
  if n == some ``Sparkle.Core.Signal.Signal.pure then
    return ← readSignal ctx atoms budget term.getAppArgs.back!
  let ty ← whnf (← inferType term)
  if ty.isAppOf ``BitVec && !term.hasFVar then
    let w ← width term
    let value ← mkAppM ``BitVec.toNat #[term]
    let some value ← (Lean.Meta.evalNat value).run | refuse "constant does not reduce"
    return ← mkAppOptM ``CExpr.const #[some ctx, some (mkNatLit w), some (mkNatLit value)]
  let reduced ← whnfCore term
  if reduced != term then return ← readSignal ctx atoms budget reduced
  if let some reduced ← unfoldDefinition? term then
    return ← readSignal ctx atoms budget reduced
  refuse m!"unsupported expression {term}"
where
  readCondition (ctx : Expr) (atoms : Array Expr) (budget : IO.Ref Nat)
      (term : Expr) : TermElabM Expr := do
    spend budget
    if term.isAppOf ``Sparkle.Core.Signal.Signal.beq then
      let (a, b) := lastTwo term
      if (← width a) == 1 then
        let dom := (← whnf (← inferType a)).getAppArgs[0]!
        let one ← Term.elabTerm (← `(1#1)) none
        let pureOne ← mkAppOptM ``Sparkle.Core.Signal.Signal.pure #[some dom, none, some one]
        if ← isDefEq b pureOne then return ← readSignal ctx atoms budget a
    let reduced ← whnfCore term
    if reduced != term then return ← readCondition ctx atoms budget reduced
    if let some reduced ← unfoldDefinition? term then
      return ← readCondition ctx atoms budget reduced
    refuse "mux condition must compare a 1-bit Signal with one"

private def addDefinition (name : Name) (value : Expr) : CommandElabM Unit := do
  let type ← liftTermElabM <| inferType value
  if value.hasFVar || value.hasMVar || type.hasFVar || type.hasMVar then
    throwError "verified source reader: open declaration {name}"
  liftCoreM <| addAndCompile <| .defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

/-- The acceptance boundary is testable independently of the candidate reader.
An unproved candidate is never promoted to a source-identity theorem. -/
def checkSourceIdentity (candidate source : Expr) : TermElabM (Expr × Expr) := do
  Term.synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq candidate source do
    refuse "candidate is not definitionally equal to the requested source"
  return (← mkEqRefl candidate, ← mkEq candidate source)

private def reflect (id result : Ident) : CommandElabM Unit := do
  let original ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo id
  let destName := (← getCurrNamespace) ++ result.getId
  for n in [destName, destName.appendAfter "_inputs", destName.appendAfter "_reset",
      destName.appendAfter "_source_eq"] do
    if (← getEnv).contains n then
      throwError "verified source reader: output declaration already exists: {n}"
  let (model, inputs, reset, proof, proofTy) ← liftTermElabM do
    let info ← getConstInfo original
    unless info.levelParams.isEmpty do refuse "universe-polymorphic definitions are outside v1"
    let some value := info.value? | refuse "source has no definition body"
    lambdaTelescope value fun params body => do
      let body := body.headBeta
      unless body.isAppOf ``Sparkle.Core.runCircuitH do refuse "expected circuit-do/runCircuitH at the definition head"
      let args := body.getAppArgs
      let dom := args[0]!
      let resultTy ← whnf args[2]!
      unless resultTy.isAppOf ``Sparkle.Core.Signal.Signal &&
          resultTy.getAppArgs.back!.isAppOf ``BitVec do
        refuse "single BitVec Signal output required"
      let types ← whnf args[1]!
      unless types.isAppOf ``List.cons do refuse "expected one register"
      let tail ← whnf types.getAppArgs.back!
      unless tail.isAppOf ``List.nil do refuse "multiple registers are outside v1"
      let initPair ← whnf args[6]!
      let init := initPair.getAppArgs[initPair.getAppArgs.size - 2]!
      if init.hasFVar then refuse "parameter-dependent initial value is outside v1"
      let r ← width init
      let mut sigs : Array Expr := #[]
      let mut widths : Array Nat := #[]
      let mut rst? : Option Expr := none
      for p in params do
        let ty ← whnf (← inferType p)
        unless ty.isAppOf ``Sparkle.Core.Signal.Signal do refuse "all parameters must be Signals"
        unless ← isDefEq ty.getAppArgs[0]! dom do refuse "mixed domains"
        let valTy := ty.getAppArgs.back!
        if valTy.isConstOf ``Bool then
          if rst?.isSome then refuse "more than one Bool parameter"
          rst? := some p
        else
          sigs := sigs.push p
          widths := widths.push (← width p)
      let Γ := toExpr widths.toList
      let ctx := toExpr (r :: widths.toList)
      let liveTy ← mkAppOptM ``Sparkle.Core.Signal.Signal
        #[some dom, some (← mkAppM ``Sparkle.Core.HList #[args[1]!])]
      withLocalDeclD `live liveTy fun live => do
        let pair ← whnf (← mkAppM ``Tools.VerifiedCircuit.evaluateBody #[args[7]!, live])
        let out := pair.getAppArgs[pair.getAppArgs.size - 2]!
        let writes ← whnf pair.getAppArgs.back!
        let next := writes.getAppArgs[writes.getAppArgs.size - 2]!
        let reg ← mkAppM ``Sparkle.Core.Signal.Signal.map
          #[← mkAppOptM ``Prod.fst #[some (← mkAppM ``BitVec #[mkNatLit r]), some (mkConst ``Unit)], live]
        let mut next := next
        let rst ← match rst? with
          | none => mkAppOptM ``Sparkle.Core.Signal.Signal.pure #[some dom, none, some (mkConst ``Bool.false)]
          | some rst => do
            -- Peel lets/coercions, but stop before expanding mux itself.
            for _ in [:128] do
              if next.isAppOf ``Sparkle.Core.Signal.Signal.mux then break
              let e ← whnfCore next
              if e != next then next := e
              else if let some e ← unfoldDefinition? next then next := e
              else break
            unless next.isAppOf ``Sparkle.Core.Signal.Signal.mux do
              refuse "Bool reset must be the outer next-state mux"
            let na := next.getAppArgs
            unless ← isDefEq na[na.size - 3]! rst do refuse "outer mux does not use the reset parameter"
            let initSig ← mkAppOptM ``Sparkle.Core.Signal.Signal.pure #[some dom, none, some init]
            unless ← isDefEq na[na.size - 2]! initSig do refuse "reset branch differs from the declared initial value"
            next := na.back!
            pure rst
        let budget ← IO.mkRef 2048
        let atoms := #[reg] ++ sigs
        let ne ← readSignal ctx atoms budget next
        let oe ← readSignal ctx atoms budget out
        let ret ← mkAppOptM ``Tools.VerifiedSource.Program.ret #[some ctx, some (mkNatLit r), none, some oe]
        let program ← mkAppM ``Tools.VerifiedSource.Program.next #[ne, ret]
        let model ← mkAppOptM ``Tools.VerifiedSource.Source.mk #[some Γ, some (mkNatLit r), none, some init, some program]
        -- Construct the dependent input tuple by elaboration inside this scope.
        let mut inputSyntax ← `(fun i => Fin.elim0 i)
        for sig in sigs.reverse do
          let sigSyntax ← PrettyPrinter.delab sig
          inputSyntax ← `(Fin.cases $sigSyntax $inputSyntax)
        let inpTy ← mkAppM ``Tools.VerifiedSource.Signals #[dom, Γ]
        let inp ← Term.elabTerm inputSyntax (some inpTy)
        let candidate ← mkAppM ``Tools.VerifiedSource.Source.run #[model, inp, rst]
        let source := mkAppN (mkConst original) params
        let (eqProof, eqTy) ← checkSourceIdentity candidate source
        Term.synthesizeSyntheticMVarsNoPostponing
        let model ← instantiateMVars model
        if model.hasFVar || model.hasMVar then refuse "model depends on an out-of-scope value"
        let inp ← instantiateMVars (← mkLambdaFVars params inp)
        let rst ← instantiateMVars (← mkLambdaFVars params rst)
        let pr ← instantiateMVars (← mkLambdaFVars params eqProof)
        let ty ← instantiateMVars (← mkForallFVars params eqTy)
        pure (model, inp, rst, pr, ty)
  addDefinition destName model
  addDefinition (destName.appendAfter "_inputs") inputs
  addDefinition (destName.appendAfter "_reset") reset
  let eqName := destName.appendAfter "_source_eq"
  liftCoreM <| addDecl <| .thmDecl { name := eqName, levelParams := [], type := proofTy, value := proof }
  for a in (← liftCoreM <| collectAxioms eqName) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "verified source reader: disallowed axiom {a}"
  if (← get).messages.hasErrors then
    throwError "verified source reader: elaboration failed; no reflected artifact"
  logInfo m!"REFLECTED SOURCE {original}: {destName}; kernel-checked source identity"

elab "#reflect_verified " id:ident " => " result:ident : command => do
  if (← get).messages.hasErrors then
    throwError "verified source reader: earlier elaboration errors"
  let saved ← get
  try
    reflect id result
  catch e =>
    set saved
    throw e

end Tools.ReflectSource
