import Tools.ShippingSeqParentGenD2M
-- BUILT (unit SR19): a8 exit 0 (dev run; 850 jobs); the final-SHA rebuild is in REPORT-SR19.md.
/-! # The decoding data of the calls, read from the GENERATED `machineExt` / `machineExtB` (unit SR19, ledger L8ay)

Used by the opt-in shared-leaf generator (`Tools/ShippingSeqParentGenD2MS.lean`, option `sparkle.sharedLeafCandidate`, default `false`).  For a call `k` of a machine `X` (`nP` own inputs), the
generated `X.machineExt` (bit-vector outputs) / `X.machineExtB` (Bool outputs) is a chain `extendBits (extendBits bits p₁ w₁ e₁) p₂ w₂ e₂ …` whose entry at the position `nP + k` is the call's value
`field (C a₁ … aₙ)`.  This module READS the arguments `aᵢ` of that call from the definition and returns the families the callee's source is applied to: the decoded families of the call's argument
`let`s with the callee's input positions overwritten by the arguments.  The elaborator only produces TEXT; every equation built from it is stated and checked by the kernel as a generated theorem
(`Tools.ShippingSeqParentGenD2MSG.decHaves`); if the text is wrong, that theorem fails and the generator falls back (unit SR18).  Nothing here is read from the old generated chain. -/
namespace Tools.ShippingSeqParentGenD2MSD
open Lean Elab Command Meta Term
open Tools.ShippingSeqParentGen (elabText)
open Tools.ShippingSeqParentGenD2 (readNats)

/-- (unit SR19) the DECODING EQUATIONS of one call, read from the generated `machineExt` / `machineExtB` of its caller: the argument `let`s, the families the callee source is applied to
(`aTxt`: the Bool family with `@BASEA@` = the decoded family, `bTxt`: the bit-vector family with `@BASEB@`), and the kinds of the callee's inputs in order (`true` = Bool). -/
structure CallDec where
  args : List Nat
  aTxt : String
  bTxt : String
  kinds : List Bool
deriving Repr


/-- the default value of a slot type (`false` / `0`) -/
noncomputable def tyDefault : (s : Tools.ShippingUnifiedSource.SType) → s.Type
  | .bool => default
  | .bits _ => default

/-- The default state tuple of a list of slot types, as nested pairs of the slot types' defaults: the same value as the instance term `instInhabitedProd` the old generated chain
carries for the machine (that term is only reachable once `machineData.ss` is unfolded; instance search does not unfold it).  Used for the `Inhabited (HList (tys ss))` instances of
the generic path instead of extracting the old chain's term. -/
noncomputable def defaultHList : (ss : List Tools.ShippingUnifiedSource.SType) → Sparkle.Core.HList (Tools.ShippingMachineDenote.tys ss)
  | [] => show Unit from ()
  | s :: ss => show Tools.ShippingUnifiedSource.SType.Type s × Sparkle.Core.HList (Tools.ShippingMachineDenote.tys ss) from (tyDefault s, defaultHList ss)

/-- the kind codes (`0` domain, `1` Bool, `w + 2` bits `w`) of a list of binders given as a Lean term of type `List (Name × MixedGateBinder)` -/
def kindCodes (binders : String) : TermElabM (List Nat) := do
  readNats (← elabText s!"(({binders}).map fun b => match b.2 with | Sparkle.Compiler.Elab.MixedGateBinder.domain => 0 | Sparkle.Compiler.Elab.MixedGateBinder.bool => 1 | Sparkle.Compiler.Elab.MixedGateBinder.bits w => w + 2)")

/-- the entries `(position, value)` of the chain `extendBits … bits` / `extendBools … bools` in the body of `X.machineExt` / `X.machineExtB` (innermost first); the pretty-printing context is the lambda telescope -/
partial def chainEntries (e : Expr) (isBits : Bool) : MetaM (List (Nat × Expr)) := do
  let e ← instantiateMVars e
  let args := e.getAppArgs
  if isBits && e.getAppFn.isConstOf ``Tools.ShippingMachineAuto.extendBits && args.size == 5 then
    let some pos := (← whnf args[2]!).rawNatLit? | throwError "chainEntries: position is not a literal"
    return (← chainEntries args[1]! isBits) ++ [(pos, args[4]!)]
  else if !isBits && e.getAppFn.isConstOf ``Tools.ShippingMachineCausal.extendBools && args.size == 4 then
    let some pos := (← whnf args[2]!).rawNatLit? | throwError "chainEntries: position is not a literal"
    return (← chainEntries args[1]! isBits) ++ [(pos, args[3]!)]
  else return []

/-- the decoding data of call `k` of `X` (callee `C`, its first `take` input binders, `none` = all): see the module header -/
def callDecOf (X C : Name) (nP k : Nat) (take : Option Nat) (args : List Nat) : TermElabM CallDec := do
  let xCodes ← kindCodes s!"{X}.machineData.bsIn"
  let some code := xCodes[nP + k]? | throwError "callDecOf: {X} has no binder at {nP + k}"
  let isBits := code ≥ 2
  if code == 0 then throwError "callDecOf: the output of call {k} of {X} is a domain"
  let tgt := match take with
    | some n => s!"(List.take {n} {C}.machineData.bsIn)"
    | none => s!"{C}.machineData.bsIn"
  let tcodes ← kindCodes tgt
  let ci ← getConstInfo (X ++ (if isBits then `machineExt else `machineExtB))
  let some v := ci.value? | throwError "callDecOf: {ci.name} has no value"
  lambdaTelescope v fun _ body => do
    let entries ← chainEntries body isBits
    let some (_, entry) := entries.find? (·.1 == nP + k)
      | throwError "callDecOf: no entry at position {nP + k} in {ci.name} (positions {entries.map (·.1)})"
    let some call := entry.find? fun x => x.isApp && x.getAppFn.isConstOf C
      | throwError "callDecOf: the entry of call {k} of {X} is not a call of {C}"
    let nExpl := (tcodes.filter (· != 0)).length
    let cargs := call.getAppArgs
    if cargs.size < nExpl then throwError "callDecOf: the call of {C} has {cargs.size} arguments, expected {nExpl} explicit ones"
    let expl := cargs.extract (cargs.size - nExpl) cargs.size
    let opts := (← getOptions).setBool `pp.fullNames true |>.setBool `pp.explicit false |>.setBool `pp.universes false
    let mut txts : Array String := #[]
    for a in expl do
      txts := txts.push (toString (← withOptions (fun _ => opts) (ppExpr a)))
    let mut aT := "@BASEA@"
    let mut bT := "@BASEB@"
    let mut kinds : List Bool := []
    let mut ai := 0
    for (c, j) in tcodes.zipIdx do
      if c == 0 then continue
      let t := txts[ai]!
      ai := ai + 1
      if c == 1 then
        aT := s!"(Tools.ShippingMachineCausal.extendBools {aT} {j} ({t}))"
        kinds := kinds ++ [true]
      else
        bT := s!"(Tools.ShippingMachineAuto.extendBits {bT} {j} {c - 2} ({t}))"
        kinds := kinds ++ [false]
    return { args := args, aTxt := aT, bTxt := bT, kinds := kinds }

end Tools.ShippingSeqParentGenD2MSD
