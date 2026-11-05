import Lean
import Sparkle
/-! # Recursors as iota rules: what `RecursorVal.rules` gives (D.D-4, issue sparkle-ledger-dd4-res)
Measurement only. For the recursors of the sample residue, print the data an iota rule is built from
(`numParams/numIndices/numMotives/numMinors/k`, the rules `(ctor, nfields, rhs)`), the sort the motive
ranges over, and whether the major premise is a proposition. Output: `logInfo` aggregates; raw rows go to
`$KJOB_REPORT_PATH.iota` if set. No theorem, no sorry. -/
open Lean Meta Elab Command

namespace Tests.Gen5.IotaStudy

def recNames : List Name :=
  [`Nat.rec, `Bool.rec, `Eq.rec, `False.rec, `Decidable.rec, `Nat.le.rec, `List.rec, `BitVec.rec,
   `PSigma.rec, `Prod.rec, `Int.rec, `And.rec, `Or.rec, `Exists.rec, `Option.rec, `Fin.rec, `Unit.rec, `PUnit.rec,
   `Sum.rec, `Sigma.rec, `Subtype.rec, `HEq.rec, `Acc.rec, `WellFounded.rec]

/-- Sort of the motive: the result sort of the type of the first motive binder. -/
def motiveSort (rv : RecursorVal) : MetaM String := do
  forallTelescope rv.type fun xs _ => do
    let i := rv.numParams
    if h : i < xs.size then
      let mty ← inferType xs[i]
      forallTelescope mty fun _ r => do
        return toString (← ppExpr r)
    else return "?"

elab "#iota_study" : command => do
  let env ← getEnv
  let mut msg := ""
  let mut raw := ""
  for n in recNames do
    match env.find? n with
    | some (.recInfo rv) =>
      let ms ← liftTermElabM (motiveSort rv)
      let ind := rv.getMajorInduct
      let isProp ← liftTermElabM do
        let some (.inductInfo iv) := env.find? ind | return "?"
        forallTelescope iv.type fun _ r => return toString (← ppExpr r)
      let rs := rv.rules.map fun r => s!"{r.ctor}/{r.nfields}"
      let line := s!"{n}: params={rv.numParams} indices={rv.numIndices} motives={rv.numMotives} minors={rv.numMinors} k={rv.k} lvls={rv.levelParams} motiveSort={ms} majorInductSort={isProp} rules={rs}"
      msg := msg ++ line ++ "\n"
      raw := raw ++ line ++ "\n"
      for r in rv.rules do
        let rhs ← liftTermElabM (do return toString (← ppExpr r.rhs))
        raw := raw ++ s!"  rule {r.ctor} nfields={r.nfields}: {rhs}\n"
    | _ => msg := msg ++ s!"{n}: not a recursor in this environment\n"
  logInfo msg
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    IO.FS.writeFile (path ++ ".iota") raw

#iota_study

end Tests.Gen5.IotaStudy
