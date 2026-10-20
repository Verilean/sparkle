import Tests.Compiler.MachineFallThroughCensusTest
import Tools.ShippingCallShadow

/-! # The shadow census of call kinds (findings A, A') — on the EXISTING reader

Compiled evidence, LOGS ONLY — nothing here throws and nothing is a theorem.
No synthesis is run and no compiler definition is changed: the pure readers
and `Tools.ShippingCallShadow` only.

Population: the 37 census declarations, the hunt's parents and children,
and the environment sweep of `MachineFallThroughCensusTest`. For every
declaration whose entry constant has a machine shape
(`machineShape? … = some shape`, the shipping reader):

    SHADOW <name>: gate=<T/F> calls=<n> unknown=<n> [children] known=<n>
      resKind=<n> fieldMissing=<n> fieldDup=<n> argCount=<n> argKind=<n>
      declInlDiffer=[children] overDecline=<n> own=<outs T/F/unknown>,<ins T/F/unknown> diffs=[…]

* `gate`: a certified gate accepts the entry constant (the declaration is
  then NOT on the machine route; its shape is still read here);
* `unknown`: call entries whose child has NO selected signature — nothing
  was compared for them. They are neither agreements nor disagreements;
* `known`: entries compared with the child's selected signature; the next
  five columns count, among them, a result-kind difference, a missing
  field, a field occurring twice, an argument-count difference, an
  argument-kind difference (counts equal);
* `declInlDiffer`: children whose declared and inlined signatures both
  exist and differ;
* `overDecline`: entries that agree with the selected signature while the
  OTHER signature (not the one the child's entry uses) disagrees — what a
  rule demanding agreement with both would refuse without cause;
* `own`: the shape's layout outputs / hardware binders against its own
  entry constant's signature.

Totals, with the names behind every non-zero count:

    SHADOW CENSUS: shapes n (machine-shaped without a gate m); call entries e; UNKNOWN u [children]; known k; …

A zero in the disagreement columns says the two readings agreed on the
compared entries of this population. It is not a proof for other sources,
and says nothing about the unknown entries.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.CallShadowCensusTest
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingCallShadow
open Tests.Compiler.CallWidthHuntTest (bs huntParents huntChildren)

/-- One shape's counts. -/
structure Row where
  gate : Bool
  calls : Nat
  unknown : Nat
  unknownKids : List Name
  known : Nat
  resKind : Nat
  fieldMissing : Nat
  fieldDup : Nat
  argCount : Nat
  argKind : Nat
  differKids : List Name
  overDecline : Nat
  own : String
  ownBad : Bool
  diffs : List String

def Row.bad (r : Row) : Bool :=
  r.resKind != 0 || r.fieldMissing != 0 || r.fieldDup != 0 || r.argCount != 0 || r.argKind != 0

def Row.str (r : Row) : String :=
  s!"gate={bs r.gate} calls={r.calls} unknown={r.unknown} {r.unknownKids} known={r.known} " ++
  s!"resKind={r.resKind} fieldMissing={r.fieldMissing} fieldDup={r.fieldDup} " ++
  s!"argCount={r.argCount} argKind={r.argKind} declInlDiffer={r.differKids} " ++
  s!"overDecline={r.overDecline} own={r.own} diffs={r.diffs}"

def cnt (rs : List (Nat × Name × EntryReport)) (p : EntryReport → Bool) : Nat :=
  (rs.filter fun r => p r.2.2).length

def kidsOf (rs : List (Nat × Name × EntryReport)) (p : EntryReport → Bool) : List Name :=
  ((rs.filter fun r => p r.2.2).map (·.2.1)).eraseDups

/-- One declaration: `none` when its entry constant has no machine shape. -/
def census (n : Name) : MetaM (Option Row) := do
  let ci ← getConstInfo n
  let env ← getEnv
  let senv := structEnv env
  let ec := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
  let some shape := machineShape? false [] ec senv | return none
  let gate := (certifiedShape? false [] ec).isSome ||
    (mixedCertifiedShape? false [] ec (instancePredicate env)).isSome
  let rs := shadowReports env shape
  let known := rs.filter fun r => !r.2.2.unknown
  let own := shadowOwnAgrees env ec shape
  let ownStr := match own with
    | some (o, i) => s!"{bs o},{bs i}"
    | none => "unknown,unknown"
  let ownBad := match own with
    | some (o, i) => !o || !i
    | none => false
  let diffs := (rs.filter fun r => r.2.2.sel.any || r.2.2.other.any).map fun r =>
    s!"{r.1} {r.2.1}: sel(missing={bs r.2.2.sel.fieldMissing} dup={bs r.2.2.sel.fieldDup} " ++
    s!"res={bs r.2.2.sel.resKind} count={bs r.2.2.sel.argCount} kind={bs r.2.2.sel.argKind}) " ++
    s!"other(any={bs r.2.2.other.any})"
  return some {
    gate := gate
    calls := rs.length
    unknown := cnt rs (·.unknown)
    unknownKids := kidsOf rs (·.unknown)
    known := known.length
    resKind := cnt known (·.sel.resKind)
    fieldMissing := cnt known (·.sel.fieldMissing)
    fieldDup := cnt known (·.sel.fieldDup)
    argCount := cnt known (·.sel.argCount)
    argKind := cnt known (·.sel.argKind)
    differKids := kidsOf rs (·.declInlDiffer)
    overDecline := cnt known (·.overDecline)
    own := ownStr
    ownBad := ownBad
    diffs := diffs }

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let lists := Tests.Compiler.PrintArtifactCensusTest.candidates ++ huntParents ++ huntChildren
  let swept :=
    if Tests.Compiler.MachineFallThroughCensusTest.envSweep then
      (Tests.Compiler.MachineFallThroughCensusTest.sweepNames env).filter
        (fun n => !lists.contains n)
    else []
  let all := lists ++ swept
  let mut rows : List (Name × Row) := []
  let mut noShape : Nat := 0
  let mut failed : List Name := []
  for n in all do
    if env.contains n then
      try
        match ← census n with
        | none => noShape := noShape + 1
        | some r =>
          rows := rows ++ [(n, r)]
          if r.calls != 0 || r.ownBad then logInfo m!"SHADOW {n}: {r.str}"
      catch e =>
        failed := failed ++ [n]
        logInfo m!"SHADOW {n}: FAILED: {e.toMessageData}"
  let sum (f : Row → Nat) : Nat := rows.foldl (fun a x => a + f x.2) 0
  let names (p : Row → Bool) : List Name := (rows.filter fun x => p x.2).map (·.1)
  let kids (f : Row → List Name) : List Name := (rows.flatMap fun x => f x.2).eraseDups
  let line : String :=
    s!"SHADOW CENSUS: shapes {rows.length} (machine-shaped without a gate " ++
    s!"{(rows.filter fun x => !x.2.gate).length}); declarations without a shape {noShape}; " ++
    s!"call entries {sum (·.calls)}; UNKNOWN signature (not compared) {sum (·.unknown)} " ++
    s!"{kids (·.unknownKids)}; known {sum (·.known)}; " ++
    s!"result-kind differences {sum (·.resKind)} {names (fun r => r.resKind != 0)}; " ++
    s!"missing field {sum (·.fieldMissing)} {names (fun r => r.fieldMissing != 0)}; " ++
    s!"duplicated field {sum (·.fieldDup)} {names (fun r => r.fieldDup != 0)}; " ++
    s!"argument-count differences {sum (·.argCount)} {names (fun r => r.argCount != 0)}; " ++
    s!"argument-kind differences {sum (·.argKind)} {names (fun r => r.argKind != 0)}; " ++
    s!"children whose declared and inlined signatures differ {kids (·.differKids)}; " ++
    s!"over-declines of an agree-with-both rule {sum (·.overDecline)} " ++
    s!"{names (fun r => r.overDecline != 0)}; " ++
    s!"own-interface differences {names (fun r => r.ownBad)}; failed {failed.length} {failed}"
  logInfo m!"{line}"

end Tests.Compiler.CallShadowCensusTest
