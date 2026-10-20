import Tests.Compiler.HierBindsCensusTest
import Tools.ShippingPrintGuard

/-! # The print guard of `mergeChecked`: hand-built cases and a census (round par/a-1)

`Sparkle.IR.RefineCheck.mergeChecked` keeps the merge of a body that is not
assignments only when `refineCheck` accepts it, `masksKept` holds AND the
merged module passes `Sparkle.IR.PrintGuard.printOk`; otherwise the module
is returned unmerged (a fallback, never a rejection).

## Hand-built (a failure throws)

* `mFire`: `t` and `u` are the same slice of an input (the merge makes `u`
  an alias of `t` and renames its readers), a register reads `u`, and
  `n = ~(t * u)` — the NOT of a product, outside the emitter's forward
  fragment. The REAL merge (`mergeDuplicates mFire`) changes the module;
  `refineCheck` accepts it; `masksKept` holds; `printOk` refuses it: the
  print guard ALONE makes `mergeChecked mFire = mFire`.
* `mKeep`: the same with `n = t + u`: the merge passes the three checks,
  `mergeChecked mKeep` is the merge, and it passes `printOk`.

Both satisfy the statement of `mergeChecked_print`, evaluated.

WHAT THE FIRING CASE DOES NOT SHOW: `mFire` itself fails `printOk` (logged).
No module was found, by reading `Sparkle/IR/RegDedup.lean`, that passes
`printOk` while its merge fails it: the merged body is the input's
statements with references renamed to the first member of their class, plus
aliases `n = rep`; a class joins nodes with the same right-hand side
(references taken up to class), and `printOk`'s statement arms pin each
node's declared width to its right-hand side's — so on a module passing
`printOk` the renamed references and the aliases have equal widths. On such
inputs the guard is expected never to fire; where it fires the fallback's
guarantee is the first disjunct of `mergeChecked_print` — the shipped
module is the cleaned module itself, the one the run-derived facts
(`leaf_run_typedIn`: `TypedIn m0`) are about.

## Census (LOGS ONLY, prefix `MERGEPRINT`)

Over the candidates of `HierBindsCensusTest` AND the declarations they call
(`readMachine`'s `insts`, transitively): the CORE entry is run, its module
cleaned (`z`), `r = mergeDuplicates z`, and

* `fires`: the body is not assignments only, `refineCheck z r` and
  `masksKept z r` accept, `printOk r` refuses — the print guard changes what
  is shipped;
* `accepted`: the first three hold; `mergeChanged`: `r != z`;
  `printOk z`: the cleaned module itself.

CAVEAT (as `MasksKeptCensusTest`): a run of the core entry outside the full
entry. Expected: fires on 0.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.MergePrintGuardTest
open Sparkle.IR.AST

def b8 (n : String) : Port := { name := n, ty := .bitVector 8 }
def b16 (n : String) : Port := { name := n, ty := .bitVector 16 }

def sl : Expr := .slice (.ref "x") 7 0

/-- The module around the node `n`. -/
def mk (name : String) (nRhs : Expr) : Module :=
  { name := name, inputs := [b16 "x"], outputs := [b8 "out"],
    wires := [b16 "x", b8 "t", b8 "u", b8 "n", b8 "r"],
    body := [.assign "t" sl, .assign "u" sl, .assign "n" nRhs,
             .assign "out" (.slice (.ref "n") 7 0),
             .register "r" "clk" ("rst", .synchronous) (.ref "u") 0] }

/-- The print guard fires: `n = ~(t * u)`. -/
def mFire : Module := mk "pq" (.op .not [.op .mul [.ref "t", .ref "u"]])

/-- The merge is kept: `n = t + u`. -/
def mKeep : Module := mk "pk" (.op .add [.ref "t", .ref "u"])

def note (name : String) (ok : Bool) (bad : Array String) : Array String :=
  if ok then bad else bad.push name

open Lean Elab Command in
run_cmd liftTermElabM do
  let mut bad : Array String := #[]
  let pOk := Sparkle.IR.PrintGuard.printOk
  let rc := Sparkle.IR.RefineCheck.refineCheck
  let mkp := Sparkle.IR.RefineCheck.masksKept
  let mc := Sparkle.IR.RefineCheck.mergeChecked
  -- the guard fires
  let m := mFire
  let r := Sparkle.IR.RegDedup.mergeDuplicates m
  logInfo m!"MERGEPRINT hand/fire: merge!=input={r != m} refineCheck={rc m r} masksKept={mkp m r} printOk(merge)={pOk r} printOk(input)={pOk m} mergeChecked==input={mc m == m}"
  bad := note "fire: the merge changes the module" (r != m) bad
  bad := note "fire: refineCheck accepts the merge" (rc m r) bad
  bad := note "fire: masksKept accepts the merge" (mkp m r) bad
  bad := note "fire: printOk refuses the merge" (!pOk r) bad
  bad := note "fire: mergeChecked returns the input" (mc m == m) bad
  bad := note "fire: mergeChecked_print's statement" (mc m == m || pOk (mc m)) bad
  -- the merge is kept
  let m := mKeep
  let r := Sparkle.IR.RegDedup.mergeDuplicates m
  logInfo m!"MERGEPRINT hand/keep: merge!=input={r != m} refineCheck={rc m r} masksKept={mkp m r} printOk(merge)={pOk r} printOk(input)={pOk m} mergeChecked==merge={mc m == r}"
  bad := note "keep: the merge changes the module" (r != m) bad
  bad := note "keep: refineCheck accepts the merge" (rc m r) bad
  bad := note "keep: masksKept accepts the merge" (mkp m r) bad
  bad := note "keep: printOk accepts the merge" (pOk r) bad
  bad := note "keep: mergeChecked is the merge" (mc m == r) bad
  bad := note "keep: the shipped module passes printOk" (pOk (mc m)) bad
  unless bad.isEmpty do
    throwError "MERGEPRINT FAILED ({bad.size}): {bad}"
  logInfo m!"MERGEPRINT: on mFire the print guard alone (refineCheck and masksKept accept) returns the input module; on mKeep the merge is kept and passes printOk"

/-- `(fires, accepted, mergeChanged, printOk z)` of a declaration's core run. -/
def row (f : Lean.Name) : Lean.MetaM (Bool × Bool × Bool × Bool) := do
  let (M, _) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore f [] false
  let z := Sparkle.IR.ZeroWidth.dropZeroWidthModule M
  let r := Sparkle.IR.RegDedup.mergeDuplicates z
  let accepted := !(z.body.all Sparkle.IR.RegDedup.isAssign) &&
    Sparkle.IR.RefineCheck.refineCheck z r && Sparkle.IR.RefineCheck.masksKept z r
  return (accepted && !Sparkle.IR.PrintGuard.printOk r, accepted, r != z,
    Sparkle.IR.PrintGuard.printOk z)

/-- The declarations a declaration calls (none where it is not read as a machine). -/
def callees (f : Lean.Name) : Lean.MetaM (List Lean.Name) := do
  try
    let r ← Tools.ShippingMachineCommand.readMachine f true
    return (r.shape.insts.map (·.1)).eraseDups
  catch _ => return []

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let cands := Tests.Compiler.HierBindsCensusTest.candidates.filter (fun n => env.contains n)
  -- the called declarations, transitively (three levels are enough here)
  let mut kids : List Name := []
  let mut frontier := cands
  for _ in [0:4] do
    let mut next : List Name := []
    for n in frontier do
      for k in ← callees n do
        if env.contains k && !cands.contains k && !kids.contains k && !next.contains k then
          next := next ++ [k]
    kids := kids ++ next
    frontier := next
  let mut total := 0
  let mut fired : List Name := []
  let mut accepted := 0
  let mut changed := 0
  let mut badZ := 0
  let mut failed : List Name := []
  for (n, kind) in cands.map (fun n => (n, "candidate")) ++ kids.map (fun n => (n, "child")) do
    try
      let (f, a, c, pz) ← row n
      total := total + 1
      if f then fired := fired ++ [n]
      if a then accepted := accepted + 1
      if c then changed := changed + 1
      unless pz do badZ := badZ + 1
      logInfo m!"MERGEPRINT {n} ({kind}): fires={f} accepted={a} mergeChanged={c} printOk(cleaned)={pz}"
    catch e =>
      failed := failed ++ [n]
      logInfo m!"MERGEPRINT {n} ({kind}): CORE RUN FAILED: {e.toMessageData}"
  logInfo m!"MERGEPRINT CENSUS: {total} declarations ({cands.length} candidates, {kids.length} called declarations {kids}; {failed.length} failed {failed}); the print guard of mergeChecked fires on {fired.length} {fired}; refineCheck and masksKept accept the merge of a register body on {accepted}; the merge changes {changed}; printOk false on the cleaned module: {badZ}"

end Tests.Compiler.MergePrintGuardTest
