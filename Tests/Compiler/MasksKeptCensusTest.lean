import Tests.Compiler.HierBindsCensusTest

/-! # Does the masks guard of `mergeChecked` ever fire? (branch `fix/opt-fallback`)

Compiled evidence, LOGS ONLY (prefix `MASKSKEPT`) — nothing here throws and
nothing is a theorem. A column added to the census of
`Tests/Compiler/HierBindsCensusTest.lean` (its `candidates`), in a file of
its own.

`Sparkle.IR.RefineCheck.mergeChecked` keeps a register merge only if
`refineCheck` accepts it AND `masksKept` holds (no output that was masked —
assigned once, by a constant or a slice no wider than the port — lost its
mask); otherwise the module is returned unmerged (a fallback, never a
rejection).

For every candidate declaration: the CORE entry is run
(`synthesizeCombinationalCore`), its module cleaned (`dropZeroWidthModule`,
`z`), `r = mergeDuplicates z`, and

* `fired`: the body is not assignment-only, `refineCheck z r` accepts and
  `masksKept z r` refuses — the guard changes what is shipped;
* `mergeChanged`: `r != z`;
* `masked`: every output of `z` is masked (`outMaskedB`).

CAVEAT (as on the branch `fix/merge-guards`): this is a run of the core
entry outside the full entry; a failure is logged as such.

Then the totals line `MASKSKEPT CENSUS: …` (expected: fired 0), and the
guard on a hand-built module where the merge turns the output's slice into
an alias (expected: `masksKept` false, `mergeChecked` returns the input). -/
namespace Tests.Compiler.MasksKeptCensusTest
open Lean Meta

/-- `(fired, mergeChanged, masked)` of a declaration. -/
def row (f : Name) : MetaM (Bool × Bool × Bool) := do
  let (M, _) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore f [] false
  let z := Sparkle.IR.ZeroWidth.dropZeroWidthModule M
  let r := Sparkle.IR.RegDedup.mergeDuplicates z
  let fired := !(z.body.all Sparkle.IR.RegDedup.isAssign) &&
    Sparkle.IR.RefineCheck.refineCheck z r && !Sparkle.IR.RefineCheck.masksKept z r
  let masked := z.outputs.all fun p =>
    Sparkle.IR.RefineCheck.outMaskedB (Sparkle.IR.RegDedup.declWidth z) z.body p
  return (fired, r != z, masked)

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut total := 0
  let mut fired : List Name := []
  let mut changed := 0
  let mut absent := 0
  let mut failed : List Name := []
  for n in Tests.Compiler.HierBindsCensusTest.candidates do
    if !env.contains n then
      absent := absent + 1
      logInfo m!"MASKSKEPT {n}: ABSENT (no such declaration in this build)"
    else
      try
        let (f, c, m) ← row n
        total := total + 1
        if f then fired := fired ++ [n]
        if c then changed := changed + 1
        logInfo m!"MASKSKEPT {n}: fired={f} mergeChanged={c} masked={m}"
      catch e =>
        failed := failed ++ [n]
        logInfo m!"MASKSKEPT {n}: CORE RUN FAILED: {e.toMessageData}"
  logInfo m!"MASKSKEPT CENSUS: {total} declarations ({absent} absent, {failed.length} failed {failed}); masksKept fires on {fired.length} {fired}; the merge changes {changed}"

/-! ## A hand-built module on which the guard fires -/

def sl : Sparkle.IR.AST.Expr := .slice (.ref "x") 7 0

def mOut : Sparkle.IR.AST.Module :=
  { name := "m", inputs := [], outputs := [{ name := "out", ty := .bitVector 8 }],
    wires := [{ name := "x", ty := .bitVector 16 }, { name := "t", ty := .bitVector 8 }],
    body := [.assign "t" sl, .assign "out" sl] }

def mReg : Sparkle.IR.AST.Module :=
  { mOut with
    wires := mOut.wires ++ [{ name := "r", ty := .bitVector 8 }],
    body := mOut.body ++ [.register "r" "clk" ("rst", .synchronous) (.ref "t") 0] }

#eval IO.println s!"MASKSKEPT hand: refineCheck accepts the merge = {Sparkle.IR.RefineCheck.refineCheck mReg (Sparkle.IR.RegDedup.mergeDuplicates mReg)}, masksKept = {Sparkle.IR.RefineCheck.masksKept mReg (Sparkle.IR.RegDedup.mergeDuplicates mReg)}, mergeChecked returns the input = {Sparkle.IR.RefineCheck.mergeChecked mReg == mReg}"

end Tests.Compiler.MasksKeptCensusTest
