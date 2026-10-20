import Lean.Elab.Command
import Tools.ShippingMachineCommand

/-! # Logging helpers of the Keccak tests and probes (round par/a-25)

WRITTEN, NOT BUILT. Meta code only: no theorem, no command, NO constant
about any Keccak declaration — so this file can be imported by
`OneOutWKeccakFTest` and by `KeccakSpongeStepProbe` (which must never be
imported together: both generate `wKeccakF.*`).

`clipStr`, `toFile`, `binderKindStr`, `describeRead` are the definitions of
the same names of `Tests/Compiler/KeccakProbeTest.lean` (BUILT and RUN,
`docs/parallel/B-keccak.md`, run record), restated here because that file
cannot be imported: it generates the Keccak constants. -/
namespace Tests.Compiler.KeccakSpongeLogLib
open Lean Meta Elab Command

/-- A long message, cut. -/
def clipStr (s : String) (n : Nat := 2000) : String :=
  if s.length ≤ n then s
  else (s.toList.take n).foldl (fun acc c => acc.push c) "" ++ " …[clipped]"

/-- One line to the progress file, at once (never fails): the file named by
`SPARKLE_MACHINE_PROGRESS` — the file the generators' own `progress` lines go
to (`Tools.ShippingMachineCommand.progress`) — else `fallback`. Each line has
a millisecond clock and the resident / peak memory of the process. -/
def toFile (fallback : String) (msg : String) : IO Unit := do
  try
    let path := (← IO.getEnv "SPARKLE_MACHINE_PROGRESS").getD fallback
    let status ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
    let rss := (status.splitOn "\n").find? (·.startsWith "VmRSS") |>.getD ""
    let hwm := (status.splitOn "\n").find? (·.startsWith "VmHWM") |>.getD ""
    let now ← IO.monoMsNow
    let h ← IO.FS.Handle.mk path IO.FS.Mode.append
    h.putStrLn s!"{now} {msg} [{rss}] [{hwm}]"
    h.flush
  catch _ => pure ()

/-- Is the generators' progress variable set? (When it is not, the
generators write NO progress line: `progress` is a no-op.) -/
def progressSet : IO Bool := do
  return (← IO.getEnv "SPARKLE_MACHINE_PROGRESS").isSome

def binderKindStr (b : Sparkle.Compiler.Elab.MixedGateBinder) : String :=
  match b with
  | Sparkle.Compiler.Elab.MixedGateBinder.domain => "domain"
  | Sparkle.Compiler.Elab.MixedGateBinder.bool => "bool"
  | Sparkle.Compiler.Elab.MixedGateBinder.bits w => s!"bits {w}"

/-- The reader's data of a declaration, as one line. -/
def describeRead (r : Tools.ShippingMachineCommand.Read) : String :=
  let sh := r.shape
  let declKinds : List String := (sh.binders.take r.nDecl).map fun b => binderKindStr b.2
  let slotWs : List Nat := sh.layout.slots.map fun s => s.width
  let stateBits : Nat := slotWs.foldl (fun a w => a + w) 0
  let outs : List String := sh.layout.outs.map fun o => s!"{o.name}:{o.width}"
  let callees : List Name := (sh.insts.map fun i => i.1).eraseDups
  let groups : List (Name × List Nat) := (sh.insts.map fun i => (i.1, i.2.1)).eraseDups
  let groupStrs : List String := groups.map fun g => s!"{g.1} with argument lets {g.2}"
  let results : List String := sh.insts.map fun i => binderKindStr i.2.2
  s!"nDecl={r.nDecl}; declared binders {declKinds}; binders={sh.binders.length}; slots={sh.layout.slots.length} of widths {slotWs} ({stateBits} state bits); lets={sh.layout.lets}; runs={sh.runs}; loops={sh.loops}; rootLets={r.rootLets}; hasOuter={r.hasOuter}; nested={r.nested}; call entries={sh.insts.length} with result kinds {results}; distinct callees {callees}; distinct (callee, argument lets) groups ({groups.length}): {groupStrs}; instFields ({sh.instFields.length}): {sh.instFields}; outputs ({sh.layout.outs.length}): {outs}; outNames {r.outNames}; tuple result: {r.tuple.isSome}"

end Tests.Compiler.KeccakSpongeLogLib
