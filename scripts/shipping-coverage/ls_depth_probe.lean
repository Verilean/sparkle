import Sparkle

/-! # The file the REAL language server elaborates for the depth check (round par/k-depth)

WRITTEN, NOT RUN. Not part of any library; opened by
`scripts/shipping-coverage/ls_depth_probe.py` through `lake serve` (the text
is sent in `textDocument/didOpen`, with `MODE` and `HOLDMS` below replaced by
the script; the file on disk is never changed). Procedure and what counts as
"reproduced": `docs/parallel/K-depth-cell.md` §5.

`#ls_depth "<tag>" <mode> <holdMs> <decl>` is a wrapper command DEFINED HERE
(the compiler is not edited). It appends lines to
`.lake/build/gen/ls-depth/log.txt` — a FILE, because the diagnostics of a
cancelled elaboration are not published:

    <tag>@<t> ENTRY t=<ms> depth=<d> childCache=<n>     before the entry is called
    <tag>@<t> HOLD-START t=<ms> depth=<d>               inside the entry, at the child
    <tag>@<t> HOLD-END t=<ms> depth=<d>
    <tag>@<t> RETURNED t=<ms>                           the entry returned normally
    <tag>@<t> EXIT t=<ms> depth=<d>                     the command's finally (also on an interrupt)

and then runs the real `synthesizeCombinational <decl>`. With `holdMs > 0`
the run is made long INSIDE the entry through the public cell
`sparkleChildSynth`: the first child entry of the run waits `holdMs`
milliseconds (`mode` = `nocheck`: without a cancellation check, a stretch
with no Meta call; `mode` = `check`: polling `Core.checkInterrupted` every
10 ms, what code inside `whnf` / `inferType` does), then calls the real
`synthesizeChild`. At `HOLD-START` it also writes the marker file
`.lake/build/gen/ls-depth/entered`, which the script waits for before it
sends the edit.

The edit the script makes is in the definition `lsAnchor`, BEFORE the
commands: the old elaboration of the commands is cancelled and the new one
starts after the re-elaborated `lsAnchor`. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Lean Elab Command Meta

namespace LsDepthProbe

def logDir : String := ".lake/build/gen/ls-depth"

def appendLog (line : String) : IO Unit := do
  IO.FS.createDirAll logDir
  let h ← IO.FS.Handle.mk (logDir ++ "/log.txt") .append
  h.putStrLn line
  h.flush

/-- Wait `left` polls of 10 ms, with or without a cancellation check. -/
partial def hold (checks : Bool) (left : Nat) : MetaM Unit := do
  if checks then
    Core.checkInterrupted
  if left == 0 then
    return
  IO.sleep 10
  hold checks (left - 1)

/-- The child entry with one hold in front of it (the first call of the run). -/
def heldChild (run : String) (checks : Bool) (polls : Nat) (fired : IO.Ref Bool) (n : Name) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let f ← fired.get
  if !f then
    fired.set true
    let t ← IO.monoMsNow
    let d ← sparkleSynthDepth.get
    appendLog s!"{run} HOLD-START t={t} depth={d}"
    IO.FS.writeFile (logDir ++ "/entered") run
    try
      hold checks polls
    finally
      let t' ← IO.monoMsNow
      let d' ← sparkleSynthDepth.get
      appendLog s!"{run} HOLD-END t={t'} depth={d'}"
  synthesizeChild n

elab "#ls_depth " tag:str mode:ident ms:num id:ident : command => do
  let declName ← liftCoreM do
    Lean.resolveGlobalConstNoOverload id
  let t0 ← IO.monoMsNow
  let run := s!"{tag.getString}@{t0}"
  let checks := mode.getId == `check
  let d0 ← sparkleSynthDepth.get
  let c0 ← sparkleChildCache.get
  appendLog s!"{run} ENTRY t={t0} depth={d0} childCache={c0.size}"
  logInfo m!"LSDEPTH {run}: depth at entry {d0}, child cache {c0.size}"
  let fired ← IO.mkRef false
  if ms.getNat > 0 then
    sparkleChildSynth.set (some (heldChild run checks (ms.getNat / 10) fired))
  try
    liftTermElabM do
      let _ ← synthesizeCombinational declName
      pure ()
    let t1 ← IO.monoMsNow
    appendLog s!"{run} RETURNED t={t1}"
  finally
    let t2 ← IO.monoMsNow
    let d2 ← sparkleSynthDepth.get
    appendLog s!"{run} EXIT t={t2} depth={d2}"

@[hardware_module]
def kidL (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))

def topL (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  kidL x + x

@[hardware_module]
def kidQ (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 2#8 : Signal defaultDomain (BitVec 8))

def topQ (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  kidQ x + x

end LsDepthProbe

-- THE EDIT: the script changes the 0 of this line to 1 (nothing else).
def lsAnchor : Nat := 0

open LsDepthProbe in
#ls_depth "long" MODE HOLDMS LsDepthProbe.topL

open LsDepthProbe in
#ls_depth "quick" MODE 0 LsDepthProbe.topQ
