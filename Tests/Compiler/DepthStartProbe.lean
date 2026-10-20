import Tests.Compiler.ShippingMachineSeqTest

/-! # PROBE (logs only): is "a public command starts at depth 0" a fact of the process? (round par/g-1)

WRITTEN, NOT BUILT. TARGET-ONLY; not in `Tests.AllTests`. It asserts
nothing about the compiler and adds no declaration that another file uses.
Every `run_cmd` puts `sparkleSynthDepth` back to 0 and empties
`sparkleChildCache` in a `finally`.

The outermost endpoint (`Tests/Compiler/MixDeepOutermostEndpointTest.lean`)
takes `Start0 mref cref w`: for a law witness, the synthesis depth reads 0
at the start world. `docs/parallel/G-mixdeep-outermost.md` §5 argues by
READING that a public command's run starts with `sparkleSynthDepth = 0`:
the ref is created as 0, written only by the entry, and restored in the
entry's `finally`. That argument is about ONE thread of control. The ref is
an `initialize`d `IO.Ref`: one heap cell per PROCESS, visible to every
thread, and not owned by a command. This probe MEASURES the three facts the
reading leaves open:

* `DEPTH PROBE A` — a write made on ANOTHER thread (an `IO.asTask`) is read
  by the command's thread: the depth is process-global, not per-command and
  not per-thread. PREDICTED: reads 1.
* `DEPTH PROBE B` — the public entry `synthesizeCombinational`, called while
  the depth reads 1 (as it would if another elaboration thread of the same
  process were inside a synthesis), does NOT clear `sparkleChildCache`
  (PREDICTED: the cache size does not go to 0 before the run; the entry
  takes the nested branch) and leaves the depth at 1 (balanced).
* `DEPTH PROBE C` — the same call from depth 0, for comparison: the cache is
  cleared at entry (PREDICTED: afterwards it holds only what this run put
  there; for a leaf declaration, nothing) and the depth is 0 afterwards.

What the probe does NOT show: that two elaboration threads of one process
ever overlap in practice. By READING of the toolchain
(`Lean/Language/Lean.lean` of v4.32.1, lines 612 and 621: the old command
snapshots are cancelled with `cancelRec` and the new parse starts without
waiting; `Lean/CoreM.lean` 463: cancellation is cooperative,
`checkInterrupted`), in the LANGUAGE SERVER an edit made while a long
`#synthesizeVerilog` runs can start the next elaboration before the
cancelled one has reached its `finally`. Under `lake build` (one `lean`
process per file, commands in sequence) no such overlap is known to me. Not
reproduced: it needs the server. -/

open Sparkle.Compiler.Elab in
set_option maxHeartbeats 0 in
run_cmd do
  try
    sparkleSynthDepth.set 0
    let t ← IO.asTask (sparkleSynthDepth.set 1)
    let r ← IO.wait t
    let okWrite : Bool := match r with
      | Except.ok _ => true
      | Except.error _ => false
    let d ← sparkleSynthDepth.get
    Lean.logInfo m!"DEPTH PROBE A: another thread set sparkleSynthDepth to 1 (its task returned ok: {toString okWrite}); the command's thread now reads {d}. The ref is one cell of the process: neither per-command nor per-thread."
  finally
    sparkleSynthDepth.set 0

open Sparkle.Compiler.Elab in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let n := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let saved ← Lean.Meta.saveState
  try
    -- C first: an ordinary outermost run, then what it left in the child cache
    sparkleSynthDepth.set 0
    let _ ← synthesizeCombinational n
    let cacheC ← sparkleChildCache.get
    let sizeC : Nat := cacheC.size
    let depthC ← sparkleSynthDepth.get
    Lean.logInfo m!"DEPTH PROBE C: synthesizeCombinational {n} from depth 0: returned; depth afterwards {depthC}; sparkleChildCache holds {sizeC} entr(y/ies)"
    -- B: the same entry while the depth reads 1 (set by another thread)
    let cacheB0 ← sparkleChildCache.get
    let entryBefore : Nat := cacheB0.size
    let t ← IO.asTask (sparkleSynthDepth.set 1)
    let _ ← IO.wait t
    let depthIn ← sparkleSynthDepth.get
    let _ ← synthesizeCombinational n
    let cacheB ← sparkleChildCache.get
    let sizeB : Nat := cacheB.size
    let depthB ← sparkleSynthDepth.get
    Lean.logInfo m!"DEPTH PROBE B: synthesizeCombinational {n} called while the depth reads {depthIn}: returned; depth afterwards {depthB}; sparkleChildCache: {entryBefore} entr(y/ies) before the call, {sizeB} after. From depth 0 the entry empties this cache first; from a non-zero depth it does not, and the child entry it calls answers from the cache if the declaration is there."
  finally
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}
    saved.restore
