/-
  JIT co-sim of the generated hardware for the plain UART blocks
  `IP.Net.UART.uartTxHW` and `uartRxHW`, checked cycle by cycle (the existing
  UARTTest only runs one byte of the loopback through the Signal interpreter
  and looks for "some rxValid pulse").

  TX (`txTop`): inputs txByte = 0, txValid = 1, bitDiv = 2; outputs txLine = 0,
  txReady = 1.  Four bytes are sent (one after the idle line, one issued on the
  first cycle `txReady` is back high, one pulse while busy that must be ignored
  with a changed `txByte` that must not corrupt the frame, one after idle).
  Checked: every bit slot of every frame held for all its cycles (decoded with
  `UartHWJIT.decodeFrames`), the decoded bytes = the bytes sent, no extra
  frame, `txReady` high at reset and while idle, one low run per frame that
  covers the whole frame and starts at the accepted request, ends within 2
  cycles of the stop slot.

  RX (`rxTop`): inputs rxLine = 0, bitDiv = 1; outputs rxByte = 0, rxValid = 1.
  Frames are driven back to back and with gaps.  Checked: `rxValid` is a
  1-cycle pulse, exactly one per good frame inside its stop slot window,
  `rxByte` at the pulse = the byte sent, none before the first frame, none in
  the idle tail.

  NOT checked: baud mismatch tolerance, break / glitch handling (see the
  separate run labelled "framing error").
  Synthetic controls for both checkers run first (no JIT): each defect below is
  rejected.
-/
import IP.Net.UART
import Sparkle.Compiler.Elab
import Tests.IP.Crypto.UartHWJITHarness

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Net.UART
open Sparkle.Tests.IP.Crypto.UartHWJIT

namespace Sparkle.Tests.IP.Net.UartHWJITTest

set_option maxRecDepth 100000

def txTop (txByte : Signal defaultDomain (BitVec 8)) (txValid : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) : TxOut defaultDomain :=
  uartTxHW txByte txValid bitDiv

def rxTop (rxLine : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) : RxOut defaultDomain :=
  uartRxHW rxLine bitDiv

#sim txTop
#sim rxTop

/-! ## Pure checkers -/

/-- Maximal runs of `false` in `ready`: (first cycle, one past the last). -/
def lowRuns (ready : Array Bool) : Array (Nat × Nat) := Id.run do
  let mut r : Array (Nat × Nat) := #[]
  let mut st : Option Nat := none
  for i in [0:ready.size] do
    match st with
    | none => if !ready[i]! then st := some i
    | some a => if ready[i]! then do r := r.push (a, i); st := none
  if let some a := st then r := r.push (a, ready.size)
  return r

/-- TX trace check: `line`/`ready` sampled per cycle, `accepts[i]` the cycle the
    i-th expected frame was requested (txValid pulse while ready), `expect` the
    bytes.  Returns violations. -/
def txErrors (line ready : Array Bool) (cpb : Nat) (accepts expect : Array Nat) :
    Array String := Id.run do
  let f := decodeFrames line cpb
  let mut errs := f.errors
  if f.bytes != expect then
    errs := errs.push s!"decoded bytes {f.bytes.toList} ≠ sent {expect.toList}"
  if ready.size > 0 && !ready[0]! then errs := errs.push "txReady low at cycle 0"
  let runs := lowRuns ready
  if runs.size != expect.size then
    errs := errs.push s!"txReady has {runs.size} low runs, expected {expect.size} (one per frame)"
  else
    for i in [0:runs.size] do
      let (a, b) := runs[i]!
      if i < f.starts.size then
        let s := f.starts[i]!
        if a > s then errs := errs.push s!"frame {i}: txReady falls at {a}, after the start bit at {s}"
        if a < accepts[i]! then errs := errs.push s!"frame {i}: txReady falls at {a}, before the request at {accepts[i]!}"
        if a > accepts[i]! + 2 then errs := errs.push s!"frame {i}: txReady falls at {a}, > 2 cycles after the request at {accepts[i]!}"
        if b < s + 10 * cpb then errs := errs.push s!"frame {i}: txReady rises at {b}, before the frame ends at {s + 10 * cpb}"
        if b > s + 10 * cpb + 2 then errs := errs.push s!"frame {i}: txReady rises at {b}, > 2 cycles after the frame ends at {s + 10 * cpb}"
  return errs

/-- RX trace check.  `starts[i]` = first low cycle of frame i, `expect[i]` = the
    byte that must be reported (`none` = no valid pulse may occur). -/
def rxErrors (valid : Array Bool) (byte : Array Nat) (cpb : Nat)
    (starts : Array Nat) (expect : Array (Option Nat)) : Array String := Id.run do
  let mut errs : Array String := #[]
  -- valid runs: pulses must be 1 cycle wide
  let mut ev : Array Nat := #[]
  for i in [0:valid.size] do
    if valid[i]! then
      if i > 0 && valid[i-1]! then errs := errs.push s!"rxValid high for more than 1 cycle at {i}"
      else ev := ev.push i
  for i in [0:starts.size] do
    let lo := starts[i]!
    let hi := if i + 1 < starts.size then starts[i+1]! else valid.size
    let got := ev.filter (fun c => lo ≤ c && c < hi)
    match expect[i]! with
    | some b =>
      if got.size != 1 then errs := errs.push s!"frame {i}: {got.size} rxValid pulses (expected 1)"
      else
        let c := got[0]!
        if byte[c]! != b then errs := errs.push s!"frame {i}: rxByte 0x{String.ofList (Nat.toDigits 16 byte[c]!)} ≠ sent 0x{String.ofList (Nat.toDigits 16 b)}"
        if c < lo + 9 * cpb || c > lo + 10 * cpb + 2 then
          errs := errs.push s!"frame {i}: rxValid at {c} outside the stop-slot window [{lo + 9 * cpb}, {lo + 10 * cpb + 2}]"
    | none =>
      if got.size != 0 then errs := errs.push s!"frame {i}: {got.size} rxValid pulse(s) for a frame with a low stop bit"
  if starts.size > 0 then
    let early := ev.filter (· < starts[0]!)
    if !early.isEmpty then errs := errs.push s!"rxValid before the first frame at {early.toList}"
  else if !ev.isEmpty then errs := errs.push "rxValid with no frame sent"
  return errs

/-! ## Synthetic controls -/

def cpbC : Nat := 8

def lineOf (bs : List Nat) (idle : Nat) : Array Bool := Id.run do
  let mut s : Array Bool := Array.replicate idle true
  for v in bs do
    s := s ++ Array.replicate cpbC false
    for i in [0:8] do s := s ++ Array.replicate cpbC (((v >>> i) &&& 1) == 1)
    s := s ++ Array.replicate cpbC true
  return s ++ Array.replicate 40 true

/-- ready trace matching `lineOf`: low from the request (cycle 10, one cycle before
    the start bit at 11) for 10·cpb+1 cycles. -/
def readyOf (n : Nat) : Array Bool := Id.run do
  let mut s := Array.replicate 10 true
  for _ in [0:n] do s := s ++ Array.replicate (10 * cpbC + 1) false
  return s ++ Array.replicate 40 true

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  {if cond then "✓" else "✗"} {name}"
  pure cond

def controls : IO Bool := do
  IO.println "-- synthetic controls (checker must accept the clean trace and reject each defect)"
  let mut ok := true
  let line := lineOf [0x5A] 11
  let rdy := readyOf 1
  ok := (← check "TX clean trace accepted" (txErrors line rdy cpbC #[10] #[0x5A]).isEmpty) && ok
  ok := (← check "TX extra frame rejected"
    (!(txErrors (lineOf [0x5A, 0x00] 11) rdy cpbC #[10] #[0x5A]).isEmpty)) && ok
  ok := (← check "TX wrong byte rejected" (!(txErrors (lineOf [0x5B] 11) rdy cpbC #[10] #[0x5A]).isEmpty)) && ok
  ok := (← check "TX 1-cycle glitch in stop bit rejected"
    (!(txErrors (line.modify (11 + 9 * cpbC + 3) (!·)) rdy cpbC #[10] #[0x5A]).isEmpty)) && ok
  ok := (← check "TX txReady stuck high rejected"
    (!(txErrors line (Array.replicate rdy.size true) cpbC #[10] #[0x5A]).isEmpty)) && ok
  ok := (← check "TX txReady rises 5 cycles early rejected"
    (!(txErrors line (readyOf 1 |>.modify (11 + 10 * cpbC - 5) (fun _ => true)) cpbC #[10] #[0x5A]).isEmpty)) && ok
  ok := (← check "TX txReady falls late (4 cycles after request) rejected"
    (!(txErrors line (readyOf 1 |>.modify 12 (fun _ => true) |>.modify 13 (fun _ => true) |>.modify 14 (fun _ => true)) cpbC #[10] #[0x5A]).isEmpty)) && ok
  -- RX: valid pulse at the stop slot of a frame starting at cycle 11
  let nC := 11 + 10 * cpbC + 40
  let pulse := fun (c : Nat) => (Array.replicate nC false).set! c true
  let bytes := fun (b : Nat) => Array.replicate nC b
  let c0 := 11 + 9 * cpbC + 4
  ok := (← check "RX clean pulse accepted"
    (rxErrors (pulse c0) (bytes 0x5A) cpbC #[11] #[some 0x5A]).isEmpty) && ok
  ok := (← check "RX missing pulse rejected"
    (!(rxErrors (Array.replicate nC false) (bytes 0x5A) cpbC #[11] #[some 0x5A]).isEmpty)) && ok
  ok := (← check "RX duplicate pulse rejected"
    (!(rxErrors ((pulse c0).set! (c0 + 6) true) (bytes 0x5A) cpbC #[11] #[some 0x5A]).isEmpty)) && ok
  ok := (← check "RX 2-cycle-wide pulse rejected"
    (!(rxErrors ((pulse c0).set! (c0 + 1) true) (bytes 0x5A) cpbC #[11] #[some 0x5A]).isEmpty)) && ok
  ok := (← check "RX wrong byte rejected"
    (!(rxErrors (pulse c0) (bytes 0x5B) cpbC #[11] #[some 0x5A]).isEmpty)) && ok
  ok := (← check "RX pulse too early (start-bit time) rejected"
    (!(rxErrors (pulse (11 + 2 * cpbC)) (bytes 0x5A) cpbC #[11] #[some 0x5A]).isEmpty)) && ok
  ok := (← check "RX pulse before the first frame rejected"
    (!(rxErrors (pulse 3) (bytes 0x5A) cpbC #[11] #[none]).isEmpty)) && ok
  ok := (← check "RX pulse for a low-stop-bit frame rejected"
    (!(rxErrors (pulse c0) (bytes 0x5A) cpbC #[11] #[none]).isEmpty)) && ok
  pure ok

/-! ## JIT runs -/

structure TxTrace where
  line : Array Bool := #[]
  ready : Array Bool := #[]
  accepts : Array Nat := #[]

def txStep (h : JITHandle) (t : IO.Ref TxTrace) (byte : Nat) (valid : Bool) : IO Unit := do
  JIT.setInput h 0 (UInt64.ofNat byte)
  JIT.setInput h 1 (if valid then 1 else 0)
  JIT.eval h
  let l := (← JIT.getOutput h 0) != 0
  let r := (← JIT.getOutput h 1) != 0
  t.modify fun s => { s with line := s.line.push l, ready := s.ready.push r }
  JIT.tick h

def runTx (h : JITHandle) (bitDiv : Nat) : IO Bool := do
  let cpb := bitDiv + 1
  JIT.reset h
  JIT.setInput h 2 (UInt64.ofNat bitDiv)
  let t ← IO.mkRef ({} : TxTrace)
  let cyc := fun () => do pure (← t.get).line.size
  let idle := fun (n : Nat) => do for _ in [0:n] do txStep h t 0 false
  let waitReady := fun (cap : Nat) => do
    let mut c := 0
    while c < cap && !((← t.get).ready.back?.getD true) do
      txStep h t 0 false; c := c + 1
  idle 30
  -- A: request after idle
  let a0 ← cyc ()
  txStep h t 0x5A true; t.modify fun s => { s with accepts := s.accepts.push a0 }
  -- the byte input changes right after the request: must not corrupt the frame
  txStep h t 0xFF false
  -- a request while busy (ignored), mid-frame, with a different byte
  idle (5 * cpb)
  txStep h t 0x11 true
  txStep h t 0x00 false
  -- wait until ready is high again
  waitReady (12 * cpb)
  -- B: request on the first cycle txReady is high
  let a1 ← cyc ()
  if (← t.get).ready.back?.getD false then
    txStep h t 0xA5 true; t.modify fun s => { s with accepts := s.accepts.push a1 }
  idle 2
  waitReady (12 * cpb)
  idle (3 * cpb)
  -- C, D: 0x00 and 0xFF after idle
  let a2 ← cyc ()
  txStep h t 0x00 true; t.modify fun s => { s with accepts := s.accepts.push a2 }
  idle 2
  waitReady (12 * cpb)
  idle 7
  let a3 ← cyc ()
  txStep h t 0xFF true; t.modify fun s => { s with accepts := s.accepts.push a3 }
  idle 2
  waitReady (12 * cpb)
  idle (20 * cpb)
  let tr ← t.get
  let errs := txErrors tr.line tr.ready cpb tr.accepts #[0x5A, 0xA5, 0x00, 0xFF]
  let f := decodeFrames tr.line cpb
  IO.println s!"  · TX bitDiv={bitDiv} (cpb {cpb}): {tr.line.size} cycles, frames {f.bytes.toList} at {f.starts.toList}, requests at {tr.accepts.toList}, txReady low runs {(lowRuns tr.ready).toList}"
  if errs.isEmpty then
    IO.println s!"  ✓ TX bitDiv={bitDiv}: frames = bytes sent (no extra frame), txReady one low run per frame covering it"
  else
    for e in errs do IO.println s!"  ✗ TX bitDiv={bitDiv}: {e}"
  pure errs.isEmpty

structure RxTrace where
  valid : Array Bool := #[]
  byte : Array Nat := #[]
  starts : Array Nat := #[]

def rxStep (h : JITHandle) (t : IO.Ref RxTrace) (line : Bool) : IO Unit := do
  JIT.setInput h 0 (if line then 1 else 0)
  JIT.eval h
  let b := (← JIT.getOutput h 0).toNat
  let v := (← JIT.getOutput h 1) != 0
  t.modify fun s => { s with valid := s.valid.push v, byte := s.byte.push b }
  JIT.tick h

/-- One frame: start bit, data bits, stop bit (level `stop`). -/
def rxFrame (h : JITHandle) (t : IO.Ref RxTrace) (cpb v : Nat) (stop : Bool := true) : IO Unit := do
  t.modify fun s => { s with starts := s.starts.push s.valid.size }
  for _ in [0:cpb] do rxStep h t false
  for i in [0:8] do
    for _ in [0:cpb] do rxStep h t (((v >>> i) &&& 1) == 1)
  for _ in [0:cpb] do rxStep h t stop

def runRx (h : JITHandle) (bitDiv : Nat) (label : String) (frames : Array (Nat × Bool))
    (gaps : Array Nat) : IO Bool := do
  let cpb := bitDiv + 1
  JIT.reset h
  JIT.setInput h 1 (UInt64.ofNat bitDiv)
  let t ← IO.mkRef ({} : RxTrace)
  for _ in [0:30] do rxStep h t true
  for i in [0:frames.size] do
    let (v, good) := frames[i]!
    rxFrame h t cpb v good
    for _ in [0:gaps[i]!] do rxStep h t true
  for _ in [0:20 * cpb] do rxStep h t true
  let tr ← t.get
  let expect := frames.map fun (v, good) => if good then some v else none
  let errs := rxErrors tr.valid tr.byte cpb tr.starts expect
  let evs := (List.range tr.valid.size).filter (fun c => tr.valid[c]!)
  let evB := evs.map fun c => tr.byte[c]!
  IO.println s!"  · RX {label} bitDiv={bitDiv}: {tr.valid.size} cycles, frames at {tr.starts.toList}, rxValid at {evs} with rxByte {evB.map fun b => "0x" ++ String.ofList (Nat.toDigits 16 b)}"
  if errs.isEmpty then
    IO.println s!"  ✓ RX {label} bitDiv={bitDiv}: one 1-cycle rxValid per frame in its stop window, rxByte = byte sent, none else"
  else
    for e in errs do IO.println s!"  ✗ RX {label} bitDiv={bitDiv}: {e}"
  pure errs.isEmpty

def main : IO Unit := do
  IO.println "=== uartTxHW / uartRxHW — JIT co-sim (handshake: txReady, rxValid) ==="
  (← IO.getStdout).flush
  let mut ok ← controls
  let tx ← txTop.Sim.load
  for bd in [15, 3] do ok := (← runTx tx.handle bd) && ok
  JIT.destroy tx.handle
  let rx ← rxTop.Sim.load
  let good : Array (Nat × Bool) := #[(0x5A, true), (0x00, true), (0xFF, true), (0xA5, true), (0x81, true)]
  for bd in [15, 3] do
    ok := (← runRx rx.handle bd "back-to-back" good #[0, 0, 0, 0, 0]) && ok
    ok := (← runRx rx.handle bd "gapped" good #[3, 17, 1, 40, 5]) && ok
  JIT.destroy rx.handle
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

/-- A frame with a low stop bit must produce no `rxValid`; the receiver waits
    for the line to return high, so no phantom byte follows
    (see the header of Tests/Drivers/UartRxFramingErrorHWJITTestMain.lean). -/
def mainFramingError : IO Unit := do
  IO.println "=== uartRxHW — framing error (stop bit low) ==="
  (← IO.getStdout).flush
  let rx ← rxTop.Sim.load
  let fe : Array (Nat × Bool) := #[(0x5A, true), (0x3C, false), (0xA5, true)]
  let ok ← runRx rx.handle 15 "framing error" fe #[40, 40, 0]
  JIT.destroy rx.handle
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Net.UartHWJITTest
