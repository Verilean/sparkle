/-
  Shared driver and strict serial-line checker for the UART-top JIT co-sims
  (policy signers, FIDO2 getAssertion).

  The tops share one port layout after `#sim` lowering:
      inputs : uartRx = 0 · bitDiv = 1
      outputs: uartTx = 0 · strobe outputs from 1 (signDone / rejected /
               assertionDone, one-cycle pulses)

  `Bench` drives the RX line one byte at a time (8-N-1, LSB first, one idle
  stop bit), records the whole `uartTx` trace from reset on, and counts rising
  edges of the strobe outputs.  `checkFrames` decodes the trace like a receiver
  (mid-bit sampling anchored on each falling edge: low start bit, stable data
  bits, high stop bit) and rejects extra frames, glitches, truncated frames and
  a line that is not idle-high before the first frame.
-/
import Sparkle.Core.JIT

namespace Sparkle.Tests.IP.Crypto.UartHWJIT

open Sparkle.Core.JIT

structure Bench where
  h : JITHandle
  cpb : Nat
  samples : IO.Ref (Array Bool)
  /-- rising-edge counts of the watched strobe outputs -/
  counts : IO.Ref (Array Nat)
  prev : IO.Ref (Array Bool)
  /-- output port indices of the watched strobes -/
  watch : Array Nat

def Bench.create (h : JITHandle) (bitDiv : Nat) (watch : Array Nat) : IO Bench := do
  JIT.reset h
  JIT.setInput h 1 (UInt64.ofNat bitDiv)
  pure { h, cpb := bitDiv + 1
         samples := ← IO.mkRef #[]
         counts := ← IO.mkRef (Array.replicate watch.size 0)
         prev := ← IO.mkRef (Array.replicate watch.size false)
         watch }

/-- One clock cycle with the given RX level; the `uartTx` level and the strobes
    are sampled before the edge. -/
def Bench.step (b : Bench) (rx : Bool) : IO Unit := do
  JIT.setInput b.h 0 (if rx then 1 else 0)
  JIT.eval b.h
  let t ← JIT.getOutput b.h 0
  b.samples.modify (·.push (t != 0))
  for i in [0:b.watch.size] do
    let v := (← JIT.getOutput b.h b.watch[i]!.toUInt32) != 0
    if v && !(← b.prev.get)[i]! then b.counts.modify (·.modify i (· + 1))
    b.prev.modify (·.set! i v)
  JIT.tick b.h

def Bench.idle (b : Bench) (n : Nat) : IO Unit := do
  for _ in [0:n] do b.step true

/-- start bit, 8 data bits LSB first, one stop bit (all `cpb` cycles wide). -/
def Bench.sendByte (b : Bench) (v : Nat) : IO Unit := do
  for _ in [0:b.cpb] do b.step false
  for i in [0:8] do
    for _ in [0:b.cpb] do b.step (((v >>> i) &&& 1) == 1)
  for _ in [0:b.cpb] do b.step true

def Bench.sendBytes (b : Bench) (bs : Array Nat) : IO Unit := do
  for v in bs do b.sendByte v

def Bench.count (b : Bench) (i : Nat) : IO Nat := do pure (← b.counts.get)[i]!

/-- Idle (RX high) until watched strobe `i` has fired `n` times in total;
    returns `false` if that does not happen within `cap` cycles. -/
def Bench.waitCount (b : Bench) (i n cap : Nat) : IO Bool := do
  let mut c := 0
  while (← b.count i) < n && c < cap do
    b.step true
    c := c + 1
  pure ((← b.count i) ≥ n)

/-- Big-endian bytes of a `width`-byte value. -/
def beBytes (v width : Nat) : Array Nat :=
  (Array.range width).map fun i => (v >>> (8 * (width - 1 - i))) &&& 0xFF

def beNat (bs : Array Nat) (off len : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:len] do v := (v <<< 8) ||| bs[off + i]!
  return v

structure Frames where
  bytes : Array Nat
  /-- start cycle of each decoded frame -/
  starts : Array Nat
  /-- human-readable framing violations (empty = clean line) -/
  errors : Array String

/-- Decode the whole `uartTx` trace into 8-N-1 frames the way a receiver does:
    anchor on each falling edge, sample the middle of the start bit (must be
    low), of the 8 data bits and of the stop bit (must be high); each sample
    must agree with its neighbours ±cpb/4 (no glitch inside a bit).  A low
    pulse shorter than half a bit is reported as a glitch, not a frame. -/
def decodeFrames (s : Array Bool) (cpb : Nat) : Frames := Id.run do
  let mut bytes : Array Nat := #[]
  let mut starts : Array Nat := #[]
  let mut errs : Array String := #[]
  if s.size > 0 && !s[0]! then errs := errs.push "line low at cycle 0 (not idle-high)"
  let q := cpb / 4
  -- level at the centre of bit slot `i` of a frame anchored at `pos`, and
  -- whether the ±q window around it is constant
  let slot := fun (pos i : Nat) =>
    let c := pos + i * cpb + cpb / 2
    let v := s[c]!
    (v, s[c - q]! == v && s[c + q]! == v)
  let mut pos := 1
  while pos < s.size do
    if s[pos - 1]! && !s[pos]! then
      if pos + 9 * cpb + cpb / 2 + q >= s.size then
        errs := errs.push s!"low edge at cycle {pos}: trace ends inside the frame"
        pos := s.size
      else
        let (st, stOk) := slot pos 0
        if st || !stOk then
          errs := errs.push s!"cycle {pos}: low pulse that is not a valid start bit (glitch)"
          pos := pos + 1
        else
          let mut byte := 0
          for i in [0:8] do
            let (v, ok) := slot pos (i + 1)
            if !ok then errs := errs.push s!"frame at cycle {pos}: data bit {i} not stable"
            if v then byte := byte ||| (1 <<< i)
          let (sp, spOk) := slot pos 9
          if !sp || !spOk then errs := errs.push s!"frame at cycle {pos}: bad stop bit"
          bytes := bytes.push byte
          starts := starts.push pos
          pos := pos + 9 * cpb + cpb / 2 + 1
    else pos := pos + 1
  return { bytes, starts, errors := errs }

/-- Run-length encoding (level, cycles) of a trace. -/
def runs (s : Array Bool) : Array (Nat × Nat) := Id.run do
  let mut r : Array (Nat × Nat) := #[]
  for i in [0:s.size] do
    if i > 0 && s[i]! == s[i-1]! then
      r := r.modify (r.size - 1) (fun (v, n) => (v, n + 1))
    else r := r.push (if s[i]! then 1 else 0, 1)
  return r

/-- Check the trace: framing of every frame (start/stop bits, glitches), and
    per request window `[bounds[i], bounds[i+1])` that the frames in it are
    exactly the expected reply, none missing and none extra.  Prints one line
    per verdict; returns success. -/
def checkFrames (label : String) (b : Bench) (steps : Array (String × Array Nat))
    (bounds : Array Nat) : IO Bool := do
  let s ← b.samples.get
  let f := decodeFrames s b.cpb
  let mut ok := true
  if !f.errors.isEmpty then
    IO.println s!"  ✗ {label}: serial framing errors: {f.errors.toList.take 6}"
    ok := false
  else
    IO.println s!"  ✓ {label}: every frame has start=0, stop=1, stable mid-bit samples, no glitches"
  for i in [0:steps.size] do
    let (name, expect) := steps[i]!
    let lo := bounds[i]!
    let hi := if i + 1 < bounds.size then bounds[i+1]! else s.size
    let got := (List.range f.bytes.size).filter (fun j => lo ≤ f.starts[j]! && f.starts[j]! < hi)
                 |>.map (fun j => f.bytes[j]!) |>.toArray
    let pre := got.extract 0 expect.size
    if pre != expect then
      IO.println s!"  ✗ {label}/{name}: reply bytes differ from the reference ({got.size} frames, expected {expect.size})"
      ok := false
    else if got.size > expect.size then
      IO.println s!"  ✗ {label}/{name}: expected {expect.size} bytes = reference, but {got.size - expect.size} EXTRA frame(s) follow: {(got.extract expect.size got.size).toList}"
      ok := false
    else
      IO.println s!"  ✓ {label}/{name}: exactly {expect.size} reply bytes = reference, none extra"
  if !ok then
    let r := runs s
    IO.println s!"    last 12 TX runs (level, cycles): {(r.extract (r.size - 12) r.size).toList}"
  pure ok

/-- One request: the frame to send, which watched strobe (index into `watch`)
    must answer it, and the exact reply bytes expected on the line. -/
structure Step where
  label : String
  frame : Array Nat
  strobe : Nat
  reply : Array Nat

/-- Run the steps back to back (each waits for its strobe and for the reply to
    drain before the next frame is sent), then idle `tail` cycles and check the
    serial line and the strobe counts: every watched strobe must have fired
    exactly as often as the steps that name it.  `cap` bounds the wait per
    strobe.  Returns success. -/
def runSteps (b : Bench) (steps : Array Step) (cap tail : Nat) : IO Bool := do
  let mut ok := true
  let mut want := Array.replicate b.watch.size 0
  let mut bounds : Array Nat := #[]
  b.idle 20
  for st in steps do
    bounds := bounds.push (← b.samples.get).size
    b.sendBytes st.frame
    let sent ← b.samples.get
    want := want.modify st.strobe (· + 1)
    if (← b.waitCount st.strobe want[st.strobe]! cap) then
      let n := (← b.samples.get).size - sent.size
      IO.println s!"  · {st.label}: strobe {b.watch[st.strobe]!} after {n} cycles from the last request byte"
    else
      IO.println s!"  ✗ {st.label}: strobe output {b.watch[st.strobe]!} did not fire within {cap} cycles"
      ok := false
    -- let the reply drain (10 bit-times per byte) plus margin
    b.idle (st.reply.size * 10 * b.cpb + 2000)
  b.idle tail
  let counts ← b.counts.get
  for i in [0:b.watch.size] do
    if counts[i]! == want[i]! then
      IO.println s!"  ✓ strobe output {b.watch[i]!} fired {counts[i]!}× (expected {want[i]!})"
    else
      IO.println s!"  ✗ strobe output {b.watch[i]!} fired {counts[i]!}× (expected {want[i]!})"
      ok := false
  let okF ← checkFrames "uartTx" b (steps.map fun st => (st.label, st.reply)) bounds
  let total := (← b.samples.get).size
  IO.println s!"  · {total} cycles simulated, {tail} idle cycles after the last reply"
  pure (ok && okF)

end Sparkle.Tests.IP.Crypto.UartHWJIT
