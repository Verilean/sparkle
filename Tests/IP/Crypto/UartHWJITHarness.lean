/-
  Shared driver and strict serial-line checker for the UART-top JIT co-sims
  (policy signers, FIDO2 getAssertion).

  The tops share one port layout after `#sim` lowering:
      inputs : uartRx = 0 · bitDiv = 1
      outputs: uartTx = 0 · strobe outputs from 1 (signDone / rejected /
               assertionDone, one-cycle pulses)

  `Bench` drives the RX line one byte at a time (8-N-1, LSB first, one idle
  stop bit), records the whole `uartTx` trace from reset on, and counts rising
  edges of the strobe outputs.  `checkFrames` decodes the trace frame by frame
  (anchored on each falling edge, every cycle of every bit slot checked: low
  start bit, constant data bits, high stop bit) and rejects extra frames,
  glitches, truncated frames and a line that is not idle-high at reset.
  `runSteps` also checks the strobes per request window, not as totals.
  Pure controls for the checker: Tests/IP/Crypto/UartHWJITHarnessTest.lean.
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

/-- Decode the whole `uartTx` trace into 8-N-1 frames.  The co-sim is
    cycle-exact, so a frame anchored on a falling edge at cycle `pos` must hold
    each of its 10 bit slots `[pos + i*cpb, pos + (i+1)*cpb)` at ONE level for
    every cycle of the slot: the start slot low, 8 data slots constant, the stop
    slot high.  A low pulse shorter than a whole start slot is reported as a
    glitch, a level change inside a data or stop slot as an error naming the
    cycle, and a trace that ends inside a frame as truncated.  The line must be
    high at cycle 0; between frames any low edge starts a new frame check. -/
def decodeFrames (s : Array Bool) (cpb : Nat) : Frames := Id.run do
  let mut bytes : Array Nat := #[]
  let mut starts : Array Nat := #[]
  let mut errs : Array String := #[]
  if s.size > 0 && !s[0]! then errs := errs.push "line low at cycle 0 (not idle-high)"
  -- level of bit slot `i` of a frame anchored at `pos`, and the first cycle in
  -- the slot whose level differs (none = constant over the whole slot)
  let slot := fun (pos i : Nat) => Id.run do
    let a := pos + i * cpb
    let v := s[a]!
    let mut bad : Option Nat := none
    for c in [a:a + cpb] do
      if bad.isNone && s[c]! != v then bad := some c
    return (v, bad)
  let mut pos := 1
  while pos < s.size do
    if s[pos - 1]! && !s[pos]! then
      if pos + 10 * cpb > s.size then
        errs := errs.push s!"low edge at cycle {pos}: trace ends inside the frame"
        pos := s.size
      else
        let (_, stBad) := slot pos 0
        if let some c := stBad then
          errs := errs.push s!"cycle {pos}: low pulse of {c - pos} cycles, shorter than a start bit (glitch)"
          pos := c
        else
          let mut byte := 0
          for i in [0:8] do
            let (v, bad) := slot pos (i + 1)
            if let some c := bad then
              errs := errs.push s!"frame at cycle {pos}: data bit {i} changes level at cycle {c}"
            if v then byte := byte ||| (1 <<< i)
          let (sp, spBad) := slot pos 9
          if !sp then errs := errs.push s!"frame at cycle {pos}: stop bit low"
          else if let some c := spBad then
            errs := errs.push s!"frame at cycle {pos}: stop bit drops low at cycle {c}"
          bytes := bytes.push byte
          starts := starts.push pos
          pos := pos + 10 * cpb
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

/-- Per request window `[bounds[i], bounds[i+1])` (the last one runs to the
    end of the trace): the frames that start in it must be exactly the expected
    reply, none missing and none extra; no frame may start before `bounds[0]`.
    One verdict (ok, line) per window, plus a failing verdict for early frames. -/
def replyVerdicts (f : Frames) (steps : Array (String × Array Nat)) (bounds : Array Nat)
    (total : Nat) : Array (Bool × String) := Id.run do
  let mut out : Array (Bool × String) := #[]
  let early := f.starts.filter (· < bounds[0]!)
  if !early.isEmpty then
    out := out.push (false, s!"{early.size} frame(s) before the first request")
  for i in [0:steps.size] do
    let (name, expect) := steps[i]!
    let lo := bounds[i]!
    let hi := if i + 1 < bounds.size then bounds[i+1]! else total
    let got := (List.range f.bytes.size).filter (fun j => lo ≤ f.starts[j]! && f.starts[j]! < hi)
                 |>.map (fun j => f.bytes[j]!) |>.toArray
    let pre := got.extract 0 expect.size
    if pre != expect then
      out := out.push (false, s!"{name}: reply bytes differ from the reference ({got.size} frames, expected {expect.size})")
    else if got.size > expect.size then
      out := out.push (false, s!"{name}: expected {expect.size} bytes = reference, but {got.size - expect.size} EXTRA frame(s) follow: {(got.extract expect.size got.size).toList}")
    else
      out := out.push (true, s!"{name}: exactly {expect.size} reply bytes = reference, none extra")
  return out

/-- Check the trace: framing of every frame (`decodeFrames`) and the reply of
    every request window (`replyVerdicts`).  Prints one line per verdict;
    returns success. -/
def checkFrames (label : String) (b : Bench) (steps : Array (String × Array Nat))
    (bounds : Array Nat) : IO Bool := do
  let s ← b.samples.get
  let f := decodeFrames s b.cpb
  let mut ok := true
  if !f.errors.isEmpty then
    IO.println s!"  ✗ {label}: serial framing errors: {f.errors.toList.take 6}"
    ok := false
  else
    IO.println s!"  ✓ {label}: every frame holds start=0, each data bit and stop=1 for all {b.cpb} cycles of its slot; no glitches"
  for (good, line) in replyVerdicts f steps bounds s.size do
    IO.println s!"  {if good then "✓" else "✗"} {label}/{line}"
    ok := ok && good
  if !ok then
    let r := runs s
    IO.println s!"    last 12 TX runs (level, cycles): {(r.extract (r.size - 12) r.size).toList}"
  pure ok

/-- Strobe check per window: `deltas[w]` are the rising edges of every watched
    strobe inside window `w`, and `expect[w]` names the one strobe that must
    fire exactly once there (`none` = no strobe may fire, e.g. before the first
    request or in the idle tail); every other watched strobe must stay at 0.
    Returns one message per violation (empty = ok). -/
def strobeErrors (watch : Array Nat) (expect : Array (String × Option Nat))
    (deltas : Array (Array Nat)) : Array String := Id.run do
  let mut errs : Array String := #[]
  for w in [0:expect.size] do
    let (name, e) := expect[w]!
    let d := deltas[w]!
    for i in [0:watch.size] do
      let want := if e == some i then 1 else 0
      if d[i]! != want then
        errs := errs.push s!"{name}: strobe output {watch[i]!} fired {d[i]!}× (expected {want})"
  return errs

/-- One request: the frame to send, which watched strobe (index into `watch`)
    must answer it, and the exact reply bytes expected on the line. -/
structure Step where
  label : String
  frame : Array Nat
  strobe : Nat
  reply : Array Nat

/-- Run the steps back to back (each waits for its strobe to fire after its own
    first request byte and for the reply to drain before the next frame is
    sent), then idle `tail` cycles and check the serial line and the strobes:
    in each request window (request start to reply drained) the named strobe
    fires exactly once and every other watched strobe not at all, and no
    strobe fires before the first request or in the tail.  `cap` bounds the
    wait per strobe.  Returns success. -/
def runSteps (b : Bench) (steps : Array Step) (cap tail : Nat) : IO Bool := do
  let mut ok := true
  let mut bounds : Array Nat := #[]
  let mut deltas : Array (Array Nat) := #[]
  let sub := fun (c1 c0 : Array Nat) => (Array.range c1.size).map fun i => c1[i]! - c0[i]!
  b.idle 20
  deltas := deltas.push (← b.counts.get)
  for st in steps do
    bounds := bounds.push (← b.samples.get).size
    let c0 ← b.counts.get
    b.sendBytes st.frame
    let sent ← b.samples.get
    if (← b.waitCount st.strobe (c0[st.strobe]! + 1) cap) then
      let n := (← b.samples.get).size - sent.size
      IO.println s!"  · {st.label}: strobe {b.watch[st.strobe]!} after {n} cycles from the last request byte"
    else
      IO.println s!"  ✗ {st.label}: strobe output {b.watch[st.strobe]!} did not fire within {cap} cycles"
      ok := false
    -- let the reply drain (10 bit-times per byte) plus margin
    b.idle (st.reply.size * 10 * b.cpb + 2000)
    deltas := deltas.push (sub (← b.counts.get) c0)
  let cT ← b.counts.get
  b.idle tail
  deltas := deltas.push (sub (← b.counts.get) cT)
  let expect := #[("before the first request", none)] ++
    steps.map (fun st => (st.label, some st.strobe)) ++ #[("idle tail", none)]
  let errs := strobeErrors b.watch expect deltas
  if errs.isEmpty then
    IO.println s!"  ✓ strobes: each request window has its strobe exactly once and every other watched strobe 0×; none before the first request or in the tail"
  else
    for e in errs do IO.println s!"  ✗ {e}"
    ok := false
  let okF ← checkFrames "uartTx" b (steps.map fun st => (st.label, st.reply)) bounds
  let total := (← b.samples.get).size
  IO.println s!"  · {total} cycles simulated, {tail} idle cycles after the last reply"
  pure (ok && okF)

end Sparkle.Tests.IP.Crypto.UartHWJIT
