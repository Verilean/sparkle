/-
  Controls for the serial-line and strobe checks of `UartHWJITHarness`, on
  synthetic traces (no JIT): each check must accept the clean case and reject
  the single defect it is meant to find.

  Framing (cpb = 16):
    · clean frames 0xFF, 0x00, 0xA5 back to back decode with no error;
    · a 1-cycle low pulse 6 cycles into the stop bit of 0xFF is rejected
      (a 3-point mid-bit sampler at +4/+8/+12 would have missed it);
    · the same 1-cycle flip inside the start bit and inside a data bit, a
      start pulse one cycle short, a line low at reset and a trace that ends
      inside a frame are rejected.
  Replies: exact reply passes; an extra trailing frame, a missing byte and a
  frame before the first request are rejected.
  Strobes: per-window deltas must be 1 for the named strobe and 0 for the
  others; a false `signDone` in a refusal window followed by a missing
  `signDone` in the next accept window is rejected although the totals match.
-/
import Tests.IP.Crypto.UartHWJITHarness

open Sparkle.Tests.IP.Crypto.UartHWJIT

namespace Sparkle.Tests.IP.Crypto.UartHWJITHarnessTest

def cpb : Nat := 16

/-- One 8-N-1 frame, `cpb` cycles per bit. -/
def frame (v : Nat) : Array Bool := Id.run do
  let mut s : Array Bool := Array.replicate cpb false
  for i in [0:8] do
    s := s ++ Array.replicate cpb (((v >>> i) &&& 1) == 1)
  return s ++ Array.replicate cpb true

/-- 20 idle cycles, the frames back to back, then 40 idle cycles. -/
def trace (bs : List Nat) : Array Bool :=
  (bs.foldl (fun acc v => acc ++ frame v) (Array.replicate 20 true)) ++ Array.replicate 40 true

def flip (s : Array Bool) (c : Nat) : Array Bool := s.modify c (!·)

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  {if cond then "✓" else "✗"} {name}"
  pure cond

def main : IO Unit := do
  IO.println "=== UartHWJITHarness checker controls ==="
  let mut ok := true
  let t0 := 20  -- first start bit
  -- framing
  let clean := decodeFrames (trace [0xFF, 0x00, 0xA5]) cpb
  ok := (← check s!"clean 0xFF 0x00 0xA5: bytes {clean.bytes.toList}, errors {clean.errors.toList}"
          (clean.bytes == #[0xFF, 0x00, 0xA5] && clean.errors.isEmpty)) && ok
  let stopG := decodeFrames (flip (trace [0xFF]) (t0 + 9 * cpb + 6)) cpb
  ok := (← check s!"0xFF, stop bit low for 1 cycle at +6: rejected ({stopG.errors.toList})"
          (!stopG.errors.isEmpty)) && ok
  let startG := decodeFrames (flip (trace [0x00]) (t0 + 6)) cpb
  ok := (← check s!"start bit high for 1 cycle at +6: rejected ({startG.errors.toList})"
          (!startG.errors.isEmpty)) && ok
  let dataG := decodeFrames (flip (trace [0xFF]) (t0 + 3 * cpb + 6)) cpb
  ok := (← check s!"data bit 2 low for 1 cycle at +6: rejected ({dataG.errors.toList})"
          (!dataG.errors.isEmpty)) && ok
  let short := decodeFrames (flip (trace [0x01]) (t0 + cpb - 1)) cpb
  ok := (← check s!"start bit one cycle short (15 cycles): rejected ({short.errors.toList})"
          (!short.errors.isEmpty)) && ok
  let low0 := decodeFrames (flip (trace [0x55]) 0) cpb
  ok := (← check s!"line low at reset: rejected ({low0.errors.toList})" (!low0.errors.isEmpty)) && ok
  let tr := trace [0x55]
  let cut := decodeFrames (tr.extract 0 (t0 + 5 * cpb)) cpb
  ok := (← check s!"trace ends inside a frame: rejected ({cut.errors.toList})" (!cut.errors.isEmpty)) && ok
  -- replies (one request window starting at cycle 10)
  let verdictsOk := fun (bs : List Nat) (expect : Array Nat) (b0 : Nat) =>
    let s := trace bs
    (replyVerdicts (decodeFrames s cpb) #[("req", expect)] #[b0] s.size).all (·.1)
  ok := (← check "exact reply 0xEE: accepted" (verdictsOk [0xEE] #[0xEE] 10)) && ok
  ok := (← check "reply 0xEE then an extra 0x00 frame: rejected" (!verdictsOk [0xEE, 0x00] #[0xEE] 10)) && ok
  ok := (← check "reply missing its last byte: rejected" (!verdictsOk [0x12] #[0x12, 0x34] 10)) && ok
  ok := (← check "frame before the first request window: rejected" (!verdictsOk [0xEE] #[] 30)) && ok
  -- strobes: watched outputs 1 (signDone) and 2 (rejected)
  let expect : Array (String × Option Nat) :=
    #[("before", none), ("refuse", some 1), ("accept", some 0), ("tail", none)]
  let good := #[#[0, 0], #[0, 1], #[1, 0], #[0, 0]]
  ok := (← check "strobes: refusal → rejected only, accept → signDone only: accepted"
          (strobeErrors #[1, 2] expect good).isEmpty) && ok
  -- false signDone during the refusal, none during the accept: totals 1 / 1 as expected
  let swapped := #[#[0, 0], #[1, 1], #[0, 0], #[0, 0]]
  let errs := strobeErrors #[1, 2] expect swapped
  ok := (← check s!"strobes: false signDone on refusal + missing on accept (totals match): rejected ({errs.toList})"
          (!errs.isEmpty)) && ok
  let lateErrs := strobeErrors #[1, 2] expect #[#[0, 0], #[0, 1], #[1, 0], #[0, 1]]
  ok := (← check s!"strobes: pulse in the idle tail: rejected ({lateErrs.toList})" (!lateErrs.isEmpty)) && ok
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.UartHWJITHarnessTest
