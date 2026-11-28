/-
  Generic "done exactly once per request, value = reference" driver for the
  crypto `*HW` cores that expose a `start` input and a `done` output (SHA-256
  block / stream, HMAC-SHA256, Keccak-256 sponge, RFC 6979 nonce, ...).

  A DUT description (`Dut`) supplies four closures over the JIT handle: how to
  apply a request together with the `start` level, how to apply idle garbage
  (start low, every data input random), and how to sample (done, outputs).  The
  driver then runs a list of requests back to back: an idle prologue with
  garbage inputs, then per request one `start` pulse cycle, the request inputs
  held (`hold`) or replaced by garbage while the core is busy, `gap` idle cycles
  after `done`, and an idle epilogue.  `doneErrors` is a pure checker over the
  per-cycle trace; per request it requires

  * exactly one `done` pulse in the request's window [start, next start),
    first seen between start + minLat and start + maxLat (cycles, start pulse
    = cycle 0) and at most `maxWidth` cycles wide;
  * the outputs at the `done` cycle equal the reference (when given);
  * the outputs unchanged until the next start (`stable`), whatever the inputs do;
  * with `fixedLatency`, the same latency for every request;
  * and no `done` anywhere outside the windows: not in the prologue before the
    first start, nor after the last request's `done` pulse.

  The checker has its own synthetic controls (`DoneHWJITHarnessTest`), and each
  instance adds live controls (a wrong reference, a too tight latency window).
-/
import Sparkle.Core.JIT

namespace Sparkle.Tests.IP.Crypto.DoneHW

open Sparkle.Core.JIT

structure Spec where
  name : String
  /-- earliest allowed `done` cycle after the start-pulse cycle (≥ 1) -/
  minLat : Nat := 1
  maxLat : Nat
  maxWidth : Nat := 1
  fixedLatency : Bool := false
  stable : Bool := true

structure Obs where
  done : Bool
  outs : Array Nat
  deriving Inhabited

/-- One request: input operands (DUT specific) and the expected outputs at
    `done` (`none` = not compared, e.g. an intermediate block). -/
structure Req where
  inputs : Array Nat
  expect : Option (Array Nat)
  deriving Inhabited

structure Dut where
  handle : JITHandle
  /-- apply the request operands; the Bool is the `start` level -/
  set : Array Nat → Bool → IO Unit
  /-- start low, all data inputs garbage (seeded) -/
  junk : Nat → IO Unit
  read : IO Obs
  /-- keep the request operands applied (start low) while the core is busy -/
  hold : Bool

def hexN (b : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 b)

/-! ## Pure checker -/

/-- Violations on a trace; `starts[i]` is the start-pulse cycle of request i. -/
def doneErrors (spec : Spec) (tr : Array Obs) (starts : Array Nat) (exps : Array (Option (Array Nat))) :
    Array String := Id.run do
  let n := tr.size
  let mut errs : Array String := #[]
  let mut lats : Array Nat := #[]
  for i in [0:starts.size] do
    let s := starts[i]!
    let hi := if i + 1 < starts.size then starts[i+1]! else n
    let tag := s!"{spec.name} request {i} (start {s})"
    -- runs of done inside the window
    let mut runs : Array (Nat × Nat) := #[]
    let mut q := s
    while q < hi do
      if tr[q]!.done && (q == s || !tr[q-1]!.done) then
        let mut w := 0
        while q + w < hi && tr[q+w]!.done do w := w + 1
        runs := runs.push (q, w)
        q := q + w
      else q := q + 1
    match runs.toList with
    | [(d, w)] =>
      if d < s + spec.minLat then errs := errs.push s!"{tag}: done at +{d - s}, earlier than minLat {spec.minLat}"
      if d > s + spec.maxLat then errs := errs.push s!"{tag}: done at +{d - s}, later than maxLat {spec.maxLat}"
      if w > spec.maxWidth then errs := errs.push s!"{tag}: done {w} cycles wide (max {spec.maxWidth})"
      lats := lats.push (d - s)
      match exps[i]! with
      | some e =>
        if tr[d]!.outs != e then
          errs := errs.push s!"{tag}: outputs {tr[d]!.outs.toList.map hexN} at done, expected {e.toList.map hexN}"
      | none => pure ()
      if spec.stable then
        for c in [d:hi] do
          if tr[c]!.outs != tr[d]!.outs then
            errs := errs.push s!"{tag}: outputs change at +{c - s} after done (+{d - s})"
            break
    | rs => errs := errs.push s!"{tag}: {rs.length} done pulses {rs.map fun (d, _) => d - s} (expected exactly 1)"
  if spec.fixedLatency && lats.size > 0 && lats.any (· != lats[0]!) then
    errs := errs.push s!"{spec.name}: latency differs between requests {lats.toList}"
  -- nothing outside the windows (prologue before the first start; the cycles of
  -- a window after its pulse are covered above)
  let first := if starts.size > 0 then starts[0]! else n
  for c in [0:first] do
    if tr[c]!.done then
      errs := errs.push s!"{spec.name}: done at cycle {c}, before the first start at {first}"
      break
  return errs

/-! ## Driver -/

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

/-- Run `reqs` back to back.  `gaps[i % gaps.size]` idle cycles follow each
    request's `done`; `pro` idle cycles come first, `epi` last.  Returns the
    trace and the start cycles. -/
def run (d : Dut) (spec : Spec) (reqs : Array Req) (gaps : Array Nat) (pro : Nat := 6) (epi : Nat := 24) :
    IO (Array Obs × Array Nat) := do
  JIT.reset d.handle
  let mut tr : Array Obs := #[]
  let mut starts : Array Nat := #[]
  let mut seed := 99
  let step := fun (f : IO Unit) => do
    f
    JIT.eval d.handle
    let o ← d.read
    JIT.tick d.handle
    pure o
  for _ in [0:pro] do
    seed := lcg seed
    tr := tr.push (← step (d.junk seed))
  for i in [0:reqs.size] do
    starts := starts.push tr.size
    tr := tr.push (← step (d.set reqs[i]!.inputs true))
    let mut seen := tr[tr.size - 1]!.done
    let mut waited := 0
    while !seen && waited < spec.maxLat + 6 do
      seed := lcg seed
      let o ← step (if d.hold then d.set reqs[i]!.inputs false else d.junk seed)
      tr := tr.push o
      seen := o.done
      waited := waited + 1
    for _ in [0:gaps[i % gaps.size]!] do
      seed := lcg seed
      tr := tr.push (← step (d.junk seed))
  for _ in [0:epi] do
    seed := lcg seed
    tr := tr.push (← step (d.junk seed))
  pure (tr, starts)

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  {if cond then "✓" else "✗"} {name}"
  pure cond

/-- Run the requests and compare with their references; prints a summary line
    (latencies, cycles) and returns success. -/
def runCase (d : Dut) (spec : Spec) (reqs : Array Req) (gaps : Array Nat) : IO Bool := do
  let (tr, starts) ← run d spec reqs gaps
  let errs := doneErrors spec tr starts (reqs.map (·.expect))
  let dones := (List.range tr.size).filter fun c => tr[c]!.done && (c == 0 || !tr[c-1]!.done)
  let lats := (List.range starts.size).filterMap fun i => dones.find? (· ≥ starts[i]!) |>.map (· - starts[i]!)
  let tag := s!"{spec.name} gaps={gaps.toList}"
  IO.println s!"  · {tag}: {reqs.size} requests, {tr.size} cycles, done latencies {lats}"
  if errs.isEmpty then
    IO.println s!"  ✓ {tag}: done exactly once per request in [+{spec.minLat}, +{spec.maxLat}], outputs = reference, stable, nothing outside"
  else
    for e in errs.toList.take 8 do IO.println s!"  ✗ {tag}: {e}"
  pure errs.isEmpty

/-- Live negative controls shared by every instance: a reference for a different
    request, and a latency window that is too tight, must be flagged. -/
def liveControls (d : Dut) (spec : Spec) (reqs : Array Req) : IO Bool := do
  let (tr, starts) ← run d spec reqs #[3]
  let exps := reqs.map (·.expect)
  let mut ok ← check s!"{spec.name}: the unmodified run passes" (doneErrors spec tr starts exps).isEmpty
  let rot := (List.range exps.size).toArray.map fun i => exps[(i + 1) % exps.size]!
  ok := (← check s!"{spec.name}: references of other requests flagged"
    (exps.size < 2 || !(doneErrors spec tr starts rot).isEmpty)) && ok
  let tight := { spec with maxLat := spec.minLat }
  ok := (← check s!"{spec.name}: a latency window ending at minLat flags the run"
    (!(doneErrors tight tr starts exps).isEmpty)) && ok
  let late := { spec with minLat := spec.maxLat + 1, maxLat := spec.maxLat + 2 }
  ok := (← check s!"{spec.name}: a latency window after the real one flags the run"
    (!(doneErrors late tr starts exps).isEmpty)) && ok
  -- the checker must see a request that never starts as a missing done
  ok := (← check s!"{spec.name}: an extra (never issued) request is flagged"
    (!(doneErrors spec tr (starts.push (tr.size - 3)) (exps.push none)).isEmpty)) && ok
  pure ok

/-! ## Helpers shared by the instances -/

/-- Write a value as ⌈w/32⌉ consecutive 32-bit input words (low word first), the
    layout `#sim` gives inputs wider than 64 bits. -/
def setWords (h : JITHandle) (base nWords v : Nat) : IO Unit := do
  for j in [0:nWords] do
    JIT.setInput h (base + j).toUInt32 (UInt64.ofNat ((v >>> (32 * j)) &&& 0xFFFFFFFF))

def getWords (h : JITHandle) (base nWords : Nat) : IO Nat := do
  let mut acc : Nat := 0
  for j in [0:nWords] do
    acc := acc ||| ((← JIT.getOutput h (base + j).toUInt32).toNat <<< (32 * j))
  pure acc

/-- Garbage value of `bits` bits from a seed. -/
def garbage (seed salt bits : Nat) : Nat :=
  let a := lcg (seed + salt * 7919)
  let b := lcg a
  let c := lcg b
  let d := lcg c
  ((a <<< 192) ||| (b <<< 128) ||| (c <<< 64) ||| d) % 2 ^ bits

/-- SHA-256 padding of `msg` as if `extra` bytes preceded it, in 512-bit blocks
    (as Nat, byte 0 = most significant). -/
def padBlocks (msg : Array UInt8) (extra : Nat := 0) : List Nat := Id.run do
  let mut p := msg.push 0x80
  while (p.size + extra) % 64 != 56 do p := p.push 0
  let bits := (msg.size + extra) * 8
  for i in [:8] do p := p.push (UInt8.ofNat ((bits >>> ((7 - i) * 8)) &&& 0xFF))
  let mut out : List Nat := []
  for b in [:p.size / 64] do
    let mut v : Nat := 0
    for i in [:64] do v := (v <<< 8) ||| (p.getD (b * 64 + i) 0).toNat
    out := out ++ [v]
  return out

def bytesOf (s : String) : Array UInt8 := s.toUTF8.toList.toArray

end Sparkle.Tests.IP.Crypto.DoneHW
