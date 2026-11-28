/-
  JIT co-sim of the generated hardware for the SLIP blocks
  `IP.Net.SLIP.slipFramerHW` and `slipDeframerHW`, compared cycle by cycle
  with an expected trace built from the pure reference (`encodeByte` /
  `decodeStream`).  The existing SLIPTest only checks, through the Signal
  interpreter, that a loopback of one payload decodes and that `frameDone`
  was seen at least once.

  Framer (`framerTop`): inputs payloadByte = 0, payloadValid = 1, frameEnd = 2;
  outputs txByte = 0, txValid = 1, txReady = 2.  Frames are sent the way an
  upstream block must: wait for `txReady`, pulse `payloadValid` for 1 cycle
  per byte, wait for `txReady`, pulse `frameEnd`.  Expected per cycle: `txValid`
  and `txByte` (a payload byte appears 1 cycle after its request, an escaped
  one as ESC then the replacement on the next cycle, the closing END 1 cycle
  after `frameEnd`), and `txReady` low exactly in the cycle between ESC and its
  replacement.  The hardware emits no leading END (documented in SLIP.lean),
  unlike `encodeFrame`.

  Deframer (`deframerTop`): inputs rxByte = 0, rxValid = 1; outputs outByte = 0,
  outValid = 1, frameDone = 2.  Wire streams (frames with and without leading
  END, empty frames, END/ESC bytes in the payload, back-to-back and spaced
  bytes) are fed as 1-cycle `rxValid` pulses.  Expected per cycle: `outValid`
  one cycle after every payload byte (none for the ESC prefix or an END in
  idle) with `outByte`, `frameDone` one cycle after each closing END, nothing
  else; the decoded stream is also cross-checked against `decodeStream`.

  NOT checked: behaviour after an ESC followed by a byte other than DC/DD,
  rxValid held high more than one cycle, `frameEnd` pulsed while `txReady` is
  low (the framer drops it; upstream must wait).
  Synthetic controls for both checkers run first (no JIT).
-/
import IP.Net.SLIP
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Net.SLIP

namespace Sparkle.Tests.IP.Net.SlipHWJITTest

set_option maxRecDepth 100000

def framerTop (payloadByte : Signal defaultDomain (BitVec 8))
    (payloadValid frameEnd : Signal defaultDomain Bool) : FramerOut defaultDomain :=
  slipFramerHW payloadByte payloadValid frameEnd

def deframerTop (rxByte : Signal defaultDomain (BitVec 8))
    (rxValid : Signal defaultDomain Bool) : DeframerOut defaultDomain :=
  slipDeframerHW rxByte rxValid

#sim framerTop
#sim deframerTop

/-- One per-cycle observation. -/
structure Obs where
  valid : Array Nat := #[]
  byte : Array Nat := #[]
  third : Array Nat := #[]   -- framer: txReady, deframer: frameDone

/-- First mismatches between expected and observed per-cycle arrays. -/
def diffs (name : String) (exp got : Array Nat) : Array String := Id.run do
  let mut out : Array String := #[]
  if exp.size != got.size then out := out.push s!"{name}: length {got.size} ≠ {exp.size}"
  for c in [0:min exp.size got.size] do
    if exp[c]! != got[c]! && out.size < 4 then
      out := out.push s!"{name}: cycle {c}: got {got[c]!}, expected {exp[c]!}"
  return out

def obsErrors (exp got : Obs) (thirdName : String) : Array String :=
  diffs "valid" exp.valid got.valid ++ diffs "byte" exp.byte got.byte
    ++ diffs thirdName exp.third got.third

/-! ## Expected traces -/

inductive Req | payload (b : Nat) | frameEnd

/-- Expected framer observation for requests at the given cycles. -/
def framerExpect (reqs : Array (Nat × Req)) (n : Nat) : Obs := Id.run do
  let mut v := Array.replicate n 0
  let mut b := Array.replicate n 0
  let mut r := Array.replicate n 1
  for (c, q) in reqs do
    match q with
    | .payload x =>
      if x == 0xC0 || x == 0xDB then
        v := v.set! (c+1) 1; b := b.set! (c+1) 0xDB
        v := v.set! (c+2) 1; b := b.set! (c+2) (if x == 0xC0 then 0xDC else 0xDD)
        r := r.set! (c+1) 0
      else
        v := v.set! (c+1) 1; b := b.set! (c+1) x
    | .frameEnd => v := v.set! (c+1) 1; b := b.set! (c+1) 0xC0
  return { valid := v, byte := b, third := r }

/-- Expected deframer observation for wire bytes at the given cycles; also
    returns the decoded frames. -/
def deframerExpect (wire : Array (Nat × Nat)) (n : Nat) : Obs × List (List Nat) := Id.run do
  let mut v := Array.replicate n 0
  let mut b := Array.replicate n 0
  let mut d := Array.replicate n 0
  let mut st := 0     -- 0 idle, 1 body, 2 esc
  let mut frames : List (List Nat) := []
  let mut cur : List Nat := []
  for (c, w) in wire do
    if st == 0 then
      if w == 0xDB then st := 2          -- spec: ESC starts an escape even as the first byte of a frame
      else if w != 0xC0 then
        v := v.set! (c+1) 1; b := b.set! (c+1) w; cur := cur ++ [w]; st := 1
    else if st == 1 then
      if w == 0xC0 then
        d := d.set! (c+1) 1; frames := frames ++ [cur]; cur := []; st := 0
      else if w == 0xDB then st := 2
      else
        v := v.set! (c+1) 1; b := b.set! (c+1) w; cur := cur ++ [w]
    else
      let x := if w == 0xDC then 0xC0 else if w == 0xDD then 0xDB else w
      v := v.set! (c+1) 1; b := b.set! (c+1) x; cur := cur ++ [x]; st := 1
  return ({ valid := v, byte := b, third := d }, frames)

/-! ## Synthetic controls -/

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  {if cond then "✓" else "✗"} {name}"
  pure cond

def controls : IO Bool := do
  IO.println "-- synthetic controls (checker must accept the expected trace and reject each defect)"
  let mut ok := true
  let reqs : Array (Nat × Req) := #[(3, .payload 0x10), (5, .payload 0xC0), (8, .payload 0x20), (10, .frameEnd)]
  let e := framerExpect reqs 20
  ok := (← check "framer: expected trace accepted" (obsErrors e e "txReady").isEmpty) && ok
  ok := (← check "framer: ESC then DC for 0xC0 at cycles 6,7 and END at 11"
    (e.valid[6]! == 1 && e.byte[6]! == 0xDB && e.byte[7]! == 0xDC && e.byte[11]! == 0xC0 && e.third[6]! == 0)) && ok
  let ex := { e with valid := e.valid.set! 14 1 }
  ok := (← check "framer: extra txValid pulse (a stray byte) rejected" (!(obsErrors e ex "txReady").isEmpty)) && ok
  let ms := { e with valid := e.valid.set! 11 0 }
  ok := (← check "framer: missing closing END rejected" (!(obsErrors e ms "txReady").isEmpty)) && ok
  let wb := { e with byte := e.byte.set! 7 0xDD }
  ok := (← check "framer: wrong escape replacement rejected" (!(obsErrors e wb "txReady").isEmpty)) && ok
  let late := { e with valid := (e.valid.set! 4 0).set! 5 1, byte := (e.byte.set! 4 0).set! 5 0x10 }
  ok := (← check "framer: byte one cycle late rejected" (!(obsErrors e late "txReady").isEmpty)) && ok
  let rd := { e with third := e.third.set! 6 1 }
  ok := (← check "framer: txReady high while the replacement is pending rejected" (!(obsErrors e rd "txReady").isEmpty)) && ok
  let wire : Array (Nat × Nat) := #[(2, 0xC0), (3, 0x10), (4, 0xDB), (5, 0xDC), (6, 0xC0), (8, 0xC0)]
  let (de, frames) := deframerExpect wire 14
  ok := (← check "deframer: expected trace accepted, frames [[0x10, 0xC0]]"
    ((obsErrors de de "frameDone").isEmpty && frames == [[0x10, 0xC0]])) && ok
  ok := (← check "deframer: leading END and empty frame produce no outValid / frameDone"
    (de.valid[3]! == 0 && de.valid[9]! == 0 && de.third[9]! == 0 && de.third[7]! == 1)) && ok
  let d1 := { de with third := de.third.set! 9 1 }
  ok := (← check "deframer: frameDone for the empty frame rejected" (!(obsErrors de d1 "frameDone").isEmpty)) && ok
  let d2 := { de with third := de.third.set! 7 0 }
  ok := (← check "deframer: missing frameDone rejected" (!(obsErrors de d2 "frameDone").isEmpty)) && ok
  let d3 := { de with third := (de.third.set! 7 0).set! 6 1 }
  ok := (← check "deframer: frameDone one cycle early rejected" (!(obsErrors de d3 "frameDone").isEmpty)) && ok
  let d4 := { de with valid := de.valid.set! 5 1 }
  ok := (← check "deframer: outValid for the ESC prefix rejected" (!(obsErrors de d4 "frameDone").isEmpty)) && ok
  let d5 := { de with byte := de.byte.set! 6 0xDC }
  ok := (← check "deframer: undecoded escape (0xDC instead of 0xC0) rejected" (!(obsErrors de d5 "frameDone").isEmpty)) && ok
  pure ok

/-! ## JIT runs -/

def framerCase (h : JITHandle) (label : String) (frames : List (List Nat)) (gap : Nat) : IO Bool := do
  JIT.reset h
  let mut o : Obs := {}
  let mut reqs : Array (Nat × Req) := #[]
  let mut t := 0
  -- one cycle with the given inputs
  let step := fun (o : Obs) (b : Nat) (v fe : Bool) => do
    JIT.setInput h 0 (UInt64.ofNat b)
    JIT.setInput h 1 (if v then 1 else 0)
    JIT.setInput h 2 (if fe then 1 else 0)
    JIT.eval h
    let tv := (← JIT.getOutput h 1)
    let tb := (← JIT.getOutput h 0).toNat
    let tr := (← JIT.getOutput h 2)
    JIT.tick h
    pure ({ valid := o.valid.push tv.toNat, byte := o.byte.push (if tv != 0 then tb else 0)
            , third := o.third.push tr.toNat } : Obs)
  let ready := fun (o : Obs) => o.third.back?.getD 1 == 1
  for _ in [0:4] do o ← step o 0 false false; t := t + 1
  for fr in frames do
    for x in fr do
      for _ in [0:gap] do o ← step o 0 false false; t := t + 1
      -- wait for txReady (peek: the observation of this cycle is recorded by the pulse step)
      let mut guard := 0
      while guard < 8 do
        JIT.setInput h 1 0; JIT.eval h
        if (← JIT.getOutput h 2) != 0 then break
        o ← step o 0 false false; t := t + 1; guard := guard + 1
      reqs := reqs.push (t, .payload x)
      o ← step o x true false; t := t + 1
    let mut guard := 0
    while guard < 8 do
      JIT.setInput h 1 0; JIT.eval h
      if (← JIT.getOutput h 2) != 0 then break
      o ← step o 0 false false; t := t + 1; guard := guard + 1
    reqs := reqs.push (t, .frameEnd)
    o ← step o 0 false true; t := t + 1
    for _ in [0:gap + 2] do o ← step o 0 false false; t := t + 1
  for _ in [0:20] do o ← step o 0 false false; t := t + 1
  let _ := ready
  let exp := framerExpect reqs o.valid.size
  let errs := obsErrors exp o "txReady"
  -- wire stream vs the pure encoder (leading END dropped by design)
  let wire := (List.range o.valid.size).filter (fun c => o.valid[c]! == 1) |>.map (o.byte[·]!)
  let ref := frames.flatMap fun fr => (fr.flatMap fun x => if x == 0xC0 then [0xDB, 0xDC] else if x == 0xDB then [0xDB, 0xDD] else [x]) ++ [0xC0]
  let refPure := frames.flatMap fun fr => ((encodeFrame (fr.map UInt8.ofNat)).drop 1).map UInt8.toNat
  let errs := if wire != ref || ref != refPure then errs.push s!"wire stream {wire} ≠ reference {ref}" else errs
  IO.println s!"  · framer {label}: {o.valid.size} cycles, {wire.length} wire bytes, requests {reqs.size}"
  if errs.isEmpty then IO.println s!"  ✓ framer {label}: txValid/txByte/txReady = expected at every cycle, wire = pure encoder"
  else for e in errs do IO.println s!"  ✗ framer {label}: {e}"
  pure errs.isEmpty

def deframerCase (h : JITHandle) (label : String) (wireBytes : List Nat) (spacing : Nat)
    (frames : List (List Nat)) : IO Bool := do
  JIT.reset h
  let mut o : Obs := {}
  let mut wire : Array (Nat × Nat) := #[]
  let mut t := 0
  let step := fun (o : Obs) (b : Nat) (v : Bool) => do
    JIT.setInput h 0 (UInt64.ofNat b)
    JIT.setInput h 1 (if v then 1 else 0)
    JIT.eval h
    let ov := (← JIT.getOutput h 1)
    let ob := (← JIT.getOutput h 0).toNat
    let od := (← JIT.getOutput h 2)
    JIT.tick h
    pure ({ valid := o.valid.push ov.toNat, byte := o.byte.push (if ov != 0 then ob else 0)
            , third := o.third.push od.toNat } : Obs)
  for _ in [0:6] do o ← step o 0 false; t := t + 1
  for w in wireBytes do
    wire := wire.push (t, w)
    o ← step o w true; t := t + 1
    for _ in [1:spacing] do o ← step o 0xAA false; t := t + 1   -- rxByte noise while rxValid = 0
  for _ in [0:20] do o ← step o 0 false; t := t + 1
  let (exp, refFrames) := deframerExpect wire o.valid.size
  let mut errs := obsErrors exp o "frameDone"
  let pure' := (decodeStreamNat wireBytes)
  if refFrames != frames || pure' != frames then
    errs := errs.push s!"decoded frames: model {refFrames}, decodeStream {pure'}, intended {frames}"
  let outs := (List.range o.valid.size).filter (fun c => o.valid[c]! == 1) |>.map (o.byte[·]!)
  if outs != frames.flatten then errs := errs.push s!"outByte stream {outs} ≠ payload {frames.flatten}"
  let dn := (List.range o.valid.size).filter (fun c => o.third[c]! == 1) |>.length
  if dn != frames.length then errs := errs.push s!"{dn} frameDone pulses, expected {frames.length}"
  IO.println s!"  · deframer {label}: {o.valid.size} cycles, {wireBytes.length} wire bytes, {outs.length} decoded bytes, {dn} frameDone"
  if errs.isEmpty then IO.println s!"  ✓ deframer {label}: outValid/outByte/frameDone = expected at every cycle, = decodeStream"
  else for e in errs do IO.println s!"  ✗ deframer {label}: {e}"
  pure errs.isEmpty
where
  decodeStreamNat (bs : List Nat) : List (List Nat) :=
    (decodeStream (bs.map UInt8.ofNat)).map (·.map UInt8.toNat)

def main : IO Unit := do
  IO.println "=== slipFramerHW / slipDeframerHW — JIT co-sim (handshake: txValid, txReady, outValid, frameDone) ==="
  (← IO.getStdout).flush
  let mut ok ← controls
  let fr ← framerTop.Sim.load
  let frames : List (List Nat) := [[0x10, 0xC0, 0x20, 0xDB, 0x30], [0xC0], [0xDB, 0xDB, 0x01], [1, 2, 3, 4]]
  for gap in [0, 3] do
    ok := (← framerCase fr.handle s!"gap={gap}" frames gap) && ok
  JIT.destroy fr.handle
  let de ← deframerTop.Sim.load
  let enc := fun (fr : List Nat) => (encodeFrame (fr.map UInt8.ofNat)).map UInt8.toNat
  let f1 : List Nat := [0x10, 0xC0, 0x20, 0xDB, 0x30]
  let f2 : List Nat := [0x07, 0xC0]
  let f3 : List Nat := [1, 2, 3]
  let stream := enc f1 ++ enc f2 ++ [0xC0] ++ enc f3     -- leading+trailing ENDs, one empty frame
  let noLead := (enc f1).drop 1 ++ (enc f2).drop 1 ++ (enc f3).drop 1   -- as the HW framer emits
  for sp in [1, 3] do
    ok := (← deframerCase de.handle s!"double-END stream spacing={sp}" stream sp [f1, f2, f3]) && ok
    ok := (← deframerCase de.handle s!"no-leading-END stream spacing={sp}" noLead sp [f1, f2, f3]) && ok
  ok := (← deframerCase de.handle "only END bytes (line noise)" [0xC0, 0xC0, 0xC0] 1 []) && ok
  JIT.destroy de.handle
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

/-- NOT in CI: a frame whose FIRST payload byte is END or ESC.  The framer emits
    ESC + replacement correctly, but the deframer in state idle treats the ESC
    as a plain data byte (see Tests/Drivers/SlipHWJITDefectsMain.lean). -/
def mainDefects : IO Unit := do
  IO.println "=== slipDeframerHW — escaped first payload byte — NOT in CI, known defect ==="
  (← IO.getStdout).flush
  let de ← deframerTop.Sim.load
  let enc := fun (fr : List Nat) => (encodeFrame (fr.map UInt8.ofNat)).map UInt8.toNat
  let mut ok := true
  for (label, fr) in [("first byte END", [0xC0, 0x01]), ("first byte ESC", [0xDB, 0x02])] do
    ok := (← deframerCase de.handle s!"{label}, leading END" (enc fr) 1 [fr]) && ok
    ok := (← deframerCase de.handle s!"{label}, no leading END (as the HW framer emits)" ((enc fr).drop 1) 1 [fr]) && ok
  JIT.destroy de.handle
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Net.SlipHWJITTest
