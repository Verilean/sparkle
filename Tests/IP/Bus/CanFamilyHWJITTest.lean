/-
  JIT co-sim of the generated hardware of the CAN-family blocks that carry
  start / valid / error strobes, checked cycle by cycle against pure references
  (the existing CANHWTest / CANopenHWTest / DroneCANHWTest feed a short list
  through the Signal interpreter and look at one sample).  There is no CAN
  frame controller in `IP/Bus/CANHW.lean`; its only block is the CRC-15 LFSR.

  Blocks (all `#sim` tops below, ports numbered in argument / field order):
  * `crc15HW`   (start, bitIn, valid → crc): a `start` cycle zeroes the register
    (also when `valid` is high), `valid` shifts one bit in, otherwise it holds.
    Reference: `IP.Bus.CAN.crc15Step` applied per cycle (random start / valid /
    bit streams; the output at cycle t is the register before cycle t's inputs).
    Frame-level: for classic frames (standard / extended, with and without
    data) the register after the bits before the CRC field equals the frame's
    CRC field, and after the CRC field too it is 0 (the CRC residue).
  * `nmtStateFsmHW` (reset, cmdIn, valid → state): the CANopen NMT state after
    each cycle.  Reference: `IP.Bus.CANopen.NmtCommand.ofByte?` mapped to the
    state (start → 1 operational, stop → 2, pre-op → 0, reset node / reset
    communication → 3 boot-up, any other byte holds), only when `valid`;
    `reset` forces boot-up (3) and beats `valid`; initial state 3.
  * `transferIdTrackerHW` (tid, tog, sot, eot, valid → expectedTid,
    expectedTog, error): the sticky `error` strobe.  Reference by construction
    from multi-frame transfers: `error` rises the cycle after the first mid
    frame with a wrong toggle / transfer id (also after a lost frame), stays
    high until the cycle after the next SOT frame, never before the first
    frame, never on clean transfers, and ignores everything while `valid` is
    low (garbage on tid / tog / sot / eot in those cycles).  Random streams are
    additionally compared with a per-cycle model of the documented tracker.

  Synthetic controls for every comparison run first (no JIT): the ideal trace
  must be accepted and a single flipped sample, a one-cycle delay, a held value
  and a spurious / missing strobe must be rejected.  Live controls: a reference
  built with another polynomial / command table / transfer id must be rejected.
-/
import IP.Bus.CANHW
import IP.Bus.CAN
import IP.Bus.CANopen
import IP.Bus.CANopenHW
import IP.Bus.DroneCANHW
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Bus

namespace Sparkle.Tests.IP.Bus.CanFamilyHWJITTest

set_option maxRecDepth 100000

def crcTop (start : Signal defaultDomain Bool) (bitIn : Signal defaultDomain Bool)
    (valid : Signal defaultDomain Bool) : CANHW.CRC15Out defaultDomain :=
  CANHW.crc15HW start bitIn valid

def nmtTop (reset : Signal defaultDomain Bool) (cmdIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) : CANopenHW.NmtStateOut defaultDomain :=
  CANopenHW.nmtStateFsmHW reset cmdIn valid

def tidTop (tid : Signal defaultDomain (BitVec 5)) (tog sot eot valid : Signal defaultDomain Bool) :
    DroneCANHW.TidOut defaultDomain :=
  DroneCANHW.transferIdTrackerHW tid tog sot eot valid

#sim crcTop
#sim nmtTop
#sim tidTop

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  {if cond then "✓" else "✗"} {name}"
  pure cond

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
def rnd (x : Nat) : Nat × Nat := let y := lcg x; (y, y / 4294967296)

/-! ## Generic per-cycle comparison -/

/-- First differing cycles of two traces (empty = equal). -/
def traceErrors (what : String) (exp act : Array Nat) : Array String := Id.run do
  let mut errs := #[]
  if exp.size != act.size then errs := errs.push s!"{what}: {act.size} samples, expected {exp.size}"
  for c in [0:min exp.size act.size] do
    if exp[c]! != act[c]! && errs.size < 3 then
      errs := errs.push s!"{what}: cycle {c}: {act[c]!}, expected {exp[c]!}"
  return errs

/-- The comparison itself must accept `t`, and reject a flip, a one-cycle delay,
    a held value and a missing change (when the trace has changes). -/
def traceControls (what : String) (t : Array Nat) : IO Bool := do
  let mut ok ← check s!"{what}: ideal trace accepted" (traceErrors what t t).isEmpty
  let n := t.size
  let mid := n / 2
  ok := (← check s!"{what}: single flipped sample rejected"
    (!(traceErrors what t (t.modify mid (· + 1))).isEmpty)) && ok
  ok := (← check s!"{what}: one-cycle delay rejected"
    (!(traceErrors what t (#[t[0]!] ++ t.pop)).isEmpty)) && ok
  ok := (← check s!"{what}: held value rejected"
    (!(traceErrors what t (Array.replicate n t[0]!)).isEmpty)) && ok
  pure ok

/-! ## CRC-15 -/

def crcRef (poly : Bool) (ins : Array (Bool × Bool × Bool)) : Array Nat := Id.run do
  let mut crc := 0
  let mut out := #[]
  for (s, b, v) in ins do
    out := out.push crc
    crc := if s then 0 else if v then
        (if poly then CAN.crc15Step crc b
         else
           -- a wrong polynomial (control)
           let x := ((crc >>> 14) &&& 1) ^^^ (if b then 1 else 0)
           let sh := (crc <<< 1) &&& 0x7FFF
           if x == 1 then sh ^^^ 0x4598 else sh)
      else crc
  return out

def runCrc (h : JITHandle) (ins : Array (Bool × Bool × Bool)) : IO (Array Nat) := do
  JIT.reset h
  let mut out := #[]
  for (s, b, v) in ins do
    JIT.setInput h 0 (if s then 1 else 0)
    JIT.setInput h 1 (if b then 1 else 0)
    JIT.setInput h 2 (if v then 1 else 0)
    JIT.eval h
    out := out.push (← JIT.getOutput h 0).toNat
    JIT.tick h
  pure out

def crcRandom (n seed : Nat) : Array (Bool × Bool × Bool) := Id.run do
  let mut x := seed
  let mut ins := #[]
  for _ in [0:n] do
    let (x1, a) := rnd x
    let (x2, b) := rnd x1
    x := x2
    ins := ins.push (a % 29 == 0, b % 2 == 0, (a / 7) % 3 != 0)
  return ins

/-- Frame-level stimulus: idle gap, `start` cycle, then the bits, one per cycle. -/
def frameStim (bits : List Bool) (gap : Nat) : Array (Bool × Bool × Bool) :=
  (Array.replicate gap (false, true, false)) ++ #[(true, false, false)]
    ++ (bits.map fun b => (false, b, true)).toArray ++ #[(false, true, false)]

def mkFrames : Array CAN.Frame := #[
  { kind := .standard, id := 0x7C5, rtr := false, dlc := 1, data := #[0xAA] },
  { kind := .standard, id := 0x123, rtr := false, dlc := 8, data := #[1,2,3,4,5,6,7,8] },
  { kind := .standard, id := 0x001, rtr := true, dlc := 0, data := #[] },
  { kind := .standard, id := 0x555, rtr := false, dlc := 0, data := #[] },
  { kind := .extended, id := 0x1ABCDE01, rtr := false, dlc := 4, data := #[0xDE, 0xAD, 0xBE, 0xEF] },
  { kind := .extended, id := 0x00000000, rtr := false, dlc := 0, data := #[] },
  { kind := .extended, id := 0x1FFFFFFF, rtr := false, dlc := 8, data := #[0xFF,0xFF,0xFF,0xFF,0,0,0,0x80] }]

def crcSuite (h : JITHandle) : IO Bool := do
  IO.println "-- CRC-15 (crc15HW): controls"
  let mut ok := true
  let ins := crcRandom 600 7
  ok := (← traceControls "crc15" (crcRef true ins)) && ok
  IO.println "-- CRC-15: random start / valid / bit streams vs crc15Step, per cycle"
  for seed in [1, 2, 3, 4] do
    let ins := crcRandom 3000 seed
    let act ← runCrc h ins
    let errs := traceErrors "crc" (crcRef true ins) act
    let nStart := (ins.filter fun (s, _, _) => s).size
    let nValid := (ins.filter fun (_, _, v) => v).size
    IO.println s!"  · seed {seed}: 3000 cycles, {nStart} start pulses, {nValid} valid bits"
    ok := (← check s!"seed {seed}: crc register equals crc15Step every cycle" errs.isEmpty) && ok
    for e in errs do IO.println s!"    {e}"
  IO.println "-- CRC-15: real classic frames (CRC field and residue)"
  for f in mkFrames do
    let bits := CAN.buildDynamicBits f
    let body := bits.take (bits.length - 15)
    let crcField := (bits.drop (bits.length - 15)).foldl (fun a b => a * 2 + (if b then 1 else 0)) 0
    let st := frameStim body 3
    let act ← runCrc h st
    let tag := s!"{repr f.kind} id=0x{String.ofList (Nat.toDigits 16 f.id)} dlc={f.dlc}"
    ok := (← check s!"{tag}: register after the body = CRC field 0x{String.ofList (Nat.toDigits 16 crcField)}"
      (act[st.size - 1]! == crcField && crcField == CAN.crc15 body)) && ok
    let st2 := frameStim bits 0
    let act2 ← runCrc h st2
    ok := (← check s!"{tag}: register after body + CRC field = 0 (residue)" (act2[st2.size - 1]! == 0)) && ok
    ok := (← check s!"{tag}: per-cycle trace equals the reference"
      (traceErrors "crc" (crcRef true st2) act2).isEmpty) && ok
  IO.println "-- CRC-15: live negative controls"
  let ins := crcRandom 3000 11
  let act ← runCrc h ins
  ok := (← check "reference with another polynomial flags the run"
    (!(traceErrors "crc" (crcRef false ins) act).isEmpty)) && ok
  ok := (← check "reference ignoring `start` priority flags the run"
    (!(traceErrors "crc" (crcRef true (ins.map fun (s, b, v) => (s && !v, b, v))) act).isEmpty)) && ok
  pure ok

/-! ## CANopen NMT state -/

def nmtNext (st : Nat) (cmd : Nat) : Nat :=
  match CANopen.NmtCommand.ofByte? (UInt8.ofNat cmd) with
  | some .startRemoteNode => 1
  | some .stopRemoteNode => 2
  | some .enterPreOperational => 0
  | some .resetNode => 3
  | some .resetCommunication => 3
  | none => st

def nmtRef (swap : Bool) (ins : Array (Bool × Nat × Bool)) : Array Nat := Id.run do
  let mut st := 3
  let mut out := #[]
  for (r, c, v) in ins do
    out := out.push st
    st := if r then 3 else if v then (if swap && c == 0x80 then 2 else nmtNext st c) else st
  return out

def runNmt (h : JITHandle) (ins : Array (Bool × Nat × Bool)) : IO (Array Nat) := do
  JIT.reset h
  let mut out := #[]
  for (r, c, v) in ins do
    JIT.setInput h 0 (if r then 1 else 0)
    JIT.setInput h 1 (UInt64.ofNat c)
    JIT.setInput h 2 (if v then 1 else 0)
    JIT.eval h
    out := out.push (← JIT.getOutput h 0).toNat
    JIT.tick h
  pure out

def nmtRandom (n seed : Nat) : Array (Bool × Nat × Bool) := Id.run do
  let mut x := seed
  let mut ins := #[]
  let cmds := #[0x01, 0x02, 0x80, 0x81, 0x82]
  for _ in [0:n] do
    let (x1, a) := rnd x
    let (x2, b) := rnd x1
    x := x2
    let c := if a % 4 == 0 then b % 256 else cmds[b % 5]!
    ins := ins.push (a % 37 == 0, c, (a / 5) % 2 == 0)
  return ins

def nmtSuite (h : JITHandle) : IO Bool := do
  IO.println "-- CANopen NMT (nmtStateFsmHW): controls"
  let mut ok := true
  ok := (← traceControls "nmt" (nmtRef false (nmtRandom 600 5))) && ok
  IO.println "-- NMT: random streams vs the NmtCommand table, per cycle"
  for seed in [1, 2, 3] do
    let ins := nmtRandom 3000 seed
    let act ← runNmt h ins
    let errs := traceErrors "nmt" (nmtRef false ins) act
    let visited := (List.range 4).map fun s => (act.toList.filter (· == s)).length
    IO.println s!"  · seed {seed}: cycles per state (pre-op, oper, stopped, boot) = {visited}"
    ok := (← check s!"seed {seed}: state equals the reference every cycle" errs.isEmpty) && ok
    for e in errs do IO.println s!"    {e}"
  IO.println "-- NMT: directed sequence (valid gating, reset priority, unknown bytes)"
  let seq : Array (Bool × Nat × Bool) := #[
    (false, 0x01, false), (false, 0x01, false),          -- valid low: stays boot-up
    (false, 0x01, true), (false, 0x55, true), (false, 0x02, true),
    (false, 0x01, false), (false, 0x80, true), (false, 0x00, true),
    (false, 0x01, true), (true, 0x01, true),              -- reset beats valid + start
    (false, 0x81, false), (false, 0x01, true), (false, 0x82, true), (false, 0x80, true),
    (false, 0x80, false), (false, 0x03, true), (false, 0xFF, true)]
  let act ← runNmt h seq
  ok := (← check "directed sequence: states 3,3,3,1,1,2,2,0,0,1,3,3,1,3,0,0,0"
    (act.toList == [3, 3, 3, 1, 1, 2, 2, 0, 0, 1, 3, 3, 1, 3, 0, 0, 0])) && ok
  IO.println s!"  · observed {act.toList}"
  IO.println "-- NMT: live negative control"
  let ins := nmtRandom 3000 9
  let act ← runNmt h ins
  ok := (← check "reference with a different command table flags the run"
    (!(traceErrors "nmt" (nmtRef true ins) act).isEmpty)) && ok
  pure ok

/-! ## DroneCAN transfer-id tracker -/

structure Fr where
  tid : Nat
  tog : Bool
  sot : Bool
  eot : Bool
  valid : Bool
  deriving Inhabited

/-- Documented per-cycle model: outputs (tid, tog, err) before each cycle. -/
def trkRef (frs : Array Fr) : Array (Nat × Nat × Nat) := Id.run do
  let mut tid := 0
  let mut tog := false
  let mut err := false
  let mut out := #[]
  for f in frs do
    out := out.push (tid, if tog then 1 else 0, if err then 1 else 0)
    let mid := f.valid && !f.sot
    let mism := f.tog != tog || f.tid != tid
    let sotV := f.valid && f.sot
    let tog' := if sotV then true else if mid then !tog else tog
    let tid' := if sotV then f.tid else tid
    let err' := if mid && mism then true else if sotV then false else err
    tid := tid'; tog := tog'; err := err'
  return out

def runTrk (h : JITHandle) (frs : Array Fr) : IO (Array (Nat × Nat × Nat)) := do
  JIT.reset h
  let mut out := #[]
  for f in frs do
    JIT.setInput h 0 (UInt64.ofNat f.tid)
    JIT.setInput h 1 (if f.tog then 1 else 0)
    JIT.setInput h 2 (if f.sot then 1 else 0)
    JIT.setInput h 3 (if f.eot then 1 else 0)
    JIT.setInput h 4 (if f.valid then 1 else 0)
    JIT.eval h
    out := out.push ((← JIT.getOutput h 0).toNat, (← JIT.getOutput h 1).toNat, (← JIT.getOutput h 2).toNat)
    JIT.tick h
  pure out

inductive Flaw where
  | none | flipTog (k : Nat) | wrongTid (k : Nat) | dropFrame (k : Nat)

/-- A transfer of `n` frames with the given flaw.  Returns the frames
    (valid cycles only) and, per frame, whether it is a "bad mid frame". -/
def transfer (tid n : Nat) (fl : Flaw) : Array (Fr × Bool) := Id.run do
  let mut out := #[]
  for k in [0:n] do
    let tog := k % 2 == 1
    let base : Fr := { tid, tog, sot := k == 0, eot := k + 1 == n, valid := true }
    match fl with
    | .dropFrame d => if k != d then out := out.push (base, false)
    | .flipTog d => out := out.push (if k == d then { base with tog := !tog } else base, k == d && k != 0)
    | .wrongTid d => out := out.push (if k == d then { base with tid := (tid + 1) % 32 } else base, k == d && k != 0)
    | .none => out := out.push (base, false)
  return out

/-- After a dropped frame the next frame carries the wrong toggle (the design
    flips on every received mid frame): mark the first frame after the gap. -/
def markDrop (tid n d : Nat) : Array (Fr × Bool) :=
  let t := transfer tid n (.dropFrame d)
  if d == 0 || d + 1 >= n then t   -- lost SOT / lost EOT: nothing detectable here
  else t.mapIdx fun i (f, _) => (f, i == d)

/-- Build the cycle stream from transfers: random gap cycles (valid low, garbage on
    every other input) between frames.  Also returns, for each cycle, the error
    value expected *by construction*: false until the first bad mid frame of a
    transfer has been seen, cleared by the next SOT. -/
def buildScenario (seed : Nat) (ts : Array (Array (Fr × Bool))) : Array Fr × Array Nat := Id.run do
  let mut x := seed
  let mut frs : Array Fr := #[]
  let mut expErr : Array Nat := #[]
  let mut err := 0
  let garbage := fun (x : Nat) =>
    let (y, a) := rnd x
    (y, { tid := a % 32, tog := a % 2 == 0, sot := a % 3 == 0, eot := a % 5 == 0, valid := false : Fr })
  for _ in [0:3] do   -- idle prologue with garbage
    let (y, g) := garbage x
    x := y; frs := frs.push g; expErr := expErr.push 0
  for t in ts do
    for (f, bad) in t do
      let (y, a) := rnd x
      x := y
      for _ in [0:a % 3] do
        let (y2, g) := garbage x
        x := y2; frs := frs.push g; expErr := expErr.push err
      -- the frame cycle shows the error accumulated so far; the effect appears next cycle
      frs := frs.push f; expErr := expErr.push err
      if f.sot then err := 0
      if bad then err := 1
  for _ in [0:4] do
    let (y, g) := garbage x
    x := y; frs := frs.push g; expErr := expErr.push err
  return (frs, expErr)

def trkRandom (n seed : Nat) : Array Fr := Id.run do
  let mut x := seed
  let mut out := #[]
  for _ in [0:n] do
    let (x1, a) := rnd x
    let (x2, b) := rnd x1
    x := x2
    out := out.push { tid := (if a % 4 == 0 then b else a) % 32, tog := b % 2 == 0, sot := a % 5 == 0,
                      eot := b % 7 == 0, valid := (a / 3) % 3 != 0 }
  return out

def errTrace (o : Array (Nat × Nat × Nat)) : Array Nat := o.map fun (_, _, e) => e

def trkSuite (h : JITHandle) : IO Bool := do
  IO.println "-- DroneCAN tracker (transferIdTrackerHW): controls"
  let mut ok := true
  let ts : Array (Array (Fr × Bool)) := #[transfer 3 4 .none, transfer 9 5 (.flipTog 2), transfer 4 3 .none,
    transfer 7 4 (.wrongTid 1), transfer 7 1 .none, transfer 12 6 .none]
  let (frs0, exp0) := buildScenario 3 ts
  ok := (← traceControls "tracker error" exp0) && ok
  -- the error trace of the ideal scenario has both edges; delaying it by a cycle is wrong
  let rises := (List.range (exp0.size - 1)).filter fun i => exp0[i]! == 0 && exp0[i+1]! == 1
  let falls := (List.range (exp0.size - 1)).filter fun i => exp0[i]! == 1 && exp0[i+1]! == 0
  ok := (← check "scenario has 2 error rises and 2 error falls (2 flawed transfers)" (rises.length == 2 && falls.length == 2)) && ok
  ok := (← check "spurious error strobe on a clean transfer rejected"
    (!(traceErrors "err" exp0 (exp0.modify 7 fun _ => 1)).isEmpty)) && ok
  ok := (← check "missing error strobe rejected"
    (!(traceErrors "err" exp0 (exp0.map fun _ => 0)).isEmpty)) && ok
  IO.println "-- tracker: constructed transfers (clean, flipped toggle, wrong tid, lost mid frame, single frame)"
  let ts : Array (Array (Fr × Bool)) := #[
    transfer 3 4 .none, transfer 9 5 (.flipTog 2), transfer 4 3 .none,
    transfer 7 4 (.wrongTid 1), transfer 7 1 .none, markDrop 12 6 2, transfer 12 6 .none,
    markDrop 20 4 3, transfer 31 3 .none, transfer 0 2 (.flipTog 1), transfer 0 2 .none]
  for seed in [1, 2, 3] do
    let (frs, expE) := buildScenario seed ts
    let act ← runTrk h frs
    let errs := traceErrors "error" expE (errTrace act)
    let nRise := ((List.range (expE.size - 1)).filter fun i => expE[i]! == 0 && expE[i+1]! == 1).length
    let obsRise := ((List.range (act.size - 1)).filter fun i => (act[i]!).2.2 == 0 && (act[i+1]!).2.2 == 1).length
    IO.println s!"  · seed {seed}: {frs.size} cycles, error rises expected {nRise}, observed {obsRise}"
    ok := (← check s!"seed {seed}: error strobe equals the by-construction timeline" errs.isEmpty) && ok
    for e in errs do IO.println s!"    {e}"
    ok := (← check s!"seed {seed}: expectedTid / expectedTog / error equal the documented model"
      (act == trkRef frs)) && ok
  IO.println "-- tracker: random streams vs the documented per-cycle model"
  for seed in [1, 2, 3] do
    let frs := trkRandom 3000 seed
    let act ← runTrk h frs
    let nErr := (act.filter fun (_, _, e) => e == 1).size
    IO.println s!"  · seed {seed}: 3000 cycles, error high in {nErr}"
    ok := (← check s!"seed {seed}: all three outputs equal the model every cycle" (act == trkRef frs)) && ok
  IO.println "-- tracker: live negative controls"
  let (frs, _) := buildScenario 1 ts
  let act ← runTrk h frs
  let ts2 : Array (Array (Fr × Bool)) := ts.set! 2 (transfer 4 3 (.flipTog 1))
  let (_, expOther) := buildScenario 1 ts2
  ok := (← check "timeline of another script flags the run" (!(traceErrors "error" expOther (errTrace act)).isEmpty)) && ok
  ok := (← check "model told `valid` is ignored flags the run"
    (act != trkRef (frs.map fun f => { f with valid := true }))) && ok
  pure ok

def main : IO Unit := do
  IO.println "=== CAN family (crc15HW, nmtStateFsmHW, transferIdTrackerHW) — JIT co-sim ==="
  (← IO.getStdout).flush
  let crc ← crcTop.Sim.load
  let nmt ← nmtTop.Sim.load
  let trk ← tidTop.Sim.load
  let mut ok := true
  ok := (← crcSuite crc.handle) && ok
  ok := (← nmtSuite nmt.handle) && ok
  ok := (← trkSuite trk.handle) && ok
  JIT.destroy crc.handle
  JIT.destroy nmt.handle
  JIT.destroy trk.handle
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.CanFamilyHWJITTest
