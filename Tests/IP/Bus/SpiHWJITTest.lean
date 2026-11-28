/-
  JIT co-sim of the generated hardware for the SPI master
  `IP.Bus.SPIHW.spiMasterHW`, checked cycle by cycle (the existing SPIHWTest
  runs one transfer at bitDiv = 0 through the Signal interpreter and only asks
  whether `done` was seen at least once).

  Ports after `#sim` lowering: inputs start = 0, cpol = 1, cpha = 2, bitDiv = 3,
  mosiByte = 4, misoBit = 5; outputs sclk = 0, mosi = 1, cs = 2, misoByte = 3,
  done = 4.

  A slave model sits on the pins: it drives MISO with its byte MSB first
  (next bit one cycle after SCLK returns to its idle level) and records MOSI at
  every leading SCLK edge.  Three back-to-back transfers with different bytes
  run for cpol ∈ {0,1} and bitDiv ∈ {0,1,3}; `start` is a 1-cycle pulse on a
  divider-tick cycle (see `Defects` below for what happens otherwise).

  `spiErrors` (in CI) checks per transfer: `cs` high before and falls the cycle
  after the start pulse; `done` exactly once and exactly 1 cycle wide; cs low
  from start to `done` and high again the cycle after; exactly 16 SCLK
  toggles inside the transfer and SCLK back at its idle level (= cpol) at
  `done`; `misoByte` at `done` = the slave byte and unchanged until the next
  transfer; no `done` before the first start or after the last; SCLK = cpol
  whenever cs is high (after the first 2 cycles).
  The MOSI check (`strictMosi`: the 8 bits seen at the 8 leading edges, MSB
  first, equal the byte sent) is NOT part of the CI exe: it fails today; see
  Tests/Drivers/SpiHWJITDefectsMain.lean.
  Synthetic controls for every check run first (no JIT).
-/
import IP.Bus.SPIHW
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Bus.SPIHW

namespace Sparkle.Tests.IP.Bus.SpiHWJITTest

set_option maxRecDepth 100000

def spiTop (start : Signal defaultDomain Bool) (cpol cpha : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) (mosiByte : Signal defaultDomain (BitVec 8))
    (misoBit : Signal defaultDomain Bool) : MasterOut defaultDomain :=
  spiMasterHW start cpol cpha bitDiv mosiByte misoBit

#sim spiTop

structure Cyc where
  sclk : Bool
  mosi : Bool
  cs : Bool
  miso : Nat
  done : Bool
  deriving Inhabited

/-! ## Pure checker -/

def hexB (b : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 b)

/-- Violations of the SPI master contract on a trace.  `starts[i]` is the cycle
    of the i-th start pulse; `mosiB[i]` / `misoB[i]` the bytes sent / returned
    by the slave. -/
def spiErrors (tr : Array Cyc) (cpol : Bool) (starts mosiB misoB : Array Nat)
    (strictMosi : Bool) : Array String := Id.run do
  let mut errs : Array String := #[]
  let n := tr.size
  if n > 0 && !tr[0]!.cs then errs := errs.push "cs low at cycle 0"
  -- idle level of SCLK whenever cs is high
  for c in [2:n] do
    if tr[c]!.cs && tr[c]!.sclk != cpol then
      errs := errs.push s!"cycle {c}: sclk {tr[c]!.sclk} while idle (cs high), cpol is {cpol}"
      break
  if starts.size > 0 then
    for c in [0:starts[0]!] do
      if tr[c]!.done then
        errs := errs.push s!"done at cycle {c}, before the first start at {starts[0]!}"
        break
  for i in [0:starts.size] do
    let s := starts[i]!
    let hi := if i + 1 < starts.size then starts[i+1]! else n
    let ds := (List.range (hi - s)).map (· + s) |>.filter (fun c => tr[c]!.done)
    let tag := s!"transfer {i} (start {s})"
    if s > 0 && !tr[s]!.cs then errs := errs.push s!"{tag}: cs already low at the start cycle"
    if s + 1 < n && tr[s+1]!.cs then errs := errs.push s!"{tag}: cs did not fall the cycle after start"
    match ds with
    | [d] =>
      if tr[d-1]!.done || (d + 1 < n && tr[d+1]!.done) then errs := errs.push s!"{tag}: done wider than 1 cycle"
      for c in [s+1:d+1] do
        if tr[c]!.cs then
          errs := errs.push s!"{tag}: cs high at cycle {c} before done at {d}"
          break
      if d + 1 < hi && !tr[d+1]!.cs then errs := errs.push s!"{tag}: cs not high the cycle after done ({d})"
      let mut tog := 0
      for c in [s+2:d+1] do if tr[c]!.sclk != tr[c-1]!.sclk then tog := tog + 1
      if tog != 16 then errs := errs.push s!"{tag}: {tog} sclk toggles before done (expected 16)"
      if tr[d]!.sclk != cpol then errs := errs.push s!"{tag}: sclk not at idle level at done"
      if tr[d]!.miso != misoB[i]! then
        errs := errs.push s!"{tag}: misoByte {hexB tr[d]!.miso} at done, slave sent {hexB misoB[i]!}"
      let stableEnd := if i + 1 < starts.size then starts[i+1]! + 1 else n
      for c in [d:stableEnd] do
        if tr[c]!.miso != tr[d]!.miso then
          errs := errs.push s!"{tag}: misoByte changes at cycle {c} after done"
          break
      if strictMosi then
        let mut got := 0
        let mut k := 0
        for c in [s+2:d+1] do
          if tr[c]!.sclk != cpol && tr[c-1]!.sclk == cpol then
            got := got * 2 + (if tr[c]!.mosi then 1 else 0); k := k + 1
        if k != 8 || got != mosiB[i]! then
          errs := errs.push s!"{tag}: slave received {hexB got} ({k} leading edges), master sent {hexB mosiB[i]!}"
    | _ => errs := errs.push s!"{tag}: {ds.length} done pulses (expected 1) at {ds}"
  return errs

/-! ## Synthetic controls -/

/-- An ideal trace for the given transfers (cpol, edge spacing `e`). -/
def ideal (cpol : Bool) (e : Nat) (starts mosiB misoB : Array Nat) (n : Nat) : Array Cyc := Id.run do
  let mut tr : Array Cyc := Array.replicate n { sclk := cpol, mosi := false, cs := true, miso := 0, done := false }
  let mut lastMiso := 0
  let mut prevEnd := 0
  for i in [0:starts.size] do
    let s := starts[i]!
    let d := s + 1 + e * 16 + 1
    for c in [prevEnd:s+2] do tr := tr.modify c fun x => { x with miso := lastMiso }
    for c in [s+1:d+1] do tr := tr.modify c fun x => { x with cs := false }
    for k in [0:16] do
      let a := s + 1 + e * (k + 1)
      let b := if k == 15 then d else s + 1 + e * (k + 2)
      let lvl := if k % 2 == 0 then !cpol else cpol
      for c in [a:b] do tr := tr.modify c fun x => { x with sclk := lvl }
    for k in [0:8] do
      let a := s + e * (2 * k + 1)
      let b := s + e * (2 * k + 3)
      let bit := ((mosiB[i]! >>> (7 - k)) &&& 1) == 1
      for c in [a:b] do tr := tr.modify c fun x => { x with mosi := bit }
    lastMiso := misoB[i]!
    tr := tr.modify d fun x => { x with done := true }
    prevEnd := d
  for c in [prevEnd:n] do tr := tr.modify c fun x => { x with miso := lastMiso }
  -- miso byte holds the slave byte from `done` of its transfer on
  for i in [0:starts.size] do
    let d := starts[i]! + 1 + e * 16 + 1
    let hi := if i + 1 < starts.size then starts[i+1]! + 1 else n
    for c in [d:hi] do tr := tr.modify c fun x => { x with miso := misoB[i]! }
  return tr

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  {if cond then "✓" else "✗"} {name}"
  pure cond

def controls : IO Bool := do
  IO.println "-- synthetic controls (checker must accept the ideal trace and reject each defect)"
  let mut ok := true
  for cpol in [false, true] do
    let st := #[10, 100]
    let mo := #[0xA5, 0x3C]
    let mi := #[0x5A, 0xC3]
    let good := ideal cpol 4 st mo mi 200
    let run := fun (t : Array Cyc) (strict : Bool) => spiErrors t cpol st mo mi strict
    let nm := fun (s : String) => s!"cpol={cpol}: {s}"
    ok := (← check (nm "ideal trace accepted") (run good true).isEmpty) && ok
    let d0 := 10 + 1 + 4 * 16 + 1
    ok := (← check (nm "second done pulse rejected")
      (!(run (good.modify (d0 + 5) fun x => { x with done := true }) false).isEmpty)) && ok
    ok := (← check (nm "done 2 cycles wide rejected")
      (!(run (good.modify (d0 + 1) fun x => { x with done := true }) false).isEmpty)) && ok
    ok := (← check (nm "missing done rejected")
      (!(run (good.modify d0 fun x => { x with done := false }) false).isEmpty)) && ok
    ok := (← check (nm "done before the first start rejected")
      (!(run (good.modify 4 fun x => { x with done := true }) false).isEmpty)) && ok
    ok := (← check (nm "cs stuck low after done rejected")
      (!(run (good.modify (d0 + 1) fun x => { x with cs := false }) false).isEmpty)) && ok
    ok := (← check (nm "cs not falling at start rejected")
      (!(run (good.modify 11 fun x => { x with cs := true }) false).isEmpty)) && ok
    ok := (← check (nm "cs glitching high inside the transfer rejected")
      (!(run (good.modify 40 fun x => { x with cs := true }) false).isEmpty)) && ok
    ok := (← check (nm "an extra sclk pulse (18 toggles) rejected")
      (!(run (good.modify 12 fun x => { x with sclk := !x.sclk }) false).isEmpty)) && ok
    ok := (← check (nm "sclk wrong idle level when cs is high rejected")
      (!(run (good.modify 60 fun x => { x with sclk := !cpol }) false).isEmpty)) && ok
    ok := (← check (nm "wrong misoByte at done rejected")
      (!(run (good.modify d0 fun x => { x with miso := 0x5B }) false).isEmpty)) && ok
    ok := (← check (nm "misoByte changing after done rejected")
      (!(run (good.modify (d0 + 8) fun x => { x with miso := 0 }) false).isEmpty)) && ok
    -- MOSI one bit early (what the design shows today): only the strict check sees it
    let early := ideal cpol 4 st (mo.map fun b => (b <<< 1) &&& 0xFF) mi 200
    ok := (← check (nm "MOSI shifted one bit: accepted by the CI check, rejected by strictMosi")
      ((run early false).isEmpty && !(run early true).isEmpty)) && ok
  pure ok

/-! ## JIT runs -/

/-- Slave model + recorder.  `starts` are cycles; the start pulse for the i-th
    transfer is issued at the first cycle ≥ the requested one that is a
    multiple of `bd + 1` (the divider tick phase after reset). -/
def runSpi (h : JITHandle) (bd : Nat) (cpol : Bool) (mosiB misoB : Array Nat)
    (aligned : Bool := true) : IO (Array Cyc × Array Nat) := do
  JIT.reset h
  JIT.setInput h 1 (if cpol then 1 else 0)
  JIT.setInput h 2 0
  JIT.setInput h 3 (UInt64.ofNat bd)
  let e := bd + 1
  let mut tr : Array Cyc := #[]
  let mut starts : Array Nat := #[]
  let mut idx := 0                -- next transfer
  let mut nextStart := if aligned then 12 else 13  -- earliest start cycle
  let mut k := 0                  -- slave bit index
  let mut prevS := cpol
  let mut waitDone := false
  let mut t := 0
  let total := 12 + 3 * (20 * e + 40) + 60
  while t < total do
    let doStart := !waitDone && idx < mosiB.size && t ≥ nextStart && (!aligned || t % e == 0)
    JIT.setInput h 0 (if doStart then 1 else 0)
    if doStart then JIT.setInput h 4 (UInt64.ofNat mosiB[idx]!)
    JIT.eval h
    let sclk := (← JIT.getOutput h 0) != 0
    let mosi := (← JIT.getOutput h 1) != 0
    let cs := (← JIT.getOutput h 2) != 0
    let miso := (← JIT.getOutput h 3).toNat
    let done := (← JIT.getOutput h 4) != 0
    -- slave: advance after SCLK returns to idle, present bit `k` MSB first
    if sclk == cpol && prevS != cpol then k := k + 1
    prevS := sclk
    if cs then k := 0
    let bit := if !cs && idx < misoB.size && k < 8 then ((misoB[idx]! >>> (7 - k)) &&& 1) else 0
    JIT.setInput h 5 (UInt64.ofNat bit)
    JIT.eval h
    tr := tr.push { sclk, mosi, cs, miso, done }
    if doStart then
      starts := starts.push t; waitDone := true
    if done && waitDone then
      waitDone := false; idx := idx + 1; nextStart := t + 6 + t % 3
    JIT.tick h
    t := t + 1
  pure (tr, starts)

def runCase (h : JITHandle) (bd : Nat) (cpol strict : Bool) : IO Bool := do
  let mo := #[0xA5, 0x3C, 0xFF]
  let mi := #[0x5A, 0xC3, 0x01]
  let (tr, starts) ← runSpi h bd cpol mo mi
  let errs := spiErrors tr cpol starts mo mi strict
  let dones := (List.range tr.size).filter (fun c => tr[c]!.done)
  let tag := s!"SPI bitDiv={bd} cpol={cpol}"
  IO.println s!"  · {tag}: {tr.size} cycles, starts {starts.toList}, done at {dones}"
  if errs.isEmpty then
    IO.println s!"  ✓ {tag}: per transfer cs/done/16 toggles/misoByte as expected, nothing outside"
  else
    for e in errs do IO.println s!"  ✗ {tag}: {e}"
  pure errs.isEmpty

def main : IO Unit := do
  IO.println "=== spiMasterHW — JIT co-sim (handshake: cs, done) ==="
  (← IO.getStdout).flush
  let mut ok ← controls
  let sim ← spiTop.Sim.load
  for bd in [0, 1, 3] do
    for cpol in [false, true] do
      ok := (← runCase sim.handle bd cpol false) && ok
  JIT.destroy sim.handle
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

/-- NOT in CI: (1) MOSI data check at the leading edges; (2) a 1-cycle start
    pulse that is not on a divider tick. -/
def mainDefects : IO Unit := do
  IO.println "=== spiMasterHW — known defects — NOT in CI ==="
  (← IO.getStdout).flush
  let sim ← spiTop.Sim.load
  let h := sim.handle
  let mut ok := true
  IO.println "-- (1) MOSI at the leading SCLK edges must carry the byte MSB first"
  for bd in [1, 3] do
    ok := (← runCase h bd false true) && ok
  IO.println "-- (2) start pulse not aligned to the divider tick (bitDiv=3, start at cycle 13)"
  let (tr, starts) ← runSpi h 3 false #[0xA5] #[0x5A] (aligned := false)
  let dones := (List.range tr.size).filter (fun c => tr[c]!.done)
  let csLow := (List.range tr.size).filter (fun c => !tr[c]!.cs)
  IO.println s!"  · starts {starts.toList}, cs low at {csLow.take 3}.. ({csLow.length} cycles), done at {dones}"
  if dones.length != 1 then
    IO.println "  ✗ unaligned start: cs asserted but no transfer, no done"
    ok := false
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.SpiHWJITTest
