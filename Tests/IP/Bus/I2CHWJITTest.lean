/-
  JIT co-sim of the generated hardware for the I2C master
  `IP.Bus.I2CHW.i2cMasterHW`, checked cycle by cycle (the existing I2CHWTest
  only asks whether every FSM state is visited once).

  Ports after `#sim` lowering: inputs start = 0, bitDiv = 1, addr = 2, rw = 3,
  dataByte = 4, sdaFromBus = 5; outputs state = 0, scl = 1, sda = 2, busy = 3.

  The master has no `done` strobe; its handshake is `busy` (= state ≠ idle).
  Reference (the FSM documented in the module header, one slot = bitDiv + 1
  cycles): a `start` seen on a divider tick at cycle s makes `busy` rise at
  s+1 and fall at s+1+20(bitDiv+1) — exactly once per request — with the
  slots start(1) addr(8) ackA(1) data(8) ackD(1) stop(1); SCL toggles at every
  slot boundary (low in even slots, high again after the stop slot); SDA is
  released (high) in start / ack / stop slots and carries {addr, rw} then the
  data byte MSB first in the addr / data slots.  `i2cErrors` compares the whole
  trace to this model per cycle and also counts the busy pulses (position and
  width), so a spurious busy before the first request / after the last, a
  missing or doubled transaction and a wrong width are named explicitly.
  Extra `start` pulses while busy must be ignored; `start` held 3 cycles still
  gives one transaction; transactions may follow back to back.

  What is NOT checked here: the slave ACK (`sdaFromBus` is only latched
  internally, there is no output), read-mode data capture (the master has none).
  Bus-protocol compliance (START / STOP conditions, one SCL pulse per bit) is
  checked separately by the NOT-in-CI probe `i2c-bus-protocol-hw-jit-test`
  (`probeMain` below), because the generated bus waveform fails it.
  Synthetic controls for every check run first (no JIT), plus live controls
  (wrong bytes / wrong divider told to the checker must be rejected).
-/
import IP.Bus.I2CHW
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Bus.I2CHW

namespace Sparkle.Tests.IP.Bus.I2CHWJITTest

set_option maxRecDepth 100000

def i2cTop (start : Signal defaultDomain Bool) (bitDiv : Signal defaultDomain (BitVec 16))
    (addr : Signal defaultDomain (BitVec 7)) (rw : Signal defaultDomain Bool)
    (dataByte : Signal defaultDomain (BitVec 8)) (sdaFromBus : Signal defaultDomain Bool) :
    MasterOut defaultDomain :=
  i2cMasterHW start bitDiv addr rw dataByte sdaFromBus

#sim i2cTop

structure Cyc where
  state : Nat
  scl : Bool
  sda : Bool
  busy : Bool
  deriving Inhabited, BEq

structure Tx where
  addr : Nat
  rw : Bool
  data : Nat
  deriving Inhabited

def idleCyc : Cyc := { state := 0, scl := true, sda := true, busy := false }

/-! ## Reference model -/

/-- The 9 + 9 bits driven by the master on SDA in slots 2..19 (`none` = released). -/
def slotSda (tx : Tx) (j : Nat) : Bool :=
  let ar := tx.addr * 2 + (if tx.rw then 1 else 0)
  if 2 ≤ j && j ≤ 9 then ((ar >>> (9 - j)) &&& 1) == 1
  else if 11 ≤ j && j ≤ 18 then ((tx.data >>> (18 - j)) &&& 1) == 1
  else true

def slotState (j : Nat) : Nat :=
  if j == 1 then 1 else if j ≤ 9 then 2 else if j == 10 then 3
  else if j ≤ 18 then 4 else if j == 19 then 5 else 6

/-- Expected state of cycle `c` of a transaction whose start pulse is at cycle `s`. -/
def modelCyc (e : Nat) (s : Nat) (tx : Tx) (c : Nat) : Cyc :=
  if c ≤ s || c > s + 20 * e then idleCyc
  else
    let j := (c - s - 1) / e + 1
    { state := slotState j, scl := j % 2 == 1, sda := slotSda tx j, busy := true }

def hexB (b : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 b)

/-! ## Pure checker -/

/-- Violations of the I2C master contract on a trace of `n` cycles; `starts[i]`
    is the cycle of the i-th accepted start pulse, `txs[i]` its transaction. -/
def i2cErrors (tr : Array Cyc) (bd : Nat) (starts : Array Nat) (txs : Array Tx) : Array String := Id.run do
  let e := bd + 1
  let n := tr.size
  let mut errs : Array String := #[]
  -- busy pulses: rising edge cycle and width
  let mut pulses : Array (Nat × Nat) := #[]
  let mut p := 0
  while p < n do
    if tr[p]!.busy && (p == 0 || !tr[p-1]!.busy) then
      let mut w := 0
      while p + w < n && tr[p+w]!.busy do w := w + 1
      pulses := pulses.push (p, w)
      p := p + w
    else p := p + 1
  if pulses.size != starts.size then
    errs := errs.push s!"{pulses.size} busy pulses {pulses.toList}, expected {starts.size} (one per start {starts.toList})"
  for i in [0:starts.size] do
    match pulses[i]? with
    | some (r, w) =>
      if r != starts[i]! + 1 then errs := errs.push s!"transaction {i}: busy rises at {r}, expected {starts[i]! + 1}"
      if w != 20 * e then errs := errs.push s!"transaction {i}: busy {w} cycles wide, expected {20 * e}"
    | none => errs := errs.push s!"transaction {i}: no busy pulse"
  if starts.size > 0 && pulses.size > 0 && pulses[0]!.1 < starts[0]! then
    errs := errs.push s!"busy at {pulses[0]!.1} before the first start at {starts[0]!}"
  -- full per-cycle comparison with the model
  let mut exp : Array Cyc := Array.replicate n idleCyc
  for i in [0:starts.size] do
    for c in [starts[i]!:min n (starts[i]! + 20 * e + 2)] do
      if c > starts[i]! then exp := exp.set! c (modelCyc e starts[i]! txs[i]! c)
  let mut bad := #[false, false, false, false]
  for c in [0:n] do
    let a := tr[c]!
    let x := exp[c]!
    if a.state != x.state && !bad[0]! then
      bad := bad.set! 0 true
      errs := errs.push s!"cycle {c}: state {a.state}, expected {x.state}"
    if a.scl != x.scl && !bad[1]! then
      bad := bad.set! 1 true
      errs := errs.push s!"cycle {c}: scl {a.scl}, expected {x.scl}"
    if a.sda != x.sda && !bad[2]! then
      bad := bad.set! 2 true
      errs := errs.push s!"cycle {c}: sda {a.sda}, expected {x.sda}"
    if a.busy != x.busy && !bad[3]! then
      bad := bad.set! 3 true
      errs := errs.push s!"cycle {c}: busy {a.busy}, expected {x.busy}"
  return errs

/-! ## Synthetic controls -/

def txA : Tx := { addr := 0x50, rw := false, data := 0xA5 }
def txB : Tx := { addr := 0x2B, rw := true, data := 0x3C }

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  {if cond then "✓" else "✗"} {name}"
  pure cond

/-- Ideal trace of the given transactions. -/
def ideal (bd : Nat) (starts : Array Nat) (txs : Array Tx) (n : Nat) : Array Cyc := Id.run do
  let e := bd + 1
  let mut tr := Array.replicate n idleCyc
  for i in [0:starts.size] do
    for c in [starts[i]!+1:min n (starts[i]! + 20 * e + 1)] do
      tr := tr.set! c (modelCyc e starts[i]! txs[i]! c)
  return tr

def controls : IO Bool := do
  IO.println "-- synthetic controls (checker must accept the ideal trace and reject each defect)"
  let mut ok := true
  for bd in [0, 1, 3] do
    let e := bd + 1
    let st := #[8 * e, 8 * e + 21 * e + 4 * e]
    let tx := #[txA, txB]
    let n := st[1]! + 22 * e + 10
    let good := ideal bd st tx n
    let run := fun (t : Array Cyc) => i2cErrors t bd st tx
    let nm := fun (s : String) => s!"bitDiv={bd}: {s}"
    let rej := fun (s : String) (t : Array Cyc) => check (nm s) (!(run t).isEmpty)
    ok := (← check (nm "ideal trace accepted") (run good).isEmpty) && ok
    let b0 := st[0]! + 1
    -- busy / handshake defects
    ok := (← rej "busy before the first start" (good.modify 2 fun x => { x with busy := true })) && ok
    ok := (← rej "busy after the last transaction" (good.modify (n - 3) fun x => { x with busy := true })) && ok
    ok := (← rej "busy drops one slot early" (good.modify (b0 + 20 * e - 1) fun x => { x with busy := false, state := 0 })) && ok
    ok := (← rej "busy glitching low inside the transaction" (good.modify (b0 + 7 * e) fun x => { x with busy := false })) && ok
    ok := (← rej "busy stays high one cycle too long" (good.modify (b0 + 20 * e) fun x => { x with busy := true })) && ok
    ok := (← rej "second transaction missing" ((ideal bd #[st[0]!] #[txA] n))) && ok
    ok := (← rej "an extra transaction" (ideal bd (st.push (st[1]! + 30 * e)) (tx.push txA) (n + 60 * e))) && ok
    ok := (← rej "busy rises one cycle late" (good.modify b0 fun x => { x with busy := false })) && ok
    -- state / scl / sda defects
    ok := (← rej "wrong state in the ack slot" (good.modify (b0 + 9 * e) fun x => { x with state := 4 })) && ok
    ok := (← rej "scl not toggling at a slot boundary" (good.modify (b0 + 5 * e) fun x => { x with scl := !x.scl })) && ok
    ok := (← rej "scl low in idle" (good.modify (n - 2) fun x => { x with scl := false })) && ok
    ok := (← rej "sda wrong address bit" (good.modify (b0 + 3 * e) fun x => { x with sda := !x.sda })) && ok
    ok := (← rej "sda wrong data bit" (good.modify (b0 + 12 * e) fun x => { x with sda := !x.sda })) && ok
    ok := (← rej "sda driven low in the ack slot" (good.modify (b0 + 9 * e) fun x => { x with sda := false })) && ok
    ok := (← rej "bytes of the other transaction" (ideal bd st #[txB, txA] n)) && ok
    ok := (← rej "address and data swapped"
      (ideal bd st #[{ txA with addr := txA.data % 128, data := txA.addr }, txB] n)) && ok
  pure ok

/-! ## JIT runs -/

/-- Run `txs` with starts at the given cycles.  Inputs addr/rw/data are set at the
    start cycle and held until the next start.  `extra` adds a 1-cycle start
    pulse in the middle of every transaction, `hold` keeps start high that
    many cycles. -/
def runI2c (h : JITHandle) (bd : Nat) (starts : Array Nat) (txs : Array Tx)
    (extra : Bool := false) (hold : Nat := 1) : IO (Array Cyc) := do
  JIT.reset h
  JIT.setInput h 1 (UInt64.ofNat bd)
  JIT.setInput h 5 0
  let e := bd + 1
  let total := starts[starts.size - 1]! + 22 * e + 30
  let mut tr : Array Cyc := #[]
  let mut idx := 0
  for t in [0:total] do
    let mut sv := false
    for i in [0:starts.size] do
      if t ≥ starts[i]! && t < starts[i]! + hold then sv := true
      if extra && t == starts[i]! + 9 * e + 1 then sv := true
    if idx < starts.size && t == starts[idx]! then
      let tx := txs[idx]!
      JIT.setInput h 2 (UInt64.ofNat tx.addr)
      JIT.setInput h 3 (if tx.rw then 1 else 0)
      JIT.setInput h 4 (UInt64.ofNat tx.data)
      idx := idx + 1
    JIT.setInput h 0 (if sv then 1 else 0)
    JIT.eval h
    let state := (← JIT.getOutput h 0).toNat
    let scl := (← JIT.getOutput h 1) != 0
    let sda := (← JIT.getOutput h 2) != 0
    let busy := (← JIT.getOutput h 3) != 0
    tr := tr.push { state, scl, sda, busy }
    JIT.tick h
  pure tr

/-- Start cycles aligned to the divider phase (ticks at multiples of bitDiv+1 in
    idle, the divider free-runs from reset).  `gaps[i]` = extra slots idle
    before transaction i beyond the earliest legal start. -/
def alignedStarts (bd : Nat) (gaps : Array Nat) : Array Nat := Id.run do
  let e := bd + 1
  let mut s := #[]
  let mut earliest := 4 * e + 8
  for g in gaps do
    let c := (earliest + e - 1) / e * e + g * e
    s := s.push c
    earliest := c + 21 * e
  return s

def runCase (h : JITHandle) (bd : Nat) (gaps : Array Nat) (txs : Array Tx)
    (extra : Bool := false) (hold : Nat := 1) : IO Bool := do
  let starts := alignedStarts bd gaps
  let tr ← runI2c h bd starts txs extra hold
  let errs := i2cErrors tr bd starts txs
  let tag := s!"I2C bitDiv={bd} gaps={gaps.toList} extraStart={extra} hold={hold}"
  let busyN := (List.range tr.size).filter (fun c => tr[c]!.busy && (c == 0 || !tr[c-1]!.busy))
  IO.println s!"  · {tag}: {tr.size} cycles, starts {starts.toList}, busy rises at {busyN}"
  if errs.isEmpty then
    IO.println s!"  ✓ {tag}: busy once per start, state/scl/sda per slot as modelled, nothing outside"
  else
    for x in errs do IO.println s!"  ✗ {tag}: {x}"
  pure errs.isEmpty

/-- Live negative controls: the checker told other bytes / another divider must
    reject the real trace. -/
def runMismatch (h : JITHandle) (bd : Nat) : IO Bool := do
  let gaps := #[0, 3]
  let starts := alignedStarts bd gaps
  let tr ← runI2c h bd starts #[txA, txB]
  let a ← check s!"bitDiv={bd}: checker told other bytes flags the run"
    (!(i2cErrors tr bd starts #[txB, txA]).isEmpty)
  let b ← check s!"bitDiv={bd}: checker told another divider flags the run"
    (!(i2cErrors tr (bd + 1) starts #[txA, txB]).isEmpty)
  let c ← check s!"bitDiv={bd}: checker told one start too many flags the run"
    (!(i2cErrors tr bd (starts.push (starts[1]! + 30 * (bd + 1))) #[txA, txB, txA]).isEmpty)
  pure (a && b && c)

def main : IO Unit := do
  IO.println "=== i2cMasterHW — JIT co-sim (busy once per request, state/SCL/SDA per slot) ==="
  (← IO.getStdout).flush
  let mut ok ← controls
  let sim ← i2cTop.Sim.load
  let h := sim.handle
  IO.println "-- single and repeated transactions (divider-aligned starts)"
  for bd in [0, 1, 2, 5] do
    ok := (← runCase h bd #[0] #[txA]) && ok
    ok := (← runCase h bd #[0, 0, 4] #[txA, txB, { addr := 0x7F, rw := false, data := 0x00 }]) && ok
  IO.println "-- more byte patterns"
  for bd in [0, 3] do
    ok := (← runCase h bd #[1, 0, 2] #[{ addr := 0x00, rw := true, data := 0xFF },
      { addr := 0x55, rw := false, data := 0xAA }, { addr := 0x2A, rw := true, data := 0x81 }]) && ok
  IO.println "-- extra start pulse while busy is ignored; start held 3 cycles"
  for bd in [0, 1, 3] do
    ok := (← runCase h bd #[0, 2] #[txA, txB] (extra := true)) && ok
  for bd in [0, 3] do
    ok := (← runCase h bd #[0, 1] #[txA, txB] (hold := 3)) && ok
  IO.println "-- negative controls on the live design"
  for bd in [0, 1, 3] do
    ok := (← runMismatch h bd) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

/-! ## Bus-protocol probe (NOT in CI) -/

/-- Standard-compliant bus waveform for one write transaction: START (SDA falls
    while SCL high), per bit one low slot (SDA set) + one high slot (SDA stable),
    ack slot released, STOP (SDA rises while SCL high). -/
def compliant (tx : Tx) : Array (Bool × Bool) := Id.run do
  let mut w : Array (Bool × Bool) := #[(true, true), (true, false)]
  let ar := tx.addr * 2 + (if tx.rw then 1 else 0)
  let bits := (List.range 8).map (fun k => ((ar >>> (7 - k)) &&& 1) == 1) ++ [true]
    ++ (List.range 8).map (fun k => ((tx.data >>> (7 - k)) &&& 1) == 1) ++ [true]
  for b in bits do w := w.push (false, b) |>.push (true, b)
  w := w ++ #[(false, false), (true, false), (true, true)]
  return w

/-- What an I2C slave sees on (scl, sda): START found, bytes sampled at SCL rises,
    number of SCL pulses between START and STOP, STOP found, SDA changes during
    an SCL-high window outside START/STOP. -/
structure BusView where
  started : Bool := false
  stopped : Bool := false
  pulses : Nat := 0
  bits : Array Bool := #[]
  glitches : Nat := 0
  deriving Inhabited

def busView (w : Array (Bool × Bool)) : BusView := Id.run do
  let mut v : BusView := {}
  let mut inTx := false
  let mut high := false   -- inside an SCL-high window that started within a transaction
  let mut hv := true
  for c in [1:w.size] do
    let (sp, dp) := w[c-1]!
    let (s, d) := w[c]!
    if s && sp && dp && !d then v := { v with started := true }; inTx := true; high := false
    else if s && sp && !dp && d then
      if inTx then v := { v with stopped := true }; inTx := false
    else if s && !sp then
      if inTx then v := { v with pulses := v.pulses + 1, bits := v.bits.push dp }; high := true; hv := dp
    else if s && sp && d != dp then
      if inTx && high then v := { v with glitches := v.glitches + 1 }
    else if !s then high := false
  return v

def protocolErrors (w : Array (Bool × Bool)) (tx : Tx) : Array String := Id.run do
  let v := busView w
  let mut errs := #[]
  if !v.started then errs := errs.push "no START condition (SDA falling while SCL high)"
  if !v.stopped then errs := errs.push "no STOP condition (SDA rising while SCL high)"
  -- 18 bit clocks; a 19th SCL rise (the clock-high before STOP) is allowed
  if v.pulses < 18 || v.pulses > 19 then errs := errs.push s!"{v.pulses} SCL pulses between START and STOP, expected 18 (2 bytes with ack)"
  if v.glitches > 0 then errs := errs.push s!"SDA changes {v.glitches}x while SCL is high"
  let ar := tx.addr * 2 + (if tx.rw then 1 else 0)
  let expBits := (List.range 8).map (fun k => ((ar >>> (7 - k)) &&& 1) == 1) ++ [true]
    ++ (List.range 8).map (fun k => ((tx.data >>> (7 - k)) &&& 1) == 1) ++ [true]
  if v.bits.toList.take 18 != expBits then
    let got := v.bits.toList.map (fun b => if b then "1" else "0")
    errs := errs.push s!"slave samples bits {String.join (got.take 18)}, expected {String.join (expBits.map fun b => if b then "1" else "0")}"
  return errs

def probeMain : IO Unit := do
  IO.println "=== i2cMasterHW — bus-protocol probe (NOT in CI: expected to FAIL on the current design) ==="
  (← IO.getStdout).flush
  let mut ok := true
  -- the checker accepts a compliant waveform and rejects broken ones
  let good := compliant txA
  ok := (← check "compliant waveform accepted" (protocolErrors good txA).isEmpty) && ok
  ok := (← check "waveform without START rejected" (!(protocolErrors (good.extract 2 good.size) txA).isEmpty)) && ok
  ok := (← check "waveform without STOP rejected" (!(protocolErrors (good.pop.pop) txA).isEmpty)) && ok
  ok := (← check "waveform with a wrong bit rejected"
    (!(protocolErrors ((good.modify 7 fun (s, d) => (s, !d)).modify 8 fun (s, d) => (s, !d)) txA).isEmpty)) && ok
  if !ok then
    IO.println "\nPROBE CONTROLS FAILED"
    IO.Process.exit 2
  -- live design
  let sim ← i2cTop.Sim.load
  let h := sim.handle
  let mut live := true
  for bd in [0, 3] do
    let starts := alignedStarts bd #[0]
    let tr ← runI2c h bd starts #[txA]
    let w := (tr.map fun c => (c.scl, c.sda)).extract (starts[0]! - 1) (starts[0]! + 22 * (bd + 1))
    -- compress to one sample per slot of the master's own clock
    let slots := (List.range 22).toArray.map fun j => w[min (w.size - 1) (1 + j * (bd + 1))]!
    let errs := protocolErrors slots txA
    let rises := (List.range 21).filter fun j => (slots[j+1]!).1 && !(slots[j]!).1
    IO.println s!"  · bitDiv={bd}: {rises.length} SCL rising edges for 18 data/ack bits + address/data; SDA at the slot boundaries {slots.toList.map fun (s, d) => (if s then 1 else 0, if d then 1 else 0)}"
    for x in errs do IO.println s!"  ✗ bitDiv={bd}: {x}"
    if errs.isEmpty then IO.println s!"  ✓ bitDiv={bd}: bus waveform is I2C-compliant"
    live := live && errs.isEmpty
  JIT.destroy h
  if !live then
    IO.println "\nPROBE FAIL (design defect, see header of Tests/IP/Bus/I2CHWJITTest.lean notes)"
    IO.Process.exit 1
  IO.println "\nPROBE PASS"

end Sparkle.Tests.IP.Bus.I2CHWJITTest
