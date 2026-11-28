/-
  JIT co-sim of the generated hardware for the I2C master
  `IP.Bus.I2CHW.i2cMasterHW`, checked cycle by cycle (the existing I2CHWTest
  only asks whether every FSM state is visited once).

  Ports after `#sim` lowering: inputs start = 0, bitDiv = 1, addr = 2, rw = 3,
  dataByte = 4, sdaFromBus = 5; outputs state = 0, scl = 1, sda = 2, busy = 3.

  The master has no `done` strobe; its handshake is `busy` (= state ≠ idle).
  Reference (the FSM documented in the module header; one half-period h =
  bitDiv + 1 cycles): a `start` pulse on ANY idle cycle s makes `busy` rise at
  s+1 and fall at s+1+39h — exactly once per request.  The 39 halves are:
  half 0 START (state 1, SCL high, SDA low); then 18 bit slots of two halves
  each (SCL low, then SCL high; SDA = the bit in both): 8 addr/rw bits
  (state 2), ack (3, SDA released), 8 data bits (4), ack (5); then STOP (state
  6, SCL low then high, SDA low); back in idle SDA rises while SCL is high.
  `i2cErrors` compares the whole trace to this model per cycle and counts the
  busy pulses (position and width).  `protocolErrors` is the independent
  bus-level view of an I2C slave (START = SDA falls while SCL high, bits sampled
  at SCL rises, SDA stable while SCL high, STOP = SDA rises while SCL high); it
  is applied to every live transaction, with controls (missing START / STOP, a
  wrong bit, SDA changing while SCL is high — synthetic and on the live trace).
  Extra `start` pulses while busy must be ignored; `start` held 3 cycles gives
  one transaction; transactions may follow back to back; start pulses may fall
  on any cycle of the divider period (they used to be lost off a tick).

  What is NOT checked here: the slave ACK (`sdaFromBus` is only latched
  internally, there is no output), read-mode data capture (the master has none),
  SDA/SCL hold time at bitDiv = 0 (SDA changes on the cycle SCL falls), clock
  stretching / arbitration (the master has no ACK-error output, so a NACK is
  invisible, and no SCL input, so it cannot sense a held-low SCL).
  Input latching: the runs with `inMode` 1 / 2 change addr / rw / dataByte right
  after the start is accepted (every cycle, mode 1) or at a start pulse while
  busy (mode 2, decoy values); the bus waveform and busy must be those of the
  inputs at the accepted start.  Pure negative controls (reference-model
  mutations: latch one cycle late, at the end of the START half, or read each bit
  live) must be rejected by the same checker on those input schedules.
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
def bitSda (tx : Tx) (k : Nat) : Bool :=
  let ar := tx.addr * 2 + (if tx.rw then 1 else 0)
  if k < 8 then ((ar >>> (7 - k)) &&& 1) == 1
  else if 9 ≤ k && k ≤ 16 then ((tx.data >>> (16 - k)) &&& 1) == 1
  else true

def bitState (k : Nat) : Nat :=
  if k < 8 then 2 else if k == 8 then 3 else if k ≤ 16 then 4 else 5

/-- Expected state of cycle `c` of a transaction whose start pulse is at cycle `s`. -/
def modelCyc (e : Nat) (s : Nat) (tx : Tx) (c : Nat) : Cyc :=
  if c ≤ s || c > s + 39 * e then idleCyc
  else
    let hf := (c - s - 1) / e
    if hf == 0 then { state := 1, scl := true, sda := false, busy := true }
    else if hf ≤ 36 then
      let k := (hf - 1) / 2
      { state := bitState k, scl := (hf - 1) % 2 == 1, sda := bitSda tx k, busy := true }
    else { state := 6, scl := hf == 38, sda := false, busy := true }

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
      if w != 39 * e then errs := errs.push s!"transaction {i}: busy {w} cycles wide, expected {39 * e}"
    | none => errs := errs.push s!"transaction {i}: no busy pulse"
  if starts.size > 0 && pulses.size > 0 && pulses[0]!.1 < starts[0]! then
    errs := errs.push s!"busy at {pulses[0]!.1} before the first start at {starts[0]!}"
  -- full per-cycle comparison with the model
  let mut exp : Array Cyc := Array.replicate n idleCyc
  for i in [0:starts.size] do
    for c in [starts[i]!:min n (starts[i]! + 39 * e + 2)] do
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

/-! ## Bus-level view (an I2C slave) -/

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
    number of SCL rises between START and STOP, STOP found, SDA changes during
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
    if s && sp && dp && !d then
      -- a START inside a transaction (no repeated START is generated) is a glitch
      if inTx then v := { v with glitches := v.glitches + 1 }
      v := { v with started := true }; inTx := true; high := false
    else if s && sp && !dp && d then
      -- a STOP before 18 bits were clocked is a glitch
      if inTx && v.pulses < 18 then v := { v with glitches := v.glitches + 1 }
      else if inTx then v := { v with stopped := true }
      inTx := false
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

/-- Every sample twice (two cycles per half-period). -/
def dup (w : Array (Bool × Bool)) : Array (Bool × Bool) := w.flatMap fun x => #[x, x]

/-- Controls of the bus-level checker alone (no JIT). -/
def protocolControls : IO Bool := do
  IO.println "-- synthetic controls of the bus-level checker"
  let good := compliant txA
  let mut ok := true
  ok := (← check "compliant waveform accepted" (protocolErrors good txA).isEmpty) && ok
  ok := (← check "compliant waveform at 2 cycles/half accepted" (protocolErrors (dup good) txA).isEmpty) && ok
  ok := (← check "waveform without START rejected" (!(protocolErrors (good.extract 2 good.size) txA).isEmpty)) && ok
  ok := (← check "waveform without STOP rejected" (!(protocolErrors (good.pop.pop) txA).isEmpty)) && ok
  ok := (← check "waveform with a wrong bit rejected"
    (!(protocolErrors ((good.modify 7 fun (s, d) => (s, !d)).modify 8 fun (s, d) => (s, !d)) txA).isEmpty)) && ok
  -- SDA flips in the second cycle of an SCL-high half only (the bit sampled at the rise is right)
  ok := (← check "SDA changing while SCL is high rejected"
    (!(protocolErrors ((dup good).modify 7 fun (s, d) => (s, !d)) txA).isEmpty)) && ok
  -- old waveform: SCL toggled at every slot boundary together with SDA
  let old := (List.range 22).toArray.map fun j => (j % 2 == 1 || j == 0, j ≥ 2 && j ≤ 19 && ((j / 2) % 2 == 1))
  ok := (← check "the previous toggling waveform rejected" (!(protocolErrors old txA).isEmpty)) && ok
  pure ok

/-- Ideal trace of the given transactions. -/
def ideal (bd : Nat) (starts : Array Nat) (txs : Array Tx) (n : Nat) : Array Cyc := Id.run do
  let e := bd + 1
  let mut tr := Array.replicate n idleCyc
  for i in [0:starts.size] do
    for c in [starts[i]!+1:min n (starts[i]! + 39 * e + 1)] do
      tr := tr.set! c (modelCyc e starts[i]! txs[i]! c)
  return tr

def controls : IO Bool := do
  IO.println "-- synthetic controls (checker must accept the ideal trace and reject each defect)"
  let mut ok := true
  for bd in [0, 1, 3] do
    let e := bd + 1
    let st := #[8 * e, 8 * e + 40 * e + 4 * e]
    let tx := #[txA, txB]
    let n := st[1]! + 41 * e + 10
    let good := ideal bd st tx n
    let run := fun (t : Array Cyc) => i2cErrors t bd st tx
    let nm := fun (s : String) => s!"bitDiv={bd}: {s}"
    let rej := fun (s : String) (t : Array Cyc) => check (nm s) (!(run t).isEmpty)
    ok := (← check (nm "ideal trace accepted") (run good).isEmpty) && ok
    let b0 := st[0]! + 1
    -- busy / handshake defects
    ok := (← rej "busy before the first start" (good.modify 2 fun x => { x with busy := true })) && ok
    ok := (← rej "busy after the last transaction" (good.modify (n - 3) fun x => { x with busy := true })) && ok
    ok := (← rej "busy drops one slot early" (good.modify (b0 + 39 * e - 1) fun x => { x with busy := false, state := 0 })) && ok
    ok := (← rej "busy glitching low inside the transaction" (good.modify (b0 + 7 * e) fun x => { x with busy := false })) && ok
    ok := (← rej "busy stays high one cycle too long" (good.modify (b0 + 39 * e) fun x => { x with busy := true })) && ok
    ok := (← rej "second transaction missing" ((ideal bd #[st[0]!] #[txA] n))) && ok
    ok := (← rej "an extra transaction" (ideal bd (st.push (st[1]! + 45 * e)) (tx.push txA) (n + 90 * e))) && ok
    ok := (← rej "busy rises one cycle late" (good.modify b0 fun x => { x with busy := false })) && ok
    -- state / scl / sda defects
    ok := (← rej "wrong state in the ack slot" (good.modify (b0 + 17 * e) fun x => { x with state := 4 })) && ok
    ok := (← rej "scl not toggling at a slot boundary" (good.modify (b0 + 5 * e) fun x => { x with scl := !x.scl })) && ok
    ok := (← rej "scl low in idle" (good.modify (n - 2) fun x => { x with scl := false })) && ok
    ok := (← rej "sda wrong address bit" (good.modify (b0 + 3 * e) fun x => { x with sda := !x.sda })) && ok
    ok := (← rej "sda wrong data bit" (good.modify (b0 + 25 * e) fun x => { x with sda := !x.sda })) && ok
    ok := (← rej "sda driven low in the ack slot" (good.modify (b0 + 17 * e) fun x => { x with sda := false })) && ok
    ok := (← rej "bytes of the other transaction" (ideal bd st #[txB, txA] n)) && ok
    ok := (← rej "address and data swapped"
      (ideal bd st #[{ txA with addr := txA.data % 128, data := txA.addr }, txB] n)) && ok
  pure ok

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
    earliest := c + 40 * e
  return s

/-! ## Input schedules (inputs change after the start is accepted) -/

/-- Inputs derived from `tx` that differ from it in addr, rw and data at every
    cycle `t > s` (rw alternates with the cycle). -/
def scrambled (tx : Tx) (s t : Nat) : Tx :=
  { addr := tx.addr ^^^ (1 + t % 127), rw := if (t - s) % 2 == 1 then !tx.rw else tx.rw,
    data := tx.data ^^^ (1 + t % 255) }

/-- Decoy inputs, different from `tx` in every field. -/
def decoy (tx : Tx) : Tx := { addr := tx.addr ^^^ 0x7F, rw := !tx.rw, data := tx.data ^^^ 0xFF }

def sameTx (a b : Tx) : Bool := a.addr == b.addr && a.rw == b.rw && a.data == b.data

/-- Input values at cycle `t`.  `inMode` 1: addr/rw/data change on every cycle after
    the accepted start (also while idle between transactions); 2: held until the
    start pulse that arrives while busy (cycle s + 9e + 1), decoy values from that
    cycle on.  At a start cycle the inputs are always the transaction's own. -/
def inputsAt (e : Nat) (starts : Array Nat) (txs : Array Tx) (inMode : Nat) (t : Nat) : Tx := Id.run do
  let mut idx := 0
  let mut found := false
  for i in [0:starts.size] do
    if starts[i]! ≤ t then idx := i; found := true
  let tx := txs[idx]!
  let s := starts[idx]!
  if !found || t == s then return tx
  if inMode == 1 then return scrambled tx s t
  if inMode == 2 && t ≥ s + 9 * e + 1 then return decoy tx
  return tx

/-- Reference-model mutation: the inputs are latched `d` cycles after the start
    pulse instead of at it. -/
def lateIdeal (bd : Nat) (starts : Array Nat) (txs : Array Tx) (inMode d n : Nat) : Array Cyc :=
  let e := bd + 1
  ideal bd starts ((List.range starts.size).toArray.map fun i =>
    inputsAt e starts txs inMode (starts[i]! + d)) n

/-- Reference-model mutation: each bit is read from the live inputs of its cycle. -/
def liveIdeal (bd : Nat) (starts : Array Nat) (txs : Array Tx) (inMode n : Nat) : Array Cyc := Id.run do
  let e := bd + 1
  let mut tr := Array.replicate n idleCyc
  for i in [0:starts.size] do
    for c in [starts[i]!+1:min n (starts[i]! + 39 * e + 1)] do
      tr := tr.set! c (modelCyc e starts[i]! (inputsAt e starts txs inMode c) c)
  return tr

def latchControls : IO Bool := do
  IO.println "-- negative controls: late-latching reference models must fail the input-change runs"
  let mut ok := true
  for bd in [0, 1, 3] do
    let e := bd + 1
    let st := alignedStarts bd #[0, 3]
    let tx := #[txA, txB]
    let n := st[1]! + 41 * e + 30
    let nm := fun (x : String) => s!"bitDiv={bd}: {x}"
    let run := fun (t : Array Cyc) => i2cErrors t bd st tx
    let differs := (List.range 2).all fun i =>
      !sameTx (inputsAt e st tx 1 (st[i]! + 1)) tx[i]! &&
      (inputsAt e st tx 1 (st[i]! + 1)).addr != tx[i]!.addr &&
      (inputsAt e st tx 1 (st[i]! + 1)).rw != tx[i]!.rw &&
      (inputsAt e st tx 1 (st[i]! + 1)).data != tx[i]!.data
    ok := (← check (nm "input schedule 1 changes addr, rw and data in the cycle after the start") differs) && ok
    ok := (← check (nm "latch at the start cycle (the design) accepted")
      (run (lateIdeal bd st tx 1 0 n)).isEmpty) && ok
    for (what, t) in [("latched one cycle after the start", lateIdeal bd st tx 1 1 n),
                      ("latched at the end of the START half", lateIdeal bd st tx 1 e n),
                      ("each bit read live from the inputs", liveIdeal bd st tx 1 n)] do
      let errs := run t
      ok := (← check (nm s!"model {what} rejected") (!errs.isEmpty)) && ok
      IO.println s!"      checker: {errs.toList.take 2}"
    -- a start while busy that is NOT ignored (the decoy inputs get latched)
    let errs := run (ideal bd st (tx.map decoy) n)
    ok := (← check (nm "model that takes the decoy inputs of the busy-start rejected") (!errs.isEmpty)) && ok
    IO.println s!"      checker: {errs.toList.take 2}"
  pure ok

/-! ## JIT runs -/

/-- Run `txs` with starts at the given cycles.  Inputs addr/rw/data are set at the
    start cycle and held until the next start.  `extra` adds a 1-cycle start
    pulse in the middle of every transaction, `hold` keeps start high that
    many cycles.  With `inMode` ≠ 0 the inputs follow `inputsAt` on every cycle. -/
def runI2c (h : JITHandle) (bd : Nat) (starts : Array Nat) (txs : Array Tx)
    (extra : Bool := false) (hold : Nat := 1) (inMode : Nat := 0) : IO (Array Cyc) := do
  JIT.reset h
  JIT.setInput h 1 (UInt64.ofNat bd)
  JIT.setInput h 5 0
  let e := bd + 1
  let total := starts[starts.size - 1]! + 41 * e + 30
  let mut tr : Array Cyc := #[]
  let mut idx := 0
  for t in [0:total] do
    let mut sv := false
    for i in [0:starts.size] do
      if t ≥ starts[i]! && t < starts[i]! + hold then sv := true
      if extra && t == starts[i]! + 9 * e + 1 then sv := true
    if inMode != 0 then
      let tx := inputsAt e starts txs inMode t
      JIT.setInput h 2 (UInt64.ofNat tx.addr)
      JIT.setInput h 3 (if tx.rw then 1 else 0)
      JIT.setInput h 4 (UInt64.ofNat tx.data)
    else if idx < starts.size && t == starts[idx]! then
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

/-- Bus waveform of the transaction started at cycle `s`, through the cycle
    after STOP. -/
def busWave (tr : Array Cyc) (bd : Nat) (s : Nat) : Array (Bool × Bool) :=
  (tr.extract s (s + 39 * (bd + 1) + 2)).map fun c => (c.scl, c.sda)

def runCase (h : JITHandle) (bd : Nat) (gaps : Array Nat) (txs : Array Tx)
    (extra : Bool := false) (hold : Nat := 1) (off : Nat := 0) (inMode : Nat := 0) : IO Bool := do
  let starts := (alignedStarts bd gaps).map (· + off)
  let tr ← runI2c h bd starts txs extra hold inMode
  let mut errs := i2cErrors tr bd starts txs
  for i in [0:starts.size] do
    for x in protocolErrors (busWave tr bd starts[i]!) txs[i]! do
      errs := errs.push s!"bus view of transaction {i}: {x}"
  let tag := s!"I2C bitDiv={bd} gaps={gaps.toList} extraStart={extra} hold={hold} startOffset={off} inMode={inMode}"
  let busyN := (List.range tr.size).filter (fun c => tr[c]!.busy && (c == 0 || !tr[c-1]!.busy))
  IO.println s!"  · {tag}: {tr.size} cycles, starts {starts.toList}, busy rises at {busyN}"
  if errs.isEmpty then
    IO.println s!"  ✓ {tag}: busy once per start, state/scl/sda per half-slot as modelled, I2C bus view ok (START, bits at SCL rises, STOP)"
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
    (!(i2cErrors tr bd (starts.push (starts[1]! + 45 * (bd + 1))) #[txA, txB, txA]).isEmpty)
  pure (a && b && c)

/-- Live controls of the bus-level checker: defects injected into the real trace. -/
def runBusControls (h : JITHandle) (bd : Nat) : IO Bool := do
  let starts := alignedStarts bd #[0]
  let tr ← runI2c h bd starts #[txA]
  let s := starts[0]!
  let e := bd + 1
  let mutate := fun (lo hi : Nat) (f : Cyc → Cyc) =>
    Id.run do
      let mut t := tr
      for c in [s + lo:s + hi] do t := t.modify c f
      return t
  let bad := fun (t : Array Cyc) => !(protocolErrors (busWave t bd s) txA).isEmpty
  let nm := fun (x : String) => s!"bitDiv={bd}: {x}"
  let mut ok ← check (nm "live trace passes the bus view") (!bad tr)
  -- START half (half 0): SDA released instead of low → no START
  ok := (← check (nm "SDA kept high in the START slot (no START) rejected")
    (bad (mutate 1 (1 + e) fun x => { x with sda := true }))) && ok
  -- STOP halves (37, 38): SDA kept high → no SDA fall / rise around STOP
  ok := (← check (nm "SDA kept high in the STOP slot (no STOP) rejected")
    (bad (mutate (1 + 37 * e) (1 + 39 * e) fun x => { x with sda := true }))) && ok
  -- bit 3 (SCL high half 1 + 2*3 + 1 = 8): SDA inverted in the last cycle of the half
  -- (needs two cycles per half: at bitDiv = 0 an SCL-high half is one sample)
  if bd > 0 then
    ok := (← check (nm "SDA changing while SCL is high rejected")
      (bad (mutate (1 + 8 * e + e - 1) (1 + 8 * e + e) fun x => { x with sda := !x.sda }))) && ok
  -- bit 3 whole slot (halves 7, 8) inverted → wrong bit
  ok := (← check (nm "a wrong bit rejected")
    (bad (mutate (1 + 7 * e) (1 + 9 * e) fun x => { x with sda := !x.sda }))) && ok
  pure ok

def main : IO Unit := do
  IO.println "=== i2cMasterHW — JIT co-sim (busy once per request, state/SCL/SDA per half-slot, bus view) ==="
  (← IO.getStdout).flush
  let mut ok ← controls
  ok := (← protocolControls) && ok
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
  IO.println "-- start pulse on every cycle of the divider period (not only on a tick)"
  for bd in [1, 3, 5] do
    for off in List.range (bd + 1) do
      ok := (← runCase h bd #[0] #[txA] (off := off)) && ok
  for bd in [2, 3] do
    ok := (← runCase h bd #[0, 1] #[txA, txB] (off := 1)) && ok
  IO.println "-- addr/rw/data change right after the accepted start (latched at the start pulse)"
  for bd in [0, 1, 3, 5] do
    ok := (← runCase h bd #[0] #[txA] (inMode := 1)) && ok
    ok := (← runCase h bd #[0, 0, 4] #[txA, txB, { addr := 0x7F, rw := false, data := 0x00 }] (inMode := 1)) && ok
  for bd in [1, 3] do
    for off in List.range (bd + 1) do
      ok := (← runCase h bd #[0, 1] #[txA, txB] (off := off) (inMode := 1)) && ok
  IO.println "-- start pulse while busy with different addr/rw/data is ignored; the next start uses its own inputs"
  for bd in [0, 1, 3] do
    ok := (← runCase h bd #[0, 2] #[txA, txB] (extra := true) (inMode := 2)) && ok
    ok := (← runCase h bd #[1, 0, 2] #[txB, txA, txB] (extra := true) (inMode := 2)) && ok
  ok := (← latchControls) && ok
  IO.println "-- negative controls on the live design"
  for bd in [0, 1, 3] do
    ok := (← runMismatch h bd) && ok
  for bd in [0, 1, 3] do
    ok := (← runBusControls h bd) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.I2CHWJITTest
