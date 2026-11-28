/-
  JIT co-sim of the generated hardware for the key-value engine
  `IP.Net.MemcachedHW.kvHw`, checked cycle by cycle against the pure oracle
  `IP.Net.Memcached.applyCommand` (the existing MemcachedHWTest runs 4 commands
  through the Signal interpreter and lists the `replyValid` pulses it saw).

  Ports after `#sim` lowering (wide ports take ⌈w/32⌉ 32-bit slots, low word
  first): inputs opStart = 0, opCode = 1, opKey = 2, opValue = 3..6,
  opFlags = 7; outputs replyValid = 0, replyKind = 1, replyKey = 2,
  replyValue = 3..6, replyFlags = 7, busy = 8.

  Reference: for a command whose `opStart` pulse is at cycle s the oracle gives
  the reply (kind, and key / flags / value for a `get` hit) and the slot i the
  key is found in (`lookup`).  The engine scans one slot per cycle, so
  `replyValid` is high for exactly one cycle, at s + 4 + i on a hit and at
  s + 19 on a miss; `busy` is low at s, high from s + 1 through the reply cycle,
  low again after it.  The script runs 63 commands (set / add / get / delete,
  hits, misses, overwrite, 20 distinct keys so the 16-slot FIFO wraps and evicts)
  with the op inputs driven with garbage on every cycle except the start pulse
  (the engine must latch them), under several start schedules (the earliest
  legal start right after the reply, and gaps of 0-3 / 17 cycles).

  `kvErrors` checks: the cycles with `replyValid` are exactly the expected
  ones (nothing before the first start, nothing after the last reply, no
  duplicate, none missing, none wider than 1 cycle); `replyKind` at each; key /
  flags / value at each `VALUE`; `busy` equal to the expected busy window on
  every cycle.  Synthetic controls for every check run first (no JIT), plus
  live controls: an oracle fed a different script must be rejected.

  Not checked: reply fields of non-VALUE replies (documented as don't-care), a
  `start` pulsed while busy (see `probeMain`, NOT in CI).
-/
import IP.Net.MemcachedHW
import IP.Net.Memcached
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Net.Memcached
open Sparkle.IP.Net.MemcachedHW

namespace Sparkle.Tests.IP.Net.MemcachedHWJITTest

set_option maxRecDepth 100000

def kvTop (opStart : Signal defaultDomain Bool) (opCode : Signal defaultDomain (BitVec 2))
    (opKey : Signal defaultDomain (BitVec 64)) (opValue : Signal defaultDomain (BitVec 128))
    (opFlags : Signal defaultDomain (BitVec 32)) : KvHwOut defaultDomain :=
  kvHw opStart opCode opKey opValue opFlags

#sim kvTop

structure Cyc where
  valid : Bool
  kind : Nat
  key : Nat
  value : Nat
  flags : Nat
  busy : Bool
  deriving Inhabited

/-- Expected reply of one command, with the cycle of the start pulse. -/
structure Exp where
  start : Nat
  emit : Nat
  kind : Nat
  isValue : Bool
  key : Nat
  value : Nat
  flags : Nat
  deriving Inhabited

/-! ## Oracle side -/

def packMsb (bytes : Array UInt8) (width : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:width] do
    acc := acc * 256 + (if i < bytes.size then (bytes[i]!).toNat else 0)
  return acc

def codeOf : Command → Nat
  | .get _ => 0 | .set .. => 1 | .add .. => 2 | .del _ => 3 | .err => 0

def keyOf : Command → Array UInt8
  | .get k => k | .set k .. => k | .add k .. => k | .del k => k | .err => #[]

def valOf : Command → Array UInt8
  | .set _ _ _ v => v | .add _ _ _ v => v | _ => #[]

def flagsOf : Command → Nat
  | .set _ f .. => f | .add _ f .. => f | _ => 0

def kindOf : Reply → Nat
  | .stored => 0 | .notStored => 1 | .value .. => 2 | .end_ => 3
  | .deleted => 4 | .notFound => 5 | .error => 6

/-- Run the commands through the oracle; the i-th command is pulsed at
    `starts[i]` and its reply expected at start + 4 + slot (hit) / start + 19. -/
def expectations (cmds : Array Command) (gaps : Array Nat) : Array Exp := Id.run do
  let mut store : KvStore := {}
  let mut out : Array Exp := #[]
  let mut earliest := 6
  for i in [0:cmds.size] do
    let c := cmds[i]!
    let s := earliest + gaps[i % gaps.size]!
    let emit := match lookup store (keyOf c) with
      | some k => s + 4 + k
      | none => s + 19
    let (st', rs) := applyCommand store c
    store := st'
    let r := rs[0]!
    let e : Exp := match r with
      | .value k f v => { start := s, emit, kind := 2, isValue := true,
                          key := packMsb k 8, value := packMsb v 16, flags := f }
      | _ => { start := s, emit, kind := kindOf r, isValue := false, key := 0, value := 0, flags := 0 }
    out := out.push e
    earliest := emit + 1
  return out

def k (n : Nat) : Array UInt8 := (strToBytes s!"key{n}")
def v (s : String) : Array UInt8 := strToBytes s

def script : Array Command := Id.run do
  let mut cs : Array Command := #[
    .get (k 1), .set (k 1) 7 0 (v "hello"), .get (k 1), .add (k 1) 1 0 (v "nope"),
    .add (k 2) 9 0 (v "second"), .get (k 2), .set (k 1) 0xDEADBEEF 0 (v "HELLO WORLD 12345"),
    .get (k 1), .del (k 1), .del (k 1), .get (k 1), .set (k 3) 3 0 (v "three"), .get (k 3),
    .get (k 2), .get (k 9)]
  -- 20 distinct keys: the 16-slot FIFO wraps and evicts the oldest
  for n in [10:30] do cs := cs.push (.set (k n) n 0 (v s!"val{n}"))
  for n in [10:30] do cs := cs.push (.get (k n))
  cs := cs ++ #[.add (k 29) 5 0 (v "dup"), .add (k 10) 6 0 (v "again"), .del (k 29), .get (k 29),
    .del (k 11), .get (k 11), .set (k 11) 11 0 (v "back"), .get (k 11)]
  return cs

/-! ## Pure checker -/

def hexN (b : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 b)

/-- Violations of the engine's handshake and reply contract on a trace. -/
def kvErrors (tr : Array Cyc) (exps : Array Exp) : Array String := Id.run do
  let n := tr.size
  let mut errs : Array String := #[]
  let expEmit := exps.map (·.emit)
  let gotValid := (List.range n).filter (fun c => tr[c]!.valid)
  if gotValid != expEmit.toList then
    errs := errs.push s!"replyValid at cycles {gotValid}, expected exactly {expEmit.toList}"
    if exps.size > 0 then
      if gotValid.any (· < exps[0]!.start) then errs := errs.push "replyValid before the first start"
      if gotValid.any (· > exps[exps.size - 1]!.emit) then errs := errs.push "replyValid after the last reply"
  for e in exps do
    if e.emit < n && tr[e.emit]!.valid then
      if tr[e.emit]!.kind != e.kind then
        errs := errs.push s!"cmd at {e.start}: replyKind {tr[e.emit]!.kind} at {e.emit}, expected {e.kind}"
      if e.isValue then
        if tr[e.emit]!.key != e.key then
          errs := errs.push s!"cmd at {e.start}: VALUE key {hexN tr[e.emit]!.key}, expected {hexN e.key}"
        if tr[e.emit]!.value != e.value then
          errs := errs.push s!"cmd at {e.start}: VALUE value {hexN tr[e.emit]!.value}, expected {hexN e.value}"
        if tr[e.emit]!.flags != e.flags then
          errs := errs.push s!"cmd at {e.start}: VALUE flags {hexN tr[e.emit]!.flags}, expected {hexN e.flags}"
  -- busy window per command: low at start, high start+1 .. emit, low after
  let mut expBusy : Array Bool := Array.replicate n false
  for e in exps do
    for c in [e.start+1:min n (e.emit+1)] do expBusy := expBusy.set! c true
  let mut bad := 0
  for c in [0:n] do
    if tr[c]!.busy != expBusy[c]! && bad < 3 then
      bad := bad + 1
      errs := errs.push s!"cycle {c}: busy {tr[c]!.busy}, expected {expBusy[c]!}"
  return errs

/-! ## Synthetic controls -/

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  {if cond then "✓" else "✗"} {name}"
  pure cond

def idealTrace (exps : Array Exp) (n : Nat) : Array Cyc := Id.run do
  let mut tr : Array Cyc := Array.replicate n { valid := false, kind := 0, key := 0, value := 0, flags := 0, busy := false }
  for e in exps do
    for c in [e.start+1:min n (e.emit+1)] do tr := tr.modify c fun x => { x with busy := true }
    if e.emit < n then
      tr := tr.modify e.emit fun x => { x with valid := true, kind := e.kind, key := e.key, value := e.value, flags := e.flags }
  return tr

def controls : IO Bool := do
  IO.println "-- synthetic controls (checker must accept the ideal trace and reject each defect)"
  let mut ok := true
  let cmds := script.extract 0 12
  let exps := expectations cmds #[0, 2]
  let n := exps[exps.size - 1]!.emit + 12
  let good := idealTrace exps n
  let rej := fun (s : String) (t : Array Cyc) => check s (!(kvErrors t exps).isEmpty)
  ok := (← check "ideal trace accepted" (kvErrors good exps).isEmpty) && ok
  let e1 := exps[1]!   -- set of a new key (miss, slowest path)
  let e2 := exps[2]!   -- get hit → VALUE
  ok := (← rej "second replyValid pulse (spurious)" (good.modify (e2.start + 3) fun x => { x with valid := true })) && ok
  ok := (← rej "replyValid 2 cycles wide" (good.modify (e1.emit + 1) fun x => { x with valid := true })) && ok
  ok := (← rej "missing replyValid" (good.modify e1.emit fun x => { x with valid := false })) && ok
  ok := (← rej "replyValid one cycle early" ((good.modify e1.emit fun x => { x with valid := false }).modify (e1.emit - 1) fun x => { x with valid := true })) && ok
  ok := (← rej "replyValid one cycle late" ((good.modify e1.emit fun x => { x with valid := false }).modify (e1.emit + 1) fun x => { x with valid := true })) && ok
  ok := (← rej "replyValid before the first start" (good.modify 2 fun x => { x with valid := true })) && ok
  ok := (← rej "replyValid after the last reply" (good.modify (n - 2) fun x => { x with valid := true })) && ok
  ok := (← rej "wrong replyKind" (good.modify e1.emit fun x => { x with kind := x.kind + 1 })) && ok
  ok := (← rej "VALUE with wrong key" (good.modify e2.emit fun x => { x with key := x.key + 1 })) && ok
  ok := (← rej "VALUE with wrong value" (good.modify e2.emit fun x => { x with value := x.value + 1 })) && ok
  ok := (← rej "VALUE with wrong flags" (good.modify e2.emit fun x => { x with flags := x.flags + 1 })) && ok
  ok := (← rej "busy high before the first start" (good.modify 2 fun x => { x with busy := true })) && ok
  ok := (← rej "busy low inside a command" (good.modify (e1.start + 6) fun x => { x with busy := false })) && ok
  ok := (← rej "busy stuck after the reply" (good.modify (e2.emit + 1) fun x => { x with busy := true })) && ok
  ok := (← rej "busy low in the reply cycle" (good.modify e2.emit fun x => { x with busy := false })) && ok
  ok := (← rej "busy high at the start cycle" (good.modify e2.start fun x => { x with busy := true })) && ok
  -- an oracle with a different command is also rejected
  let other := expectations ((script.extract 0 12).set! 2 (.get (k 9))) #[0, 2]
  ok := (← check "trace of another script rejected" (!(kvErrors good other).isEmpty)) && ok
  pure ok

/-! ## JIT runs -/

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

/-- Drive the commands at the expected start cycles; non-start cycles carry
    garbage on the op inputs. -/
def runKv (h : JITHandle) (cmds : Array Command) (exps : Array Exp) (extra : Nat := 12) :
    IO (Array Cyc) := do
  JIT.reset h
  let total := exps[exps.size - 1]!.emit + extra
  let mut tr : Array Cyc := #[]
  let mut idx := 0
  let mut rnd := 12345
  for t in [0:total] do
    let isStart := idx < exps.size && t == exps[idx]!.start
    rnd := lcg rnd
    let g1 := rnd
    rnd := lcg rnd
    let g2 := rnd
    let setWide := fun (base : UInt32) (x : Nat) (lo : Nat) =>
      (List.range 4).forM fun j => JIT.setInput h (base + UInt32.ofNat j) (UInt64.ofNat (((x >>> (32 * j)) + lo * j) % 4294967296))
    if isStart then
      let c := cmds[idx]!
      JIT.setInput h 0 1
      JIT.setInput h 1 (UInt64.ofNat (codeOf c))
      JIT.setInput h 2 (UInt64.ofNat (packMsb (keyOf c) 8))
      let vv := packMsb (valOf c) 16
      (List.range 4).forM fun j => JIT.setInput h (3 + UInt32.ofNat j) (UInt64.ofNat ((vv >>> (32 * j)) % 4294967296))
      JIT.setInput h 7 (UInt64.ofNat (flagsOf c))
      idx := idx + 1
    else
      JIT.setInput h 0 0
      JIT.setInput h 1 (UInt64.ofNat (g1 % 4))
      JIT.setInput h 2 (UInt64.ofNat g2)
      setWide 3 (g1 * 65537 + g2) 0
      JIT.setInput h 7 (UInt64.ofNat (g1 % 4294967296))
    JIT.eval h
    let valid := (← JIT.getOutput h 0) != 0
    let kind := (← JIT.getOutput h 1).toNat
    let key := (← JIT.getOutput h 2).toNat
    let mut value := 0
    for j in [0:4] do
      value := value + ((← JIT.getOutput h (3 + UInt32.ofNat j)).toNat % 4294967296) * 2 ^ (32 * j)
    let flags := (← JIT.getOutput h 7).toNat
    let busy := (← JIT.getOutput h 8) != 0
    tr := tr.push { valid, kind, key, value, flags, busy }
    JIT.tick h
  pure tr

def runCase (h : JITHandle) (gaps : Array Nat) (cmds : Array Command) : IO Bool := do
  let exps := expectations cmds gaps
  let tr ← runKv h cmds exps
  let errs := kvErrors tr exps
  let nValid := (tr.filter (·.valid)).size
  let nHit := (exps.filter (·.isValue)).size
  let tag := s!"kvHw gaps={gaps.toList}"
  IO.println s!"  · {tag}: {cmds.size} commands, {tr.size} cycles, {nValid} replyValid pulses ({nHit} VALUE)"
  if errs.isEmpty then
    IO.println s!"  ✓ {tag}: replyValid exactly once per command at the expected cycle, kinds / VALUE fields / busy as the oracle"
  else
    for x in errs.toList.take 8 do IO.println s!"  ✗ {tag}: {x}"
  pure errs.isEmpty

def main : IO Unit := do
  IO.println "=== kvHw (memcached HW) — JIT co-sim (replyValid once per command, busy, replies vs oracle) ==="
  (← IO.getStdout).flush
  let mut ok ← controls
  let sim ← kvTop.Sim.load
  let h := sim.handle
  IO.println "-- script under several start schedules"
  for gaps in [#[0], #[0, 1, 2, 3], #[3, 0, 0, 1, 2], #[17]] do
    ok := (← runCase h gaps script) && ok
  IO.println "-- negative controls on the live design"
  let exps := expectations script #[0]
  let tr ← runKv h script exps
  let other := expectations (script.set! 2 (.get (k 9))) #[0]
  ok := (← check "oracle fed a different script flags the run" (!(kvErrors tr other).isEmpty)) && ok
  let other2 := expectations (script.set! 5 (.set (k 1) 7 0 (v "hellp"))) #[0]
  ok := (← check "oracle with a different stored value flags the run" (!(kvErrors tr other2).isEmpty)) && ok
  let late := exps.map fun e => { e with emit := e.emit + 1 }
  ok := (← check "checker told replies one cycle later flags the run" (!(kvErrors tr late).isEmpty)) && ok
  JIT.destroy h
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

/-! ## Probe: `opStart` while busy (NOT in CI) -/

/-- A `get` of a stored key is started; one cycle later (the engine is busy)
    `opStart` is pulsed again with a different command.  The first command's
    reply must be unaffected (the pulse is a protocol violation, so the second
    command may be ignored, but the in-flight one must still be answered with
    its own kind / key). -/
def probeMain : IO Unit := do
  IO.println "=== kvHw — opStart while busy (NOT in CI: expected to FAIL on the current design) ==="
  (← IO.getStdout).flush
  let sim ← kvTop.Sim.load
  let h := sim.handle
  let cmds : Array Command := #[.set (k 1) 7 0 (v "hello"), .get (k 1)]
  let exps := expectations cmds #[0]
  let mut tr : Array Cyc := #[]
  JIT.reset h
  let s1 := exps[1]!.start
  for t in [0:exps[1]!.emit + 40] do
    let setCmd := fun (c : Command) => do
      JIT.setInput h 0 1
      JIT.setInput h 1 (UInt64.ofNat (codeOf c))
      JIT.setInput h 2 (UInt64.ofNat (packMsb (keyOf c) 8))
      let vv := packMsb (valOf c) 16
      (List.range 4).forM fun j => JIT.setInput h (3 + UInt32.ofNat j) (UInt64.ofNat ((vv >>> (32 * j)) % 4294967296))
      JIT.setInput h 7 (UInt64.ofNat (flagsOf c))
    if t == exps[0]!.start then setCmd cmds[0]!
    else if t == s1 then setCmd cmds[1]!
    else if t == s1 + 3 then setCmd (.del (k 1))   -- start pulse while busy
    else JIT.setInput h 0 0
    JIT.eval h
    let valid := (← JIT.getOutput h 0) != 0
    let kind := (← JIT.getOutput h 1).toNat
    let key := (← JIT.getOutput h 2).toNat
    let busy := (← JIT.getOutput h 8) != 0
    tr := tr.push { valid, kind, key, value := 0, flags := 0, busy }
    JIT.tick h
  JIT.destroy h
  let vs := (List.range tr.size).filter fun c => tr[c]!.valid && c ≥ s1
  let kinds := vs.map fun c => tr[c]!.kind
  IO.println s!"  · get started at {s1}, extra start (del) at {s1 + 3}: replyValid at {vs}, kinds {kinds} (expected one reply, VALUE = 2, at {exps[1]!.emit})"
  if vs == [exps[1]!.emit] && kinds == [2] then
    IO.println "\nPROBE PASS"
  else
    IO.println "  ✗ the in-flight get was disturbed by the start pulse while busy"
    IO.println "\nPROBE FAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.MemcachedHWJITTest
