/-
  Protocol agents for AXI4-Stream and AXI4-Lite — transactions as a
  SystemVerilog verification engineer means them.

  Vocabulary and structure follow the documents SV users learn this from:

  * UVM User's Guide (Accellera, 1.2), ch. 3 "Developing Reusable
    Verification Components": a DATA ITEM (transaction) is a record of the
    protocol's fields; a DRIVER turns items into pin activity; a MONITOR
    turns pin activity back into items and publishes them on an ANALYSIS
    PORT; a SCOREBOARD subscribes.  Ch. 2 (TLM): blocking put/get, analysis
    ports, and the TLM-2 generic payload (command, address, data, byte
    enables, response) — the fields of `AxiLiteTxn`.
  * cocotbext-axi — the same idea from a host language, which is our
    situation.  The API mirrors it: `AxiStreamBus.fromPrefix`,
    `AxiStreamSource.send`, `AxiStreamSink.recv`, `AxiStreamMonitor`,
    `AxiStreamFrame`, `AxiLiteMaster.read` / `write`, `AxiLiteRam`.
  * AMBA AXI and AXI4-Stream specifications — the handshake rules the
    monitors check: once VALID is asserted it stays asserted, with the
    payload unchanged, until the handshake.

  A bus is bound to the design BY SIGNAL NAME (`fromPrefix pins "s_axil"`
  finds `s_axil_awaddr`, …), so it attaches to a design written in
  SystemVerilog by somebody else (`Sv.Dut`) as well as to one Sparkle
  emitted.  Which signals exist and how wide they are is read from the
  design, not typed in.

  Not here: AXI4 bursts and IDs, APB, constrained-random stimulus,
  functional coverage.
-/
import Std.Data.HashMap
import Sparkle.Verification.Tlm
import Sparkle.Core.SimSv

namespace Sparkle.Verification.Tlm

open Sparkle.Core.Sim

/-! ### Analysis port -/

/-- UVM's `uvm_analysis_port`: a monitor WRITES each transaction it has
    seen; any number of subscribers (scoreboards, coverage, a log) receive
    it.  Every transaction is also kept, with the cycle it completed in. -/
structure AnalysisPort (τ : Type) where
  subscribers : IO.Ref (Array (Nat → τ → IO Unit))
  log : IO.Ref (Array (Nat × τ))

namespace AnalysisPort

def new {τ : Type} : IO (AnalysisPort τ) :=
  return { subscribers := ← IO.mkRef #[], log := ← IO.mkRef #[] }

def subscribe {τ : Type} (ap : AnalysisPort τ) (f : Nat → τ → IO Unit) : IO Unit :=
  ap.subscribers.modify (·.push f)

def write {τ : Type} (ap : AnalysisPort τ) (cycle : Nat) (x : τ) : IO Unit := do
  ap.log.modify (·.push (cycle, x))
  for f in ← ap.subscribers.get do f cycle x

def items {τ : Type} (ap : AnalysisPort τ) : IO (List τ) :=
  return (← ap.log.get).toList.map (·.2)

def count {τ : Type} (ap : AnalysisPort τ) : IO Nat := return (← ap.log.get).size

end AnalysisPort

/-! ### Pins -/

/-- One signal of the design, by name.  Either the testbench drives it (a
    DUT input) or the DUT does (a DUT output). -/
structure Pin (I O : Type) where
  name : String
  width : Nat
  /-- DUT input: (set, read back what was set) -/
  drive? : Option ((I → Nat → I) × (I → Nat))
  /-- DUT output -/
  sample? : Option (O → Nat)

/-- The value on the pin in a cycle, whoever drives it. -/
def Pin.get {I O : Type} (p : Pin I O) (i : I) (o : O) : Nat :=
  match p.sample?, p.drive? with
  | some f, _ => f o
  | none, some (_, g) => g i
  | none, none => 0

/-- The signals of a design, looked up by name. -/
structure PinMap (I O : Type) where
  /-- what the design is called in error messages -/
  design : String
  names : List String
  find : String → Option (Pin I O)

/-- A signal that must exist. -/
def PinMap.pin {I O : Type} (pins : PinMap I O) (name : String) : IO (Pin I O) :=
  match pins.find name with
  | some p => pure p
  | none => throw (IO.userError s!"design '{pins.design}' has no signal '{name}'; its ports are {pins.names}")

/-- The pins of a design loaded from SystemVerilog. -/
def _root_.Sparkle.Core.Sim.Sv.Dut.pins (d : Sv.Dut) : PinMap Sv.Pins Sv.Pins where
  design := d.top
  names := d.portNames
  find name :=
    match d.inputIndex? name, d.outputIndex? name with
    | some k, _ =>
      some { name, width := (d.inputs.getD k default).width
             drive? := some (fun i v => i.setIfInBounds k v, fun i => i.getD k 0)
             sample? := none }
    | none, some k =>
      some { name, width := (d.outputs.getD k default).width
             drive? := none, sample? := some fun o => o.getD k 0 }
    | none, none => none

/-! ### One ready/valid channel on pins -/

/-- `valid`, `ready` (absent: the receiver is always ready) and the payload
    signals. -/
structure Channel (I O : Type) where
  name : String
  valid : Pin I O
  ready : Option (Pin I O)
  fields : Array (Pin I O)

namespace Channel

variable {I O : Type}

/-- The payload on the wires when `valid` is high. -/
def offered (ch : Channel I O) (i : I) (o : O) : Option (Array Nat) :=
  if ch.valid.get i o != 0 then some (ch.fields.map (·.get i o)) else none

def isReady (ch : Channel I O) (i : I) (o : O) : Bool :=
  match ch.ready with
  | some r => r.get i o != 0
  | none => true

/-- The testbench SENDS on this channel: it must be able to drive `valid`
    and every payload signal, and the DUT drives `ready`. -/
def source (ch : Channel I O) (role : String) : Except String (SourcePort I O (Array Nat)) := do
  let drv (p : Pin I O) : Except String (I → Nat → I) :=
    match p.drive? with
    | some (set, _) => pure set
    | none => throw s!"{role}: '{p.name}' is an OUTPUT of the design, but {role} has to drive it — the stream runs the other way (bind the agent of the opposite role)"
  let setValid ← drv ch.valid
  let setFields ← ch.fields.mapM drv
  let ready ← match ch.ready with
    | none => pure (fun (_ : O) => true)
    | some r => match r.sample? with
      | some f => pure (fun o => f o != 0)
      | none => throw s!"{role}: '{r.name}' is an INPUT of the design, but {role} expects the design to drive it"
  return {
    name := ch.name
    drive := fun i x? =>
      match x? with
      | some xs =>
        let i := setValid i 1
        (List.range setFields.size).foldl (fun i k =>
          (setFields.getD k (fun i _ => i)) i (xs.getD k 0)) i
      | none => setValid i 0
    ready }

/-- The testbench RECEIVES on this channel: the DUT drives `valid` and the
    payload, the testbench drives `ready`. -/
def sink (ch : Channel I O) (role : String) : Except String (SinkPort I O (Array Nat)) := do
  let smp (p : Pin I O) : Except String (O → Nat) :=
    match p.sample? with
    | some f => pure f
    | none => throw s!"{role}: '{p.name}' is an INPUT of the design, but {role} expects the design to drive it — the stream runs the other way (bind the agent of the opposite role)"
  let valid ← smp ch.valid
  let fields ← ch.fields.mapM smp
  let setReady ← match ch.ready with
    | none => pure (fun (i : I) (_ : Bool) => i)
    | some r => match r.drive? with
      | some (set, _) => pure (fun i b => set i (if b then 1 else 0))
      | none => throw s!"{role}: '{r.name}' is an OUTPUT of the design, but {role} has to drive it"
  return {
    name := ch.name
    setReady
    valid := fun o => if valid o != 0 then some (fields.map (· o)) else none }

end Channel

/-- Watch a channel without driving anything (UVM: a passive monitor).
    `onFire` is called in the cycle of each handshake.  Reports the two
    handshake violations of the AMBA specifications: `valid` withdrawn, or
    the payload changed, before the handshake. -/
def Bench.addChannelMonitor {S I O : Type} (b : Bench S I O) (ch : Channel I O)
    (onFire : Nat → Array Nat → IO Unit) : IO Unit := do
  let pending : IO.Ref (Option (Array Nat)) ← IO.mkRef none
  let agent : Agent I O := {
    name := ch.name
    drive := fun _ i => pure i
    observe := fun c i o => do
      let before ← pending.get
      match ch.offered i o with
      | some xs =>
        let changed := match before with
          | some ys => ys != xs
          | none => false
        if ch.isReady i o then
          onFire c xs
          pending.set none
        else pending.set (some xs)
        return if changed then ["the payload changed while valid was waiting for ready"] else []
      | none =>
        pending.set none
        return if before.isSome then ["valid was withdrawn before the handshake"] else []
    busy := return false }
  b.agents.modify (·.push agent)

/-- `0x…` -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

private def lookup {I O : Type} (pins : PinMap I O) (what pfx : String)
    (required : List String) (name : String) : IO (Option (Pin I O)) := do
  match pins.find s!"{pfx}_{name}" with
  | some p => return some p
  | none =>
    if required.contains name then
      let have_ := pins.names.filter (·.startsWith (pfx ++ "_"))
      throw (IO.userError
        (s!"{what}.fromPrefix: design '{pins.design}' has no signal '{pfx}_{name}'. " ++
         (if have_.isEmpty then s!"No signal starts with '{pfx}_'; its ports are {pins.names}"
          else s!"Signals with that prefix: {have_}")))
    else return none

/-! ### AXI4-Stream -/

/-- A frame (packet): the bytes between two `tlast`, and the sideband of
    its last beat.  cocotbext-axi's `AxiStreamFrame`. -/
structure AxiStreamFrame where
  tdata : Array UInt8
  tid : Nat := 0
  tdest : Nat := 0
  tuser : Nat := 0
  deriving BEq, Repr, Inhabited

/-- The signals of one AXI4-Stream interface.  Only `tdata` and `tvalid` are
    required; the rest are used when the design has them. -/
structure AxiStreamBus (I O : Type) where
  name : String
  tdata : Pin I O
  tvalid : Pin I O
  tready : Option (Pin I O)
  tlast : Option (Pin I O)
  tkeep : Option (Pin I O)
  tid : Option (Pin I O)
  tdest : Option (Pin I O)
  tuser : Option (Pin I O)

namespace AxiStreamBus

variable {I O : Type}

/-- Bind `<prefix>_tdata`, `<prefix>_tvalid`, … -/
def fromPrefix (pins : PinMap I O) (pfx : String) : IO (AxiStreamBus I O) := do
  let get := lookup pins "AxiStreamBus" pfx ["tdata", "tvalid"]
  let some tdata ← get "tdata" | unreachable!
  let some tvalid ← get "tvalid" | unreachable!
  if tdata.width % 8 != 0 then
    throw (IO.userError s!"AxiStreamBus.fromPrefix: '{tdata.name}' is {tdata.width} bits wide; AXI4-Stream data is a whole number of bytes")
  return { name := pfx, tdata, tvalid
           tready := ← get "tready", tlast := ← get "tlast", tkeep := ← get "tkeep"
           tid := ← get "tid", tdest := ← get "tdest", tuser := ← get "tuser" }

def bytesPerBeat (bus : AxiStreamBus I O) : Nat := bus.tdata.width / 8

/-- Payload signals, in a fixed order: tdata, then the optional ones. -/
def channel (bus : AxiStreamBus I O) : Channel I O where
  name := bus.name
  valid := bus.tvalid
  ready := bus.tready
  fields := #[bus.tdata] ++ ([bus.tkeep, bus.tlast, bus.tid, bus.tdest, bus.tuser].filterMap id).toArray

/-- One transfer. -/
structure Beat where
  data : Nat
  keep : Nat
  last : Bool
  id : Nat
  dest : Nat
  user : Nat

def encode (bus : AxiStreamBus I O) (x : Beat) : Array Nat :=
  #[x.data]
    ++ (if bus.tkeep.isSome then #[x.keep] else #[])
    ++ (if bus.tlast.isSome then #[if x.last then 1 else 0] else #[])
    ++ (if bus.tid.isSome then #[x.id] else #[])
    ++ (if bus.tdest.isSome then #[x.dest] else #[])
    ++ (if bus.tuser.isSome then #[x.user] else #[])

def decode (bus : AxiStreamBus I O) (xs : Array Nat) : Beat :=
  -- the next optional field, if the bus has it
  let next (present : Bool) (dflt : Nat) (k : Nat) : Nat × Nat :=
    if present then (xs.getD k dflt, k + 1) else (dflt, k)
  let (keep, k1) := next bus.tkeep.isSome (2 ^ bus.bytesPerBeat - 1) 1
  -- no tlast signal: every transfer is a frame
  let (last, k2) := next bus.tlast.isSome 1 k1
  let (id, k3) := next bus.tid.isSome 0 k2
  let (dest, k4) := next bus.tdest.isSome 0 k3
  let (user, _) := next bus.tuser.isSome 0 k4
  { data := xs.getD 0 0, keep, last := last != 0, id, dest, user }

/-- A frame as transfers: bytes packed low lane first, `tkeep` marking the
    bytes of a partial last transfer. -/
def beats (bus : AxiStreamBus I O) (f : AxiStreamFrame) : Except String (List Beat) := do
  let n := bus.bytesPerBeat
  if f.tdata.isEmpty then throw s!"{bus.name}: an AXI4-Stream frame needs at least one byte"
  if f.tdata.size % n != 0 && bus.tkeep.isNone then
    throw s!"{bus.name}: a frame of {f.tdata.size} bytes does not fill {n}-byte transfers and the bus has no tkeep"
  let count := (f.tdata.size + n - 1) / n
  return (List.range count).map fun b =>
    let len := min n (f.tdata.size - b * n)
    let data := (List.range len).foldl (fun acc j =>
      acc ||| ((f.tdata.getD (b * n + j) 0).toNat <<< (8 * j))) 0
    { data, keep := 2 ^ len - 1, last := b + 1 == count
      id := f.tid, dest := f.tdest, user := f.tuser }

end AxiStreamBus

/-- Turns transfers into frames (shared by the sink and the monitor). -/
private def frameAssembler {I O : Type} (bus : AxiStreamBus I O)
    (ap : AnalysisPort AxiStreamFrame) : IO (Nat → Array Nat → IO Unit) := do
  let acc : IO.Ref (Array UInt8) ← IO.mkRef #[]
  return fun c xs => do
    let x := bus.decode xs
    for j in [0:bus.bytesPerBeat] do
      if (x.keep >>> j) % 2 == 1 then
        acc.modify (·.push ((x.data >>> (8 * j)) % 256).toUInt8)
    if x.last then
      ap.write c { tdata := ← acc.get, tid := x.id, tdest := x.dest, tuser := x.user }
      acc.set #[]

/-- Drives a stream INTO the design (all signals except `tready`). -/
structure AxiStreamSource where
  /-- queue a frame -/
  send : AxiStreamFrame → IO Unit
  /-- clock until everything queued has been accepted (`false`: timeout) -/
  wait : IO Bool
  /-- frames whose last transfer has been accepted -/
  sent : AnalysisPort AxiStreamFrame

def AxiStreamSource.new {S I O : Type} [Sim S I O] (b : Bench S I O) (bus : AxiStreamBus I O)
    (pace : Pace := .always) : IO AxiStreamSource := do
  let port ← IO.ofExcept ((bus.channel.source s!"AxiStreamSource({bus.name})").mapError IO.userError)
  let sent ← AnalysisPort.new
  let onBeat ← frameAssembler bus sent
  let d ← b.addDriver port pace onBeat
  return {
    send := fun f => do
      let bs ← IO.ofExcept ((bus.beats f).mapError IO.userError)
      d.sendAll (bs.map bus.encode)
    wait := b.runUntil d.idle s!"{bus.name}: the queued frames to be accepted"
    sent }

/-- Receives a stream FROM the design: drives `tready`, collects frames. -/
structure AxiStreamSink where
  /-- every frame received, as it completes -/
  frames : AnalysisPort AxiStreamFrame
  /-- the next frame not yet handed out, clocking the bench until it has
      arrived (`none`: timeout) -/
  recv : IO (Option AxiStreamFrame)

def AxiStreamSink.new {S I O : Type} [Sim S I O] (b : Bench S I O) (bus : AxiStreamBus I O)
    (pace : Pace := .always) : IO AxiStreamSink := do
  let port ← IO.ofExcept ((bus.channel.sink s!"AxiStreamSink({bus.name})").mapError IO.userError)
  let frames ← AnalysisPort.new
  let onBeat ← frameAssembler bus frames
  let _ ← b.addMonitor port pace onBeat
  let taken ← IO.mkRef 0
  return {
    frames
    recv := do
      let n ← taken.get
      if ← b.runUntil (return (← frames.count) > n) s!"{bus.name}: a frame" then
        taken.set (n + 1)
        return ((← frames.log.get)[n]?).map (·.2)
      else return none }

/-- Watches a stream without driving it — on a stream into the design or out
    of it — and publishes its frames. -/
def AxiStreamMonitor.new {S I O : Type} (b : Bench S I O) (bus : AxiStreamBus I O) :
    IO (AnalysisPort AxiStreamFrame) := do
  let frames ← AnalysisPort.new
  let onBeat ← frameAssembler bus frames
  b.addChannelMonitor { bus.channel with name := s!"{bus.name} (monitor)" } onBeat
  return frames

/-! ### AXI4-Lite -/

inductive AxiResp where
  | okay | exokay | slverr | decerr
  deriving BEq, Repr, Inhabited, DecidableEq

/-- The two-bit encoding on `bresp` / `rresp`. -/
def AxiResp.ofBits (n : Nat) : AxiResp :=
  match n % 4 with
  | 0 => .okay | 1 => .exokay | 2 => .slverr | _ => .decerr

def AxiResp.toBits : AxiResp → Nat
  | .okay => 0 | .exokay => 1 | .slverr => 2 | .decerr => 3

instance : ToString AxiResp where
  toString
    | .okay => "OKAY" | .exokay => "EXOKAY" | .slverr => "SLVERR" | .decerr => "DECERR"

/-- One bus access.  The fields are those of the TLM-2 generic payload:
    command, address, data, byte enables, response. -/
structure AxiLiteTxn where
  write : Bool
  addr : Nat
  /-- one bus word -/
  data : Nat
  /-- byte enables of a write (all ones for a read) -/
  strb : Nat
  resp : AxiResp := .okay
  deriving BEq, Repr, Inhabited

instance : ToString AxiLiteTxn where
  toString t := (if t.write then s!"WRITE {hex t.addr} := {hex t.data} strb {hex t.strb}"
    else s!"READ {hex t.addr} = {hex t.data}") ++ (if t.resp == .okay then "" else s!" ({t.resp})")

/-- The signals of one AXI4-Lite interface (five channels). -/
structure AxiLiteBus (I O : Type) where
  name : String
  aw : Channel I O
  w : Channel I O
  b : Channel I O
  ar : Channel I O
  r : Channel I O
  addrWidth : Nat
  dataBytes : Nat
  hasStrb : Bool
  hasAwProt : Bool
  hasArProt : Bool
  hasBResp : Bool
  hasRResp : Bool

namespace AxiLiteBus

variable {I O : Type}

/-- Bind `<prefix>_awaddr`, `<prefix>_awvalid`, … `<prefix>_rready`.
    `awprot`, `arprot`, `wstrb`, `bresp` and `rresp` are optional. -/
def fromPrefix (pins : PinMap I O) (pfx : String) : IO (AxiLiteBus I O) := do
  let required := ["awaddr", "awvalid", "awready", "wdata", "wvalid", "wready",
    "bvalid", "bready", "araddr", "arvalid", "arready", "rdata", "rvalid", "rready"]
  let opt := lookup pins "AxiLiteBus" pfx required
  let req (n : String) : IO (Pin I O) := do
    let some p ← opt n | unreachable!
    return p
  let awaddr ← req "awaddr"
  let wdata ← req "wdata"
  let araddr ← req "araddr"
  let rdata ← req "rdata"
  if wdata.width % 8 != 0 || wdata.width != rdata.width then
    throw (IO.userError s!"AxiLiteBus.fromPrefix: '{wdata.name}' is {wdata.width} bits and '{rdata.name}' is {rdata.width}; they must be equal and a whole number of bytes")
  let awprot ← opt "awprot"
  let arprot ← opt "arprot"
  let wstrb ← opt "wstrb"
  let bresp ← opt "bresp"
  let rresp ← opt "rresp"
  let ch (n : String) (v r : String) (fields : List (Option (Pin I O))) : IO (Channel I O) :=
    return { name := s!"{pfx} {n}", valid := ← req v, ready := some (← req r)
             fields := (fields.filterMap id).toArray }
  return {
    name := pfx
    aw := ← ch "AW" "awvalid" "awready" [some awaddr, awprot]
    w := ← ch "W" "wvalid" "wready" [some wdata, wstrb]
    b := ← ch "B" "bvalid" "bready" [bresp]
    ar := ← ch "AR" "arvalid" "arready" [some araddr, arprot]
    r := ← ch "R" "rvalid" "rready" [some rdata, rresp]
    addrWidth := awaddr.width, dataBytes := wdata.width / 8
    hasStrb := wstrb.isSome, hasAwProt := awprot.isSome, hasArProt := arprot.isSome
    hasBResp := bresp.isSome, hasRResp := rresp.isSome }

def allStrobes (bus : AxiLiteBus I O) : Nat := 2 ^ bus.dataBytes - 1

def awItem (bus : AxiLiteBus I O) (addr prot : Nat) : Array Nat :=
  if bus.hasAwProt then #[addr, prot] else #[addr]
def arItem (bus : AxiLiteBus I O) (addr prot : Nat) : Array Nat :=
  if bus.hasArProt then #[addr, prot] else #[addr]
def wItem (bus : AxiLiteBus I O) (data strb : Nat) : Array Nat :=
  if bus.hasStrb then #[data, strb] else #[data]
def bItem (bus : AxiLiteBus I O) (resp : AxiResp) : Array Nat :=
  if bus.hasBResp then #[resp.toBits] else #[]
def rItem (bus : AxiLiteBus I O) (data : Nat) (resp : AxiResp) : Array Nat :=
  if bus.hasRResp then #[data, resp.toBits] else #[data]
def wStrbOf (bus : AxiLiteBus I O) (xs : Array Nat) : Nat :=
  if bus.hasStrb then xs.getD 1 bus.allStrobes else bus.allStrobes
def bRespOf (bus : AxiLiteBus I O) (xs : Array Nat) : AxiResp :=
  if bus.hasBResp then .ofBits (xs.getD 0 0) else .okay
def rRespOf (bus : AxiLiteBus I O) (xs : Array Nat) : AxiResp :=
  if bus.hasRResp then .ofBits (xs.getD 1 0) else .okay

end AxiLiteBus

/-- Paces of the five channels of one agent. -/
structure AxiLitePace where
  aw : Pace := .always
  w : Pace := .always
  b : Pace := .always
  ar : Pace := .always
  r : Pace := .always

/-- Issues reads and writes against a design that is an AXI4-Lite SLAVE. -/
structure AxiLiteMaster where
  dataBytes : Nat
  /-- write one bus word; `strb = none` writes every byte.  Returns when
      the response has arrived. -/
  writeWord : Nat → Nat → Option Nat → IO AxiResp
  /-- read one bus word -/
  readWord : Nat → IO (Nat × AxiResp)

def AxiLiteMaster.new {S I O : Type} [Sim S I O] (b : Bench S I O) (bus : AxiLiteBus I O)
    (pace : AxiLitePace := {}) : IO AxiLiteMaster := do
  let role := s!"AxiLiteMaster({bus.name})"
  let src (ch : Channel I O) := IO.ofExcept ((ch.source role).mapError IO.userError)
  let snk (ch : Channel I O) := IO.ofExcept ((ch.sink role).mapError IO.userError)
  let aw ← b.addDriver (← src bus.aw) pace.aw
  let w ← b.addDriver (← src bus.w) pace.w
  let ar ← b.addDriver (← src bus.ar) pace.ar
  let bm ← b.addMonitor (← snk bus.b) pace.b
  let rm ← b.addMonitor (← snk bus.r) pace.r
  return {
    dataBytes := bus.dataBytes
    writeWord := fun addr data strb? => do
      let strb := strb?.getD bus.allStrobes
      if strb != bus.allStrobes && !bus.hasStrb then
        throw (IO.userError s!"{role}: a partial write (strb {hex strb}) needs wstrb, which the design does not have")
      let n := (← bm.received.get).size
      aw.send (bus.awItem addr 0)
      w.send (bus.wItem data strb)
      if !(← b.runUntil (bm.count (n + 1)) s!"{bus.name}: the response to WRITE {hex addr}") then
        throw (IO.userError s!"{role}: no response to WRITE {hex addr}")
      return bus.bRespOf (((← bm.received.get)[n]?).map (·.2) |>.getD #[])
    readWord := fun addr => do
      let n := (← rm.received.get).size
      ar.send (bus.arItem addr 0)
      if !(← b.runUntil (rm.count (n + 1)) s!"{bus.name}: the data of READ {hex addr}") then
        throw (IO.userError s!"{role}: no response to READ {hex addr}")
      let xs := ((← rm.received.get)[n]?).map (·.2) |>.getD #[]
      return (xs.getD 0 0, bus.rRespOf xs) }

namespace AxiLiteMaster

/-- Issue a list of accesses in order (a directed sequence): for a write,
    `addr`, `data` and `strb` are used; for a read, `addr`. -/
def run (m : AxiLiteMaster) (seq : List AxiLiteTxn) : IO Unit := do
  for t in seq do
    if t.write then
      let _ ← m.writeWord t.addr t.data (some t.strb)
    else
      let _ ← m.readWord t.addr

/-- The worse of two responses. -/
private def worse (a b : AxiResp) : AxiResp := if a == .okay then b else a

/-- Write bytes starting at `addr` (any alignment, any length): split into
    bus words with byte enables, as cocotbext-axi's `write` does. -/
def write (m : AxiLiteMaster) (addr : Nat) (bytes : Array UInt8) : IO AxiResp := do
  let n := m.dataBytes
  let mut resp := AxiResp.okay
  let mut k := 0
  while k < bytes.size do
    let a := addr + k
    let base := a / n * n
    let lane := a - base
    let len := min (n - lane) (bytes.size - k)
    let mut data := 0
    let mut strb := 0
    for j in [0:len] do
      data := data ||| ((bytes.getD (k + j) 0).toNat <<< (8 * (lane + j)))
      strb := strb ||| (1 <<< (lane + j))
    resp := worse resp (← m.writeWord base data (some strb))
    k := k + len
  return resp

/-- Read `len` bytes starting at `addr`. -/
def read (m : AxiLiteMaster) (addr len : Nat) : IO (Array UInt8 × AxiResp) := do
  let n := m.dataBytes
  let mut out : Array UInt8 := #[]
  let mut resp := AxiResp.okay
  let mut k := 0
  while k < len do
    let a := addr + k
    let base := a / n * n
    let lane := a - base
    let take := min (n - lane) (len - k)
    let (word, r) ← m.readWord base
    resp := worse resp r
    for j in [0:take] do
      out := out.push ((word >>> (8 * (lane + j))) % 256).toUInt8
    k := k + take
  return (out, resp)

end AxiLiteMaster

/-- Watches all five channels of an AXI4-Lite interface without driving any
    — whichever side the design is on — and publishes one transaction per
    completed access.  A write completes with its B transfer, a read with
    its R transfer; address and data are matched in order.  A response with
    nothing to answer is reported. -/
def AxiLiteMonitor.new {S I O : Type} [Sim S I O] (b : Bench S I O) (bus : AxiLiteBus I O) :
    IO (AnalysisPort AxiLiteTxn) := do
  let ap ← AnalysisPort.new
  let awq : IO.Ref (Array Nat) ← IO.mkRef #[]
  let wq : IO.Ref (Array (Nat × Nat)) ← IO.mkRef #[]
  let arq : IO.Ref (Array Nat) ← IO.mkRef #[]
  let named (ch : Channel I O) : Channel I O := { ch with name := s!"{ch.name} (monitor)" }
  b.addChannelMonitor (named bus.aw) fun _ xs => awq.modify (·.push (xs.getD 0 0))
  b.addChannelMonitor (named bus.w) fun _ xs => wq.modify (·.push (xs.getD 0 0, bus.wStrbOf xs))
  b.addChannelMonitor (named bus.ar) fun _ xs => arq.modify (·.push (xs.getD 0 0))
  b.addChannelMonitor (named bus.b) fun c xs => do
    match (← awq.get)[0]?, (← wq.get)[0]? with
    | some addr, some (data, strb) =>
      awq.modify (·.eraseIdx! 0)
      wq.modify (·.eraseIdx! 0)
      ap.write c { write := true, addr, data, strb, resp := bus.bRespOf xs }
    | _, _ => b.error s!"cycle {c}: {bus.name}: write response without a completed address and data transfer"
  b.addChannelMonitor (named bus.r) fun c xs => do
    match (← arq.get)[0]? with
    | some addr =>
      arq.modify (·.eraseIdx! 0)
      ap.write c { write := false, addr, data := xs.getD 0 0, strb := bus.allStrobes
                   resp := bus.rRespOf xs }
    | none => b.error s!"cycle {c}: {bus.name}: read data without a read address"
  return ap

/-- A memory behind an AXI4-Lite interface, for a design that is a MASTER
    (cocotbext-axi's `AxiLiteRam`).  Bytes never written read as 0. -/
structure AxiLiteRam where
  mem : IO.Ref (Std.HashMap Nat UInt8)

namespace AxiLiteRam

def new {S I O : Type} [Sim S I O] (b : Bench S I O) (bus : AxiLiteBus I O)
    (pace : AxiLitePace := {}) : IO AxiLiteRam := do
  let role := s!"AxiLiteRam({bus.name})"
  let src (ch : Channel I O) := IO.ofExcept ((ch.source role).mapError IO.userError)
  let snk (ch : Channel I O) := IO.ofExcept ((ch.sink role).mapError IO.userError)
  let mem : IO.Ref (Std.HashMap Nat UInt8) ← IO.mkRef {}
  let awq : IO.Ref (Array Nat) ← IO.mkRef #[]
  let wq : IO.Ref (Array (Nat × Nat)) ← IO.mkRef #[]
  let arq : IO.Ref (Array Nat) ← IO.mkRef #[]
  let _ ← b.addMonitor (← snk bus.aw) pace.aw fun _ xs => awq.modify (·.push (xs.getD 0 0))
  let _ ← b.addMonitor (← snk bus.w) pace.w fun _ xs => wq.modify (·.push (xs.getD 0 0, bus.wStrbOf xs))
  let _ ← b.addMonitor (← snk bus.ar) pace.ar fun _ xs => arq.modify (·.push (xs.getD 0 0))
  let bd ← b.addDriver (← src bus.b) pace.b
  let rd ← b.addDriver (← src bus.r) pace.r
  let n := bus.dataBytes
  -- Registered after the monitors, so it sees this cycle's transfers and
  -- queues the responses for the next one.
  let logic : Agent I O := {
    name := s!"{bus.name} (ram)"
    drive := fun _ i => pure i
    observe := fun _ _ _ => do
      while (← awq.get).size > 0 && (← wq.get).size > 0 do
        let addr := (← awq.get)[0]!
        let (data, strb) := (← wq.get)[0]!
        awq.modify (·.eraseIdx! 0)
        wq.modify (·.eraseIdx! 0)
        let base := addr / n * n
        for j in [0:n] do
          if (strb >>> j) % 2 == 1 then
            mem.modify (·.insert (base + j) ((data >>> (8 * j)) % 256).toUInt8)
        bd.send (bus.bItem .okay)
      while (← arq.get).size > 0 do
        let addr := (← arq.get)[0]!
        arq.modify (·.eraseIdx! 0)
        let base := addr / n * n
        let m ← mem.get
        let word := (List.range n).foldl (fun acc j =>
          acc ||| (((m.getD (base + j) 0).toNat) <<< (8 * j))) 0
        rd.send (bus.rItem word .okay)
      return []
    busy := return false }
  b.agents.modify (·.push logic)
  return { mem }

/-- Preload bytes at `addr`. -/
def load (r : AxiLiteRam) (addr : Nat) (bytes : Array UInt8) : IO Unit :=
  r.mem.modify fun m => (List.range bytes.size).foldl (fun m k => m.insert (addr + k) (bytes.getD k 0)) m

/-- Preload little-endian words of `bytesPerWord` bytes. -/
def loadWords (r : AxiLiteRam) (addr : Nat) (words : List Nat) (bytesPerWord : Nat := 4) : IO Unit :=
  r.mem.modify fun m => Id.run do
    let mut m := m
    let mut a := addr
    for wd in words do
      for j in [0:bytesPerWord] do
        m := m.insert (a + j) ((wd >>> (8 * j)) % 256).toUInt8
      a := a + bytesPerWord
    return m

def readByte (r : AxiLiteRam) (addr : Nat) : IO UInt8 := return (← r.mem.get).getD addr 0

end AxiLiteRam

/-- Scoreboard for a memory-like slave (the UVM User's Guide's UBus example
    checks "the memory operation of the slave" the same way): it subscribes
    to a monitor, remembers every byte written with an OKAY response, and
    checks every byte read back against that.  Bytes never written are
    checked against `unwritten` when given, else not checked.  Returns the
    count of bytes it has checked. -/
def AxiLiteMonitor.memoryScoreboard {S I O : Type} (b : Bench S I O)
    (ap : AnalysisPort AxiLiteTxn) (dataBytes : Nat) (unwritten : Option UInt8 := none) :
    IO (IO.Ref Nat) := do
  let model : IO.Ref (Std.HashMap Nat UInt8) ← IO.mkRef {}
  let checked ← IO.mkRef 0
  ap.subscribe fun c t => do
    let base := t.addr / dataBytes * dataBytes
    if t.resp != .okay then
      b.error s!"cycle {c}: scoreboard: {t}"
    else if t.write then
      for j in [0:dataBytes] do
        if (t.strb >>> j) % 2 == 1 then
          model.modify (·.insert (base + j) ((t.data >>> (8 * j)) % 256).toUInt8)
    else
      for j in [0:dataBytes] do
        let got := ((t.data >>> (8 * j)) % 256).toUInt8
        let want? := match (← model.get)[base + j]? with
          | some v => some v
          | none => unwritten
        if let some want := want? then
          checked.modify (· + 1)
          if got != want then
            b.error s!"cycle {c}: scoreboard: {t}: byte at {hex (base + j)} is {hex got.toNat}, expected {hex want.toNat}"
  return checked

end Sparkle.Verification.Tlm
