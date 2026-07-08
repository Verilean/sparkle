/-
  IP.Net.UsbWebServer — full synthesizable top-level for the
  Tang Nano 50K USB-Web demo.

  Wiring (single `circuit do` so the synth elaborator sees one
  module):

      uart_rx_line ──> uartRxHW ──> slipDeframerHW
                                     │  outByte/outValid
                                     ▼
                                 ipv4RxParser    (sopIp = frame-start register)
                                     │
                                     ▼
                                 tcpRxParser     (sopTcp = ip-done register)
                                     │
                                     ▼
                                 httpRequestParser
                                     │  gotRequest
                                     ▼
                                 TX sequencer (74-cycle FSM)
                                     │  byte/valid/frameEnd
                                     ▼
                                 slipFramerHW ──> uartTxHW ──> uart_tx_line

  Fixed parameters (compile-time):
    src IP  : 192.168.7.2  (FPGA)
    dst IP  : 192.168.7.1  (host)
    src port: 80
    dst port: 12345
    response body: "HTTP/1.0 200 OK\r\n\r\nHello, Sparkle!"

  Clock / baud:
    27 MHz Tang Nano 50K crystal → PLL → 100 MHz design clock
    UART 1 Mbps → bitDiv = 99

  Outputs (the only board-level pins after synth):
    uart_tx_line : Bool
-/
import Sparkle
import Sparkle.Core.Lut
import IP.Net.UART
import IP.Net.SLIP
import IP.Net.IPv4
import IP.Net.TCP
import IP.Net.HTTP

namespace Sparkle.IP.Net.UsbWebServer

open Sparkle.Core
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.UART
open Sparkle.IP.Net.SLIP

/-! ### TX sequencer.

    Drives an 80-cycle FSM that emits, byte by byte, a complete
    response packet: IPv4 header (20) + TCP header (20) + HTTP
    body (34) + 6-cycle slack to let slipFramer emit closing END.

    State numbering:
      0          = idle, waiting for `trigger` pulse
      1..20      = IPv4 header byte 0..19
      21..40     = TCP header byte 0..19
      41..74     = HTTP body byte 0..33
      75         = frameEnd pulse (1 cycle)
      76..79     = slack (let slipFramer finish trailing END)
      → back to 0
-/
structure TxSeqOut (dom : DomainConfig) where
  byte     : Signal dom (BitVec 8)
  valid    : Signal dom Bool
  frameEnd : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TxSeqOut dom) dom := ⟨⟩

/-- Pre-computed response packet bytes (76 = 20+20+34+2-padding).
    All constants here; the synth elaborator turns this into a
    big mux. -/
def respPacketBytes : List (BitVec 8) :=
  let ipHeader : List Nat :=
    [0x45, 0x00,        -- ver/IHL, DSCP
     0x00, 0x4A,        -- total length = 74
     0x00, 0x01,        -- ID
     0x40, 0x00,        -- flags+frag (DF)
     0x40, 0x06,        -- TTL 64, proto TCP
     0x00, 0x00,        -- chksum (host accepts without checking)
     0xC0, 0xA8, 0x07, 0x02,   -- src IP = 192.168.7.2
     0xC0, 0xA8, 0x07, 0x01]   -- dst IP = 192.168.7.1
  let tcpHeader : List Nat :=
    [0x00, 0x50,        -- src port = 80
     0x30, 0x39,        -- dst port = 12345
     0x00, 0x00, 0x00, 0x00,   -- seq num
     0x00, 0x00, 0x00, 0x00,   -- ack num
     0x50, 0x18,        -- data offset 5 + flags PSH+ACK
     0xFF, 0xFF,        -- window
     0x00, 0x00,        -- chksum
     0x00, 0x00]        -- urgent
  let httpBody : List Nat :=
    -- "HTTP/1.0 200 OK\r\n\r\nHello, Sparkle!"
    [0x48, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x30, 0x20, 0x32, 0x30, 0x30,
     0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x0D, 0x0A, 0x48, 0x65, 0x6C, 0x6C, 0x6F,
     0x2C, 0x20, 0x53, 0x70, 0x61, 0x72, 0x6B, 0x6C, 0x65, 0x21]
  (ipHeader ++ tcpHeader ++ httpBody).map (BitVec.ofNat 8 ·)

/-- Build a byte-mux: given a register holding offset 0..73,
    return the corresponding response packet byte via the
    `kLut!` macro (which fully unrolls into 74 nested
    Signal.mux's at elaboration time — synth-elaborator-
    friendly). -/
@[hardware_module] def respByteMux {dom : DomainConfig}
    (offset : Signal dom (BitVec 7)) :
    Signal dom (BitVec 8) :=
  kLut! offset [
    -- IPv4 header (20)
    Signal.pure 0x45#8, Signal.pure 0x00#8, Signal.pure 0x00#8, Signal.pure 0x4A#8,
    Signal.pure 0x00#8, Signal.pure 0x01#8, Signal.pure 0x40#8, Signal.pure 0x00#8,
    Signal.pure 0x40#8, Signal.pure 0x06#8, Signal.pure 0x00#8, Signal.pure 0x00#8,
    Signal.pure 0xC0#8, Signal.pure 0xA8#8, Signal.pure 0x07#8, Signal.pure 0x02#8,
    Signal.pure 0xC0#8, Signal.pure 0xA8#8, Signal.pure 0x07#8, Signal.pure 0x01#8,
    -- TCP header (20)
    Signal.pure 0x00#8, Signal.pure 0x50#8, Signal.pure 0x30#8, Signal.pure 0x39#8,
    Signal.pure 0x00#8, Signal.pure 0x00#8, Signal.pure 0x00#8, Signal.pure 0x00#8,
    Signal.pure 0x00#8, Signal.pure 0x00#8, Signal.pure 0x00#8, Signal.pure 0x00#8,
    Signal.pure 0x50#8, Signal.pure 0x18#8, Signal.pure 0xFF#8, Signal.pure 0xFF#8,
    Signal.pure 0x00#8, Signal.pure 0x00#8, Signal.pure 0x00#8, Signal.pure 0x00#8,
    -- HTTP body: "HTTP/1.0 200 OK\r\n\r\nHello, Sparkle!" (34)
    Signal.pure 0x48#8, Signal.pure 0x54#8, Signal.pure 0x54#8, Signal.pure 0x50#8,
    Signal.pure 0x2F#8, Signal.pure 0x31#8, Signal.pure 0x2E#8, Signal.pure 0x30#8,
    Signal.pure 0x20#8, Signal.pure 0x32#8, Signal.pure 0x30#8, Signal.pure 0x30#8,
    Signal.pure 0x20#8, Signal.pure 0x4F#8, Signal.pure 0x4B#8, Signal.pure 0x0D#8,
    Signal.pure 0x0A#8, Signal.pure 0x0D#8, Signal.pure 0x0A#8, Signal.pure 0x48#8,
    Signal.pure 0x65#8, Signal.pure 0x6C#8, Signal.pure 0x6C#8, Signal.pure 0x6F#8,
    Signal.pure 0x2C#8, Signal.pure 0x20#8, Signal.pure 0x53#8, Signal.pure 0x70#8,
    Signal.pure 0x61#8, Signal.pure 0x72#8, Signal.pure 0x6B#8, Signal.pure 0x6C#8,
    Signal.pure 0x65#8, Signal.pure 0x21#8
  ]

/-- FSM that, on each `trigger` pulse, emits a 74-byte response
    packet across the next 74 cycles with `valid` high, then a
    single `frameEnd` pulse, then idle.

    State layout:
      `running` : Bool   — false = idle, true = actively emitting
      `phase`   : BV 7  — 0..73 = byte offset (valid),
                          74 = frameEnd pulse,
                          75..79 = slack (let slipFramer drain),
                          then `running` falls and FSM goes idle.

    Separating "are we running" from "where in the sequence" lets
    `respByteMux` consume `phase` directly (0..73) without needing
    a state-1-based off-by-one ladder. -/
def txSequencer {dom : DomainConfig}
    (trigger : Signal dom Bool) :
    TxSeqOut dom :=
  circuit do
    let running ← Signal.reg false
    let phase ← Signal.reg (0#7)

    let runSig := (running : Signal dom Bool)
    let phSig := (phase : Signal dom (BitVec 7))

    let p0 := (Signal.pure 0#7 : Signal dom (BitVec 7))
    let p1 := (Signal.pure 1#7 : Signal dom (BitVec 7))
    let p73 := (Signal.pure 73#7 : Signal dom (BitVec 7))
    let p74 := (Signal.pure 74#7 : Signal dom (BitVec 7))
    let p75 := (Signal.pure 75#7 : Signal dom (BitVec 7))
    let p76 := (Signal.pure 76#7 : Signal dom (BitVec 7))
    let p77 := (Signal.pure 77#7 : Signal dom (BitVec 7))
    let p78 := (Signal.pure 78#7 : Signal dom (BitVec 7))
    let p79 := (Signal.pure 79#7 : Signal dom (BitVec 7))

    -- Detect each phase value (we need explicit equality muxes
    -- because the synth elaborator can't translate arithmetic
    -- comparisons).
    let isByteLast := (phSig === p73 : Signal dom Bool)
    let isFrameEnd := (phSig === p74 : Signal dom Bool)
    let is75 := (phSig === p75 : Signal dom Bool)
    let is76 := (phSig === p76 : Signal dom Bool)
    let is77 := (phSig === p77 : Signal dom Bool)
    let is78 := (phSig === p78 : Signal dom Bool)
    let isPhaseEnd := (phSig === p79 : Signal dom Bool)

    -- inSlack = phase ∈ [75..79]
    let inSlack :=
      ((· || ·) <$> is75 <*>
        (((· || ·) <$> is76 <*>
          (((· || ·) <$> is77 <*>
            ((is78 ||| isPhaseEnd : Signal dom Bool))
            : Signal dom Bool))
          : Signal dom Bool))
        : Signal dom Bool)
    -- inBytes = running AND phase ∈ [0..73]
    -- = running AND !isFrameEnd AND !inSlack
    let notFrameEnd := ((fun b => !b) <$> isFrameEnd : Signal dom Bool)
    let notSlack := ((fun b => !b) <$> inSlack : Signal dom Bool)
    let inBodyPhase :=
      (notFrameEnd &&& notSlack : Signal dom Bool)
    let inBytes := (runSig &&& inBodyPhase : Signal dom Bool)

    -- Phase next: when running, increment phase; when at slot 79
    -- (phaseEnd), wrap to 0 and clear running.
    -- When idle (running=false), trigger latches phase=0 and sets running=true.
    let phInc := (phSig + p1 : Signal dom (BitVec 7))
    let phNext :=
      Signal.mux trigger p0
        (Signal.mux runSig
          (Signal.mux isPhaseEnd p0 phInc)
          phSig)
    let runNext :=
      Signal.mux trigger (Signal.pure true)
        (Signal.mux isPhaseEnd (Signal.pure false) runSig)

    phase <~ phNext
    running <~ runNext

    -- Output byte = respByteMux phase  (only meaningful when
    -- inBytes is high; downstream gates on `valid`).
    let byteOut := respByteMux phSig
    -- frameEnd pulse = running AND phase == 74
    let frameEndOut := (runSig &&& isFrameEnd : Signal dom Bool)

    -- Suppress unused warning
    let _useIsByteLast := isByteLast

    return ({ byte := byteOut
            , valid := inBytes
            , frameEnd := frameEndOut } : TxSeqOut dom)

/-! ### SOP pulse generator.

    Hardware-friendly: take a `valid` stream + a `reset` pulse
    (e.g. SLIP `frameDone`), and emit a single-cycle pulse on
    the first `valid` byte after each reset.
-/
def sopPulse {dom : DomainConfig}
    (validIn : Signal dom Bool)
    (reset : Signal dom Bool) :
    Signal dom Bool :=
  circuit do
    -- `armed` register: true when waiting for the next valid.
    -- On reset we set armed=true; on the first valid while
    -- armed we pulse and clear armed.
    let armed ← Signal.reg true
    let armedSig := (armed : Signal dom Bool)
    let pulse := (armedSig &&& validIn : Signal dom Bool)
    -- next armed = (reset OR (armed AND !validIn))
    let stillArmed :=
      ((· && ·) <$> armedSig <*>
        ((fun b => !b) <$> validIn : Signal dom Bool) : Signal dom Bool)
    let armedNext := (reset ||| stillArmed : Signal dom Bool)
    armed <~ armedNext
    return pulse

/-! ### Full top-level. -/

structure WebServerOut (dom : DomainConfig) where
  /-- Serial line driven onto the BL616 TX pin. -/
  uartTx : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (WebServerOut dom) dom := ⟨⟩

/-- One-shot Web server module.  Takes the UART RX line plus a
    bit-divider constant (so the same module compiles for any
    baud / clock), drives the full pipeline, and exposes the
    UART TX line. -/
def usbWebServer {dom : DomainConfig}
    (uartRxLine : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16)) :
    WebServerOut dom :=
  -- All wiring is done OUTSIDE a single `circuit do` block: the
  -- individual sub-IPs are themselves `circuit do` modules, and
  -- Sparkle's elaborator inlines them as needed.
  let rx := uartRxHW uartRxLine bitDiv
  let deframer := slipDeframerHW rx.rxByte rx.rxValid

  let sopIp := sopPulse deframer.outValid deframer.frameDone

  let ipv4 := Sparkle.IP.Net.IPv4.ipv4RxParser
                deframer.outByte deframer.outValid sopIp

  let sopTcp := sopPulse deframer.outValid ipv4.done

  let tcp := Sparkle.IP.Net.TCP.tcpRxParser
               deframer.outByte deframer.outValid sopTcp

  -- HTTP parser sees all deframer bytes; it only fires on
  -- "GET " so it's tolerant of seeing the IP/TCP header
  -- bytes first (they don't match the pattern).
  let http := Sparkle.IP.Net.HTTP.httpRequestParser
                deframer.outByte deframer.outValid

  -- TX side: sequencer driven by gotRequest, then SLIP+UART.
  let txSeq := txSequencer http.gotRequest
  let framer := slipFramerHW txSeq.byte txSeq.valid txSeq.frameEnd
  let tx := uartTxHW framer.txByte framer.txValid bitDiv

  ({ uartTx := tx.txLine } : WebServerOut dom)

end Sparkle.IP.Net.UsbWebServer
