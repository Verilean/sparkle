/-
  IP.Bus.PCIeHFT — PCIe → HFT-strategy loopback.

  The minimal "host → board" demo:
    1. Host CPU writes 1 to BAR0 + 0 (any value to trigger).
    2. PCIe MMIO endpoint receives the MemWr, pulses
       `writePulse` for one cycle.
    3. The pulse is gated to BAR offset 0 (= reg0 selector)
       and fed into the HTTP GET emitter as `trigger`.
    4. The board emits the 18-byte
       `GET / HTTP/1.0\r\n\r\n` packet on its outbound
       byte stream.

  Wire-level pipeline:
    host writes BAR0+0    → cycle K   : MemWr arrives
                          → cycle K+1 : writePulse goes high
                          → cycle K+2 : HTTP emit starts
                          → cycle K+19: last HTTP byte

  Note: in a real production board the bound side would be
  TCP/IP framing + an MAC PHY, not a raw HTTP byte stream.
  This demo wires HTTP directly to keep the demo's
  cycle-accurate latency-budget story compact.

  Real board: TCP segment + IP header + Ethernet would add
  ~10 µs and ~50+ bytes of headers; for the demo we go
  straight from PCIe → HTTP.

  No new HW primitives — just glue.  This file is intended
  to land as a single `def hftPcieLoop` that downstream
  tests / iverilog fixtures can drive.
-/

import IP.Bus.PCIe
import IP.Net.HTTP

namespace Sparkle.IP.Bus.PCIeHFT

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.PCIe (mmioEndpoint MMIOEndpoint)
open Sparkle.IP.Net.HTTP (httpGetEmitter HttpEmitOut)

structure HFTPcieOut (dom : DomainConfig) where
  /-- Host-visible register file. -/
  reg0 : Signal dom (BitVec 32)
  /-- Outbound HTTP byte (the "order packet"). -/
  outByte  : Signal dom (BitVec 8)
  outValid : Signal dom Bool
  outLast  : Signal dom Bool
  /-- The writePulse that fired the emit — exposed for
      cycle-accurate latency measurement. -/
  writePulse : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (HFTPcieOut dom) dom := ⟨⟩

/-- The PCIe → HFT loopback. -/
def hftPcieLoop {dom : DomainConfig}
    (rxByte : Signal dom (BitVec 8))
    (rxValid sopTlp : Signal dom Bool)
    (dataDword : Signal dom (BitVec 32))
    (cplId : Signal dom (BitVec 16)) :
    HFTPcieOut dom :=
  let ep := mmioEndpoint rxByte rxValid sopTlp dataDword cplId
  let emit := httpGetEmitter ep.writePulse
  { reg0 := ep.reg0
  , outByte := emit.byte
  , outValid := emit.valid
  , outLast := emit.last
  , writePulse := ep.writePulse }

end Sparkle.IP.Bus.PCIeHFT
