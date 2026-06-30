/-
  IP.Bus.PCIe — minimal PCIe TLP header emitter / parser.

  Scope (read this BEFORE making external claims):
    * Transaction Layer Packets (TLPs) only — Memory Read
      and Memory Write requests with 32-bit addresses
      (3 DWORD header).  Length is always 1 DWORD (4 bytes
      of data per packet).
    * NO physical / link layer: no 8b/10b serdes, no DLLP,
      no sequence numbers / ACK / NAK, no retry buffer.
    * NO ECRC field (the optional digest at the end of a
      TLP).
    * NO ordering rules, no IDO, no traffic-class
      separation.
    * 32-bit addresses only — the 4-DWORD-header 64-bit
      address variant is omitted.

  This is the wire-format piece that an FPGA-side PCIe
  endpoint would emit / consume.  A real endpoint needs
  the link layer + serdes underneath; that's what
  vendor-supplied "PCIe Hard IP" macros provide.

  Layout (Memory Read, 3 DWORD header = 12 bytes):
    DWORD 0 (bytes 0-3):
      byte 0: Fmt[2:0] | Type[4:0]
              Fmt = 000 (MRd, 3 DW header, no data)
                  = 010 (MWr, 3 DW header, with data — 1 DWORD)
              Type = 00000 (memory request)
      byte 1: 0
      byte 2: 0 | Length[9:8]
      byte 3: Length[7:0]   (DWORDs of payload; for MMIO = 1)
    DWORD 1 (bytes 4-7):
      bytes 4-5: Requester ID
      byte 6:    Tag
      byte 7:    Last DW BE[3:0] | First DW BE[3:0]
                 (we use 0xFF = all bytes enabled)
    DWORD 2 (bytes 8-11):
      bytes 8-11: 32-bit address (aligned to 4 bytes)

  For a Memory Write the header is followed by 1 DWORD of
  data (bytes 12-15).
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Bus.PCIe

/-- TLP type codes. -/
abbrev tlpFmtMRd : BitVec 8 := 0x00#8   -- Memory Read, 3DW, no data
abbrev tlpFmtMWr : BitVec 8 := 0x40#8   -- Memory Write, 3DW, 1DW data

/-- Byte 0 selector helper.  fmt = 0 → MRd, 1 → MWr.  -/
@[inline] def fmtByte (isWrite : Bool) : BitVec 8 :=
  if isWrite then tlpFmtMWr else tlpFmtMRd

/-! ### Per-byte extractors.  Same pattern as the L2 stack. -/

@[inline] private def byte16 {dom : DomainConfig}
    (v : Signal dom (BitVec 16)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (1 - k) * 8
  v.map (BitVec.extractLsb' lo 8 ·)

@[inline] private def byte32 {dom : DomainConfig}
    (v : Signal dom (BitVec 32)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (3 - k) * 8
  v.map (BitVec.extractLsb' lo 8 ·)

/-! ### TLP header emit — 12-byte byte stream. -/

structure TlpTxOut (dom : DomainConfig) where
  byte  : Signal dom (BitVec 8)
  valid : Signal dom Bool
  last  : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TlpTxOut dom) dom := ⟨⟩

/-- Per-cycle byte selector for the 12-byte TLP header.
    `cntSig` 1..12 = byte offset 0..11.  Fields:
      isWrite : true = MWr, false = MRd
      reqId   : 16-bit requester ID
      tag     : 8-bit tag
      addr    : 32-bit memory address
    Length is always 1 DWORD for this demo.
    BE byte is always 0xFF (all 4 bytes enabled). -/
@[hardware_module] def tlpHeaderByte {dom : DomainConfig}
    (isWrite : Signal dom Bool)
    (reqId   : Signal dom (BitVec 16))
    (tag     : Signal dom (BitVec 8))
    (addr    : Signal dom (BitVec 32))
    (cntSig  : Signal dom (BitVec 4)) :
    Signal dom (BitVec 8) :=
  let b0 := Signal.mux isWrite
              (Signal.pure tlpFmtMWr : Signal dom (BitVec 8))
              (Signal.pure tlpFmtMRd : Signal dom (BitVec 8))
  let b1 := (Signal.pure (0x00#8 : BitVec 8) : Signal dom (BitVec 8))
  let b2 := (Signal.pure (0x00#8 : BitVec 8) : Signal dom (BitVec 8))  -- Length[9:8]=0
  let b3 := (Signal.pure (0x01#8 : BitVec 8) : Signal dom (BitVec 8))  -- Length[7:0]=1
  let b4 := byte16 reqId 0
  let b5 := byte16 reqId 1
  let b6 := tag
  let b7 := (Signal.pure (0xFF#8 : BitVec 8) : Signal dom (BitVec 8))  -- 1st+Last BE all enabled
  let b8  := byte32 addr 0
  let b9  := byte32 addr 1
  let b10 := byte32 addr 2
  let b11 := byte32 addr 3
  let p1  := (Signal.pure 1#4  : Signal dom (BitVec 4))
  let p2  := (Signal.pure 2#4  : Signal dom (BitVec 4))
  let p3  := (Signal.pure 3#4  : Signal dom (BitVec 4))
  let p4  := (Signal.pure 4#4  : Signal dom (BitVec 4))
  let p5  := (Signal.pure 5#4  : Signal dom (BitVec 4))
  let p6  := (Signal.pure 6#4  : Signal dom (BitVec 4))
  let p7  := (Signal.pure 7#4  : Signal dom (BitVec 4))
  let p8  := (Signal.pure 8#4  : Signal dom (BitVec 4))
  let p9  := (Signal.pure 9#4  : Signal dom (BitVec 4))
  let p10 := (Signal.pure 10#4 : Signal dom (BitVec 4))
  let p11 := (Signal.pure 11#4 : Signal dom (BitVec 4))
  let e1  := (· == ·) <$> cntSig <*> p1
  let e2  := (· == ·) <$> cntSig <*> p2
  let e3  := (· == ·) <$> cntSig <*> p3
  let e4  := (· == ·) <$> cntSig <*> p4
  let e5  := (· == ·) <$> cntSig <*> p5
  let e6  := (· == ·) <$> cntSig <*> p6
  let e7  := (· == ·) <$> cntSig <*> p7
  let e8  := (· == ·) <$> cntSig <*> p8
  let e9  := (· == ·) <$> cntSig <*> p9
  let e10 := (· == ·) <$> cntSig <*> p10
  let e11 := (· == ·) <$> cntSig <*> p11
  Signal.mux e1 b0
    (Signal.mux e2 b1
      (Signal.mux e3 b2
        (Signal.mux e4 b3
          (Signal.mux e5 b4
            (Signal.mux e6 b5
              (Signal.mux e7 b6
                (Signal.mux e8 b7
                  (Signal.mux e9 b8
                    (Signal.mux e10 b9
                      (Signal.mux e11 b10 b11))))))))))

/-! ### TLP header parser — extracts fields from a byte stream. -/

structure TlpRxOut (dom : DomainConfig) where
  isWrite : Signal dom Bool
  reqId   : Signal dom (BitVec 16)
  tag     : Signal dom (BitVec 8)
  addr    : Signal dom (BitVec 32)
  /-- One-cycle pulse after the 12th header byte is latched.
      A real parser would also indicate "data DWORD now" for
      MWr; we stop at the header. -/
  done    : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TlpRxOut dom) dom := ⟨⟩

@[inline] private def shiftIn32 {dom : DomainConfig}
    (acc : Signal dom (BitVec 32)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 32) :=
  (acc <<< (8#32 : BitVec 32)) ||| ((0#24 : BitVec 24) ++ b)

@[inline] private def shiftIn16 {dom : DomainConfig}
    (acc : Signal dom (BitVec 16)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 16) :=
  (acc <<< (8#16 : BitVec 16)) ||| ((0#8 : BitVec 8) ++ b)

def tlpRxParser {dom : DomainConfig}
    (byte  : Signal dom (BitVec 8))
    (valid : Signal dom Bool)
    (sopTlp : Signal dom Bool) :
    TlpRxOut dom :=
  circuit do
    let cnt   ← Signal.reg (0#4)
    let fmtR  ← Signal.reg (0#8)
    let reqR  ← Signal.reg (0#16)
    let tagR  ← Signal.reg (0#8)
    let addrR ← Signal.reg (0#32)
    let doneR ← Signal.reg false

    let cntSig := (cnt : Signal dom (BitVec 4))
    let fmtSig := (fmtR : Signal dom (BitVec 8))
    let reqSig := (reqR : Signal dom (BitVec 16))
    let tagSig := (tagR : Signal dom (BitVec 8))
    let addrSig := (addrR : Signal dom (BitVec 32))
    let doneSig := (doneR : Signal dom Bool)

    -- Offset selectors.  sopTlp covers offset 0 (fmt byte).
    let p1  := (Signal.pure 1#4  : Signal dom (BitVec 4))
    let p4  := (Signal.pure 4#4  : Signal dom (BitVec 4))
    let p5  := (Signal.pure 5#4  : Signal dom (BitVec 4))
    let p6  := (Signal.pure 6#4  : Signal dom (BitVec 4))
    let p8  := (Signal.pure 8#4  : Signal dom (BitVec 4))
    let p9  := (Signal.pure 9#4  : Signal dom (BitVec 4))
    let p10 := (Signal.pure 10#4 : Signal dom (BitVec 4))
    let p11 := (Signal.pure 11#4 : Signal dom (BitVec 4))
    let inReq := (((· == ·) <$> cntSig <*> p4) |||
                  ((· == ·) <$> cntSig <*> p5))
    let inTag := (· == ·) <$> cntSig <*> p6
    let inAddr := (((· == ·) <$> cntSig <*> p8) |||
                   ((· == ·) <$> cntSig <*> p9) |||
                   ((· == ·) <$> cntSig <*> p10) |||
                   ((· == ·) <$> cntSig <*> p11))
    let isLast := (· == ·) <$> cntSig <*> p11

    let cntInc := (· + ·) <$> cntSig <*> p1
    cnt   <~ Signal.mux sopTlp p1
              (Signal.mux valid cntInc cntSig)
    fmtR  <~ Signal.mux sopTlp byte fmtSig
    reqR  <~ Signal.mux (valid &&& inReq) (shiftIn16 reqSig byte) reqSig
    tagR  <~ Signal.mux (valid &&& inTag) byte tagSig
    addrR <~ Signal.mux (valid &&& inAddr) (shiftIn32 addrSig byte) addrSig
    doneR <~ valid &&& isLast

    -- isWrite = (fmtByte ≠ MRd).  We check just the top
    -- bit of Fmt (0x40 = MWr).  Bit 6 of byte 0.
    let topBit := fmtSig.map (BitVec.extractLsb' 6 1 ·)
    let isWriteSig := (· == ·) <$> topBit <*> (Signal.pure 1#1 : Signal dom (BitVec 1))

    return ({ isWrite := isWriteSig
            , reqId   := reqSig
            , tag     := tagSig
            , addr    := addrSig
            , done    := doneSig
            } : TlpRxOut dom)

/-! ### Completion TLP — CplD (Completion with Data) emit.

    16-byte total: 12-byte header + 4-byte data payload.
    Used to respond to a Memory Read request.

    Layout:
      DWORD 0:
        byte 0:  0x4A     (Fmt=010 CplD, Type=01010)
        byte 1:  0x00
        byte 2:  0x00      (Length high bits = 0)
        byte 3:  0x01      (Length = 1 DWORD)
      DWORD 1:
        bytes 4-5:  Completer ID
        byte 6:     Status[2:0]|BCM|ByteCount[11:8]
                    = 0x00 for success (Successful Completion),
                      no BCM, byte count high = 0
        byte 7:     ByteCount[7:0] = 4 (1 DWORD = 4 bytes)
      DWORD 2:
        bytes 8-9:  Requester ID (from the request)
        byte 10:    Tag (from the request)
        byte 11:    Lower Address[6:0] (low 7 bits of the
                    request address)
      DWORD 3:
        bytes 12-15: 4-byte data payload (the read value)
-/

abbrev tlpFmtCplD : BitVec 8 := 0x4A#8

/-- Per-cycle byte selector for the 16-byte Completion TLP.
    cnt 1..16 = byte offset 0..15. -/
@[hardware_module] def tlpCplByte {dom : DomainConfig}
    (cplId : Signal dom (BitVec 16))
    (reqId : Signal dom (BitVec 16))
    (tag   : Signal dom (BitVec 8))
    (lowerAddr : Signal dom (BitVec 8))   -- only low 7 bits used
    (data  : Signal dom (BitVec 32))
    (cntSig : Signal dom (BitVec 5)) :
    Signal dom (BitVec 8) :=
  let b0  := (Signal.pure tlpFmtCplD : Signal dom (BitVec 8))
  let b1  := (Signal.pure (0x00#8 : BitVec 8) : Signal dom (BitVec 8))
  let b2  := (Signal.pure (0x00#8 : BitVec 8) : Signal dom (BitVec 8))
  let b3  := (Signal.pure (0x01#8 : BitVec 8) : Signal dom (BitVec 8))
  let b4  := byte16 cplId 0
  let b5  := byte16 cplId 1
  let b6  := (Signal.pure (0x00#8 : BitVec 8) : Signal dom (BitVec 8))  -- Status=0 (success)
  let b7  := (Signal.pure (0x04#8 : BitVec 8) : Signal dom (BitVec 8))  -- ByteCount = 4
  let b8  := byte16 reqId 0
  let b9  := byte16 reqId 1
  let b10 := tag
  let b11 := lowerAddr
  let b12 := byte32 data 0
  let b13 := byte32 data 1
  let b14 := byte32 data 2
  let b15 := byte32 data 3
  let pK (k : Nat) : Signal dom (BitVec 5) :=
    Signal.pure (BitVec.ofNat 5 k)
  let _ := pK   -- silence; inline below
  let p1  := (Signal.pure 1#5  : Signal dom (BitVec 5))
  let p2  := (Signal.pure 2#5  : Signal dom (BitVec 5))
  let p3  := (Signal.pure 3#5  : Signal dom (BitVec 5))
  let p4  := (Signal.pure 4#5  : Signal dom (BitVec 5))
  let p5  := (Signal.pure 5#5  : Signal dom (BitVec 5))
  let p6  := (Signal.pure 6#5  : Signal dom (BitVec 5))
  let p7  := (Signal.pure 7#5  : Signal dom (BitVec 5))
  let p8  := (Signal.pure 8#5  : Signal dom (BitVec 5))
  let p9  := (Signal.pure 9#5  : Signal dom (BitVec 5))
  let p10 := (Signal.pure 10#5 : Signal dom (BitVec 5))
  let p11 := (Signal.pure 11#5 : Signal dom (BitVec 5))
  let p12 := (Signal.pure 12#5 : Signal dom (BitVec 5))
  let p13 := (Signal.pure 13#5 : Signal dom (BitVec 5))
  let p14 := (Signal.pure 14#5 : Signal dom (BitVec 5))
  let p15 := (Signal.pure 15#5 : Signal dom (BitVec 5))
  let e1  := (· == ·) <$> cntSig <*> p1
  let e2  := (· == ·) <$> cntSig <*> p2
  let e3  := (· == ·) <$> cntSig <*> p3
  let e4  := (· == ·) <$> cntSig <*> p4
  let e5  := (· == ·) <$> cntSig <*> p5
  let e6  := (· == ·) <$> cntSig <*> p6
  let e7  := (· == ·) <$> cntSig <*> p7
  let e8  := (· == ·) <$> cntSig <*> p8
  let e9  := (· == ·) <$> cntSig <*> p9
  let e10 := (· == ·) <$> cntSig <*> p10
  let e11 := (· == ·) <$> cntSig <*> p11
  let e12 := (· == ·) <$> cntSig <*> p12
  let e13 := (· == ·) <$> cntSig <*> p13
  let e14 := (· == ·) <$> cntSig <*> p14
  let e15 := (· == ·) <$> cntSig <*> p15
  Signal.mux e1 b0
    (Signal.mux e2 b1
      (Signal.mux e3 b2
        (Signal.mux e4 b3
          (Signal.mux e5 b4
            (Signal.mux e6 b5
              (Signal.mux e7 b6
                (Signal.mux e8 b7
                  (Signal.mux e9 b8
                    (Signal.mux e10 b9
                      (Signal.mux e11 b10
                        (Signal.mux e12 b11
                          (Signal.mux e13 b12
                            (Signal.mux e14 b13
                              (Signal.mux e15 b14 b15))))))))))))))

/-! ### MMIO endpoint — 4-register dispatch.

    Wires the TLP parser into a small register file.  On
    every parser-done pulse:
      * If `isWrite`: latch the data DWORD into the register
        at addr[3:2] (4 regs).  Data DWORD reception is a
        follow-up cycle, so we accept it via a separate
        `dataDword` input (caller threads it).
      * If !isWrite (= MemRead): emit a CplD on the next 16
        cycles, with the addressed register's value as
        data.

    Inputs:
      rxByte / rxValid / sopTlp : 12-byte TLP header stream
      dataDword                : 32-bit data DWORD that
                                 follows a MemWr header
                                 (caller is expected to
                                 hold it valid for one
                                 cycle after `done`)
      cplId                    : our completer ID (fixed)

    Outputs:
      regs[0..3]               : current register file values
      cplByte / cplValid / cplLast : 16-byte completion
                                 stream for MemRd responses
-/

structure MMIOEndpoint (dom : DomainConfig) where
  reg0 : Signal dom (BitVec 32)
  reg1 : Signal dom (BitVec 32)
  reg2 : Signal dom (BitVec 32)
  reg3 : Signal dom (BitVec 32)
  /-- Completion TX stream. -/
  cplByte  : Signal dom (BitVec 8)
  cplValid : Signal dom Bool
  cplLast  : Signal dom Bool
  /-- Pulses for one cycle when a MemWr's data has been
      latched.  Useful for downstream "we received a write"
      handling. -/
  writePulse : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MMIOEndpoint dom) dom := ⟨⟩

def mmioEndpoint {dom : DomainConfig}
    (rxByte : Signal dom (BitVec 8))
    (rxValid sopTlp : Signal dom Bool)
    (dataDword : Signal dom (BitVec 32))
    (cplId : Signal dom (BitVec 16)) :
    MMIOEndpoint dom :=
  let parsed := tlpRxParser rxByte rxValid sopTlp
  circuit do
    -- 4 × 32-bit register file.
    let r0 ← Signal.reg (0#32)
    let r1 ← Signal.reg (0#32)
    let r2 ← Signal.reg (0#32)
    let r3 ← Signal.reg (0#32)
    -- Completion-emit counter (5-bit covers 0..16).
    let cplCnt ← Signal.reg (0#5)
    -- Latched request fields for the completion.
    let reqIdLatch ← Signal.reg (0#16)
    let tagLatch ← Signal.reg (0#8)
    let lowAddrLatch ← Signal.reg (0#8)
    let dataLatch ← Signal.reg (0#32)
    -- writePulse register.
    let wPulseR ← Signal.reg false

    let r0Sig := (r0 : Signal dom (BitVec 32))
    let r1Sig := (r1 : Signal dom (BitVec 32))
    let r2Sig := (r2 : Signal dom (BitVec 32))
    let r3Sig := (r3 : Signal dom (BitVec 32))
    let cplCntSig := (cplCnt : Signal dom (BitVec 5))
    let reqIdSig := (reqIdLatch : Signal dom (BitVec 16))
    let tagSig   := (tagLatch   : Signal dom (BitVec 8))
    let lowAddrSig := (lowAddrLatch : Signal dom (BitVec 8))
    let dataSig := (dataLatch : Signal dom (BitVec 32))

    -- Decode the addressed register from addr[3:2] (low 2
    -- bits of the DWORD-aligned address index).
    let addrIdx := parsed.addr.map (BitVec.extractLsb' 2 2 ·)
    let isR0 := (· == ·) <$> addrIdx <*> (Signal.pure (0#2 : BitVec 2) : Signal dom (BitVec 2))
    let isR1 := (· == ·) <$> addrIdx <*> (Signal.pure (1#2 : BitVec 2) : Signal dom (BitVec 2))
    let isR2 := (· == ·) <$> addrIdx <*> (Signal.pure (2#2 : BitVec 2) : Signal dom (BitVec 2))
    let isR3 := (· == ·) <$> addrIdx <*> (Signal.pure (3#2 : BitVec 2) : Signal dom (BitVec 2))

    -- On parserDone + isWrite, latch the dataDword into the
    -- addressed register.  On parserDone + !isWrite, kick
    -- off the completion emit by loading cplCnt=1.
    let writeFire := parsed.done &&& parsed.isWrite
    let readFire  := parsed.done &&& ((fun b => !b) <$> parsed.isWrite)

    r0 <~ Signal.mux (writeFire &&& isR0) dataDword r0Sig
    r1 <~ Signal.mux (writeFire &&& isR1) dataDword r1Sig
    r2 <~ Signal.mux (writeFire &&& isR2) dataDword r2Sig
    r3 <~ Signal.mux (writeFire &&& isR3) dataDword r3Sig

    -- writePulse: 1 cycle when writeFire occurs.
    wPulseR <~ writeFire

    -- On readFire: latch request info + the addressed
    -- register's value into dataLatch, and start cplCnt.
    -- Selected register value:
    let regSel :=
      Signal.mux isR0 r0Sig
        (Signal.mux isR1 r1Sig
          (Signal.mux isR2 r2Sig r3Sig))
    reqIdLatch <~ Signal.mux readFire parsed.reqId reqIdSig
    tagLatch   <~ Signal.mux readFire parsed.tag   tagSig
    -- Lower address: low 8 bits of addr (we use byte 11 of
    -- the request addr; here just the low byte).
    let lowByte := parsed.addr.map (BitVec.extractLsb' 0 8 ·)
    lowAddrLatch <~ Signal.mux readFire lowByte lowAddrSig
    dataLatch  <~ Signal.mux readFire regSel dataSig

    -- Completion counter: load 1 on readFire, +1 while
    -- emitting (1..16), back to 0 after 16.
    let pZ5  := (Signal.pure 0#5  : Signal dom (BitVec 5))
    let p1_5 := (Signal.pure 1#5  : Signal dom (BitVec 5))
    let p16_5 := (Signal.pure 16#5 : Signal dom (BitVec 5))
    let cplInc := (· + ·) <$> cplCntSig <*> p1_5
    let isCplIdle := (· == ·) <$> cplCntSig <*> pZ5
    let isCplLast := (· == ·) <$> cplCntSig <*> p16_5
    cplCnt <~ Signal.mux readFire p1_5
                (Signal.mux isCplLast pZ5
                  (Signal.mux isCplIdle pZ5 cplInc))

    -- Emit cplByte from the helper.
    let cplByteOut :=
      tlpCplByte cplId reqIdSig tagSig lowAddrSig dataSig cplCntSig
    let cplValidOut := (fun b => !b) <$> isCplIdle

    return ({ reg0 := r0Sig
            , reg1 := r1Sig
            , reg2 := r2Sig
            , reg3 := r3Sig
            , cplByte  := cplByteOut
            , cplValid := cplValidOut
            , cplLast  := isCplLast
            , writePulse := (wPulseR : Signal dom Bool)
            } : MMIOEndpoint dom)

end Sparkle.IP.Bus.PCIe
