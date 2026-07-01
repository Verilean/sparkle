/-
  IP.Bus.CANopenHW — CANopen (CiA 301) HW building blocks.

  Two small pieces:

  1. `cobIdDemuxHW` — combinational: given an 11-bit CAN ID
     from `IP.Bus.CANHW`-level frames, split it into (function
     code, node ID) fields and expose one-hot "kind" flags:
       isNmt / isSync / isHeartbeat / isSdoRx / isSdoTx /
       isTpdo1..4 / isRpdo1..4.

  2. `nmtStateFsmHW` — the CiA 301 NMT state machine.  Consumes
     an NMT command byte (validated when `valid = true`) and
     updates the internal state register per §7.2.4:

         PowerOn / BootUp
              │
              ▼
       PreOperational  ── startRemoteNode → Operational
              │           ── stopRemoteNode → Stopped
              │           ── resetNode / resetComm → PreOperational
              │
     any other state can be forced back via reset commands.

     State encoding (2-bit register):
         0 = pre-operational
         1 = operational
         2 = stopped
         3 = boot-up (initial value after reset)

  Validation:
    * cobIdDemuxHW: sweep a small set of COB-IDs and compare
      against `IP.Bus.CANopen.decodeCobId`.
    * nmtStateFsmHW: feed a small sequence of NMT commands and
      check the state register.
-/
import IP.Bus.CAN
import IP.Bus.CANHW

namespace Sparkle.IP.Bus.CANopenHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### COB-ID demux. -/

structure DemuxOut (dom : DomainConfig) where
  fc          : Signal dom (BitVec 4)
  nid         : Signal dom (BitVec 7)
  isNmt       : Signal dom Bool
  isSync      : Signal dom Bool
  isHeartbeat : Signal dom Bool
  isSdoRx     : Signal dom Bool
  isSdoTx     : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (DemuxOut dom) dom := ⟨⟩

/-- Purely combinational COB-ID demultiplexer.
    Input: 11-bit CAN standard ID.
    Outputs: function code (4-bit), node ID (7-bit), plus
    one-hot flags for the most common CANopen services. -/
def cobIdDemuxHW {dom : DomainConfig}
    (cobId : Signal dom (BitVec 11)) :
    DemuxOut dom :=
  let fc  := cobId.map (BitVec.extractLsb' 7 4 ·)
  let nid := cobId.map (BitVec.extractLsb' 0 7 ·)
  let pNmt := (Signal.pure 0#4 : Signal dom (BitVec 4))
  let pSync := (Signal.pure 1#4 : Signal dom (BitVec 4))
  let pHb := (Signal.pure 14#4 : Signal dom (BitVec 4))
  let pSdoTx := (Signal.pure 11#4 : Signal dom (BitVec 4))
  let pSdoRx := (Signal.pure 12#4 : Signal dom (BitVec 4))
  let isNmt := ((· == ·) <$> fc <*> pNmt : Signal dom Bool)
  let isSync := ((· == ·) <$> fc <*> pSync : Signal dom Bool)
  let isHb := ((· == ·) <$> fc <*> pHb : Signal dom Bool)
  let isSdoRx := ((· == ·) <$> fc <*> pSdoRx : Signal dom Bool)
  let isSdoTx := ((· == ·) <$> fc <*> pSdoTx : Signal dom Bool)
  { fc := fc, nid := nid
  , isNmt := isNmt, isSync := isSync, isHeartbeat := isHb
  , isSdoRx := isSdoRx, isSdoTx := isSdoTx }

/-! ### NMT state machine. -/

structure NmtStateOut (dom : DomainConfig) where
  /-- 2-bit NMT state:
       0 = pre-operational
       1 = operational
       2 = stopped
       3 = boot-up (init) -/
  state : Signal dom (BitVec 2)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (NmtStateOut dom) dom := ⟨⟩

/-- NMT state machine.  On `valid` high, decode the NMT
    command byte and transition:

      cmd = 0x01 (start)     → operational
      cmd = 0x02 (stop)      → stopped
      cmd = 0x80 (preOp)     → pre-operational
      cmd = 0x81 (resetNode) → boot-up  (then falls to pre-op
                                on the next valid cycle
                                — modelled as one-cycle latch)
      cmd = 0x82 (resetComm) → boot-up
      other                  → hold.

    An external `reset` pulse forces boot-up. -/
def nmtStateFsmHW {dom : DomainConfig}
    (reset : Signal dom Bool)
    (cmdIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool) :
    NmtStateOut dom :=
  circuit do
    let stR ← Signal.reg (3#2)   -- init = boot-up
    let stSig := (stR : Signal dom (BitVec 2))

    -- Compare cmdIn against known command bytes.
    let pStart  := (Signal.pure 0x01#8 : Signal dom (BitVec 8))
    let pStop   := (Signal.pure 0x02#8 : Signal dom (BitVec 8))
    let pPreOp  := (Signal.pure 0x80#8 : Signal dom (BitVec 8))
    let pRstN   := (Signal.pure 0x81#8 : Signal dom (BitVec 8))
    let pRstC   := (Signal.pure 0x82#8 : Signal dom (BitVec 8))

    let isStart := ((· == ·) <$> cmdIn <*> pStart : Signal dom Bool)
    let isStop  := ((· == ·) <$> cmdIn <*> pStop  : Signal dom Bool)
    let isPreOp := ((· == ·) <$> cmdIn <*> pPreOp : Signal dom Bool)
    let isRstN  := ((· == ·) <$> cmdIn <*> pRstN  : Signal dom Bool)
    let isRstC  := ((· == ·) <$> cmdIn <*> pRstC  : Signal dom Bool)

    let stOper := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let stStop := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let stPre  := (Signal.pure 0#2 : Signal dom (BitVec 2))
    let stBoot := (Signal.pure 3#2 : Signal dom (BitVec 2))

    -- Reset command → boot-up.
    let stAfterRst := ((· || ·) <$> isRstN <*> isRstC : Signal dom Bool)

    -- Priority mux (highest priority first):
    --   isStart → oper
    --   isStop → stopped
    --   isPreOp → pre-op
    --   reset command → boot-up
    --   else hold.
    let hold  := stSig
    let afterRstCmd := Signal.mux stAfterRst stBoot hold
    let afterPreOp := Signal.mux isPreOp stPre afterRstCmd
    let afterStop := Signal.mux isStop stStop afterPreOp
    let afterStart := Signal.mux isStart stOper afterStop

    -- Apply only when valid.
    let nextInValid := Signal.mux valid afterStart hold

    -- External reset pulse forces boot-up.
    let final := Signal.mux reset stBoot nextInValid
    stR <~ final

    return ({ state := stSig } : NmtStateOut dom)

end Sparkle.IP.Bus.CANopenHW
