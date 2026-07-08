/-
  IP.Net.MemcachedHW — BRAM-backed KV store as Signal-DSL.

  Implements the pure-data semantics of
  `Sparkle.IP.Net.Memcached.applyCommand` for the four
  commands `get / set / add / del`, using three BRAMs:

      validMem : 16 × 1-bit   (present flag per slot)
      keyMem   : 16 × 64-bit  (8-byte key per slot, MSB-aligned)
      valueMem : 16 × 128-bit (16-byte value per slot, MSB-aligned)

  The HW exposes a one-cycle "command-in" + multi-cycle
  "reply-out" interface.  The lookup is sequential over all 16
  slots (one slot per cycle).  At the demanded baud rates we
  care about, 16 cycles is negligible.

  Op interface (one-cycle pulse, latched internally):

      opStart  : Bool                — pulse for one cycle
      opCode   : BitVec 2            — 0=get, 1=set, 2=add, 3=del
      opKey    : BitVec 64           — key, MSB-first byte order
                                        (pad with zeros on the LSB side)
      opValue  : BitVec 128          — value (only consumed for set/add)
      opFlags  : BitVec 32           — set/add flags (echoed on get)

  Out (cycle by cycle, valid only when `replyValid`):

      replyKind  : BitVec 3
        0 = STORED
        1 = NOT_STORED
        2 = VALUE   (followed by replyKey/replyValue/replyFlags signals)
        3 = END
        4 = DELETED
        5 = NOT_FOUND
        6 = ERROR
      replyKey/replyValue/replyFlags : valid alongside replyKind=2
      replyValid : Bool              — pulse after lookup completes
      busy       : Bool              — high while op is in progress
-/
import Sparkle
import Sparkle.Core.Lut
import IP.Net.Memcached

namespace Sparkle.IP.Net.MemcachedHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.Memcached (NUM_SLOTS)

/-! ### Output bundle. -/

structure KvHwOut (dom : DomainConfig) where
  /-- Pulse: high for one cycle when a command completes. -/
  replyValid : Signal dom Bool
  /-- Reply category (see module doc). -/
  replyKind  : Signal dom (BitVec 3)
  /-- Recovered key (matches `opKey` if reply is `VALUE`). -/
  replyKey   : Signal dom (BitVec 64)
  /-- Recovered value (valid alongside `VALUE`). -/
  replyValue : Signal dom (BitVec 128)
  /-- Recovered flags (valid alongside `VALUE`). -/
  replyFlags : Signal dom (BitVec 32)
  /-- High while a command is in progress. -/
  busy       : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (KvHwOut dom) dom := ⟨⟩

/-! ### Engine state.

    State register `st : BitVec 3`:
      0 = idle (waiting for opStart)
      1 = lookup (sequentially scan all 16 slots, comparing key)
      2 = decision (we have hit?/idx; figure out which reply
                    to emit)
      3 = emit (one-cycle pulse on replyValid, with the right
                reply fields; for set/add we also do the BRAM
                write here)
      4..7 = unused
-/

@[hardware_module] def kvHw {dom : DomainConfig}
    (opStart : Signal dom Bool)
    (opCode  : Signal dom (BitVec 2))
    (opKey   : Signal dom (BitVec 64))
    (opValue : Signal dom (BitVec 128))
    (opFlags : Signal dom (BitVec 32)) :
    KvHwOut dom :=
  circuit do
    -- Major state.
    let st        ← Signal.reg (0#3)
    -- Sequential lookup index (0..16; 16 = done with miss).
    let scanIdx   ← Signal.reg (0#5)
    -- Hit?  Cached at end of lookup phase.
    let hit       ← Signal.reg false
    -- Slot index of the hit (or where to write on miss).
    let hitIdx    ← Signal.reg (0#4)
    -- Latched op fields so the host can drop opKey/opValue
    -- after the start pulse.
    let opCodeR   ← Signal.reg (0#2)
    let opKeyR    ← Signal.reg (0#64)
    let opValueR  ← Signal.reg (0#128)
    let opFlagsR  ← Signal.reg (0#32)
    -- Next free slot for set/add when key is absent (FIFO).
    let nextSlot  ← Signal.reg (0#4)

    let stSig := (st : Signal dom (BitVec 3))
    let scanSig := (scanIdx : Signal dom (BitVec 5))
    let hitSig := (hit : Signal dom Bool)
    let hitIdxSig := (hitIdx : Signal dom (BitVec 4))
    let codeSig := (opCodeR : Signal dom (BitVec 2))
    let keyR_sig := (opKeyR : Signal dom (BitVec 64))
    let valueR_sig := (opValueR : Signal dom (BitVec 128))
    let flagsR_sig := (opFlagsR : Signal dom (BitVec 32))
    let nextSlotSig := (nextSlot : Signal dom (BitVec 4))

    -- Phase predicates
    let p0_3 := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let p1_3 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let p2_3 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let p3_3 := (Signal.pure 3#3 : Signal dom (BitVec 3))

    let isIdle    := (stSig === p0_3 : Signal dom Bool)
    let isLookup  := (stSig === p1_3 : Signal dom Bool)
    let isDecide  := (stSig === p2_3 : Signal dom Bool)
    let isEmit    := (stSig === p3_3 : Signal dom Bool)

    -- Scan index helpers
    let p0_5 := (Signal.pure 0#5 : Signal dom (BitVec 5))
    let p16_5 := (Signal.pure 16#5 : Signal dom (BitVec 5))
    let p1_5 := (Signal.pure 1#5 : Signal dom (BitVec 5))
    let scanDone := (scanSig === p16_5 : Signal dom Bool)
    let scanInc := (scanSig + p1_5 : Signal dom (BitVec 5))

    -- BRAM read address = current scan index (truncated to 4 bits).
    -- Read happens with 1-cycle latency: at cycle T set readAddr=N,
    -- at cycle T+1 readData = mem[N].  We exploit that by sampling
    -- the BRAM output AFTER advancing scanIdx, so each cycle reads
    -- slot scanIdx-1 (after the first warm-up cycle).
    let scanIdx4 := Signal.map (BitVec.extractLsb' 0 4 ·) scanSig
    -- Write path: in EMIT state, for set/add we write to hitIdx
    -- (if hit) or nextSlot (if miss).  Write happens for ONE
    -- cycle inside EMIT.
    let opIsSet := (codeSig === (Signal.pure 1#2 : Signal dom (BitVec 2)) : Signal dom Bool)
    let opIsAdd := (codeSig === (Signal.pure 2#2 : Signal dom (BitVec 2)) : Signal dom Bool)
    let opIsDel := (codeSig === (Signal.pure 3#2 : Signal dom (BitVec 2)) : Signal dom Bool)
    let opIsGet := (codeSig === (Signal.pure 0#2 : Signal dom (BitVec 2)) : Signal dom Bool)

    -- "set/add will write": set always writes; add writes only if !hit.
    let addWillWrite := ((· && ·) <$> opIsAdd <*>
      ((fun b => !b) <$> hitSig : Signal dom Bool) : Signal dom Bool)
    let willWrite := (opIsSet ||| addWillWrite : Signal dom Bool)
    -- "del will clear": del writes valid=0 when hit.
    let delWillClear := (opIsDel &&& hitSig : Signal dom Bool)
    -- Combined: in EMIT we touch validMem if willWrite or delWillClear,
    -- with new valid = willWrite (clear-on-del, set-on-write).
    let validWE := ((· && ·) <$> isEmit <*>
      ((willWrite ||| delWillClear : Signal dom Bool))
      : Signal dom Bool)
    let validData := Signal.mux willWrite (Signal.pure 1#1 : Signal dom (BitVec 1))
                                          (Signal.pure 0#1 : Signal dom (BitVec 1))

    -- Write slot for set/add: hitIdx if hit, else nextSlot.
    let writeSlot := Signal.mux hitSig hitIdxSig nextSlotSig

    -- Write address (for ALL memories):
    --   validMem / keyMem / valueMem: in EMIT, use writeSlot;
    --   else use scan-time addressing (writes are gated by *WE,
    --   so the address only matters when writing).
    -- Read address during LOOKUP: scanIdx4.  Otherwise hitIdx
    -- (for re-fetching the data needed in EMIT).
    let readAddrLookup := scanIdx4
    -- After lookup ends, switch readAddr to hitIdx so EMIT sees
    -- the right data.  Simplification: feed readAddr = scanIdx4
    -- during LOOKUP, and = hitIdx in all other states.
    let readAddr := Signal.mux isLookup readAddrLookup hitIdxSig

    -- 1-bit "valid" BRAM
    let validRead := Signal.memory (addrWidth := 4) (dataWidth := 1)
      writeSlot validData validWE readAddr
    -- 64-bit key BRAM (data = opKeyR, write gate = willWrite in EMIT)
    let keyWE := (isEmit &&& willWrite : Signal dom Bool)
    let keyRead := Signal.memory (addrWidth := 4) (dataWidth := 64)
      writeSlot keyR_sig keyWE readAddr
    -- 128-bit value BRAM
    let valueRead := Signal.memory (addrWidth := 4) (dataWidth := 128)
      writeSlot valueR_sig keyWE readAddr
    -- For flags we keep one register-array: small enough to use
    -- another BRAM but a 32-bit × 16-entry memory works the same.
    let flagsRead := Signal.memory (addrWidth := 4) (dataWidth := 32)
      writeSlot flagsR_sig keyWE readAddr

    -- Compare current BRAM read against opKeyR.  BRAM has 1-cycle
    -- latency: cycle N sets readAddr=N, cycle N+1 we see slot N.
    -- We compare during LOOKUP whenever scanIdx >= 1.
    let keyEqOpKey := (keyRead === keyR_sig : Signal dom Bool)
    let validBitTrue := ((· == ·) <$> validRead
                          <*> (Signal.pure 1#1 : Signal dom (BitVec 1))
                          : Signal dom Bool)
    let slotMatches := (validBitTrue &&& keyEqOpKey : Signal dom Bool)

    -- "Slot we just compared" = scanIdx - 1.  In LOOKUP we increment
    -- scanIdx, and on the cycle AFTER scanIdx becomes K, the BRAM
    -- output reflects slot K-1.  We capture hitIdx = scanIdx - 1.
    let scanMinus1 := (scanSig - p1_5 : Signal dom (BitVec 5))
    let scanMinus1_4 := Signal.map (BitVec.extractLsb' 0 4 ·) scanMinus1

    -- "Are we examining a real slot this cycle?"
    --   true iff isLookup AND scanIdx ≥ 1 AND scanIdx ≤ 16.  We
    -- have scanDone (= 16) as the stop signal.  Within [1..16]
    -- both bounds hold; scanIdx == 0 only happens on the entry
    -- cycle.
    let inScanCmp := ((· && ·) <$> isLookup <*>
      ((fun b => !b) <$> ((scanSig === p0_5 : Signal dom Bool))
       : Signal dom Bool) : Signal dom Bool)
    let foundThisCycle := (inScanCmp &&& slotMatches : Signal dom Bool)

    -- State next
    let stNextFromIdle := Signal.mux opStart p1_3 stSig
    let stNextFromLookup :=
      Signal.mux foundThisCycle p2_3            -- hit → DECIDE
        (Signal.mux scanDone p2_3 stSig)        -- exhausted → DECIDE (miss)
    let stNextFromDecide := p3_3
    let stNextFromEmit := p0_3
    let stNext :=
      Signal.mux isIdle stNextFromIdle
        (Signal.mux isLookup stNextFromLookup
          (Signal.mux isDecide stNextFromDecide
            (Signal.mux isEmit stNextFromEmit stSig)))

    -- scanIdx next
    let scanNextLookup :=
      Signal.mux foundThisCycle scanSig
        (Signal.mux scanDone p0_5 scanInc)
    let scanNext :=
      Signal.mux opStart p0_5
        (Signal.mux isLookup scanNextLookup
          (Signal.mux isEmit p0_5 scanSig))

    -- hit / hitIdx next
    let hitNext :=
      Signal.mux opStart (Signal.pure false)
        (Signal.mux foundThisCycle (Signal.pure true) hitSig)
    let hitIdxNext :=
      Signal.mux opStart (Signal.pure 0#4)
        (Signal.mux foundThisCycle scanMinus1_4 hitIdxSig)

    -- Latch op fields on start.
    let opCodeNext := Signal.mux opStart opCode codeSig
    let opKeyNext := Signal.mux opStart opKey keyR_sig
    let opValueNext := Signal.mux opStart opValue valueR_sig
    let opFlagsNext := Signal.mux opStart opFlags flagsR_sig

    -- Bump nextSlot on a successful set/add miss (= when we just
    -- consumed a fresh slot).
    let bumpNext := ((· && ·) <$> isEmit <*>
      (((· && ·) <$> willWrite <*>
        ((fun b => !b) <$> hitSig : Signal dom Bool) : Signal dom Bool))
      : Signal dom Bool)
    let p1_4 := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let nextSlotInc := (nextSlotSig + p1_4 : Signal dom (BitVec 4))
    let nextSlotNext := Signal.mux bumpNext nextSlotInc nextSlotSig

    st <~ stNext
    scanIdx <~ scanNext
    hit <~ hitNext
    hitIdx <~ hitIdxNext
    opCodeR <~ opCodeNext
    opKeyR <~ opKeyNext
    opValueR <~ opValueNext
    opFlagsR <~ opFlagsNext
    nextSlot <~ nextSlotNext

    -- Outputs
    let replyValid := isEmit
    let busy := ((fun b => !b) <$> isIdle : Signal dom Bool)

    -- Reply kind decoder (only meaningful when replyValid):
    --   get + hit  → 2 (VALUE)   ─ next cycle host expects END
    --                                separately, but we emit VALUE
    --                                only here; the FSM consumer
    --                                concatenates END\r\n.
    --   get + miss → 3 (END)
    --   set        → 0 (STORED)
    --   add + miss → 0 (STORED)
    --   add + hit  → 1 (NOT_STORED)
    --   del + hit  → 4 (DELETED)
    --   del + miss → 5 (NOT_FOUND)
    --   err        → 6
    let pKind_STORED   := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let pKind_NOTSTORED:= (Signal.pure 1#3 : Signal dom (BitVec 3))
    let pKind_VALUE    := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let pKind_END      := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let pKind_DELETED  := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let pKind_NOTFOUND := (Signal.pure 5#3 : Signal dom (BitVec 3))

    let getKind := Signal.mux hitSig pKind_VALUE pKind_END
    let setKind := pKind_STORED
    let addKind := Signal.mux hitSig pKind_NOTSTORED pKind_STORED
    let delKind := Signal.mux hitSig pKind_DELETED pKind_NOTFOUND

    let replyKind :=
      Signal.mux opIsGet getKind
        (Signal.mux opIsSet setKind
          (Signal.mux opIsAdd addKind
            (Signal.mux opIsDel delKind (Signal.pure 6#3 : Signal dom (BitVec 3)))))

    -- For VALUE: replyKey/replyValue/replyFlags come from the
    -- most recent BRAM read.  Since readAddr = hitIdx during
    -- DECIDE→EMIT, the data is settled at EMIT.
    return ({ replyValid := replyValid
            , replyKind := replyKind
            , replyKey := keyRead
            , replyValue := valueRead
            , replyFlags := flagsRead
            , busy := busy } : KvHwOut dom)

end Sparkle.IP.Net.MemcachedHW
