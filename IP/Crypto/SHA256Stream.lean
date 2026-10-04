/-
  IP.Crypto.SHA256Stream — multi-block SHA-256 streaming wrapper
  around `SHA256.sha256Block`.

  `sha256Block` compresses a single 512-bit block and carries its
  H-state (H0..H7) across successive `start` pulses (reloading a..h
  from H0..H7 on start, accumulating into H0..H7 at finish; H0..H7
  hold initH from domain reset).  So a variable-length hash is just
  a loop that pulses `start` once per already-padded 512-bit block
  and reads `hash` after the last block completes.

  FIDO2 hashes `authenticatorData(37) ‖ clientDataHash(32) = 69 B`,
  which pads to two 512-bit blocks.  The caller supplies the
  already-padded blocks (padding is a fixed combinational function
  of the message length, assembled at the call site) and `nBlocks`.

  Cycle schedule (per block):
    * pulse `blk.start` with the current block,
    * `sha256Block` runs 64 rounds, pulses `done` at its cycle 65,
    * on `done`, either advance to the next block's `start` (if any)
      or assert this module's `done` with the final `hash`.

  Supports up to 2 blocks (enough for the FIDO2 message); the
  interface takes `blk0`/`blk1` and `nBlocks ∈ {1, 2}`.
-/
import Sparkle
import IP.Crypto.SHA256

namespace Sparkle.IP.Crypto.SHA256Stream

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA256 (sha256Block SHA256Out)

/-- Output record. -/
structure StreamOut (dom : DomainConfig) where
  /-- 256-bit digest (H0 in MSB), valid at `done`. -/
  hash : Signal dom (BitVec 256)
  /-- Pulses one cycle when the whole message hash finishes. -/
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (StreamOut dom) dom := ⟨⟩

/-- `@[hardware_module]` wrapper so the streaming FSM can project
    the single-block core's `.hash` / `.done`. -/
@[hardware_module] def wBlock {dom : DomainConfig}
    (start : Signal dom Bool) (blockIn : Signal dom (BitVec 512))
    (first : Signal dom Bool) :
    SHA256Out dom :=
  sha256Block start blockIn first

/-- Multi-block SHA-256 streaming FSM (≤ 2 padded blocks). -/
def sha256StreamHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (nBlocks : Signal dom (BitVec 2))
    (blk0 blk1 : Signal dom (BitVec 512)) :
    StreamOut dom :=
  circuit do
    -- Block index (0 or 1), latched block count, done strobe.
    let blkR   ← Signal.reg (0#2)
    let nBlkR  ← Signal.reg (0#2)
    let doneR  ← Signal.reg false
    -- Delay of the single-block `done` (so we launch the next block
    -- one cycle after the previous finishes, reading only registered
    -- state).
    let blkDoneP ← Signal.reg false

    let blkSig  := (blkR  : Signal dom (BitVec 2))
    let nBlkSig := (nBlkR : Signal dom (BitVec 2))

    let p0_2 := (Signal.pure 0#2 : Signal dom (BitVec 2))
    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))

    -- The block currently fed to the compressor: block 0 on the
    -- first pass, block 1 on a continuation.
    let blkNext := (blkSig + p1_2 : Signal dom (BitVec 2))
    let atBlk1 := (blkNext === p1_2 : Signal dom Bool)
    let curBlock := (Signal.mux start blk0 (Signal.mux atBlk1 blk1 blk0)
                      : Signal dom (BitVec 512))

    -- Are there more blocks after the one just finished?
    let moreBlocks := ((BitVec.ult · ·) <$> blkNext <*> nBlkSig : Signal dom Bool)
    -- Launch-next continuation: one cycle after the block done, if
    -- there is a next block.
    let contLaunch := ((blkDoneP : Signal dom Bool) &&& moreBlocks
                      : Signal dom Bool)
    let blkStart := (start ||| contLaunch : Signal dom Bool)

    -- `first` re-inits the H-state to the IV on block 0 of each message, so
    -- the stream can hash multiple independent messages without a hard reset.
    let blk := wBlock blkStart curBlock start

    -- Registers.
    blkR <~ Signal.mux start p0_2 (Signal.mux contLaunch blkNext blkSig)
    nBlkR <~ Signal.mux start nBlocks nBlkSig
    blkDoneP <~ blk.done
    -- Overall done: the block that just finished (blkDoneP) was the
    -- LAST (no more blocks).
    let noMore := (~~~moreBlocks : Signal dom Bool)
    let finish := ((blkDoneP : Signal dom Bool) &&& noMore : Signal dom Bool)
    doneR <~ finish

    return ({ hash := blk.hash
            , done := (doneR : Signal dom Bool)
            } : StreamOut dom)

end Sparkle.IP.Crypto.SHA256Stream
