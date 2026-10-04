/-
  IP.Net.HFTQuote — an Avellaneda–Stoikov quoting engine in Q15.16.

  The market-making core of Chapter 14: given the mid price and the current
  inventory, quote a bid and an ask around the *reservation price*

      r[n]   = mid[n] − k₁·q[n]          -- inventory skew, k₁ = γσ²τ
      bid[n] = r[n] − δ                  -- δ = half-spread
      ask[n] = r[n] + δ
      q[n+1] = clamp_qMax( q[n] + buyFill[n] − sellFill[n] )

  All prices are Q15.16 **ticks** — exchange prices are integer ticks, so
  fixed point is the NATIVE format here, not an approximation compromise.
  Inventory is in Q15.16 lots (fills move it by exactly 1.0).

  Two properties the chapter proves about this datapath:

  * the skew term `−k₁·q` mean-reverts the inventory (the ℝ proof gives
    `|q| ≤ ρⁿ|q₀| + W/(1−ρ)` with fill randomness as a bounded disturbance
    — `proofs/SparkleProofs/Hft/MarketMaking.lean`);
  * independently of ANY model assumption, `clampSym qMax` makes the
    position limit a **wire**: `|q[n]| ≤ qMax` for every n, by construction
    — the same anti-windup-by-clamping argument as the PID integrator
    (`IP/Control/PID.lean`).

  Mirrors the PID file's structure: a pure-data reference (`quoteStep` /
  `runQuote`) next to the synthesizable circuit, so the sim test compares
  the two cycle-by-cycle.
-/
import Sparkle
import IP.Control.FixedPoint

namespace Sparkle.IP.Net.HFTQuote

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPoint

/-! ### Parameters (Q15.16 ticks / lots) -/

/-- Quoting parameters.  `k1` is the inventory-skew gain γσ²τ in ticks per
    lot; `halfSpread` is δ; `qMax` the hard position limit in lots. -/
structure QuoteParams where
  k1         : BitVec 32
  halfSpread : BitVec 32
  qMax       : BitVec 32

/-- Worked-example numbers: skew 0.5 tick/lot, half-spread 1.25 ticks,
    limit ±8 lots. -/
def defaultParams : QuoteParams :=
  { k1         := BitVec.ofNat 32 32768        -- 0.5
  , halfSpread := BitVec.ofNat 32 81920        -- 1.25
  , qMax       := BitVec.ofNat 32 (8 * 65536) }

/-! ### Pure-data reference -/

/-- One quoting cycle: quotes are combinational from the CURRENT inventory;
    the inventory then absorbs this cycle's fills, clamped to ±qMax. -/
def quoteStep (p : QuoteParams) (q mid : BitVec 32)
    (buyFill sellFill : Bool) : BitVec 32 × BitVec 32 × BitVec 32 :=
  let r    := mid - mulQ p.k1 q
  let bid  := r - p.halfSpread
  let ask  := r + p.halfSpread
  let dq   := (if buyFill then one else 0#32) - (if sellFill then one else 0#32)
  let q'   := clampSym p.qMax (q + dq)
  (q', bid, ask)

/-- Reference trajectory over a scripted tape of (mid, buyFill, sellFill).
    Emits (inventory-during-cycle, bid, ask) per cycle. -/
def runQuote (p : QuoteParams) : BitVec 32 →
    List (BitVec 32 × Bool × Bool) → List (BitVec 32 × BitVec 32 × BitVec 32)
  | _, [] => []
  | q, (mid, b, s) :: rest =>
    let (q', bid, ask) := quoteStep p q mid b s
    (q, bid, ask) :: runQuote p q' rest

/-! ### Synthesizable circuit -/

/-- Named outputs of the quoting engine. -/
structure QuoteOut (dom : DomainConfig) where
  bid : Signal dom (BitVec 32)
  ask : Signal dom (BitVec 32)
  inv : Signal dom (BitVec 32)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (QuoteOut dom) dom := ⟨⟩

/-- The quoting engine.  Parameters are passed as plain `BitVec` constants
    (they lower to literals in the datapath).  `clampSymC qMax` is the
    position limit in silicon. -/
def quoteEngine {dom : DomainConfig}
    (k1 halfSpread qMax : BitVec 32)
    (mid : Signal dom (BitVec 32))
    (buyFill sellFill : Signal dom Bool) : QuoteOut dom :=
  circuit do
    let q ← Signal.reg (0#32)
    let qS := (q : Signal dom (BitVec 32))
    let buyInc  := Signal.mux buyFill  (Signal.pure one) (Signal.pure (0#32))
    let sellDec := Signal.mux sellFill (Signal.pure one) (Signal.pure (0#32))
    q <~ clampSymC qMax (qS + buyInc - sellDec)
    let r := mid - mulQSig (Signal.pure k1) qS
    return ({ bid := r - halfSpread
            , ask := r + halfSpread
            , inv := qS } : QuoteOut dom)

/-! ### Single-output wrappers (synthesis entry points)

    A record-returning TOP module doesn't synthesize directly (the
    bundled-tuple limitation, CLAUDE.md); each wrapper realises one scalar
    output, exactly like `msvrByte`/`msvrValid` in the memcached IP. -/

def quoteBid {dom : DomainConfig} (mid : Signal dom (BitVec 32))
    (buyFill sellFill : Signal dom Bool) : Signal dom (BitVec 32) :=
  (quoteEngine defaultParams.k1 defaultParams.halfSpread defaultParams.qMax
    mid buyFill sellFill).bid

def quoteAsk {dom : DomainConfig} (mid : Signal dom (BitVec 32))
    (buyFill sellFill : Signal dom Bool) : Signal dom (BitVec 32) :=
  (quoteEngine defaultParams.k1 defaultParams.halfSpread defaultParams.qMax
    mid buyFill sellFill).ask

def quoteInv {dom : DomainConfig} (mid : Signal dom (BitVec 32))
    (buyFill sellFill : Signal dom Bool) : Signal dom (BitVec 32) :=
  (quoteEngine defaultParams.k1 defaultParams.halfSpread defaultParams.qMax
    mid buyFill sellFill).inv

end Sparkle.IP.Net.HFTQuote
