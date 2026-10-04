/-
  Chapter 14, layer 2: transport the quoting equations to Q15.16 and check
  they are what the datapath computes.

  Same construction as `FixedPointTransport.lean` (the PID transport): the ℝ
  definitions live in `SparkleProofs.Hft.MarketMaking` — the SAME definitions
  `inventory_ultimate_bound` is proved about — and `retype_def` derives their
  Q15.16 counterparts.  Nobody types the fixed-point quote formula; it cannot
  drift from the proved one because there is only one copy.

  Then two closures:
    * a general theorem: the transported reservation price sits within ONE
      LSB of the exact value (the single `mulQ` floor is the only error —
      bid/ask add an exact constant on top);
    * fixture cross-checks against `IP.Net.HFTQuote.quoteStep` — the BitVec
      pure-data reference the circuit is sim-tested against — including a
      negative-inventory case, where a truncating (rather than flooring)
      multiply would differ.  Equation → FixQ → BitVec datapath, one chain.
-/
import SparkleProofs.Retype.FixedPointTransport
import SparkleProofs.Hft.MarketMaking
import IP.Net.HFTQuote

namespace SparkleProofs.Retype.HftTransport

open SparkleProofs.Retype.FixedPointTransport
open SparkleProofs.Hft.MarketMaking

/-! ### The transport — derived, not written -/

retype_def resPriceQ := resPrice using Real => FixQ
retype_def bidPriceQ := bidPrice using Real => FixQ
retype_def askPriceQ := askPrice using Real => FixQ

/-! ### One general theorem: the only error is the one floor

`resPriceQ` computes `s − (k₁·q >> 16)` with a flooring shift, so the scaled
result sits in `[exact, exact + 1 lsb)` — the subtraction flips the floor's
downward bias upward, and bid/ask only add exact constants to it. -/

theorem resPriceQ_within_one_lsb (k1 s q : FixQ) :
    0 ≤ FixQ.scale * (resPriceQ k1 s q).n - (FixQ.scale * s.n - k1.n * q.n) ∧
    FixQ.scale * (resPriceQ k1 s q).n - (FixQ.scale * s.n - k1.n * q.n) < FixQ.scale := by
  have hdef : (resPriceQ k1 s q).n = s.n - (k1.n * q.n) / FixQ.scale := rfl
  -- `omega` handles Int `/`/`%` with the literal divisor 65536 directly.
  constructor <;> (rw [hdef]; simp only [FixQ.scale]; omega)

/-! ### Fixtures: transported equation ≡ the circuit's pure-data reference

Worked-example numbers (`IP/Net/HFTQuote.defaultParams`): k₁ = 0.5 tick/lot
(32768), δ = 1.25 ticks (81920), mid = 100 ticks, q = ±3 lots. -/

-- r = 100 − 0.5·3 = 98.5 ticks → 98.5·65536
#guard (resPriceQ ⟨32768⟩ ⟨100 * 65536⟩ ⟨3 * 65536⟩).n == 6455296
-- bid = 97.25, ask = 99.75
#guard (bidPriceQ ⟨32768⟩ ⟨81920⟩ ⟨100 * 65536⟩ ⟨3 * 65536⟩).n == 6373376
#guard (askPriceQ ⟨32768⟩ ⟨81920⟩ ⟨100 * 65536⟩ ⟨3 * 65536⟩).n == 6537216
-- short inventory skews the quotes UP: r = 100 + 1.5 = 101.5
#guard (resPriceQ ⟨32768⟩ ⟨100 * 65536⟩ ⟨-3 * 65536⟩).n == 6651904

/-! The floor shows itself on a sub-lsb product: k₁·q = 1.5 lsb floors to
1 lsb, and the SUBTRACTION turns that into a result 0.5 lsb ABOVE exact —
the one-sided bias `resPriceQ_within_one_lsb` states. -/
#guard (resPriceQ ⟨32768⟩ ⟨0⟩ ⟨3⟩).n == -1     -- exact −1.5 lsb, floored mul

/-! ### Cross-check against the BitVec datapath (`quoteStep`)

`quoteStep` is the pure-data reference the CIRCUIT is sim-tested against
cycle-by-cycle (`Tests/IP/Net/HFTQuoteTest.lean`), so agreement here chains
the ℝ equation all the way to the RTL: retype (this file) ⋈ quoteStep
(these guards) ⋈ circuit (the sim test).  `.toInt` on the BitVec side and
`.n` on the FixQ side compare the same Q15.16 numerator. -/

open Sparkle.IP.Net.HFTQuote in
private def fixtureBidAsk (qLots : Int) : Int × Int :=
  let q : BitVec 32 := BitVec.ofInt 32 (qLots * 65536)
  let mid : BitVec 32 := BitVec.ofNat 32 (100 * 65536)
  let (_, bid, ask) := quoteStep defaultParams q mid false false
  (bid.toInt, ask.toInt)

#guard (fixtureBidAsk 3).1 ==
  (bidPriceQ ⟨32768⟩ ⟨81920⟩ ⟨100 * 65536⟩ ⟨3 * 65536⟩).n
#guard (fixtureBidAsk 3).2 ==
  (askPriceQ ⟨32768⟩ ⟨81920⟩ ⟨100 * 65536⟩ ⟨3 * 65536⟩).n
-- negative inventory: floors must agree on the sign-crossing side too
#guard (fixtureBidAsk (-3)).1 ==
  (bidPriceQ ⟨32768⟩ ⟨81920⟩ ⟨100 * 65536⟩ ⟨-3 * 65536⟩).n
#guard (fixtureBidAsk (-3)).2 ==
  (askPriceQ ⟨32768⟩ ⟨81920⟩ ⟨100 * 65536⟩ ⟨-3 * 65536⟩).n
-- a non-lot-aligned inventory, so the mulQ floor is actually exercised
#guard
  (let q : BitVec 32 := BitVec.ofInt 32 3
   let mid : BitVec 32 := BitVec.ofNat 32 0
   let (_, bid, _) := Sparkle.IP.Net.HFTQuote.quoteStep
     Sparkle.IP.Net.HFTQuote.defaultParams q mid false false
   bid.toInt)
  == (bidPriceQ ⟨32768⟩ ⟨81920⟩ ⟨0⟩ ⟨3⟩).n

end SparkleProofs.Retype.HftTransport
