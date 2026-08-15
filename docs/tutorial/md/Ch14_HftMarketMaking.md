# Chapter 14 — Market Making on Silicon: an HFT Quoting Engine with a Proved Position Bound

Chapter 12 took one control law through three layers: an ℝ equation with a
stability theorem, a fixed-point transport of *the same equation*, and an
RTL datapath checked against it. This chapter runs the identical flow on a
different industry's version of the same problem — and in this industry, the
translation bug Chapter 12 guards against has a price tag with nine digits.

## 14.0 Why HFT is Chapter 12 with money on the line

Inside a high-frequency trading firm, two people own one formula:

1. **The quant** writes the strategy over ℝ — stochastic differential
   equations, continuous time, floating point. For market making the
   canonical model is Avellaneda–Stoikov: quote around a *reservation
   price* that leans against your inventory.
2. **The hardware engineer** re-implements it on an FPGA in fixed point,
   because the strategy must answer in nanoseconds and a soft CPU cannot.

Between them sits a hand translation, and hand translations drift: a gain
rounded differently, a floor that became a truncation on one side, a shift
the wrong way. The industry's defence is simulation — which, as §12.2.1
said, compares the RTL against itself; the ℝ model that was actually
*reasoned about* is never in the loop. When the drift is in the feedback
path, the failure mode is not a wrong price, it is a position that grows
instead of mean-reverting. (The canonical cautionary tale is Knight
Capital, 2012: a deployment defect in automated order flow, \$460M in 45
minutes. Not a fixed-point bug — but exactly the class of "the deployed
thing was not the thing we reasoned about".)

One fact makes hardware trading *friendlier* to this chapter's method than
control was: **exchange prices are integer ticks**. Q15.16 ticks is not an
approximation compromise forced by the FPGA — it is the market's native
number format. The ℝ model is the idealisation; fixed point is the ground
truth. That inversion makes the transport story stronger, not weaker.

## 14.1 The worked example: one quoting engine

### The equations

Avellaneda–Stoikov, constant-window form (γσ²τ and the spread folded into
two constants):

    r[n]   = mid[n] − k₁·q[n]        reservation price   (k₁ ticks per lot)
    bid[n] = r[n] − δ                δ = half-spread
    ask[n] = r[n] + δ
    q[n+1] = clamp±qMax( q[n] + buyFill[n] − sellFill[n] )

The strategy's entire intelligence is the term **−k₁·q**: long inventory
(q > 0) shifts *both* quotes down, so the ask becomes more attractive (you
sell more) and the bid less attractive (you buy less). The book pushes your
position back toward flat. That is a feedback loop — and feedback loops are
what Chapters 12's machinery certifies.

### The RTL

`IP/Net/HFTQuote.lean`, in full:

```lean
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
    return { bid := r - halfSpread, ask := r + halfSpread, inv := qS }
```

One register (the inventory), one Q15.16 multiply, two adds. `clampSymC
qMax` is the position limit — note that it is a *wire*, not a risk-desk
policy document. Worked-example constants: k₁ = 0.5 tick/lot (`32768`),
δ = 1.25 ticks (`81920`), qMax = ±8 lots.

As in Chapter 12 (and `IP/Control/PID.lean`), the file carries a pure-data
reference (`quoteStep` / `runQuote`) beside the circuit, and
`Tests/IP/Net/HFTQuoteTest.lean` drives both through a 14-cycle tape —
rising and falling mids, a fill pattern that pins the inventory against
*both* clamp rails — asserting `Signal.val` equality cycle-by-cycle:

    lake exe hft-quote-test
    === HFT quoting engine: circuit vs pure-data reference ===
      inventory at cycle 5 = 196608 (expected 196608 = +3 lots, clamp active)
      ✓ all 14 cycles match the reference (incl. both clamp hits)

## 14.2 One equation, three layers

Exactly Chapter 12's spine, with new file names:

| layer | file | what it holds |
|---|---|---|
| 1 · ℝ | `proofs/SparkleProofs/Hft/MarketMaking.lean` | the quote equations + the inventory stability theorem |
| 2 · Q15.16 | `proofs/SparkleProofs/Retype/HftTransport.lean` | the SAME equations, transported by `retype` — nobody typed them |
| 3 · RTL | `IP/Net/HFTQuote.lean` | the datapath, sim-checked against layer 2's numbers |

Layer 2 is generated, not written:

```lean
retype_def resPriceQ := resPrice using Real => FixQ
retype_def bidPriceQ := bidPrice using Real => FixQ
retype_def askPriceQ := askPrice using Real => FixQ
```

and then closed against both neighbours. Upward, a theorem: the transported
reservation price sits within **one LSB** of the exact value — the single
`mulQ` floor is the only error source, and the subtraction flips its bias
one-sided:

```lean
theorem resPriceQ_within_one_lsb (k1 s q : FixQ) :
    0 ≤ scale * (resPriceQ k1 s q).n - (scale * s.n - k1.n * q.n) ∧
        scale * (resPriceQ k1 s q).n - (scale * s.n - k1.n * q.n) < scale
```

Downward, `#guard` fixtures chain the transported equation to the BitVec
`quoteStep` the circuit is sim-tested against — including negative
inventory, where a truncating multiply would silently disagree with the
flooring `mulQ` (the §12.2.1 asymmetry, again):

```lean
#guard (fixtureBidAsk (-3)).1 ==
  (bidPriceQ ⟨32768⟩ ⟨81920⟩ ⟨100 * 65536⟩ ⟨-3 * 65536⟩).n
```

So: ℝ equation ⋈ (retype) ⋈ FixQ ⋈ (`#guard`) ⋈ `quoteStep` ⋈ (14-cycle
`Signal.val` sim) ⋈ RTL. One chain, no hand-copied formula anywhere in it.

## 14.3 The theorem a risk desk can read

Chapter 12 proved: contraction + bounded disturbance ⇒ geometric envelope
plus a noise ball (`§12.4`). Here the *same shape* appears with the
disturbance recast: not quantization error — **fill randomness**.

Under a linearised fill response, one quoting window removes an expected
`c·q` of inventory (0 < c < 1; `c` collects k₁ × the book's fill
sensitivity × window length), leaving

    q' = (1 − c)·q + w,     |w| ≤ W

where W is the per-window fill cap — you cannot be filled for more than you
quote. `SparkleProofs.Hft.MarketMaking` then proves:

```lean
theorem inventory_ultimate_bound (T : InvTraj) (n : Nat) :
    |T.q n| ≤ (1 - T.c) ^ n * |T.q0| + T.W / T.c
```

Read as a trading statement: **whatever position you start from, the mean
dynamics bring you within W/c of flat, geometrically fast, and keep you
there.** The noise ball W/c is *exact*, not an over-approximation — one
line of algebra shows it reproduces itself: `(1−c)·(W/c) + W = W/c`. And
the corollary is phrased the way the desk would ask the question:

```lean
theorem inventory_settles (T : InvTraj) (n : Nat) (ε : ℝ)
    (htrans : (1 - T.c) ^ n * |T.q0| ≤ ε) :
    |T.q n| ≤ T.W / T.c + ε
```

With the worked numbers — say the skew produces c = 0.2 per window and you
quote 1 lot per side (W = 1) — the resting position stays within 5 lots of
flat, comfortably inside the ±8-lot clamp. The clamp should be *slack* in
normal operation; if the model is right you never touch it.

## 14.4 Two safety layers, honestly separated

This chapter deliberately stacks two guarantees of different character:

1. **Model-based** (the theorem above): the mean dynamics mean-revert.
   Its hypothesis — expected drift −c·q — is a *linearisation* of the
   A–S exponential fill intensities around small inventory. It is a model.
   Markets can violate models.
2. **Model-free** (the clamp): `|q[n]| ≤ qMax` for every n, *by
   construction*, for any market behaviour whatsoever — the same
   clamp-by-construction argument as the PID integrator's anti-windup
   (§12.1's `I[n] ∈ [−iLim, iLim]` "for ANY gains and any input").

Layer 1 says the strategy *behaves well* when the world is roughly as
modelled. Layer 2 says the position *cannot exceed the limit* even when it
isn't. A risk framework needs both, and needs to know which is which —
conflating them is how "our model says we're fine" becomes a headline.

## 14.5 The latency budget: this slots into the wire path

`IP/Net/HFTStrategy.lean` (Chapter's companion IP, tested by
`hft-strategy-test`) already demonstrates the NIC-side skeleton: market
data bytes in → parser → strategy → emitter → order bytes out, first-in to
first-out in **5 cycles** (~32 ns at 156 MHz), no CPU anywhere. Its
strategy block is deliberately trivial ("always fire") — a placeholder with
a comment promising that "a real HFT block would inspect the payload…
between parser and emitter".

`quoteEngine` is that block: one `mulQ` and two adds of combinational
depth, quotes valid in the same cycle the inventory register settles.
The composition — parser feeding `mid`, fill reports feeding
`buyFill`/`sellFill`, emitter serialising `bid`/`ask` — keeps the whole
loop on silicon, with the part that decides *prices* carrying an ℝ-level
stability certificate and the part that touches *risk* clamped by
construction.

## 14.6 What this does and does not buy

In the Chapter 12 tradition of §12.10, the honest list:

* **The fill model is an assumption.** −c·q expected drift is the A–S
  linearisation; adverse selection, quote fading, and self-impact are not
  in it. The theorem constrains the model's world; the clamp constrains
  every world.
* **No SDE is solved on chip.** The SDE machinery (geometric Brownian
  price, exponential fill intensities) lives in the *derivation* of k₁ and
  δ; the circuit computes the resulting affine law. That is not a
  limitation peculiar to this chapter — it is how the real systems are
  built, and it is exactly why the translation seam this chapter closes
  exists at all.
* **W assumes you honour your own quote size.** If the venue can fill you
  beyond your quoted size (self-match, busted-trade adjustments), W is
  wrong and only the clamp holds.
* **k₁, δ here are worked-example constants.** Recomputing them per
  regime (σ² estimation, time-of-day τ) is upstream of this datapath —
  the Ch12 §12.5 verifier split applies unchanged if those become
  circuits too.
* **This is an engineering artefact, not trading advice.** The value
  demonstrated is the *method*: equation → transport → RTL with the seams
  proved shut.

## 14.7 Where next

The same three layers extend to the rest of the quant stack: a geometric
Brownian price generator (for on-chip scenario simulation — the CUDA batch
backend of Chapter 13 runs a million of them in parallel), Black–Scholes
edge calculators, multi-asset inventory with a matrix skew (the Lyapunov
machinery of §12.3 applies verbatim). Each is the same recipe this chapter
just ran: prove it over ℝ, transport it with `retype`, check the datapath
against the transported numbers, and keep one copy of the equation.

### Build and run everything in this chapter

```bash
lake exe hft-quote-test                 # layer 3: circuit vs reference, clamp hits
lake build Tests.IP.Net.HFTQuoteTest    # synth checks (3 wrappers)
cd proofs
lake build SparkleProofs.Hft.MarketMaking      # layer 1: ultimate bound
lake build SparkleProofs.Retype.HftTransport   # layer 2: retype + 1-lsb + fixtures
```
