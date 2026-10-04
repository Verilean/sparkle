# FFTNTT

A Cooley–Tukey radix-2 network and an `N = N₁·N₂` four-step
decomposition, written once and specialised by type inference to either
a Number Theoretic Transform (`Zp p w`) or a complex fixed-point FFT
(`Cx w f`), and carried either by plain values (reference model), by
`Signal` (combinational or pipelined circuit), or by raw `BitVec` wires
(synthesisable RTL).

Built on [Sparkle](https://github.com/Verilean/sparkle).

## Build

```
lake build FFT        # the datapath
lake exe fft-test     # 29 tests
```

## Layout

| module | contents |
|---|---|
| `FFT.Algebra` | `FFTAlg`, `FFTRoot`, `AlgOn`, `HVec`, the butterfly |
| `FFT.Zp` | ℤ/pℤ in a `BitVec`: conditional-subtract add/sub, Barrett multiply, `ω_n = g^((p−1)/n)` |
| `FFT.Fixed` | complex Q-format: 4-multiply product with round-to-nearest |
| `FFT.Spec` | the DFT as a literal sum — what everything is judged against |
| `FFT.CooleyTukey` | radix-2 DIT, recursive, forward and inverse |
| `FFT.FourStep` | `N = N₁·N₂`, sub-transforms as parameters |
| `FFT.Unrolled` | non-recursive, projection-free spellings for `N = 2, 4, 8`, proved `rfl`-equal to the recursive ones |
| `FFT.RTL` | the synthesisable carrier and the Verilog tops |
| `FFT.Equiv` | the proofs |

See `FFT/README.md` for the design rationale, what is proved, and what
is not.

## Verilog

```lean
import FFT.RTL
open FFTNTT Sparkle.Core.Domain Sparkle.Core.Signal
abbrev D : DomainConfig := defaultDomain
def ntt8D (a b c d e f g h : Signal D (BitVec 16)) := ntt8 a b c d e f g h
#synthesizeVerilog ntt8D
```

Pre-generated output for four tops is in `hw/`.
