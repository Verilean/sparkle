# FFT — one butterfly network, four instantiations

A Cooley–Tukey radix-2 network and an `N = N₁·N₂` four-step
decomposition, written **once** and specialised by type inference to
either a Number Theoretic Transform or a complex fixed-point FFT, and
carried either by plain values (reference model) or by `Signal` (the
circuit).

## The two type classes

The design turns on splitting two things that are usually conflated:

| class | question it answers |
|---|---|
| `FFTAlg` / `FFTRoot α` | what are the **coefficients**? (`Zp p w` for an NTT, `Cx w f` for a fixed-point FFT) |
| `AlgOn β α` | what do the **wires** carry? (`α` itself, `Signal dom α`, or a raw `Signal dom (BitVec 16)`) |

`α` is an `outParam` of `AlgOn`, so `cadd a b` picks the coefficient
ring out of the carrier with no annotation. Because the two are
separate, the carrier can be something that is *not* `Signal dom α` —
which is exactly what `algOnRtl` exploits: wires of raw machine words,
twiddles that are still residues mod `p`.

```
        coefficients α                 carrier β                     what you get
  ┌──────────────────────┐    ┌──────────────────────────┐
  │ Zp 12289 14  (NTT)   │ ×  │ α                        │ →  reference model, exact
  │ Cx 16 14   (fixed pt)│    │ Signal dom α             │ →  combinational circuit
  └──────────────────────┘    │ Signal dom α + register  │ →  pipelined circuit
                              │ Signal dom (BitVec 16)   │ →  synthesisable RTL
                              └──────────────────────────┘
```

## Files

| file | contents |
|---|---|
| `FFT/Algebra.lean` | `FFTAlg`, `FFTRoot`, `AlgOn`, `HVec`, the butterfly |
| `Zp.lean` | ℤ/pℤ in a `BitVec`: conditional-subtract add/sub, Barrett multiply, `ω_n = g^((p−1)/n)` |
| `Fixed.lean` | complex Q-format: 4-multiply product with round-to-nearest, twiddles from `cos`/`sin` |
| `Spec.lean` | the DFT as a literal sum — the thing everything is judged against |
| `CooleyTukey.lean` | radix-2 DIT, recursive (natural order in *and* out), forward and inverse |
| `FourStep.lean` | `N = N₁·N₂`, sub-transforms as parameters |
| `Unrolled.lean` | non-recursive, projection-free spellings for `N = 2, 4, 8`, proved `rfl`-equal to the recursive ones |
| `RTL.lean` | the synthesisable carrier and the Verilog tops |
| `Equiv.lean` | the proofs |

## What is proved

* `ctWith_sampleAt` / `ct_sampleAt` — the circuit sampled at time `t`
  equals the reference model applied to the inputs at time `t`. The
  proof is an induction whose every leaf is `rfl`, because the circuit
  and the model are literally the same term at two different carriers.
* `ctWith_pipelined_delay` / `ctPipelined_delay` — the registered
  network at `t + m` equals the combinational one at `t`. This is what
  makes `ctPipelinedLatency` a specification rather than a comment.
* `ctPipelined_eq_model` — the two composed.
* `ct2u_eq`, `ct4u_eq`, `ct8u_eq`, `fs8u_eq` — the unrolled,
  synthesisable spellings are *definitionally* the recursive ones, so
  the theorems above apply to the emitted Verilog without restatement.

No `sorry`; `#print axioms` shows only `propext` and `Quot.sound`.

## What is not proved yet

`fourStep = ct` as an algebraic identity. It needs commutativity,
associativity, distributivity and the root-of-unity laws — collected in
`LawfulFFT` in `Equiv.lean`, with the target statement spelled out.
`Zp` satisfies those laws; `Cx` satisfies none of them exactly, because
fixed-point addition wraps and fixed-point multiplication rounds. That
asymmetry is the honest content of "an NTT is exact and an FFT is not",
which is why it lives in a class rather than a comment.

Meanwhile the identity is checked by execution: over `Zp` the tests
assert `ct = dft = ctFourStep` **exactly**, for `N = 8` and `16`, for the
splits `2×4`, `4×2`, `4×4`, and for a non-power-of-two `3×4`.

## Verilog

`hw/` holds emitted SystemVerilog for four tops:

| module | structure | assigns | registers |
|---|---|---|---|
| `ntt4D` | 4-point, combinational | 34 | 0 |
| `ntt8D` | 8-point Cooley–Tukey, combinational | 100 | 0 |
| `ntt8fsD` | 8-point as four-step 2×4 | 132 | 0 |
| `ntt8pD` | 8-point pipelined, latency 3 | 108 | 24 |

`ntt8D` and `ntt8fsD` compute the same function and are visibly
different circuits — which is the point of having the decomposition.

Two things had to be true for these to emit. Sparkle's Verilog
elaborator inlines non-recursive definitions but cannot unfold a
recursive one, and does not reduce type-class projections; hence
`Unrolled.lean`'s `…Ops` forms. And it only recognises a fixed
vocabulary of lifted operators, so a lifted `Zp.add` (a Lean `if`) is
rejected — hence `algOnRtl`, which rewrites the modular arithmetic as
`Signal.mux` / `Signal.ule` / shift / subtract. Neither change touched
the network, the model, or the proofs.

## Running

```
lake build FFT
lake exe fft-test
```
