/-
  FFT — generic FFT / NTT datapath.

  One Cooley-Tukey butterfly network, written against a coefficient
  typeclass, instantiated by inference at:
    * `Zp p w`  — modular arithmetic, i.e. a Number Theoretic Transform
    * `Cx w f`  — complex fixed point, i.e. an ordinary FFT
  and carried either by plain values (reference model) or by
  `Signal dom _` (the circuit).
-/
import FFT.Algebra
import FFT.Zp
import FFT.Fixed
import FFT.Spec
import FFT.CooleyTukey
import FFT.FourStep
import FFT.Equiv
import FFT.Unrolled
import FFT.RTL
