/-
  Driver for the FFT / NTT test suite.

      lake exe fft-test
-/
import LSpec
import FFTTests.FFTTest

open Std (HashMap)

def main (args : List String) : IO UInt32 := do
  let t ← FFTNTT.Tests.suite
  LSpec.lspecIO (HashMap.ofList [("fft", [t])]) args
