import Sparkle.Core.Signal

/-!
Regression tests for the stream semantics of `Signal.registerWithEnable`.
These examples are kernel-checked when this module is built; no test runner
or external RTL simulator is needed. Synthesis coverage is provided by the
existing `test_reg_enable` in `Tests.TestCompilerExtensions`.
-/

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.RegisterWithEnableTest

private def changingInput : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => BitVec.ofNat 8 (10 + t)⟩

-- A single capture must survive arbitrarily many disabled cycles. The old
-- implementation produced [0, 7, 7, 0, 0, 0] for this trace.
example :
    ((Signal.registerWithEnable (0#8)
      (⟨fun t => t == 0⟩ : Signal defaultDomain Bool)
      (Signal.pure (7#8))).sample 6).map BitVec.toNat =
      [0, 7, 7, 7, 7, 7] := by decide

-- Disabled inputs must not leak through, including before the first capture.
example :
    ((Signal.registerWithEnable (42#8) (Signal.pure false)
      changingInput).sample 6).map BitVec.toNat =
      [42, 42, 42, 42, 42, 42] := by decide

-- Continuous enable retains the usual one-cycle register latency.
example :
    ((Signal.registerWithEnable (42#8) (Signal.pure true)
      changingInput).sample 6).map BitVec.toNat =
      [42, 10, 11, 12, 13, 14] := by decide

-- Capture again after a long disabled gap, then hold the new value.
example :
    ((Signal.registerWithEnable (99#8)
      (⟨fun t => t == 1 || t == 5⟩ : Signal defaultDomain Bool)
      changingInput).sample 9).map BitVec.toNat =
      [99, 99, 11, 11, 11, 11, 15, 15, 15] := by decide

-- Alternating enable exercises the update/hold boundary without long gaps.
example :
    ((Signal.registerWithEnable (42#8)
      (⟨fun t => t % 2 == 0⟩ : Signal defaultDomain Bool)
      changingInput).sample 7).map BitVec.toNat =
      [42, 10, 10, 12, 12, 14, 14] := by decide

-- Nonzero initialization, a late first capture, and a trailing disabled run.
example :
    ((Signal.registerWithEnable (42#8)
      (⟨fun t => t == 3⟩ : Signal defaultDomain Bool)
      changingInput).sample 8).map BitVec.toNat =
      [42, 42, 42, 42, 13, 13, 13, 13] := by decide

end Sparkle.Tests.RegisterWithEnableTest
