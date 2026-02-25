/-
  BitNet Attention — INT8 Q·K^T Dot Product — Signal DSL

  Dot product between INT8 Q and K vectors:
    1. Sign-extend q[i], k[i] from 8 → 32 bits
    2. Multiply: 32-bit signed product
    3. Adder tree reduction
    4. Scale by 1/sqrt(d_k) via arithmetic right shift
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Examples.BitNet.Config
import Examples.BitNet.SignalHelpers

namespace Sparkle.Examples.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Examples.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- INT8 dot product with 1/sqrt(d_k) scaling using Signal DSL.
    Sign-extends INT8 to 32 bits for sufficient accumulator width. -/
def dotProductSignal (qs ks : Array (Signal dom (BitVec 8))) (dkShift : Nat)
    : Signal dom (BitVec 32) :=
  let products : Array (Signal dom (BitVec 32)) := Id.run do
    let mut prods : Array (Signal dom (BitVec 32)) := #[]
    for i in [:qs.size] do
      if i < ks.size then
        -- Sign-extend INT8 to 32 bits (24 + 8 = 32)
        let qExt := signExtendSignal 24 qs[i]!
        let kExt := signExtendSignal 24 ks[i]!
        prods := prods.push ((· * ·) <$> qExt <*> kExt)
    return prods
  let sum := adderTree products
  -- Scale by 1/sqrt(d_k) via arithmetic shift right
  if dkShift > 0 then
    (ashr · ·) <$> sum <*> Signal.pure (BitVec.ofNat 32 dkShift)
  else sum

end Sparkle.Examples.BitNet.Attention
