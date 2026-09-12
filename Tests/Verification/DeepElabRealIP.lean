import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import IP.Net.CRC32
import IP.Net.UART
import IP.Crypto.EcdsaSignSmall
import IP.Bus.DroneCANHW
import IP.Bus.SBUSHW
import IP.Bus.SPIHW
import Tools.DeepElab

/-!
  `#verify_elab_deep` on REAL shipping IP — not demo circuits.

  Each success here is an instance of the general Signal↔IR theorem
  (`Cdo.elab_general`) on a production circuit: the cycle-by-cycle
  Signal semantics of the shipped DSL definition equals the proven
  IR evaluator on its compiled next-state/output cones.

  Current real-IP coverage:
  * `crc32Engine` — CRC-32 byte engine (IP/Net): xor/shr/and/sub/
    concat/mux over 32 bits, a private two-level helper chain
    (`crc32StepSig` → 8 × `crc32BitSig`) unfolded via the collected-
    helper mechanism, plus a private `abbrev poly : BitVec 32`
    constant (closed BitVec constants ride along with the helpers).
  * `uartTxHW` — UART transmitter (IP/Net): 4 registers (10/4/16-bit
    plus a Bool `busy`), 3 inputs (one Bool), a struct output `TxOut`
    with two Bool ports, literal-width `++` ascriptions.  The first
    circuit with a register index ≥ 3 — the case that forced the
    Signal-side bridge onto literal-width readers (`{f}_deep_rd{i}`)
    instead of `Cdo.stateAt`'s `Γr.get i`-typed values.
  * `regFile` — the ECDSA signer's 64×256 BRAM register file
    (IP/Crypto/EcdsaSignSmall): a `Signal.memory` with 256-bit data
    feeding a register, struct output `RfOut`.  The first shipping
    memory on the deep route: `CdoM` capstone AND the `stepIterM`
    replay, both ports.
  * `transferIdTrackerHW` — DroneCAN transfer-ID tracker (IP/Bus):
    3 registers (5-bit + two Bools), 5 inputs (four Bools), struct
    output with three ports.
  * `frameAccumulatorHW` — S.BUS frame accumulator (IP/Bus): 4
    registers, 3 inputs, struct output with four ports.
  * `spiMasterHW` — SPI master (IP/Bus): 7 registers (2/4/16/8/8-bit
    plus two Bools), 6 inputs, struct output with five ports.  The
    widest state chain on the route; it forced the seed-boundedness
    proof onto an explicit case cascade (`repeat' split`'s inner simp
    exceeds its step limit at this width, and `repeat'` swallowed the
    failure).

  Known boundaries (each is a worklist item, not a silent skip):
  * non-Signal value parameters (`biquad`'s `lim`, `mulQSig`'s
    `w f`) go through a specialized wrapper def, as for synthesis
    (demos `accK15` / `accN200` in DeepElabReifyDemo);
  * arithmetic size: `closedLoopCircuit` (PID + plant, 32/64-bit
    fixed-point multiplies, nested; 3 registers once RegDedup merges
    the two-pass copies) times out in the definition phase (`isDefEq`
    on the multiply cones) before the bridge runs — the nesting itself
    is covered by the `DeepElabReifyDemo` nested demos;
  * cone size: `crc16CcittHW` (DroneCAN) unrolls `crc16Step` 8 times,
    each step reading its input 3 times.  Measured: the module is 94
    statements and its single register's INLINED CONE is 16 MB of
    `repr` text — the blowup is in `inlineConeT` (which substitutes a
    wire's definition at every use), not in the reification, so a
    `let`-sharing `CExpr` alone would not help.  The whole certified
    chain (`cone_resolved_agrees_at_seed` and everything above it) is
    stated over the fully-inlined cone, so sharing has to enter at the
    cone level with its own agreement theorem — a design change, not a
    patch;
  * slot count: `kvHw` (memcached key-value engine, 13 registers + 5
    inputs + 4 memories) hits a hard ceiling in the generated name
    table — past 15 arms the match compiler stops enumerating `Fin`
    literals and calls the tail a missing case.  Neither escape works:
    matching on `i.val` stops `nm ⟨i, _⟩` from iota-reducing (the
    pointwise readers are `rfl` on it) and a catch-all arm defeats the
    `simp` that discharges the "not a slot" reader.  A `List String`
    read with `getD` clears the exhaustiveness failure (measured) but
    is NOT sufficient on its own: with a symbolic context length the
    "not a slot" reader's `List.finRange` becomes a `List.ofFn` over
    `Fin (Γ.length)` that simp will not unfold, whereas over a literal
    `Fin 18` it does.  So this boundary needs both the list-backed
    table and a `finRange` enumeration keyed on the literal slot count.
-/

namespace Sparkle.Tests.DeepElabRealIP

open Sparkle.IP.Net.CRC32 Sparkle.IP.Net.UART

#verify_elab_deep crc32Engine
#verify_elab_deep uartTxHW
#verify_elab_deep Sparkle.IP.Crypto.EcdsaSignSmall.regFile
#verify_elab_deep Sparkle.IP.Bus.DroneCANHW.transferIdTrackerHW
#verify_elab_deep Sparkle.IP.Bus.SBUSHW.frameAccumulatorHW
#verify_elab_deep Sparkle.IP.Bus.SPIHW.spiMasterHW

/-- The theorems above are build-time facts; the exe is a formality
    so `lake build` has an anchor. -/
def main : IO Unit := do
  IO.println "deep-elab real-IP: crc32Engine, uartTxHW, regFile, transferIdTrackerHW, frameAccumulatorHW, spiMasterHW PROVEN (build-time)"


-- deep-bridge replay pins: the general-theorem route's per-instance
-- chain (seed bound → register phase → cycle trace → Signal ≡ runModule),
-- generated by #verify_elab_deep and audited against sorryAx
#check @crc32Engine_deep_seed_bounded
#check @crc32Engine_deep_regstep
#check @crc32Engine_deep_state_trace
#check @crc32Engine_deep_signal_fold
#check @crc32Engine_deep_signal_run

-- uart: the capstone per struct port, the shared register chain, and
-- the literal-width readers the Signal-side bridge is stated over
#check @uartTxHW_txLine_deep_trace
#check @uartTxHW_txReady_deep_trace
#check @uartTxHW_txLine_deep_rd3_succ
#check @uartTxHW_deep_seed_bounded
#check @uartTxHW_deep_regstep
#check @uartTxHW_deep_state_trace
#check @uartTxHW_txLine_deep_signal_run
#check @uartTxHW_txReady_deep_signal_run

-- the shipping memory: contents step and the runModule statement
#check @regFile_deep_memstep
#check @regFile_rdata_deep_signal_run
#print axioms regFile_rdata_deep_signal_run
#check @transferIdTrackerHW_error_deep_signal_run
#check @frameAccumulatorHW_ch0_deep_signal_run
-- the widest state chain (7 registers): the cascade-proved seed bound
#check @spiMasterHW_deep_envSt_bounded
#check @spiMasterHW_done_deep_signal_run

end Sparkle.Tests.DeepElabRealIP
