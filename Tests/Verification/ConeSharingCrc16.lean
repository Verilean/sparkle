/-
  crc16CcittHW (DroneCAN) on the generator's cone-sharing route — the
  circuit the default route could never finish (its single register's
  inlined cone is 16 M chars; see DeepElabRealIP's ceiling notes).

  `set_option sparkle.deepShare true in #verify_elab_deep crc16CcittHW`
  proves BOTH the Signal-side trace theorem and the IR replay
  (`crc16CcittHW_sdeep_signal_run`) on the CdoW route: 1 register, 3
  inputs, 17 shared wires; replay axioms = the standard three plus
  decision-procedure auxiliaries (native_decide / bv_decide), no sorryAx —
  the generator audits this and refuses otherwise.

  Measured 2026-09-14: 709 s wall, `lake env lean`, MemoryMax=24G,
  maxHeartbeats 1,600,000 per generated declaration.  Expensive; CI runs
  it as its own step.
-/
import IP.Bus.DroneCANHW
import Tools.DeepElab
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Bus.DroneCANHW

set_option sparkle.deepShare true in
#verify_elab_deep crc16CcittHW
