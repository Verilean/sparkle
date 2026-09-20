/-
  crc16CcittHW (DroneCAN) on the generator's cone-sharing route — the
  circuit the default route could never finish (its single register's
  inlined cone is 16 M chars; see DeepElabRealIP's ceiling notes).

  `set_option sparkle.deepShare true in #verify_elab_deep crc16CcittHW`
  proves the chain from the Signal value to the printed Verilog on the
  CdoW route (1 register, 3 inputs, 16 shared wires — a full-width slice
  alias is not a slot): `_sdeep_trace`, the IR replay
  `_sdeep_signal_run`, the optimized-body replay `_sdeep_signal_runOpt`
  (`optimizeModule m` is what is printed), and the printed text read back
  by the shipping parser+lowerer, `_sdeep_text_parses` +
  `_sdeep_signal_runRT`.  Axioms: standard + decision-procedure
  auxiliaries, no sorryAx — audited by the generator.

  NOT proven here, by design of the M4 fragment: the forward
  emitter-semantics theorem `_sdeep_signal_svOpt`.  crc16's `(byte << 8)`
  is a 16-bit literal-amount shift whose value does not fit
  (`bitwiseShl`'s fit condition), so `seqCheck` refuses the statement and
  the generator reports `Opt SV-semantics theorem SKIPPED — statement
  `…` … outside the M4 sequential fragment`.  CI requires exactly that one
  SKIPPED line and nothing else skipped (docs/SharedRoute-Guarantees.md
  §4a; docs/RefusalLedger.md, shl width rule).

  Measured 2026-09-20: 122 s wall (cgroup peak 2.13 GB; 107–109 s /
  2.07–2.10 GB earlier the same day before the mask equations moved to
  the kernel — single runs, spread not attributed; was 880 s on
  2026-09-19 — kernel-unfolding `rfl`/`show` steps replaced by the
  generic `natJoin_right`, and each body's woCheck / memFree /
  noSelfRead / bodyWidthOk proven once, the 17 hwfCheckL facts derived
  from bodyWidthOk instead of walked), `lake build`, MemoryMax=24G,
  maxHeartbeats 1,600,000 per generated declaration (was 709 s before the
  two bridges).  Expensive; CI runs it as its own step.

  Axioms (F2 step 11, 2026-09-20): `_signal_run`, `_signal_runOpt`,
  `_signal_runRT` depend on the standard three plus the trace's
  `crc16CcittHW_sdeep_trace._native.bv_decide.ax_*` only (1 auxiliary);
  `_text_parses` on the parse oracle's
  `crc16CcittHW_sdeep_text_parses._native.native_decide.ax_1`.  CI
  checks that the Opt/RT replay lines report the same auxiliary count as
  the plain replay.
-/
import IP.Bus.DroneCANHW
import Tools.DeepElab
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Bus.DroneCANHW

set_option sparkle.deepShare true in
#verify_elab_deep crc16CcittHW
