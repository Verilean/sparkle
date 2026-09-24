import Tools.CertifyShared
import Tests.Verification.ConeSharingCrc16

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Bus.DroneCANHW
open Tools.CertifiedRoundtrip

-- The forward SV theorem is intentionally absent for this circuit. The
-- roundtrip contract is nevertheless complete, with its parser trust explicit.
#seal_shared_roundtrip crc16CcittHW => crc16Certified

open Lean Elab Command in
run_cmd do
  let cert ← getConstInfo ``crc16Certified
  let axs ← liftCoreM <| collectAxioms cert.name
  let parseAxiom := `crc16CcittHW_sdeep_text_parses._native.native_decide.ax_1
  unless axs.contains parseAxiom do
    throwError "crc16 certificate is missing its parse dependency"
  if axs.contains ``sorryAx then throwError "crc16 certificate uses sorryAx"
  logInfo "CRC16 CERTIFICATION OK: roundtrip complete; forward SV not claimed"
