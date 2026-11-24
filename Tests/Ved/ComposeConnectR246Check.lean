import IP.Net.UsbWebServer
import Tests.Ved.ComposeConnectCheck
import Tools.VedComposeMultiCircuit

/-!
# Post-check of a WRAPPER COPY of the real row R246 (`synth_usbWebServer`) through the connection path (unit 24)

This file is a COPY of the private wrapper `synth_usbWebServer` of `Tests/IP/Net/UsbWebServerSynth.lean` (the executed name is
`_private._stdin.0.synth_usbWebServer` of this file, not the fixed inventory constant): a local real-IP-content result, NOT a
fixed ledger row, NOT in CI.  The web server is a chain of six closed circuits (rx, deframer, http, txSeq, framer, tx; one real
child `respByteMux`).  This file sets `ved.compose.step`, `ved.compose.connect`, `sparkle.deepExportState` and
`ved.compose.multiCircuit` (the last one selects the fused deep closer of unit 23 and the normalised register comparison
`RegsOkNF` / `reg_connectN` of unit 24).  Run by hand, ONE process, guarded:

    VED_HIER_STATS=1 VED_HIER_PHASE_FILE=<abs>/phase \
      python3 -I rss_guard.py 23068672 timeout 890 kjob lake env lean <abs>/Tests/Ved/ComposeConnectR246Check.lean

(`kjob lake build Tests.Ved.ComposeConnectCheck`, `kjob lake build IP.Net.UsbWebServer` first.)  It runs the entry ONCE
(`checkChain` of `Tests/Ved/ComposeConnectCheck.lean`): stored type `==` `U2HRStmt` of the declaration, module/design equal a fresh
synthesis of the declaration, axioms within the standard three, 20 `reg_connect(N)` + 1 `out_connect(N)` sites (and 21
`VED COMPOSE CONNECT` log lines), the child's real theorem `respByteMux.ved_u1` occurs in the proof.
-/

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Net.UsbWebServer

set_option maxHeartbeats 4000000 in
private def synth_usbWebServer
    (uartRxLine : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (usbWebServer uartRxLine bitDiv).uartTx

set_option maxHeartbeats 4000000 in
#synthesizeVerilog synth_usbWebServer

open Lean Elab Command in
set_option Elab.async false in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option sparkle.deepExportState true in
set_option ved.compose.multiCircuit true in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
run_cmd do
  let t0 ← IO.monoMsNow
  let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent `synth_usbWebServer)
  logInfo m!"R246 POST decl {n}"
  let kid := n ++ `ved_child ++ `Sparkle.IP.Net.UsbWebServer.respByteMux ++ `ved_u1
  Tests.Ved.ComposeConnectCheck.checkChain n [kid] 20
  logInfo m!"R246 POST total {(← IO.monoMsNow) - t0} ms"
