import IP.Net.ICMP
import Tests.Ved.ComposeConnectCheck
import Tools.VedComposeMultiCircuit

/-!
# Post-check of a WRAPPER COPY of the real row R227 (`synth_icmpResponderByte`) through the connection path (connect16)

This file is a COPY of the private wrapper `synth_icmpResponderByte` of `Tests/IP/Net/ICMPTest.lean` (the executed name is
`_private._stdin.0.synth_icmpResponderByte`-like, of this file, not the fixed inventory constant): a local real-IP-content
result, NOT a fixed ledger row, NOT in CI.  The responder and the parser are two wired closed circuits, so it needs
`ved.compose.step`, `ved.compose.connect`, `sparkle.deepExportState` and `ved.compose.multiCircuit`.  Run by hand, ONE process, guarded:

    python3 -I rss_guard.py 23068672 timeout 890 kjob lake env lean <abs>/Tests/Ved/ComposeConnectR227Check.lean

(`kjob lake build Tests.Ved.ComposeConnectCheck` and `kjob lake build IP.Net.ICMP` first.)  It runs the entry ONCE (`checkChain` of
`Tests/Ved/ComposeConnectCheck.lean`): stored type `==` `U2HRStmt` of the declaration, module/design equal a fresh synthesis of the
declaration, axioms within the standard three, 9 `reg_connect` + 1 `out_connect` sites (and 10 `VED COMPOSE CONNECT` log lines), the
real theorem of the child (`icmpHeaderByte.ved_u1`) occurs in the proof.
-/

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Net.ICMP

private def synth_icmpResponderByte
    (byte  : Signal defaultDomain (BitVec 8))
    (valid sopIcmp : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (icmpEchoResponder byte valid sopIcmp).txByte

#synthesizeVerilog synth_icmpResponderByte

open Lean Elab Command in
set_option Elab.async false in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option sparkle.deepExportState true in
set_option ved.compose.multiCircuit true in
set_option maxRecDepth 20000 in
run_cmd do
  let t0 ← IO.monoMsNow
  let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent `synth_icmpResponderByte)
  logInfo m!"R227 POST decl {n}"
  let kid := n ++ `ved_child ++ `Sparkle.IP.Net.ICMP.icmpHeaderByte ++ `ved_u1
  Tests.Ved.ComposeConnectCheck.checkChain n [kid] 9
  logInfo m!"R227 POST total {(← IO.monoMsNow) - t0} ms"
