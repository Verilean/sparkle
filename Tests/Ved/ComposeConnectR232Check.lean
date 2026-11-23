import IP.Net.IPv4
import Tests.Ved.ComposeConnectCheck

/-!
# Post-check of a WRAPPER COPY of the real row R232 (`synth_ipv4RxHeaderOk`) through the connection path

This file is a COPY of the private wrapper `synth_ipv4RxHeaderOk` of `Tests/IP/Net/IPv4Test.lean` (the executed name is
`_private._stdin.0.synth_ipv4RxHeaderOk` of this file, not the fixed inventory constant): a local real-IP-content result,
NOT a fixed ledger row, NOT in CI.  Run by hand, ONE process, guarded:

    VED_HIER_STATS=1 VED_HIER_PHASE_FILE=<abs>/phase \
      python3 -I rss_guard.py 23068672 timeout 890 kjob lake env lean <abs>/Tests/Ved/ComposeConnectR232Check.lean

(`kjob lake build Tests.Ved.ComposeConnectCheck` and `kjob lake build IP.Net.IPv4` first.)  It runs the entry ONCE (`checkRow` of
`Tests/Ved/ComposeConnectCheck.lean`): stored type `==` `U2HRStmt` of the declaration, module/design equal a fresh synthesis of the
declaration, axioms within the standard three, 9 `reg_connect` + 1 `out_connect` sites (and 10 `VED COMPOSE CONNECT` log lines), the
child's real theorem `ipv4HeaderChecksumSig.ved_u1` (proved by the add-stage chain route) occurs in the proof.
-/

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Net.IPv4

private def synth_ipv4RxHeaderOk
    (byte  : Signal defaultDomain (BitVec 8))
    (valid sopIp : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (ipv4RxParser byte valid sopIp).headerOk

#synthesizeVerilog synth_ipv4RxHeaderOk

open Lean Elab Command in
set_option Elab.async false in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option maxRecDepth 20000 in
run_cmd do
  let t0 ← IO.monoMsNow
  let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent `synth_ipv4RxHeaderOk)
  logInfo m!"R232 POST decl {n}"
  let kid := n ++ `ved_child ++ `Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig ++ `ved_u1
  Tests.Ved.ComposeConnectCheck.checkRow n kid 9
  logInfo m!"R232 POST total {(← IO.monoMsNow) - t0} ms"
