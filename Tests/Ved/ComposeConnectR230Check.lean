import IP.Net.IPv4
import Tests.Ved.ComposeConnectCheck

/-!
# Post-check of a WRAPPER COPY of the real row R230 (`synth_ipv4TxByte`) through the connection path (connect14)

This file is a COPY of the private wrapper `synth_ipv4TxByte` of `Tests/IP/Net/IPv4Test.lean` (the executed name is
`_private._stdin.0.synth_ipv4TxByte` of this file, not the fixed inventory constant): a local real-IP-content result,
NOT a fixed ledger row, NOT in CI.  The declaration's port is directly a child's output and the two children are chained, so it
needs `ved.compose.step`, `ved.compose.connect` and `sparkle.deepExportState`.  Run by hand, ONE process, guarded:

    python3 -I rss_guard.py 23068672 timeout 890 kjob lake env lean <abs>/Tests/Ved/ComposeConnectR230Check.lean

(`kjob lake build Tests.Ved.ComposeConnectCheck` and `kjob lake build IP.Net.IPv4` first.)  It runs the entry ONCE (`checkChain` of
`Tests/Ved/ComposeConnectCheck.lean`): stored type `==` `U2HRStmt` of the declaration, module/design equal a fresh synthesis of the
declaration, axioms within the standard three, 5 `reg_connect` + 1 `out_connect` sites (and 6 `VED COMPOSE CONNECT` log lines), the
real theorems of both children (`ipv4HeaderByte.ved_u1`, `ipv4HeaderChecksumSig.ved_u1`) occur in the proof.
-/

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Net.IPv4

private def synth_ipv4TxByte
    (totalLen : Signal defaultDomain (BitVec 16))
    (proto    : Signal defaultDomain (BitVec 8))
    (srcIp dstIp : Signal defaultDomain (BitVec 32))
    (start    : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (ipv4TxBuilder totalLen proto srcIp dstIp start).headerByte

#synthesizeVerilog synth_ipv4TxByte

open Lean Elab Command in
set_option Elab.async false in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option sparkle.deepExportState true in
set_option maxRecDepth 20000 in
run_cmd do
  let t0 ← IO.monoMsNow
  let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent `synth_ipv4TxByte)
  logInfo m!"R230 POST decl {n}"
  let kid1 := n ++ `ved_child ++ `Sparkle.IP.Net.IPv4.ipv4HeaderByte ++ `ved_u1
  let kid2 := n ++ `ved_child ++ `Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig ++ `ved_u1
  Tests.Ved.ComposeConnectCheck.checkChain n [kid1, kid2] 5
  logInfo m!"R230 POST total {(← IO.monoMsNow) - t0} ms"
