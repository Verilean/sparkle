import IP.Crypto.SHA512BlockHW
import Tests.Ved.ComposeConnectCheck

/-!
# Independent post-check of the real row R194 (`synth_sha512Block_done`) accepted through the connection path

NOT part of CI (a ~7 min proof, ~18 GB).  Run by hand, ONE process, guarded:

    VED_HIER_STATS=1 VED_HIER_SCRIPT_FILE=<abs>/script.txt VED_HIER_PHASE_FILE=<abs>/phase \
      python3 -I rss_guard.py 23068672 timeout 890 kjob lake env lean <abs>/Tests/Ved/ComposeConnectR194Check.lean

(`kjob lake build Tests.Ved.ComposeConnectCheck` and `kjob lake build IP.Crypto.SHA512BlockHW` first.)  It runs the entry ONCE
(`checkRow`, the toys' check from `Tests/Ved/ComposeConnectCheck.lean`, not a weaker copy) and then, in the same command, checks
independently of the entry: (i) the stored type `==` `U2HRStmt` of the ORIGINAL declaration (Expr equality), (ii) the module/design
equal a fresh synthesis of the declaration, (iii) the axioms are within the standard three, (iv) 35 `VED COMPOSE CONNECT` log
lines, 34 `reg_connect` and 1 `out_connect` site in the proof, (v) the child's real theorem constant occurs in the proof.
The declaration is the one of `Tests/IP/Crypto/SHA512BlockHWTest.lean` (`synth_sha512Block_done`, copied unchanged).
-/

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Crypto.SHA512BlockHW

private def synth_sha512Block_done
    (start : Signal defaultDomain Bool)
    (h0 h1 h2 h3 h4 h5 h6 h7 : Signal defaultDomain (BitVec 64))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 :
      Signal defaultDomain (BitVec 64)) :
    Signal defaultDomain Bool :=
  (sha512BlockHW start h0 h1 h2 h3 h4 h5 h6 h7
     w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15).done

#synthesizeVerilog synth_sha512Block_done

open Lean Elab Command in
set_option Elab.async false in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option maxRecDepth 20000 in
run_cmd do
  let t0 ← IO.monoMsNow
  let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent `synth_sha512Block_done)
  logInfo m!"R194 POST decl {n}"
  let kid := n ++ `ved_child ++ `Sparkle.IP.Crypto.SHA512HW.kMux ++ `ved_u1
  Tests.Ved.ComposeConnectCheck.checkRow n kid 34
  logInfo m!"R194 POST total {(← IO.monoMsNow) - t0} ms"
