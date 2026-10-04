-- Driver: emit the FULL hierarchical Verilog design (top + every
-- @[hardware_module] submodule) for the policy signer's UART-TX top.
-- #synthesizeVerilog prints only the top module; #writeVerilogDesign
-- lands the whole design (all submodules) on disk. Run with:
--   lake env lean fpga/tangNano20k/build/GenPolicySigner.lean
import Sparkle
import IP.Crypto.Proof.Keccak256
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.TxPolicy
import IP.Crypto.PolicySignDemo

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Crypto.PolicySignDemo

set_option maxRecDepth 100000
set_option maxHeartbeats 80000000

def gen_policyTx
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (policySignDemo uartRx bitDiv).uartTx

#writeVerilogDesign gen_policyTx "fpga/tangNano20k/build/policy_signer.v"
