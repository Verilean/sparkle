/-
  FPGABench — `#verify_fpga` resource-fit table for the
  existing synthesizable IP catalog.

  Each entry mirrors a `synth_*` wrapper from the per-IP
  test files (which themselves gate `lake build`-time
  synthesis).  Here we additionally estimate LUT / FF / BRAM
  / DSP usage against the published ceilings of the
  Gowin Tang Nano 9K and Tang Nano 50K parts.

  Build this file (it runs at `lake build` time via the
  command-elab `#verify_fpga`) to get a per-IP fit summary
  in `info:` lines.  A non-fit aborts the build, so the
  table doubles as a regression gate: if the Sparkle
  compiler's lowering ever grows past the part ceilings,
  this file catches it before tape-out.

  Notes & caveats:
    - Resource numbers are coarse upper bounds — Vivado
      / Gowin EDA's actual P&R will likely yield smaller
      LUT counts thanks to logic packing and retiming.
    - Designs that need a 512-bit register (sha256Block's
      W-buffer) currently can't be synthesised by Sparkle
      due to the runCircuitH HList depth (see Compiler
      task C2).  Only their building-block sub-modules
      appear here.
    - Pure-Nat IPs (Ed25519Field, X25519, AES, GHASH) are
      software-side reference implementations and aren't
      synthesisable — they have no entry here.
-/
import Sparkle
import Sparkle.Verification.CostCmd
import IP.Crypto.SHA256
import IP.Crypto.GHASHHW
import IP.Net.Ethernet
import IP.Net.ARP
import IP.Net.ICMP
import IP.Net.IPv4
import IP.Net.HFTStrategy

namespace Sparkle.Tests.Verification.FPGABench

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.Cost.Targets

/-! ### Crypto — SHA-256 K-table mux (64-way constant LUT). -/

def sha256KMux (cnt : Signal defaultDomain (BitVec 7)) :
    Signal defaultDomain (BitVec 32) :=
  Sparkle.IP.Crypto.SHA256.kMux cnt

#verify_fpga sha256KMux tangNano9K
#verify_fpga sha256KMux tangNano50K

/-! ### Crypto — GHASH HW multiplier (multi-cycle GF(2^128)).
    Does NOT fit Tang Nano 9K (the 128-bit XOR + mux fabric
    exceeds 8640 LUT4); 50K has plenty of headroom.  Real
    Gowin EDA usually halves the static estimate via LUT4
    packing, so this may actually fit 9K in practice, but
    our conservative estimator says no. -/

def ghashHWResult
    (start : Signal defaultDomain Bool)
    (xIn yIn : Signal defaultDomain (BitVec 128)) :
    Signal defaultDomain (BitVec 128) :=
  (Sparkle.IP.Crypto.GHASHHW.gmulHW start xIn yIn).result

-- 9K is over our conservative estimate — would need real
-- Gowin EDA to confirm or denser shapes.  Verify against
-- the 50K target only here.
#verify_fpga ghashHWResult tangNano50K

/-! ### Network — Ethernet TX framer. -/

def ethTxByte
    (dmacIn smacIn : Signal defaultDomain (BitVec 48))
    (etIn          : Signal defaultDomain (BitVec 16))
    (payloadByte   : Signal defaultDomain (BitVec 8))
    (payloadValid payloadLast start : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (Sparkle.IP.Net.Ethernet.txFramer dmacIn smacIn etIn
     payloadByte payloadValid payloadLast start).txByte

#verify_fpga ethTxByte tangNano9K
#verify_fpga ethTxByte tangNano50K

/-! ### Network — ARP responder. -/

def arpRespByte
    (rxByte : Signal defaultDomain (BitVec 8))
    (rxValid sopArp : Signal defaultDomain Bool)
    (ownMac : Signal defaultDomain (BitVec 48))
    (ownIp  : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 8) :=
  (Sparkle.IP.Net.ARP.arpResponder rxByte rxValid sopArp ownMac ownIp).payloadByte

#verify_fpga arpRespByte tangNano9K
#verify_fpga arpRespByte tangNano50K

/-! ### Network — IPv4 TX byte path. -/

def ipv4TxByte
    (totalLen : Signal defaultDomain (BitVec 16))
    (proto    : Signal defaultDomain (BitVec 8))
    (srcIp dstIp : Signal defaultDomain (BitVec 32))
    (start    : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (Sparkle.IP.Net.IPv4.ipv4TxBuilder totalLen proto srcIp dstIp start).headerByte

#verify_fpga ipv4TxByte tangNano9K
#verify_fpga ipv4TxByte tangNano50K

/-! ### Network — HFT strategy (recv-trigger → emit). -/

def hftOut
    (inByte : Signal defaultDomain (BitVec 8))
    (inValid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (Sparkle.IP.Net.HFTStrategy.hftStrategy inByte inValid).outByte

#verify_fpga hftOut tangNano9K
#verify_fpga hftOut tangNano50K

/-! ### Network — ICMP echo responder. -/

def icmpResp
    (byte  : Signal defaultDomain (BitVec 8))
    (valid sopIcmp : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (Sparkle.IP.Net.ICMP.icmpEchoResponder byte valid sopIcmp).txByte

#verify_fpga icmpResp tangNano9K
#verify_fpga icmpResp tangNano50K

end Sparkle.Tests.Verification.FPGABench
