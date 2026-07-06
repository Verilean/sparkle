import Sparkle
import IP.Crypto.Keccak256Sponge
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.Keccak256Sponge
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def keccakSpongeTop
    (start : Signal defaultDomain Bool) (nBlocks : Signal defaultDomain (BitVec 2))
    (m0  m1  m2  m3  m4  m5  m6  m7  m8  m9
     m10 m11 m12 m13 m14 m15 m16 m17 m18 m19
     m20 m21 m22 m23 m24 m25 m26 m27 m28 m29
     m30 m31 m32 m33 : Signal defaultDomain (BitVec 64)) : SpongeOut defaultDomain :=
  keccak256SpongeHW start nBlocks m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33
#sim keccakSpongeTop
