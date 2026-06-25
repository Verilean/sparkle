import IP.Net.Ethernet
import Sparkle
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.Ethernet

def frameBytes : List (BitVec 8) :=
  [ 0xAA#8, 0xBB#8, 0xCC#8, 0xDD#8, 0xEE#8, 0xFF#8
  , 0x11#8, 0x22#8, 0x33#8, 0x44#8, 0x55#8, 0x66#8
  , 0x08#8, 0x00#8
  , 0xDE#8, 0xAD#8, 0xBE#8, 0xEF#8 ]

def n : Nat := frameBytes.length

def byteStream : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => (frameBytes[t]?).getD 0#8⟩
def validStream : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < n)⟩
def sopStream : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩
def eopStream : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = n - 1)⟩

def rxOut : RxOut defaultDomain := rxFramer byteStream validStream sopStream eopStream

def main : IO Unit := do
  for t in [:18] do
    let dmac := rxOut.dmac.val t
    let pv   := rxOut.payloadValid.val t
    IO.println s!"cycle {t}: dmac={dmac.toNat} payloadValid={pv}"
