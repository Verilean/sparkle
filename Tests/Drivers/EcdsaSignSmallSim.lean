-- Native Sparkle simulation of the modular ALU (compiled `lake exe`, so the
-- `Signal.memory` native impl links).  No iverilog: evaluates the `Signal`
-- model directly via `.atTime`.
--   lake exe ecdsa-sign-small-sim
import Sparkle
import IP.Crypto.EcdsaSignSmall
import IP.Crypto.Secp256k1Field
import IP.Crypto.Secp256k1ECDSA

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall

namespace Sparkle.Tests.Drivers.EcdsaSignSmallSim

abbrev D := defaultDomain

structure Cmd where
  lo : Nat
  op : BitVec 3
  ra : BitVec 6
  rb : BitVec 6
  rd : BitVec 6
  isLoad : Bool := false
  ldData : BitVec 256 := 0

def sched : List Cmd :=
  [ { lo := 1,   op := 7, ra:=0,rb:=0,rd:=0, isLoad := true, ldData := 5 }
  , { lo := 3,   op := 7, ra:=0,rb:=1,rd:=1, isLoad := true, ldData := 7 }
  , { lo := 20,  op := 2, ra:=0,rb:=1,rd:=2 }   -- ADDP reg2 = 5+7
  , { lo := 60,  op := 3, ra:=0,rb:=1,rd:=3 }   -- SUBP reg3 = 5-7
  , { lo := 100, op := 4, ra:=0,rb:=1,rd:=5 }   -- ADDN reg5 = 5+7
  , { lo := 140, op := 5, ra:=0,rb:=1,rd:=6 }   -- SUBN reg6 = 5-7
  , { lo := 200, op := 0, ra:=0,rb:=1,rd:=4 }   -- MULP reg4 = 5*7
  , { lo := 600, op := 1, ra:=0,rb:=1,rd:=7 } ] -- MULN reg7 = 5*7

def activeAt (t : Nat) : Option Cmd :=
  (sched.filter (fun c => c.lo ≤ t)).getLast?

def startSig : Signal D Bool := ⟨fun t => sched.any (fun c => c.lo == t && !c.isLoad)⟩
def loadEnSig : Signal D Bool := ⟨fun t => sched.any (fun c => c.lo == t && c.isLoad)⟩
def opSig : Signal D (BitVec 3) := ⟨fun t => match activeAt t with | some c => c.op | none => 0⟩
def aSig : Signal D (BitVec 6) := ⟨fun t => match activeAt t with | some c => c.ra | none => 0⟩
def bSig : Signal D (BitVec 6) := ⟨fun t => match activeAt t with | some c => c.rb | none => 0⟩
def dSig : Signal D (BitVec 6) := ⟨fun t => match activeAt t with | some c => c.rd | none => 0⟩
def loadAddrSig : Signal D (BitVec 6) := ⟨fun t => match activeAt t with | some c => c.rd | none => 0⟩
def loadDataSig : Signal D (BitVec 256) := ⟨fun t => match activeAt t with | some c => c.ldData | none => 0⟩

def alu : AluOut D :=
  bignumALU startSig opSig aSig bSig dSig loadEnSig loadAddrSig loadDataSig

def p : Nat := Sparkle.IP.Crypto.Secp256k1Field.p
def n : Nat := Sparkle.IP.Crypto.Secp256k1ECDSA.n

def check (name : String) (got exp : BitVec 256) : IO Bool := do
  if got == exp then IO.println s!"PASS {name} = {got.toNat}"; return true
  else IO.println s!"FAIL {name}: got={got.toNat} exp={exp.toNat}"; return false

def main : IO Unit := do
  let r1 ← check "ADDP 5+7" (alu.outVal.atTime 55)  (BitVec.ofNat 256 12)
  let r2 ← check "SUBP 5-7" (alu.outVal.atTime 95)  (BitVec.ofNat 256 (p - 2))
  let r3 ← check "ADDN 5+7" (alu.outVal.atTime 135) (BitVec.ofNat 256 12)
  let r4 ← check "SUBN 5-7" (alu.outVal.atTime 195) (BitVec.ofNat 256 (n - 2))
  let r5 ← check "MULP 5*7" (alu.outVal.atTime 560) (BitVec.ofNat 256 35)
  let r6 ← check "MULN 5*7" (alu.outVal.atTime 980) (BitVec.ofNat 256 35)
  if r1 && r2 && r3 && r4 && r5 && r6 then IO.println "ALL PASS (native Sparkle .atTime sim)"
  else do IO.println "FAILURES"; IO.Process.exit 1

end Sparkle.Tests.Drivers.EcdsaSignSmallSim

def main : IO Unit := Sparkle.Tests.Drivers.EcdsaSignSmallSim.main
