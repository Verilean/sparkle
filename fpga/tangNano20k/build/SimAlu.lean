-- Native Sparkle simulation of the modular ALU (no iverilog).
-- Evaluates the `Signal` model directly via `.atTime`.
--   lake env lean fpga/tangNano20k/build/SimAlu.lean
import Sparkle
import IP.Crypto.EcdsaSignSmall
import IP.Crypto.Secp256k1Field
import IP.Crypto.Secp256k1ECDSA

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall

abbrev D := defaultDomain

/-- A single ALU command occupying a cycle window `[lo, hi)`; `start`
    pulses at `lo`.  Loads use `op = 7` (ignored) and set `loadEn`. -/
structure Cmd where
  lo : Nat
  op : BitVec 3
  ra : BitVec 6
  rb : BitVec 6
  rd : BitVec 6
  isLoad : Bool := false
  ldData : BitVec 256 := 0

/-- Schedule: two loads, then the six ALU ops.  add/sub windows are 20
    cycles; mul windows 340 (bit-serial mul ≈ 267 cycles). -/
def sched : List Cmd :=
  [ { lo := 1,   op := 7, ra:=0,rb:=0,rd:=0, isLoad := true, ldData := 5 }   -- reg0 = 5
  , { lo := 3,   op := 7, ra:=0,rb:=1,rd:=1, isLoad := true, ldData := 7 }   -- reg1 = 7  (d=addr)
  , { lo := 20,  op := 2, ra:=0,rb:=1,rd:=2 }   -- ADDP reg2 = 5+7
  , { lo := 60,  op := 3, ra:=0,rb:=1,rd:=3 }   -- SUBP reg3 = 5-7
  , { lo := 100, op := 4, ra:=0,rb:=1,rd:=5 }   -- ADDN reg5 = 5+7
  , { lo := 140, op := 5, ra:=0,rb:=1,rd:=6 }   -- SUBN reg6 = 5-7
  , { lo := 200, op := 0, ra:=0,rb:=1,rd:=4 }   -- MULP reg4 = 5*7
  , { lo := 600, op := 1, ra:=0,rb:=1,rd:=7 } ] -- MULN reg7 = 5*7

/-- For load commands the "window" is a single cycle; for ALU ops we hold
    op/src/dst until the next command's `lo`. -/
def activeAt (t : Nat) : Option Cmd :=
  (sched.filter (fun c => c.lo ≤ t)).getLast?

def startSig : Signal D Bool := ⟨fun t =>
  (sched.any (fun c => c.lo == t && !c.isLoad))⟩
def loadEnSig : Signal D Bool := ⟨fun t =>
  (sched.any (fun c => c.lo == t && c.isLoad))⟩
def opSig : Signal D (BitVec 3) := ⟨fun t =>
  match activeAt t with | some c => c.op | none => 0⟩
def aSig : Signal D (BitVec 6) := ⟨fun t =>
  match activeAt t with | some c => c.ra | none => 0⟩
def bSig : Signal D (BitVec 6) := ⟨fun t =>
  match activeAt t with | some c => c.rb | none => 0⟩
def dSig : Signal D (BitVec 6) := ⟨fun t =>
  match activeAt t with | some c => c.rd | none => 0⟩
def loadAddrSig : Signal D (BitVec 6) := ⟨fun t =>
  match activeAt t with | some c => c.rd | none => 0⟩
def loadDataSig : Signal D (BitVec 256) := ⟨fun t =>
  match activeAt t with | some c => c.ldData | none => 0⟩

def alu : AluOut D :=
  bignumALU startSig opSig aSig bSig dSig loadEnSig loadAddrSig loadDataSig

/-- Read `outVal` at the sample cycle for a command that started at `lo`. -/
def sampleAt (lo : Nat) : BitVec 256 := alu.outVal.atTime lo

def p : Nat := Sparkle.IP.Crypto.Secp256k1Field.p
def n : Nat := Sparkle.IP.Crypto.Secp256k1ECDSA.n

def check (name : String) (got exp : BitVec 256) : IO Bool := do
  if got == exp then
    IO.println s!"PASS {name} = {got.toNat}"
    return true
  else
    IO.println s!"FAIL {name}: got={got.toNat} exp={exp.toNat}"
    return false

def main : IO Unit := do
  -- Sample each op just before the next command (result is latched & held).
  let r1 ← check "ADDP 5+7" (sampleAt 55)  (BitVec.ofNat 256 12)
  let r2 ← check "SUBP 5-7" (sampleAt 95)  (BitVec.ofNat 256 (p - 2))
  let r3 ← check "ADDN 5+7" (sampleAt 135) (BitVec.ofNat 256 12)
  let r4 ← check "SUBN 5-7" (sampleAt 195) (BitVec.ofNat 256 (n - 2))
  let r5 ← check "MULP 5*7" (sampleAt 560) (BitVec.ofNat 256 35)
  let r6 ← check "MULN 5*7" (sampleAt 980) (BitVec.ofNat 256 35)
  if r1 && r2 && r3 && r4 && r5 && r6 then
    IO.println "ALL PASS (native Sparkle .atTime sim)"
  else
    IO.println "FAILURES"

#eval main
