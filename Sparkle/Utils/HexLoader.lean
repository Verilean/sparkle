/-
  Hex File Loader

  Parses $readmemh-format hex files into Lean arrays for use with
  Signal.memoryWithInit. Supports the same format used by iverilog
  and Verilog simulators.

  Format:
    - One hex word per line (e.g., "00000013")
    - Lines starting with "@" are address directives (skipped)
    - Lines starting with "//" are comments (skipped)
    - Empty lines are skipped
-/

import Sparkle.Core.JIT

open Sparkle.Core.JIT

namespace Sparkle.Utils.HexLoader

/-- Parse a single hex string into a Nat. Returns 0 on invalid input. -/
def hexToNat (s : String) : Nat :=
  let s := s.trimAscii.toString
  let s := if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 else s
  s.foldl (fun acc c =>
    let digit := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
                 else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
                 else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
                 else 0
    acc * 16 + digit) 0

/-- Parse a $readmemh-format hex file into an array of 32-bit words. -/
def loadHex (path : System.FilePath) : IO (Array (BitVec 32)) := do
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n"
  let mut words : Array (BitVec 32) := #[]
  for line in lines do
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    if trimmed.startsWith "@" then continue
    if trimmed.startsWith "//" then continue
    -- Handle multiple words per line (space-separated)
    let parts := trimmed.splitOn " " |>.filter (fun s => !s.trimAscii.toString.isEmpty)
    for part in parts do
      let p := part.trimAscii.toString
      if !p.isEmpty && !p.startsWith "//" then
        words := words.push (BitVec.ofNat 32 (hexToNat p))
  return words

/-- Convert an array into a lookup function for memoryWithInit.
    Out-of-bounds addresses return 0. -/
def arrayToInitFn (arr : Array (BitVec 32)) : BitVec 12 → BitVec 32 :=
  fun addr =>
    let idx := addr.toNat
    if h : idx < arr.size then arr[idx] else 0#32

/-- Convert an array into a lookup function with configurable address width. -/
def arrayToInitFn' {n : Nat} (arr : Array (BitVec 32)) : BitVec n → BitVec 32 :=
  fun addr =>
    let idx := addr.toNat
    if h : idx < arr.size then arr[idx] else 0#32

/-- Load a raw binary file as an array of 32-bit words (little-endian).
    Pads the last word with zeros if the file size is not a multiple of 4. -/
def loadBinary (path : System.FilePath) : IO (Array UInt32) := do
  let bytes ← IO.FS.readBinFile path
  let numWords := (bytes.size + 3) / 4
  let mut words : Array UInt32 := Array.mkEmpty numWords
  for i in [:numWords] do
    let b0 := if h : 4*i < bytes.size then bytes[4*i].toNat else 0
    let b1 := if h : 4*i + 1 < bytes.size then bytes[4*i + 1].toNat else 0
    let b2 := if h : 4*i + 2 < bytes.size then bytes[4*i + 2].toNat else 0
    let b3 := if h : 4*i + 3 < bytes.size then bytes[4*i + 3].toNat else 0
    words := words.push ((b3 <<< 24 ||| b2 <<< 16 ||| b1 <<< 8 ||| b0) : Nat).toUInt32
  return words

/-- Load a raw binary file into JIT DRAM byte-lane memories.
    The SoC has 8 DRAM byte-lane memories (4 data + 4 ifetch) that must all
    be loaded with the same data for coherent access.

    Parameters:
    - `handle`: JIT simulation handle
    - `path`: Path to the binary file
    - `baseWordAddr`: Starting word address in DRAM (e.g., 0x000000 for 0x80000000)

    Returns: number of 32-bit words loaded -/
def loadBinaryToDRAM (handle : JITHandle) (path : System.FilePath)
    (baseWordAddr : UInt32) (dramWords : UInt32 := 8388608) : IO Nat := do
  let bytes ← IO.FS.readBinFile path
  let numWords := (bytes.size + 3) / 4
  let mut loaded := 0
  for i in [:numWords] do
    let addr := baseWordAddr + i.toUInt32
    if addr >= dramWords then break
    let b0 := if h : 4*i < bytes.size then bytes[4*i].toNat else 0
    let b1 := if h : 4*i + 1 < bytes.size then bytes[4*i + 1].toNat else 0
    let b2 := if h : 4*i + 2 < bytes.size then bytes[4*i + 2].toNat else 0
    let b3 := if h : 4*i + 3 < bytes.size then bytes[4*i + 3].toNat else 0
    -- Data byte lanes (memIdx 1-4)
    JIT.setMem handle 1 addr b0.toUInt32
    JIT.setMem handle 2 addr b1.toUInt32
    JIT.setMem handle 3 addr b2.toUInt32
    JIT.setMem handle 4 addr b3.toUInt32
    -- Instruction fetch byte lanes (memIdx 7-10)
    JIT.setMem handle 7  addr b0.toUInt32
    JIT.setMem handle 8  addr b1.toUInt32
    JIT.setMem handle 9  addr b2.toUInt32
    JIT.setMem handle 10 addr b3.toUInt32
    loaded := loaded + 1
  return loaded

end Sparkle.Utils.HexLoader
