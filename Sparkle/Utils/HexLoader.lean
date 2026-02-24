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

end Sparkle.Utils.HexLoader
