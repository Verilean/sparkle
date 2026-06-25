import IP.Crypto.SHA512
open Sparkle.IP.Crypto.SHA512

def hexByte (b : Nat) : String :=
  let lo := b &&& 0xF
  let hi := (b >>> 4) &&& 0xF
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  String.ofList [digit hi, digit lo]

def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let mut s := ""
  for b in bs do
    s := s ++ hexByte b.toNat
  return s

def main : IO Unit := do
  let empty := sha512Bytes (#[] : Array UInt8)
  IO.println s!"SHA-512(empty) = {hexOfBytes empty}"
  IO.println "expected       = cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
  let abc := sha512Bytes ((("abc" : String).toUTF8.toList).toArray)
  IO.println s!"SHA-512(abc)   = {hexOfBytes abc}"
  IO.println "expected       = ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
