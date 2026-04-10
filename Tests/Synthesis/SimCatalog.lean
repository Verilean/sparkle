/-
  SimCatalog — Simulation correctness tests for the synthesis catalog.

  Each entry from SynthCatalog.lean is exercised with concrete inputs
  via `Signal.pure` + `.atTime 0`, verifying that the Signal DSL
  semantics produce the expected value. This catches bugs where
  Verilog is generated but the operation has the wrong meaning.

  Run: lake env lean Tests/Synthesis/SimCatalog.lean
  All #eval must produce `true`.
-/
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- Abbreviation to avoid domain inference issues in #eval
abbrev S (n : Nat) := Signal defaultDomain (BitVec n)
abbrev SB := Signal defaultDomain Bool
def s (v : BitVec n) : S n := Signal.pure v
def ev (sig : S n) : BitVec n := sig.atTime 0

-- ============================================================
-- 1. Signal.pure
-- ============================================================
#eval ev (s 42#8) == 42#8

-- ============================================================
-- 2. Arithmetic: +, -, *
-- ============================================================
#eval ev ((s 3#8 : S 8) + s 5#8) == 8#8
#eval ev ((s 10#8 : S 8) - s 3#8) == 7#8
#eval ev ((s 6#8 : S 8) * s 7#8) == 42#8
#eval ev ((s 200#8 : S 8) + s 100#8) == 44#8  -- overflow wraps

-- ============================================================
-- 3. Bitwise: &&&, |||, ^^^
-- ============================================================
#eval ev ((s 0xF0#8 : S 8) &&& s 0x3C#8) == 0x30#8
#eval ev ((s 0xF0#8 : S 8) ||| s 0x0F#8) == 0xFF#8
#eval ev ((s 0xFF#8 : S 8) ^^^ s 0x0F#8) == 0xF0#8

-- ============================================================
-- 4. Shift
-- ============================================================
#eval ev ((s 1#8 : S 8) <<< s 3#8) == 8#8
#eval ev ((s 128#8 : S 8) >>> s 2#8) == 32#8

-- ============================================================
-- 5. Signal.mux
-- ============================================================
#eval ev (Signal.mux (Signal.pure true : SB) (s 42#8) (s 99#8)) == 42#8
#eval ev (Signal.mux (Signal.pure false : SB) (s 42#8) (s 99#8)) == 99#8

-- ============================================================
-- 6. Signal.register (at time 0 → init value)
-- ============================================================
#eval ev (Signal.register (dom := defaultDomain) 77#8 (s 0#8)) == 77#8

-- ============================================================
-- 7. Comparison (===)
-- ============================================================
#eval (s 5#8 === s 5#8).atTime 0 == true
#eval (s 5#8 === s 6#8).atTime 0 == false

-- ============================================================
-- 8. extractLsb' (slice)
-- ============================================================
#eval ev (Signal.map (BitVec.extractLsb' 8 8 ·) (s 0xABCD1234#32)) == 0x12#8
#eval ev (Signal.map (BitVec.extractLsb' 0 8 ·) (s 0xABCD1234#32)) == 0x34#8
#eval ev (Signal.map (BitVec.extractLsb' 24 8 ·) (s 0xABCD1234#32)) == 0xAB#8

-- ============================================================
-- 9. Negation
-- ============================================================
#eval ev (-(s 1#8 : S 8)) == 0xFF#8
#eval ev (-(s 0#8 : S 8)) == 0x00#8

-- ============================================================
-- 10. Concat (++)
-- ============================================================
#eval ev ((s 0xAB#8 : S 8) ++ s 0xCD#8) == 0xABCD#16

-- ============================================================
-- 11. let binding
-- ============================================================
#eval
  let a : S 8 := s 10#8
  let b : S 8 := s 20#8
  let sum := a + b
  let doubled := sum + sum
  ev doubled == 60#8

-- ============================================================
-- 12. signExtend
-- ============================================================
#eval ev (Signal.map (BitVec.signExtend 16 ·) (s 0x7F#8)) == 0x007F#16
#eval ev (Signal.map (BitVec.signExtend 16 ·) (s 0x80#8)) == 0xFF80#16
#eval ev (Signal.map (BitVec.signExtend 16 ·) (s 0x00#8)) == 0x0000#16

-- ============================================================
-- 13. Scale multiply pattern
-- ============================================================
#eval
  let a : S 16 := Signal.map (BitVec.signExtend 16 ·) (s 4#8)
  let b : S 16 := Signal.map (BitVec.signExtend 16 ·) (s 3#8)
  let prod : S 16 := a * b
  let lo := Signal.map (BitVec.extractLsb' 0 8 ·) prod
  ev lo == 12#8

-- ============================================================
-- 14. Tree reduction
-- ============================================================
@[reducible] def pairR (f : α → α → α) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest => f x y :: pairR f rest

@[reducible] def treeR (f : α → α → α) (z : α) (fuel : Nat) : List α → α
  | [] => z
  | [x] => x
  | xs => match fuel with
    | 0 => xs.headD z
    | n + 1 => treeR f z n (pairR f xs)

#eval
  let result : S 8 := treeR (· + ·) (s 0#8) 4 [s 1#8, s 2#8, s 3#8, s 4#8]
  ev result == 10#8

-- ============================================================
-- 15. Mux + eq combo
-- ============================================================
#eval
  let addr : S 4 := s 5#4
  ev (Signal.mux (addr === s 5#4) (s 42#8) (s 99#8)) == 42#8

#eval
  let addr : S 4 := s 3#4
  ev (Signal.mux (addr === s 5#4) (s 42#8) (s 99#8)) == 99#8

-- ============================================================
-- 16. Bus decompose
-- ============================================================
#eval
  let bus : S 32 := s 0x12345678#32
  let b0 := ev (Signal.map (BitVec.extractLsb' 0 8 ·) bus)
  let b1 := ev (Signal.map (BitVec.extractLsb' 8 8 ·) bus)
  let b2 := ev (Signal.map (BitVec.extractLsb' 16 8 ·) bus)
  let b3 := ev (Signal.map (BitVec.extractLsb' 24 8 ·) bus)
  b0 == 0x78#8 && b1 == 0x56#8 && b2 == 0x34#8 && b3 == 0x12#8

-- ============================================================
-- 17. Bus compose
-- ============================================================
#eval
  let packed : S 32 := (s 0x12#8 : S 8) ++ s 0x34#8 ++ s 0x56#8 ++ s 0x78#8
  ev packed == 0x12345678#32

-- ============================================================
-- 18. Struct-like bundle
-- ============================================================
#eval
  let x : S 16 := s 0x1234#16
  let y : S 16 := s 0x5678#16
  let pair : S 32 := x ++ y
  let fst := ev (Signal.map (BitVec.extractLsb' 16 16 ·) pair)
  let snd := ev (Signal.map (BitVec.extractLsb' 0 16 ·) pair)
  fst == 0x1234#16 && snd == 0x5678#16

-- ============================================================
-- 19. Field overwrite
-- ============================================================
#eval
  let bus : S 32 := s 0xAABBCCDD#32
  let hi : S 16 := Signal.map (BitVec.extractLsb' 16 16 ·) bus
  let lo : S 8 := Signal.map (BitVec.extractLsb' 0 8 ·) bus
  let newByte : S 8 := s 0xFF#8
  let result : S 32 := hi ++ newByte ++ lo
  ev result == 0xAABBFFDD#32

-- ============================================================
-- 20. MMIO dispatcher
-- ============================================================
#eval
  let addr : S 4 := s 0x4#4
  let a : S 32 := s 11#32
  let b : S 32 := s 22#32
  let c : S 32 := s 33#32
  let result := Signal.mux (addr === s 0x0#4) a
    (Signal.mux (addr === s 0x4#4) b
      (Signal.mux (addr === s 0x8#4) c (s 0#32)))
  ev result == 22#32
