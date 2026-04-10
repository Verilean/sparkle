/-
  SynthCatalog — Unit tests for confirmed synthesizable Signal DSL constructs.

  Each `#synthesizeVerilog` invocation is a contract: if it generates Verilog
  today, it must keep generating Verilog tomorrow. Regressions here mean the
  backend broke a construct that users depend on.

  Run: lake env lean Tests/Synthesis/SynthCatalog.lean
  All entries must produce "Verilog successfully generated!" with no errors.
-/
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- ============================================================
-- 1. Signal.pure (constant)
-- ============================================================
def synth_pure (_ : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.pure 42

#synthesizeVerilog synth_pure

-- ============================================================
-- 2. Binary arithmetic: +, -, *
-- ============================================================
def synth_add (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  a + b

#synthesizeVerilog synth_add

def synth_sub (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  a - b

#synthesizeVerilog synth_sub

def synth_mul (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  a * b

#synthesizeVerilog synth_mul

-- ============================================================
-- 3. Bitwise: &&&, |||, ^^^
-- ============================================================
def synth_and (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  a &&& b

#synthesizeVerilog synth_and

def synth_or (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  a ||| b

#synthesizeVerilog synth_or

def synth_xor (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  a ^^^ b

#synthesizeVerilog synth_xor

-- ============================================================
-- 4. Shift
-- ============================================================
def synth_shl (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  a <<< b

#synthesizeVerilog synth_shl

def synth_shr (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  a >>> b

#synthesizeVerilog synth_shr

-- ============================================================
-- 5. Signal.mux (condition: Signal dom Bool)
-- ============================================================
def synth_mux (c : Signal defaultDomain Bool) (a b : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  Signal.mux c a b

#synthesizeVerilog synth_mux

-- ============================================================
-- 6. Signal.register
-- ============================================================
def synth_reg (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0 a

#synthesizeVerilog synth_reg

-- ============================================================
-- 7. Comparison (===) → Signal dom Bool
-- ============================================================
def synth_eq (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain Bool :=
  a === b

#synthesizeVerilog synth_eq

-- ============================================================
-- 8. Signal.map extractLsb' (bit slice)
-- ============================================================
def synth_slice (a : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 8) :=
  a.map (BitVec.extractLsb' 8 8 ·)

#synthesizeVerilog synth_slice

-- ============================================================
-- 9. Negation (unary -)
-- ============================================================
def synth_neg (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  -a

#synthesizeVerilog synth_neg

-- ============================================================
-- 10. HAppend (bit concatenation)
-- ============================================================
def synth_concat (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 16) :=
  a ++ b

#synthesizeVerilog synth_concat

-- ============================================================
-- 11. let binding (wire reuse)
-- ============================================================
def synth_let (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let sum := a + b
  let doubled := sum + sum
  doubled

#synthesizeVerilog synth_let

-- ============================================================
-- 12. Signal.map signExtend (sign extension)
-- ============================================================
def synth_sext (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 16) :=
  a.map (BitVec.signExtend 16 ·)

#synthesizeVerilog synth_sext

-- ============================================================
-- 13. Scale multiply pattern (signext + mul + slice)
-- ============================================================
def synth_scale (acc : Signal defaultDomain (BitVec 48)) (scale : Signal defaultDomain (BitVec 32))
    : Signal defaultDomain (BitVec 32) :=
  let accExt : Signal defaultDomain (BitVec 80) := acc.map (BitVec.signExtend 80 ·)
  let scaleExt : Signal defaultDomain (BitVec 80) := scale.map (BitVec.signExtend 80 ·)
  let prod := accExt * scaleExt
  prod.map (BitVec.extractLsb' 24 32 ·)

#synthesizeVerilog synth_scale

-- ============================================================
-- 14. @[reducible] tree reduction (adder tree pattern)
-- ============================================================
@[reducible] def _root_.pairReduce (f : α → α → α) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest => f x y :: pairReduce f rest

@[reducible] def _root_.treeReduceAux (f : α → α → α) (zero : α) (fuel : Nat) : List α → α
  | [] => zero
  | [x] => x
  | xs => match fuel with
    | 0 => xs.headD zero
    | fuel' + 1 => treeReduceAux f zero fuel' (pairReduce f xs)

def synth_tree (a b c d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  treeReduceAux (· + ·) (Signal.pure 0) 4 [a, b, c, d]

#synthesizeVerilog synth_tree

-- ============================================================
-- 15. Mux + eq combo (address decode pattern)
-- ============================================================
def synth_mux_eq (addr : Signal defaultDomain (BitVec 4))
    (a b : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  Signal.mux (addr === 0x5#4) a b

#synthesizeVerilog synth_mux_eq

-- ============================================================
-- 16. Bus decompose: split 32-bit into 4 × 8-bit fields
-- ============================================================
def synth_bus_split (bus : Signal defaultDomain (BitVec 32))
    : Signal defaultDomain (BitVec 8) :=
  let byte0 := bus.map (BitVec.extractLsb' 0 8 ·)
  let byte1 := bus.map (BitVec.extractLsb' 8 8 ·)
  let byte2 := bus.map (BitVec.extractLsb' 16 8 ·)
  let byte3 := bus.map (BitVec.extractLsb' 24 8 ·)
  (byte0 + byte1) + (byte2 + byte3)

#synthesizeVerilog synth_bus_split

-- ============================================================
-- 17. Bus compose: pack 4 × 8-bit fields into 32-bit
-- ============================================================
def synth_bus_pack (a b c d : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 32) :=
  d ++ c ++ b ++ a

#synthesizeVerilog synth_bus_pack

-- ============================================================
-- 18. Struct-like bundle (pack + project via slice)
-- ============================================================
def synth_bundle (x y : Signal defaultDomain (BitVec 16))
    : Signal defaultDomain (BitVec 16) :=
  let pair := x ++ y
  let fst := pair.map (BitVec.extractLsb' 16 16 ·)
  let snd := pair.map (BitVec.extractLsb' 0 16 ·)
  fst + snd

#synthesizeVerilog synth_bundle

-- ============================================================
-- 19. Bus field overwrite (read-modify-write)
-- ============================================================
def synth_field_write (bus : Signal defaultDomain (BitVec 32))
    (newByte1 : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 32) :=
  let hi := bus.map (BitVec.extractLsb' 16 16 ·)
  let lo := bus.map (BitVec.extractLsb' 0 8 ·)
  hi ++ newByte1 ++ lo

#synthesizeVerilog synth_field_write

-- ============================================================
-- 20. Address-decoded bus mux (MMIO dispatcher)
-- ============================================================
def synth_mmio_mux (addr : Signal defaultDomain (BitVec 4))
    (periph_a periph_b periph_c : Signal defaultDomain (BitVec 32))
    : Signal defaultDomain (BitVec 32) :=
  Signal.mux (addr === 0x0#4) periph_a
    (Signal.mux (addr === 0x4#4) periph_b
      (Signal.mux (addr === 0x8#4) periph_c
        (Signal.pure 0)))

#synthesizeVerilog synth_mmio_mux

-- ============================================================
-- 21. Signal.loop (scalar feedback — counter)
-- ============================================================
def synth_loop_counter : Signal defaultDomain (BitVec 8) :=
  Signal.loop (dom := defaultDomain) (α := BitVec 8)
    fun (self : Signal defaultDomain (BitVec 8)) =>
    Signal.register 0#8 (self + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)))

#synthesizeVerilog synth_loop_counter

-- ============================================================
-- 22. Signal.loop with tuple state (FSM pattern)
-- ============================================================
def synth_loop_fsm (start : Signal defaultDomain Bool)
    (act : Signal defaultDomain (BitVec 32))
    : Signal defaultDomain (BitVec 32 × BitVec 32) :=
  Signal.loop (dom := defaultDomain)
    (α := BitVec 32 × BitVec 32)
    fun (self : Signal defaultDomain (BitVec 32 × BitVec 32)) =>
    let counter := Signal.fst self
    let acc := Signal.snd self
    let nextCounter : Signal defaultDomain (BitVec 32) :=
      Signal.mux start (Signal.pure 0#32 : Signal defaultDomain (BitVec 32))
        (counter + (Signal.pure 1#32 : Signal defaultDomain (BitVec 32)))
    let nextAcc : Signal defaultDomain (BitVec 32) :=
      Signal.mux start (Signal.pure 0#32 : Signal defaultDomain (BitVec 32))
        (acc + act)
    bundle2 (Signal.register 0#32 nextCounter) (Signal.register 0#32 nextAcc)

#synthesizeVerilog synth_loop_fsm

-- ============================================================
-- 23. Signal.loop + memoryComboRead (BRAM + FSM)
-- ============================================================
def synth_loop_bram
    (wAddr : Signal defaultDomain (BitVec 8))
    (wData : Signal defaultDomain (BitVec 32))
    (wEn : Signal defaultDomain Bool)
    : Signal defaultDomain (BitVec 32) :=
  let state := Signal.loop (dom := defaultDomain) (α := BitVec 8 × BitVec 32)
    fun (self : Signal defaultDomain (BitVec 8 × BitVec 32)) =>
    let addr := Signal.fst self
    let acc := Signal.snd self
    let readData := Signal.memoryComboRead wAddr wData wEn addr
    let nextAddr : Signal defaultDomain (BitVec 8) :=
      addr + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))
    let nextAcc : Signal defaultDomain (BitVec 32) := acc + readData
    bundle2 (Signal.register 0#8 nextAddr) (Signal.register 0#32 nextAcc)
  Signal.snd state

#synthesizeVerilog synth_loop_bram
