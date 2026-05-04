/-
  RV32 bus read-data mux — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (lines 814..816). The
  WB-stage bus read-data mux selects which peripheral's
  rdata to forward, based on the WB-stage address decode.

  Spec:

      busRdataRaw =
        if isCLINT_wb then clintRdata
        else if isUART_wb then uartRdata
        else if is_mmio_wb then mmioRdata
        else dmemRdataFwd          -- DMEM is the catch-all

  Companion to:
    * `Bus/Decoder.lean` (commit 3d7acf8) — proves the four
      target predicates are mutex + exhaustive.
    * `Bus/PeripheralWE.lean` (commit 6cae0b7) — proves writes
      are also mutex.

  Together with the decoder mutex, this priority cascade is
  also a "at most one fires" decoder — the priority order
  doesn't matter for correctness when the predicates are
  already mutex.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Bus

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Pure 4-way bus rdata mux -/

/-- 4-way priority mux. Default = DMEM (the bus-decoder catch-all). -/
@[inline] def busRdataRawPure
    (isCLINT_wb : Bool) (clintRdata : BitVec 32)
    (isUART_wb : Bool) (uartRdata : BitVec 32)
    (is_mmio_wb : Bool) (mmioRdata : BitVec 32)
    (dmemRdataFwd : BitVec 32) : BitVec 32 :=
  if isCLINT_wb then clintRdata
  else if isUART_wb then uartRdata
  else if is_mmio_wb then mmioRdata
  else dmemRdataFwd

/-! ## Spec invariants — closed by `rfl` -/

/-- CLINT match: returns clintRdata. -/
@[simp] theorem busRdataRaw_clint
    (clintRdata : BitVec 32) (isUART_wb : Bool) (uartRdata : BitVec 32)
    (is_mmio_wb : Bool) (mmioRdata dmemRdataFwd : BitVec 32) :
    busRdataRawPure true clintRdata isUART_wb uartRdata
      is_mmio_wb mmioRdata dmemRdataFwd = clintRdata := by rfl

/-- UART match (no CLINT): returns uartRdata. -/
@[simp] theorem busRdataRaw_uart
    (clintRdata uartRdata : BitVec 32) (is_mmio_wb : Bool)
    (mmioRdata dmemRdataFwd : BitVec 32) :
    busRdataRawPure false clintRdata true uartRdata
      is_mmio_wb mmioRdata dmemRdataFwd = uartRdata := by rfl

/-- MMIO match (no CLINT/UART): returns mmioRdata. -/
@[simp] theorem busRdataRaw_mmio
    (clintRdata uartRdata mmioRdata dmemRdataFwd : BitVec 32) :
    busRdataRawPure false clintRdata false uartRdata
      true mmioRdata dmemRdataFwd = mmioRdata := by rfl

/-- DMEM (default): returns dmemRdataFwd. -/
@[simp] theorem busRdataRaw_dmem
    (clintRdata uartRdata mmioRdata dmemRdataFwd : BitVec 32) :
    busRdataRawPure false clintRdata false uartRdata
      false mmioRdata dmemRdataFwd = dmemRdataFwd := by rfl

/-! ## Composite spec -/

theorem busRdataRawPure_spec
    (isCLINT_wb : Bool) (clintRdata : BitVec 32)
    (isUART_wb : Bool) (uartRdata : BitVec 32)
    (is_mmio_wb : Bool) (mmioRdata dmemRdataFwd : BitVec 32) :
    busRdataRawPure isCLINT_wb clintRdata isUART_wb uartRdata
       is_mmio_wb mmioRdata dmemRdataFwd =
      (if isCLINT_wb then clintRdata
       else if isUART_wb then uartRdata
       else if is_mmio_wb then mmioRdata
       else dmemRdataFwd) := by rfl

/-! ## Signal-level wrapper -/

def busRdataRawSignal {dom : DomainConfig}
    (isCLINT_wb : Signal dom Bool) (clintRdata : Signal dom (BitVec 32))
    (isUART_wb : Signal dom Bool) (uartRdata : Signal dom (BitVec 32))
    (is_mmio_wb : Signal dom Bool) (mmioRdata dmemRdataFwd : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  Signal.mux isCLINT_wb clintRdata
    (Signal.mux isUART_wb uartRdata
    (Signal.mux is_mmio_wb mmioRdata dmemRdataFwd))

end Sparkle.IP.RV32.Bus
