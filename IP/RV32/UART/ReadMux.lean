/-
  RV32 UART 8250 read mux — Signal-level wrapper + spec

  The UART read mux in `IP/RV32/SoC.lean` (~line 780..811) is a
  7-way priority cascade producing `uartRdata`. The DLAB-aware
  aliasing applies to offsets 0 and 1.

  Spec (per 8250 register layout):

    offset  DLAB=0          DLAB=1
    0       RBR (read-only) DLL
    1       IER             DLM
    2       IIR             —     (always 0x01: "no interrupt")
    3       LCR             LCR
    4       MCR             MCR
    5       LSR             —     (always 0x60: TX always ready)
    6       MSR             —     (we don't expose)
    7       SCR             SCR
    other                          (returns 0)

  In Sparkle:
    * RBR returns 0 (no RX path).
    * LSR returns 0x60 = bit 5 (THRE = TX holding empty) + bit 6
      (TEMT = TX empty), modeling a TX-always-ready endpoint.
    * IIR returns 0x01 = "no interrupt pending" (we don't model
      interrupts on the UART).
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.UART

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## UART read constants (per 8250 spec) -/

/-- IIR's "no interrupt" value. -/
def uartIIRNoIrq : BitVec 32 := 0x00000001#32

/-- LSR's "TX always ready" value: THRE (bit 5) | TEMT (bit 6). -/
def uartLSRTxReady : BitVec 32 := 0x00000060#32

/-! ## Pure offset-0/1 reads (DLAB-aware) -/

/-- offset-0 read: DLAB=1 → DLL, else RBR (=0). -/
@[inline] def uartRd0Pure (uartDLAB : Bool) (uartDLL : BitVec 8) : BitVec 32 :=
  if uartDLAB then (0#24 : BitVec 24) ++ uartDLL
  else 0#32

/-- offset-1 read: DLAB=1 → DLM, else IER. -/
@[inline] def uartRd1Pure
    (uartDLAB : Bool) (uartDLM uartIER : BitVec 8) : BitVec 32 :=
  if uartDLAB then (0#24 : BitVec 24) ++ uartDLM
  else (0#24 : BitVec 24) ++ uartIER

/-! ## Pure 7-way read mux -/

/-- 7-way UART read priority mux. Default = 0 for unused offsets. -/
@[inline] def uartRdataPure
    (offset : BitVec 3) (uartDLAB : Bool)
    (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8)
    : BitVec 32 :=
  if offset == 0#3 then uartRd0Pure uartDLAB uartDLL
  else if offset == 1#3 then uartRd1Pure uartDLAB uartDLM uartIER
  else if offset == 2#3 then uartIIRNoIrq
  else if offset == 3#3 then (0#24 : BitVec 24) ++ uartLCR
  else if offset == 4#3 then (0#24 : BitVec 24) ++ uartMCR
  else if offset == 5#3 then uartLSRTxReady
  else if offset == 7#3 then (0#24 : BitVec 24) ++ uartSCR
  else 0#32

/-! ## Spec invariants — closed by `bv_decide` / `rfl` -/

/-- offset 0 with DLAB=1 reads DLL. -/
@[simp] theorem uartRdata_off0_dlab
    (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 0#3 true uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = (0#24 : BitVec 24) ++ uartDLL := by rfl

/-- offset 0 with DLAB=0 reads RBR (= 0). -/
@[simp] theorem uartRdata_off0_no_dlab
    (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 0#3 false uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = 0#32 := by rfl

/-- offset 1 with DLAB=1 reads DLM. -/
@[simp] theorem uartRdata_off1_dlab
    (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 1#3 true uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = (0#24 : BitVec 24) ++ uartDLM := by rfl

/-- offset 1 with DLAB=0 reads IER. -/
@[simp] theorem uartRdata_off1_no_dlab
    (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 1#3 false uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = (0#24 : BitVec 24) ++ uartIER := by rfl

/-- offset 2 → IIR (no IRQ). -/
@[simp] theorem uartRdata_off2
    (uartDLAB : Bool) (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 2#3 uartDLAB uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = uartIIRNoIrq := by
  unfold uartRdataPure
  cases uartDLAB <;> rfl

/-- offset 3 → LCR. -/
@[simp] theorem uartRdata_off3
    (uartDLAB : Bool) (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 3#3 uartDLAB uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = (0#24 : BitVec 24) ++ uartLCR := by
  unfold uartRdataPure
  cases uartDLAB <;> rfl

/-- offset 4 → MCR. -/
@[simp] theorem uartRdata_off4
    (uartDLAB : Bool) (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 4#3 uartDLAB uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = (0#24 : BitVec 24) ++ uartMCR := by
  unfold uartRdataPure
  cases uartDLAB <;> rfl

/-- offset 5 → LSR (TX always ready). -/
@[simp] theorem uartRdata_off5
    (uartDLAB : Bool) (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 5#3 uartDLAB uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = uartLSRTxReady := by
  unfold uartRdataPure
  cases uartDLAB <;> rfl

/-- offset 7 → SCR. -/
@[simp] theorem uartRdata_off7
    (uartDLAB : Bool) (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 7#3 uartDLAB uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = (0#24 : BitVec 24) ++ uartSCR := by
  unfold uartRdataPure
  cases uartDLAB <;> rfl

/-- offset 6 → 0 (MSR not exposed). -/
@[simp] theorem uartRdata_off6
    (uartDLAB : Bool) (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : BitVec 8) :
    uartRdataPure 6#3 uartDLAB uartDLL uartDLM uartIER uartLCR uartMCR uartSCR
      = 0#32 := by
  unfold uartRdataPure
  cases uartDLAB <;> rfl

/-! ## LSR bits — TX-always-ready spec -/

/-- LSR has THRE (bit 5) set. -/
theorem uartLSR_THRE_set :
    uartLSRTxReady.extractLsb' 5 1 = 1#1 := by
  unfold uartLSRTxReady
  bv_decide

/-- LSR has TEMT (bit 6) set. -/
theorem uartLSR_TEMT_set :
    uartLSRTxReady.extractLsb' 6 1 = 1#1 := by
  unfold uartLSRTxReady
  bv_decide

/-- IIR has bit 0 = 1 ("no interrupt pending"). -/
theorem uartIIR_no_irq_bit :
    uartIIRNoIrq.extractLsb' 0 1 = 1#1 := by
  unfold uartIIRNoIrq
  bv_decide

/-! ## Signal-level wrapper -/

def uartRdataSignal {dom : DomainConfig}
    (offset : Signal dom (BitVec 3)) (uartDLAB : Signal dom Bool)
    (uartDLL uartDLM uartIER uartLCR uartMCR uartSCR : Signal dom (BitVec 8))
    : Signal dom (BitVec 32) :=
  let zero24 : Signal dom (BitVec 24) := Signal.pure 0#24
  let zero32 : Signal dom (BitVec 32) := Signal.pure 0#32
  let iir : Signal dom (BitVec 32) := Signal.pure uartIIRNoIrq
  let lsr : Signal dom (BitVec 32) := Signal.pure uartLSRTxReady
  let rd0 := Signal.mux uartDLAB (zero24 ++ uartDLL) zero32
  let rd1 := Signal.mux uartDLAB (zero24 ++ uartDLM) (zero24 ++ uartIER)
  Signal.mux (offset === 0#3) rd0
    (Signal.mux (offset === 1#3) rd1
    (Signal.mux (offset === 2#3) iir
    (Signal.mux (offset === 3#3) (zero24 ++ uartLCR)
    (Signal.mux (offset === 4#3) (zero24 ++ uartMCR)
    (Signal.mux (offset === 5#3) lsr
    (Signal.mux (offset === 7#3) (zero24 ++ uartSCR) zero32))))))

end Sparkle.IP.RV32.UART
