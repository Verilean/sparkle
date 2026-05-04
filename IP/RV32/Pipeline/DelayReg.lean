/-
  RV32 1-cycle delay register — sequential lemma

  Generic form for `Signal.register init x.val (t+1) = x.val t`
  used by:

    * `flushDelay` (= `Signal.register false flush`)
    * `stallDelay` (= `Signal.register false ifetchStall`)
    * `prev_wb_addr/data/en` (= `Signal.register init wb_*`)

  These are all "pure 1-cycle delay" registers — no mux, no
  conditional update — just `register init x`. The cycle-wise
  semantics is:

      reg.val 0       = init
      reg.val (t+1)   = x.val t

  This module captures the second equation as named lemmas at
  Bool, BitVec 5, BitVec 32, and generic widths.
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Generic 1-cycle delay register -/

/-- 1-cycle delay register at any type. -/
def delayRegSignal {dom : DomainConfig} {α : Type}
    (init : α) (x : Signal dom α) : Signal dom α :=
  Signal.register init x

/-- **Generic delay-register: reg.val (t+1) = x.val t.** -/
@[simp] theorem delayReg_step {dom : DomainConfig} {α : Type}
    (init : α) (x : Signal dom α) (t : Nat) :
    (delayRegSignal init x).val (t + 1) = x.val t := by
  unfold delayRegSignal
  -- Signal.register's t+1-cycle definition is x.val t.
  show (Signal.register init x).val (t + 1) = x.val t
  rfl

/-- At cycle 0, the delay register holds its init. -/
@[simp] theorem delayReg_init {dom : DomainConfig} {α : Type}
    (init : α) (x : Signal dom α) :
    (delayRegSignal init x).val 0 = init := by
  unfold delayRegSignal
  show (Signal.register init x).val 0 = init
  rfl

/-! ## Specialized aliases for common widths -/

/-- flushDelay = register false flush. -/
def flushDelayRegSignal {dom : DomainConfig}
    (flush : Signal dom Bool) : Signal dom Bool :=
  delayRegSignal false flush

theorem flushDelayReg_step {dom : DomainConfig}
    (flush : Signal dom Bool) (t : Nat) :
    (flushDelayRegSignal flush).val (t + 1) = flush.val t :=
  delayReg_step false flush t

/-- stallDelay = register false ifetchStall. -/
def stallDelayRegSignal {dom : DomainConfig}
    (ifetchStall : Signal dom Bool) : Signal dom Bool :=
  delayRegSignal false ifetchStall

theorem stallDelayReg_step {dom : DomainConfig}
    (ifetchStall : Signal dom Bool) (t : Nat) :
    (stallDelayRegSignal ifetchStall).val (t + 1) = ifetchStall.val t :=
  delayReg_step false ifetchStall t

/-- prev_wb_addr = register 0#5 wb_addr. -/
def prevWbAddrRegSignal {dom : DomainConfig}
    (wb_addr : Signal dom (BitVec 5)) : Signal dom (BitVec 5) :=
  delayRegSignal 0#5 wb_addr

theorem prevWbAddrReg_step {dom : DomainConfig}
    (wb_addr : Signal dom (BitVec 5)) (t : Nat) :
    (prevWbAddrRegSignal wb_addr).val (t + 1) = wb_addr.val t :=
  delayReg_step 0#5 wb_addr t

/-- prev_wb_data = register 0#32 wb_data. -/
def prevWbDataRegSignal {dom : DomainConfig}
    (wb_data : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  delayRegSignal 0#32 wb_data

theorem prevWbDataReg_step {dom : DomainConfig}
    (wb_data : Signal dom (BitVec 32)) (t : Nat) :
    (prevWbDataRegSignal wb_data).val (t + 1) = wb_data.val t :=
  delayReg_step 0#32 wb_data t

/-- prev_wb_en = register false wb_en. -/
def prevWbEnRegSignal {dom : DomainConfig}
    (wb_en : Signal dom Bool) : Signal dom Bool :=
  delayRegSignal false wb_en

theorem prevWbEnReg_step {dom : DomainConfig}
    (wb_en : Signal dom Bool) (t : Nat) :
    (prevWbEnRegSignal wb_en).val (t + 1) = wb_en.val t :=
  delayReg_step false wb_en t

/-- prevStoreData = register 0#32 ex_rs2. -/
def prevStoreDataRegSignal {dom : DomainConfig}
    (ex_rs2 : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  delayRegSignal 0#32 ex_rs2

theorem prevStoreDataReg_step {dom : DomainConfig}
    (ex_rs2 : Signal dom (BitVec 32)) (t : Nat) :
    (prevStoreDataRegSignal ex_rs2).val (t + 1) = ex_rs2.val t :=
  delayReg_step 0#32 ex_rs2 t

end Sparkle.IP.RV32.Pipeline
