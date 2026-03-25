/-
  AXI4-Lite Bus Protocol — Formal Properties

  Pure state-machine model of an AXI4-Lite slave handshake controller,
  together with formal proofs of:

  Safety     — mutual exclusion of response channels, no spurious signals
  Compliance — valid persistence (AXI spec A3.3.1), ready-only-in-idle
  Liveness   — every transaction produces a response, deadlock-freedom
  Fairness   — write priority on simultaneous requests, no data loss

  Reference: ARM AMBA AXI4-Lite Protocol Specification (IHI 0022E)

  Pattern follows ArbiterProps.lean: self-contained definitions + proofs,
  no cross-library dependencies.
-/

namespace Sparkle.IP.Bus.AXI4Lite.Props

/-- AXI4-Lite slave FSM states -/
inductive SlaveState where
  | Idle       -- Waiting for transaction
  | WriteResp  -- Write complete, BVALID asserted, waiting BREADY
  | ReadResp   -- Read complete, RVALID asserted, waiting RREADY
  deriving DecidableEq, Repr, BEq, Inhabited

open SlaveState

/-- Channel handshake inputs to the slave -/
structure SlaveInputs where
  awvalid : Bool  -- Write address channel valid
  wvalid  : Bool  -- Write data channel valid
  bready  : Bool  -- Write response channel ready (from master)
  arvalid : Bool  -- Read address channel valid
  rready  : Bool  -- Read data channel ready (from master)
  deriving DecidableEq, Repr, BEq, Inhabited

/--
  Next-state function for AXI4-Lite slave handshake FSM.

  - Idle: Accept write (AW+W simultaneous) or read (AR).
    Write has priority when both arrive in the same cycle.
  - WriteResp: Hold BVALID until BREADY, then return to Idle.
  - ReadResp: Hold RVALID until RREADY, then return to Idle.
-/
def slaveNextState (s : SlaveState) (i : SlaveInputs) : SlaveState :=
  match s with
  | Idle =>
    if i.awvalid && i.wvalid then WriteResp
    else if i.arvalid then ReadResp
    else Idle
  | WriteResp => if i.bready then Idle else WriteResp
  | ReadResp  => if i.rready then Idle else ReadResp

/-- AWREADY: slave accepts write address (only in Idle) -/
def awready : SlaveState → Bool
  | Idle => true
  | _    => false

/-- WREADY: slave accepts write data (only in Idle) -/
def wready : SlaveState → Bool
  | Idle => true
  | _    => false

/-- ARREADY: slave accepts read address (Idle, and no write pending) -/
def arready (s : SlaveState) (i : SlaveInputs) : Bool :=
  match s with
  | Idle => !(i.awvalid && i.wvalid)
  | _    => false

/-- BVALID: write response valid (only in WriteResp) -/
def bvalid : SlaveState → Bool
  | WriteResp => true
  | _         => false

/-- RVALID: read response valid (only in ReadResp) -/
def rvalid : SlaveState → Bool
  | ReadResp => true
  | _        => false

/-! ## Safety Properties -/

/--
  Mutual exclusion: BVALID and RVALID are never both asserted.
  The slave never drives both response channels simultaneously.
-/
theorem mutual_exclusion (s : SlaveState) :
    ¬(bvalid s ∧ rvalid s) := by
  cases s <;> simp [bvalid, rvalid]

/--
  No spurious BVALID: write response is only asserted in WriteResp state.
-/
theorem no_spurious_bvalid (s : SlaveState) :
    bvalid s = true ↔ s = WriteResp := by
  cases s <;> simp [bvalid]

/--
  No spurious RVALID: read response is only asserted in ReadResp state.
-/
theorem no_spurious_rvalid (s : SlaveState) :
    rvalid s = true ↔ s = ReadResp := by
  cases s <;> simp [rvalid]

/--
  Idle means quiet: neither BVALID nor RVALID is asserted in Idle state.
-/
theorem idle_no_valid :
    bvalid Idle = false ∧ rvalid Idle = false := by
  simp [bvalid, rvalid]

/-! ## Protocol Compliance Properties (AXI Spec A3.3.1) -/

/--
  Valid persistence for BVALID: once asserted, BVALID stays high until
  the master acknowledges with BREADY (AXI spec requirement A3.3.1).
-/
theorem valid_persistence_b (i : SlaveInputs) (h : ¬i.bready) :
    slaveNextState WriteResp i = WriteResp := by
  simp [slaveNextState, h]

/--
  Valid persistence for RVALID: once asserted, RVALID stays high until
  the master acknowledges with RREADY (AXI spec requirement A3.3.1).
-/
theorem valid_persistence_r (i : SlaveInputs) (h : ¬i.rready) :
    slaveNextState ReadResp i = ReadResp := by
  simp [slaveNextState, h]

/--
  AWREADY and WREADY are only asserted in Idle state.
  The slave does not accept new transactions while processing.
-/
theorem ready_only_in_idle (s : SlaveState) :
    (awready s = true ∨ wready s = true) → s = Idle := by
  cases s <;> simp [awready, wready]

/-! ## Liveness Properties -/

/--
  Write produces response: accepting a write (AWVALID ∧ WVALID in Idle)
  transitions to WriteResp, guaranteeing BVALID on the next cycle.
-/
theorem write_produces_response (i : SlaveInputs)
    (haw : i.awvalid) (hw : i.wvalid) :
    slaveNextState Idle i = WriteResp := by
  simp [slaveNextState, haw, hw]

/--
  Read produces response: accepting a read (ARVALID in Idle, no write)
  transitions to ReadResp, guaranteeing RVALID on the next cycle.
-/
theorem read_produces_response (i : SlaveInputs)
    (har : i.arvalid = true) (hnowr : i.awvalid = false ∨ i.wvalid = false) :
    slaveNextState Idle i = ReadResp := by
  cases hnowr with
  | inl h => simp [slaveNextState, h, har]
  | inr h => simp [slaveNextState, h, har]

/--
  Deadlock-freedom: every response state returns to Idle within 1 cycle
  when the master asserts the corresponding ready signal.
-/
theorem deadlock_free_write (i : SlaveInputs) (h : i.bready) :
    slaveNextState WriteResp i = Idle := by
  simp [slaveNextState, h]

theorem deadlock_free_read (i : SlaveInputs) (h : i.rready) :
    slaveNextState ReadResp i = Idle := by
  simp [slaveNextState, h]

/-! ## Fairness Properties -/

/--
  Write priority: when both write (AWVALID ∧ WVALID) and read (ARVALID)
  arrive simultaneously, write is accepted first.
-/
theorem write_priority (i : SlaveInputs)
    (haw : i.awvalid = true) (hw : i.wvalid = true) (_har : i.arvalid = true) :
    slaveNextState Idle i = WriteResp := by
  simp [slaveNextState, haw, hw]

/--
  No data loss: after a response handshake completes, the slave returns
  to Idle and is immediately ready for the next transaction.
-/
theorem no_data_loss_write (i : SlaveInputs) (h : i.bready) :
    awready (slaveNextState WriteResp i) = true := by
  simp [slaveNextState, h, awready]

theorem no_data_loss_read (i : SlaveInputs) (h : i.rready) :
    awready (slaveNextState ReadResp i) = true := by
  simp [slaveNextState, h, awready]

end Sparkle.IP.Bus.AXI4Lite.Props
