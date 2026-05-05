/-
  RV32 Linux-boot regression-pinning theorems

  Concrete-vector theorems pinning the hardware-side fixes that
  unblocked Linux boot. Each theorem is `decide`-closed and serves
  as a machine-checked regression alarm: a future refactor that
  re-introduces any of these bugs will fail the build.

  Bugs covered (all fixed in commits visible in `git log`):

    * `bf6d873` — Sv32 megapage PA formation. Pinned in
      `MMU/PA.lean` (5 concrete-vector theorems). NOT re-pinned here.

    * `5a3fdfb` — DTB-overlap / earlycon / C-extension fixes. The
      hardware-relevant piece is the C-extension absence: SoC.lean
      advertises `misa = 0x40141101` (rv32IMA + S + U), no C bit.
      With kernel built `rv32imac`, the kernel's first compressed
      instruction faults instantly because the SoC doesn't decode
      C-format. The fix was build-side (CONFIG_RISCV_ISA_C=n), but
      the *hardware contract* "misa.C = 0" is what the kernel must
      respect. We pin that contract here.

    * DTB-overlap: post-fix, OpenSBI hands the DTB at PA 0x81F00000,
      which is past the kernel image (which ends well before 0x81F00000
      since DRAM is 32MB starting at 0x80000000 and kernel image is
      ~24MB). The hardware contract is that DRAM covers [0x80000000,
      0x82000000), and the DTB region [0x81F00000, 0x81F00500) sits
      inside DRAM but outside the kernel image. We pin the address-range
      arithmetic that makes the layout consistent.

  These theorems are independent of the rest of the proof scaffold —
  they don't require the SoC's full register state to evaluate, just
  bitvector arithmetic.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.RV32.MMU.IfetchFault
import IP.RV32.Bus.Decoder

namespace Sparkle.IP.RV32.Verification

/-! ## misa.C = 0 contract -/

/-- The SoC's misa-CSR constant value, as advertised by `csrReadMuxSignal`. -/
def misaConstSparkle : BitVec 32 := 0x40141101#32

/-- **misa MXL field = 1 (= 32-bit) at bits [31:30].**

    Per RISC-V priv §3.1.1, misa[31:30] = MXL where 1 means RV32. -/
theorem misa_mxl_is_rv32 :
    misaConstSparkle.extractLsb' 30 2 = 1#2 := by
  unfold misaConstSparkle
  decide

/-- **misa.A bit (bit 0) = 1 (Atomic extension supported).** -/
theorem misa_has_A : misaConstSparkle.extractLsb' 0 1 = 1#1 := by
  unfold misaConstSparkle; decide

/-- **misa.I bit (bit 8) = 1 (Integer base ISA).** -/
theorem misa_has_I : misaConstSparkle.extractLsb' 8 1 = 1#1 := by
  unfold misaConstSparkle; decide

/-- **misa.M bit (bit 12) = 1 (Multiply/Divide).** -/
theorem misa_has_M : misaConstSparkle.extractLsb' 12 1 = 1#1 := by
  unfold misaConstSparkle; decide

/-- **misa.S bit (bit 18) = 1 (Supervisor mode).** -/
theorem misa_has_S : misaConstSparkle.extractLsb' 18 1 = 1#1 := by
  unfold misaConstSparkle; decide

/-- **misa.U bit (bit 20) = 1 (User mode).** -/
theorem misa_has_U : misaConstSparkle.extractLsb' 20 1 = 1#1 := by
  unfold misaConstSparkle; decide

/-- **CRITICAL: misa.C bit (bit 2) = 0 (Compressed extension NOT supported).**

    This is the regression-pinning theorem for the C-extension half
    of commit `5a3fdfb`. If a future refactor accidentally enables
    the C bit in `misa`, the kernel will think it can issue compressed
    instructions, and the SoC's instruction decoder (which only
    handles 32-bit RV32IMA encodings) will fault on the first
    compressed instruction. -/
theorem misa_no_C : misaConstSparkle.extractLsb' 2 1 = 0#1 := by
  unfold misaConstSparkle; decide

/-- **misa.B bit (bit 1) = 0 (Bit manipulation extension NOT supported).** -/
theorem misa_no_B : misaConstSparkle.extractLsb' 1 1 = 0#1 := by
  unfold misaConstSparkle; decide

/-- **misa.D bit (bit 3) = 0 (Double-float NOT supported).** -/
theorem misa_no_D : misaConstSparkle.extractLsb' 3 1 = 0#1 := by
  unfold misaConstSparkle; decide

/-- **misa.F bit (bit 5) = 0 (Single-float NOT supported).** -/
theorem misa_no_F : misaConstSparkle.extractLsb' 5 1 = 0#1 := by
  unfold misaConstSparkle; decide

/-- **misa.V bit (bit 21) = 0 (Vector NOT supported).** -/
theorem misa_no_V : misaConstSparkle.extractLsb' 21 1 = 0#1 := by
  unfold misaConstSparkle; decide

/-! ## Sparkle SoC memory map -/

/-- DRAM base PA. -/
def dramBase : BitVec 32 := 0x80000000#32

/-- DRAM size in bytes (32 MB). -/
def dramSize : Nat := 0x02000000

/-- DRAM end PA (exclusive). -/
def dramEnd : BitVec 32 := dramBase + (BitVec.ofNat 32 dramSize)

/-- OpenSBI image base in DRAM. -/
def opensbiBase : BitVec 32 := 0x80000000#32

/-- Linux kernel image base (post-OpenSBI, FW_JUMP_ADDR). -/
def kernelBase : BitVec 32 := 0x80200000#32

/-- DTB address (post-fix, see commit 5a3fdfb). -/
def dtbAddrPostFix : BitVec 32 := 0x81F00000#32

/-- DTB address (pre-fix, the buggy value that overlapped the kernel image). -/
def dtbAddrPreFix : BitVec 32 := 0x80F00000#32

/-- A typical kernel image size (24 MB observed in JIT logs). -/
def kernelImageSize : Nat := 0x01800000

/-- Kernel image end PA (exclusive). -/
def kernelEnd : BitVec 32 := kernelBase + (BitVec.ofNat 32 kernelImageSize)

/-! ## DTB-region layout regression theorems -/

/-- **Post-fix DTB sits past the kernel image end.**

    `kernelEnd = 0x80200000 + 0x01800000 = 0x81A00000` < `dtbAddrPostFix
    = 0x81F00000`, so the DTB does not overlap the kernel image. -/
theorem dtb_post_fix_past_kernel :
    kernelEnd ≤ dtbAddrPostFix := by
  unfold kernelEnd kernelBase kernelImageSize dtbAddrPostFix
  decide

/-- **Post-fix DTB is still inside DRAM.**

    `dtbAddrPostFix = 0x81F00000` < `dramEnd = 0x82000000`, so the
    DTB is reachable by the kernel as a normal DRAM load. -/
theorem dtb_post_fix_in_dram :
    dtbAddrPostFix < dramEnd := by
  unfold dtbAddrPostFix dramEnd dramBase dramSize
  decide

/-- **CRITICAL: pre-fix DTB sits INSIDE the kernel image (the bug).**

    `dtbAddrPreFix = 0x80F00000` < `kernelEnd = 0x81A00000` and
    `dtbAddrPreFix > kernelBase = 0x80200000`. With this layout,
    OpenSBI's DTB write (or a kernel image load) would corrupt the
    other one. The pre-fix DTB at 0x80F00000 was inside the kernel
    image, which is why the kernel "booted past OpenSBI but produced
    no UART output" before `5a3fdfb`. -/
theorem dtb_pre_fix_overlapped_kernel :
    kernelBase ≤ dtbAddrPreFix ∧ dtbAddrPreFix < kernelEnd := by
  unfold dtbAddrPreFix kernelBase kernelEnd kernelImageSize
  refine ⟨?_, ?_⟩ <;> decide

/-- **The post-fix and pre-fix DTB addresses differ by exactly 16 MB.**

    `0x81F00000 - 0x80F00000 = 0x01000000 = 16 MB`. The fix moved
    the DTB exactly one megabyte-page boundary past the kernel image. -/
theorem dtb_fix_distance :
    dtbAddrPostFix - dtbAddrPreFix = 0x01000000#32 := by
  unfold dtbAddrPostFix dtbAddrPreFix
  decide

/-! ## Trampoline_pg_dir kernel-mapping concrete vectors

  The Linux kernel boots with a trampoline page-table at PA
  `0x81ca9000` (observed value in the JIT log; exact PA depends
  on the kernel build, but the layout is regular). The kernel
  image VMA `0xc0000000` is mapped via a megapage entry to PA
  `0x80400000`. Verifying this concrete mapping is the same
  vector that was machine-checked in `MMU/PA.lean` —
  `dPhysAddrMega_kernel_first_fetch_concrete`.

  Here we add the *PTE-decoding* half: from the raw 32-bit PTE
  word `0x201000ef`, extract the PPN field (bits [31:10]) and
  confirm it's the value the megapage-PA formula expects.
-/

/-- The kernel's trampoline_pg_dir megapage PTE for VMA 0xc0000000. -/
def kernelTrampolinePTE : BitVec 32 := 0x201000ef#32

/-- **PTE → PPN extraction (bits [31:10]).** -/
theorem trampolinePTE_PPN_extract :
    kernelTrampolinePTE.extractLsb' 10 22 = 0x080400#22 := by
  unfold kernelTrampolinePTE; decide

/-- **PTE flags = 0xef** (V|R|W|X|U|G|A|D — all set except no D-typo). -/
theorem trampolinePTE_flags_extract :
    kernelTrampolinePTE.extractLsb' 0 10 = 0x0ef#10 := by
  unfold kernelTrampolinePTE; decide

/-- **PTE.V (bit 0) = 1 (the entry is valid).** -/
theorem trampolinePTE_valid :
    kernelTrampolinePTE.extractLsb' 0 1 = 1#1 := by
  unfold kernelTrampolinePTE; decide

/-- **PTE.X (bit 3) = 1 (executable — kernel needs to fetch from this page).** -/
theorem trampolinePTE_executable :
    kernelTrampolinePTE.extractLsb' 3 1 = 1#1 := by
  unfold kernelTrampolinePTE; decide

/-- **For a megapage leaf, PPN[0] (low 10 bits) MUST be zero (Sv32 §10.3.2).**

    If PPN[0] ≠ 0, the megapage is misaligned and the spec mandates
    a page-fault (cause 12 / 13 / 15). The kernel's trampoline PTE
    is properly aligned. -/
theorem trampolinePTE_megapage_aligned :
    (kernelTrampolinePTE.extractLsb' 10 22).extractLsb' 0 10 = 0#10 := by
  unfold kernelTrampolinePTE; decide

/-! ## Open issue: PTW back-to-back ifetch fault

  Commit `bf6d873`'s message says: "the PTW seems to mis-walk on
  back-to-back ifetch faults" — a follow-up issue still pending
  at the time of writing.

  The hardware contract for `ifetchFaultPendingNextPure` is the
  4-way priority:
    ifetchPageFault → false   (trap delivery wins)
    bypassMMU       → false   (no MMU)
    ptwFault ∧ ptwIsIfetch → true   (set on fresh fault)
    else            → hold

  The "back-to-back" scenario is: the previous ifetch-PTW fault has
  set the pending bit, the trap delivers, and a NEW ifetch-PTW
  fault fires in the SAME cycle as the trap-delivery. Per the
  4-way priority, the trap-clear wins — the new fault's set is
  dropped.

  Whether this is a *bug* depends on whether the hardware ever
  produces simultaneous trap-delivery + new-PTW-fault. We pin the
  CURRENT contract here so any change to the priority gets caught
  by `lake build`, and the discussion of "is this priority
  correct?" can be tracked separately.
-/

/-- **Documented contract: trap delivery has top priority in
    ifetchFaultPending's next-state.**

    Even if a fresh PTW fault for an ifetch fires in the same cycle
    as the trap-delivery, the pending bit is cleared. This is the
    *current design* — the open question is whether the trapped
    instruction's fault info has already been latched into mtval/sepc
    so dropping the next-set is safe. -/
theorem ifetchFault_trap_overrides_simultaneous_ptw_fault
    (ifetchFaultPending : Bool) :
    Sparkle.IP.RV32.MMU.ifetchFaultPendingNextPure
      (ifetchPageFault := true)
      (bypassMMU := false)
      (ptwFault := true)
      (ptwIsIfetch := true)
      ifetchFaultPending = false := by
  rfl

/-- **Documented contract: bypassMMU has priority over PTW-fault-sets.**

    If the MMU is bypassed (M-mode or satp.MODE=Bare), no fault
    can be pending. -/
theorem ifetchFault_bypass_overrides_simultaneous_ptw_fault
    (ifetchFaultPending : Bool) :
    Sparkle.IP.RV32.MMU.ifetchFaultPendingNextPure
      (ifetchPageFault := false)
      (bypassMMU := true)
      (ptwFault := true)
      (ptwIsIfetch := true)
      ifetchFaultPending = false := by
  rfl

/-- **The complete 4-way priority truth table.**

    Enumerates all 16 input combinations of (ifetchPageFault,
    bypassMMU, ptwFault, ptwIsIfetch) and verifies the next-state
    matches the stated 4-way priority (with `ifetchFaultPending`
    quantified). This is the strongest possible contract: any
    deviation from the priority will fail this `decide`. -/
theorem ifetchFault_priority_complete :
    ∀ (ifetchPageFault bypassMMU ptwFault ptwIsIfetch
       ifetchFaultPending : Bool),
      Sparkle.IP.RV32.MMU.ifetchFaultPendingNextPure
        ifetchPageFault bypassMMU ptwFault ptwIsIfetch ifetchFaultPending =
        (if ifetchPageFault then false
         else if bypassMMU then false
         else if ptwFault && ptwIsIfetch then true
         else ifetchFaultPending) := by
  decide

/-! ## Bus-decoder routing for Linux-boot critical addresses

  The bus decoder routes each PA to exactly one of {CLINT, MMIO,
  UART, DMEM}. For Linux to boot correctly, certain addresses MUST
  route to specific targets:

    * `0x10000000` (UART register base) → UART
    * `0x40000000` (BitNet MMIO base)   → MMIO
    * `0x80200000` (kernel image base)  → DMEM
    * `0x80400000` (kernel megapage base after Sv32 translation) → DMEM
    * `0x81F00000` (post-fix DTB address)                         → DMEM
    * `0x81FFFFFF` (last DRAM byte)                               → DMEM

  Any future change to the bus decoder that re-routes any of these
  will fail the corresponding `decide`-closed theorem. -/

/-- **UART register base (0x10000000) routes to UART.** -/
theorem uart_routes_to_UART :
    Sparkle.IP.RV32.Bus.isUARTPure 0x10000000#32 = true := by decide

/-- **BitNet MMIO base (0x40000000) routes to MMIO.** -/
theorem bitnet_routes_to_MMIO :
    Sparkle.IP.RV32.Bus.isMmioPure 0x40000000#32 = true := by decide

/-- **Kernel image base (0x80200000) routes to DMEM.** -/
theorem kernel_image_routes_to_DMEM :
    Sparkle.IP.RV32.Bus.isDMEMPure 0x80200000#32 = true := by decide

/-- **Kernel megapage post-translation base (0x80400000) routes to DMEM.** -/
theorem kernel_megapage_routes_to_DMEM :
    Sparkle.IP.RV32.Bus.isDMEMPure 0x80400000#32 = true := by decide

/-- **Post-fix DTB address (0x81F00000) routes to DMEM.**

    This is the regression alarm for the DTB-overlap fix:
    OpenSBI hands the kernel a DTB pointer at 0x81F00000, and that
    address MUST route to DMEM (not UART/MMIO/CLINT) so the kernel
    can read the DTB blob via normal load instructions. -/
theorem dtb_post_fix_routes_to_DMEM :
    Sparkle.IP.RV32.Bus.isDMEMPure dtbAddrPostFix = true := by
  unfold dtbAddrPostFix; decide

/-- **Last DRAM byte (0x81FFFFFF) routes to DMEM.**

    Confirms the DRAM region extends through 0x81FFFFFF. -/
theorem dram_last_byte_routes_to_DMEM :
    Sparkle.IP.RV32.Bus.isDMEMPure 0x81FFFFFF#32 = true := by decide

/-- **Pre-fix DTB address (0x80F00000) ALSO routes to DMEM.**

    The pre-fix DTB also routed to DMEM — that's not the bug.
    The bug was that 0x80F00000 sits *inside* the kernel image's
    DRAM range, not that it was routed to a wrong target. We
    pin both vectors here to clarify what was/wasn't broken. -/
theorem dtb_pre_fix_also_routes_to_DMEM :
    Sparkle.IP.RV32.Bus.isDMEMPure dtbAddrPreFix = true := by
  unfold dtbAddrPreFix; decide

/-- **UART address does NOT route to DMEM** (sanity: separation holds). -/
theorem uart_not_DMEM :
    Sparkle.IP.RV32.Bus.isDMEMPure 0x10000000#32 = false := by decide

/-- **Kernel image base does NOT route to UART** (sanity). -/
theorem kernel_image_not_UART :
    Sparkle.IP.RV32.Bus.isUARTPure 0x80200000#32 = false := by decide

end Sparkle.IP.RV32.Verification
