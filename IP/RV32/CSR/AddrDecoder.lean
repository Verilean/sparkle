/-
  RV32 CSR address decoder — pure logic + invariants

  Extracted from `IP/RV32/SoC.lean` (~lines 914..938). The 28
  inline CSR address predicates (`csrIsMstatus`, `csrIsMie`, ...)
  all share the same shape:

      csrIsXyz = (csrAddr == xyzAddr)

  This file packages them as instances of a single generic
  `csrAddrEqPure` and proves the structural invariant that any
  two distinct expected addresses produce mutex predicates.

  CSR addresses (per RISC-V priv §3.1, §4.1, §6):

    M-mode trap:    0x300 mstatus, 0x304 mie, 0x305 mtvec, 0x340..0x344
    M-mode info:    0x301 misa, 0xF14 mhartid
    M-mode deleg:   0x302 medeleg, 0x303 mideleg
    M-mode cnt-en:  0x306 mcounteren
    S-mode trap:    0x100 sstatus, 0x104 sie, 0x105 stvec, 0x140..0x144
    S-mode atp:     0x180 satp
    S-mode cnt-en:  0x106 scounteren
    Counter:        0xC00 cycle, 0xC01 time, 0xC80 cycleh, 0xC81 timeh
-/

import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.IP.RV32.CSR

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ## Generic equality predicate -/

/-- True iff `csrAddr == expected`. -/
@[inline] def csrAddrEqPure (csrAddr expected : BitVec 12) : Bool :=
  csrAddr == expected

/-! ## Mutex theorem

  This is the key invariant: if two predicates check different
  expected addresses, they cannot both fire on the same csrAddr. -/

/-- For any csrAddr, two distinct expected addresses produce mutex
    predicates. The proof: if csrAddr matches both exp1 and exp2,
    then exp1 = exp2 (transitivity), contradicting `h`. -/
theorem csrAddrEq_mutex
    (csrAddr exp1 exp2 : BitVec 12) (h : exp1 ≠ exp2) :
    !(csrAddrEqPure csrAddr exp1 && csrAddrEqPure csrAddr exp2) = true := by
  unfold csrAddrEqPure
  -- The `&&` is true iff both `==` are true iff csrAddr = exp1 ∧ csrAddr = exp2.
  -- That implies exp1 = exp2, contradicting `h`. Encode as: the goal is
  -- !(A && B) = true, equivalently (A && B) = false. We split on each `==`.
  cases h1 : csrAddr == exp1
  · -- LHS false → !(false && _) = !false = true
    simp [h1]
  · cases h2 : csrAddr == exp2
    · simp [h2]
    · -- Both true → csrAddr = exp1 ∧ csrAddr = exp2 ⇒ contradiction
      exfalso
      have e1 : csrAddr = exp1 := by
        revert h1; cases h1' : csrAddr == exp1
        · intro h_; cases h_
        · intro _; bv_decide
      have e2 : csrAddr = exp2 := by
        revert h2; cases h2' : csrAddr == exp2
        · intro h_; cases h_
        · intro _; bv_decide
      exact h (e1.symm.trans e2)

/-! ## CSR address constants

  Naming each address as a `def` documents the spec layout and
  enables future invariants to refer to them by name. -/

/-- mstatus = 0x300. -/
def csrAddrMstatus  : BitVec 12 := 0x300#12
def csrAddrMisa     : BitVec 12 := 0x301#12
def csrAddrMedeleg  : BitVec 12 := 0x302#12
def csrAddrMideleg  : BitVec 12 := 0x303#12
def csrAddrMie      : BitVec 12 := 0x304#12
def csrAddrMtvec    : BitVec 12 := 0x305#12
def csrAddrMcounteren : BitVec 12 := 0x306#12
def csrAddrMscratch : BitVec 12 := 0x340#12
def csrAddrMepc     : BitVec 12 := 0x341#12
def csrAddrMcause   : BitVec 12 := 0x342#12
def csrAddrMtval    : BitVec 12 := 0x343#12
def csrAddrMip      : BitVec 12 := 0x344#12
def csrAddrMhartid  : BitVec 12 := 0xF14#12
def csrAddrSstatus  : BitVec 12 := 0x100#12
def csrAddrSie      : BitVec 12 := 0x104#12
def csrAddrStvec    : BitVec 12 := 0x105#12
def csrAddrScounteren : BitVec 12 := 0x106#12
def csrAddrSscratch : BitVec 12 := 0x140#12
def csrAddrSepc     : BitVec 12 := 0x141#12
def csrAddrScause   : BitVec 12 := 0x142#12
def csrAddrStval    : BitVec 12 := 0x143#12
def csrAddrSip      : BitVec 12 := 0x144#12
def csrAddrSatp     : BitVec 12 := 0x180#12
def csrAddrCycle    : BitVec 12 := 0xC00#12
def csrAddrTime     : BitVec 12 := 0xC01#12
def csrAddrCycleh   : BitVec 12 := 0xC80#12
def csrAddrTimeh    : BitVec 12 := 0xC81#12

/-! ## Sample mutex theorems

  Demonstrate the generic mutex applied to specific pairs. We
  don't enumerate all C(28,2) = 378 pairs explicitly — the
  generic `csrAddrEq_mutex` covers them all when supplied with
  a proof that the two addresses differ. -/

/-- mstatus and mie are distinct addresses. -/
theorem mstatus_ne_mie : csrAddrMstatus ≠ csrAddrMie := by decide

/-- mstatus and satp are distinct (different mode CSRs). -/
theorem mstatus_ne_satp : csrAddrMstatus ≠ csrAddrSatp := by decide

/-- mstatus and sstatus are distinct (M vs S aliases). -/
theorem mstatus_ne_sstatus : csrAddrMstatus ≠ csrAddrSstatus := by decide

/-- mepc and sepc are distinct. -/
theorem mepc_ne_sepc : csrAddrMepc ≠ csrAddrSepc := by decide

/-- mtvec and stvec are distinct. -/
theorem mtvec_ne_stvec : csrAddrMtvec ≠ csrAddrStvec := by decide

/-- Sample: mstatus_pred and mie_pred can't both fire. -/
theorem mstatus_mie_mutex (csrAddr : BitVec 12) :
    !(csrAddrEqPure csrAddr csrAddrMstatus
       && csrAddrEqPure csrAddr csrAddrMie) = true :=
  csrAddrEq_mutex csrAddr csrAddrMstatus csrAddrMie mstatus_ne_mie

/-! ## Composite spec -/

theorem csrAddrEqPure_spec (csrAddr expected : BitVec 12) :
    csrAddrEqPure csrAddr expected = (csrAddr == expected) := by rfl

/-! ## Signal-level wrapper -/

def csrAddrEqSignal {dom : DomainConfig}
    (csrAddr : Signal dom (BitVec 12)) (expected : BitVec 12) : Signal dom Bool :=
  csrAddr === expected

/-! ## Per-CSR write-enable gate

  Each CSR register has its own write-enable: `idex_isCsr_valid ∧
  <csrIsRegX>` — the in-flight instruction must be a CSR op AND
  the address must match this register.

  This is the same shape as `clintRegWePure` (CLINT/Decode.lean),
  generalized over any (idex-CSR-valid, addr-match) pair.
-/

@[inline] def csrRegWePure
    (idexIsCsrValid csrIsX : Bool) : Bool :=
  idexIsCsrValid && csrIsX

@[simp] theorem csrRegWe_no_csr (csrIsX : Bool) :
    csrRegWePure false csrIsX = false := rfl

@[simp] theorem csrRegWe_no_match (idexIsCsrValid : Bool) :
    csrRegWePure idexIsCsrValid false = false := by
  unfold csrRegWePure; cases idexIsCsrValid <;> rfl

@[simp] theorem csrRegWe_active : csrRegWePure true true = true := rfl

theorem csrRegWePure_spec
    (idexIsCsrValid csrIsX : Bool) :
    csrRegWePure idexIsCsrValid csrIsX = (idexIsCsrValid && csrIsX) := rfl

def csrRegWeSignal {dom : DomainConfig}
    (idexIsCsrValid csrIsX : Signal dom Bool) : Signal dom Bool :=
  idexIsCsrValid &&& csrIsX

end Sparkle.IP.RV32.CSR
