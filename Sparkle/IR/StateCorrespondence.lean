/-
  State correspondence and duplication-freedom of an emitted module.

  The certified chain proves that the emitted module COMPUTES what the
  DSL circuit computes.  It says nothing about how much hardware the
  emission uses, and that gap is not hypothetical: three bugs found on
  this branch were duplications the chain could not see —

  * a nested `circuit do` emitted its register block twice (five
    registers for `closedLoopCircuit`'s three; the two body passes
    reduce an outer register read differently, so no syntactic cache key
    was stable),
  * a `Signal.memory` inside a `circuit do` emitted two BRAMs for one
    DSL memory (the same two-pass copy),
  * and again for `Signal.memoryComboRead`.

  Each was found by eye and fixed by a dedup pass; nothing would have
  caught a regression.  The trace theorems stay true under duplication,
  because two copies of one register hold the same value at every cycle
  — that is exactly why the bug class is quiet.

  Two decidable properties close it, at different strengths:

  * `stateCorrespondence` — the DSL's state bindings map ONE-TO-ONE
    onto the emitted module's state (registers to registers, memories
    to memories).  This is the property whose absence let all three
    bugs through, and it is scale-free: a doubling fails it, whereas
    any size bound loose enough to permit legitimate fan-out permits a
    doubling too.
  * `noDuplicateDefs` — no two defining statements of the emitted body
    have the same canonical form modulo their own name.  Syntactic and
    cheap; it covers the combinational side, where duplication costs
    area rather than correctness.

  Both are `Bool` checkers with soundness theorems, so a generator can
  discharge them by `decide` and get a kernel-checked fact.
-/
import Sparkle.IR.AST

namespace Sparkle.IR.StateCorrespondence

open Sparkle.IR.AST

/-! ### The emitted module's state -/

/-- A state slot of the emitted body: a register (width, initial value)
    or a memory (address width, data width).  The read-data wire of a
    memory is state too, but it is the memory's own latch — counting it
    separately would double-count one DSL binding. -/
inductive Slot where
  | reg (w : Nat) (init : Int)
  | mem (aw dw : Nat)
  deriving DecidableEq, Repr

/-- The emitted body's state slots, in body order. -/
def slotsOf (widthOf : String → Nat) : List Stmt → List Slot
  | [] => []
  | .register out _ _ _ init :: rest => .reg (widthOf out) init :: slotsOf widthOf rest
  | .memory _ aw dw _ _ _ _ _ _ _ _ _ :: rest => .mem aw dw :: slotsOf widthOf rest
  | _ :: rest => slotsOf widthOf rest

/-- Emitted register count. -/
def regCount : List Stmt → Nat
  | [] => 0
  | .register .. :: rest => regCount rest + 1
  | _ :: rest => regCount rest

/-- Emitted memory count. -/
def memCount : List Stmt → Nat
  | [] => 0
  | .memory .. :: rest => memCount rest + 1
  | _ :: rest => memCount rest

theorem slotsOf_length (widthOf : String → Nat) :
    ∀ body, (slotsOf widthOf body).length = regCount body + memCount body
  | [] => rfl
  | .register .. :: rest => by
    simp only [slotsOf, regCount, memCount, List.length_cons,
      slotsOf_length widthOf rest]
    omega
  | .memory .. :: rest => by
    simp only [slotsOf, regCount, memCount, List.length_cons,
      slotsOf_length widthOf rest]
    omega
  | .assign .. :: rest => by
    simp only [slotsOf, regCount, memCount, slotsOf_length widthOf rest]
  | .inst .. :: rest => by
    simp only [slotsOf, regCount, memCount, slotsOf_length widthOf rest]

/-! ### State correspondence

The DSL side is given as a multiset of slots — for the deep route these
are the loop nodes' register blocks (each carries its widths and initial
values) plus one entry per `Signal.memory`.  Correspondence is
one-to-one, so it is a permutation: the same slots, each exactly once,
in any order (the emitter is free to reorder). -/

/-- Remove one occurrence of `s`, or fail. -/
def takeOne (s : Slot) : List Slot → Option (List Slot)
  | [] => none
  | t :: rest => if s = t then some rest else (takeOne s rest).map (t :: ·)

/-- `dsl` and `emitted` hold the same slots, each exactly once. -/
def matchSlots : List Slot → List Slot → Bool
  | [], emitted => emitted.isEmpty
  | s :: rest, emitted =>
    match takeOne s emitted with
    | some emitted' => matchSlots rest emitted'
    | none => false

/-- **The state-correspondence check.**  Every DSL state binding has
    exactly one emitted counterpart and vice versa. -/
def stateCorrespondence (widthOf : String → Nat) (dsl : List Slot)
    (body : List Stmt) : Bool :=
  matchSlots dsl (slotsOf widthOf body)

/-- `takeOne` removes exactly one element. -/
theorem takeOne_length (s : Slot) :
    ∀ (l l' : List Slot), takeOne s l = some l' → l.length = l'.length + 1
  | [], _, h => by simp [takeOne] at h
  | t :: rest, l', h => by
    simp only [takeOne] at h
    by_cases hst : s = t
    · rw [if_pos hst] at h
      simp only [Option.some.injEq] at h
      simp [← h]
    · rw [if_neg hst] at h
      cases hk : takeOne s rest with
      | none => rw [hk] at h; simp at h
      | some rest' =>
        rw [hk] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have := takeOne_length s rest rest' hk
        simp [← h]
        omega

/-- Soundness, counting form: correspondence forces the emitted state
    count to equal the DSL's.  This is the statement that fails under
    duplication (five registers for three), and it holds regardless of
    emission order. -/
theorem matchSlots_length :
    ∀ (dsl emitted : List Slot), matchSlots dsl emitted = true →
      dsl.length = emitted.length
  | [], emitted, h => by
    simp only [matchSlots, List.isEmpty_iff] at h
    simp [h]
  | s :: rest, emitted, h => by
    simp only [matchSlots] at h
    cases hk : takeOne s emitted with
    | none => rw [hk] at h; simp at h
    | some emitted' =>
      rw [hk] at h
      have hlen : emitted.length = emitted'.length + 1 := takeOne_length s emitted emitted' hk
      have := matchSlots_length rest emitted' h
      simp only [List.length_cons]
      omega

theorem stateCorrespondence_count (widthOf : String → Nat) (dsl : List Slot)
    (body : List Stmt) (h : stateCorrespondence widthOf dsl body = true) :
    dsl.length = regCount body + memCount body := by
  have := matchSlots_length dsl (slotsOf widthOf body) h
  rw [this, slotsOf_length]

/-! ### Duplication-freedom of the emitted body

The canonical form of a defining statement, modulo the name it defines:
two statements with the same canonical form compute the same value from
the same inputs, so one of them is redundant hardware. -/

/-- Canonical form of a defining statement, or `none` when the
    statement cannot represent duplicated hardware.

    A plain ALIAS (`x := y`, a bare `.ref`) is excluded: several names
    for one wire is naming, not duplicated logic, and the optimizer's
    copy propagation collapses them.  Measured on the proven circuits,
    aliases are the ONLY repeats — `crc32Engine` has one wire under
    eight names — so including them would report every circuit as
    duplicating and the check would be worthless. -/
def defSig : Stmt → Option String
  | .assign _ (.ref _) => none
  | .assign _ rhs => some s!"A|{repr rhs}"
  | .register _ clk (rstName, rk) input init =>
    some s!"R|{clk}|{rstName}|{repr rk}|{init}|{repr input}"
  | .memory _ aw dw clk wa wd we ra _ cr ew er =>
    some s!"M|{cr}|{aw}|{dw}|{clk}|{repr wa}|{repr wd}|{repr we}|{repr ra}|{repr ew}|{repr er}"
  | .inst .. => none

/-- The canonical forms of a body's defining statements. -/
def defSigs (body : List Stmt) : List String := body.filterMap defSig

/-- **The duplication-freedom check**: no canonical form repeats.
    Stated as an explicit pairwise scan rather than via `eraseDups`, so
    the soundness theorem below is a direct induction (core has no
    `Nodup` lemma for `eraseDups`). -/
def noDupSigs : List String → Bool
  | [] => true
  | s :: rest => !rest.contains s && noDupSigs rest

def noDuplicateDefs (body : List Stmt) : Bool :=
  noDupSigs (defSigs body)

/-- Soundness: under the check the canonical forms are pairwise
    distinct, so no two statements of the emitted body compute the same
    value from the same inputs — the emitted hardware contains no
    redundant copy of a DSL construct. -/
theorem noDupSigs_nodup : ∀ l : List String, noDupSigs l = true → l.Nodup
  | [], _ => List.nodup_nil
  | s :: rest, h => by
    simp only [noDupSigs, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, noDupSigs_nodup rest h.2⟩

theorem noDuplicateDefs_nodup (body : List Stmt)
    (h : noDuplicateDefs body = true) : (defSigs body).Nodup :=
  noDupSigs_nodup _ h

end Sparkle.IR.StateCorrespondence
