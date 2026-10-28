import Tools.ShippingSrm5Height
import Tools.ShippingSrm4Check
-- BUILT (unit SRM5): s5b3 exit 0 (dev run); final-SHA rebuild in REPORT-SRM5.md.
-- SCOPE: REGRESSION for the height-indexed check `hcheck` (`Tools/ShippingSrm5Height.lean`) on a small UNBALANCED tree
--   R (rank 2) --> A (rank 1) --> L (rank 0, ordinary leaf)        [one branch through one ordinary level]
--   R (rank 2) --> mem (rank 0, the built memory module)           [the other branch: a memory leaf DIRECTLY below]
-- (1) the height check SUCCEEDS on R (`unbalanced_height_ok`), given the TEXT checks of R and A (`hRt`, `hAt`, premises of the toy: they are checks of emitted text with port connections, not what is
--     under test; the ranks, the targets and the leaf level are) and the leaf check of the toy leaf `L` (decided).
-- (2) the OLD uniform check FAILS on that tree at EVERY depth (`uniform_fails`): at depth 0 `A` is asked `leafCheck` (it has an instance), at depth ≥ 1 the memory module is asked `designCheck`, which it fails
--     (`designCheck_memModule`, `kidCheck_memModule_succ`).  This is a statement about the uniform check on THIS tree, not "unbalanced trees are rejected".
-- (3) MUTATIONS are REJECTED by the height check: a statement re-targeted to its own module / to an ancestor (`mut_self`, `mut_backEdge`), to an unresolved name (`mut_unresolved`), a table that resolves the
--     statement's name to a module of ANOTHER name (`mut_misnamed`), a rank table without the target (`mut_norank`).
-- (4) the conditional reproduction lemma on a balanced one-level tree (`balanced_reproduces`).
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.Srm5HeightTest
open Sparkle.IR.AST Sparkle.IR.Semantics Tools.ShippingDesignSV Tools.ShippingSrm5Height
open Sparkle.Compiler.MachMemory (memModule)
open Tools.ShippingChecksDesign (kidCheck designCheck_eq)

def memM : Module := (memModule false 2 4).1
def memNm : String := memM.name

def Lm : Module := { name := "L", inputs := [], outputs := [], wires := [], body := [] }
def Am : Module := { name := "A", inputs := [], outputs := [], wires := [], body := [.inst "L" "l0" []] }
def Rm : Module := { name := "R", inputs := [], outputs := [], wires := [], body := [.inst "A" "a0" [], .inst memNm "m0" []] }

/-- the resolver: each name to its module, with its width table -/
def C : String → Option (Module × WEnv) := fun mn =>
  if mn = memNm then some (memM, Sparkle.IR.RegDedup.declWidth memM)
  else if mn = "R" then some (Rm, Sparkle.IR.RegDedup.declWidth Rm)
  else if mn = "A" then some (Am, Sparkle.IR.RegDedup.declWidth Am)
  else if mn = "L" then some (Lm, Sparkle.IR.RegDedup.declWidth Lm)
  else none

/-- the rank table: heights, memory at 0 -/
def rk : String → Option Nat := fun mn =>
  if mn = memNm then some 0 else if mn = "R" then some 2 else if mn = "A" then some 1 else if mn = "L" then some 0 else none

theorem memNm_ne_R : ¬ ("R" = memNm) := by decide
theorem memNm_ne_A : ¬ ("A" = memNm) := by decide
theorem memNm_ne_L : ¬ ("L" = memNm) := by decide
theorem memNm_ne_Z : ¬ ("Z" = memNm) := by decide
theorem memNm_ne_R2 : ¬ ("R2" = memNm) := by decide

theorem C_mem : C memNm = some (memM, Sparkle.IR.RegDedup.declWidth memM) := by simp [C]
theorem C_R : C "R" = some (Rm, Sparkle.IR.RegDedup.declWidth Rm) := by simp [C, memNm_ne_R]
theorem C_A : C "A" = some (Am, Sparkle.IR.RegDedup.declWidth Am) := by simp [C, memNm_ne_A]
theorem C_L : C "L" = some (Lm, Sparkle.IR.RegDedup.declWidth Lm) := by simp [C, memNm_ne_L]
theorem C_Z : C "Z" = none := by simp [C, memNm_ne_Z]
theorem rk_mem : rk memNm = some 0 := by simp [rk]
theorem rk_R : rk "R" = some 2 := by simp [rk, memNm_ne_R]
theorem rk_A : rk "A" = some 1 := by simp [rk, memNm_ne_A]
theorem rk_L : rk "L" = some 0 := by simp [rk, memNm_ne_L]

theorem leaf_L : leafCheck Lm = true := by first | decide | rfl
theorem leaf_A_false : leafCheck Am = false := by simp [leafCheck, Am, Tools.ShippingDesignSV.seqStmtOkA]

/-! ## (1) the height check SUCCEEDS on the unbalanced tree -/

theorem unbalanced_height_ok (hRt : textCheckI C Rm = true) (hAt : textCheckI C Am = true) :
    hdesign C rk Rm = true := by
  have hrR : rk Rm.name = some (1 + 1) := rk_R
  have hrA : rk Am.name = some (0 + 1) := rk_A
  rw [hdesign_succ hrR]
  refine hcheck_ord hrR hRt ?_
  intro mn iname conns hm
  simp only [Rm, List.mem_cons, Stmt.inst.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
  · refine ⟨Am, _, 1, C_A, rk_A, Nat.le_refl _, rfl, ?_⟩
    refine hcheck_ord hrA hAt ?_
    intro mn iname conns hm
    simp only [Am, List.mem_cons, Stmt.inst.injEq, List.not_mem_nil, or_false] at hm
    obtain ⟨rfl, -, -⟩ := hm
    exact ⟨Lm, _, 0, C_L, rk_L, Nat.le_refl _, rfl, hcheck_ordLeaf rk_L leaf_L 0⟩
  · exact ⟨memM, _, 0, C_mem, rk_mem, Nat.zero_le _, rfl, hcheck_memModule false 2 4 rk_mem 1⟩

/-! ## (2) the OLD uniform check FAILS on it, at every depth -/

theorem uniform_fails (n : Nat) : designCheck C n Rm = false := by
  rw [designCheck_eq]
  have hm : ∀ m, kidCheck C (m + 1) memM = false := fun m =>
    Tools.ShippingSrm4Check.kidCheck_memModule_succ C false 2 4 m
  cases n with
  | zero =>
    have : kidsPass C (kidCheck C 0) Rm.body = false := by
      simp [kidsPass, Rm, C_A, kidCheck, leaf_A_false]
    simp [this]
  | succ m =>
    have : kidsPass C (kidCheck C (m + 1)) Rm.body = false := by
      simp [kidsPass, Rm, C_A, C_mem, hm]
    simp [this]

/-! ## (3) MUTATIONS are rejected -/

/-- the root re-targeted to ITSELF -/
def RmSelf : Module := { Rm with body := [.inst "R" "a0" []] }
theorem mut_self (f : Nat) : hcheck C rk (f + 1) RmSelf = false :=
  hcheck_selfInst (h := 1) (iname := "a0") (conns := []) rk_R (by simp [RmSelf, Rm])

/-- the middle module re-targeted to its ANCESTOR (a cycle `R → A → R`) -/
def AmBack : Module := { Am with body := [.inst "R" "l0" []] }
theorem mut_backEdge (f : Nat) : hcheck C rk (f + 1) AmBack = false :=
  hcheck_notBelow (h := 0) (iname := "l0") (conns := []) (r := 2) rk_A (by simp [AmBack, Am]) rk_R (by omega)

/-- the root re-targeted to an UNRESOLVED name -/
def RmZ : Module := { Rm with body := [.inst "Z" "a0" []] }
theorem mut_unresolved (f : Nat) : hcheck C rk (f + 1) RmZ = false :=
  hcheck_unresolved (h := 1) (iname := "a0") (conns := []) rk_R (by simp [RmZ, Rm]) C_Z

/-- a rank table WITHOUT the target `A` -/
def rkNoA : String → Option Nat := fun mn => if mn = "A" then none else rk mn
theorem mut_norank (f : Nat) : hcheck C rkNoA (f + 1) Rm = false := by
  have hr : rkNoA Rm.name = some (1 + 1) := by
    show rkNoA "R" = _
    simp [rkNoA, rk_R]
  exact hcheck_norank (h := 1) (mn := "A") (iname := "a0") (conns := []) hr (by simp [Rm]) (by simp [rkNoA])

/-- a resolver that sends the statement's name `A` to the module `L` (another NAME) -/
def Cbad : String → Option (Module × WEnv) := fun mn =>
  if mn = "A" then some (Lm, Sparkle.IR.RegDedup.declWidth Lm) else C mn
theorem mut_misnamed (f : Nat) : hcheck Cbad rk (f + 1) Rm = false :=
  hcheck_misnamed (h := 1) (mn := "A") (iname := "a0") (conns := []) rk_R (by simp [Rm]) (child := Lm)
    (cwe := Sparkle.IR.RegDedup.declWidth Lm) (by simp [Cbad]) (by simp [Lm])

/-! ## (4) the conditional reproduction on a balanced one-level tree -/

def R2m : Module := { name := "R2", inputs := [], outputs := [], wires := [], body := [.inst "L" "l0" []] }
def C2 : String → Option (Module × WEnv) := fun mn =>
  if mn = "L" then some (Lm, Sparkle.IR.RegDedup.declWidth Lm) else none
def rk2 : String → Option Nat := fun mn => if mn = "R2" then some 1 else if mn = "L" then some 0 else none

theorem balanced_reproduces : hcheck C2 rk2 1 R2m = designCheck C2 0 R2m := by
  refine hcheck_eq_designCheck (n := 0) R2m ⟨by simp [rk2, R2m], ?_⟩
  intro mn iname conns hm
  simp only [R2m, List.mem_cons, Stmt.inst.injEq, List.not_mem_nil, or_false] at hm
  obtain ⟨rfl, -, -⟩ := hm
  exact ⟨Lm, Sparkle.IR.RegDedup.declWidth Lm, by simp [C2], rfl, by simp [rk2]⟩

end Tests.Compiler.Srm5HeightTest

#print axioms Tests.Compiler.Srm5HeightTest.unbalanced_height_ok
#print axioms Tests.Compiler.Srm5HeightTest.uniform_fails
#print axioms Tests.Compiler.Srm5HeightTest.mut_misnamed
#print axioms Tests.Compiler.Srm5HeightTest.balanced_reproduces
