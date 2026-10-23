import Tools.ShippingDesignSVMem
import Tools.ShippingChecksDesign
-- UNBUILT (unit SRM5): see the BUILT line below once a run is recorded.
-- SCOPE (binding): a HEIGHT-INDEXED child check `hcheck C rk f` replacing the UNIFORM-depth `kidCheck C n` / `designCheck C n` for the children of a design.
-- `rk : String → Option Nat` is a RANK TABLE by module NAME.  A module of rank 0 is checked by `leafCheck` (a built memory module, or an ordinary leaf without instances); a module of rank `h + 1`
-- by its own text check `textCheckI C` AND, for each of its instance statements, (i) the statement's target name `mn` resolves in `C` to a module `child` (an unresolved name is a REFUSAL: the check is `false`),
-- (ii) `child.name = mn` (the target is identified BY NAME), (iii) `rk mn = some r` with `r ≤ h` (no rank, or a non-decreasing edge, is a REFUSAL), (iv) `child` is checked at ITS OWN rank `r` (`hcheck _ _ f child`).
-- Rank non-existence is therefore never assumed: a cycle, an unresolved name or a missing rank makes the check `false` (`hcheck_edge`, `hcheck_unresolved`, `hcheck_norank`, `hcheck_selfInst`).
-- NOT claimed: that the check holds for any compiled design (that is `Tools/ShippingSrm5Transfer.lean`, with its premises), nor that `rk` exists for every design: `rk` is the CALLER's table.
-- `kidFactsA_check_false` (`Tools/ShippingSrm4Check.lean`) stays a counterexample to the UNIFORM positive-depth check ONLY; it says nothing about unbalanced trees under this check.
-- No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.

namespace Tools.ShippingSrm5Height
open Sparkle.IR.AST Sparkle.IR.Semantics Tools.ShippingDesignSV
open Sparkle.Compiler.MachMemory (memModule)

variable (C : String → Option (Module × WEnv)) (rk : String → Option Nat)

/-- The check of ONE statement of a module of rank `h + 1`, with `F` the check applied to a resolved child:
an instance needs its target name to resolve, to be the child's own name, to have a rank `r ≤ h`, and `F child`. -/
def instOkH (F : Module → Bool) (h : Nat) : Stmt → Bool
  | .inst mn _ _ => match C mn, rk mn with
    | some (child, _), some r => decide (r ≤ h) && (child.name == mn) && F child
    | _, _ => false
  | _ => true

/-- **The height-indexed check.**  `f` is a fuel (it must be ≥ the rank of the module; `hdesign` supplies it). -/
def hcheck : Nat → Module → Bool
  | 0, o => decide (rk o.name = some 0) && leafCheck o
  | f + 1, o => match rk o.name with
    | none => false
    | some 0 => leafCheck o
    | some (h + 1) => textCheckI C o && o.body.all (instOkH C rk (hcheck f) h)

/-- The check of a module at its own rank (a module without a rank is refused). -/
def hdesign (o : Module) : Bool :=
  match rk o.name with
  | none => false
  | some r => hcheck C rk r o

variable {C rk}

theorem instOkH_inst {F : Module → Bool} {h : Nat} {mn iname conns} :
    instOkH C rk F h (.inst mn iname conns) = true ↔
      ∃ child cwe r, C mn = some (child, cwe) ∧ rk mn = some r ∧ r ≤ h ∧ child.name = mn ∧ F child = true := by
  cases hc : C mn with
  | none => simp [instOkH, hc]
  | some p =>
    obtain ⟨child, cwe⟩ := p
    cases hr : rk mn with
    | none => simp [instOkH, hc, hr]
    | some r => simp [instOkH, hc, hr, and_assoc]

/-- rank 0: the check is `leafCheck`, at every fuel -/
theorem hcheck_rank0 {o : Module} (hr : rk o.name = some 0) (hl : leafCheck o = true) (f : Nat) :
    hcheck C rk f o = true := by
  cases f <;> simp [hcheck, hr, hl]

theorem hcheck_succ {o : Module} {h : Nat} (hr : rk o.name = some (h + 1)) (f : Nat) :
    hcheck C rk (f + 1) o = (textCheckI C o && o.body.all (instOkH C rk (hcheck C rk f) h)) := by
  simp [hcheck, hr]

/-- **The check of a module of positive rank, in one statement**: its own text check and the per-edge facts. -/
theorem hcheck_succ_iff {o : Module} {h : Nat} (hr : rk o.name = some (h + 1)) (f : Nat) :
    hcheck C rk (f + 1) o = true ↔ textCheckI C o = true ∧
      ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
        ∃ child cwe r, C mn = some (child, cwe) ∧ rk mn = some r ∧ r ≤ h ∧ child.name = mn ∧
          hcheck C rk f child = true := by
  rw [hcheck_succ hr, Bool.and_eq_true, List.all_eq_true]
  refine and_congr Iff.rfl ⟨fun hall mn iname conns hm => instOkH_inst.mp (hall _ hm), fun hall st hst => ?_⟩
  cases st with
  | inst mn iname conns => exact instOkH_inst.mpr (hall mn iname conns hst)
  | _ => rfl

/-! ## The refusals (rank non-existence is a `false`, never an assumption) -/

/-- every instance edge of a checked module of positive rank goes to a module of strictly smaller rank -/
theorem hcheck_edge {o : Module} {h f : Nat} (hr : rk o.name = some (h + 1))
    (hc : hcheck C rk (f + 1) o = true) {mn iname conns} (hm : Stmt.inst mn iname conns ∈ o.body) :
    ∃ child cwe r, C mn = some (child, cwe) ∧ rk mn = some r ∧ r < h + 1 ∧ child.name = mn ∧
      hcheck C rk f child = true := by
  obtain ⟨child, cwe, r, h1, h2, h3, h4, h5⟩ := ((hcheck_succ_iff hr f).mp hc).2 mn iname conns hm
  exact ⟨child, cwe, r, h1, h2, Nat.lt_succ_of_le h3, h4, h5⟩

/-- an unresolved target name is refused -/
theorem hcheck_unresolved {o : Module} {h f : Nat} (hr : rk o.name = some (h + 1)) {mn iname conns}
    (hm : Stmt.inst mn iname conns ∈ o.body) (hu : C mn = none) : hcheck C rk (f + 1) o = false := by
  cases hb : hcheck C rk (f + 1) o
  · rfl
  · obtain ⟨child, cwe, r, h1, -⟩ := hcheck_edge hr hb hm
    rw [hu] at h1; cases h1

/-- a target name without a rank is refused -/
theorem hcheck_norank {o : Module} {h f : Nat} (hr : rk o.name = some (h + 1)) {mn iname conns}
    (hm : Stmt.inst mn iname conns ∈ o.body) (hu : rk mn = none) : hcheck C rk (f + 1) o = false := by
  cases hb : hcheck C rk (f + 1) o
  · rfl
  · obtain ⟨child, cwe, r, -, h2, -⟩ := hcheck_edge hr hb hm
    rw [hu] at h2; cases h2

/-- a target whose rank is not below the instantiating module's is refused (a cycle cannot be ranked) -/
theorem hcheck_notBelow {o : Module} {h f : Nat} (hr : rk o.name = some (h + 1)) {mn iname conns}
    (hm : Stmt.inst mn iname conns ∈ o.body) {r : Nat} (hrm : rk mn = some r) (hge : h + 1 ≤ r) :
    hcheck C rk (f + 1) o = false := by
  cases hb : hcheck C rk (f + 1) o
  · rfl
  · obtain ⟨child, cwe, r', -, h2, h3, -⟩ := hcheck_edge hr hb hm
    rw [hrm] at h2; cases h2; omega

/-- a module instantiating itself is refused -/
theorem hcheck_selfInst {o : Module} {h f : Nat} (hr : rk o.name = some (h + 1)) {iname conns}
    (hm : Stmt.inst o.name iname conns ∈ o.body) : hcheck C rk (f + 1) o = false :=
  hcheck_notBelow hr hm hr (Nat.le_refl _)

/-- a target whose resolved module has another name than the statement's is refused (the target is identified BY NAME) -/
theorem hcheck_misnamed {o : Module} {h f : Nat} (hr : rk o.name = some (h + 1)) {mn iname conns}
    (hm : Stmt.inst mn iname conns ∈ o.body) {child : Module} {cwe} (hc : C mn = some (child, cwe))
    (hne : child.name ≠ mn) : hcheck C rk (f + 1) o = false := by
  cases hb : hcheck C rk (f + 1) o
  · rfl
  · obtain ⟨child', cwe', r, h1, -, -, h4, -⟩ := hcheck_edge hr hb hm
    rw [hc] at h1
    cases h1
    exact absurd h4 hne

/-! ## (a) the memory-leaf level (height 0) and (b) the ordinary level -/

/-- (a) every instance of the body resolves to a built memory module of rank 0 (by name) -/
def MemKidsH (C : String → Option (Module × WEnv)) (rk : String → Option Nat) (body : List Stmt) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
    ∃ cb aw dw cwe, C mn = some ((memModule cb aw dw).1, cwe) ∧ rk mn = some 0 ∧ (memModule cb aw dw).1.name = mn

/-- (a) **the memory module is a rank-0 child, for every read kind and widths** -/
theorem hcheck_memModule (cb : Bool) (aw dw : Nat) (hr : rk (memModule cb aw dw).1.name = some 0) (f : Nat) :
    hcheck C rk f (memModule cb aw dw).1 = true :=
  hcheck_rank0 hr (leafCheck_memModule cb aw dw) f

/-- (a) **a parent all of whose instances are built memory modules**: its own text check is the only thing left, at every positive rank and fuel -/
theorem hcheck_memKids {o : Module} {h : Nat} (hr : rk o.name = some (h + 1))
    (ht : textCheckI C o = true) (hk : MemKidsH C rk o.body) (f : Nat) :
    hcheck C rk (f + 1) o = true := by
  refine (hcheck_succ_iff hr f).mpr ⟨ht, fun mn iname conns hm => ?_⟩
  obtain ⟨cb, aw, dw, cwe, hc, hrm, hn⟩ := hk mn iname conns hm
  refine ⟨(memModule cb aw dw).1, cwe, 0, hc, hrm, Nat.zero_le _, hn, ?_⟩
  exact hcheck_memModule cb aw dw (hn ▸ hrm) f

/-- (b) an ordinary LEAF (no instances) passes at rank 0 exactly when `leafCheck` does -/
theorem hcheck_ordLeaf {o : Module} (hr : rk o.name = some 0) (hl : leafCheck o = true) (f : Nat) :
    hcheck C rk f o = true := hcheck_rank0 hr hl f

/-- (b) an ORDINARY non-leaf of rank `h + 1`: text check, and each instance edge's target resolved by name, below it, and checked at ITS rank -/
theorem hcheck_ord {o : Module} {h : Nat} (hr : rk o.name = some (h + 1))
    (ht : textCheckI C o = true)
    (hk : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
      ∃ child cwe r, C mn = some (child, cwe) ∧ rk mn = some r ∧ r ≤ h ∧ child.name = mn ∧
        hcheck C rk f child = true) :
    hcheck C rk (f + 1) o = true :=
  (hcheck_succ_iff hr f).mpr ⟨ht, hk⟩

/-- the check at the module's own rank, positive case -/
theorem hdesign_succ {o : Module} {h : Nat} (hr : rk o.name = some (h + 1)) :
    hdesign C rk o = hcheck C rk (h + 1) o := by
  simp [hdesign, hr]

/-! ## (A5) reproduction of the uniform `designCheck` on a BALANCED tree -/

/-- **Balanced with exact levels**: `Uni C rk n o` says `o` has rank `n + 1`, every instance target resolves by name, and the targets all have rank `n` (`n = 0`: rank 0) and, recursively, are `Uni (n-1)`.
Every root-to-leaf path has length `n + 1` and the rank table is the exact level.  This is the RANGE of `hcheck_eq_designCheck`. -/
def Uni (C : String → Option (Module × WEnv)) (rk : String → Option Nat) : Nat → Module → Prop
  | 0, o => rk o.name = some 1 ∧ ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
      ∃ child cwe, C mn = some (child, cwe) ∧ child.name = mn ∧ rk mn = some 0
  | n + 1, o => rk o.name = some (n + 2) ∧ ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
      ∃ child cwe, C mn = some (child, cwe) ∧ child.name = mn ∧ Uni C rk n child

theorem Uni_rank : ∀ {n : Nat} {o : Module}, Uni C rk n o → rk o.name = some (n + 1)
  | 0, _, h => h.1
  | _ + 1, _, h => h.1

/-- **CONDITIONAL reproduction**: on a balanced tree with the exact-level rank table (`Uni`), the height check at fuel `n + 1` IS the uniform `designCheck C n`.
Range: exactly the trees `Uni` describes (all root-to-leaf paths of equal length, ranks = levels); it does NOT say the uniform check holds, only that the two Bool values agree. -/
theorem hcheck_eq_designCheck : ∀ (n : Nat) (o : Module), Uni C rk n o →
    hcheck C rk (n + 1) o = designCheck C n o := by
  intro n
  induction n with
  | zero =>
    intro o ⟨hr, hk⟩
    rw [Tools.ShippingChecksDesign.designCheck_eq, hcheck_succ hr]
    congr 1
    unfold kidsPass
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine ⟨fun hall st hst => ?_, fun hall st hst => ?_⟩
    · cases st with
      | inst mn iname conns =>
        obtain ⟨child, cwe, hc, hn, hrm⟩ := hk mn iname conns hst
        obtain ⟨child', cwe', r, h1, h2, h3, h4, h5⟩ := instOkH_inst.mp (hall _ hst)
        rw [hc] at h1; cases h1
        simpa [hc, Tools.ShippingChecksDesign.kidCheck] using (by
          have := h5; simp [hcheck, hn, hrm] at this; exact this)
      | _ => rfl
    · cases st with
      | inst mn iname conns =>
        obtain ⟨child, cwe, hc, hn, hrm⟩ := hk mn iname conns hst
        have hl := hall _ hst
        simp only [hc, Tools.ShippingChecksDesign.kidCheck] at hl
        exact instOkH_inst.mpr ⟨child, cwe, 0, hc, hrm, Nat.le_refl _, hn, by simp [hcheck, hn, hrm, hl]⟩
      | _ => rfl
  | succ n ih =>
    intro o ⟨hr, hk⟩
    rw [Tools.ShippingChecksDesign.designCheck_eq, hcheck_succ (h := n + 1) hr]
    congr 1
    unfold kidsPass
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine ⟨fun hall st hst => ?_, fun hall st hst => ?_⟩
    · cases st with
      | inst mn iname conns =>
        obtain ⟨child, cwe, hc, hn, hu⟩ := hk mn iname conns hst
        obtain ⟨child', cwe', r, h1, h2, h3, h4, h5⟩ := instOkH_inst.mp (hall _ hst)
        rw [hc] at h1; cases h1
        simp only [hc, Tools.ShippingChecksDesign.kidCheck]
        rw [← ih child hu]; exact h5
      | _ => rfl
    · cases st with
      | inst mn iname conns =>
        obtain ⟨child, cwe, hc, hn, hu⟩ := hk mn iname conns hst
        have hl := hall _ hst
        simp only [hc, Tools.ShippingChecksDesign.kidCheck] at hl
        have hrc : rk mn = some (n + 1) := by
          have := Uni_rank hu; rw [hn] at this; exact this
        exact instOkH_inst.mpr ⟨child, cwe, n + 1, hc, hrc, Nat.le_refl _, hn, by rw [ih child hu]; exact hl⟩
      | _ => rfl

end Tools.ShippingSrm5Height

#print axioms Tools.ShippingSrm5Height.hcheck_memKids
#print axioms Tools.ShippingSrm5Height.hcheck_eq_designCheck
#print axioms Tools.ShippingSrm5Height.hcheck_edge
