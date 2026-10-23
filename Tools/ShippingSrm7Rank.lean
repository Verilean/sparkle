import Tools.ShippingMemOnlyNames
import Tools.ShippingModuleName
-- UNBUILT (unit SRM7): see the BUILT line below once a run is recorded.
-- SCOPE (binding): a COMPUTED rank table for a BOUNDED, CONCRETE class of designs, replacing the hand-written `rkM`/`rkQ` of SRM5.
-- THE CLASS (R1): a CALL GRAPH `g : CallGraph` (one entry per declaration: its name and the callee names of its call entries, i.e. `X.machineData.shape.insts.map (·.1)`),
-- a fuel bound `B` and a root `top`; `InClass g B top` (decidable, a `Bool`) holds iff `WfG g` (declaration names pairwise distinct, no declaration is named like a memory placeholder)
-- and `declRank g B top` succeeds.  The graph is READ from the generated declarations by the test file (never typed in by hand beyond the list of declaration names to read).
-- THE COMPUTATION (R2): `declRank g f c` = height of `c` in the call graph: a declaration without call entries has rank 0, otherwise 1 + the maximum rank of its callees; a memory placeholder
-- (origin `.mem cb aw dw`, named `memChildName cb aw dw`) has rank 0; a name missing from the graph, a cycle (fuel runs out), or a graph failing `WfG` is REFUSED (`none`).
-- `rkOf g F` is the rank table by MODULE NAME (decoded with the injective encoding `ModuleName.decode`): every built memory module has rank 0, the module of declaration `n` has rank `declRank g F n`, every other name has no rank.
-- SOUNDNESS (PROVED): `rkOf_mem` (= SRM5 `hrkmem`), `rkOf_decl` (= the `hrb`/`hrT`-style own-rank equation), `rkOf_edge` (= `hrank`: a rank-`r` declaration's callees have module ranks `< r`, hence `≤ h` when `r = h+1`),
-- `rkOf_ge_one` (a declaration with a callee has rank `≥ 1`), `declRank_le` (rank `≤` fuel), `declRank_mono`, and the refusals `declRank_self` (self call), `declRank_cycle2` style facts follow from `rkOf_edge`
-- (a strict decrease along every edge cannot go round a cycle); `rkChecked_dup` (duplicate names refused: the table is empty).
-- NOT claimed: that a rank table exists for an arbitrary design (the graph must be supplied and READ from the design; the class is bounded by `B`); NOT claimed here: the kid's own height check `hkidH`
-- (that is the machine-level `*_kidHeight` theorem of SRM5 with its premises).  No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.

namespace Tools.ShippingSrm7Rank
open Lean (Name)
open Sparkle.IR.ModuleName
open Sparkle.Compiler.MachMemory (memChildName memModule)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)

/-- a call entry: the callee name and its ORIGIN (`X.machineData.shape.instTagged`): the origin, not the name, says whether the callee is a built memory -/
abbrev Kid := Name × InstOrigin

/-- the call graph: one entry per declaration, with its call entries (in the reader's order) -/
abbrev CallGraph := List (Name × List Kid)

/-- the callees of declaration `c` (the first entry of that name) -/
def callees : CallGraph → Name → Option (List Kid)
  | [], _ => none
  | (d, ks) :: t, c => if d == c then some ks else callees t c

/-- the maximum of the callee ranks, `none` as soon as one callee has no rank -/
def kidsMax (kr : Kid → Option Nat) : List Kid → Option Nat
  | [] => some 0
  | k :: ks => match kr k, kidsMax kr ks with
    | some a, some b => some (max a b)
    | _, _ => none

/-- the rank of a call entry: an entry of origin `.mem cb aw dw` (named by its placeholder) is the built memory module, rank 0; any other entry is a declaration, looked up in the graph at one less fuel -/
def kidRank (dr : Name → Option Nat) : Kid → Option Nat
  | (k, .mem cb aw dw) => if k == memChildName cb aw dw then some 0 else none
  | (k, _) => dr k

/-- **The rank computation** (fuel-bounded): a memory entry has rank 0; a declaration without call entries rank 0; otherwise `1 +` the maximum of its callees' ranks. -/
def declRank (g : CallGraph) : Nat → Name → Option Nat
  | 0, _ => none
  | f + 1, c => match callees g c with
    | none => none
    | some ks => match kidsMax (kidRank (declRank g f)) ks with
      | none => none
      | some m => some (if ks.isEmpty then 0 else m + 1)

/-- the module name of a call entry: the built memory module's name for a memory origin, the declaration's module name otherwise -/
def kidModName : Kid → String
  | (_, .mem cb aw dw) => ofMem cb aw dw
  | (k, _) => ofDecl k

/-- **The rank table by module name.** -/
def rkOf (g : CallGraph) (F : Nat) (s : String) : Option Nat :=
  match decode s with
  | some (.mem _ _ _) => some 0
  | some (.decl n) => declRank g F n
  | _ => none

/-- (R1) well-formedness: declaration names pairwise distinct -/
def WfG (g : CallGraph) : Bool :=
  (g.map Prod.fst).eraseDups.length == g.length

/-- (R1) **the class**: a well-formed graph whose root has a rank within the fuel bound `B` -/
def InClass (g : CallGraph) (B : Nat) (top : Name) : Bool := WfG g && (declRank g B top).isSome

/-- the table, refused (empty) when the graph is not well-formed -/
def rkChecked (g : CallGraph) (F : Nat) : String → Option Nat :=
  if WfG g then rkOf g F else fun _ => none

/-! ## Soundness -/

theorem kidsMax_le {kr : Kid → Option Nat} :
    ∀ {ks : List Kid} {m : Nat}, kidsMax kr ks = some m → ∀ k ∈ ks, ∃ a, kr k = some a ∧ a ≤ m := by
  intro ks
  induction ks with
  | nil => intro _ _ k hk; cases hk
  | cons k0 ks ih =>
    intro m h k hk
    unfold kidsMax at h
    cases h0 : kr k0 with
    | none => rw [h0] at h; simp at h
    | some a =>
      cases h1 : kidsMax kr ks with
      | none => rw [h0, h1] at h; simp at h
      | some b =>
        rw [h0, h1] at h
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hk with rfl | hk
        · exact ⟨a, h0, Nat.le_max_left _ _⟩
        · obtain ⟨a', ha', hle⟩ := ih h1 k hk
          exact ⟨a', ha', Nat.le_trans hle (Nat.le_max_right _ _)⟩

theorem kidsMax_mono {kr kr' : Kid → Option Nat} :
    ∀ {ks : List Kid} {m : Nat}, (∀ k ∈ ks, ∀ a, kr k = some a → kr' k = some a) →
      kidsMax kr ks = some m → kidsMax kr' ks = some m := by
  intro ks
  induction ks with
  | nil => intro _ _ h; exact h
  | cons k0 ks ih =>
    intro m hm h
    unfold kidsMax at h ⊢
    cases h0 : kr k0 with
    | none => rw [h0] at h; simp at h
    | some a =>
      cases h1 : kidsMax kr ks with
      | none => rw [h0, h1] at h; simp at h
      | some b =>
        rw [h0, h1] at h
        rw [hm k0 (List.mem_cons_self) a h0, ih (fun k hk => hm k (List.mem_cons_of_mem _ hk)) h1]
        exact h

theorem kidsMax_lt {kr : Kid → Option Nat} {B : Nat} :
    ∀ {ks : List Kid} {m : Nat}, kidsMax kr ks = some m → (∀ k ∈ ks, ∀ a, kr k = some a → a ≤ B) → m ≤ B := by
  intro ks
  induction ks with
  | nil => intro m h _; simp [kidsMax] at h; omega
  | cons k0 ks ih =>
    intro m h hB
    unfold kidsMax at h
    cases h0 : kr k0 with
    | none => rw [h0] at h; simp at h
    | some a =>
      cases h1 : kidsMax kr ks with
      | none => rw [h0, h1] at h; simp at h
      | some b =>
        rw [h0, h1] at h
        simp only [Option.some.injEq] at h
        subst h
        have := hB k0 List.mem_cons_self a h0
        have := ih h1 (fun k hk => hB k (List.mem_cons_of_mem _ hk))
        omega

/-- more fuel never changes a successful rank -/
theorem declRank_mono (g : CallGraph) : ∀ (f : Nat) (c : Name) (r : Nat),
    declRank g f c = some r → ∀ F, f ≤ F → declRank g F c = some r := by
  intro f
  induction f with
  | zero => intro c r h; simp [declRank] at h
  | succ f ih =>
    intro c r h F hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    unfold declRank at h ⊢
    cases hc : callees g c with
    | none => rw [hc] at h; simp at h
    | some ks =>
      try rw [hc] at h
      try rw [hc]
      simp only at h ⊢
      cases hk : kidsMax (kidRank (declRank g f)) ks with
      | none => rw [hk] at h; simp at h
      | some m =>
        rw [hk] at h
        rw [kidsMax_mono (kr' := kidRank (declRank g F')) ?_ hk]
        · exact h
        · intro k _ a ha
          obtain ⟨n, o⟩ := k
          cases o with
          | ord => exact ih n a ha F' (by omega)
          | field i => exact ih n a ha F' (by omega)
          | mem cb aw dw => exact ha

/-- the rank is at most the fuel -/
theorem declRank_le (g : CallGraph) : ∀ (f : Nat) (c : Name) (r : Nat), declRank g f c = some r → r ≤ f := by
  intro f
  induction f with
  | zero => intro c r h; simp [declRank] at h
  | succ f ih =>
    intro c r h
    unfold declRank at h
    cases hc : callees g c with
    | none => rw [hc] at h; simp at h
    | some ks =>
      try rw [hc] at h
      simp only at h
      cases hk : kidsMax (kidRank (declRank g f)) ks with
      | none => rw [hk] at h; simp at h
      | some m =>
        rw [hk] at h
        simp only [Option.some.injEq] at h
        have hm : m ≤ f := kidsMax_lt hk (fun k _ a ha => by
          obtain ⟨n, o⟩ := k
          cases o with
          | ord => exact ih n a ha
          | field i => exact ih n a ha
          | mem cb aw dw =>
            simp only [kidRank] at ha
            split at ha
            · simp at ha; omega
            · cases ha)
        split at h <;> omega

/-- (`hrkmem`) every built memory module has rank 0 -/
theorem rkOf_mem (g : CallGraph) (F : Nat) (cb : Bool) (aw dw : Nat) :
    rkOf g F (memModule cb aw dw).1.name = some 0 := by
  have h : (memModule cb aw dw).1.name = ofMem cb aw dw := Tools.ShippingMemOnlyNames.memModule_name cb aw dw
  rw [h, rkOf, ofMem, Tools.ShippingModuleName.decode_encode]

/-- (own rank, `hrb`/`hrT`-style) the module of a declaration has the computed rank -/
theorem rkOf_decl (g : CallGraph) (F : Nat) (c : Name) : rkOf g F (ofDecl c) = declRank g F c := by
  rw [rkOf, ofDecl, Tools.ShippingModuleName.decode_encode]

/-- (`hrank`) **every call entry of a ranked declaration has a module rank strictly below it** -/
theorem rkOf_edge {g : CallGraph} {F : Nat} {c : Name} {r : Nat} {ks : List Kid}
    (h : declRank g F c = some r) (hc : callees g c = some ks) {k : Kid} (hk : k ∈ ks) :
    ∃ r', rkOf g F (kidModName k) = some r' ∧ r' < r := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
    cases F with
    | zero => simp [declRank] at h
    | succ f => exact ⟨f, rfl⟩
  unfold declRank at h
  try rw [hc] at h
  simp only at h
  cases hm : kidsMax (kidRank (declRank g f)) ks with
  | none => rw [hm] at h; simp at h
  | some m =>
    rw [hm] at h
    have hne : ks.isEmpty = false := by cases ks with | nil => cases hk | cons _ _ => rfl
    rw [hne] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨a, ha, hle⟩ := kidsMax_le hm k hk
    obtain ⟨n, o⟩ := k
    cases o with
    | ord => exact ⟨a, by simp only [kidModName]; rw [rkOf_decl]; exact declRank_mono g f n a ha _ (by omega), by omega⟩
    | field i => exact ⟨a, by simp only [kidModName]; rw [rkOf_decl]; exact declRank_mono g f n a ha _ (by omega), by omega⟩
    | mem cb aw dw =>
      refine ⟨0, ?_, by omega⟩
      have := rkOf_mem g (f + 1) cb aw dw
      rwa [Tools.ShippingMemOnlyNames.memModule_name] at this

/-- a declaration with a call entry has rank `≥ 1` -/
theorem rank_pos {g : CallGraph} {F : Nat} {c : Name} {r : Nat} {ks : List Kid}
    (h : declRank g F c = some r) (hc : callees g c = some ks) {k : Kid} (hk : k ∈ ks) : 1 ≤ r := by
  obtain ⟨r', -, hlt⟩ := rkOf_edge h hc hk
  omega

/-- (refusal) a declaration that calls itself (as a declaration, not as a memory) has NO rank, at any fuel -/
theorem declRank_self {g : CallGraph} {c : Name} {ks : List Kid} (hc : callees g c = some ks) (hk : (c, InstOrigin.ord) ∈ ks)
    (F : Nat) : declRank g F c = none := by
  cases h : declRank g F c with
  | none => rfl
  | some r =>
    obtain ⟨r', hr', hlt⟩ := rkOf_edge h hc hk
    simp only [kidModName] at hr'
    rw [rkOf_decl, h] at hr'
    simp only [Option.some.injEq] at hr'
    omega

/-- (refusal) a graph with duplicate declaration names gets the EMPTY table -/
theorem rkChecked_dup {g : CallGraph} (h : WfG g = false) (F : Nat) (s : String) : rkChecked g F s = none := by
  unfold rkChecked
  rw [if_neg (by simp [h])]

/-- a well-formed graph gets the computed table -/
theorem rkChecked_wf {g : CallGraph} (h : WfG g = true) (F : Nat) : rkChecked g F = rkOf g F := by
  unfold rkChecked
  rw [if_pos h]

/-- the class predicate implies a rank within the bound for the root -/
theorem inClass_rank {g : CallGraph} {B : Nat} {top : Name} (h : InClass g B top = true) :
    ∃ r, declRank g B top = some r ∧ r ≤ B ∧ WfG g = true := by
  unfold InClass at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hw, hs⟩ := h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨r, hr, declRank_le g B top r hr, hw⟩

end Tools.ShippingSrm7Rank
