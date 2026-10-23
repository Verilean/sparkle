import Tools.ShippingSrm25Init
import Tools.ShippingMachineEntry
set_option autoImplicit false
-- BUILT (unit SRM26): dev runs o1 (exit 1, 4 errors), o2 (exit 0); the final-SHA rebuild in REPORT-SRM26.md is the only final evidence.
-- SCOPE (generic, no topshare{M,Q} instance): K1 (the equation `regs = ps.map Port.name`) is NOT exported by MachineWired / MachinePreservesX / MachineTraceLBX / ComposedGW(W)
-- (scripts/srm26/K1_INVENTORY.txt §2) and is NOT proved here.  What IS proved: SRM25's source fact `SourceRegsAreSlots m regs slots` for the exported `regs` witness follows, WITHOUT any
-- equation regs = psN, from the exported MachineWired facts (names Nodup, the slot→register conjunct) plus `hK0`, the source fact for the slot-port names `psN` (K0N) — an explicit PREMISE,
-- not proved here and not exported by any existing theorem.  K0, G1, G3, hsk, FitTree, hRK, hst facts untouched.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm26
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.RefineCheck
open Sparkle.IR.Machine (SlotField)
open Sparkle.Compiler.Elab (MachineShape)
open Tools.ShippingMachineEntry (MachineWired machPorts)
open Tools.ShippingSrm25Init (SourceRegsAreSlots shippedRegsAreSlots_of_source)
open Tools.ShippingSrm22Width (ShippedRegsAreSlots)

/-- **PROVED** (pigeonhole): a duplicate-free `l1` inside `l2` with `l2.length ≤ l1.length` covers `l2`. -/
theorem subset_of_length_le {α : Type} [DecidableEq α] (l1 l2 : List α) (hnd : l1.Nodup)
    (hsub : ∀ x ∈ l1, x ∈ l2) (hlen : l2.length ≤ l1.length) : ∀ x ∈ l2, x ∈ l1 := by
  induction l1 generalizing l2 with
  | nil =>
    intro x hx
    have : l2 = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst this; cases hx
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l2 := hsub a List.mem_cons_self
    have hsub' : ∀ y ∈ t, y ∈ l2.erase a := fun y hy =>
      (List.mem_erase_of_ne (by intro h; rw [h] at hy; exact hnd.1 hy)).mpr (hsub y (List.mem_cons_of_mem _ hy))
    have hlen' : (l2.erase a).length ≤ t.length := by
      rw [List.length_erase_of_mem ha]; simp only [List.length_cons] at hlen; omega
    intro x hx
    by_cases hxa : x = a
    · rw [hxa]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (ih (l2.erase a) hnd.2 hsub' hlen' x ((List.mem_erase_of_ne hxa).mpr hx))

/-- **PROVED**: distinct entries have distinct positions. -/
theorem nodup_getElem?_inj {α : Type} : ∀ (l : List α) (i j : Nat) (x : α), l.Nodup →
    l[i]? = some x → l[j]? = some x → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | a :: t, 0, 0, _, _, _, _ => rfl
  | a :: t, 0, j + 1, x, hnd, h1, h2 => by
    have hx : a = x := by simpa using h1
    exact absurd (hx ▸ List.mem_of_getElem? (by simpa using h2)) (List.nodup_cons.mp hnd).1
  | a :: t, i + 1, 0, x, hnd, h1, h2 => by
    have hx : a = x := by simpa using h2
    exact absurd (hx ▸ List.mem_of_getElem? (by simpa using h1)) (List.nodup_cons.mp hnd).1
  | a :: t, i + 1, j + 1, x, hnd, h1, h2 => by
    have := nodup_getElem?_inj t i j x (List.nodup_cons.mp hnd).2 (by simpa using h1) (by simpa using h2)
    omega

/-- **PROVED**: the source fact for the `regs` witness from the source fact for the slot-port names `psN`
(`hK0`, PREMISE), the exported slot→register conjunct (`hslot`) and the counts; no equation `regs = psN`. -/
theorem sourceRegsAreSlots_regs_of_ports (b : Module) (psN regs : List String) (slots : List SlotField)
    (hpsNd : psN.Nodup) (hregsNd : regs.Nodup) (hlen : regs.length = slots.length)
    (hpl : psN.length ≤ slots.length)
    (hslot : ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → slots[k]? = some f →
      ∃ (rk : Sparkle.IR.Type.ResetKind) (inp : Expr),
        Stmt.register r "clk" ("rst", rk) inp (Int.ofNat f.init) ∈ b.body)
    (hK0 : SourceRegsAreSlots b psN slots) :
    SourceRegsAreSlots b regs slots := by
  intro r c rs inp init hmem
  obtain ⟨j, f, hj, hf, hinit⟩ := hK0 _ _ _ _ _ hmem
  have hrp : r ∈ psN := List.mem_of_getElem? hj
  have hsub : ∀ x ∈ regs, x ∈ psN := by
    intro x hx
    obtain ⟨k, hkx⟩ := List.mem_iff_getElem?.mp hx
    have hk : k < regs.length := (List.getElem?_eq_some_iff.mp hkx).1
    obtain ⟨f', hf'⟩ : ∃ f', slots[k]? = some f' :=
      ⟨slots[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨rk, inp', hm'⟩ := hslot k x f' hkx hf'
    obtain ⟨j', f'', hj', _, _⟩ := hK0 _ _ _ _ _ hm'
    exact List.mem_of_getElem? hj'
  have hr : r ∈ regs := subset_of_length_le regs psN hregsNd hsub (by omega) r hrp
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  have hk' : k < regs.length := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨f', hf'⟩ : ∃ f', slots[k]? = some f' :=
    ⟨slots[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨rk, inp', hm'⟩ := hslot k r f' hk hf'
  obtain ⟨j', f'', hj', hf'', hinit'⟩ := hK0 _ _ _ _ _ hm'
  have hjj : j = j' := nodup_getElem?_inj psN j j' r hpsNd hj hj'
  subst hjj
  have hff : f'' = f := by rw [hf] at hf''; exact (Option.some.inj hf'').symm
  subst hff
  exact ⟨k, f', hk, hf', hinit.trans hinit'.symm⟩

/-- **PROVED**: as `sourceRegsAreSlots_regs_of_ports`, with the exported facts read off `MachineWired`
(its names are distinct; its last conjunct is the slot→register clause) and `psN` spelled as the slot slice
of the machine's port names.  `hK0` (K0N) is the one residual PREMISE. -/
theorem sourceRegsAreSlots_of_wired {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (hW : MachineWired declName shape ids cache m dsn regs lets)
    (hregsNd : regs.Nodup) (hlen : regs.length = shape.layout.slots.length)
    (hK0 : SourceRegsAreSlots m
      ((((machPorts declName ids cache shape.binders).map (·.name)).drop
          (((machPorts declName ids cache shape.binders).map (·.name)).length - shape.layout.lets -
            shape.layout.slots.length)).take shape.layout.slots.length) shape.layout.slots) :
    SourceRegsAreSlots m regs shape.layout.slots := by
  simp only [MachineWired] at hW
  obtain ⟨hnd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlast⟩ := hW
  exact sourceRegsAreSlots_regs_of_ports m _ regs shape.layout.slots
    (List.Nodup.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _)) hnd) hregsNd hlen
    (List.length_take_le ..) hlast hK0

/-- **PROVED (reduction, under hK0)**: G5 for the exported `regs` witness, from `hierGate m`, `MachineWired`
and K0N (`hK0`, PREMISE); composes `sourceRegsAreSlots_of_wired` with SRM25's `shippedRegsAreSlots_of_source`. -/
theorem shippedRegsAreSlots_of_wired {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (hgate : hierGate m = true)
    (hW : MachineWired declName shape ids cache m dsn regs lets)
    (hregsNd : regs.Nodup) (hlen : regs.length = shape.layout.slots.length)
    (hK0 : SourceRegsAreSlots m
      ((((machPorts declName ids cache shape.binders).map (·.name)).drop
          (((machPorts declName ids cache shape.binders).map (·.name)).length - shape.layout.lets -
            shape.layout.slots.length)).take shape.layout.slots.length) shape.layout.slots) :
    ShippedRegsAreSlots m regs shape.layout.slots :=
  shippedRegsAreSlots_of_source hgate regs shape.layout.slots
    (sourceRegsAreSlots_of_wired hW hregsNd hlen hK0)

end Tools.ShippingSrm26

#print axioms Tools.ShippingSrm26.nodup_getElem?_inj
#print axioms Tools.ShippingSrm26.subset_of_length_le
#print axioms Tools.ShippingSrm26.sourceRegsAreSlots_regs_of_ports
#print axioms Tools.ShippingSrm26.sourceRegsAreSlots_of_wired
#print axioms Tools.ShippingSrm26.shippedRegsAreSlots_of_wired
