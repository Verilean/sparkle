import Tools.ShippingChecksDerived2
import Tools.ShippingOutsExtractedParts

/-! # The optimizer's guards are sound (isolated branch `fix/opt-fallback`)

`Sparkle.IR.HierCheck.deinline m o` is, on this branch, the candidate
`deinlineRaw m o` when it passes two design-free guards — G4, distinct
instance names (`instNamesOf`), and G2, the linked order with an instance's
outputs read as its connected wires among the extracted inputs
(`linkedWFX ((openIns m).map name)`) — and `m` otherwise. And
`checkedOptimize` returns the input module when the hierarchical check does
not bind on an instance / assignment / register module.

* `linkedWFX_sound`: `linkedWFX X body` implies `linkedWF C body` for every
  child map `C` in which every instance statement of `body` resolves, its
  output wires are in `X` and are pairwise distinct (`InstsIn`).
* `instsIn_of`: that holds of a body whose instance statements are among
  `m`'s, when `m.body` is linked-well-formed and `m`'s instance-driven wires
  are extracted (`outsExtracted`).
* `deinline_guards`: under `hierRefineCheck m (deinline m o)`, the candidate
  kept is linked-well-formed with distinct instance names — conjuncts 2 and
  4 of `shipsHierCheck` for an accepted candidate.
* `RunFacts C b`: what the core run of a machine with calls provides of the
  full entry's module (`core_hierGate`, `core_linkedWF`, `core_raw_facts`,
  `core_outsExtracted`, `core_instOutWidthsOk`).
* `checkedOptimize_facts`: for ANY such module the SHIPPED module
  `checkedOptimize b` is linked-well-formed, has distinct instance names and
  `b`'s inputs — by cases on the compiler's own branches (not binding:
  `b` itself; binding and rejected: `b`; accepted: the guards).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingGuardsSound
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierOpen
open Sparkle.IR.HierCheck (connX outsX writesX linkedWFX instNamesOf)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (hierBinds hierGate hierRefineCheck)

/-- The guard's instance names are the checks'. -/
theorem instNamesOf_eq : ∀ body : List Stmt,
    instNamesOf body = Tools.ShippingHierState.instNames body
  | [] => rfl
  | st :: rest => by
    have ih := instNamesOf_eq rest
    cases st with
    | inst mn i conns => exact congrArg (fun l => i :: l) ih
    | _ => exact ih

/-- A connection of a wire in `X` is among the instance's `X`-wires. -/
theorem mem_connX {X : List String} {conns : List (String × Expr)} {nm w : String}
    (h : (nm, Expr.ref w) ∈ conns) (hX : w ∈ X) : w ∈ connX X conns := by
  unfold Sparkle.IR.HierCheck.connX
  refine List.mem_filterMap.mpr ⟨(nm, Expr.ref w), h, ?_⟩
  have hc : X.contains w = true := by simpa [List.contains_eq_mem] using hX
  show (if X.contains w = true then some w else none) = some w
  rw [if_pos hc]

/-- Every instance statement of the body resolves, its output wires are in
`X` and pairwise distinct. -/
def InstsIn (C : String → Option (Sparkle.IR.AST.Module × WEnv)) (X : List String)
    (body : List Stmt) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
    ∃ child cwe, C mn = some (child, cwe) ∧
      (∀ w ∈ instOutWires child.outputs conns, w ∈ X) ∧
      (instOutWires child.outputs conns).Nodup

theorem InstsIn.tail {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {X : List String}
    {st : Stmt} {rest : List Stmt} (h : InstsIn C X (st :: rest)) : InstsIn C X rest :=
  fun mn iname conns hm => h mn iname conns (List.Mem.tail _ hm)

/-- An instance's output wires are among its `X`-wires. -/
theorem stmtInstOuts_sub {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {X : List String}
    {mn iname : String} {conns : List (String × Expr)} {child : Sparkle.IR.AST.Module}
    {cwe : WEnv} (hc : C mn = some (child, cwe))
    (hX : ∀ w ∈ instOutWires child.outputs conns, w ∈ X) {w : String}
    (h : w ∈ stmtInstOuts C (Stmt.inst mn iname conns)) : w ∈ connX X conns := by
  unfold Tools.ShippingHierOpen.stmtInstOuts at h
  simp only [hc] at h
  obtain ⟨p, -, hpc⟩ := Tools.ShippingOutsExtractedParts.instOutWires_port h
  exact mem_connX hpc (hX w h)

/-- The instance outputs of a body are among its `X`-wires. -/
theorem bodyInstOuts_sub {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {X : List String} :
    ∀ (body : List Stmt), InstsIn C X body →
      ∀ w, w ∈ bodyInstOuts C body → w ∈ outsX X body
  | [], _, w, h => by
    have h' : w ∈ ([] : List String) := h
    cases h'
  | st :: rest, H, w, h => by
    have h' : w ∈ stmtInstOuts C st ++ bodyInstOuts C rest := h
    have ih := bodyInstOuts_sub (C := C) (X := X) rest H.tail w
    cases st with
    | inst mn i conns =>
      obtain ⟨child, cwe, hc, hX, -⟩ := H mn i conns (List.Mem.head _)
      show w ∈ connX X conns ++ outsX X rest
      rcases List.mem_append.mp h' with h1 | h1
      · exact List.mem_append_left _ (stmtInstOuts_sub hc hX h1)
      · exact List.mem_append_right _ (ih h1)
    | _ =>
      show w ∈ outsX X rest
      rcases List.mem_append.mp h' with h1 | h1
      · have h0 : w ∈ ([] : List String) := h1
        cases h0
      · exact ih h1

/-- The linked writes of a body are among the guard's writes. -/
theorem linkedWrites_sub {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {X : List String} :
    ∀ (body : List Stmt), InstsIn C X body →
      ∀ w, w ∈ linkedWrites C body → w ∈ writesX X body
  | [], _, w, h => by
    have h' : w ∈ ([] : List String) := h
    cases h'
  | st :: rest, H, w, h => by
    have ih := linkedWrites_sub (C := C) (X := X) rest H.tail w
    cases st with
    | assign l r =>
      have h' : w ∈ l :: linkedWrites C rest := h
      show w ∈ l :: writesX X rest
      rcases List.mem_cons.mp h' with e | h1
      · rw [e]
        exact List.Mem.head _
      · exact List.Mem.tail _ (ih h1)
    | inst mn i conns =>
      obtain ⟨child, cwe, hc, hX, -⟩ := H mn i conns (List.Mem.head _)
      have h' : w ∈ stmtInstOuts C (Stmt.inst mn i conns) ++ linkedWrites C rest := h
      show w ∈ connX X conns ++ writesX X rest
      rcases List.mem_append.mp h' with h1 | h1
      · exact List.mem_append_left _ (stmtInstOuts_sub hc hX h1)
      · exact List.mem_append_right _ (ih h1)
    | _ =>
      have h1 : w ∈ linkedWrites C rest := h
      show w ∈ writesX X rest
      exact ih h1

/-- **G2 is sound**: the guard's linked order implies `linkedWF`, for every
child map whose instance outputs are in `X` and distinct per instance. -/
theorem linkedWFX_sound {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {X : List String} :
    ∀ (body : List Stmt), InstsIn C X body → linkedWFX X body = true →
      linkedWF C body = true
  | [], _, _ => rfl
  | st :: rest, H, h => by
    cases st with
    | assign l r =>
      simp only [Sparkle.IR.HierCheck.linkedWFX, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have ih := linkedWFX_sound (C := C) (X := X) rest H.tail h3
      have hl : l ∉ outsX X rest := by simpa [List.contains_eq_mem] using h1
      have hlC : l ∉ bodyInstOuts C rest := fun hm => hl (bodyInstOuts_sub rest H.tail l hm)
      simp only [Tools.ShippingHierOpen.linkedWF, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ih⟩
      · simpa [List.contains_eq_mem] using hlC
      · rw [List.all_eq_true] at h2 ⊢
        intro n hn
        have hn' : n ∉ outsX X rest := by simpa [List.contains_eq_mem] using h2 n hn
        have hnC : n ∉ bodyInstOuts C rest := fun hm => hn' (bodyInstOuts_sub rest H.tail n hm)
        simpa [List.contains_eq_mem] using hnC
    | inst mn i conns =>
      obtain ⟨child, cwe, hc, hX, hnd⟩ := H mn i conns (List.Mem.head _)
      simp only [Sparkle.IR.HierCheck.linkedWFX, Bool.and_eq_true] at h
      obtain ⟨h1, h3⟩ := h
      have ih := linkedWFX_sound (C := C) (X := X) rest H.tail h3
      -- no connected wire is written afterwards
      have hconn : ∀ (nm w : String), (nm, Expr.ref w) ∈ conns → w ∉ linkedWrites C rest := by
        intro nm w hm hw
        have h0 := List.all_eq_true.mp h1 (nm, Expr.ref w) hm
        have h' : (!(writesX X rest).contains w) = true := h0
        have hnw : w ∉ writesX X rest := by simpa [List.contains_eq_mem] using h'
        exact hnw (linkedWrites_sub rest H.tail w hw)
      simp only [Tools.ShippingHierOpen.linkedWF, hc, Bool.and_eq_true]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ih⟩
      · rw [List.all_eq_true]
        intro w hw
        obtain ⟨p, -, hpc⟩ := Tools.ShippingOutsExtractedParts.instOutWires_port hw
        have hnw := hconn p.name w hpc
        simpa [List.contains_eq_mem] using hnw
      · first | exact decide_eq_true hnd | exact hnd
      · rw [List.all_eq_true]
        intro cn hcn
        obtain ⟨nm, e⟩ := cn
        cases e with
        | ref w =>
          have hnw := hconn nm w hcn
          have h2 : (!(linkedWrites C rest).contains w) = true := by
            simpa [List.contains_eq_mem] using hnw
          show ((instOutWires child.outputs conns).contains w ||
            !(linkedWrites C rest).contains w) = true
          rw [h2, Bool.or_true]
        | _ => rfl
    | register o c rk inp iv =>
      have h3 : linkedWFX X rest = true := by
        simp only [Sparkle.IR.HierCheck.linkedWFX] at h
        exact h
      have ih := linkedWFX_sound (C := C) (X := X) rest H.tail h3
      simp only [Tools.ShippingHierOpen.linkedWF]
      exact ih
    | _ => simp [Sparkle.IR.HierCheck.linkedWFX] at h

/-- Under `linkedWF`, an instance statement resolves and its output wires
are pairwise distinct. -/
theorem linkedWF_inst {C : String → Option (Sparkle.IR.AST.Module × WEnv)} :
    ∀ (body : List Stmt), linkedWF C body = true →
      ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
        ∃ child cwe, C mn = some (child, cwe) ∧ (instOutWires child.outputs conns).Nodup
  | [], _, mn, iname, conns, hm => by cases hm
  | st :: rest, h, mn, iname, conns, hm => by
    rcases List.mem_cons.mp hm with e | hm'
    · subst e
      cases hc : C mn with
      | none => simp [Tools.ShippingHierOpen.linkedWF, hc] at h
      | some cw =>
        obtain ⟨child, cwe⟩ := cw
        simp only [Tools.ShippingHierOpen.linkedWF, hc, Bool.and_eq_true] at h
        obtain ⟨⟨⟨-, hnd⟩, -⟩, -⟩ := h
        exact ⟨child, cwe, rfl, of_decide_eq_true hnd⟩
    · have hrest : linkedWF C rest = true := by
        cases st with
        | assign l r =>
          simp only [Tools.ShippingHierOpen.linkedWF, Bool.and_eq_true] at h
          exact h.2
        | inst mn' i' conns' =>
          simp only [Tools.ShippingHierOpen.linkedWF, Bool.and_eq_true] at h
          exact h.2
        | register o c rk inp iv =>
          simp only [Tools.ShippingHierOpen.linkedWF] at h
          exact h
        | _ => simp [Tools.ShippingHierOpen.linkedWF] at h
      exact linkedWF_inst (C := C) rest hrest mn iname conns hm'

/-- An output wire of an instance statement of the body is an instance
output of the body. -/
theorem mem_bodyInstOuts_of {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {mn iname : String} {conns : List (String × Expr)} {w : String} :
    ∀ (body : List Stmt), Stmt.inst mn iname conns ∈ body →
      w ∈ stmtInstOuts C (Stmt.inst mn iname conns) → w ∈ bodyInstOuts C body
  | [], hm, _ => by cases hm
  | st :: rest, hm, hw => by
    show w ∈ stmtInstOuts C st ++ bodyInstOuts C rest
    rcases List.mem_cons.mp hm with e | hm'
    · subst e
      exact List.mem_append_left _ hw
    · exact List.mem_append_right _ (mem_bodyInstOuts_of (C := C) rest hm' hw)

/-- **The guard's hypothesis from `m`**: a body whose instance statements
are among `m`'s, `m.body` linked-well-formed, `m`'s instance outputs in `X`. -/
theorem instsIn_of {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {X : List String}
    {m o : Sparkle.IR.AST.Module} (hwf : linkedWF C m.body = true)
    (hX : ∀ w ∈ bodyInstOuts C m.body, w ∈ X)
    (hOM : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
      Stmt.inst mn iname conns ∈ m.body) : InstsIn C X o.body := by
  intro mn iname conns hm
  have hmM := hOM mn iname conns hm
  obtain ⟨child, cwe, hc, hnd⟩ := linkedWF_inst m.body hwf mn iname conns hmM
  refine ⟨child, cwe, hc, fun w hw => hX w (mem_bodyInstOuts_of m.body hmM ?_), hnd⟩
  unfold Tools.ShippingHierOpen.stmtInstOuts
  simp only [hc]
  exact hw

/-- **Conjuncts 2 and 4 of an accepted candidate**: the guarded candidate
the interface check accepted is linked-well-formed and has distinct
instance names. -/
theorem deinline_guards {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {m o : Sparkle.IR.AST.Module}
    (hchk : hierRefineCheck m (Sparkle.IR.HierCheck.deinline m o) = true)
    (hwf : linkedWF C m.body = true)
    (hnd : (Tools.ShippingHierState.instNames m.body).Nodup)
    (hout : Tools.ShippingHierPremisesBase.outsExtracted C m = true) :
    linkedWF C (Sparkle.IR.HierCheck.deinline m o).body = true ∧
      (Tools.ShippingHierState.instNames (Sparkle.IR.HierCheck.deinline m o).body).Nodup := by
  rcases Sparkle.IR.HierCheck.deinline_cases m o with ⟨-, h4, h2⟩ | e
  · refine ⟨linkedWFX_sound (Sparkle.IR.HierCheck.deinline m o).body
      (instsIn_of (o := Sparkle.IR.HierCheck.deinline m o) hwf
        (Tools.ShippingHierPremisesBase.outsExtracted_sound hout)
        (fun mn iname conns =>
          (Tools.ShippingChecksDerived2.hierRefineCheck_inst_iff hchk mn iname conns).mp)) h2, ?_⟩
    rw [← instNamesOf_eq]
    exact h4
  · rw [e]
    exact ⟨hwf, hnd⟩

/-- A module passing the statement-kind gate has an instance statement. -/
theorem hasInst_of_hierGate {m : Sparkle.IR.AST.Module} (h : hierGate m = true) :
    Tools.ShippingMachineShipsHier.hasInst m := by
  simp only [Sparkle.IR.RefineCheck.hierGate, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨st, hst, hi⟩, -⟩ := h
  cases st with
  | inst mn iname conns => exact ⟨mn, iname, conns, hst⟩
  | _ => simp at hi

/-- An instance / assignment / register module on which the hierarchical
check does not bind is shipped unoptimized. -/
theorem checkedOptimize_not_binding {b : Sparkle.IR.AST.Module} (hgate : hierGate b = true)
    (hb0 : hierBinds b = false) : checkedOptimize b = b := by
  have hI := hasInst_of_hierGate hgate
  unfold Sparkle.IR.OptCheck.checkedOptimize
  simp only [Tools.ShippingMachineShipsHier.simpleBody_inst hI,
    Tools.ShippingMachineShipsHier.not_all_seqOk hI, hb0, hgate, Bool.false_eq_true, if_false,
    if_true]

/-- On a binding module the shipped module is the accepted guarded candidate
or the module itself. -/
theorem checkedOptimize_binding {b : Sparkle.IR.AST.Module} (hb : hierBinds b = true) :
    checkedOptimize b = (if hierRefineCheck b
      (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b))
      then Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
  have hI := Tools.ShippingMachineShipsHier.hasInst_of_hierBinds hb
  unfold Sparkle.IR.OptCheck.checkedOptimize
  simp only [Tools.ShippingMachineShipsHier.simpleBody_inst hI,
    Tools.ShippingMachineShipsHier.not_all_seqOk hI, hb, Bool.false_eq_true, if_false, if_true]

/-- **What the core run of a machine with calls provides of the full
entry's module** (each field is derived from the run: `core_hierGate`,
`core_linkedWF`, `core_raw_facts`, `core_outsExtracted`,
`core_instOutWidthsOk`). -/
structure RunFacts (C : String → Option (Sparkle.IR.AST.Module × WEnv))
    (b : Sparkle.IR.AST.Module) : Prop where
  gate : hierGate b = true
  wfB : linkedWF C b.body = true
  ndB : (Tools.ShippingHierState.instNames b.body).Nodup
  self : Tools.ShippingHierPremisesBase.noSelfRead C b.body = true
  outs : Tools.ShippingHierPremisesBase.outsExtracted C b = true
  rst : "rst" ∈ b.inputs.map (·.name)
  wid : instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth b) b.body = true

/-- **The shipped module, whatever branch the compiler took**: it is
linked-well-formed, its instance names are distinct, and it has the full
entry's inputs (conjuncts 2 and 4 of `shipsHierCheck`, and
`checkedOptimize_inputs`, with NO `hierBinds` premise). -/
theorem checkedOptimize_facts {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {b : Sparkle.IR.AST.Module} (hgate : hierGate b = true)
    (hwfB : linkedWF C b.body = true)
    (hndB : (Tools.ShippingHierState.instNames b.body).Nodup)
    (hOut : Tools.ShippingHierPremisesBase.outsExtracted C b = true) :
    linkedWF C (checkedOptimize b).body = true ∧
      (Tools.ShippingHierState.instNames (checkedOptimize b).body).Nodup ∧
      (checkedOptimize b).inputs = b.inputs := by
  by_cases hbind : hierBinds b = true
  · rw [checkedOptimize_binding hbind]
    by_cases hacc : hierRefineCheck b
        (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
    · rw [if_pos hacc]
      obtain ⟨h2, h4⟩ := deinline_guards hacc hwfB hndB hOut
      exact ⟨h2, h4, Tools.ShippingHierShipsSV.hierRefineCheck_inputs hacc⟩
    · rw [if_neg hacc]
      exact ⟨hwfB, hndB, rfl⟩
  · have hb0 : hierBinds b = false := by simpa using hbind
    rw [checkedOptimize_not_binding hgate hb0]
    exact ⟨hwfB, hndB, rfl⟩

end Tools.ShippingGuardsSound
