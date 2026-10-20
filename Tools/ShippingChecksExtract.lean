import Tools.ShippingChecksRaw

/-! # Conjuncts 6 and 8 of `shipsHierCheck`: what is there and what is missing (G1)

## Conjunct 6, `outsExtracted C b`

Every instance-driven wire `w` (`w ∈ bodyInstOuts C b.body`) must be the
name of an element of `openIns b`: a wire of `b` that (b) is in
`connRefs b.body`, (c) is not in `drivesOf b.body` (assignment targets and
register outputs), (d) is not an input name; and (a) is a declared wire.

* (b) PROVED here, from the definitions alone: `bodyInstOuts_connRefs`.
* (c), assignment targets: FOLLOWS from the linked well-formedness the
  wiring gives (`MachineWired` clause 7, `linkedOk_eq`): `linkedWF` says an
  assignment does not target an output of a LATER instance and an
  instance's outputs are never written afterwards. The induction over the
  body is NOT written here. Settled negatively: `WO [] m.body` does NOT
  give it — `stmtWrites` of an instance statement is `[]`
  (`Sparkle/IR/ReorderInvariance.lean:76`), so the write-once order knows
  nothing of instance outputs.
* (c), register outputs: MISSING. `drivesOf` also lists every register
  statement's output. For a machine with calls the wiring says each slot
  HAS its register statement (last clause) but not that every register
  statement is a slot's (that is stated only under `shape.insts = []`).
  Missing statement:

      for a machine with calls (the hypotheses of `core_kids_facts`):
      ∀ r c rs inp init, Stmt.register r c rs inp init ∈ M.body → r ∈ regs

  with which a register output is a port name at a slot position, a call
  port a port name at a call position, and the port names are distinct
  (`MachineWired` clause 1).
* (a) declared wire: FOLLOWS in principle from `CloseCalls.some`
  (`m.wires = m₀.wires`), `closeMachine_parts` (the transition's wires are
  the closed machine's), `closeLets` keeping the wires, and the transition's
  "every input is a wire" (`hinW` of `transition_calls_facts`) — but the
  last fact is internal to `closedBody_kinds_of_run`'s proof and no theorem
  exports it for a run. Missing statement:

      for the harness run of a machine (`run : MReturns (synthesizeMixedCertified …) (t, d₀)`
      under the hypotheses of `closedBody_kinds_of_run`):
      ∀ p ∈ t.inputs, p ∈ t.wires

  (it is `hinW` there; exporting it is a copy of that proof's first part).
* (d): from `MachineWired`'s input clause (the call ports are filtered out
  of the inputs), once `w` is identified as a call port through `CallStmtG`.

## Conjunct 8, `instOutWidthsOk C (declWidth b) b.body`, parent side

`CallStmtG` (`Tools/ShippingMachineInstG.lean:19`) has NO width component:
it states the connection list (child field names zipped with the call
ports), distinctness, and that the fields are output ports of the child. So
with `Tools.ShippingChildIfaceTy.ChildOutTys` (the child's port types) the
parent side still lacks, for each call `k` reading field `f` of child `c`
through the port `w = names[machNIn + k]`:

      declWidth b w = (the width of field `f` in `c`'s layout)

i.e. the declared type of the transition's port for the call's result is
the child's output field's type. The front end allocates that port from the
call's result type; no theorem states it. That is the missing statement.

`core_shipsHier_rest` (`Tools/ShippingChecksRaw.lean`) is therefore
UNCHANGED: 6 and 8 stay hypotheses.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksExtract
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierOpen

/-- An instance-output wire is the reference of a connection. -/
theorem instOutWires_conn {outs : List Port} {conns : List (String × Expr)} {w : String}
    (h : w ∈ instOutWires outs conns) : ∃ nm, (nm, Expr.ref w) ∈ conns := by
  unfold Tools.ShippingHierOpen.instOutWires at h
  obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp h
  cases hl : conns.lookup p.name with
  | none =>
    rw [hl] at hp
    have hp' : (none : Option String) = some w := hp
    cases hp'
  | some e =>
    rw [hl] at hp
    cases e with
    | ref v =>
      have hv : some v = some w := hp
      cases hv
      obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hl
      exact ⟨p.name, by rw [e]; exact List.mem_append_right _ (List.Mem.head _)⟩
    | _ =>
      have hp' : (none : Option String) = some w := hp
      cases hp'

/-- A wire a statement's instance drives is the reference of a connection of
that instance statement. -/
theorem stmtInstOuts_conn {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {st : Stmt}
    {w : String} (h : w ∈ stmtInstOuts C st) :
    ∃ mn i conns nm, st = Stmt.inst mn i conns ∧ (nm, Expr.ref w) ∈ conns := by
  cases st with
  | inst mn i conns =>
    unfold Tools.ShippingHierOpen.stmtInstOuts at h
    cases hc : C mn with
    | none =>
      simp only [hc] at h
      cases h
    | some cw =>
      obtain ⟨child, cwe⟩ := cw
      simp only [hc] at h
      obtain ⟨nm, hnm⟩ := instOutWires_conn h
      exact ⟨mn, i, conns, nm, rfl, hnm⟩
  | _ =>
    have h' : w ∈ ([] : List String) := h
    cases h'

/-- **(b)**: every instance-driven wire is a connected wire. -/
theorem bodyInstOuts_connRefs {C : String → Option (Sparkle.IR.AST.Module × WEnv)} :
    ∀ (body : List Stmt) (w : String), w ∈ bodyInstOuts C body →
      w ∈ Sparkle.IR.HierCheck.connRefs body
  | [], w, h => by
    have h' : w ∈ ([] : List String) := h
    cases h'
  | st :: rest, w, h => by
    have h' : w ∈ stmtInstOuts C st ++ bodyInstOuts C rest := h
    have ih := bodyInstOuts_connRefs (C := C) rest w
    unfold Sparkle.IR.HierCheck.connRefs at ih ⊢
    rw [List.flatMap_cons]
    rcases List.mem_append.mp h' with h1 | h1
    · refine List.mem_append_left _ ?_
      obtain ⟨mn, i, conns, nm, e, hm⟩ := stmtInstOuts_conn h1
      subst e
      exact List.mem_filterMap.mpr ⟨(nm, Expr.ref w), hm, rfl⟩
    · exact List.mem_append_right _ (ih h1)

end Tools.ShippingChecksExtract
