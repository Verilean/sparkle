import Tools.VedU2HierReg

/-!
# `U2HRStmtK`: the hierarchical statement for children with k ≥ 1 outputs (CANDIDATE, not reviewed)

`U2HRStmt` (Tools/VedU2HierReg.lean) is unchanged and is false for a design with a child that has
two or more outputs, because `HierShapeS` -> `connsOkS` contains `c.outputs.length == 1`.  This file
adds a SEPARATE statement for the wider shape (user decision 2026-11-23, option 3).

* `connsOkK` is `connsOkS` with `c.outputs.length == 1` replaced by `1 ≤ c.outputs.length`, plus two
  clauses that are trivial for one output: the child's output port names are pairwise distinct, and
  the parent wires the child's outputs are connected to are pairwise distinct.
  NO OUTPUT IS DROPPED: the clause `(c.inputs ++ c.outputs).all (fun p => cs.any (· .1 == p.name))`
  (already in `connsOkS`) requires every input AND every output port to be connected, the clause
  `cs.all (… .ref x …)` requires each connection to be a plain wire, and its width test requires
  `declWidth m x == p.ty.bitWidth` (each output wire has the width of its port).
* `HierShapeK` is `HierShapeS` with `connsOkK` (every other clause is the same).
* `U2HRStmtK` is `U2HRStmt` with `HierShapeS d m = true` replaced by `HierShapeK d m = true`; every
  other conjunct is the SAME definition (`CorrStmt`, `ShapeCore`, `designClkRst`, `WidthStmt`,
  `OrderHS`, `OrderStmt`, `AdmArr`, `OutputsStmtHS`), none of which mentions the number of a child's
  outputs: the semantics (`instEvalS`, `outWrites`, `instOuts`/`wrH`) already writes EVERY connected
  output port (`outWrites` filters the connections on all output ports; the order check writes all
  output refs, so a parent wire written by two outputs / instances is refused by `WOH`).
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- The parent wires the child's output ports are connected to (a connection of an output port to
anything but a plain wire is refused by `connsOkK`). -/
def outRefNames (c : Module) (cs : List (String × Expr)) : List String :=
  (cs.filter (fun q => c.outputs.any (·.name == q.1))).filterMap fun q =>
    match q.2 with
    | .ref x => some x
    | _ => none

/-- One `inst` against the design, k ≥ 1 outputs: `connsOkS` with `c.outputs.length == 1` replaced
by `1 ≤ c.outputs.length`, distinct output port names and distinct output wires added. -/
def connsOkK (d : Design) (m : Module) (mn : String) (cs : List (String × Expr)) : Bool :=
  match findMod d mn with
  | none => false
  | some c =>
    !c.isPrimitive && c.parameters.isEmpty && c.assertions.isEmpty && leafBody c.body &&
    childSane c &&
    decide (1 ≤ c.outputs.length) && decide (c.outputs.map (·.name)).Nodup &&
    decide (outRefNames c cs).Nodup &&
    decide (cs.map (·.1)).Nodup &&
    (c.inputs ++ c.outputs).all (fun p => cs.any (fun q => q.1 == p.name)) &&
    cs.all (fun q => (c.inputs ++ c.outputs).any (fun p => p.name == q.1)) &&
    cs.all (fun q => match q.2 with
      | .ref x => (c.inputs ++ c.outputs).any
          (fun p => p.name == q.1 && scalar p.ty &&
            (declWidth m x == p.ty.bitWidth || isClkRstPort c p.name))
      | _ => false)

/-- `HierShapeS` with `connsOkK`. -/
def HierShapeK (d : Design) (m : Module) : Bool :=
  d.topModule == m.name && decide (d.modules.map (·.name)).Nodup &&
  !((d.modules.map (·.name)).contains m.name) &&
  m.body.all isAsgInstReg &&
  m.body.all (fun s => match s with
    | .inst mn _ cs => connsOkK d m mn cs
    | _ => true) &&
  decide (instNames m.body).Nodup &&
  d.modules.all (fun c => m.body.any (fun s => match s with
    | .inst mn _ _ => mn == c.name
    | _ => false)) &&
  clkRstOk d m

/-- CANDIDATE statement for a parent with registers whose children have one or more outputs:
`U2HRStmt` with `HierShapeS d m = true` replaced by `HierShapeK d m = true`. -/
def U2HRStmtK (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeK d m = true ∧
  WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f

/-! ## Coincidence with `U2HRStmt` -/

theorem filter_key_le_one {α : Type} (l : List (String × α)) (a : String)
    (h : (l.map Prod.fst).Nodup) : (l.filter (fun q => q.1 == a)).length ≤ 1 := by
  have hn : ((l.filter (fun q => q.1 == a)).map Prod.fst).Nodup :=
    h.sublist ((List.filter_sublist).map _)
  have hall : ∀ q ∈ l.filter (fun q => q.1 == a), q.1 = a := by
    intro q hq; simpa using (List.mem_filter.mp hq).2
  generalize l.filter (fun q => q.1 == a) = r at hn hall
  match r, hn, hall with
  | [], _, _ => simp
  | [_], _, _ => simp
  | x :: y :: t, hn, hall =>
    exfalso
    have h1 := hall x (by simp)
    have h2 := hall y (by simp)
    simp at hn
    exact hn.1.1 (h1.trans h2.symm)

/-- `connsOkS` gives `connsOkK` (a single output: the two added clauses are trivial). -/
theorem connsOkK_of_S {d : Design} {m : Module} {mn : String} {cs : List (String × Expr)}
    (h : connsOkS d m mn cs = true) : connsOkK d m mn cs = true := by
  obtain ⟨c, hf, _, _, _, _, hol, hcsnd, _⟩ := connsOkS_facts h
  have hs := h
  simp only [connsOkS, hf] at hs
  simp only [connsOkK, hf]
  have hn : (c.outputs.map (·.name)).Nodup := by
    match hc : c.outputs, hol with
    | [_], _ => simp
  have hr : (outRefNames c cs).Nodup := by
    unfold outRefNames
    obtain ⟨o, ho⟩ : ∃ o, c.outputs = [o] := by
      match hc : c.outputs, hol with
      | [o], _ => exact ⟨o, rfl⟩
    have hle := filter_key_le_one cs o.name hcsnd
    have hfe : (cs.filter (fun q => c.outputs.any (·.name == q.1))) = cs.filter (fun q => q.1 == o.name) := by
      apply List.filter_congr; intro q _; simp only [ho, List.any_cons, List.any_nil, Bool.or_false]; rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
    rw [hfe]
    generalize cs.filter (fun q => q.1 == o.name) = r at hle
    have : (r.filterMap fun q => match q.2 with | .ref x => some x | _ => none).length ≤ 1 :=
      Nat.le_trans (List.length_filterMap_le _ _) hle
    generalize (r.filterMap fun q => match q.2 with | .ref x => some x | _ => none) = z at this
    match z, this with
    | [], _ => simp
    | [_], _ => simp
    | _ :: _ :: _, h => simp at h
  have hl : 1 ≤ c.outputs.length := by omega
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq, and_assoc] at hs ⊢
  obtain ⟨a1, a2, a3, a4, a5, _, a7, a8, a9, a10⟩ := hs
  exact ⟨a1, a2, a3, a4, a5, hl, hn, hr, a7, a8, a9, a10⟩

/-- Conversely, when the resolved child has exactly one output, `connsOkK` gives `connsOkS`. -/
theorem connsOkS_of_K {d : Design} {m : Module} {mn : String} {cs : List (String × Expr)}
    (h1 : ∀ x ∈ d.modules, x.outputs.length = 1) (h : connsOkK d m mn cs = true) :
    connsOkS d m mn cs = true := by
  simp only [connsOkK] at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c =>
    have hl := h1 c (findMod_mem hf)
    simp only [hf] at h
    simp only [connsOkS, hf]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq, and_assoc] at h ⊢
    obtain ⟨a1, a2, a3, a4, a5, _, _, _, a7, a8, a9, a10⟩ := h
    exact ⟨a1, a2, a3, a4, a5, hl, a7, a8, a9, a10⟩

theorem HierShapeK_of_S {d : Design} {m : Module} (h : HierShapeS d m = true) :
    HierShapeK d m = true := by
  have e5 : m.body.all (fun s => match s with
      | .inst mn _ cs => connsOkK d m mn cs
      | _ => true) = true := by
    rw [List.all_eq_true]
    intro s hs
    cases s with
    | inst mn i cs => exact connsOkK_of_S (hierS_inst_ok h hs)
    | _ => rfl
  simp only [HierShapeS, Bool.and_eq_true] at h
  simp only [HierShapeK, Bool.and_eq_true]
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, _⟩, a6⟩, a7⟩, a8⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, e5⟩, a6⟩, a7⟩, a8⟩

theorem HierShapeS_of_K {d : Design} {m : Module} (h1 : ∀ x ∈ d.modules, x.outputs.length = 1)
    (h : HierShapeK d m = true) : HierShapeS d m = true := by
  have e5 : m.body.all (fun s => match s with
      | .inst mn _ cs => connsOkS d m mn cs
      | _ => true) = true := by
    have hK : m.body.all (fun s => match s with
        | .inst mn _ cs => connsOkK d m mn cs
        | _ => true) = true := by
      simp only [HierShapeK, Bool.and_eq_true] at h
      exact h.1.1.1.2
    rw [List.all_eq_true] at hK ⊢
    intro s hs
    have := hK s hs
    cases s with
    | inst mn i cs => exact connsOkS_of_K h1 this
    | _ => rfl
  simp only [HierShapeK, Bool.and_eq_true] at h
  simp only [HierShapeS, Bool.and_eq_true]
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, _⟩, a6⟩, a7⟩, a8⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, e5⟩, a6⟩, a7⟩, a8⟩

/-- COINCIDENCE: when every module of the design has exactly one output, `U2HRStmtK` is `U2HRStmt`
(both directions; `U2HRStmt → U2HRStmtK` needs no hypothesis, see `U2HRStmtK_of_U2HRStmt`). -/
theorem U2HRStmtK_iff (c : Contract) (m : Module) (d : Design) (f : c.table.Ty)
    (h1 : ∀ x ∈ d.modules, x.outputs.length = 1) : U2HRStmtK c m d f ↔ U2HRStmt c m d f := by
  unfold U2HRStmtK U2HRStmt
  constructor
  · rintro ⟨a, b, c', d', e, f', g, h, i⟩
    exact ⟨a, b, c', HierShapeS_of_K h1 d', e, f', g, h, i⟩
  · rintro ⟨a, b, c', d', e, f', g, h, i⟩
    exact ⟨a, b, c', HierShapeK_of_S d', e, f', g, h, i⟩

theorem U2HRStmtK_of_U2HRStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty)
    (h : U2HRStmt c m d f) : U2HRStmtK c m d f := by
  obtain ⟨a, b, c', d', e, f', g, h, i⟩ := h
  exact ⟨a, b, c', HierShapeK_of_S d', e, f', g, h, i⟩

end Tools.VedU2Hier
