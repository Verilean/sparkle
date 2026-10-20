import Tools.ShippingGateDesignWalk

variable {tenv : Lean.Environment}

/-! # Gate-route parents: the design walk extended by names, order and connections (worker N, round 13)

WRITTEN, NOT BUILT.

`Tools.ShippingGateDesignWalk`'s invariant `DOk` records statement SHAPES
only. The checker conjuncts left on the seven `…_gate_designSVN`
(`combSideB`: linked order, distinct instance names, no self read, extracted
instance outputs, combinational children) need what the builder knows about
NAMES. This file adds a second invariant, `NOk G I s`, walked through the
SAME fuel walk (input binders, canonical binary nodes, canonical comparisons,
instance calls whose arguments are such cones):

* every name a body statement mentions (`stmtNamesN`: an assignment's target
  and reads, an instance's connected wires), every instance name and every
  input port name `I` is RESERVED (`usedNames`), and every reserved name is
  ALLOCATED (`_gen_…` / `_tmp_…`, never `out`);
* the body is assignments and instances, its instance names are distinct;
* ORDER (`ord`): a statement's written wire (`WritesN`: an assignment's
  target, an instance's last connection) is mentioned by NO earlier
  statement — the builder allocates a written wire fresh, and a wire
  allocated but not yet written is mentioned by nothing (`PendN`);
* every instance names a module `x` with `G x` and CONNECTIONS keyed by the
  callee's input ports (`ConnOkN`): `cs = ins ++ [(o, ref w)]`, `ins` keyed
  exactly by `x`'s input names, every input connection a wire other than
  the output wire `w`, `o` the one output port and not an input name;
* every written wire is a declared wire and not an input; every recorded
  translation names a mentioned wire.

`NamW L mF D rec ctx G I e`: every returning run of `rec e …` keeps `NOk`,
grows the state (`NGrows`), mentions no pending name (`PendN`), and returns
an input wire or a mentioned wire (`RetN`). Nodes: `namW_fvar`,
`namW_binary`, `namW_compare`, `namW_inst` (with `instUncached_namW`, the
round-11 `instUncached_desW` with the fresh wire and the instance name
exposed, and `instArgs_namW`: the connections are keyed by the callee's
inputs in order). -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

/-! ## Names, writes, order -/

section names
open Sparkle.IR.AST Sparkle.IR.Builder

/-- The wire a connection carries. -/
def connRefN (c : String × Sparkle.IR.AST.Expr) : Option String :=
  match c.2 with
  | .ref x => some x
  | _ => none

/-- The names a statement mentions: an assignment's target and reads, an
instance's connected wires. -/
def stmtNamesN : Stmt → List String
  | .assign l r => l :: Sparkle.IR.Reorder.refsOf r
  | .inst _ _ cs => cs.filterMap connRefN
  | _ => []

theorem stmtNamesN_assign (l : String) (r : Sparkle.IR.AST.Expr) :
    stmtNamesN (.assign l r) = l :: Sparkle.IR.Reorder.refsOf r := rfl

theorem stmtNamesN_inst (mn i : String) (cs : List (String × Sparkle.IR.AST.Expr)) :
    stmtNamesN (.inst mn i cs) = cs.filterMap connRefN := rfl

theorem mem_stmtNamesN_inst {mn i k x : String} {cs : List (String × Sparkle.IR.AST.Expr)}
    (h : (k, Sparkle.IR.AST.Expr.ref x) ∈ cs) : x ∈ stmtNamesN (.inst mn i cs) := by
  rw [stmtNamesN_inst]
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem mem_stmtNamesN_bin {l a b x : String} {o : Operator}
    (h : x ∈ stmtNamesN (.assign l (.op o [.ref a, .ref b]))) : x = l ∨ x = a ∨ x = b := by
  simpa [stmtNamesN, Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList] using h

theorem connRefN_of {c : String × Sparkle.IR.AST.Expr} {a : String}
    (h : c.2 = Sparkle.IR.AST.Expr.ref a) : connRefN c = some a := by
  unfold connRefN
  rw [h]

/-- `T` writes `x`: an assignment's target, or an instance's last
connection. -/
def WritesN (T : Stmt) (x : String) : Prop :=
  (∃ r, T = Stmt.assign x r) ∨
    (∃ (mn i o : String) (ins : List (String × Sparkle.IR.AST.Expr)),
      T = Stmt.inst mn i (ins ++ [(o, Sparkle.IR.AST.Expr.ref x)]))

theorem writesN_names {T : Stmt} {x : String} (h : WritesN T x) : x ∈ stmtNamesN T := by
  rcases h with ⟨r, rfl⟩ | ⟨mn, i, o, ins, rfl⟩
  · rw [stmtNamesN_assign]
    exact List.mem_cons_self
  · exact mem_stmtNamesN_inst (List.mem_append_right _ (List.mem_singleton_self _))

theorem writesN_assign {l x : String} {r : Sparkle.IR.AST.Expr} (h : WritesN (.assign l r) x) :
    x = l := by
  rcases h with ⟨r', he⟩ | ⟨mn, i, o, ins, he⟩
  · exact ((Stmt.assign.inj he).1).symm
  · cases he

theorem writesN_inst {mn i o w x : String} {ins : List (String × Sparkle.IR.AST.Expr)}
    (h : WritesN (.inst mn i (ins ++ [(o, Sparkle.IR.AST.Expr.ref w)])) x) : x = w := by
  rcases h with ⟨r, he⟩ | ⟨mn', i', o', ins', he⟩
  · cases he
  · have h3 := (Stmt.inst.inj he).2.2
    have h4 := (List.append_inj' h3 rfl).2
    have h5 := (List.cons.inj h4).1
    have h6 := (Prod.mk.inj h5).2
    exact (Sparkle.IR.AST.Expr.ref.inj h6).symm

theorem writesN_inst_mem {mn i w : String} {cs : List (String × Sparkle.IR.AST.Expr)}
    (h : WritesN (.inst mn i cs) w) : ∃ o, (o, Sparkle.IR.AST.Expr.ref w) ∈ cs := by
  rcases h with ⟨r, he⟩ | ⟨mn', i', o, ins, he⟩
  · cases he
  · refine ⟨o, ?_⟩
    rw [(Stmt.inst.inj he).2.2]
    exact List.mem_append_right _ (List.mem_singleton_self _)

/-- `S` (earlier) mentions nothing `T` (later) writes. -/
abbrev RWN (S T : Stmt) : Prop := ∀ x, WritesN T x → x ∉ stmtNamesN S

/-- An instance's connections, keyed by the callee's ports (file header). -/
def ConnOkN (x : Sparkle.IR.AST.Module) (cs : List (String × Sparkle.IR.AST.Expr)) : Prop :=
  ∃ (ins : List (String × Sparkle.IR.AST.Expr)) (o : String) (k : Nat) (w : String),
    x.outputs = [⟨o, .bitVector k⟩] ∧ cs = ins ++ [(o, Sparkle.IR.AST.Expr.ref w)] ∧
    ins.map Prod.fst = x.inputs.map (·.name) ∧
    (∀ c ∈ ins, ∃ a, c.2 = Sparkle.IR.AST.Expr.ref a ∧ a ≠ w) ∧
    o ∉ x.inputs.map (·.name)

/-- The instance names of a body, as `Tools.ShippingHierState.instNames`. -/
theorem mem_instNamesN {i : String} :
    ∀ {B : List Stmt}, i ∈ Tools.ShippingHierState.instNames B →
      ∃ mn cs, Stmt.inst mn i cs ∈ B
  | [], h => by simp [Tools.ShippingHierState.instNames] at h
  | st :: rest, h => by
    cases st with
    | inst mn i' cs =>
      have h' : i ∈ i' :: Tools.ShippingHierState.instNames rest := h
      rcases List.mem_cons.mp h' with he | h'
      · subst he
        exact ⟨mn, cs, List.mem_cons_self⟩
      · obtain ⟨mn', cs', hm⟩ := mem_instNamesN h'
        exact ⟨mn', cs', List.mem_cons_of_mem _ hm⟩
    | assign l r =>
      obtain ⟨mn', cs', hm⟩ := mem_instNamesN (B := rest) h
      exact ⟨mn', cs', List.mem_cons_of_mem _ hm⟩
    | register a b c d e =>
      obtain ⟨mn', cs', hm⟩ := mem_instNamesN (B := rest) h
      exact ⟨mn', cs', List.mem_cons_of_mem _ hm⟩
    | memory =>
      obtain ⟨mn', cs', hm⟩ := mem_instNamesN (B := rest) h
      exact ⟨mn', cs', List.mem_cons_of_mem _ hm⟩

/-- `out` is not an allocated name. -/
theorem nAllocOutN : ¬ Sparkle.IR.NameHints.Allocated "out" := by
  intro h
  have := h.2
  revert this
  decide

/-! ## The invariant -/

/-- **The naming invariant** (file header). -/
structure NOk (G : Sparkle.IR.AST.Module → Prop) (I : List String) (s : CircuitState) : Prop where
  ins : s.module.inputs.map (·.name) = I
  inU : ∀ x ∈ I, s.usedNames.contains x = true
  alloc : ∀ x, s.usedNames.contains x = true → Sparkle.IR.NameHints.Allocated x
  kinds : ∀ st ∈ s.module.body,
    (∃ l r, st = Stmt.assign l r) ∨ (∃ mn i cs, st = Stmt.inst mn i cs)
  nmU : ∀ st ∈ s.module.body, ∀ x ∈ stmtNamesN st, s.usedNames.contains x = true
  iU : ∀ mn i cs, Stmt.inst mn i cs ∈ s.module.body → s.usedNames.contains i = true
  nd : (Tools.ShippingHierState.instNames s.module.body).Nodup
  ord : s.module.body.Pairwise (fun T S => RWN S T)
  conn : ∀ mn i cs, Stmt.inst mn i cs ∈ s.module.body →
    ∃ x, G x ∧ x.name = mn ∧ ConnOkN x cs
  wr : ∀ st ∈ s.module.body, ∀ x, WritesN st x →
    x ∈ s.module.wires.map (·.name) ∧ x ∉ I
  recs : ∀ w e, s.translateRecord.get? w = some e → ∃ st ∈ s.module.body, w ∈ stmtNamesN st

/-- The state grows: reservations, statements, wires. -/
def NGrows (s t : CircuitState) : Prop :=
  (∀ x, s.usedNames.contains x = true → t.usedNames.contains x = true) ∧
    (∀ st ∈ s.module.body, st ∈ t.module.body) ∧
    (∀ x ∈ s.module.wires.map (·.name), x ∈ t.module.wires.map (·.name))

theorem NGrows.refl (s : CircuitState) : NGrows s s :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem NGrows.trans {s t u : CircuitState} (h1 : NGrows s t) (h2 : NGrows t u) : NGrows s u :=
  ⟨fun x h => h2.1 x (h1.1 x h), fun st h => h2.2.1 st (h1.2.1 st h),
    fun x h => h2.2.2 x (h1.2.2 x h)⟩

/-- A pending name: reserved, not an input, mentioned by no statement. -/
def FreshN (I : List String) (s : CircuitState) (x : String) : Prop :=
  s.usedNames.contains x = true ∧ x ∉ I ∧ ∀ st ∈ s.module.body, x ∉ stmtNamesN st

/-- A run mentions no name pending at its start. -/
def PendN (I : List String) (s t : CircuitState) : Prop :=
  ∀ x, FreshN I s x → ∀ st ∈ t.module.body, x ∉ stmtNamesN st

theorem PendN.refl {I : List String} {s : CircuitState} : PendN I s s := fun _ hx => hx.2.2

theorem PendN.fresh {I : List String} {s t : CircuitState} {x : String} (hp : PendN I s t)
    (hg : NGrows s t) (hx : FreshN I s x) : FreshN I t x :=
  ⟨hg.1 x hx.1, hx.2.1, hp x hx⟩

theorem PendN.trans {I : List String} {s t u : CircuitState} (h1 : PendN I s t) (g1 : NGrows s t)
    (h2 : PendN I t u) : PendN I s u :=
  fun x hx => h2 x (h1.fresh g1 hx)

theorem PendN.of_body {I : List String} {s t : CircuitState}
    (hb : ∀ st ∈ t.module.body, st ∈ s.module.body) : PendN I s t :=
  fun _ hx st hst => hx.2.2 st (hb st hst)

/-- A returned wire: an input, or a wire some statement mentions. -/
def RetN (I : List String) (s : CircuitState) (w : String) : Prop :=
  w ∈ I ∨ ∃ st ∈ s.module.body, w ∈ stmtNamesN st

theorem RetN.mono {I : List String} {s t : CircuitState} {w : String} (hg : NGrows s t)
    (h : RetN I s w) : RetN I t w := by
  rcases h with h | ⟨st, hst, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨st, hg.2.1 st hst, hw⟩

theorem RetN.used {G : Sparkle.IR.AST.Module → Prop} {I : List String} {s : CircuitState}
    {w : String} (h : RetN I s w) (hok : NOk G I s) : s.usedNames.contains w = true := by
  rcases h with h | ⟨st, hst, hw⟩
  · exact hok.inU w h
  · exact hok.nmU st hst w hw

theorem RetN.ne {I : List String} {s : CircuitState} {w x : String} (h : RetN I s w)
    (hx : FreshN I s x) : w ≠ x := by
  intro he
  subst he
  rcases h with h | ⟨st, hst, hw⟩
  · exact hx.2.1 h
  · exact hx.2.2 st hst hw

/-! ## The builder steps -/

/-- **A step that keeps the body** keeps `NOk`. -/
theorem NOk.transfer {G : Sparkle.IR.AST.Module → Prop} {I : List String} {s t : CircuitState}
    (h : NOk G I s)
    (hb : t.module.body = s.module.body) (hi : t.module.inputs = s.module.inputs)
    (hw : ∀ x ∈ s.module.wires.map (·.name), x ∈ t.module.wires.map (·.name))
    (hu : ∀ x, s.usedNames.contains x = true → t.usedNames.contains x = true)
    (ha : ∀ x, t.usedNames.contains x = true → Sparkle.IR.NameHints.Allocated x)
    (hr : ∀ w e, t.translateRecord.get? w = some e → s.translateRecord.get? w = some e) :
    NOk G I t where
  ins := by rw [hi]; exact h.ins
  inU := fun x hx => hu x (h.inU x hx)
  alloc := ha
  kinds := by rw [hb]; exact h.kinds
  nmU := by
    rw [hb]
    exact fun st hst x hx => hu x (h.nmU st hst x hx)
  iU := by
    rw [hb]
    exact fun mn i cs hm => hu i (h.iU mn i cs hm)
  nd := by rw [hb]; exact h.nd
  ord := by rw [hb]; exact h.ord
  conn := by rw [hb]; exact h.conn
  wr := by
    rw [hb]
    exact fun st hst x hx => ⟨hw x (h.wr st hst x hx).1, (h.wr st hst x hx).2⟩
  recs := by
    intro w e he
    rw [hb]
    exact h.recs w e (hr w e he)

theorem used_makeWire (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool)
    (s : CircuitState) {x : String} (hx : s.usedNames.contains x = true) :
    (CircuitM.makeWire hint ty named s).2.usedNames.contains x = true := by
  rw [(CircuitM.makeWire_spec hint ty named s).2.1]
  simp [Std.HashSet.contains_insert, hx]

theorem wire_makeWire (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool)
    (s : CircuitState) :
    (CircuitM.makeWire hint ty named s).1 ∈
      (CircuitM.makeWire hint ty named s).2.module.wires.map (·.name) := by
  rw [(CircuitM.makeWire_spec hint ty named s).2.2.2, List.map_cons]
  exact List.mem_cons_self

theorem nGrows_makeWire (s : CircuitState) (hint : String) (ty : Sparkle.IR.Type.HWType)
    (named : Bool) : NGrows s (CircuitM.makeWire hint ty named s).2 := by
  refine ⟨fun x hx => used_makeWire hint ty named s hx, fun st hst => ?_, fun x hx => ?_⟩
  · rw [(CircuitM.makeWire_spec hint ty named s).2.2.1]
    exact hst
  · rw [(CircuitM.makeWire_spec hint ty named s).2.2.2, List.map_cons]
    exact List.mem_cons_of_mem _ hx

theorem NOk.makeWire {G : Sparkle.IR.AST.Module → Prop} {I : List String} {s : CircuitState}
    (h : NOk G I s) (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    NOk G I (CircuitM.makeWire hint ty named s).2 := by
  have hspec := CircuitM.makeWire_spec hint ty named s
  have hm := makeWire_module hint ty named s
  refine h.transfer hspec.2.2.1 (by rw [hm]; try rfl) (nGrows_makeWire s hint ty named).2.2
    (fun x hx => used_makeWire hint ty named s hx) ?_ ?_
  · intro x hx
    rw [hspec.2.1] at hx
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with h1 | h1
    · rw [← h1]
      exact CircuitM.makeWire_allocated hint ty named s
    · exact h.alloc x h1
  · intro w e he
    rw [CircuitM.makeWire_translateRecord] at he
    exact he

/-- The made wire is pending, and was not reserved before. -/
theorem fresh_makeWire {G : Sparkle.IR.AST.Module → Prop} {I : List String} {s : CircuitState}
    (h : NOk G I s) (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    FreshN I (CircuitM.makeWire hint ty named s).2 (CircuitM.makeWire hint ty named s).1 ∧
      s.usedNames.contains (CircuitM.makeWire hint ty named s).1 = false := by
  have hspec := CircuitM.makeWire_spec hint ty named s
  have hnot : s.usedNames.contains (CircuitM.makeWire hint ty named s).1 = false := hspec.1
  refine ⟨⟨?_, ?_, ?_⟩, hnot⟩
  · rw [hspec.2.1]
    simp [Std.HashSet.contains_insert]
  · intro hI
    have := h.inU _ hI
    rw [hnot] at this
    cases this
  · intro st hst hx
    rw [hspec.2.2.1] at hst
    have := h.nmU st hst _ hx
    rw [hnot] at this
    cases this

theorem used_freshName (hint : String) (named : Bool) (s : CircuitState) {x : String}
    (hx : s.usedNames.contains x = true) :
    (CircuitM.freshName hint named s).2.usedNames.contains x = true := by
  rw [(CircuitM.freshName_spec hint named s).2.1]
  simp [Std.HashSet.contains_insert, hx]

theorem nGrows_freshName (s : CircuitState) (hint : String) (named : Bool) :
    NGrows s (CircuitM.freshName hint named s).2 := by
  refine ⟨fun x hx => used_freshName hint named s hx, fun st hst => ?_, fun x hx => ?_⟩
  · rw [(CircuitM.freshName_spec hint named s).2.2]
    exact hst
  · rw [(CircuitM.freshName_spec hint named s).2.2]
    exact hx

theorem NOk.freshName {G : Sparkle.IR.AST.Module → Prop} {I : List String} {s : CircuitState}
    (h : NOk G I s) (hint : String) (named : Bool) :
    NOk G I (CircuitM.freshName hint named s).2 := by
  have hspec := CircuitM.freshName_spec hint named s
  refine h.transfer (by rw [hspec.2.2]) (by rw [hspec.2.2]) (nGrows_freshName s hint named).2.2
    (fun x hx => used_freshName hint named s hx) ?_ ?_
  · intro x hx
    rw [hspec.2.1] at hx
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with h1 | h1
    · rw [← h1]
      exact CircuitM.freshName_allocated hint named s
    · exact h.alloc x h1
  · intro w e he
    rw [CircuitM.freshName_translateRecord] at he
    exact he

theorem NOk.design {G : Sparkle.IR.AST.Module → Prop} {I : List String} {s : CircuitState}
    (h : NOk G I s) (d' : Sparkle.IR.AST.Design) : NOk G I { s with design := d' } :=
  h.transfer rfl rfl (fun _ hx => hx) (fun _ hx => hx) h.alloc (fun _ _ he => he)

/-- `ShippingMergeKeeps.hm_get?_insert` at the translation record. -/
theorem rec_get?_insertN {m : Std.HashMap String Lean.Expr} {k a : String} {v : Lean.Expr} :
    (m.insert k v).get? a = if k = a then some v else m.get? a := by
  rw [Std.HashMap.get?_insert]
  by_cases h : k = a
  · have hb : (k == a) = true := by simp [h]
    rw [if_pos h, if_pos hb]
  · have hb : ¬ ((k == a) = true) := by simpa using h
    rw [if_neg h, if_neg hb]

theorem NOk.record {G : Sparkle.IR.AST.Module → Prop} {I : List String} {s : CircuitState}
    (h : NOk G I s) (w : String) (e : Lean.Expr)
    (hw : ∃ st ∈ s.module.body, w ∈ stmtNamesN st) :
    NOk G I { s with translateRecord := s.translateRecord.insert w e } := by
  refine ⟨h.ins, h.inU, h.alloc, h.kinds, h.nmU, h.iU, h.nd, h.ord, h.conn, h.wr, ?_⟩
  intro w' e' he
  have he' : (s.translateRecord.insert w e).get? w' = some e' := he
  rw [rec_get?_insertN] at he'
  by_cases hk : w = w'
  · rw [← hk]
    exact hw
  · rw [if_neg hk] at he'
    exact h.recs w' e' he'

theorem nGrows_record (s : CircuitState) (w : String) (e : Lean.Expr) :
    NGrows s { s with translateRecord := s.translateRecord.insert w e } :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem pend_record {I : List String} {s u : CircuitState} (h : PendN I s u) (w : String)
    (e : Lean.Expr) : PendN I s { u with translateRecord := u.translateRecord.insert w e } :=
  fun x hx st hst => h x hx st hst

/-- A new statement mentioning no pending name. -/
theorem pend_addStmt {I : List String} {s u : CircuitState} {st0 : Stmt}
    (hnew : ∀ x, FreshN I s x → x ∉ stmtNamesN st0) (hpu : PendN I s u) :
    PendN I s { u with module := u.module.addStmt st0 } := by
  intro x hx st hst
  have hst' : st ∈ st0 :: u.module.body := hst
  rcases List.mem_cons.mp hst' with rfl | hst'
  · exact hnew x hx
  · exact hpu x hx st hst'

theorem nGrows_addStmt (u : CircuitState) (st0 : Stmt) :
    NGrows u { u with module := u.module.addStmt st0 } :=
  ⟨fun _ h => h, fun _ h => List.mem_cons_of_mem _ h, fun _ h => h⟩

theorem emitAssign_eqN (l : String) (r : Sparkle.IR.AST.Expr) (s : CircuitState) :
    (CircuitM.emitAssign l r s).2 = { s with module := s.module.addStmt (.assign l r) } := rfl

/-- **An assignment** of a target mentioned by no statement, reserved, a
declared wire and not an input, whose names are reserved. -/
theorem NOk.emitAssign {G : Sparkle.IR.AST.Module → Prop} {I : List String} {s : CircuitState}
    (h : NOk G I s) {l : String} {r : Sparkle.IR.AST.Expr}
    (hU : ∀ x ∈ stmtNamesN (.assign l r), s.usedNames.contains x = true)
    (hfresh : ∀ S ∈ s.module.body, l ∉ stmtNamesN S)
    (hwire : l ∈ s.module.wires.map (·.name)) (hlI : l ∉ I) :
    NOk G I (CircuitM.emitAssign l r s).2 := by
  rw [emitAssign_eqN]
  have hb : ({ s with module := s.module.addStmt (.assign l r) } : CircuitState).module.body =
      Stmt.assign l r :: s.module.body := rfl
  refine ⟨h.ins, h.inU, h.alloc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro st hst
    rw [hb] at hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact Or.inl ⟨l, r, rfl⟩
    · exact h.kinds st hst
  · intro st hst x hx
    rw [hb] at hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact hU x hx
    · exact h.nmU st hst x hx
  · intro mn i cs hm
    rw [hb] at hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he
    · exact h.iU mn i cs hm
  · rw [hb]
    exact h.nd
  · rw [hb]
    refine List.pairwise_cons.mpr ⟨fun S hS x hx => ?_, h.ord⟩
    rw [writesN_assign hx]
    exact hfresh S hS
  · intro mn i cs hm
    rw [hb] at hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he
    · exact h.conn mn i cs hm
  · intro st hst x hx
    rw [hb] at hst
    rcases List.mem_cons.mp hst with rfl | hst
    · rw [writesN_assign hx]
      exact ⟨hwire, hlI⟩
    · exact h.wr st hst x hx
  · intro w e he
    obtain ⟨st, hst, hw⟩ := h.recs w e he
    rw [hb]
    exact ⟨st, List.mem_cons_of_mem _ hst, hw⟩

/-- **An instance statement** of a `G` module with keyed connections, a
fresh instance name and a fresh written wire. -/
theorem NOk.addInst {G : Sparkle.IR.AST.Module → Prop} {I : List String} {s : CircuitState}
    (h : NOk G I s) {mn i : String} {cs : List (String × Sparkle.IR.AST.Expr)}
    (x : Sparkle.IR.AST.Module) (hG : G x) (hn : x.name = mn) (hc : ConnOkN x cs)
    (hU : ∀ y ∈ stmtNamesN (.inst mn i cs), s.usedNames.contains y = true)
    (hiU : s.usedNames.contains i = true)
    (hinot : i ∉ Tools.ShippingHierState.instNames s.module.body)
    (hwr : ∀ y, WritesN (.inst mn i cs) y →
      (∀ S ∈ s.module.body, y ∉ stmtNamesN S) ∧ y ∈ s.module.wires.map (·.name) ∧ y ∉ I) :
    NOk G I { s with module := s.module.addStmt (.inst mn i cs) } := by
  have hb : ({ s with module := s.module.addStmt (.inst mn i cs) } : CircuitState).module.body =
      Stmt.inst mn i cs :: s.module.body := rfl
  refine ⟨h.ins, h.inU, h.alloc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro st hst
    rw [hb] at hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact Or.inr ⟨mn, i, cs, rfl⟩
    · exact h.kinds st hst
  · intro st hst y hy
    rw [hb] at hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact hU y hy
    · exact h.nmU st hst y hy
  · intro mn' i' cs' hm
    rw [hb] at hm
    rcases List.mem_cons.mp hm with he | hm
    · rw [(Stmt.inst.inj he).2.1]
      exact hiU
    · exact h.iU mn' i' cs' hm
  · rw [hb]
    exact List.nodup_cons.mpr ⟨hinot, h.nd⟩
  · rw [hb]
    exact List.pairwise_cons.mpr ⟨fun S hS y hy => (hwr y hy).1 S hS, h.ord⟩
  · intro mn' i' cs' hm
    rw [hb] at hm
    rcases List.mem_cons.mp hm with he | hm
    · obtain ⟨h1, -, h3⟩ := Stmt.inst.inj he
      rw [h1, h3]
      exact ⟨x, hG, hn, hc⟩
    · exact h.conn mn' i' cs' hm
  · intro st hst y hy
    rw [hb] at hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact ⟨(hwr y hy).2.1, (hwr y hy).2.2⟩
    · exact h.wr st hst y hy
  · intro w e he
    obtain ⟨st, hst, hw⟩ := h.recs w e he
    rw [hb]
    exact ⟨st, List.mem_cons_of_mem _ hst, hw⟩

/-- **A fresh assignment `l := op [a, b]`** of two returned wires: the
invariant, the growth, and no pending name other than `l` mentioned. -/
theorem emit_freshN {G : Sparkle.IR.AST.Module → Prop} {I : List String} {sc : CircuitState}
    {l a b : String} {o : Operator}
    (hc : NOk G I sc) (hl : FreshN I sc l) (hwl : l ∈ sc.module.wires.map (·.name))
    (ha : RetN I sc a) (hb : RetN I sc b) :
    NOk G I (CircuitM.emitAssign l (.op o [.ref a, .ref b]) sc).2 ∧
      NGrows sc (CircuitM.emitAssign l (.op o [.ref a, .ref b]) sc).2 ∧
      ∀ x, FreshN I sc x → x ≠ l → x ∉ stmtNamesN (.assign l (.op o [.ref a, .ref b])) := by
  refine ⟨hc.emitAssign ?_ hl.2.2 hwl hl.2.1, ?_, ?_⟩
  · intro x hx
    rcases mem_stmtNamesN_bin hx with rfl | rfl | rfl
    · exact hl.1
    · exact ha.used hc
    · exact hb.used hc
  · rw [emitAssign_eqN]
    exact nGrows_addStmt sc _
  · intro x hx hne hmem
    rcases mem_stmtNamesN_bin hmem with rfl | rfl | rfl
    · exact hne rfl
    · exact ha.ne hx rfl
    · exact hb.ne hx rfl

end names

/-! ## The walk -/

section namWalk
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec Grows
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness
open Tools.ShippingEntrySoundness
open Sparkle.IR.AST (Operator)
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingUnifiedRecursion
open Tools.ShippingHierarchySoundness
open Tools.ShippingInstanceEntrySoundness
open Tools.ShippingInstanceLeaf
open Tools.ShippingChildInv (RefLaws InvV J KeepsC Res childKeeps
  cacheLookupValidated_keepsC recordTranslation_keepsC makeWire_keepsC emitAssign_keepsC
  instArgs_keepsC instClkRst_keepsC)
open Tools.ShippingCacheCoherentRun (SubMap sub_trans sub_refl)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **The naming contract** (file header). -/
def NamW (L : RefLaws mref cref) (mF : Std.HashMap Lean.Name Res) (D : Nat) (rec : TranslateFn)
    (ctx : CompilerState) (G : Sparkle.IR.AST.Module → Prop) (I : List String) (e : Lean.Expr) :
    Prop :=
  ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String) (top named : Bool)
    (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
    InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
    RunsC (rec e hint top named) ctx s mctx mref cctx cref w0 (w, t) w1 →
    NOk G I s → NOk G I t ∧ NGrows s t ∧ PendN I s t ∧ RetN I t w

/-- `InstLeafOk` and: no output port of the callee is named like an input. -/
def InstLeafOk2 (G : Sparkle.IR.AST.Module → Prop) (n : Nat) (y : Res) : Prop :=
  InstLeafOk G n y ∧ ∀ p ∈ y.1.outputs, p.name ∉ y.1.inputs.map (·.name)

/-- **An input binder**: no state change, an input wire returned. -/
theorem namW_fvar (L : RefLaws mref cref) {mF : Std.HashMap Lean.Name Res} {D : Nat}
    {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop} {I : List String} {id : FVarId}
    {z : String} (hz : ctx.varMap.lookup id = some z) (hzI : z ∈ I) :
    ∀ fuel, NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I (.fvar id)
  | 0 => by
    intro mctx cctx hint top named s t w w0 w1 _ _ _ hr _
    exact (Returns.throw (runsCReturns hr)).elim
  | fuel + 1 => by
    intro mctx cctx hint top named s t w w0 w1 _ _ _ hr hok
    change RunsC (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel) (.fvar id) hint top named) ctx s
      mctx mref cctx cref w0 (w, t) w1 at hr
    have bound : visible ctx s.sourceBindings id = some z := by
      simp [visible, hz]
    obtain ⟨hwz, ht⟩ :=
      Tools.ShippingMixedInvariant.translateStep_fvar_returns (tenv := tenv) bound
        (runsCReturns hr)
    subst ht
    rw [hwz]
    exact ⟨hok, NGrows.refl _, PendN.refl, Or.inl hzI⟩

/-- **The core and the record of a binary node** (`binary_coreDes`'s run). -/
theorem binary_coreNam (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {I : List String} {e : Lean.Expr} {m : Lean.Name} {us : List Level} {op : Operator} {n : Nat}
    {hint : String} {top named cacheable : Bool}
    {s t : CircuitState} {w : String} {w0 w1 : Void IO.RealWorld}
    {K : Option String → CompilerM String}
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ca : NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I
      e.getAppArgs[e.getAppArgs.size - 2]!)
    (cb : NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I
      e.getAppArgs[e.getAppArgs.size - 1]!)
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => Pure.pure z))
    (hw0 : InvV L w0) (hd0 : L.dval w0 = D) (hsub : SubMap (L.val w1) mF)
    (hr : RunsC (translateCore (translateFuelFix (translateStep tenv) fuel) e hint top named >>= K)
      ctx s mctx mref cctx cref w0 (w, t) w1) (hok : NOk G I s) :
    NOk G I t ∧ NGrows s t ∧ PendN I s t ∧ RetN I t w := by
  obtain ⟨r, sm, wc, core, rest⟩ := RunsC.bind hr
  rw [core_binary_eq fn hop kinds width] at core
  obtain ⟨z, sm', wz, lower, back⟩ := RunsC.bind core
  obtain ⟨hp, hwz⟩ := RunsC.pure back
  obtain ⟨hrz, hsm⟩ := Prod.mk.inj hp
  subst hrz hsm hwz
  rw [hk] at rest
  obtain ⟨u, sr, wr, record, fin⟩ := RunsC.bind rest
  obtain ⟨hp2, hw1⟩ := RunsC.pure fin
  obtain ⟨hwz', ht'⟩ := Prod.mk.inj hp2
  subst hwz' ht' hw1
  obtain ⟨sa, sb, sc, a, b, wm, wa, wb, hwname, hsa, rmk, ra, rb, remit, ht⟩ :=
    binary_returnsW width lower
  -- the worlds: makeWire, operand a, operand b, the assign, the record
  obtain ⟨hwm, hdm, -⟩ :=
    keepsW L (fun L' => makeWire_keepsC L' D hint (.bitVector n) named) hw0 hd0 rmk
  obtain ⟨hwa, hda, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hwm hdm ra
  obtain ⟨hwb, hdb, hsbc⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa hda rb
  obtain ⟨hwc, hdc, hscd⟩ :=
    keepsW L (fun L' => emitAssign_keepsC L' D w (.op op [.ref a, .ref b])) hwb hdb remit
  obtain ⟨-, -, hsd⟩ :=
    keepsW L (fun L' => recordTranslation_keepsC L' D e w cacheable) hwc hdc record
  have subB : SubMap (L.val wb) mF := sub_trans hscd (sub_trans hsd hsub)
  have subA : SubMap (L.val wa) mF := sub_trans hsbc subB
  -- the target wire, fresh at `s`
  obtain ⟨fW, hnotW⟩ := fresh_makeWire hok hint (.bitVector n) named
  have nA0 : NOk G I sa := by
    rw [hsa]
    exact hok.makeWire hint (.bitVector n) named
  have gA0 : NGrows s sa := by
    rw [hsa]
    exact nGrows_makeWire s hint (.bitVector n) named
  have pA0 : PendN I s sa := by
    rw [hsa]
    exact PendN.of_body (fun st hst => by
      rw [(CircuitM.makeWire_spec hint (.bitVector n) named s).2.2.1] at hst
      exact hst)
  have hwF : FreshN I sa w := by
    rw [hsa, hwname]
    exact fW
  have hwS : s.usedNames.contains w = false := by
    rw [hwname]
    exact hnotW
  have hwA : w ∈ sa.module.wires.map (·.name) := by
    rw [hsa, hwname]
    exact wire_makeWire hint (.bitVector n) named s
  obtain ⟨nB, gB, pB, retA⟩ := ca mctx cctx "op_a" false false sa sb a wm wa hwm hdm subA ra nA0
  obtain ⟨nC, gC, pC, retB⟩ := cb mctx cctx "op_b" false false sb sc b wa wb hwa hda subB rb nB
  have hwC : FreshN I sc w := pC.fresh gC (pB.fresh gB hwF)
  have hwCw : w ∈ sc.module.wires.map (·.name) := gC.2.2 _ (gB.2.2 _ hwA)
  obtain ⟨nM, gM, hnew⟩ := emit_freshN (o := op) nC hwC hwCw (retA.mono gC) retB
  have gSC : NGrows s sc := (gA0.trans gB).trans gC
  have pSC : PendN I s sc := (pA0.trans gA0 pB).trans (gA0.trans gB) pC
  have pM : PendN I s sm := by
    rw [ht, emitAssign_eqN]
    refine pend_addStmt (fun x hx => hnew x (pSC.fresh gSC hx) ?_) pSC
    intro hxw
    have hx1 : s.usedNames.contains x = true := hx.1
    rw [hxw, hwS] at hx1
    exact Bool.false_ne_true hx1
  have hrecE := recordTranslation_returns (runsCReturns record)
  have hretM : ∃ st ∈ sm.module.body, w ∈ stmtNamesN st := by
    refine ⟨.assign w (.op op [.ref a, .ref b]), ?_, ?_⟩
    · rw [ht, emitAssign_eqN]
      exact List.mem_cons_self
    · rw [stmtNamesN_assign]
      exact List.mem_cons_self
  have nM' : NOk G I sm := by
    rw [ht]
    exact nM
  have gM' : NGrows sc sm := by
    rw [ht]
    exact gM
  rw [hrecE]
  exact ⟨nM'.record _ _ hretM, (gSC.trans gM').trans (nGrows_record _ _ _), pend_record pM _ _,
    Or.inr hretM⟩

/-- **A canonical binary node** (either branch of the validated lookup). -/
theorem namW_binary (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {I : List String} {e : Lean.Expr} {m : Lean.Name} {us : List Level} {op : Operator} {n : Nat}
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ca : NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I
      e.getAppArgs[e.getAppArgs.size - 2]!)
    (cb : NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I
      e.getAppArgs[e.getAppArgs.size - 1]!) :
    NamW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G I e := by
  have nf := isFVar_false_of_const fn
  intro mctx cctx hint top named s t w w0 w1 hw0 hd0 hsub hr hok
  change RunsC (translateStepWith (translateFallback tenv)
    (translateFuelFix (translateStep tenv) fuel) e hint top named) ctx s
    mctx mref cctx cref w0 (w, t) w1 at hr
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, w2, rh, hr2⟩ := RunsC.bind hr
    have rhR := runsCReturns rh
    have hs := (cacheLookupValidated_returns rhR).1
    subst hs
    obtain ⟨hw2, hd2, -⟩ :=
      keepsW L (fun L' => cacheLookupValidated_keepsC L' D e) hw0 hd0 rh
    split at hr2
    · obtain ⟨hp, -⟩ := RunsC.pure hr2
      obtain ⟨hw', ht'⟩ := Prod.mk.inj hp
      subst hw' ht'
      exact ⟨hok, NGrows.refl _, PendN.refl,
        Or.inr (hok.recs _ _ ((cacheLookupValidated_returns rhR).2 _ rfl))⟩
    · exact binary_coreNam (cacheable := !named && !e.isFVar && !top) L hD fuel
        fn hop kinds width ca cb
        (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hw2 hd2 hsub hr2 hok
  · exact binary_coreNam (cacheable := !named && !e.isFVar && !top) L hD fuel
      fn hop kinds width ca cb
      (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hw0 hd0 hsub hr hok

/-- **A canonical comparison** (both branches of the validated wrapper). -/
theorem namW_compare (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {I : List String} {dom ae be : Lean.Expr} {n : Nat} {le : SignalCompareKind}
    (ca : NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I ae)
    (cb : NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I be) :
    NamW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G I
      (compareE le dom n ae be) := by
  intro mctx cctx hint top named s t w w0 w1 hw0 hd0 hsub hr hok
  change RunsC (translateStepWith (translateFallback tenv)
    (translateFuelFix (translateStep tenv) fuel) (compareE le dom n ae be) hint top named) ctx s
    mctx mref cctx cref w0 (w, t) w1 at hr
  rw [Tools.ShippingMixedRecursion.compare_step,
    translateFallback_bool (translateFuelFix (translateStep tenv) fuel)
      (compareE le dom n ae be) hint top named (by cases le <;> rfl)] at hr
  rcases controlCached_runsW L hw0 hd0 hr with hit | ⟨sm, wa, wb, hwa, hda, hl, hrec⟩
  · have hlk := cacheLookupValidated_returns hit
    rw [hlk.1]
    exact ⟨hok, NGrows.refl _, PendN.refl, Or.inr (hok.recs _ _ (hlk.2 _ rfl))⟩
  · rw [translateBoolUncachedWith_compare] at hl
    unfold translateSignalCompare at hl
    obtain ⟨a, sa, wa1, ra, rest⟩ := RunsC.bind hl
    obtain ⟨b, sb, wb1, rb, re⟩ := RunsC.bind rest
    obtain ⟨hwa1, hda1, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa hda ra
    obtain ⟨hwb1, hdb1, hsab⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa1 hda1 rb
    have reE : RunsC (emitBoolResult (.op (signalCompareOp le) [.ref a, .ref b]) hint named)
        ctx sb mctx mref cctx cref wb1 (w, sm) wb := re
    unfold emitBoolResult at reE
    obtain ⟨r1, s1, wq, rm, rest2⟩ := RunsC.bind reE
    obtain ⟨u2, s2, wq2, rem, fin⟩ := RunsC.bind rest2
    obtain ⟨hp, hwq⟩ := RunsC.pure fin
    obtain ⟨hwr, hsm⟩ := Prod.mk.inj hp
    obtain ⟨hwm, hdm, hs1⟩ :=
      keepsW L (fun L' => makeWire_keepsC L' D hint .bit named) hwb1 hdb1 rm
    obtain ⟨hwq', hdq', hs2⟩ :=
      keepsW L (fun L' => emitAssign_keepsC L' D r1 (.op (signalCompareOp le) [.ref a, .ref b]))
        hwm hdm rem
    rw [← hwq] at hwq' hdq' hs2
    obtain ⟨-, -, hsr⟩ :=
      keepsW L (fun L' => recordTranslation_keepsC L' D (compareE le dom n ae be) w
        (!named && !(compareE le dom n ae be).isFVar && !top)) hwq' hdq' hrec
    have subB : SubMap (L.val wb1) mF := sub_trans hs1 (sub_trans hs2 (sub_trans hsr hsub))
    have subA : SubMap (L.val wa1) mF := sub_trans hsab subB
    obtain ⟨nA, gA, pA, retA⟩ := ca mctx cctx "a" false false s sa a wa wa1 hwa hda subA ra hok
    obtain ⟨nB, gB, pB, retB⟩ := cb mctx cctx "b" false false sa sb b wa1 wb1 hwa1 hda1 subB rb nA
    obtain ⟨hr1, hs1e⟩ := Tools.ShippingTranslateSoundness.makeWire_returns (runsCReturns rm)
    have hs2e := Tools.ShippingTranslateSoundness.emitAssign_returns (runsCReturns rem)
    have hrecE := recordTranslation_returns (runsCReturns hrec)
    have gSB : NGrows s sb := gA.trans gB
    have pSB : PendN I s sb := pA.trans gA pB
    -- the result wire, fresh at `sb`
    obtain ⟨fW, hnotW⟩ := fresh_makeWire nB hint .bit named
    have n1 : NOk G I s1 := by
      rw [hs1e]
      exact nB.makeWire hint .bit named
    have g1 : NGrows sb s1 := by
      rw [hs1e]
      exact nGrows_makeWire sb hint .bit named
    have p1 : PendN I sb s1 := by
      rw [hs1e]
      exact PendN.of_body (fun st hst => by
        rw [(CircuitM.makeWire_spec hint .bit named sb).2.2.1] at hst
        exact hst)
    have hrF : FreshN I s1 r1 := by
      rw [hs1e, hr1]
      exact fW
    have hrS : sb.usedNames.contains r1 = false := by
      rw [hr1]
      exact hnotW
    have hrW : r1 ∈ s1.module.wires.map (·.name) := by
      rw [hs1e, hr1]
      exact wire_makeWire hint .bit named sb
    obtain ⟨n2, g2, hnew⟩ := emit_freshN (o := signalCompareOp le) n1 hrF hrW
      ((retA.mono gB).mono g1) (retB.mono g1)
    have gS1 : NGrows s s1 := gSB.trans g1
    have pS1 : PendN I s s1 := pSB.trans gSB p1
    have p2 : PendN I s s2 := by
      rw [hs2e, emitAssign_eqN]
      refine pend_addStmt (fun x hx => hnew x (pS1.fresh gS1 hx) ?_) pS1
      intro hxr
      have hxB : sb.usedNames.contains x = true := gSB.1 x hx.1
      rw [hxr, hrS] at hxB
      exact Bool.false_ne_true hxB
    have hret2 : ∃ st ∈ s2.module.body, w ∈ stmtNamesN st := by
      refine ⟨.assign r1 (.op (signalCompareOp le) [.ref a, .ref b]), ?_, ?_⟩
      · rw [hs2e, emitAssign_eqN]
        exact List.mem_cons_self
      · rw [stmtNamesN_assign, hwr]
        exact List.mem_cons_self
    rw [← hs2e] at n2 g2
    rw [hrecE, hsm]
    exact ⟨n2.record _ _ hret2, (gS1.trans g2).trans (nGrows_record _ _ _), pend_record p2 _ _,
      Or.inr hret2⟩

/-- **The uncached instance lowering** (`instUncached_desW`, a copy of its
proof) with the fresh case's output wire and instance name exposed. -/
theorem instUncached_namW (L : RefLaws mref cref) {D : Nat} {rec : TranslateFn}
    (hrec : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D) (rec e hint top named))
    {ctx : CompilerState} {mn : Name}
    {mc : Sparkle.IR.AST.Module} {dc : Sparkle.IR.AST.Design} {so : Sparkle.IR.AST.Port}
    {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {hint : String} {top named : Bool} {s t : CircuitState} {w : String}
    {w0 w1 : Void IO.RealWorld}
    (hdc : dc.modules = [])
    (hnoclk : ∀ p ∈ mc.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hlen : mc.inputs.length = argsE.length)
    (hw0 : InvV L w0) (hd0 : L.dval w0 = D)
    (run : RunsC (translateInstanceUncachedWith rec mn mc dc so
      (instEN mn lvls dom argsE) hint top named) ctx s mctx mref cctx cref w0 (w, t) w1) :
    ∃ (d' : Sparkle.IR.AST.Design) (conns : List (String × Sparkle.IR.AST.Expr))
      (sA : CircuitState) (wa wb : Void IO.RealWorld),
      InvV L wa ∧ L.dval wa = D ∧ InvV L w1 ∧ L.dval w1 = D ∧ SubMap (L.val wb) (L.val w1) ∧
      RunsC (instArgs rec [] (mc.inputs.zip argsE) 0) ctx { s with design := d' }
        mctx mref cctx cref wa (conns, sA) wb ∧
      (∀ x ∈ d'.modules, x ∈ s.design.modules ∨ x = mc) ∧
      (∀ x ∈ s.design.modules, x ∈ d'.modules) ∧ (∃ x ∈ d'.modules, x.name = mc.name) ∧
      ((instHitValid s.translateRecord (instEN mn lvls dom argsE) w = true ∧ t = sA) ∨
       (w = (CircuitM.makeWire hint so.ty named sA).1 ∧
        ∃ iname : String,
         iname = (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).1 ∧
         t = { (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2 with
           module := (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module.addStmt
             (.inst mc.name iname (conns.reverse ++ [(so.name, .ref w)])) })) := by
  rw [instanceUncached_run] at run
  obtain ⟨cs0, sG, wg, hget0, k1⟩ := RunsC.bind (c := (get : CompilerM CircuitState)) run
  obtain ⟨hcs0, hsG, hwg⟩ := runsC_get hget0
  rw [hcs0, hsG, hwg] at k1
  rw [hdc] at k1
  obtain ⟨u0, sA0, wA0, hAdd0, k2⟩ := RunsC.bind (c := instAddModules _ []) k1
  have hAdd0' : RunsC (Pure.pure () : CompilerM Unit) ctx s mctx mref cctx cref w0 (u0, sA0)
      wA0 := hAdd0
  obtain ⟨hp0, hwA0⟩ := RunsC.pure hAdd0'
  rw [(Prod.mk.inj hp0).2, hwA0] at k2
  obtain ⟨uR, sB, wR, hReg, k3⟩ := RunsC.bind (c := instRegisterChild _ mc) k2
  obtain ⟨hwR, hdR, -⟩ := keepsW L (fun L' => by vc) hw0 hd0 hReg
  obtain ⟨d', hsB, hdes1, hdes2, hdes3⟩ := instRegisterChild_des (runsCReturns hReg)
  obtain ⟨conns0, sC, wC, hClk, k4⟩ := RunsC.bind (c := instClkRst [] mc.inputs) k3
  obtain ⟨hwC, hdC, -⟩ :=
    keepsW L (fun L' => instClkRst_keepsC L' D mc.inputs []) hwR hdR hClk
  obtain ⟨hconns0, hsC⟩ := instClkRst_skip hnoclk (runsCReturns hClk)
  have hfl : mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst") = mc.inputs := by
    rw [List.filter_eq_self]
    intro p hp
    obtain ⟨h1, h2⟩ := hnoclk p hp
    simp [bne, h1, h2]
  rw [hfl, instEN_spineArgs] at k4
  obtain ⟨uG, sH, wH, hGuard, k5⟩ := RunsC.bind (c := instArityCheck mn _ _) k4
  unfold instArityCheck at hGuard
  rw [if_neg (by simp [hlen])] at hGuard
  obtain ⟨hpG, hwH⟩ := RunsC.pure hGuard
  have hsH : sH = sC := (Prod.mk.inj hpG).2
  have hdrop : (dom :: argsE).drop ((dom :: argsE).length - mc.inputs.length) = argsE := by
    simp [hlen]
  rw [hdrop, hconns0] at k5
  obtain ⟨conns, sF, wb, hArgs, k6⟩ := RunsC.bind (c := instArgs _ _ _ 0) k5
  rw [hsH, hsC, hsB, hwH] at hArgs
  obtain ⟨hwb, hdb, -⟩ :=
    keepsW L (fun L' => instArgs_keepsC L' D rec (hrec L') _ _ _) hwC hdC hArgs
  obtain ⟨hw1, hd1, hsub6⟩ := keepsW L (fun L' => by vc) hwb hdb k6
  refine ⟨d', conns, sF, wC, wb, hwC, hdC, hw1, hd1, hsub6, hArgs, hdes1, hdes2, hdes3, ?_⟩
  have k6R := runsCReturns k6
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6R
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  have hsQ := Returns.liftMetaM hCacheRead
  cases hhit : (cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
      (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}").filter
      (instHitValid s.translateRecord (instEN mn lvls dom argsE)) with
  | some cw =>
    rw [hhit] at k8
    obtain ⟨hw, ht⟩ := Returns.pure k8
    left
    refine ⟨?_, by rw [ht, hsQ, hsP2]⟩
    rw [hw]
    cases hget : cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
        (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}" with
    | none => rw [hget] at hhit; cases hhit
    | some c0 =>
      rw [hget] at hhit
      by_cases hv : instHitValid s.translateRecord (instEN mn lvls dom argsE) c0 = true
      · have : (some c0 : Option String) = some cw := by
          simpa [Option.filter, hv] using hhit
        cases this
        exact hv
      · simp [Option.filter, hv] at hhit
  | none =>
    rw [hhit] at k8
    simp only [] at k8
    obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire hint _ named) k8
    obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
    obtain ⟨uP, sV, hPut, k10⟩ :=
      Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
    have hsV := Returns.liftMetaM hPut
    obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
    obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
    obtain ⟨uL, sL, hLink, k11⟩ := Returns.bind (m := instLinkCheck _ _ _) k11
    obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
    rw [hsL] at k11
    obtain ⟨uE, sI, hEmit, k12⟩ :=
      Returns.bind (m := CompilerM.emitInstance mc.name _ _) k11
    have hsI := emitInstanceC_returns hEmit
    obtain ⟨hwEq, ht⟩ := Returns.pure k12
    right
    refine ⟨?_, instName, ?_, ?_⟩
    · (rw [hwEq, houtW, hsQ, hsP2]) <;> simp
    · (rw [hinstName, hsV, hsW, hsQ, hsP2]) <;> simp
    · rw [ht, hsI, hsN, hsV, hsW, hsQ, hsP2, hwEq]
      simp

/-- **The operand walk, with names**: the connections are keyed by the
callee's ports in order and carry returned wires. -/
theorem instArgs_namW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {I : List String} :
    ∀ (pairs : List (Sparkle.IR.AST.Port × Lean.Expr))
      (acc : List (String × Sparkle.IR.AST.Expr)) (i : Nat)
      (r : List (String × Sparkle.IR.AST.Expr)) (s t : CircuitState)
      (w0 w1 : Void IO.RealWorld),
    (∀ k (hk : k < pairs.length),
      NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I (pairs[k]'hk).2) →
    InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
    RunsC (instArgs (translateFuelFix (translateStep tenv) fuel) acc pairs i) ctx s
      mctx mref cctx cref w0 (r, t) w1 →
    SubMap (L.val w0) (L.val w1) ∧
      (NOk G I s → (∀ c ∈ acc, ∃ a, c.2 = Sparkle.IR.AST.Expr.ref a ∧ RetN I s a) →
        NOk G I t ∧ NGrows s t ∧ PendN I s t ∧
        r.map Prod.fst = (pairs.map (fun q => q.1.name)).reverse ++ acc.map Prod.fst ∧
        ∀ c ∈ r, ∃ a, c.2 = Sparkle.IR.AST.Expr.ref a ∧ RetN I t a)
  | [], acc, i, r, s, t, w0, w1, _, _, _, _, hr => by
    unfold instArgs at hr
    obtain ⟨hp, hw⟩ := RunsC.pure hr
    obtain ⟨hr', hs⟩ := Prod.mk.inj hp
    refine ⟨by rw [hw]; exact sub_refl _, fun hok hacc => ?_⟩
    rw [hs, hr']
    exact ⟨hok, NGrows.refl _, PendN.refl, by simp, hacc⟩
  | (p, e) :: rest, acc, i, r, s, t, w0, w1, hc, hw, hd, hsub, hr => by
    unfold instArgs at hr
    obtain ⟨aw, s1, wa, hread, hrest⟩ := RunsC.bind hr
    obtain ⟨hwa, hda, hsa⟩ := fuel_runsW (tenv := tenv) L hD fuel hw hd hread
    have hcRest : ∀ k (hk : k < rest.length),
        NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I (rest[k]'hk).2 := by
      intro k hk
      have := hc (k + 1) (by simpa using hk)
      simpa using this
    obtain ⟨subT, hT⟩ := instArgs_namW L hD fuel rest _ (i + 1) r s1 t wa w1 hcRest hwa hda hsub
      hrest
    have c0 := hc 0 (by simp)
    refine ⟨sub_trans hsa subT, fun hok hacc => ?_⟩
    obtain ⟨n1, g1, p1, ret1⟩ := c0 mctx cctx _ false false s s1 aw w0 wa hw hd
      (sub_trans subT hsub) hread hok
    have hacc1 : ∀ c ∈ (p.name, Sparkle.IR.AST.Expr.ref aw) :: acc,
        ∃ a, c.2 = Sparkle.IR.AST.Expr.ref a ∧ RetN I s1 a := by
      intro c hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨aw, rfl, ret1⟩
      · obtain ⟨a, ha, hra⟩ := hacc c hc'
        exact ⟨a, ha, hra.mono g1⟩
    obtain ⟨nT, gT, pT, hmap, hrefs⟩ := hT n1 hacc1
    refine ⟨nT, g1.trans gT, p1.trans g1 pT, ?_, hrefs⟩
    rw [hmap]
    simp

/-- **An instance call** of a designated callee whose `mF` entry satisfies
`InstLeafOk2 G`, with `NamW` arguments. -/
theorem namW_inst (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {I : List String} {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr}
    {argsE : List Lean.Expr}
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom argsE) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    (hleaf : ∀ y : Res, mF.get? mn = some y → InstLeafOk2 G argsE.length y)
    (hargs : ∀ k (hk : k < argsE.length),
      NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I (argsE[k]'hk)) :
    NamW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G I
      (instEN mn lvls dom argsE) := by
  intro mctx cctx hint top named s t w w0 w1 hw hd hsub hr hok
  obtain ⟨y, wm, -, hget, hwm, hdm, hrA⟩ :=
    inst_leaf_runsW (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
  obtain ⟨⟨hG, hdc, hnoclk, hlen, o, k, houts, hk⟩, hoin⟩ := hleaf y (hsub mn y hget)
  have hrecK : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D)
        (translateFuelFix (translateStep tenv) fuel e hint top named) :=
    fun L' => fuelRec_keepsC (tenv := tenv) L' D (childKeeps L' D (fun h => absurd h hD)) fuel
  have hr' : RunsC (translateControlCachedWith
      (translateInstanceUncachedWith (translateFuelFix (translateStep tenv) fuel) mn y.1 y.2
        ⟨o, .bitVector k⟩) (instEN mn lvls dom argsE) hint top named) ctx s
      mctx mref cctx cref wm (w, t) w1 := by
    unfold Tools.ShippingChildInv.armCont at hrA
    rw [houts] at hrA
    exact hrA
  rcases controlCached_runsW L hwm hdm hr' with hit | ⟨sm, wa, wb, hwa, hda, lowerRun, recordRun⟩
  · have hlk := cacheLookupValidated_returns hit
    rw [hlk.1]
    exact ⟨hok, NGrows.refl _, PendN.refl, Or.inr (hok.recs _ _ (hlk.2 _ rfl))⟩
  · obtain ⟨d', conns, sA, wc, wd, hwc, hdc', hwb, hdb, subD, hArgs, hdes1, hdes2, hdes3,
      hcase⟩ := instUncached_namW L hrecK hdc hnoclk hlen hwa hda lowerRun
    obtain ⟨-, -, subR⟩ := keepsW L (fun L' => recordTranslation_keepsC L' D
      (instEN mn lvls dom argsE) w (!named && !(instEN mn lvls dom argsE).isFVar && !top))
      hwb hdb recordRun
    have hpairs : ∀ j (hj : j < (y.1.inputs.zip argsE).length),
        NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I
          ((y.1.inputs.zip argsE)[j]'hj).2 := by
      intro j hj
      have hjA : j < argsE.length := by
        simp only [List.length_zip] at hj
        omega
      have : ((y.1.inputs.zip argsE)[j]'hj).2 = argsE[j]'hjA := by simp
      rw [this]
      exact hargs j hjA
    have nS : NOk G I { s with design := d' } := hok.design d'
    obtain ⟨-, hAr⟩ := instArgs_namW L hD fuel (y.1.inputs.zip argsE) [] 0 conns
      { s with design := d' } sA wc wd hpairs hwc hdc' (sub_trans subD (sub_trans subR hsub))
      hArgs
    obtain ⟨nA, gA, pA, hmapA, hrefsA⟩ := hAr nS (fun c hc => by simp at hc)
    have gSA : NGrows s sA := gA
    have pSA : PendN I s sA := fun x hx => pA x hx
    have hrecE := recordTranslation_returns (runsCReturns recordRun)
    rw [hrecE]
    rcases hcase with ⟨hvalid, hsm⟩ | ⟨hwm', iname, hiname, hsm⟩
    · -- a hit of the instance dedupe cache: a wire some statement mentions
      have hretA : ∃ st ∈ sA.module.body, w ∈ stmtNamesN st := by
        obtain ⟨st, hst, hw'⟩ := hok.recs _ _ (instHitValid_recordD hvalid)
        exact ⟨st, gSA.2.1 st hst, hw'⟩
      rw [hsm]
      exact ⟨nA.record _ _ hretA, gSA.trans (nGrows_record _ _ _), pend_record pSA _ _,
        Or.inr hretA⟩
    · -- a fresh wire, a fresh instance name, one instance statement
      have hspecW := CircuitM.makeWire_spec hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty
        named sA
      have hwNot : sA.usedNames.contains w = false := by
        rw [hwm']
        exact hspecW.1
      have hwUsedW : (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
          sA).2.usedNames.contains w = true := by
        rw [hspecW.2.1, hwm']
        simp [Std.HashSet.contains_insert]
      have hwWire : w ∈ (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
          sA).2.module.wires.map (·.name) := by
        rw [hwm']
        exact wire_makeWire hint _ named sA
      have hwI : w ∉ I := fun hI => by
        have := nA.inU w hI
        rw [hwNot] at this
        cases this
      have hwB : ∀ st ∈ sA.module.body, w ∉ stmtNamesN st := fun st hst hx => by
        have := nA.nmU st hst w hx
        rw [hwNot] at this
        cases this
      have nW := nA.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
      have gW := nGrows_makeWire sA hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
      have nN := nW.freshName s!"inst_{y.1.name}" false
      have gN := nGrows_freshName
        (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2
        s!"inst_{y.1.name}" false
      have hspecN := CircuitM.freshName_spec s!"inst_{y.1.name}" false
        (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2
      -- the instance name
      have hiNot : iname ∉ Tools.ShippingHierState.instNames
          (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.body := by
        rw [hspecN.2.2, hiname]
        intro hm
        obtain ⟨mn', cs', hm'⟩ := mem_instNamesN hm
        have := nW.iU _ _ _ hm'
        rw [hspecN.1] at this
        cases this
      have hiU : (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
            sA).2).2.usedNames.contains iname = true := by
        rw [hspecN.2.1, hiname]
        simp [Std.HashSet.contains_insert]
      -- the connections, keyed by the callee's inputs
      have hz : (y.1.inputs.zip argsE).map (fun q => q.1.name) = y.1.inputs.map (·.name) := by
        have h1 : (y.1.inputs.zip argsE).map (fun q => q.1.name) =
            ((y.1.inputs.zip argsE).map Prod.fst).map (·.name) := by
          rw [List.map_map]
          try rfl
        have hle : y.1.inputs.length ≤ argsE.length := by omega
        rw [h1, List.map_fst_zip (l₁ := y.1.inputs) (l₂ := argsE) hle]
      have hmapIns : conns.reverse.map Prod.fst = y.1.inputs.map (·.name) := by
        rw [List.map_reverse, hmapA, List.map_nil, List.append_nil, List.reverse_reverse, hz]
      have hrefsW : ∀ c ∈ conns.reverse, ∃ a, c.2 = Sparkle.IR.AST.Expr.ref a ∧ a ≠ w := by
        intro c hc
        obtain ⟨a, ha, hra⟩ := hrefsA c (List.mem_reverse.mp hc)
        refine ⟨a, ha, fun he => ?_⟩
        have := hra.used nA
        rw [he, hwNot] at this
        cases this
      have hoin' : o ∉ y.1.inputs.map (·.name) :=
        hoin ⟨o, .bitVector k⟩ (by rw [houts]; exact List.mem_singleton_self _)
      have hconn : ConnOkN y.1 (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)]) :=
        ⟨conns.reverse, o, k, w, houts, rfl, hmapIns, hrefsW, hoin'⟩
      -- the names of the instance statement
      have hnames : ∀ x ∈ stmtNamesN (.inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)])),
          x = w ∨ RetN I sA x := by
        intro x hx
        rw [stmtNamesN_inst] at hx
        obtain ⟨c, hc, hcx⟩ := List.mem_filterMap.mp hx
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨a, ha, hra⟩ := hrefsA c (List.mem_reverse.mp hc)
          rw [connRefN_of ha] at hcx
          rw [← Option.some.inj hcx]
          exact Or.inr hra
        · rw [List.mem_singleton.mp hc] at hcx
          have h0 : connRefN ((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name,
              Sparkle.IR.AST.Expr.ref w) = some w := rfl
          rw [h0] at hcx
          exact Or.inl (Option.some.inj hcx).symm
      have hU : ∀ x ∈ stmtNamesN (.inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)])),
          (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.usedNames.contains x = true := by
        intro x hx
        rcases hnames x hx with rfl | hra
        · exact gN.1 _ hwUsedW
        · exact gN.1 _ (gW.1 _ (hra.used nA))
      have hwr : ∀ x, WritesN (.inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)])) x →
          (∀ S ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.body, x ∉ stmtNamesN S) ∧
          x ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.wires.map (·.name) ∧ x ∉ I := by
        intro x hx
        rw [writesN_inst hx]
        refine ⟨?_, ?_, hwI⟩
        · rw [hspecN.2.2, hspecW.2.2.1]
          exact hwB
        · rw [hspecN.2.2]
          exact hwWire
      have nI := nN.addInst y.1 hG rfl hconn hU hiU hiNot hwr
      have gI := nGrows_addStmt (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2
        (.inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)]))
      have gSN : NGrows s (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2 :=
        (gSA.trans gW).trans gN
      have pSN : PendN I s (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2 :=
        pSA.trans gSA (PendN.of_body (fun st hst => by
          rw [hspecN.2.2, hspecW.2.2.1] at hst
          exact hst))
      have pI := pend_addStmt (st0 := .inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)]))
        (fun x hx hxn => by
          have hxA : FreshN I sA x := pSA.fresh gSA hx
          rcases hnames x hxn with rfl | hra
          · have := hxA.1
            rw [hwNot] at this
            cases this
          · exact hra.ne hxA rfl) pSN
      have hretI : ∃ st ∈ ({ (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2 with
          module := (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.addStmt
            (.inst y.1.name iname (conns.reverse ++
              [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name,
                Sparkle.IR.AST.Expr.ref w)])) } : CircuitState).module.body,
          w ∈ stmtNamesN st :=
        ⟨_, List.mem_cons_self,
          mem_stmtNamesN_inst (List.mem_append_right _ (List.mem_singleton_self _))⟩
      rw [hsm]
      exact ⟨nI.record _ _ hretI, (gSN.trans gI).trans (nGrows_record _ _ _),
        pend_record pI _ _, Or.inr hretI⟩

end namWalk

end Tools.ShippingGateParentRun

#print axioms Tools.ShippingGateParentRun.namW_fvar
#print axioms Tools.ShippingGateParentRun.namW_binary
#print axioms Tools.ShippingGateParentRun.namW_compare
#print axioms Tools.ShippingGateParentRun.namW_inst
