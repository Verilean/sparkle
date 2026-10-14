import Tools.ShippingGateConeEntryC
import Tools.ShippingGateConeNested
import Tools.ShippingFirstGateKid
import Tools.ShippingGateDesignLift

variable {tenv : Lean.Environment}

/-! # Gate-route parents, obstacle (A): the translator's design along the cone (worker N, round 11)

WRITTEN, NOT BUILT.

`Tools.ShippingGateDesignLift` states obstacle (A) `DesignHasChild ms y`
(`moduleByName ms y.1.name = some y.1`): the returned design resolves the
cached child's name to the cached child's module. Here it is PROVED for the
gate-route parents whose cone is built from input binders, canonical binary
nodes, canonical comparisons and instance calls (whose arguments are again
such cones), by a state invariant over the translator's run, world by world
(the fuel walk of `binary_contractW` / `compare_entryWN` / `inst_leaf_runsW`,
with the run's own child cache):

* `DOk G N s` — the invariant of a circuit state: every design module
  satisfies `G` (the caller's predicate: "is `mF`'s entry of the callee");
  every instance statement of the body names a design module; the module's
  name is `N`; ports and wires are scalar of positive width; outputs are
  empty; the body's statements are assignments of `op [ref, ref]` or `ref`
  and instances with reference connections (`DesStmt`); a recorded
  translation implies an instance statement in the body (`recs`: a cache
  hit can only return a wire recorded for an expression whose translation
  already emitted an instance — every recorded node of these cones contains
  an instance leaf).
* `DesW L mF D rec ctx G N e hi` — every returning run of `rec e …` from an
  invariant world of depth `D`, ending in a world whose child cache is in
  `mF`, keeps `DOk`, grows the design and the body (`DGrows`), and, when
  `hi`, ends with an instance statement in the body.
* the nodes: `desW_fvar` (an input binder: no state change), `desW_binary`
  (a canonical binary node, either branch of the validated lookup),
  `desW_compare` (a canonical comparison), `desW_inst` (an instance call of
  a designated callee whose `mF` entry satisfies `InstLeafOk G`: the child is
  registered — `instRegisterChild_des` — or a module of its name is already
  in the design, which by `DOk` IS a `G` module; arguments by `instArgs_desW`).
* `desFinal_of_run` — on the harness run (`mixedHarness_runs`): the prepared
  state has `DOk` (`prepare_dok`), so the core module and design returned by
  the mixed entry satisfy `FinalOk`.
* `designHasChild_of_final` — (A) from `FinalOk` when `G` pins the child and
  the child's name is not the parent's (`full_split`: the returned design is
  then the core design).
* `first_child_name` — a first-gate child's module is named after its
  declaration (`ChildFull.name`).

The (B) facts (body shape, port widths, an instance in the body) are part of
`FinalOk.mod` (`ModOk`); `Tools/ShippingGateDesignPost.lean` turns them into
`PostKeeps`. -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

/-! ## The state invariant -/

section desState
open Sparkle.IR.AST Sparkle.IR.Builder

/-- A scalar type of positive width. -/
def PosTy (ty : Sparkle.IR.Type.HWType) : Prop :=
  ty = .bit ∨ ∃ n, 0 < n ∧ ty = .bitVector n

theorem PosTy.bitWidth_pos {ty : Sparkle.IR.Type.HWType} (h : PosTy ty) : 0 < ty.bitWidth := by
  rcases h with rfl | ⟨n, hn, rfl⟩
  · show 0 < 1
    decide
  · exact hn

/-- A statement the cone's walk emits. -/
def DesStmt (st : Stmt) : Prop :=
  (∃ (l : String) (o : Operator) (a b : String),
      st = Stmt.assign l (Sparkle.IR.AST.Expr.op o [.ref a, .ref b])) ∨
  (∃ (l x : String), st = Stmt.assign l (Sparkle.IR.AST.Expr.ref x)) ∨
  (∃ (mn i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
      st = Stmt.inst mn i cs ∧ ∀ c ∈ cs, ∃ x, c.2 = Sparkle.IR.AST.Expr.ref x)

/-- The body holds an instance statement. -/
def HasInst (body : List Stmt) : Prop :=
  ∃ (mn i : String) (cs : List (String × Sparkle.IR.AST.Expr)), Stmt.inst mn i cs ∈ body

/-- **The invariant of the cone's walk** (file header). -/
structure DOk (G : Sparkle.IR.AST.Module → Prop) (N : String) (s : CircuitState) : Prop where
  mods : ∀ x ∈ s.design.modules, G x
  insts : ∀ (mn i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
    Stmt.inst mn i cs ∈ s.module.body → ∃ x ∈ s.design.modules, x.name = mn
  name : s.module.name = N
  ins : ∀ p ∈ s.module.inputs, PosTy p.ty
  outs : s.module.outputs = []
  body : ∀ st ∈ s.module.body, DesStmt st
  wires : ∀ p ∈ s.module.wires, PosTy p.ty
  recs : ∀ (w : String) (e : Lean.Expr), s.translateRecord.get? w = some e →
    HasInst s.module.body

/-- The design's modules and the body's statements are kept. -/
def DGrows (s t : CircuitState) : Prop :=
  (∀ x ∈ s.design.modules, x ∈ t.design.modules) ∧
    (∀ st ∈ s.module.body, st ∈ t.module.body)

theorem DGrows.refl (s : CircuitState) : DGrows s s := ⟨fun _ h => h, fun _ h => h⟩

theorem DGrows.trans {s t u : CircuitState} (h1 : DGrows s t) (h2 : DGrows t u) : DGrows s u :=
  ⟨fun x hx => h2.1 x (h1.1 x hx), fun st hs => h2.2 st (h1.2 st hs)⟩

theorem DGrows.hasInst {s t : CircuitState} (h : DGrows s t) (hs : HasInst s.module.body) :
    HasInst t.module.body := by
  obtain ⟨mn, i, cs, hm⟩ := hs
  exact ⟨mn, i, cs, h.2 _ hm⟩

/-! ### The builder steps -/

theorem makeWire_module (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool)
    (s : CircuitState) :
    (CircuitM.makeWire hint ty named s).2.module =
      s.module.addWire { name := (CircuitM.makeWire hint ty named s).1, ty := ty } := by
  have h : (CircuitM.makeWire hint ty named s).2.module =
      (CircuitM.freshName (CircuitM.sanitizeName hint) named s).2.module.addWire
        { name := (CircuitM.freshName (CircuitM.sanitizeName hint) named s).1, ty := ty } := rfl
  have h1 : (CircuitM.makeWire hint ty named s).1 =
      (CircuitM.freshName (CircuitM.sanitizeName hint) named s).1 := rfl
  rw [h, h1, (CircuitM.freshName_spec (CircuitM.sanitizeName hint) named s).2.2]

theorem DOk.makeWire {G : Sparkle.IR.AST.Module → Prop} {N : String} {s : CircuitState}
    (h : DOk G N s) (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool)
    (hty : PosTy ty) : DOk G N (CircuitM.makeWire hint ty named s).2 := by
  have hm := makeWire_module hint ty named s
  have hd := Tools.ShippingInstanceEntrySoundness.makeWire_design hint ty named s
  have hr := CircuitM.makeWire_translateRecord hint ty named s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd]; exact h.mods
  · rw [hm, hd]; exact h.insts
  · rw [hm]; exact h.name
  · rw [hm]; exact h.ins
  · rw [hm]; exact h.outs
  · rw [hm]; exact h.body
  · rw [hm]
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hty
    · exact h.wires p hp
  · rw [hr, hm]; exact h.recs

theorem dGrows_makeWire (s : CircuitState) (hint : String) (ty : Sparkle.IR.Type.HWType)
    (named : Bool) : DGrows s (CircuitM.makeWire hint ty named s).2 := by
  refine ⟨fun x hx => ?_, fun st hs => ?_⟩
  · rw [Tools.ShippingInstanceEntrySoundness.makeWire_design]; exact hx
  · rw [(CircuitM.makeWire_spec hint ty named s).2.2.1]; exact hs

theorem DOk.freshName {G : Sparkle.IR.AST.Module → Prop} {N : String} {s : CircuitState}
    (h : DOk G N s) (hint : String) (named : Bool) :
    DOk G N (CircuitM.freshName hint named s).2 := by
  have hm := (CircuitM.freshName_spec hint named s).2.2
  have hd := Tools.ShippingInstanceEntrySoundness.freshName_design hint named s
  have hr := CircuitM.freshName_translateRecord hint named s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd]; exact h.mods
  · rw [hm, hd]; exact h.insts
  · rw [hm]; exact h.name
  · rw [hm]; exact h.ins
  · rw [hm]; exact h.outs
  · rw [hm]; exact h.body
  · rw [hm]; exact h.wires
  · rw [hr, hm]; exact h.recs

theorem dGrows_freshName (s : CircuitState) (hint : String) (named : Bool) :
    DGrows s (CircuitM.freshName hint named s).2 := by
  refine ⟨fun x hx => ?_, fun st hs => ?_⟩
  · rw [Tools.ShippingInstanceEntrySoundness.freshName_design]; exact hx
  · rw [(CircuitM.freshName_spec hint named s).2.2]; exact hs

theorem DOk.emitAssign {G : Sparkle.IR.AST.Module → Prop} {N : String} {s : CircuitState}
    (h : DOk G N s) {l : String} {r : Sparkle.IR.AST.Expr} (hst : DesStmt (.assign l r)) :
    DOk G N (CircuitM.emitAssign l r s).2 := by
  have hb : (CircuitM.emitAssign l r s).2.module.body = .assign l r :: s.module.body := rfl
  refine ⟨h.mods, ?_, h.name, h.ins, h.outs, ?_, h.wires, ?_⟩
  · intro mn i cs hm
    rw [hb] at hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he
    · exact h.insts mn i cs hm
  · intro st hs
    rw [hb] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hst
    · exact h.body st hs
  · intro w e he
    obtain ⟨mn, i, cs, hm⟩ := h.recs w e he
    rw [hb]
    exact ⟨mn, i, cs, List.mem_cons_of_mem _ hm⟩

theorem dGrows_emitAssign (s : CircuitState) (l : String) (r : Sparkle.IR.AST.Expr) :
    DGrows s (CircuitM.emitAssign l r s).2 := by
  have hb : (CircuitM.emitAssign l r s).2.module.body = .assign l r :: s.module.body := rfl
  refine ⟨fun _ hx => hx, fun st hs => ?_⟩
  rw [hb]
  exact List.mem_cons_of_mem _ hs

theorem DOk.record {G : Sparkle.IR.AST.Module → Prop} {N : String} {s : CircuitState}
    (h : DOk G N s) (w : String) (e : Lean.Expr) (has : HasInst s.module.body) :
    DOk G N { s with translateRecord := s.translateRecord.insert w e } :=
  ⟨h.mods, h.insts, h.name, h.ins, h.outs, h.body, h.wires, fun _ _ _ => has⟩

theorem dGrows_record (s : CircuitState) (w : String) (e : Lean.Expr) :
    DGrows s { s with translateRecord := s.translateRecord.insert w e } :=
  ⟨fun _ hx => hx, fun _ hs => hs⟩

theorem DOk.design {G : Sparkle.IR.AST.Module → Prop} {N : String} {s : CircuitState}
    (h : DOk G N s) (d' : Design) (hmods : ∀ x ∈ d'.modules, G x)
    (hgrow : ∀ x ∈ s.design.modules, x ∈ d'.modules) :
    DOk G N { s with design := d' } := by
  refine ⟨hmods, ?_, h.name, h.ins, h.outs, h.body, h.wires, h.recs⟩
  intro mn i cs hm
  obtain ⟨x, hx, hn⟩ := h.insts mn i cs hm
  exact ⟨x, hgrow x hx, hn⟩

theorem DOk.addInst {G : Sparkle.IR.AST.Module → Prop} {N : String} {s : CircuitState}
    (h : DOk G N s) {mn i : String} {cs : List (String × Sparkle.IR.AST.Expr)}
    (hcs : ∀ c ∈ cs, ∃ x, c.2 = Sparkle.IR.AST.Expr.ref x)
    (hx : ∃ x ∈ s.design.modules, x.name = mn) :
    DOk G N { s with module := s.module.addStmt (.inst mn i cs) } := by
  have hb : ({ s with module := s.module.addStmt (.inst mn i cs) } : CircuitState).module.body =
      .inst mn i cs :: s.module.body := rfl
  refine ⟨h.mods, ?_, h.name, h.ins, h.outs, ?_, h.wires, ?_⟩
  · intro mn' i' cs' hm
    rw [hb] at hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      exact hx
    · exact h.insts mn' i' cs' hm
  · intro st hst
    rw [hb] at hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact Or.inr (Or.inr ⟨mn, i, cs, rfl, hcs⟩)
    · exact h.body st hst
  · intro _ _ _
    rw [hb]
    exact ⟨mn, i, cs, List.mem_cons_self⟩

theorem dGrows_addInst (s : CircuitState) (mn i : String)
    (cs : List (String × Sparkle.IR.AST.Expr)) :
    DGrows s { s with module := s.module.addStmt (.inst mn i cs) } := by
  have hb : ({ s with module := s.module.addStmt (.inst mn i cs) } : CircuitState).module.body =
      .inst mn i cs :: s.module.body := rfl
  refine ⟨fun _ hx => hx, fun st hs => ?_⟩
  rw [hb]
  exact List.mem_cons_of_mem _ hs

theorem DOk.addInput {G : Sparkle.IR.AST.Module → Prop} {N : String} {s : CircuitState}
    (h : DOk G N s) (n : String) (ty : Sparkle.IR.Type.HWType) (hty : PosTy ty) :
    DOk G N (CircuitM.addInput n ty s).2 := by
  rw [Tools.ShippingEntrySoundness.addInput_state]
  refine ⟨h.mods, h.insts, h.name, ?_, h.outs, h.body, h.wires, h.recs⟩
  intro p hp
  have hp' : p ∈ ({ name := n, ty := ty } : Port) :: s.module.inputs := hp
  rcases List.mem_cons.mp hp' with rfl | hp'
  · exact hty
  · exact h.ins p hp'

theorem DOk.input {G : Sparkle.IR.AST.Module → Prop} {N : String} {s : CircuitState}
    (h : DOk G N s) (name : String) (ty : Sparkle.IR.Type.HWType) (hty : PosTy ty) :
    DOk G N (Tools.ShippingMixedInputSoundness.inputState s name ty) := by
  show DOk G N (CircuitM.addInput (Tools.ShippingMixedInputSoundness.inputWire s name ty) ty
    (CircuitM.makeWire name ty true s).2).2
  exact (h.makeWire name ty true hty).addInput _ ty hty

/-- The empty start state. -/
theorem dOk_init (G : Sparkle.IR.AST.Module → Prop) (N : String) : DOk G N (CircuitM.init N) := by
  refine ⟨?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · intro x hx
    simp [CircuitM.init, Design.empty] at hx
  · intro mn i cs hm
    simp [CircuitM.init, Module.empty] at hm
  · intro p hp
    simp [CircuitM.init, Module.empty] at hp
  · intro st hst
    simp [CircuitM.init, Module.empty] at hst
  · intro p hp
    simp [CircuitM.init, Module.empty] at hp
  · intro w e he
    simp [CircuitM.init] at he

end desState

/-! ## The prepared state -/

section prepared
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingMixedEntrySoundness (Setup prepare extend start)

/-- **Input preparation keeps the invariant** when every bit-vector binder has
a positive width. -/
theorem prepare_dok {G : Sparkle.IR.AST.Module → Prop} {N : String}
    (bools : Lean.FVarId → Bool) (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × Lean.FVarId)) (a : Setup),
    (∀ x ∈ L, ∀ n, x.1.2 = MixedGateBinder.bits n → 0 < n) → DOk G N a.state →
    DOk G N (prepare bools bits L a).state
  | [], _, _, h => h
  | ((nm, k), id) :: rest, a, hp, h => by
    apply prepare_dok bools bits rest (extend a ((nm, k), id) bools bits)
      (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    cases k with
    | domain => exact h
    | bool => exact h.input nm.toString .bit (Or.inl rfl)
    | bits n =>
      exact h.input nm.toString (.bitVector n) (Or.inr ⟨n, hp _ List.mem_cons_self n rfl, rfl⟩)

/-- Preparing binders other than `id` keeps `id`'s local binding. -/
theorem prepare_lookup_keep (bools : Lean.FVarId → Bool)
    (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × Lean.FVarId)) (a : Setup) (id : Lean.FVarId),
    (∀ x ∈ L, x.2 ≠ id) →
    (prepare bools bits L a).context.varMap.lookup id = a.context.varMap.lookup id
  | [], _, _, _ => rfl
  | ((nm, k), i) :: rest, a, id, h => by
    have hi : i ≠ id := h _ List.mem_cons_self
    show (prepare bools bits rest (extend a ((nm, k), i) bools bits)).context.varMap.lookup id = _
    rw [prepare_lookup_keep bools bits rest _ id (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    cases k with
    | domain => rfl
    | bool => exact Tools.ShippingEntrySoundness.lookup_cons_ne _ _ (Ne.symm hi)
    | bits n => exact Tools.ShippingEntrySoundness.lookup_cons_ne _ _ (Ne.symm hi)

/-- **A prepared (non-domain) binder is bound locally** in the prepared
context, when the ids are distinct. -/
theorem prepare_lookup_hit (bools : Lean.FVarId → Bool)
    (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × Lean.FVarId)) (a : Setup) (nm : Lean.Name)
      (k : MixedGateBinder) (id : Lean.FVarId),
    (L.map (·.2)).Nodup → ((nm, k), id) ∈ L → k ≠ .domain →
    ∃ z, (prepare bools bits L a).context.varMap.lookup id = some z
  | [], _, _, _, _, _, hm, _ => by simp at hm
  | ((nm', k'), i) :: rest, a, nm, k, id, hnd, hm, hk => by
    have hnd' := List.nodup_cons.mp hnd
    show ∃ z, (prepare bools bits rest (extend a ((nm', k'), i) bools bits)).context.varMap.lookup
      id = some z
    rcases List.mem_cons.mp hm with he | hm'
    · have hid : id = i := (Prod.mk.inj he).2
      have hkk : k = k' := (Prod.mk.inj (Prod.mk.inj he).1).2
      rw [hkk] at hk
      rw [hid]
      rw [prepare_lookup_keep bools bits rest _ i
        (fun x hx hxe => hnd'.1 (List.mem_map.mpr ⟨x, hx, hxe⟩))]
      cases k' with
      | domain => exact absurd rfl hk
      | bool => exact ⟨_, Tools.ShippingEntrySoundness.lookup_cons_self _ _ _⟩
      | bits n => exact ⟨_, Tools.ShippingEntrySoundness.lookup_cons_self _ _ _⟩
    · exact prepare_lookup_hit bools bits rest _ nm k id hnd'.2 hm' hk

/-- A binder of positive width (a bit-vector binder of width 0 is refused). -/
def binderPos : MixedGateBinder → Bool
  | .bits n => decide (0 < n)
  | _ => true

/-- A decidable form of "every bit-vector binder has a positive width". -/
theorem binders_pos_of_all {bs : List (Lean.Name × MixedGateBinder)}
    (h : bs.all (fun b => binderPos b.2) = true) :
    ∀ b ∈ bs, ∀ n, b.2 = MixedGateBinder.bits n → 0 < n := by
  intro b hb n hn
  have h1 : binderPos b.2 = true := List.all_eq_true.mp h b hb
  rw [hn] at h1
  have h2 : decide (0 < n) = true := h1
  exact of_decide_eq_true h2

end prepared

/-! ## The returned core module and design -/

section final
open Sparkle.IR.AST Sparkle.IR.Builder Sparkle.Compiler.Elab

/-- What (B) needs of the core module: an instance in the body, its name, the
body's shape, the ports' and wires' widths. -/
structure ModOk (N : String) (m : Sparkle.IR.AST.Module) : Prop where
  has : HasInst m.body
  name : m.name = N
  body : ∀ st ∈ m.body, DesStmt st
  ports : ∀ p ∈ m.inputs ++ m.outputs ++ m.wires, PosTy p.ty

/-- What the walk concludes of the core module and design the mixed entry
returns. -/
structure FinalOk (G : Sparkle.IR.AST.Module → Prop) (N : String) (m : Sparkle.IR.AST.Module)
    (d : Design) : Prop where
  mods : ∀ x ∈ d.modules, G x
  insts : ∀ (mn i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
    Stmt.inst mn i cs ∈ m.body → ∃ x ∈ d.modules, x.name = mn
  mod : ModOk N m

/-- A body of assignments and instances gets no clock/reset ports. -/
theorem addClockReset_des (m : Sparkle.IR.AST.Module)
    (h : ∀ st ∈ m.body, (∃ l r, st = .assign l r) ∨ (∃ mn i cs, st = .inst mn i cs)) :
    addClockResetIfSequential m = m := by
  unfold addClockResetIfSequential
  dsimp only
  split
  · rename_i hc
    obtain ⟨st, hst, hf⟩ := List.any_eq_true.mp hc
    rcases h st hst with ⟨l, r, rfl⟩ | ⟨mn, i, cs, rfl⟩ <;> simp at hf
  · rfl

/-- The output port's type is a positive scalar. -/
theorem leafOutputType_pos {G : Sparkle.IR.AST.Module → Prop} {N : String} {s : CircuitState}
    (h : DOk G N s) (wire : String) :
    PosTy (Tools.ShippingEntrySoundness.leafOutputType s wire) := by
  unfold Tools.ShippingEntrySoundness.leafOutputType
  split
  · rename_i decl hdecl
    exact h.wires decl (List.mem_of_find?_eq_some hdecl)
  · split
    · rename_i ip hip
      exact h.ins ip (List.mem_of_find?_eq_some hip)
    · exact Or.inr ⟨8, by decide, rfl⟩

/-- **The entry's tail** (output port, assign, clock/reset, `finalize`) on a
state with `DOk` and an instance in the body. -/
theorem finalOk_of {G : Sparkle.IR.AST.Module → Prop} {N : String} {sm0 st : CircuitState}
    {wire : String} {ty : Sparkle.IR.Type.HWType} {m : Sparkle.IR.AST.Module} {d : Design}
    (h : DOk G N sm0) (has : HasInst sm0.module.body)
    (hst : st = (CircuitM.emitAssign "out" (.ref wire) (CircuitM.addOutput "out" ty sm0).2).2)
    (hty : ty = Tools.ShippingEntrySoundness.leafOutputType sm0 wire)
    (hm : m = (addClockResetIfSequential st.module).finalize) (hd : d = st.design) :
    FinalOk G N m d := by
  have hmod : st.module =
      (sm0.module.addOutput { name := "out", ty := ty }).addStmt (.assign "out" (.ref wire)) := by
    subst hst; rfl
  have hdes : st.design = sm0.design := by subst hst; rfl
  have hbody : ∀ x ∈ st.module.body, x = .assign "out" (.ref wire) ∨ x ∈ sm0.module.body := by
    intro x hx
    rw [hmod] at hx
    exact List.mem_cons.mp hx
  have hcomb : addClockResetIfSequential st.module = st.module := by
    apply addClockReset_des
    intro x hx
    rcases hbody x hx with rfl | hx
    · exact Or.inl ⟨_, _, rfl⟩
    · rcases h.body x hx with ⟨l, o, a, b, rfl⟩ | ⟨l, y, rfl⟩ | ⟨mn, i, cs, rfl, -⟩
      · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inr ⟨_, _, _, rfl⟩
  have hm' : m = st.module.finalize := by rw [hm, hcomb]
  subst hm' hd
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hdes]; exact h.mods
  · intro mn i cs hmem
    have hmem' : Stmt.inst mn i cs ∈ st.module.body := List.mem_reverse.mp hmem
    rw [hdes]
    rcases hbody _ hmem' with he | hmem''
    · cases he
    · exact h.insts mn i cs hmem''
  · obtain ⟨mn, i, cs, hmem⟩ := has
    refine ⟨mn, i, cs, List.mem_reverse.mpr ?_⟩
    rw [hmod]
    exact List.mem_cons_of_mem _ hmem
  · show st.module.name = N
    rw [hmod]
    exact h.name
  · intro x hx
    rcases hbody x (List.mem_reverse.mp hx) with rfl | hx
    · exact Or.inr (Or.inl ⟨"out", wire, rfl⟩)
    · exact h.body x hx
  · intro p hp
    have hp' : p ∈ st.module.inputs ∨ p ∈ st.module.outputs ∨ p ∈ st.module.wires := by
      simp only [Module.finalize, List.mem_append, List.mem_reverse] at hp
      rcases hp with (h1 | h1) | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    rw [hmod] at hp'
    rcases hp' with h1 | h1 | h1
    · exact h.ins p h1
    · have h1' : p ∈ ({ name := "out", ty := ty } : Port) :: sm0.module.outputs := h1
      rw [h.outs] at h1'
      rw [List.mem_singleton.mp h1']
      show PosTy ty
      rw [hty]
      exact leafOutputType_pos h wire
    · exact h.wires p h1

end final

/-! ## The walk -/

/-- `ShippingInstanceLeaf.instHitValid_record`, restated here: the original is stated in a
section with `variable [HierCtx] [ChildSem]` and takes both instances although it uses neither. -/
theorem instHitValid_recordD {record : Std.HashMap String Lean.Expr} {e : Lean.Expr}
    {cw : String} (h : Sparkle.Compiler.Elab.instHitValid record e cw = true) :
    record.get? cw = some e := by
  unfold Sparkle.Compiler.Elab.instHitValid at h
  cases hg : record.get? cw with
  | none => rw [hg] at h; cases h
  | some e' =>
    rw [hg] at h
    have : e' = e := @of_decide_eq_true _ (Sparkle.Compiler.ExprDecEq.exprDecEq e' e) h
    rw [this]

section desWalk
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

/-- **The walk's contract** (file header): every returning run of `rec e …`
from an invariant world at depth `D` that ends in a world whose child cache is
in `mF` keeps `DOk`, grows the design and the body, and when `hi` ends with an
instance statement in the body. -/
def DesW (L : RefLaws mref cref) (mF : Std.HashMap Lean.Name Res) (D : Nat) (rec : TranslateFn)
    (ctx : CompilerState) (G : Sparkle.IR.AST.Module → Prop) (N : String) (e : Lean.Expr)
    (hi : Bool) : Prop :=
  ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String) (top named : Bool)
    (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
    InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
    RunsC (rec e hint top named) ctx s mctx mref cctx cref w0 (w, t) w1 →
    DOk G N s → DOk G N t ∧ DGrows s t ∧ (hi = true → HasInst t.module.body)

/-- What an instance leaf asks of its callee's `mF` entry: the design
predicate holds of the child's module, its design is empty, it has no clock /
reset input, one input per argument, one positive-width output. -/
def InstLeafOk (G : Sparkle.IR.AST.Module → Prop) (n : Nat) (y : Res) : Prop :=
  G y.1 ∧ y.2.modules = [] ∧
  (∀ p ∈ y.1.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false) ∧
  y.1.inputs.length = n ∧
  ∃ (o : String) (k : Nat), y.1.outputs = [⟨o, .bitVector k⟩] ∧ 0 < k

/-- **An input binder** bound locally in the context: no state change. -/
theorem desW_fvar (L : RefLaws mref cref) {mF : Std.HashMap Lean.Name Res} {D : Nat}
    {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop} {N : String} {id : FVarId}
    {z : String} (hz : ctx.varMap.lookup id = some z) :
    ∀ fuel, DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N (.fvar id) false
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
    obtain ⟨-, ht⟩ :=
      Tools.ShippingMixedInvariant.translateStep_fvar_returns (tenv := tenv) bound
        (runsCReturns hr)
    subst ht
    exact ⟨hok, DGrows.refl _, fun h => absurd h (by decide)⟩

/-- **The core and the record of a binary node** keep `DOk`, from its
operands' `DesW` (the worlds of `binary_coreW`). -/
theorem binary_coreDes (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {N : String} {e : Lean.Expr} {m : Lean.Name} {us : List Level} {op : Operator} {n : Nat}
    {ha hb : Bool} {hint : String} {top named cacheable : Bool}
    {s t : CircuitState} {w : String} {w0 w1 : Void IO.RealWorld}
    {K : Option String → CompilerM String}
    (hn : 0 < n)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ca : DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N
      e.getAppArgs[e.getAppArgs.size - 2]! ha)
    (cb : DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N
      e.getAppArgs[e.getAppArgs.size - 1]! hb)
    (hab : ha = true ∨ hb = true)
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => Pure.pure z))
    (hw0 : InvV L w0) (hd0 : L.dval w0 = D) (hsub : SubMap (L.val w1) mF)
    (hr : RunsC (translateCore (translateFuelFix (translateStep tenv) fuel) e hint top named >>= K)
      ctx s mctx mref cctx cref w0 (w, t) w1) (hok : DOk G N s) :
    DOk G N t ∧ DGrows s t ∧ HasInst t.module.body := by
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
  obtain ⟨sa, sb, sc, a, b, wm, wa, wb, -, hsa, rmk, ra, rb, remit, ht⟩ :=
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
  -- the states
  have dA0 : DOk G N sa := by
    rw [hsa]
    exact hok.makeWire hint (.bitVector n) named (Or.inr ⟨n, hn, rfl⟩)
  have gA0 : DGrows s sa := by
    rw [hsa]
    exact dGrows_makeWire s hint (.bitVector n) named
  obtain ⟨dB, gB, iB⟩ := ca mctx cctx "op_a" false false sa sb a wm wa hwm hdm subA ra dA0
  obtain ⟨dC, gC, iC⟩ := cb mctx cctx "op_b" false false sb sc b wa wb hwa hda subB rb dB
  have hasC : HasInst sc.module.body := by
    rcases hab with h | h
    · exact gC.hasInst (iB h)
    · exact iC h
  have dM : DOk G N sm := by
    rw [ht]
    exact dC.emitAssign (Or.inl ⟨w, op, a, b, rfl⟩)
  have gM : DGrows sc sm := by
    rw [ht]
    exact dGrows_emitAssign sc _ _
  have hasM : HasInst sm.module.body := gM.hasInst hasC
  have hrecE := recordTranslation_returns (runsCReturns record)
  rw [hrecE]
  exact ⟨dM.record _ _ hasM, (((gA0.trans gB).trans gC).trans gM).trans (dGrows_record _ _ _),
    hasM⟩

/-- **A canonical binary node** (either branch of the validated lookup), one
of whose operands holds an instance leaf. -/
theorem desW_binary (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {N : String} {e : Lean.Expr} {m : Lean.Name} {us : List Level} {op : Operator} {n : Nat}
    {ha hb : Bool}
    (hn : 0 < n)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ca : DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N
      e.getAppArgs[e.getAppArgs.size - 2]! ha)
    (cb : DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N
      e.getAppArgs[e.getAppArgs.size - 1]! hb)
    (hab : ha = true ∨ hb = true) :
    DesW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G N e true := by
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
      exact ⟨hok, DGrows.refl _,
        fun _ => hok.recs _ _ ((cacheLookupValidated_returns rhR).2 _ rfl)⟩
    · obtain ⟨d1, g1, i1⟩ := binary_coreDes (cacheable := !named && !e.isFVar && !top) L hD fuel
        hn fn hop kinds width ca cb hab
        (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hw2 hd2 hsub hr2 hok
      exact ⟨d1, g1, fun _ => i1⟩
  · obtain ⟨d1, g1, i1⟩ := binary_coreDes (cacheable := !named && !e.isFVar && !top) L hD fuel
      hn fn hop kinds width ca cb hab
      (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hw0 hd0 hsub hr hok
    exact ⟨d1, g1, fun _ => i1⟩

/-- **A canonical comparison** (`compare_entryWN`'s walk, both branches of
the validated wrapper), one of whose operands holds an instance leaf. -/
theorem desW_compare (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {N : String} {dom ae be : Lean.Expr} {n : Nat} {le : SignalCompareKind} {ha hb : Bool}
    (ca : DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N ae ha)
    (cb : DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N be hb)
    (hab : ha = true ∨ hb = true) :
    DesW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G N
      (compareE le dom n ae be) true := by
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
    exact ⟨hok, DGrows.refl _, fun _ => hok.recs _ _ (hlk.2 _ rfl)⟩
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
    obtain ⟨-, hsm⟩ := Prod.mk.inj hp
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
    obtain ⟨dA, gA, iA⟩ := ca mctx cctx "a" false false s sa a wa wa1 hwa hda subA ra hok
    obtain ⟨dB, gB, iB⟩ := cb mctx cctx "b" false false sa sb b wa1 wb1 hwa1 hda1 subB rb dA
    obtain ⟨-, hs1e⟩ := Tools.ShippingTranslateSoundness.makeWire_returns (runsCReturns rm)
    have hs2e := Tools.ShippingTranslateSoundness.emitAssign_returns (runsCReturns rem)
    have hrecE := recordTranslation_returns (runsCReturns hrec)
    have hasB : HasInst sb.module.body := by
      rcases hab with h | h
      · exact gB.hasInst (iA h)
      · exact iB h
    have d1 : DOk G N s1 := by
      rw [hs1e]
      exact dB.makeWire hint .bit named (Or.inl rfl)
    have g1 : DGrows sb s1 := by
      rw [hs1e]
      exact dGrows_makeWire sb hint .bit named
    have d2 : DOk G N s2 := by
      rw [hs2e]
      exact d1.emitAssign (Or.inl ⟨r1, _, a, b, rfl⟩)
    have g2 : DGrows s1 s2 := by
      rw [hs2e]
      exact dGrows_emitAssign s1 _ _
    have has2 : HasInst s2.module.body := g2.hasInst (g1.hasInst hasB)
    rw [hrecE, hsm]
    exact ⟨d2.record _ _ has2, (((gA.trans gB).trans g1).trans g2).trans (dGrows_record _ _ _),
      fun _ => has2⟩

/-- The child's registration: the design gains the child, or already holds a
module of its name. -/
theorem instRegisterChild_des {mc : Sparkle.IR.AST.Module} {ctx : CompilerState}
    {s s' : CircuitState} {u : Unit}
    (h : Returns (instRegisterChild (s.design.modules.map (fun x => x.name)) mc) ctx s u s') :
    ∃ d' : Sparkle.IR.AST.Design, s' = { s with design := d' } ∧
      (∀ x ∈ d'.modules, x ∈ s.design.modules ∨ x = mc) ∧
      (∀ x ∈ s.design.modules, x ∈ d'.modules) ∧ ∃ x ∈ d'.modules, x.name = mc.name := by
  unfold instRegisterChild at h
  obtain ⟨cs, s1, hget, k⟩ := Returns.bind (m := (get : CompilerM CircuitState)) h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  rw [hcs, hs1] at k
  split at k
  · refine ⟨s.design.addModule mc, addModuleToDesignC_returns k, ?_, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ s.design.modules ++ [mc] := hx
      rcases List.mem_append.mp hx' with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_singleton.mp h1)
    · intro x hx
      show x ∈ s.design.modules ++ [mc]
      exact List.mem_append_left _ hx
    · refine ⟨mc, ?_, rfl⟩
      show mc ∈ s.design.modules ++ [mc]
      exact List.mem_append_right _ (List.mem_singleton_self mc)
  · rename_i hc
    obtain ⟨-, hs⟩ := Returns.pure k
    refine ⟨s.design, hs, fun x hx => Or.inl hx, fun x hx => hx, ?_⟩
    have hor : ((s.design.modules.map fun x => x.name).contains mc.name = true) ∨
        ((s.design.modules.any fun x => x.name == mc.name) = true) := by
      cases h1 : (s.design.modules.map fun x => x.name).contains mc.name
      · cases h2 : s.design.modules.any (fun x => x.name == mc.name)
        · exfalso
          apply hc
          simp [h2]
          intro x hx hxn
          have h3 : (s.design.modules.any fun x => x.name == mc.name) = true :=
            List.any_eq_true.mpr ⟨x, hx, (show (x.name == mc.name) = true from beq_iff_eq.mpr hxn)⟩
          rw [h2] at h3
          cases h3
        · exact Or.inr rfl
      · exact Or.inl rfl
    rcases hor with h1 | h1
    · obtain ⟨x, hx, hxn⟩ := List.mem_map.mp (List.contains_iff_mem.mp h1)
      exact ⟨x, hx, hxn⟩
    · obtain ⟨x, hx, hxn⟩ := List.any_eq_true.mp h1
      exact ⟨x, hx, beq_iff_eq.mp hxn⟩

/-- **The uncached instance lowering, with its worlds and the design** (the
text of `instUncached_shapeW`, the registration by `instRegisterChild_des`). -/
theorem instUncached_desW (L : RefLaws mref cref) {D : Nat} {rec : TranslateFn}
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
       (∃ iname : String,
         t = { (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2 with
           module := (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module.addStmt
             (.inst mc.name iname (conns.reverse ++ [(so.name, .ref w)])) })) := by
  rw [instanceUncached_run] at run
  -- the prefix: `get`, the (empty) design modules, the child's registration,
  -- the clk/rst plumbing (none), the arity guard
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
  -- the operand walk, from an invariant world
  obtain ⟨conns, sF, wb, hArgs, k6⟩ := RunsC.bind (c := instArgs _ _ _ 0) k5
  rw [hsH, hsC, hsB, hwH] at hArgs
  obtain ⟨hwb, hdb, -⟩ :=
    keepsW L (fun L' => instArgs_keepsC L' D rec (hrec L') _ _ _) hwC hdC hArgs
  -- the suffix keeps the invariant: the walk's end cache is in the end cache
  obtain ⟨hw1, hd1, hsub6⟩ := keepsW L (fun L' => by vc) hwb hdb k6
  refine ⟨d', conns, sF, wC, wb, hwC, hdC, hw1, hd1, hsub6, hArgs, hdes1, hdes2, hdes3, ?_⟩
  -- the suffix's shape: the text of the built `instUncached_shape`
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
    refine ⟨instName, ?_⟩
    rw [ht, hsI, hsN, hsV, hsW, hsQ, hsP2, hwEq]
    simp

/-- The operand walk builds reference connections. -/
theorem instArgs_refs {rec : TranslateFn} {ctx : CompilerState} :
    ∀ (pairs : List (Sparkle.IR.AST.Port × Lean.Expr))
      (acc : List (String × Sparkle.IR.AST.Expr)) (i : Nat)
      (r : List (String × Sparkle.IR.AST.Expr)) (s t : CircuitState),
    (∀ c ∈ acc, ∃ x, c.2 = Sparkle.IR.AST.Expr.ref x) →
    Returns (instArgs rec acc pairs i) ctx s r t → ∀ c ∈ r, ∃ x, c.2 = Sparkle.IR.AST.Expr.ref x
  | [], acc, i, r, s, t, hacc, h => by
    unfold instArgs at h
    obtain ⟨hr, -⟩ := Returns.pure h
    rw [hr]
    exact hacc
  | (p, e) :: rest, acc, i, r, s, t, hacc, h => by
    unfold instArgs at h
    obtain ⟨aw, s1, -, hrest⟩ := Returns.bind h
    refine instArgs_refs rest _ (i + 1) r s1 t ?_ hrest
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨aw, rfl⟩
    · exact hacc c hc

/-- **The operand walk, world by world**: every operand's run keeps `DOk`
(its `DesW`, the end cache contained in the walk's end cache). -/
theorem instArgs_desW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {N : String} :
    ∀ (pairs : List (Sparkle.IR.AST.Port × Lean.Expr))
      (acc : List (String × Sparkle.IR.AST.Expr)) (i : Nat)
      (r : List (String × Sparkle.IR.AST.Expr)) (s t : CircuitState)
      (w0 w1 : Void IO.RealWorld),
    (∀ k (hk : k < pairs.length), ∃ hi : Bool,
      DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N (pairs[k]'hk).2 hi) →
    InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
    RunsC (instArgs (translateFuelFix (translateStep tenv) fuel) acc pairs i) ctx s
      mctx mref cctx cref w0 (r, t) w1 →
    SubMap (L.val w0) (L.val w1) ∧ (DOk G N s → DOk G N t ∧ DGrows s t)
  | [], acc, i, r, s, t, w0, w1, _, _, _, _, hr => by
    unfold instArgs at hr
    obtain ⟨hp, hw⟩ := RunsC.pure hr
    obtain ⟨-, hs⟩ := Prod.mk.inj hp
    refine ⟨by rw [hw]; exact sub_refl _, fun hok => ?_⟩
    rw [hs]
    exact ⟨hok, DGrows.refl _⟩
  | (p, e) :: rest, acc, i, r, s, t, w0, w1, hc, hw, hd, hsub, hr => by
    unfold instArgs at hr
    obtain ⟨aw, s1, wa, hread, hrest⟩ := RunsC.bind hr
    obtain ⟨hwa, hda, hsa⟩ := fuel_runsW (tenv := tenv) L hD fuel hw hd hread
    have hcRest : ∀ k (hk : k < rest.length), ∃ hi : Bool,
        DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N (rest[k]'hk).2 hi := by
      intro k hk
      have := hc (k + 1) (by simpa using hk)
      simpa using this
    obtain ⟨subT, hT⟩ := instArgs_desW L hD fuel rest _ (i + 1) r s1 t wa w1 hcRest hwa hda hsub
      hrest
    obtain ⟨hi0, c0⟩ := hc 0 (by simp)
    refine ⟨sub_trans hsa subT, fun hok => ?_⟩
    obtain ⟨d1, g1, -⟩ := c0 mctx cctx _ false false s s1 aw w0 wa hw hd (sub_trans subT hsub)
      hread hok
    obtain ⟨dT, gT⟩ := hT d1
    exact ⟨dT, g1.trans gT⟩

/-- **An instance call** of a callee designated in the translator's
environment, whose `mF` entry satisfies `InstLeafOk G`, with `DesW`
arguments. -/
theorem desW_inst (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {N : String} {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr}
    {argsE : List Lean.Expr}
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom argsE) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    (hleaf : ∀ y : Res, mF.get? mn = some y → InstLeafOk G argsE.length y)
    (hargs : ∀ k (hk : k < argsE.length), ∃ hi : Bool,
      DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N (argsE[k]'hk) hi) :
    DesW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G N
      (instEN mn lvls dom argsE) true := by
  intro mctx cctx hint top named s t w w0 w1 hw hd hsub hr hok
  obtain ⟨y, wm, -, hget, hwm, hdm, hrA⟩ :=
    inst_leaf_runsW (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
  obtain ⟨hG, hdc, hnoclk, hlen, o, k, houts, hk⟩ := hleaf y (hsub mn y hget)
  have hrecK : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D)
        (translateFuelFix (translateStep tenv) fuel e hint top named) :=
    fun L' => fuelRec_keepsC (tenv := tenv) L' D (childKeeps L' D (fun h => absurd h hD)) fuel
  -- the continuation at a one-output child is the validated wrapper
  have hr' : RunsC (translateControlCachedWith
      (translateInstanceUncachedWith (translateFuelFix (translateStep tenv) fuel) mn y.1 y.2
        ⟨o, .bitVector k⟩) (instEN mn lvls dom argsE) hint top named) ctx s
      mctx mref cctx cref wm (w, t) w1 := by
    unfold Tools.ShippingChildInv.armCont at hrA
    rw [houts] at hrA
    exact hrA
  rcases controlCached_runsW L hwm hdm hr' with hit | ⟨sm, wa, wb, hwa, hda, lowerRun, recordRun⟩
  · -- a validated hit of the expression cache: the recorded expression's
    -- translation already emitted an instance
    have hlk := cacheLookupValidated_returns hit
    rw [hlk.1]
    exact ⟨hok, DGrows.refl _, fun _ => hok.recs _ _ (hlk.2 _ rfl)⟩
  · obtain ⟨d', conns, sA, wc, wd, hwc, hdc', hwb, hdb, subD, hArgs, hdes1, hdes2, hdes3,
      hcase⟩ := instUncached_desW L hrecK hdc hnoclk hlen hwa hda lowerRun
    obtain ⟨-, -, subR⟩ := keepsW L (fun L' => recordTranslation_keepsC L' D
      (instEN mn lvls dom argsE) w (!named && !(instEN mn lvls dom argsE).isFVar && !top))
      hwb hdb recordRun
    have hpairs : ∀ j (hj : j < (y.1.inputs.zip argsE).length), ∃ hi : Bool,
        DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N
          ((y.1.inputs.zip argsE)[j]'hj).2 hi := by
      intro j hj
      have hjA : j < argsE.length := by
        simp only [List.length_zip] at hj
        omega
      have : ((y.1.inputs.zip argsE)[j]'hj).2 = argsE[j]'hjA := by simp
      rw [this]
      exact hargs j hjA
    -- the design after the registration
    have dS : DOk G N { s with design := d' } := by
      refine hok.design d' (fun x hx => ?_) hdes2
      rcases hdes1 x hx with hx' | rfl
      · exact hok.mods x hx'
      · exact hG
    have gS : DGrows s { s with design := d' } := ⟨hdes2, fun _ h => h⟩
    obtain ⟨-, hAr⟩ := instArgs_desW L hD fuel (y.1.inputs.zip argsE) [] 0 conns
      { s with design := d' } sA wc wd hpairs hwc hdc' (sub_trans subD (sub_trans subR hsub))
      hArgs
    obtain ⟨dA, gA⟩ := hAr dS
    have gSA : DGrows s sA := gS.trans gA
    have hrefs := instArgs_refs (y.1.inputs.zip argsE) [] 0 conns _ sA
      (fun c hc => by simp at hc) (runsCReturns hArgs)
    have hrecE := recordTranslation_returns (runsCReturns recordRun)
    rw [hrecE]
    rcases hcase with ⟨hvalid, hsm⟩ | ⟨iname, hsm⟩
    · -- a hit of the instance dedupe cache
      have hasS : HasInst s.module.body := hok.recs _ _ (instHitValid_recordD hvalid)
      have hasA : HasInst sA.module.body := gSA.hasInst hasS
      rw [hsm]
      exact ⟨dA.record _ _ hasA, gSA.trans (dGrows_record _ _ _), fun _ => hasA⟩
    · -- a fresh wire and one instance statement
      have dW := dA.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
        (Or.inr ⟨k, hk, rfl⟩)
      have gW := dGrows_makeWire sA hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
      have dN := dW.freshName s!"inst_{y.1.name}" false
      have gN := dGrows_freshName
        (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2
        s!"inst_{y.1.name}" false
      have hX : ∃ x ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
            sA).2).2.design.modules, x.name = y.1.name := by
        obtain ⟨x, hx, hxn⟩ := hdes3
        exact ⟨x, gN.1 x (gW.1 x (gA.1 x hx)), hxn⟩
      have hcs : ∀ c ∈ conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)],
          ∃ x, c.2 = Sparkle.IR.AST.Expr.ref x := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h1
        · exact hrefs c (List.mem_reverse.mp h1)
        · rw [List.mem_singleton.mp h1]
          exact ⟨w, rfl⟩
      have dI := dN.addInst (i := iname) hcs hX
      have gI := dGrows_addInst
        (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2
        y.1.name iname
        (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)])
      have hasI : HasInst ({ (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2 with
          module := (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.addStmt
            (.inst y.1.name iname (conns.reverse ++
              [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name,
                Sparkle.IR.AST.Expr.ref w)])) } : CircuitState).module.body :=
        ⟨_, _, _, List.mem_cons_self⟩
      rw [hsm]
      exact ⟨dI.record _ _ hasI,
        (((gSA.trans gW).trans gN).trans gI).trans (dGrows_record _ _ _), fun _ => hasI⟩

/-! ## The harness run, to the returned core module and design -/

/-- **On the mixed entry's run** (`mixedHarness_runs`'s facts): the body's
`DesW` at the prepared context, positive bit-vector binders, and the
translation's run give `FinalOk` of the returned core module and design. -/
theorem desFinal_of_run {L : RefLaws mref cref} {mF : Std.HashMap Lean.Name Res} {D : Nat}
    {rec : TranslateFn} {bs : List (Lean.Name × MixedGateBinder)} {ids : List FVarId}
    {ctx0 : CompilerState} {N : String} {G : Sparkle.IR.AST.Module → Prop} {e : Lean.Expr}
    {wT wT' : Void IO.RealWorld} {wire : String} {sm0 st : CircuitState}
    {ty : Sparkle.IR.Type.HWType} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hE : DesW L mF D rec
      (Tools.ShippingMixedEntrySoundness.prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start ctx0 N)).context G N e true)
    (hpos : ∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n)
    (hwT : InvV L wT) (hdT : L.dval wT = D) (hsubT : SubMap (L.val wT') mF)
    (htr : RunsC (rec e "out" false true)
      (Tools.ShippingMixedEntrySoundness.prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start ctx0 N)).context
      (Tools.ShippingMixedEntrySoundness.prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start ctx0 N)).state
      mctx mref cctx cref wT (wire, sm0) wT')
    (hst : st = (CircuitM.emitAssign "out" (.ref wire) (CircuitM.addOutput "out" ty sm0).2).2)
    (hty : ty = Tools.ShippingEntrySoundness.leafOutputType sm0 wire)
    (hm : m = (addClockResetIfSequential st.module).finalize) (hd : d = st.design) :
    FinalOk G N m d := by
  have h0 : DOk G N (Tools.ShippingMixedEntrySoundness.prepare (fun _ => false) (fun _ _ => 0)
      (bs.zip ids) (Tools.ShippingMixedEntrySoundness.start ctx0 N)).state :=
    prepare_dok _ _ (bs.zip ids) (Tools.ShippingMixedEntrySoundness.start ctx0 N)
      (fun x hx n hn => by
        obtain ⟨b, id⟩ := x
        exact hpos b (List.of_mem_zip hx).1 n hn)
      (dOk_init G N)
  obtain ⟨h1, -, h2⟩ := hE mctx cctx "out" false true _ sm0 wire wT wT' hwT hdT hsubT htr h0
  exact finalOk_of h1 (h2 rfl) hst hty hm hd

end desWalk

/-! ## (A) from `FinalOk` -/

section discharge
open Lean Sparkle.IR.AST Sparkle.Compiler.Elab
open Tools.ShippingChildInv (Res RealChild)
open Tools.ShippingEntrySoundness (RunsTo FExpr quoteDecl)
open Tools.ShippingInlineSoundness (EntryDefines)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- On a list whose every element is `a`, and which holds `a`, the name
lookup answers `a`. -/
theorem find_all_eq (a : Sparkle.IR.AST.Module) :
    ∀ (l : List Sparkle.IR.AST.Module), (∀ x ∈ l, x = a) → a ∈ l →
      Sparkle.IR.Machine.moduleByName l a.name = some a
  | [], _, h => by simp at h
  | x :: rest, hall, _ => by
    have hx : x = a := hall x List.mem_cons_self
    subst hx
    unfold Sparkle.IR.Machine.moduleByName
    simp [List.find?]

/-- **Obstacle (A) from the walk's conclusion**: the design predicate pins the
child (`hG`), the child's name is not the parent's (so the returned design is
the core design, `full_split`). -/
theorem designHasChild_of_final {G : Sparkle.IR.AST.Module → Prop} {N : String}
    {M : Sparkle.IR.AST.Module} {Dd design : Design} {y : Res}
    (fin : FinalOk G N M Dd) (hG : ∀ x, G x → x = y.1) (hyN : y.1.name ≠ N)
    (hmods : (∀ x ∈ Dd.modules, x.name ≠ M.name) → design.modules = Dd.modules) :
    Tools.ShippingGateDesignLift.DesignHasChild design.modules y := by
  have hall : ∀ x ∈ Dd.modules, x = y.1 := fun x hx => hG x (fin.mods x hx)
  have hd : design.modules = Dd.modules := hmods (fun x hx he => by
    rw [hall x hx, fin.mod.name] at he
    exact hyN he)
  obtain ⟨mn, i, cs, hmem⟩ := fin.mod.has
  obtain ⟨x0, hx0, -⟩ := fin.insts mn i cs hmem
  have hy : y.1 ∈ Dd.modules := by
    have e0 := hall x0 hx0
    rw [← e0]
    exact hx0
  show Sparkle.IR.Machine.moduleByName design.modules y.1.name = some y.1
  rw [hd]
  exact find_all_eq y.1 Dd.modules hall hy

/-- **A first-gate child's module is named after its declaration**
(`ChildFull.name`, from the child's own run and `EntryDefines`). -/
theorem first_child_name {c : Name} {y : Res} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (entry : EntryDefines mctx mref cctx cref c (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) (h : RealChild mref cref c y) :
    y.1.name = Sparkle.IR.ModuleName.ofDecl c := by
  obtain ⟨b, design⟩ := y
  obtain ⟨mctx', cctx', w, w', -, hr⟩ := h.inv
  have entry' : EntryDefines mctx' mref cctx' cref c (quoteDecl dn names n fe) :=
    Tools.ShippingReflectCtx.EntryDefines.ctx entry
  exact (Tools.ShippingFirstGateChild.first_child_fullFacts hr entry' hwf hn).name

end discharge

end Tools.ShippingGateParentRun

#print axioms Tools.ShippingGateParentRun.desW_fvar
#print axioms Tools.ShippingGateParentRun.desW_binary
#print axioms Tools.ShippingGateParentRun.desW_compare
#print axioms Tools.ShippingGateParentRun.desW_inst
#print axioms Tools.ShippingGateParentRun.desFinal_of_run
#print axioms Tools.ShippingGateParentRun.designHasChild_of_final
#print axioms Tools.ShippingGateParentRun.first_child_name
