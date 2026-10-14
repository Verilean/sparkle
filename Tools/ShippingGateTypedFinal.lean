import Tools.ShippingGateTypedWalk
import Tools.ShippingGateNamesFinal
import Tools.ShippingFirstGatePorts
import Tools.ShippingPortsMatchShipped
import Tools.ShippingGateOutPort

variable {tenv : Lean.Environment}

/-! # Gate-route parents: `hierTyped` and `designSideB3` from the typed walk (worker N, round 14)

WRITTEN, NOT BUILT.

From `TOk` (`Tools.ShippingGateTypedWalk`) and `NOk` at the end of the walk,
the returned core module `M = finalize (out := wire :: body)` — and every
module with its body, wires and ports, in particular the shipped `b` — passes
(`typed_checks`, `TFin`), for any design `ms` in which every `G` module `x`
is resolved to itself and has the port facts of a gate child (`GFactsT`:
`childTyped`, input ports of their types' widths in both tables, output
ports of their types' widths in the emitter's table):

* `hierTyped (childMap ms) b` — every assignment `assignTyped` (operands and
  target of the walk's widths; `out := wire` targets an output port), every
  instance `childTyped` / `connsTyped` (an input connection carries a wire of
  EXACTLY its port's width, the output wire has the output port's width), no
  output port among the extracted inputs (wires are allocated names);
* `seqCheck (wofOf b) (weS b) b.body` — `seqCheck_of_typed`: names declared
  and sanitize-stable, right-hand sides `TypedExpr` at the target's emitted
  width (`out`'s port width is the returned wire's: `leafOutputType`);
* the `seqNames` width agreement — every name read is a wire
  (`seqNames_widths`);
* `portsMatchB (childMap ms) b` — the connected wires have the child ports'
  emitted widths; then of the SHIPPED module by the existing
  `portsMatchB_shipped` (`checkedOptimize b = b` or a candidate whose
  connected wires keep `b`'s emitted widths, `connsKept`).

`gate_cone_runTyped`: the full entry with all three walks (a copy of
`gate_cone_runNames`). `gate_typedFacts`: for a parent whose instance leaves
call one gate child `c` with `GateChildPorts` facts, from the run,
`GateDefines` (NOT ALLOWED), `ChildBnd` and the per-body walks:
`hierTyped (childMap design.modules) b ∧ designSideB3 design.modules b`. -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

/-! ## The prepared state -/

section preparedT
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingMixedEntrySoundness (Setup prepare extend start)
open Tools.ShippingMixedInputSoundness (inputState inputWire)

/-- A prepared state's widths: no output, wires distinct and reserved, inputs
are wires, wires scalar. -/
def PrepT (s : CircuitState) : Prop :=
  s.module.outputs = [] ∧ Tools.ShippingTranslateSoundness.WiresOk s ∧
    (∀ p ∈ s.module.inputs, p ∈ s.module.wires) ∧
    (∀ p ∈ s.module.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n)

theorem prepT_init (N : String) : PrepT (CircuitM.init N) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp [CircuitM.init, Sparkle.IR.AST.Module.empty]
  · simp [CircuitM.init, Sparkle.IR.AST.Module.empty]
  · intro p hp
    simp [CircuitM.init, Sparkle.IR.AST.Module.empty] at hp
  · intro p hp
    simp [CircuitM.init, Sparkle.IR.AST.Module.empty] at hp
  · intro p hp
    simp [CircuitM.init, Sparkle.IR.AST.Module.empty] at hp

theorem prepT_input {s : CircuitState} (h : PrepT s) (name : String) (ty : Sparkle.IR.Type.HWType)
    (hty : ty = .bit ∨ ∃ n, ty = .bitVector n) : PrepT (inputState s name ty) := by
  obtain ⟨ho, hw, hi, hs⟩ := h
  have hwires := Tools.ShippingMixedInputSoundness.input_wires s name ty
  refine ⟨?_, Tools.ShippingMixedInputSoundness.input_wiresOk hw, ?_, ?_⟩
  · rw [inputState_eqN]
    show (CircuitM.makeWire name ty true s).2.module.outputs = []
    rw [makeWire_module]
    exact ho
  · intro p hp
    rw [inputState_inputsN] at hp
    rw [hwires]
    rcases List.mem_cons.mp hp with he | hp
    · rw [he]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hi p hp)
  · intro p hp
    rw [hwires] at hp
    rcases List.mem_cons.mp hp with he | hp
    · rw [he]
      exact hty
    · exact hs p hp

theorem prepare_prepT (bools : Lean.FVarId → Bool)
    (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × Lean.FVarId)) (a : Setup),
    PrepT a.state → PrepT (prepare bools bits L a).state
  | [], _, h => h
  | ((nm, k), id) :: rest, a, h => by
    apply prepare_prepT bools bits rest (extend a ((nm, k), id) bools bits)
    cases k with
    | domain => exact h
    | bool => exact prepT_input h nm.toString .bit (Or.inl rfl)
    | bits n => exact prepT_input h nm.toString (.bitVector n) (Or.inr ⟨n, rfl⟩)

theorem prepare_inputs_monoP (bools : Lean.FVarId → Bool)
    (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × Lean.FVarId)) (a : Setup)
      (p : Sparkle.IR.AST.Port),
    p ∈ a.state.module.inputs → p ∈ (prepare bools bits L a).state.module.inputs
  | [], _, _, h => h
  | ((nm, k), id) :: rest, a, p, h => by
    apply prepare_inputs_monoP bools bits rest (extend a ((nm, k), id) bools bits) p
    cases k with
    | domain => exact h
    | bool =>
      show p ∈ (inputState a.state nm.toString .bit).module.inputs
      rw [inputState_inputsN]
      exact List.mem_cons_of_mem _ h
    | bits n =>
      show p ∈ (inputState a.state nm.toString (.bitVector n)).module.inputs
      rw [inputState_inputsN]
      exact List.mem_cons_of_mem _ h

/-- **A prepared bit-vector binder is bound to an input port of its type**
(`prepare_lookup_hitI` with the port's type). -/
theorem prepare_lookup_hitB (bools : Lean.FVarId → Bool)
    (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × Lean.FVarId)) (a : Setup) (nm : Lean.Name)
      (n : Nat) (id : Lean.FVarId),
    (L.map (·.2)).Nodup → ((nm, MixedGateBinder.bits n), id) ∈ L →
    ∃ z, (prepare bools bits L a).context.varMap.lookup id = some z ∧
      ({ name := z, ty := .bitVector n } : Sparkle.IR.AST.Port) ∈
        (prepare bools bits L a).state.module.inputs
  | [], _, _, _, _, _, hm => by simp at hm
  | ((nm', k'), i) :: rest, a, nm, n, id, hnd, hm => by
    have hnd' := List.nodup_cons.mp hnd
    show ∃ z, (prepare bools bits rest (extend a ((nm', k'), i) bools bits)).context.varMap.lookup
      id = some z ∧
      ({ name := z, ty := .bitVector n } : Sparkle.IR.AST.Port) ∈
        (prepare bools bits rest (extend a ((nm', k'), i) bools bits)).state.module.inputs
    rcases List.mem_cons.mp hm with he | hm'
    · have hid : id = i := (Prod.mk.inj he).2
      have hkk : MixedGateBinder.bits n = k' := (Prod.mk.inj (Prod.mk.inj he).1).2
      subst hkk
      rw [hid]
      rw [prepare_lookup_keep bools bits rest _ i
        (fun x hx hxe => hnd'.1 (List.mem_map.mpr ⟨x, hx, hxe⟩))]
      refine ⟨_, Tools.ShippingEntrySoundness.lookup_cons_self _ _ _, ?_⟩
      apply prepare_inputs_monoP
      show ({ name := inputWire a.state nm'.toString (.bitVector n), ty := .bitVector n } :
          Sparkle.IR.AST.Port) ∈
        (inputState a.state nm'.toString (.bitVector n)).module.inputs
      rw [inputState_inputsN]
      exact List.mem_cons_self
    · exact prepare_lookup_hitB bools bits rest _ nm n id hnd'.2 hm'

/-- **The typed invariant at a prepared state** (empty body, no record). -/
theorem tok_of_prep {G : Sparkle.IR.AST.Module → Prop} {τ : Lean.Expr → Nat} {s : CircuitState}
    (h : PrepOkN s) (hT : PrepT s) : TOk G s.module.inputs τ s := by
  obtain ⟨hb, hr, -, -⟩ := h
  obtain ⟨ho, hw, hi, hs⟩ := hT
  refine ⟨ho, rfl, hi, hw, hs, ?_, ?_, ?_⟩
  · intro l r hm
    rw [hb] at hm
    simp at hm
  · intro mn i cs hm
    rw [hb] at hm
    simp at hm
  · intro w e he
    exact (hr w e he).elim

end preparedT

/-! ## The checks of the returned module -/

section finalT
open Sparkle.IR.AST Sparkle.IR.Builder Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingTypedExprSoundness (TypedExpr)

/-- What the checks ask of a callee `x` in the design `ms`: resolved to
itself, width-typed, its ports of their types' widths (a gate child's
`GateChildPorts`, `gFacts_of_ports`). -/
def GFactsT (ms : List Sparkle.IR.AST.Module) (x : Sparkle.IR.AST.Module) : Prop :=
  Sparkle.IR.Machine.moduleByName ms x.name = some x ∧
  Tools.ShippingHierTyped.childTyped (declWidth x) x = true ∧
  (∀ q ∈ x.inputs, declWidth x q.name = q.ty.bitWidth ∧
    Tools.ShippingDesignSV.weS x q.name = q.ty.bitWidth) ∧
  (∀ p ∈ x.outputs, Tools.ShippingDesignSV.weS x p.name = p.ty.bitWidth)

theorem gFacts_of_ports {ms : List Sparkle.IR.AST.Module} {x : Sparkle.IR.AST.Module}
    {c : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {w : Nat}
    (hm : Sparkle.IR.Machine.moduleByName ms x.name = some x)
    (h : Tools.ShippingGatePorts.GateChildPorts c bs w x) : GFactsT ms x := by
  refine ⟨hm, h.childTyped_ok, fun q hq => ⟨h.declWidth_in hq, h.weS_in hq⟩, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := h.outWidth p hp
  rw [h1, h2]
  exact h.weS_out

theorem prod_eqT {c : String × Sparkle.IR.AST.Expr} {x : String} {y : Sparkle.IR.AST.Expr}
    (h1 : c.1 = x) (h2 : c.2 = y) : c = (x, y) := by
  obtain ⟨c1, c2⟩ := c
  subst h1 h2
  rfl

theorem refs_binT {o : Operator} {a b x : String}
    (h : x ∈ Sparkle.IR.Reorder.refsOf (.op o [.ref a, .ref b])) : x = a ∨ x = b := by
  simpa [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList] using h

theorem refs_refT {a x : String} (h : x ∈ Sparkle.IR.Reorder.refsOf (.ref a)) : x = a := by
  simpa [Sparkle.IR.Reorder.refsOf] using h

theorem typed_refT {we : WEnv} {x : String} {k : Nat} (hx : we x = k) (hk : 0 < k) :
    TypedExpr we (.ref x) k := by
  rw [← hx]
  exact Tools.ShippingTypedExprSoundness.TypedExpr.ref x (by rw [hx]; exact hk)

theorem typed_binT {we : WEnv} {bo : Tools.ShippingScalarSoundness.Binary} {a b : String}
    {k : Nat} (ha : we a = k) (hb : we b = k) (hk : 0 < k) :
    TypedExpr we (.op bo.operator [.ref a, .ref b]) k :=
  Tools.ShippingTypedExprSoundness.TypedExpr.bin bo (typed_refT ha hk) (typed_refT hb hk) (by cases bo <;> rfl)

theorem typed_cmpT {we : WEnv} {le : SignalCompareKind} {a b : String} {k : Nat}
    (ha : we a = k) (hb : we b = k) (hk : 0 < k) :
    TypedExpr we (.op (signalCompareOp le) [.ref a, .ref b]) 1 := by
  cases le with
  | ult => exact Tools.ShippingTypedExprSoundness.TypedExpr.compare (n := k) rfl (typed_refT ha hk) (typed_refT hb hk)
  | ule => exact Tools.ShippingTypedExprSoundness.TypedExpr.compare (n := k) rfl (typed_refT ha hk) (typed_refT hb hk)
  | eq => exact Tools.ShippingTypedExprSoundness.TypedExpr.compare (n := k) rfl (typed_refT ha hk) (typed_refT hb hk)
  | slt => exact Tools.ShippingTypedExprSoundness.TypedExpr.signedCompare a b rfl (by rw [ha]; exact hk) (by rw [ha, hb])
  | sle => exact Tools.ShippingTypedExprSoundness.TypedExpr.signedCompare a b rfl (by rw [ha]; exact hk) (by rw [ha, hb])

/-- **The four width checks of a module with the core module's body, wires
and ports** (file header). Pure. -/
theorem typed_checks {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {I : List String} {sm0 : CircuitState} {wire : String}
    {ty : Sparkle.IR.Type.HWType} {kw : Nat} {b : Sparkle.IR.AST.Module}
    (ht : TOk G Ip τ sm0) (hn : NOk G I sm0) (hwire : WidthIs sm0 wire kw) (hty : ScalT ty kw)
    (hb : b.body = (Stmt.assign "out" (.ref wire) :: sm0.module.body).reverse)
    (hw : b.wires = sm0.module.wires.reverse) (hi : b.inputs = sm0.module.inputs.reverse)
    (ho : b.outputs = [{ name := "out", ty := ty }])
    (ms : List Sparkle.IR.AST.Module) (hG : ∀ x, G x → GFactsT ms x) :
    Tools.ShippingHierTyped.hierTyped (childMap ms) b = true ∧
      Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
        (Tools.ShippingDesignSV.weS b) b.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames b.body).all
        (fun x => declWidth b x == Tools.ShippingDesignSV.weS b x) = true ∧
      Tools.ShippingDesignSV.portsMatchB (childMap ms) b = true := by
  -- the wires of `b`: the walk's, allocated, distinct, scalar
  have hwM : ∀ p ∈ b.wires, p ∈ sm0.module.wires := by
    intro p hp
    rw [hw] at hp
    exact List.mem_reverse.mp hp
  have hwA : ∀ p ∈ b.wires, Sparkle.IR.NameHints.Allocated p.name :=
    fun p hp => hn.alloc _ (ht.wok.2 p (hwM p hp))
  have hwn : ∀ p ∈ b.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
    fun p hp => Tools.ShippingNamesStable.sanitizeName_of_allocated (hwA p hp)
  have hwout : ∀ p ∈ b.wires, p.name ≠ "out" := fun p hp e => nAllocOutN (e ▸ hwA p hp)
  have hwnd : (b.wires.map (·.name)).Nodup := by
    rw [hw, List.map_reverse]
    exact Tools.ShippingEntrySoundness.nodup_reverse ht.wok.1
  have hwsc : ∀ p ∈ b.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n :=
    fun p hp => ht.wsc p (hwM p hp)
  have hinw : ∀ p ∈ b.inputs, p ∈ b.wires := by
    intro p hp
    rw [hi] at hp
    rw [hw]
    exact List.mem_reverse.mpr (ht.inw p (List.mem_reverse.mp hp))
  -- a walk width is the width in both tables
  have dW : ∀ x k, WidthIs sm0 x k →
      declWidth b x = k ∧ Tools.ShippingDesignSV.weS b x = k ∧ x ∈ b.wires.map (·.name) := by
    intro x k hx
    obtain ⟨ty', hm, hsc⟩ := hx
    have hmb : ({ name := x, ty := ty' } : Sparkle.IR.AST.Port) ∈ b.wires := by
      rw [hw]
      exact List.mem_reverse.mpr hm
    have hxm : x ∈ b.wires.map (·.name) := List.mem_map.mpr ⟨_, hmb, rfl⟩
    have hd : declWidth b x = k :=
      (Tools.ShippingInstWidthsParts.declWidth_of_unique hmb
        (fun r hr hrn => Tools.ShippingTransitionPortTys.port_of_name hwnd hr hmb hrn)
        hsc.scalar).trans hsc.bitWidth
    have hs : Tools.ShippingDesignSV.weS b x = k :=
      (Tools.ShippingWidthTables.declWidth_eq_weS hwn hxm).symm.trans hd
    exact ⟨hd, hs, hxm⟩
  have hX0 : declWidth b "out" = 0 :=
    Tools.ShippingTypedWidthOk.weOf_not_wire (m := b) (x := "out") (fun p hp => hwout p hp)
  -- the one output port `out`
  have hXp : b.outputs.map (·.name) = ["out"] := by
    rw [ho]
    try rfl
  have hq : ({ name := "out", ty := ty } : Sparkle.IR.AST.Port) ∈ b.outputs := by
    rw [ho]
    exact List.mem_singleton_self _
  have hso : Sparkle.Backend.Verilog.sanitizeName "out" = "out" := by
    simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
  have hP : Tools.ShippingLeafTyped.PortsIn b := by
    refine { wn := hwn, ow := ?_, oi := ?_, ostable := ?_, ond := ?_, oty := ?_ }
    · intro q hq' p hp
      rw [ho] at hq'
      rw [List.mem_singleton.mp hq']
      exact hwout p hp
    · intro q hq' p hp
      rw [ho] at hq'
      rw [List.mem_singleton.mp hq', hwn p (hinw p hp)]
      exact hwout p (hinw p hp)
    · intro q hq'
      rw [ho] at hq'
      rw [List.mem_singleton.mp hq']
      exact hso
    · rw [ho]
      first
        | exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
        | simp
    · intro q hq'
      rw [ho] at hq'
      rw [List.mem_singleton.mp hq']
      exact hty.scalar
  obtain ⟨hdw, hsw, hwm⟩ := dW wire kw hwire
  have hsO : Tools.ShippingDesignSV.weS b "out" = kw := (hP.weS_output hq).trans hty.bitWidth
  -- the body: `out := wire` and the walk's statements
  have hmemB : ∀ st ∈ b.body, st = Stmt.assign "out" (.ref wire) ∨ st ∈ sm0.module.body := by
    intro st hst
    rw [hb, List.mem_reverse] at hst
    exact List.mem_cons.mp hst
  have hkind : ∀ st ∈ b.body,
      (∃ l r, st = Stmt.assign l r) ∨ (∃ mn i cs, st = Stmt.inst mn i cs) := by
    intro st hst
    rcases hmemB st hst with he | h
    · exact Or.inl ⟨_, _, he⟩
    · exact hn.kinds st h
  have hk : ∀ st ∈ b.body, Tools.ShippingHierSVSoundness.seqStmtOkI st = true := by
    intro st hst
    rcases hkind st hst with ⟨l, r, he⟩ | ⟨mn, i, cs, he⟩
    · subst he
      rfl
    · subst he
      rfl
  have hnoReg : ∀ o c rk i iv, Stmt.register o c rk i iv ∉ b.body := by
    intro o c rk i iv hm
    rcases hkind _ hm with ⟨l, r, he⟩ | ⟨mn, i', cs, he⟩ <;> cases he
  -- every assignment: `out := wire`, or typed at its target's width in both tables
  have hA : ∀ l r, Stmt.assign l r ∈ b.body →
      (l = "out" ∧ r = .ref wire) ∨
      ∃ (k : Nat), 0 < k ∧ declWidth b l = k ∧ Tools.ShippingDesignSV.weS b l = k ∧
        l ∈ b.wires.map (·.name) ∧
        (∀ x ∈ Sparkle.IR.Reorder.refsOf r, x ∈ b.wires.map (·.name)) ∧
        ∀ we : WEnv, (∀ x ∈ b.wires.map (·.name), we x = declWidth b x) → TypedExpr we r k := by
    intro l r hm
    rcases hmemB _ hm with he | hm'
    · left
      cases he
      exact ⟨rfl, rfl⟩
    · right
      obtain ⟨o, a, a', k, hr, wa, wa', hl⟩ := ht.asg l r hm'
      obtain ⟨hda, -, hma⟩ := dW a k wa
      obtain ⟨hda', -, hma'⟩ := dW a' k wa'
      have hrefs : ∀ x ∈ Sparkle.IR.Reorder.refsOf r, x ∈ b.wires.map (·.name) := by
        intro x hx
        rw [hr] at hx
        rcases refs_binT hx with hx' | hx'
        · rw [hx']
          exact hma
        · rw [hx']
          exact hma'
      rcases hl with ⟨⟨bo, hbo⟩, wl⟩ | ⟨⟨le, hle⟩, wl⟩
      · obtain ⟨hdl, hsl, hml⟩ := dW l k wl
        refine ⟨k, wa.pos, hdl, hsl, hml, hrefs, fun we hwe => ?_⟩
        rw [hr, ← hbo]
        exact typed_binT ((hwe a hma).trans hda) ((hwe a' hma').trans hda') wa.pos
      · obtain ⟨hdl, hsl, hml⟩ := dW l 1 wl
        refine ⟨1, Nat.one_pos, hdl, hsl, hml, hrefs, fun we hwe => ?_⟩
        rw [hr, ← hle]
        exact typed_cmpT ((hwe a hma).trans hda) ((hwe a' hma').trans hda') wa.pos
  -- the child behind an instance statement
  have hInst : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      InstT G sm0 mn conns := by
    intro mn iname conns hm
    rcases hmemB _ hm with he | hm'
    · cases he
    · exact ht.inst mn iname conns hm'
  have hCx : ∀ x, G x → childMap ms x.name = some (x, declWidth x) := by
    intro x hx
    show (Sparkle.IR.Machine.moduleByName ms x.name).map _ = _
    rw [(hG x hx).1]
    try rfl
  -- (1) `hierTyped`
  have hty1 : Tools.ShippingHierTyped.hierTyped (childMap ms) b = true := by
    unfold Tools.ShippingHierTyped.hierTyped
    rw [Bool.and_eq_true]
    constructor
    · refine Tools.ShippingTypedWidthOk.kidsTyped_of ?_ ?_ hk
      · intro l r hm
        have hX : ∀ x ∈ b.outputs.map (·.name), declWidth b x = 0 := by
          intro x hx
          rw [hXp] at hx
          rw [List.mem_singleton.mp hx]
          exact hX0
        rcases hA l r hm with ⟨hl, hr⟩ | ⟨k, hk0, hdl, -, -, -, hT⟩
        · rw [hl, hr]
          refine Tools.ShippingTypedWidthOk.assignTyped_of_typed
            (typed_refT hdw (WidthIs.pos hwire)) hX (Or.inr ?_)
          rw [hXp]
          exact List.mem_singleton_self _
        · exact Tools.ShippingTypedWidthOk.assignTyped_of_typed (hT _ (fun _ _ => rfl)) hX
            (Or.inl hdl)
      · intro mn iname conns hm
        obtain ⟨x, ins, o, k, w0, hGx, hxn, hxo, hcs, hoin, ww, hconn⟩ :=
          hInst mn iname conns hm
        obtain ⟨-, hct, hinq, -⟩ := hG x hGx
        subst hxn
        obtain ⟨hdw0, -, -⟩ := dW w0 k ww
        refine ⟨x, declWidth x, hCx x hGx, hct, ?_⟩
        refine Tools.ShippingTypedWidthOk.connsTyped_call (outW := w0)
          (argWs := ins.filterMap connRefN) hxo ?_ ?_ ?_ ?_
        · intro c hc
          rw [hcs] at hc
          rcases List.mem_append.mp hc with hc | hc
          · right
            obtain ⟨a, q, hqx, hca, hqn, -⟩ := hconn c hc
            refine ⟨q, hqx, a, List.mem_filterMap.mpr ⟨c, hc, connRefN_of hca⟩,
              prod_eqT hqn.symm hca, ?_⟩
            intro he
            exact hoin (List.mem_map.mpr ⟨q, hqx, he⟩)
          · left
            exact List.mem_singleton.mp hc
        · rw [hcs]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · intro pn aw hpa hne
          rw [hcs] at hpa
          rcases List.mem_append.mp hpa with hpa | hpa
          · obtain ⟨a, q, hqx, hca, hqn, wa⟩ := hconn _ hpa
            have haw : aw = a := Sparkle.IR.AST.Expr.ref.inj hca
            subst haw
            obtain ⟨hda, -, hma⟩ := dW aw _ wa
            have hqn' : q.name = pn := hqn
            refine ⟨?_, ?_⟩
            · intro hX'
              rw [hXp] at hX'
              obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hma
              have hpn' : p.name = aw := hpn
              exact hwout p hp (hpn'.trans (List.mem_singleton.mp hX'))
            · exact Nat.le_of_eq (by rw [hda, ← hqn', (hinq q hqx).1])
          · exact absurd (Prod.mk.inj (List.mem_singleton.mp hpa)).1 hne
        · right
          rw [hdw0]
          exact Nat.le_refl _
    · rw [List.all_eq_true]
      intro p hp
      unfold Sparkle.IR.HierCheck.openIns at hp
      have hpw : p ∈ b.wires := (List.mem_filter.mp hp).1
      rw [hXp]
      exact Tools.ShippingTypedWidthOk.not_contains
        (fun h => hwout p hpw (List.mem_singleton.mp h))
  -- (2) `seqCheck`
  have hweq : ∀ x ∈ b.wires.map (·.name),
      Tools.SVParser.EmitSem.weOf (Tools.ShippingDesignSV.wofOf b) x = declWidth b x :=
    fun x hx => (Tools.ShippingWidthTables.declWidth_eq_weS hwn hx).symm
  have hDw : ∀ x ∈ b.wires.map (·.name),
      Tools.ShippingSeqCheckTyped.Decl (Tools.ShippingDesignSV.wofOf b) x := by
    intro x hx
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hx
    have hpn' : p.name = x := hpn
    refine ⟨?_, Tools.ShippingWidthTables.moduleWof_wire hwn hwsc hx⟩
    rw [← hpn']
    exact hwn p hp
  have hDo : Tools.ShippingSeqCheckTyped.Decl (Tools.ShippingDesignSV.wofOf b) "out" :=
    ⟨hso, ty.bitWidth, hP.wof_output hq⟩
  have hsc1 : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
      (Tools.ShippingDesignSV.weS b) b.body = true := by
    refine Tools.ShippingSeqCheckTyped.seqCheck_of_typed b.body hk ?_ ?_
    · intro l r hm
      rcases hA l r hm with ⟨hl, hr⟩ | ⟨k, hk0, hdl, hsl, hml, hrefs, hT⟩
      · rw [hl, hr]
        refine ⟨hDo, ?_, ?_⟩
        · have e1 : Tools.SVParser.EmitSem.weOf (Tools.ShippingDesignSV.wofOf b) "out" =
              Tools.SVParser.EmitSem.weOf (Tools.ShippingDesignSV.wofOf b) wire :=
            hsO.trans hsw.symm
          rw [e1]
          exact Tools.ShippingTypedExprSoundness.TypedExpr.ref wire (Nat.lt_of_lt_of_eq (WidthIs.pos hwire) hsw.symm)
        · intro x hx
          rw [refs_refT hx]
          exact hDw wire hwm
      · refine ⟨hDw l hml, ?_, fun x hx => hDw x (hrefs x hx)⟩
        have hsl' : Tools.SVParser.EmitSem.weOf (Tools.ShippingDesignSV.wofOf b) l = k := hsl
        rw [hsl']
        exact hT _ hweq
    · intro o c rk i iv hm
      exact absurd hm (hnoReg o c rk i iv)
  -- (3) the `seqNames` agreement
  have hsn : (Tools.ShippingSeqSVSoundness.seqNames b.body).all
      (fun x => declWidth b x == Tools.ShippingDesignSV.weS b x) = true := by
    refine Tools.ShippingWidthTables.seqNames_widths hwn ?_
    intro x hx
    rcases Tools.ShippingTextTyped.mem_seqNames b.body x hx with
      ⟨l, r, hm, hxr⟩ | ⟨o, c, rk, i, iv, hm, -⟩
    · rcases hA l r hm with ⟨-, hr⟩ | ⟨k, -, -, -, -, hrefs, -⟩
      · rw [hr] at hxr
        rw [refs_refT hxr]
        exact hwm
      · exact hrefs x hxr
    · exact absurd hm (hnoReg o c rk i iv)
  -- (4) `portsMatchB`
  have hpm : Tools.ShippingDesignSV.portsMatchB (childMap ms) b = true := by
    refine Tools.ShippingTextShipped.portsMatchB_of ?_ ?_
    · intro mn iname conns child cwe hm hc c hcm w0' hw0'
      obtain ⟨x, ins, o, k, w0, hGx, hxn, hxo, hcs, hoin, ww, hconn⟩ :=
        hInst mn iname conns hm
      obtain ⟨-, -, hinq, houtq⟩ := hG x hGx
      subst hxn
      rw [hCx x hGx] at hc
      have hcx : x = child := (Prod.mk.inj (Option.some.inj hc)).1
      subst hcx
      rw [hcs] at hcm
      rcases List.mem_append.mp hcm with hcm | hcm
      · obtain ⟨a, q, hqx, hca, hqn, wa⟩ := hconn c hcm
        rw [hw0'] at hca
        have haw : w0' = a := Sparkle.IR.AST.Expr.ref.inj hca
        subst haw
        obtain ⟨-, hsa, -⟩ := dW w0' _ wa
        rw [hsa, ← hqn, (hinq q hqx).2]
      · have hce := List.mem_singleton.mp hcm
        rw [hce] at hw0'
        have hww : w0 = w0' := Sparkle.IR.AST.Expr.ref.inj hw0'
        subst hww
        obtain ⟨-, hsw0, -⟩ := dW w0 k ww
        rw [hsw0, hce]
        have hko := houtq ⟨o, .bitVector k⟩ (by rw [hxo]; exact List.mem_singleton_self _)
        exact hko.symm
    · intro mn iname conns hm
      obtain ⟨x, -, -, -, -, hGx, hxn, -⟩ := hInst mn iname conns hm
      subst hxn
      rw [hCx x hGx]
      try rfl
  exact ⟨hty1, hsc1, hsn, hpm⟩

/-- `leafOutputType` of a walk wire is its declared type. -/
theorem leafOutputType_scalT {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {s : CircuitState} {wire : String} {k : Nat}
    (ht : TOk G Ip τ s) (hw : WidthIs s wire k) :
    ScalT (Tools.ShippingEntrySoundness.leafOutputType s wire) k := by
  obtain ⟨ty, hm, hsc⟩ := hw
  have hf : s.module.wires.find? (fun p => p.name == wire) =
      some ({ name := wire, ty := ty } : Sparkle.IR.AST.Port) :=
    Tools.ShippingEntrySoundness.find?_of_nodup ht.wok.1 hm
  unfold Tools.ShippingEntrySoundness.leafOutputType
  rw [hf]
  exact hsc

/-- What the typed walk concludes of the core module (file header): the four
checks of every module with its body, wires and ports. -/
def TFin (G : Sparkle.IR.AST.Module → Prop) (m : Sparkle.IR.AST.Module) : Prop :=
  ∀ b : Sparkle.IR.AST.Module, b.body = m.body → b.wires = m.wires → b.inputs = m.inputs →
    b.outputs = m.outputs →
  ∀ ms : List Sparkle.IR.AST.Module, (∀ x, G x → GFactsT ms x) →
    Tools.ShippingHierTyped.hierTyped (childMap ms) b = true ∧
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
      (Tools.ShippingDesignSV.weS b) b.body = true ∧
    (Tools.ShippingSeqSVSoundness.seqNames b.body).all
      (fun x => declWidth b x == Tools.ShippingDesignSV.weS b x) = true ∧
    Tools.ShippingDesignSV.portsMatchB (childMap ms) b = true

/-- **The typed walk's conclusion on the returned core module** (the entry's
tail: output port, `out := wire`, no clock/reset, `finalize`). -/
theorem typed_final_of {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {I : List String} {sm0 st : CircuitState} {wire : String}
    {ty : Sparkle.IR.Type.HWType} {m : Sparkle.IR.AST.Module} {kw : Nat}
    (ht : TOk G Ip τ sm0) (hn : NOk G I sm0) (hwire : WidthIs sm0 wire kw)
    (hst : st = (CircuitM.emitAssign "out" (.ref wire) (CircuitM.addOutput "out" ty sm0).2).2)
    (hty : ty = Tools.ShippingEntrySoundness.leafOutputType sm0 wire)
    (hm : m = (addClockResetIfSequential st.module).finalize) : TFin G m := by
  have hmod : st.module =
      (sm0.module.addOutput { name := "out", ty := ty }).addStmt (.assign "out" (.ref wire)) := by
    subst hst; rfl
  have hcomb : addClockResetIfSequential st.module = st.module := by
    apply addClockReset_des
    intro x hx
    rw [hmod] at hx
    rcases List.mem_cons.mp hx with he | hx
    · exact Or.inl ⟨_, _, he⟩
    · exact hn.kinds x hx
  have hbody : m.body = (Stmt.assign "out" (.ref wire) :: sm0.module.body).reverse := by
    rw [hm, hcomb, hmod]
    try rfl
  have hwires : m.wires = sm0.module.wires.reverse := by
    rw [hm, hcomb, hmod]
    try rfl
  have hins : m.inputs = sm0.module.inputs.reverse := by
    rw [hm, hcomb, hmod]
    try rfl
  have houts0 : m.outputs =
      (({ name := "out", ty := ty } : Sparkle.IR.AST.Port) :: sm0.module.outputs).reverse := by
    rw [hm, hcomb, hmod]
    try rfl
  have houts : m.outputs = [{ name := "out", ty := ty }] := by
    rw [houts0, ht.outs]
    try rfl
  have hsc : ScalT ty kw := by
    rw [hty]
    exact leafOutputType_scalT ht hwire
  intro b hb hw hi ho ms hG
  exact typed_checks ht hn hwire hsc (hb.trans hbody) (hw.trans hwires) (hi.trans hins)
    (ho.trans houts) ms hG

end finalT

/-! ## The harness and the full entry -/

section harnessT
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingChildInv (RefLaws InvV Res CacheInv ChildBnd bodyRel profLogIO RealChild)
open Tools.ShippingCacheCoherentRun (SubMap sub_refl)
open Tools.ShippingGateDefines (GateDefines)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- The prepared input ports of a body instantiated at `ids`. -/
abbrev prepPortsT (bs : List (Lean.Name × MixedGateBinder)) (ids : List FVarId)
    (cache : IO.Ref (Lean.ExprStructMap String)) (N : String) : List Sparkle.IR.AST.Port :=
  (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
    (start (entryCompilerState false cache) N)).state.module.inputs

/-- **On the harness run**: the naming and the typed walks' contracts of the
body give `TFin` of the returned core module. -/
theorem typedFinal_of_run {L : RefLaws mref cref} {mF : Std.HashMap Lean.Name Res} {D : Nat}
    {rec : TranslateFn} {bs : List (Lean.Name × MixedGateBinder)} {ids : List FVarId}
    {cache : IO.Ref (Lean.ExprStructMap String)} {N : String}
    {G : Sparkle.IR.AST.Module → Prop} {τ : Lean.Expr → Nat} {e : Lean.Expr}
    {wT wT' : Void IO.RealWorld} {wire : String} {sm0 st : CircuitState}
    {ty : Sparkle.IR.Type.HWType} {m : Sparkle.IR.AST.Module}
    (hN : NamW L mF D rec
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).context G (prepInsN bs ids cache N) e)
    (hT : TypW L mF D rec
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).context G (prepPortsT bs ids cache N) τ e)
    (hwT : InvV L wT) (hdT : L.dval wT = D) (hsubT : SubMap (L.val wT') mF)
    (htr : RunsC (rec e "out" false true)
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).context
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).state
      mctx mref cctx cref wT (wire, sm0) wT')
    (hst : st = (CircuitM.emitAssign "out" (.ref wire) (CircuitM.addOutput "out" ty sm0).2).2)
    (hty : ty = leafOutputType sm0 wire)
    (hm : m = (addClockResetIfSequential st.module).finalize) : TFin G m := by
  have hP := prepare_prepOkN (fun _ => false) (fun _ _ => 0) (bs.zip ids)
    (start (entryCompilerState false cache) N) (prepOk_initN N)
  have h0 : NOk G (prepInsN bs ids cache N)
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).state :=
    nok_of_prepN hP
  have t0 : TOk G (prepPortsT bs ids cache N) τ
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).state :=
    tok_of_prep hP (prepare_prepT _ _ (bs.zip ids) _ (prepT_init N))
  obtain ⟨h1, -, -, -⟩ := hN mctx cctx "out" false true _ sm0 wire wT wT' hwT hdT hsubT htr h0
  obtain ⟨t1, -, hw1⟩ := hT mctx cctx "out" false true _ sm0 wire wT wT' hwT hdT hsubT htr t0
  exact typed_final_of t1 h1 hw1 hst hty hm

/-- **The harness with three walks** (`cone_harness_names` with the typed
walk; the old theorems kept). -/
theorem cone_harness_typed (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      ∀ (G : Sparkle.IR.AST.Module → Prop) (τ : Lean.Expr → Nat),
        (∀ (cache' : IO.Ref (Lean.ExprStructMap String)) (ids' : List FVarId), ids'.Nodup →
          ids'.length = bs.length →
          DesW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (Sparkle.IR.ModuleName.ofDecl declName)
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) true ∧
          NamW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (prepInsN bs ids' cache' (Sparkle.IR.ModuleName.ofDecl declName))
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) ∧
          TypW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (prepPortsT bs ids' cache' (Sparkle.IR.ModuleName.ofDecl declName)) τ
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body)) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl declName) m d ∧ NFin G m ∧ TFin G m := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, hty, hm,
    hdd⟩ :=
    mixedHarness_runs L hw hd hr
  obtain ⟨⟨hcT, -, -⟩, -, -⟩ := fuel_runsW (tenv := tenv) L hD translateFuelLimit hwT hdT htr
  refine ⟨wT', hcT, fun G τ hE hpos => ⟨?_, ?_, ?_⟩⟩
  · exact desFinal_of_run (hE cache ids nd len).1 hpos hwT hdT (sub_refl _) htr hst hty hm hdd
  · exact namesFinal_of_run (hE cache ids nd len).2.1 hwT hdT (sub_refl _) htr hst hm
  · exact typedFinal_of_run (hE cache ids nd len).2.1 (hE cache ids nd len).2.2 hwT hdT
      (sub_refl _) htr hst hty hm

/-- **The full entry with three walks** (`gate_cone_runNames` with the typed
walk; a copy of its proof, the old theorems kept). -/
theorem gate_cone_runTyped {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs body)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (Dd : Sparkle.IR.AST.Design) (envR : Lean.Environment)
      (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      ((∀ x ∈ Dd.modules, x.name ≠ M.name) → design.modules = Dd.modules) ∧
      (∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body)) ∧
      CacheInv mref cref mF ∧
      (∀ (G : Sparkle.IR.AST.Module → Prop) (τ : Lean.Expr → Nat),
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 →
          ∀ (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId), ids.Nodup →
          ids.length = bs.length →
          DesW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
              (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
            G (Sparkle.IR.ModuleName.ofDecl f)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) true ∧
          NamW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
              (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
            G (prepInsN bs ids cache (Sparkle.IR.ModuleName.ofDecl f))
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) ∧
          TypW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
              (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
            G (prepPortsT bs ids cache (Sparkle.IR.ModuleName.ofDecl f)) τ
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body)) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl f) M Dd ∧ NFin G M ∧ TFin G M) := by
  obtain ⟨L, ⟨hsv, hdep⟩, hq⟩ := bnd
  obtain ⟨M, Dd, w1, hcore, hpost⟩ :=
    Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨M2, D2, w2, hcore2, -, hname, hmods⟩ := Tools.ShippingCacheCoherentRun.full_split L hr
  obtain ⟨hMD, -⟩ := runsTo_det hcore2 hcore
  obtain ⟨hM, hD⟩ := Prod.mk.inj hMD
  rw [hM] at hname
  rw [hM, hD] at hmods
  have hreads : ∃ (bb : Bool) (envR : Lean.Environment) (ci : Lean.ConstantInfo)
      (a1 a2 a3 a4 a5 a6 : Void IO.RealWorld),
      RunsTo (Lean.getConstInfo f) mctx mref cctx cref a1 ci a2 ∧
      RunsTo (Lean.getEnv : Lean.Meta.MetaM Lean.Environment) mctx mref cctx cref a5 envR a6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n)
        (profLogIO bb) f [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref a3 (M, Dd) a4 ∧ InvV L a3 ∧ L.dval a3 ≠ 0 := by
    by_cases h0 : L.dval w = 0
    · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
        Tools.ShippingCacheCoherentOuter.core_reads_val0 L (fun L' => bodyRel L') hsv hq h0 hcore
      exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
    · rcases hdep with hz | hci
      · exact absurd hz h0
      · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
          Tools.ShippingCacheCoherentVia.core_reads_val L (fun L' => bodyRel L')
            ⟨hci, hsv, hq⟩ h0 hcore
        exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
  obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩ := hreads
  obtain ⟨dv, hdv, hold, hshape⟩ := gdef a1 ci a2 a5 envR a6 hget henv
  rw [hdv] at run
  obtain ⟨wa, wb, hwa, hda, hharn⟩ := sfc_mixed_run L hold hshape hw3 run
  have hDa : L.dval wa ≠ 0 := by rw [hda]; exact hd3
  obtain ⟨wT', hcache, hdes⟩ :=
    cone_harness_typed (tenv := envR) L (D := L.dval wa) hDa hwa rfl hharn
  exact ⟨M, Dd, envR, L.val wT', hpost, hmods, ⟨dv, hshape⟩, hcache,
    fun G τ hE hpos => hdes G τ (fun cache ids nd len => hE L (L.dval wa) hDa cache ids nd len)
      hpos⟩

end harnessT

/-! ## `hierTyped` and `designSideB3` for a parent of one gate child -/

section factsT
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingChildInv (RefLaws Res CacheInv ChildBnd RealChild)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingMixedEntrySoundness (prepare start)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **`hierTyped` and `designSideB3` derived** for a gate parent whose
instance leaves call one gate child `c` (file header). Premises: the run,
`GateDefines` (NOT ALLOWED), `ChildBnd`; the child facts of every `c` entry
of a `CacheInv` cache (incl. `GateChildPorts`); the body's three walks under
a fixed typing `τ`. -/
theorem gate_typedFacts {f c : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {n : Nat} {bsc : List (Lean.Name × MixedGateBinder)} {nc : Nat}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (τ : Lean.Expr → Nat)
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs body)
    (bnd : ChildBnd mref cref w)
    (hkid : ∀ mF : Std.HashMap Lean.Name Res, CacheInv mref cref mF → ∀ y : Res,
      mF.get? c = some y →
      InstLeafOk (ChildGN c mF) n y ∧ Tools.ShippingGateChildComb.ChildComb y.1 ∧
        y.1.name ≠ Sparkle.IR.ModuleName.ofDecl f ∧
        Tools.ShippingGatePorts.GateChildPorts c bsc nc y.1)
    (hwalk : ∀ envR : Lean.Environment,
      (∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body)) →
      ∀ mF : Std.HashMap Lean.Name Res,
      (∀ y : Res, mF.get? c = some y →
        InstLeafOk2 (ChildGN c mF) n y ∧ Tools.ShippingGatePorts.GateChildPorts c bsc nc y.1) →
      ∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 →
      ∀ (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId), ids.Nodup →
      ids.length = bs.length →
      DesW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
        (ChildGN c mF) (Sparkle.IR.ModuleName.ofDecl f)
        (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) true ∧
      NamW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
        (ChildGN c mF) (prepInsN bs ids cache (Sparkle.IR.ModuleName.ofDecl f))
        (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) ∧
      TypW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
        (ChildGN c mF) (prepPortsT bs ids cache (Sparkle.IR.ModuleName.ofDecl f)) τ
        (instFVars (ids.map Lean.Expr.fvar).toArray 0 body))
    (hpos : ∀ x ∈ bs, ∀ k, x.2 = MixedGateBinder.bits k → 0 < k) :
    Tools.ShippingHierTyped.hierTyped (childMap design.modules) b = true ∧
      designSideB3 design.modules b = true := by
  obtain ⟨M, Dd, envR, mF, hpost, hmods, hacc, hcache, hdes⟩ := gate_cone_runTyped hr gdef bnd
  have hleaf2 : ∀ y : Res, mF.get? c = some y →
      InstLeafOk2 (ChildGN c mF) n y ∧ Tools.ShippingGatePorts.GateChildPorts c bsc nc y.1 :=
    fun y hy => ⟨⟨(hkid mF hcache y hy).1, leaf_extra_of_combN (hkid mF hcache y hy).2.1⟩,
      (hkid mF hcache y hy).2.2.2⟩
  obtain ⟨fin, -, hT⟩ := hdes (ChildGN c mF) τ
    (fun L' D hD cache ids nd len => hwalk envR hacc mF hleaf2 L' D hD cache ids nd len) hpos
  have hms : ∀ x, ChildGN c mF x →
      Sparkle.IR.Machine.moduleByName design.modules x.name = some x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [hxy]
    exact designHasChild_of_final fin (childGN_eq hy) (hkid mF hcache y hy).2.2.1 hmods
  have hGF : ∀ x, ChildGN c mF x → GFactsT design.modules x := by
    intro x hx
    have hm := hms x hx
    obtain ⟨y, hy, hxy⟩ := hx
    subst hxy
    exact gFacts_of_ports hm (hkid mF hcache y hy).2.2.2
  obtain ⟨hb, hw, hi⟩ := post_fieldsN fin.mod hpost
  have ho := Tools.ShippingGateOutPort.post_outputs hpost
  obtain ⟨h1, h2, h3, h4⟩ := hT b hb hw hi ho design.modules hGF
  have hg := Tools.ShippingGateCombSide.hierGate_of_modOk fin.mod hpost
  refine ⟨h1, ?_⟩
  simp only [designSideB3, Bool.and_eq_true]
  exact ⟨⟨h2, h3⟩, Tools.ShippingPortsMatchShipped.portsMatchB_shipped hg h4⟩

end factsT

end Tools.ShippingGateParentRun

#print axioms Tools.ShippingGateParentRun.typed_checks
#print axioms Tools.ShippingGateParentRun.typed_final_of
#print axioms Tools.ShippingGateParentRun.gate_cone_runTyped
#print axioms Tools.ShippingGateParentRun.gate_typedFacts
