import Tools.ShippingTranslateSoundness

/-! # Synthesis success and semantic preservation at the ENTRY

`Tools.ShippingTranslateSoundness` proves the real translator
`translateExprToWire` sound on the fragment (inputs, `Signal.pure` BitVec
literals, canonical `+ - * &&& ||| ^^^` at one literal width) UNDER three
premises: the invariant `Inv` at the call, the width agreement `WidthsAgree`,
and a source meaning `Denotes`. This file discharges all three at the real
synthesis entry `synthesizeCombinationalCore`, for declarations of the form

    def f {dom : DomainConfig} (x₀ … : Signal dom (BitVec n)) : Signal dom (BitVec n) := fe

Main results (standard axioms only, audited in the test):

* `synthesizeCombinationalCore_reads` — a run of the real entry executes
  `getConstInfo declName` in the SAME contexts and state references
  (`RunsTo`) and then `synthesizeFromConst … ci` on the constant it read.
* `synthesizeCombinationalCore_sound` — for that same-run `ci`,
  `CertifiedOutcome ci M`.
* `fragmentDecl_sound` / `fragmentDecl_sound_signal` / `outcome_quote` — if
  `ci`'s value is `quoteDecl … fe`: distinct input ports, and for all input
  values the module's statements under its own declared widths drive `out`
  with `evalFE n vals fe` = `(denoteFE n sigs fe).val t`, the Lean meaning.
* `fragmentDecl_of_env` — the same from `EnvDefines … declName (quoteDecl …)`,
  the one statement about Lean's environment; applied to the real `fragA` in
  the test (`fragA_ir_correct`).

## How each premise disappeared

1. **`Inv`** is built from the entry's own construction: `CircuitM.init`
   (empty body, record, bindings), the binder walk `bindCertifiedInputs`
   (fresh wire per `Signal` binder, reader-scoped binding, input port), and the
   input valuation `rhoOf` (`bindCertifiedInputs_returns`, `rhoOf_some`).
2. **`WidthsAgree`** holds for `weOf M`, the widths READ OFF the returned
   module's wires, because wire names stay distinct: `WiresOk`, now carried by
   `Grows` through the translator (`widthsAgree_weOf`).
3. **`Denotes`** is derived, not assumed: the gate accepts `quoteDecl … fe`
   (`certifiedShape_quote`), the entry's instantiated body is the quotation
   over its fvars (`instFVars_quoteBody`), and it denotes `evalFE`
   (`denotes_quote`), which is the library meaning by `rfl` (`denoteFE_val`).

## What changed in the shipping entry to make this provable

The entry was a `partial def` inside the translator's `partial` block, so
nothing could be proved about it. It is now an ordinary definition
(`synthesizeCombinationalCoreWith`), and for the certified shape its front end
is pure (`certifiedShape?`, `instFVars`, fresh fvars checked distinct) instead
of `openRecordInputs` / `stripMemoizeWrappers` / `lambdaTelescope` /
`splitReturnLeaves`, which are `partial` or rest on `extern` primitives. The
binder walk, translator, leaf emission and module finish are shared with the
legacy path. A leaf's port name that is already a module name is now refused
(`emitLeaves`); `canonicalSignalBitVecWidth` tests the Bool instances by an
explicit list instead of a name suffix (same result; the suffix test does not
reduce in proofs).

## Remaining trust and scope (named, not hidden)

* `EnvDefines` is a hypothesis: the Core state sits behind an opaque
  `ST.Ref`, so "the run's environment defines `f := v`" cannot be derived. The
  constant is proved to be the one the run read; `#def_decl_value` takes `v`
  from the same `getConstInfo` at elaboration time.
* Post-processing is covered separately in `Tools/ShippingPostSoundness.lean`
  (`synthesizeCombinational_fragment`).
* Declarations outside the certified shape take the legacy front end and are
  not covered; the entry theorem says nothing about them (`CertifiedOutcome`
  is vacuous there). The gate also accepts the canonical shifts `<<< >>>`
  (the translator core lowers them), but `Denotes` gives meaning only to
  `+ - * &&& ||| ^^^`, so for a shift `Preserves` holds vacuously: shifts are
  on the certified front end but NOT proved.
* IR semantics is `evalAssigns` (one combinational cycle); Verilog printing
  and Verilog semantics are separate. -/

namespace Tools.ShippingEntrySoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.IR.Type Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingTranslateSoundness


def MReturns {α : Type} (m : MetaM α) (a : α) : Prop :=
  ∃ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld),
    m mctx mref cctx cref w = EST.Out.ok a w'

theorem MReturns.bind {α β : Type} {m : MetaM α} {f : α → MetaM β} {b : β}
    (h : MReturns (m >>= f) b) : ∃ a, MReturns m a ∧ MReturns (f a) b := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (m mctx mref cctx cref) fun a => f a mctx mref cctx cref) w = _ at hrun
  unfold EST.bind at hrun
  split at hrun
  · rename_i a w1 heq
    exact ⟨a, ⟨mctx, mref, cctx, cref, w, w1, heq⟩, ⟨mctx, mref, cctx, cref, w1, w', hrun⟩⟩
  · cases hrun

theorem MReturns.pure {α : Type} {a b : α} (h : MReturns (Pure.pure a : MetaM α) b) : b = a := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.ok a w = _ at hrun
  cases hrun; rfl

theorem MReturns.throw {α : Type} {e : Exception} {a : α}
    (h : MReturns (throw e : MetaM α) a) : False := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change EST.Out.error e w = _ at hrun
  cases hrun

theorem MReturns.run {α : Type} {c : CompilerM α} {ctx : CompilerState} {s : CircuitState}
    {p : α × CircuitState} (h : MReturns ((c.run ctx).run s) p) : Returns c ctx s p.1 p.2 := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  exact ⟨mctx, mref, cctx, cref, w, w', hrun⟩

theorem fv (a b : FVarId) : (a == b) = true ↔ a = b := by
  cases a; cases b
  show instBEqFVarId.beq _ _ = true ↔ _
  simp [instBEqFVarId.beq]

/-- try/finally: a successful run is a successful run of the body. -/
theorem MReturns.try_finally {α β : Type} {x : MetaM α} {fin : MetaM β} {a : α}
    (h : MReturns (_root_.tryFinally x fin) a) : MReturns x a := by
  obtain ⟨mctx, mref, cctx, cref, w, w', hrun⟩ := h
  change (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w = _
    at hrun
  unfold EST.bind at hrun
  split at hrun
  · rename_i p w1 heq
    simp only [MonadFinally.tryFinally'] at heq
    split at heq
    · rename_i v w2 hx
      split at heq
      · cases heq
        simp only [EST.pure] at hrun
        cases hrun
        exact ⟨mctx, mref, cctx, cref, w, w2, hx⟩
      · cases heq
    · split at heq <;> cases heq
  · cases hrun


/-! ## Builder operations of the entry -/

theorem addInput_state (name : String) (ty : HWType) (s : CircuitState) :
    (CircuitM.addInput name ty s).2 =
      { s with usedNames := s.usedNames.insert name,
               module := s.module.addInput { name := name, ty := ty } } := rfl

theorem addOutput_state (name : String) (ty : HWType) (s : CircuitState) :
    (CircuitM.addOutput name ty s).2 =
      { s with usedNames := s.usedNames.insert name,
               module := s.module.addOutput { name := name, ty := ty } } := rfl

theorem addInput_returns {name : String} {ty : HWType} {ctx : CompilerState}
    {s s' : CircuitState} {u : Unit} (h : Returns (CompilerM.addInput name ty) ctx s u s') :
    s' = (CircuitM.addInput name ty s).2 := by
  unfold CompilerM.addInput at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  subst hcs hs1
  split at k1
  rename_i cs' hmk
  obtain ⟨u1, s2, hset, k2⟩ := Returns.bind k1
  have hs2 : s2 = cs' := Returns.set hset
  have goal : s' = s2 := by
    split at k2
    · exact Returns.liftMetaM k2
    · exact (Returns.pure k2).2
  rw [hmk]; exact goal.trans hs2

theorem addOutput_returns {name : String} {ty : HWType} {ctx : CompilerState}
    {s s' : CircuitState} {u : Unit} (h : Returns (CompilerM.addOutput name ty) ctx s u s') :
    s' = (CircuitM.addOutput name ty s).2 := by
  unfold CompilerM.addOutput at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  subst hcs hs1
  split at k1
  rename_i cs' hmk
  obtain ⟨u1, s2, hset, k2⟩ := Returns.bind k1
  have hs2 : s2 = cs' := Returns.set hset
  have goal : s' = s2 := by
    split at k2
    · exact Returns.liftMetaM k2
    · exact (Returns.pure k2).2
  rw [hmk]; exact goal.trans hs2

theorem withVarMapping_returns {α : Type} {id : FVarId} {w : String} {k : CompilerM α}
    {ctx : CompilerState} {s s' : CircuitState} {a : α}
    (h : Returns (CompilerM.withVarMapping id w k) ctx s a s') :
    Returns k { ctx with varMap := (id, w) :: ctx.varMap } s a s' := by
  unfold CompilerM.withVarMapping at h
  obtain ⟨c, s1, hread, k1⟩ := Returns.bind h
  obtain ⟨hc, hs1⟩ := Returns.read hread
  subst hc hs1
  obtain ⟨mctx, mref, cctx, cref, w0, w', hrun⟩ := k1
  exact ⟨mctx, mref, cctx, cref, w0, w', hrun⟩

/-- An oracle-only `if` (a MetaM effect or nothing) leaves the builder state. -/
theorem Returns.ite_lift {c : Bool} {x : MetaM Unit} {ctx : CompilerState}
    {s s' : CircuitState} {u : Unit}
    (h : Returns (if c = true then CompilerM.liftMetaM x else pure ()) ctx s u s') : s' = s := by
  split at h
  · exact Returns.liftMetaM h
  · exact (Returns.pure h).2

/-! ## The binder walk of the certified front end -/

/-- `bindInputPort`: a fresh `n`-bit wire, declared as an input, bound in the
reader context of the continuation. -/
theorem bindInputPort_returns {α : Type} {id : FVarId} {nm : String} {ty : HWType}
    {k : CompilerM α} {ctx : CompilerState} {s s' : CircuitState} {a : α}
    (h : Returns (bindInputPort id nm ty k) ctx s a s') :
    let w := (CircuitM.makeWire nm ty true s).1
    let s1 := (CircuitM.addInput w ty (CircuitM.makeWire nm ty true s).2).2
    Returns k { ctx with varMap := (id, w) :: ctx.varMap } s1 a s' := by
  unfold bindInputPort at h
  obtain ⟨w, sA, hmk, k1⟩ := Returns.bind h
  obtain ⟨hw, hsA⟩ := makeWire_returns hmk
  obtain ⟨u, sB, hin, k2⟩ := Returns.bind k1
  have hsB := addInput_returns hin
  have k3 := withVarMapping_returns k2
  rw [hsB, hsA, hw] at k3
  exact k3


theorem Grows.refl (s : CircuitState) : Grows s s :=
  ⟨fun _ h => h, fun _ h => h, fun h => h, fun _ h => h, DeclFrame.refl s⟩

theorem Grows.trans {a b c : CircuitState} (h1 : Grows a b) (h2 : Grows b c) : Grows a c :=
  ⟨fun z hz => h2.1 z (h1.1 z hz), fun p hp => h2.2.1 p (h1.2.1 p hp),
   fun h => h2.2.2.1 (h1.2.2.1 h), fun p hp => h2.2.2.2.1 p (h1.2.2.2.1 p hp),
   h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem WiresOk.mono_used {s t : CircuitState} (hw : t.module.wires = s.module.wires)
    (hu : ∀ x, s.usedNames.contains x = true → t.usedNames.contains x = true)
    (h : WiresOk s) : WiresOk t := by
  obtain ⟨hnd, hin⟩ := h
  exact ⟨by rw [hw]; exact hnd, fun p hp => hu _ (hin p (by rw [← hw]; exact hp))⟩

theorem fvarId_beq_iff (a b : FVarId) : (a == b) = true ↔ a = b := by
  cases a; cases b
  show instBEqFVarId.beq _ _ = true ↔ _
  simp [instBEqFVarId.beq]

theorem lookup_cons_self (id : FVarId) (w : String) (l : List (FVarId × String)) :
    ((id, w) :: l).lookup id = some w := by
  simp [List.lookup_cons, (fvarId_beq_iff id id).mpr rfl]

theorem lookup_cons_ne {id id' : FVarId} (w : String) (l : List (FVarId × String))
    (hne : id' ≠ id) : ((id, w) :: l).lookup id' = l.lookup id' := by
  have : (id' == id) = false := by
    cases h : (id' == id) with
    | false => rfl
    | true => exact absurd ((fvarId_beq_iff _ _).mp h) hne
  simp [List.lookup_cons, this]

/-- The certified binder walk: every `Signal` binder gets its own fresh input
wire, found by the real `lookupVar` path (the reader context) in the
continuation; nothing else about the state changes. -/
theorem bindCertifiedInputs_returns {α : Type} {k : CompilerM α} :
    ∀ (L : List ((Name × GateBinder) × FVarId)) {ctx : CompilerState} {s s' : CircuitState}
      {a : α}, (L.map Prod.snd).Nodup →
    Returns (bindCertifiedInputs k L) ctx s a s' →
    ∃ (ctx' : CompilerState) (s1 : CircuitState) (ws : List (Option String)),
      Returns k ctx' s1 a s' ∧ ws.length = L.length ∧
      (∀ (j : Nat) (nm : Name) (n : Nat) (id : FVarId),
        L[j]? = some ((nm, GateBinder.signal n), id) →
        ∃ w, ws[j]? = some (some w) ∧ ctx'.varMap.lookup id = some w ∧
          ({ name := w, ty := .bitVector n } : Port) ∈ s1.module.wires ∧
          ({ name := w, ty := .bitVector n } : Port) ∈ s1.module.inputs) ∧
      (∀ (j : Nat) (w : String), ws[j]? = some (some w) → s.usedNames.contains w = false) ∧
      (∀ (j j' : Nat) (w : String), ws[j]? = some (some w) → ws[j']? = some (some w) → j = j') ∧
      (∀ id, id ∉ L.map Prod.snd → ctx'.varMap.lookup id = ctx.varMap.lookup id) ∧
      Grows s s1 ∧ s1.module.body = s.module.body ∧ s1.translateRecord = s.translateRecord ∧
      s1.sourceBindings = s.sourceBindings ∧ s1.module.outputs = s.module.outputs ∧
      (∀ p ∈ s1.module.inputs, p ∈ s.module.inputs ∨
        ∃ (j : Nat) (nm : Name) (n : Nat) (id : FVarId) (w : String),
          L[j]? = some ((nm, GateBinder.signal n), id) ∧ ws[j]? = some (some w) ∧
          p = { name := w, ty := .bitVector n })
  | [], ctx, s, s', a, _, h =>
    ⟨ctx, s, [], h, rfl, fun j _ _ _ hj => by simp at hj, fun j w hj => by simp at hj,
     fun j _ w hj => by simp at hj, fun _ _ => rfl, Grows.refl s, rfl, rfl, rfl, rfl,
     fun p hp => Or.inl hp⟩
  | ((nm, .domain), id) :: rest, ctx, s, s', a, hnd, h => by
    have hnd' : (rest.map Prod.snd).Nodup := (List.nodup_cons.mp hnd).2
    obtain ⟨ctx', s1, ws, hk, hlen, hsig, hfr, hdist, hlook, hg, hb, hr, hsb, hout, hinp⟩ :=
      bindCertifiedInputs_returns rest hnd' h
    refine ⟨ctx', s1, none :: ws, hk, by simp [hlen], ?_, ?_, ?_, ?_, hg, hb, hr, hsb, hout, ?_⟩
    · intro j nm' n id' hj
      cases j with
      | zero => simp at hj
      | succ j =>
        obtain ⟨w, hw, rest'⟩ := hsig j nm' n id' (by simpa using hj)
        exact ⟨w, by simpa using hw, rest'⟩
    · intro j w hj
      cases j with
      | zero => simp at hj
      | succ j => exact hfr j w (by simpa using hj)
    · intro j j' w hj hj'
      cases j with
      | zero => simp at hj
      | succ j =>
        cases j' with
        | zero => simp at hj'
        | succ j' => rw [hdist j j' w (by simpa using hj) (by simpa using hj')]
    · intro id' hid
      exact hlook id' (fun hm => hid (List.mem_cons_of_mem _ hm))
    · intro p hp
      rcases hinp p hp with h | ⟨j, nm', n', id', w, hj, hw, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨j + 1, nm', n', id', w, by simpa using hj, by simpa using hw, rfl⟩
  | ((nm, .signal n), id) :: rest, ctx, s, s', a, hnd, h => by
    obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
    have h1 := bindInputPort_returns (h : Returns (bindInputPort id nm.toString (.bitVector n)
      (bindCertifiedInputs k rest)) ctx s a s')
    dsimp only at h1
    obtain ⟨ctx', s1, ws, hk, hlen, hsig, hfr, hdist, hlook, hg, hb, hr, hsb, hout, hinp⟩ :=
      bindCertifiedInputs_returns rest hnd' h1
    obtain ⟨hfresh, hused, hbody, hwires⟩ :=
      CircuitM.makeWire_spec nm.toString (.bitVector n) true s
    have hsbA := CircuitM.makeWire_sourceBindings nm.toString (.bitVector n) true s
    have hrecA := CircuitM.makeWire_translateRecord nm.toString (.bitVector n) true s
    have hinA := makeWire_inputs nm.toString (.bitVector n) true s
    have houtA := makeWire_outputs nm.toString (.bitVector n) true s
    generalize hw0 : (CircuitM.makeWire nm.toString (.bitVector n) true s).1 = w0 at *
    generalize hsA : (CircuitM.makeWire nm.toString (.bitVector n) true s).2 = sA at *
    -- the state after the head binder
    have hNu : (CircuitM.addInput w0 (.bitVector n) sA).2.usedNames = sA.usedNames.insert w0 := by
      rw [addInput_state]
    have hNw : (CircuitM.addInput w0 (.bitVector n) sA).2.module.wires = sA.module.wires := by
      rw [addInput_state]; rfl
    have hNi : (CircuitM.addInput w0 (.bitVector n) sA).2.module.inputs =
        { name := w0, ty := .bitVector n } :: sA.module.inputs := by
      rw [addInput_state]; rfl
    have hNb : (CircuitM.addInput w0 (.bitVector n) sA).2.module.body = sA.module.body := by
      rw [addInput_state]; rfl
    have hNr : (CircuitM.addInput w0 (.bitVector n) sA).2.translateRecord = sA.translateRecord := by
      rw [addInput_state]
    have hNs : (CircuitM.addInput w0 (.bitVector n) sA).2.sourceBindings = sA.sourceBindings := by
      rw [addInput_state]
    have huN : ∀ x, s.usedNames.contains x = true →
        (CircuitM.addInput w0 (.bitVector n) sA).2.usedNames.contains x = true := by
      intro x hx; rw [hNu, hused]; simp [Std.HashSet.contains_insert, hx]
    have hw0N : (CircuitM.addInput w0 (.bitVector n) sA).2.usedNames.contains w0 = true := by
      rw [hNu]; simp [Std.HashSet.contains_insert]
    have gN : Grows s (CircuitM.addInput w0 (.bitVector n) sA).2 := by
      refine ⟨huN, fun p hp => ?_, fun hok => ?_, fun p hp => ?_, ?_⟩
      · rw [hNw, hwires]; exact List.mem_cons_of_mem _ hp
      · exact WiresOk.mono_used hNw
          (fun x hx => by rw [hNu]; simp [Std.HashSet.contains_insert, hx])
          (WiresOk.fresh hfresh hused hwires hok)
      · rw [hNi, hinA]; exact List.mem_cons_of_mem _ hp
      · have hf : DeclFrame s sA := by rw [← hsA]; exact DeclFrame.makeWire _ _ _ _
        rw [addInput_state]
        exact ⟨hf.parameters, hf.primitive, hf.wireTypes⟩
    refine ⟨ctx', s1, some w0 :: ws, hk, by simp [hlen], ?_, ?_, ?_, ?_, Grows.trans gN hg,
      by rw [hb, hNb]; exact hbody, by rw [hr, hNr]; exact hrecA, by rw [hsb, hNs]; exact hsbA,
      by rw [hout, addInput_state]; exact houtA, ?_⟩
    · intro j nm' n' id' hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq,
          GateBinder.signal.injEq] at hj
        obtain ⟨⟨-, hn⟩, hid⟩ := hj
        rw [← hn, ← hid]
        refine ⟨w0, rfl, ?_, ?_, ?_⟩
        · rw [hlook id hnotin]; exact lookup_cons_self id w0 ctx.varMap
        · exact hg.2.1 _ (by rw [hNw, hwires]; simp)
        · exact hg.2.2.2.1 _ (by rw [hNi]; simp)
      | succ j =>
        obtain ⟨w, hw, rest'⟩ := hsig j nm' n' id' (by simpa using hj)
        exact ⟨w, by simpa using hw, rest'⟩
    · intro j w hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj; exact hfresh
      | succ j =>
        have := hfr j w (by simpa using hj)
        cases hc : s.usedNames.contains w with
        | false => rfl
        | true => rw [huN w hc] at this; cases this
    · intro j j' w hj hj'
      have head : ∀ j : Nat, ws[j]? = some (some w0) → False := by
        intro j hj
        have := hfr j w0 hj
        rw [hw0N] at this; cases this
      cases j with
      | zero =>
        cases j' with
        | zero => rfl
        | succ j' =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj; exact (head j' (by simpa using hj')).elim
      | succ j =>
        cases j' with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj'
          subst hj'; exact (head j (by simpa using hj)).elim
        | succ j' => rw [hdist j j' w (by simpa using hj) (by simpa using hj')]
    · intro id' hid
      have hne : id' ≠ id := fun he => hid (by rw [he]; exact List.mem_cons_self)
      rw [hlook id' (fun hm => hid (List.mem_cons_of_mem _ hm))]
      exact lookup_cons_ne w0 ctx.varMap hne
    · intro p hp
      rcases hinp p hp with h | ⟨j, nm', n', id', w, hj, hw, rfl⟩
      · rw [hNi, hinA] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨0, nm, n, id, w0, by simp, by simp, rfl⟩
        · exact Or.inl h
      · exact Or.inr ⟨j + 1, nm', n', id', w, by simpa using hj, by simpa using hw, rfl⟩


/-- Peel one oracle step (`CompilerM.liftMetaM _`) off a successful run. -/
macro "peel_lift" h:ident : tactic =>
  `(tactic| (obtain ⟨_, _, hl, $h:ident⟩ := Returns.bind $h:ident; rw [Returns.liftMetaM hl] at $h:ident))

theorem Returns.lift_or_skip {β : Type} {c : Bool} {x : MetaM Unit} {K : Unit → CompilerM β}
    {ctx : CompilerState} {s s' : CircuitState} {r : β}
    (h : Returns (if c = true then (CompilerM.liftMetaM x >>= K) else K ()) ctx s r s') :
    Returns (K ()) ctx s r s' := by
  split at h
  · obtain ⟨u, s1, hl, k⟩ := Returns.bind h
    obtain rfl := Returns.liftMetaM hl
    exact k
  · exact h

theorem Returns.guard_throw {β : Type} {c : Bool} {ex : Exception} {K : Unit → CompilerM β}
    {ctx : CompilerState} {s s' : CircuitState} {r : β}
    (h : Returns (if c = true then (throw ex >>= K) else K ()) ctx s r s') :
    c = false ∧ Returns (K ()) ctx s r s' := by
  split at h
  · obtain ⟨u, s1, ht, _⟩ := Returns.bind h
    exact (Returns.throw ht).elim
  · rename_i hc; exact ⟨by simpa using hc, h⟩

/-- The type the leaf loop gives an output port driven by wire `w`. -/
def leafOutputType (s : CircuitState) (w : String) : HWType :=
  match s.module.wires.find? (fun p => p.name == w) with
  | some decl => decl.ty
  | none =>
    match s.module.inputs.find? (fun p => p.name == w) with
    | some inputPort => inputPort.ty
    | none => .bitVector 8

/-- One return leaf: the translator's run, the port-name check, the port and
its `assign`. -/
theorem emitLeaves_single {tr : TranslateFn} {cacheRef : IO.Ref (Lean.ExprStructMap String)}
    {logProf : String → IO Unit} {port : String} {e : Lean.Expr}
    {ctx : CompilerState} {s s' : CircuitState} {r : String}
    (h : Returns (emitLeaves tr cacheRef logProf [(port, e)] none 0) ctx s r s') :
    ∃ w s1 ty, Returns (tr e port false true) ctx s w s1 ∧ s1.usedNames.contains port = false ∧
      s' = (CircuitM.emitAssign port (.ref w) (CircuitM.addOutput port ty s1).2).2 ∧
      ty = leafOutputType s1 w := by
  unfold emitLeaves at h
  peel_lift h; peel_lift h; peel_lift h; peel_lift h
  obtain ⟨w, s1, htr, h⟩ := Returns.bind h
  peel_lift h; peel_lift h; peel_lift h; peel_lift h
  try dsimp only at h
  have h1 := Returns.lift_or_skip h
  clear h
  obtain ⟨cs, s3, hget, h2⟩ := Returns.bind h1
  obtain ⟨hcs, hs3⟩ := Returns.get hget
  obtain ⟨hfresh, h3⟩ := Returns.guard_throw h2
  obtain ⟨_, s5, hout, h4⟩ := Returns.bind h3
  have hs5 := addOutput_returns hout
  obtain ⟨_, s6, hem, h5⟩ := Returns.bind h4
  have hs6 := emitAssign_returns hem
  unfold emitLeaves at h5
  obtain ⟨-, hs'⟩ := Returns.pure h5
  rw [hcs] at hfresh hs5
  exact ⟨w, _, leafOutputType _ w, htr, hfresh, by rw [hs', hs6, hs5, hs3]; rfl, rfl⟩


/-! ## Finishing the module -/

theorem addClockReset_facts (m : Sparkle.IR.AST.Module) :
    (addClockResetIfSequential m).body = m.body ∧ (addClockResetIfSequential m).wires = m.wires ∧
    (addClockResetIfSequential m).outputs = m.outputs ∧
    (∀ p ∈ m.inputs, p ∈ (addClockResetIfSequential m).inputs) := by
  unfold addClockResetIfSequential
  dsimp only
  split
  · refine ⟨?_, ?_, ?_, ?_⟩
    · split <;> split <;> rfl
    · split <;> split <;> rfl
    · split <;> split <;> rfl
    · intro p hp
      split <;> split <;> simp [Module.addInput, hp]
  · exact ⟨rfl, rfl, rfl, fun _ h => h⟩

/-- A body without registers or memories gets no clock/reset ports. -/
theorem addClockReset_assigns (m : Sparkle.IR.AST.Module)
    (h : ∀ st ∈ m.body, ∃ l r, st = .assign l r) : addClockResetIfSequential m = m := by
  unfold addClockResetIfSequential
  dsimp only
  split
  · rename_i hc
    obtain ⟨st, hst, hf⟩ := List.any_eq_true.mp hc
    obtain ⟨l, r, rfl⟩ := h st hst
    simp at hf
  · rfl

theorem addClockReset_metadata (m : Sparkle.IR.AST.Module) :
    (addClockResetIfSequential m).parameters = m.parameters ∧
    (addClockResetIfSequential m).isPrimitive = m.isPrimitive := by
  unfold addClockResetIfSequential
  dsimp only
  split
  · split <;> split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem finishSynth_returns {declName : Name} {st : CircuitState} {M : Sparkle.IR.AST.Module} {D : Design}
    (h : MReturns (finishSynth declName [] false st) (M, D)) :
    M = (addClockResetIfSequential st.module).finalize ∧ D = st.design := by
  unfold finishSynth at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  have := MReturns.pure h
  simp only [Prod.mk.injEq] at this
  exact this

/-! ## The width environment of the final module -/

/-- Widths READ OFF a module's declared wires (0 for an undeclared name). -/
def weOf (M : Sparkle.IR.AST.Module) : WEnv := fun name =>
  match M.wires.find? (fun p => p.name == name) with
  | some { ty := .bitVector k, .. } => k
  | _ => 0

theorem nodup_reverse {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup :=
  List.pairwise_reverse.mpr (h.imp fun hne heq => hne heq.symm)

theorem find?_of_nodup {l : List Port} (hnd : (l.map (·.name)).Nodup) {p : Port} (hp : p ∈ l) :
    l.find? (fun q => q.name == p.name) = some p := by
  induction l with
  | nil => cases hp
  | cons q rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp
    · have hne : q.name ≠ p.name := by
        intro he; exact hnd.1 (he ▸ List.mem_map_of_mem hp')
      simp [hne, ih hnd.2 hp']

/-- Item 2: when the final module's wires are those of a state with distinct
wire names, `weOf` agrees with every declared width of that state. -/
theorem widthsAgree_weOf {M : Sparkle.IR.AST.Module} {s : CircuitState} (hok : WiresOk s)
    (hw : M.wires = s.module.wires.reverse) : WidthsAgree (weOf M) s := by
  intro p hp k hk
  have hnd : (M.wires.map (·.name)).Nodup := by
    rw [hw, List.map_reverse]; exact nodup_reverse hok.1
  have hpM : p ∈ M.wires := by rw [hw, List.mem_reverse]; exact hp
  unfold weOf
  rw [find?_of_nodup hnd hpM]
  obtain ⟨nm, ty⟩ := p
  simp only at hk
  subst hk
  rfl


/-! ## Item 1: the input valuation, and the invariant at the first leaf -/

/-- The source valuation for binder values `vals` (binder `j` has value
`vals j`, at the width its `Signal` type declares). -/
def rhoOf : List ((Name × GateBinder) × FVarId) → (Nat → Nat) → Valuation
  | [], _ => fun _ => none
  | ((_, k), id) :: rest, vals => fun id' =>
    if id' = id then
      match k with
      | .signal n => some ⟨n, BitVec.ofNat n (vals 0)⟩
      | .domain => none
    else rhoOf rest (fun i => vals (i + 1)) id'

theorem rhoOf_some : ∀ (L : List ((Name × GateBinder) × FVarId)) (vals : Nat → Nat)
    (id : FVarId) (n : Nat) (x : BitVec n), rhoOf L vals id = some ⟨n, x⟩ →
    ∃ j nm, L[j]? = some ((nm, .signal n), id) ∧ x = BitVec.ofNat n (vals j)
  | [], _, _, _, _, h => by simp [rhoOf] at h
  | ((nm, k), id0) :: rest, vals, id, n, x, h => by
    unfold rhoOf at h
    split at h
    · rename_i heq
      subst heq
      cases k with
      | domain => cases h
      | signal n0 =>
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, hx⟩ := h
        exact ⟨0, nm, by simp, (eq_of_heq hx).symm⟩
    · obtain ⟨j, nm', hj, hx⟩ := rhoOf_some rest _ id n x h
      exact ⟨j + 1, nm', by simpa using hj, hx⟩

/-- The translator's growth fact at the real entry (the `grows` half of the
fuel induction). -/
theorem translateExprToWire_grows {ctx : CompilerState} {ρ : Valuation} {e : Lean.Expr}
    {hint : String} {named : Bool} {n : Nat} {x : BitVec n} {s0 : CircuitState} {w : String}
    {s1 : CircuitState} (hden : Denotes ρ e n x)
    (hrun : Returns (translateExprToWire e hint false named) ctx s0 w s1)
    (hbl : BoundLookup ctx ρ s0) :
    Grows s0 s1 ∧ s1.sourceBindings = s0.sourceBindings ∧ RecordFresh s0 s1 ∧ Emits n s0 s1 :=
  (translateFuelFix_spec (step := translateStep) (we := fun _ => 0) (mems := fun _ _ => 0)
    (initial := fun _ => 0) (fun _ ih => translateStepWith_spec ih)
    translateFuelLimit).grows e hint named n x s0 w s1 hden hrun hbl

/-- Facts about a module the entry returned, READ OFF its construction, that
the post-processing proofs need (`Tools/ShippingPostSoundness.lean`). -/
def DeclReady (M : Sparkle.IR.AST.Module) : Prop :=
  M.parameters = [] ∧ M.isPrimitive = false ∧
  ∀ p ∈ M.wires, ∃ k, p.ty = .bitVector k

def PostReady (M : Sparkle.IR.AST.Module) (n : Nat) : Prop :=
  (M.wires.map (·.name)).Nodup ∧
  "out" ∉ M.wires.map (·.name) ∧
  (∀ st ∈ M.body, ∃ l r, st = .assign l r ∧
    ((ShapedRhs r ∧ ({ name := l, ty := .bitVector n } : Port) ∈ M.wires) ∨
     (l = "out" ∧ ∃ w, r = .ref w))) ∧
  (0 < n → M.outputs = [{ name := "out", ty := .bitVector n }]) ∧ DeclReady M ∧
  (∀ l r, Stmt.assign l r ∈ M.body → SizedExpr (weOf M) r n)

/-- What synthesis success guarantees for a certified-shape declaration:
distinct input ports for the `Signal` binders, and for ALL binder values, the
IR (the module's own statements, under the widths it declares) drives `out`
with the value the source has at those binder values. -/
def Preserves (bs : List (Name × GateBinder)) (body : Lean.Expr)
    (M : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ port : Nat → Option String,
    (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
    (∀ j nm n, bs[j]? = some (nm, GateBinder.signal n) → ∃ w, port j = some w) ∧
    ∀ (vals : Nat → Nat) (mems : MEnv) (initial : Env),
      (∀ j nm n w, bs[j]? = some (nm, GateBinder.signal n) → port j = some w →
        initial w = (BitVec.ofNat n (vals j)).toNat) →
      ∀ n (x : BitVec n),
        Denotes (rhoOf (bs.zip ids) vals) (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) n x →
        ∃ env, evalAssigns (weOf M) mems M.body initial = some env ∧ env "out" = x.toNat ∧
          "out" ∈ M.outputs.map (·.name) ∧
          (∀ j nm n' w, bs[j]? = some (nm, GateBinder.signal n') → port j = some w →
            ({ name := w, ty := .bitVector n' } : Port) ∈ M.inputs) ∧
          PostReady M n ∧
          (∀ p ∈ M.inputs, ∃ j nm n', bs[j]? = some (nm, GateBinder.signal n') ∧
            port j = some p.name ∧ p.ty = .bitVector n' ∧
            ({ name := p.name, ty := .bitVector n' } : Port) ∈ M.wires)

theorem synthesizeCertified_sound {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × GateBinder)} {body : Lean.Expr} {M : Sparkle.IR.AST.Module} {D : Design}
    (h : MReturns (synthesizeCertified (fun e h t n => translateExprToWire e h t n) logProf
      declName bs body) (M, D)) :
    Preserves bs body M := by
  unfold synthesizeCertified at h
  obtain ⟨ids, -, h1⟩ := MReturns.bind h
  split at h1
  rotate_left
  · exact (MReturns.throw h1).elim
  rename_i hids
  dsimp only at h1
  obtain ⟨cacheRef, -, h2⟩ := MReturns.bind h1
  obtain ⟨⟨u, st⟩, hp, h3⟩ := MReturns.bind h2
  dsimp only at h3
  obtain ⟨hM, -⟩ := finishSynth_returns h3
  have hr := MReturns.run hp
  dsimp only at hr
  have hnd : ((bs.zip ids).map Prod.snd).Nodup := by
    rw [List.map_snd_zip (by rw [hids.2]; exact Nat.le_refl _)]; exact hids.1
  obtain ⟨ctx', s1, ws, hk, hlen, hsig, hfr, hdist, hlook, hg, hb, hrec, hsb, hout1, hinp1⟩ :=
    bindCertifiedInputs_returns _ hnd hr
  obtain ⟨w, s2, ty, htr, hfresh, hst, hty⟩ := emitLeaves_single hk
  -- the module the entry returns
  obtain ⟨cb, cw, co, ci⟩ := addClockReset_facts st.module
  have hst_w : st.module.wires = s2.module.wires := by rw [hst]; rfl
  have hst_b : st.module.body = .assign "out" (.ref w) :: s2.module.body := by rw [hst]; rfl
  have hst_o : st.module.outputs = { name := "out", ty := ty } :: s2.module.outputs := by
    rw [hst]; rfl
  have hst_i : st.module.inputs = s2.module.inputs := by rw [hst]; rfl
  have hMw : M.wires = s2.module.wires.reverse := by rw [hM]; simp [Module.finalize, cw, hst_w]
  have hMb : M.body = st.module.finalize.body := by rw [hM]; simp [Module.finalize, cb]
  have hMi : ∀ p ∈ s2.module.inputs, p ∈ M.inputs := by
    intro p hp; rw [hM]; simp only [Module.finalize, List.mem_reverse]; exact ci p (hst_i ▸ hp)
  have hMo : "out" ∈ M.outputs.map (·.name) := by rw [hM]; simp [Module.finalize, co, hst_o]
  -- the state the first leaf starts in
  have hs1b : s1.module.body = [] := by rw [hb]; rfl
  have hs1r : s1.translateRecord = {} := by rw [hrec]; rfl
  have hs1s : s1.sourceBindings = {} := by rw [hsb]; rfl
  have hok1 : WiresOk s1 := hg.2.2.1 ⟨by simp [CircuitM.init, Module.empty], by
    simp [CircuitM.init, Module.empty]⟩
  let port : Nat → Option String := fun j => (ws[j]?).join
  have hzip : ∀ (j : Nat) (nm : Name) (n : Nat), bs[j]? = some (nm, GateBinder.signal n) →
      ∃ id, (bs.zip ids)[j]? = some ((nm, GateBinder.signal n), id) := by
    intro j nm n hj
    have hlt : j < ids.length := by
      rw [hids.2]; exact (List.getElem?_eq_some_iff.mp hj).1
    exact ⟨ids[j], List.getElem?_zip_eq_some.mpr ⟨hj, by simp [hlt]⟩⟩
  have hsig' : ∀ (j : Nat) (nm : Name) (n : Nat) (id : FVarId), (bs.zip ids)[j]? = some ((nm, GateBinder.signal n), id) →
      ∃ w, port j = some w ∧ ctx'.varMap.lookup id = some w ∧
        ({ name := w, ty := .bitVector n } : Port) ∈ s1.module.wires ∧
        ({ name := w, ty := .bitVector n } : Port) ∈ s1.module.inputs := by
    intro j nm n id hj
    obtain ⟨w, hw, rest⟩ := hsig j nm n id hj
    exact ⟨w, by simp [port, hw], rest⟩
  have hjoin : ∀ (j : Nat) (w' : String), port j = some w' → ws[j]? = some (some w') := by
    intro j w' hj
    simp only [port] at hj
    cases hc : ws[j]? with
    | none => rw [hc] at hj; cases hj
    | some o => rw [hc] at hj; simp at hj; rw [hj]
  refine ⟨ids, hids.1, hids.2, port, ?_, ?_, ?_⟩
  · intro j j' w' hj hj'
    exact hdist j j' w' (hjoin j w' hj) (hjoin j' w' hj')
  · intro j nm n hj
    obtain ⟨id, hz⟩ := hzip j nm n hj
    obtain ⟨w', hw', -⟩ := hsig' j nm n id hz
    exact ⟨w', hw'⟩
  · intro vals mems initial hinit n x hden
    have hbl : BoundLookup ctx' (rhoOf (bs.zip ids) vals) s1 := by
      intro id n' x' hx
      obtain ⟨j, nm, hj, -⟩ := rhoOf_some _ vals id n' x' hx
      obtain ⟨w', -, hl, hwire, -⟩ := hsig' j nm n' id hj
      exact ⟨w', Tools.ShippingBindingsSoundness.visible_local ctx' _ id w' hl, hok1.2 _ hwire⟩
    obtain ⟨⟨gu, gw, gk, gi, gf⟩, -, -, hemit⟩ := translateExprToWire_grows hden htr hbl
    have hok2 : WiresOk s2 := gk hok1
    have hwid : WidthsAgree (weOf M) s2 := widthsAgree_weOf hok2 hMw
    have hinv : Inv ctx' (rhoOf (bs.zip ids) vals) (weOf M) mems initial s1 initial := by
      refine ⟨?_, hbl, ?_, ?_, ?_⟩
      · show evalAssigns _ _ s1.module.finalize.body initial = some initial
        simp [Module.finalize, hs1b, evalAssigns]
      · intro id n' x' w' hx hv
        obtain ⟨j, nm, hj, hxv⟩ := rhoOf_some _ vals id n' x' hx
        obtain ⟨w'', hp, hl, hwire, -⟩ := hsig' j nm n' id hj
        have hvis := Tools.ShippingBindingsSoundness.visible_local ctx' s1.sourceBindings id w'' hl
        rw [hvis] at hv
        have hww : w'' = w' := Option.some.inj hv
        subst hww
        have hbj : bs[j]? = some (nm, GateBinder.signal n') := (List.getElem?_zip_eq_some.mp hj).1
        refine ⟨?_, hwid _ (gw _ hwire) n' rfl⟩
        rw [hinit j nm n' w'' hbj hp, hxv]
      · intro w' e' he
        rw [hs1r] at he; simp at he
      · rw [hs1b]; intro l r hr; cases hr
    obtain ⟨env1, hinv1, -, -, hwn, hval⟩ := translateExprToWire_sound hden htr hinv hwid
    refine ⟨fun n => if n = "out" then env1 w else env1 n, ?_, by simp [hval], hMo, ?_, ?_, ?_⟩
    · rw [hMb]
      have hpre : evalAssigns (weOf M) mems
          (CircuitM.addOutput "out" ty s2).2.module.finalize.body initial = some env1 := by
        have := hinv1.runs
        unfold Runs at this
        rw [addOutput_state]; exact this
      have := emitAssign_sound _ (weOf M) mems initial env1 "out" (.ref w) (env1 w) hpre rfl
      rw [hst]; exact this
    · intro j nm n' w' hj hp
      obtain ⟨id, hz⟩ := hzip j nm n' hj
      obtain ⟨w'', hp', -, -, hin⟩ := hsig' j nm n' id hz
      rw [hp] at hp'
      cases hp'
      exact hMi _ (gi _ hin)
    · obtain ⟨hout2, -, pre, hbody2, hpre⟩ := hemit
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hMw, List.map_reverse]; exact nodup_reverse hok2.1
      · intro hm
        rw [hMw, List.map_reverse, List.mem_reverse] at hm
        obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hm
        have := hok2.2 p hp
        rw [hpn, hfresh] at this; cases this
      · intro stm hstm
        rw [hMb] at hstm
        simp only [Module.finalize, List.mem_reverse] at hstm
        rw [hst_b] at hstm
        rcases List.mem_cons.mp hstm with rfl | hstm
        · exact ⟨"out", _, rfl, Or.inr ⟨rfl, w, rfl⟩⟩
        · rw [hbody2, hs1b, List.append_nil] at hstm
          obtain ⟨l, r, rfl, hr, hl⟩ := hpre _ hstm
          exact ⟨l, r, rfl, Or.inl ⟨hr, by rw [hMw, List.mem_reverse]; exact hl⟩⟩
      · intro hn
        -- the output port's type is the leaf wire's declared width
        have hty' : ty = .bitVector n := by
          rw [hty]
          cases hf : M.wires.find? (fun p => p.name == w) with
          | none =>
            simp only [weOf, hf] at hwn; omega
          | some p =>
            have hpM : p ∈ M.wires := List.mem_of_find?_eq_some hf
            have hpn : p.name = w := by simpa using List.find?_some hf
            have hp2 : p ∈ s2.module.wires := by rw [hMw, List.mem_reverse] at hpM; exact hpM
            have hf2 := find?_of_nodup hok2.1 hp2
            rw [hpn] at hf2
            unfold leafOutputType
            rw [hf2]
            obtain ⟨pn, pty⟩ := p
            simp only [weOf, hf] at hwn
            cases pty <;> simp at hwn <;> first | omega | (subst hwn; rfl)
        rw [hM]
        simp only [Module.finalize, co, hst_o, hout2, hout1, hty']
        rfl
      · have hf := hg.2.2.2.2.trans gf
        obtain ⟨cp, cm⟩ := addClockReset_metadata st.module
        refine ⟨?_, ?_, ?_⟩
        · rw [hM]; simp only [Module.finalize, cp]
          rw [hst]
          change s2.module.parameters.reverse = []
          rw [hf.parameters]; rfl
        · rw [hM]; simp only [Module.finalize, cm]
          rw [hst]
          exact hf.primitive
        · intro p hp
          rw [hMw, List.mem_reverse] at hp
          rcases hf.wireTypes p hp with hp | hp
          · simp [CircuitM.init, Module.empty] at hp
          · exact hp
      · intro l r hstm
        rw [hMb] at hstm
        simp only [Module.finalize, List.mem_reverse] at hstm
        rw [hst_b] at hstm
        rcases List.mem_cons.mp hstm with heq | hstm
        · cases heq
          exact hwn ▸ SizedExpr.ref w
        · have hsz := hinv1.sized l r hstm
          rw [hbody2, hs1b, List.append_nil] at hstm
          obtain ⟨l', r', heq, _, hl⟩ := hpre _ hstm
          cases heq
          have hlw := hwid ({name := l, ty := .bitVector n} : Port) hl n rfl
          simpa only [hlw] using hsz
    · obtain ⟨-, hin2, pre, hbody2, hpre⟩ := hemit
      -- no registers: no clock/reset ports, so the inputs are the binder ports
      have hall : ∀ stm ∈ st.module.body, ∃ l r, stm = Stmt.assign l r := by
        intro stm hstm
        rw [hst_b] at hstm
        rcases List.mem_cons.mp hstm with rfl | hstm
        · exact ⟨_, _, rfl⟩
        · rw [hbody2, hs1b, List.append_nil] at hstm
          obtain ⟨l, r, rfl, -, -⟩ := hpre _ hstm
          exact ⟨l, r, rfl⟩
      have hMin : M.inputs = s1.module.inputs.reverse := by
        rw [hM, addClockReset_assigns _ hall]
        simp [Module.finalize, hst_i, hin2]
      intro p hp
      rw [hMin, List.mem_reverse] at hp
      rcases hinp1 p hp with h | ⟨j, nm, n', id, w', hj, hw', rfl⟩
      · simp [CircuitM.init, Module.empty] at h
      · obtain ⟨w'', hp'', -, hwire, -⟩ := hsig' j nm n' id hj
        have hww : w'' = w' := by
          have := hjoin j w'' hp''
          rw [hw'] at this; exact (Option.some.inj (Option.some.inj this)).symm
        subst hww
        refine ⟨j, nm, n', (List.getElem?_zip_eq_some.mp hj).1, hp'', rfl, ?_⟩
        rw [hMw, List.mem_reverse]; exact gw _ hwire


/-- What the returned module guarantees for a constant `ci`: if `ci` has the
certified shape, the module preserves its meaning. -/
def CertifiedOutcome (ci : ConstantInfo) (M : Sparkle.IR.AST.Module) : Prop :=
  ∀ bs body, certifiedShape? false [] ci = some (bs, body) → Preserves bs body M

theorem MReturns.ite {α : Type} {c : Prop} [Decidable c] {a b : MetaM α} {r : α}
    (h : MReturns (if c then a else b) r) : MReturns a r ∨ MReturns b r := by
  by_cases hc : c
  · left; rw [if_pos hc] at h; exact h
  · right; rw [if_neg hc] at h; exact h

/-! ## One run, in ONE context

`MReturns` closes over the contexts, state references and worlds, so two
`MReturns` facts may describe two different runs. To relate the synthesis to the
constant IT read, a run is stated in a fixed Meta/Core context and state
references (`RunsTo`): the sub-run of `getConstInfo` found below happens in the
same contexts and references as the synthesis, at a world between its start
and end. -/

/-- `m` run in exactly these contexts and state references, from world `w`,
returns `a` at world `w'`. -/
def RunsTo {α : Type} (m : MetaM α) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (a : α) (w' : Void IO.RealWorld) : Prop :=
  m mctx mref cctx cref w = EST.Out.ok a w'

theorem RunsTo.mreturns {α : Type} {m : MetaM α} {mctx mref cctx cref w a w'}
    (h : RunsTo m mctx mref cctx cref w a w') : MReturns m a :=
  ⟨mctx, mref, cctx, cref, w, w', h⟩

theorem RunsTo.bind {α β : Type} {m : MetaM α} {f : α → MetaM β} {mctx mref cctx cref w b w''}
    (h : RunsTo (m >>= f) mctx mref cctx cref w b w'') :
    ∃ a w1, RunsTo m mctx mref cctx cref w a w1 ∧ RunsTo (f a) mctx mref cctx cref w1 b w'' := by
  unfold RunsTo at h
  change (EST.bind (m mctx mref cctx cref) fun a => f a mctx mref cctx cref) w = _ at h
  unfold EST.bind at h
  split at h
  · rename_i a w1 heq
    exact ⟨a, w1, heq, h⟩
  · cases h

theorem RunsTo.ite {α : Type} {c : Prop} [Decidable c] {a b : MetaM α} {mctx mref cctx cref w r w'}
    (h : RunsTo (if c then a else b) mctx mref cctx cref w r w') :
    RunsTo a mctx mref cctx cref w r w' ∨ RunsTo b mctx mref cctx cref w r w' := by
  by_cases hc : c
  · left; rw [if_pos hc] at h; exact h
  · right; rw [if_neg hc] at h; exact h

theorem RunsTo.try_finally {α β : Type} {x : MetaM α} {fin : MetaM β} {mctx mref cctx cref w a w'}
    (h : RunsTo (_root_.tryFinally x fin) mctx mref cctx cref w a w') :
    ∃ w1, RunsTo x mctx mref cctx cref w a w1 := by
  unfold RunsTo at h
  change (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w = _
    at h
  unfold EST.bind at h
  split at h
  · rename_i p w1 heq
    simp only [MonadFinally.tryFinally'] at heq
    split at heq
    · rename_i v w2 hx
      split at heq
      · cases heq
        simp only [EST.pure] at h
        cases h
        exact ⟨w2, hx⟩
      · cases heq
    · split at heq <;> cases heq
  · cases h

/-- `some isRunsTo` if the hypothesis is `MReturns`/`RunsTo` of a program with
head `c`. -/
meta def runHeadIs (h : Lean.Name) (c : Lean.Name) : Lean.Elab.Tactic.TacticM (Option Bool) :=
  Lean.Elab.Tactic.withMainContext do
    let d ← Lean.Meta.getLocalDeclFromUserName h
    let ty ← Lean.instantiateMVars d.type
    let args := ty.getAppArgs
    if ty.isAppOf ``MReturns && args.size == 3 && args[1]!.isAppOf c then return some false
    if ty.isAppOf ``RunsTo && args.size == 9 && args[1]!.isAppOf c then return some true
    return none

/-- Peel a SYNTACTIC bind (never one exposed by unfolding the head). -/
elab "peel_bind " h:ident : tactic => do
  match ← runHeadIs h.getId ``Bind.bind with
  | some false =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| obtain ⟨_, -, $h:ident⟩ := MReturns.bind $h:ident))
  | some true =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| obtain ⟨_, _, -, $h:ident⟩ := RunsTo.bind $h:ident))
  | none => throwError "head is not a bind"

/-- Case on a SYNTACTIC `if` at the head. -/
elab "peel_ite " h:ident : tactic => do
  match ← runHeadIs h.getId ``ite with
  | some false =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| rcases MReturns.ite $h:ident with $h:ident | $h:ident))
  | some true =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| rcases RunsTo.ite $h:ident with $h:ident | $h:ident))
  | none => throwError "head is not an if"

/-- Everything after reading the declaration, as a function of the constant. -/
theorem synthesizeFromConst_sound {logProf : String → IO Unit} {declName : Name}
    {ci : ConstantInfo} {M : Sparkle.IR.AST.Module} {D : Design}
    (h : MReturns (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) logProf
      declName [] false true ci) (M, D)) :
    CertifiedOutcome ci M := by
  intro bs body hshape
  unfold synthesizeFromConst at h
  simp only [↓reduceIte, hshape] at h
  peel_bind h
  obtain ⟨result, hres, h⟩ := MReturns.bind h
  peel_bind h
  have := MReturns.pure h
  subst this
  exact synthesizeCertified_sound hres

/-- The real entry reads the declaration with `getConstInfo`, then runs
`synthesizeFromConst` on THAT constant — in the same contexts and state
references, from the world `getConstInfo` returned. -/
theorem synthesizeCombinationalCore_reads {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (logProf : String → IO Unit) (ci : ConstantInfo) (w1 w2 w3 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) logProf
        declName [] false true ci) mctx mref cctx cref w2 (M, D) w3 := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  iterate 40 (all_goals (first | peel_bind h | peel_ite h | skip))
  all_goals (
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    exact ⟨_, ci, _, w2, _, hget, h⟩)

/-- **The entry theorem.** A successful run of the real entry read SOME
constant `ci` with `getConstInfo declName` in the same contexts and state
references, and the module it returned satisfies `CertifiedOutcome ci`. -/
theorem synthesizeCombinationalCore_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ CertifiedOutcome ci M := by
  obtain ⟨logProf, ci, w1, w2, w3, hget, hrest⟩ := synthesizeCombinationalCore_reads h
  exact ⟨ci, w1, w2, hget, synthesizeFromConst_sound hrest.mreturns⟩

/-! ## Item 3: the declaration's Lean meaning

`FExpr` is the fragment as data; `quoteDecl` is EXACTLY the `Lean.Expr` Lean's
elaborator produces for such a declaration (checked in the test against real
declarations by the Lean-level `exprDecEq`), and `denoteFE` is its Lean meaning,
built from the library operators themselves, so a user's definition is
`denoteFE … fe` by `rfl`. -/

inductive FExpr where
  | inp (j : Nat)
  | lit (v : Nat)
  | bin (op : Binary) (a b : FExpr)

/-- Inputs in range, literals representable. -/
def FExpr.WF (k n : Nat) : FExpr → Prop
  | .inp j => j < k
  | .lit v => v < 2 ^ n
  | .bin _ a b => a.WF k n ∧ b.WF k n

def evalFE (n : Nat) (vals : Nat → BitVec n) : FExpr → BitVec n
  | .inp j => vals j
  | .lit v => BitVec.ofNat n v
  | .bin op a b => op.apply (evalFE n vals a) (evalFE n vals b)

open Sparkle.Core.Signal in
def binSig {dom : Sparkle.Core.Domain.DomainConfig} {n : Nat} :
    Binary → Signal dom (BitVec n) → Signal dom (BitVec n) → Signal dom (BitVec n)
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·)
  | .and => (· &&& ·) | .or => (· ||| ·) | .xor => (· ^^^ ·)

open Sparkle.Core.Signal in
/-- The Lean meaning: the library Signal operators applied to the inputs. -/
def denoteFE {dom : Sparkle.Core.Domain.DomainConfig} (n : Nat)
    (sigs : Nat → Signal dom (BitVec n)) : FExpr → Signal dom (BitVec n)
  | .inp j => sigs j
  | .lit v => Signal.pure (BitVec.ofNat n v)
  | .bin op a b => binSig op (denoteFE n sigs a) (denoteFE n sigs b)

/-- At every cycle, the Lean meaning is `evalFE` of the inputs' values
(the `library_*` lemmas, all definitional). -/
theorem denoteFE_val {dom : Sparkle.Core.Domain.DomainConfig} (n : Nat)
    (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) :
    ∀ fe, (denoteFE n sigs fe).val t = evalFE n (fun j => (sigs j).val t) fe
  | .inp _ => rfl
  | .lit _ => rfl
  | .bin op a b => by
    show (binSig op (denoteFE n sigs a) (denoteFE n sigs b)).val t =
      op.apply (evalFE n (fun j => (sigs j).val t) a) (evalFE n (fun j => (sigs j).val t) b)
    rw [← denoteFE_val n sigs t a, ← denoteFE_val n sigs t b]
    cases op
    · exact library_add dom n _ _ t
    · exact library_sub dom n _ _ t
    · exact library_mul dom n _ _ t
    · exact library_and dom n _ _ t
    · exact library_or dom n _ _ t
    · exact library_xor dom n _ _ t

def natE (n : Nat) : Lean.Expr :=
  mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``Nat []) (.lit (.natVal n))
    (mkApp (.const ``instOfNatNat []) (.lit (.natVal n)))

def sigT (dom : Lean.Expr) (n : Nat) : Lean.Expr :=
  mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (mkApp (.const ``BitVec []) (natE n))

def binMethod : Binary → Name
  | .add => ``HAdd.hAdd | .sub => ``HSub.hSub | .mul => ``HMul.hMul
  | .and => ``HAnd.hAnd | .or => ``HOr.hOr | .xor => ``HXor.hXor

def binInst : Binary → Name
  | .add => ``Sparkle.Core.Signal.instHAddSignalBitVec
  | .sub => ``Sparkle.Core.Signal.instHSubSignalBitVec
  | .mul => ``Sparkle.Core.Signal.instHMulSignalBitVec
  | .and => ``Sparkle.Core.Signal.instHAndSignalBitVec
  | .or => ``Sparkle.Core.Signal.instHOrSignalBitVec
  | .xor => ``Sparkle.Core.Signal.instHXorSignalBitVec

/-- A canonical width-`n` operator application, as Lean elaborates it. -/
def binE (dom : Lean.Expr) (n : Nat) (op : Binary) (a b : Lean.Expr) : Lean.Expr :=
  mkApp6 (.const (binMethod op) [.zero, .zero, .zero]) (sigT dom n) (sigT dom n) (sigT dom n)
    (mkApp2 (.const (binInst op) []) dom (natE n)) a b

def quoteF (dom : Lean.Expr) (n : Nat) (inp : Nat → Lean.Expr) : FExpr → Lean.Expr
  | .inp j => inp j
  | .lit v =>
    mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom
      (mkApp (.const ``BitVec []) (natE n)) (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v))
  | .bin op a b => binE dom n op (quoteF dom n inp a) (quoteF dom n inp b)

/-- The body under `{dom}` and `k` inputs: `dom` is `.bvar k`, input `j` is
`.bvar (k - 1 - j)`. -/
def quoteBody (k n : Nat) (fe : FExpr) : Lean.Expr :=
  quoteF (.bvar k) n (fun j => .bvar (k - 1 - j)) fe

def quoteInputs (n : Nat) : List Name → Nat → Lean.Expr → Lean.Expr
  | [], _, body => body
  | nm :: rest, j, body => .lam nm (sigT (.bvar j) n) (quoteInputs n rest (j + 1) body) .default

/-- `def f {dom : DomainConfig} (x₀ … : Signal dom (BitVec n)) : Signal dom (BitVec n) := fe`. -/
def quoteDecl (domName : Name) (names : List Name) (n : Nat) (fe : FExpr) : Lean.Expr :=
  .lam domName (.const ``Sparkle.Core.Domain.DomainConfig [])
    (quoteInputs n names 0 (quoteBody names.length n fe)) .implicit

def quoteBinders (domName : Name) (names : List Name) (n : Nat) : List (Name × GateBinder) :=
  (domName, .domain) :: names.map (·, .signal n)

/-- The per-operator facts the gate and `Denotes` read, all by computation. -/
theorem op_checks (op : Binary) (dom a b : Lean.Expr) (n : Nat) :
    let e := binE dom n op a b
    e.getAppFn = .const (binMethod op) [.zero, .zero, .zero] ∧
    signalBinOpOf (binMethod op) = some op.operator ∧
    canonicalSignalBinKinds (binMethod op) e.getAppArgs = some (true, true) ∧
    canonicalSignalBitVecWidth e.getAppArgs = some n ∧
    e.getAppArgs[e.getAppArgs.size - 2]! = a ∧ e.getAppArgs[e.getAppArgs.size - 1]! = b ∧
    ((binMethod op) == ``Sparkle.Core.Signal.Signal.pure) = false := by
  intro e
  have hargs : e.getAppArgs = #[sigT dom n, sigT dom n, sigT dom n,
      mkApp2 (.const (binInst op) []) dom (natE n), a, b] := rfl
  have h1 : signalBinOpOf (binMethod op) = some op.operator := by cases op <;> rfl
  have h2 : ((binMethod op) == ``Sparkle.Core.Signal.Signal.pure) = false := by
    cases op <;> decide
  have h3 : canonicalSignalBinKinds (binMethod op) e.getAppArgs = some (true, true) := by
    rw [hargs]
    cases op <;> simp [canonicalSignalBinKinds, canonicalSignalBinInsts, binMethod,
      binInst, mkApp2, mkApp, Expr.getAppFn]
  have h4 : canonicalSignalBitVecWidth e.getAppArgs = some n := by
    rw [hargs]
    cases op <;> simp [canonicalSignalBitVecWidth, canonicalSignalBinInsts,
      canonicalSignalBoolInsts, binInst, mkApp2, mkApp, Expr.getAppFn] <;> rfl
  exact ⟨rfl, h1, h3, h4, by rw [hargs]; rfl, by rw [hargs]; rfl, h2⟩

theorem litValue_natE (n v : Nat) (h : v < 2 ^ n) :
    bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) = some (n, v) := by
  have e : bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) =
      (if v < 2 ^ n then some (n, v) else none) := rfl
  rw [e, if_pos h]


theorem instFVars_quoteF (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr) (n : Nat)
    (inp : Nat → Lean.Expr) : ∀ fe, instFVars xs d (quoteF dom n inp fe) =
      quoteF (instFVars xs d dom) n (fun j => instFVars xs d (inp j)) fe
  | .inp _ => rfl
  | .lit _ => rfl
  | .bin op a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quoteF dom n inp a)))
      (instFVars xs d (quoteF dom n inp b)) = _
    rw [instFVars_quoteF xs d dom n inp a, instFVars_quoteF xs d dom n inp b]
    rfl

theorem quoteF_congr {k n : Nat} {dom : Lean.Expr} {inp inp' : Nat → Lean.Expr}
    (h : ∀ j, j < k → inp j = inp' j) : ∀ fe, fe.WF k n → quoteF dom n inp fe = quoteF dom n inp' fe
  | .inp j, hj => h j hj
  | .lit _, _ => rfl
  | .bin op a b, ⟨ha, hb⟩ => by
    show binE _ _ _ _ _ = binE _ _ _ _ _
    rw [quoteF_congr h a ha, quoteF_congr h b hb]

/-- The body instantiated with the entry's fvars is the quotation over them. -/
theorem instFVars_quoteBody {xs : Array Lean.Expr} {k n : Nat} (hs : xs.size = k + 1)
    (fe : FExpr) (hwf : fe.WF k n) :
    instFVars xs 0 (quoteBody k n fe) = quoteF xs[0]! n (fun j => xs[j + 1]!) fe := by
  unfold quoteBody
  rw [instFVars_quoteF]
  have hdom : instFVars xs 0 (.bvar k) = xs[0]! := by
    simp only [instFVars]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1; omega
  rw [hdom]
  apply quoteF_congr _ fe hwf
  intro j hj
  simp only [instFVars]
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem gatePeel_quoteInputs {n : Nat} {body : Lean.Expr} (hb : gatePeel body = some ([], body)) :
    ∀ (names : List Name) (j : Nat),
      gatePeel (quoteInputs n names j body) = some (names.map (·, GateBinder.signal n), body)
  | [], _ => hb
  | nm :: rest, j => by
    have hk : gateBinderKind? (sigT (.bvar j) n) = some (.signal n) := rfl
    show (match gateBinderKind? (sigT (.bvar j) n), gatePeel (quoteInputs n rest (j + 1) body) with
      | some k, some (bs, body) => some ((nm, k) :: bs, body)
      | _, _ => none) = _
    rw [hk, gatePeel_quoteInputs hb rest (j + 1)]
    rfl

theorem gatePeel_quoteBody (k n : Nat) : ∀ fe, gatePeel (quoteBody k n fe) = some ([], quoteBody k n fe)
  | .inp _ => rfl
  | .lit _ => rfl
  | .bin _ _ _ => rfl

theorem gatePeel_quoteDecl (dn : Name) (names : List Name) (n : Nat) (fe : FExpr) :
    gatePeel (quoteDecl dn names n fe) =
      some (quoteBinders dn names n, quoteBody names.length n fe) := by
  have hk : gateBinderKind? (.const ``Sparkle.Core.Domain.DomainConfig []) = some .domain := rfl
  show (match gateBinderKind? (.const ``Sparkle.Core.Domain.DomainConfig []),
      gatePeel (quoteInputs n names 0 (quoteBody names.length n fe)) with
    | some k, some (bs, body) => some ((dn, k) :: bs, body)
    | _, _ => none) = _
  rw [hk, gatePeel_quoteInputs (gatePeel_quoteBody _ n fe) names 0]
  rfl

theorem gateBVar_quote {dn : Name} {names : List Name} {n j : Nat} (hj : j < names.length) :
    gateBVar? ((quoteBinders dn names n).map (·.2)).toArray (names.length - 1 - j) =
      some (.signal n) := by
  unfold gateBVar?
  have hsz : ((quoteBinders dn names n).map (·.2)).toArray.size = names.length + 1 := by
    simp [quoteBinders]
  rw [hsz, if_pos (by omega)]
  have : names.length + 1 - 1 - (names.length - 1 - j) = j + 1 := by omega
  rw [this]
  simp [quoteBinders, List.getElem?_map, hj]

theorem gateTopWidth_of_fn {kinds : Array GateBinder} {e : Lean.Expr} {m : Name} {us : List Level}
    (hnb : ∀ i, e ≠ .bvar i) (hfn : e.getAppFn = .const m us) :
    gateTopWidth? kinds e =
      if m == ``Sparkle.Core.Signal.Signal.pure then
        (e.getAppArgs.back?.bind bitVecLitValue?).map (·.1)
      else canonicalSignalBitVecWidth e.getAppArgs := by
  unfold gateTopWidth?
  split
  · exact absurd rfl (hnb _)
  · rw [hfn]

theorem gateTopWidth_inp {dn : Name} {names : List Name} {n j : Nat} (hj : j < names.length) :
    gateTopWidth? ((quoteBinders dn names n).map (·.2)).toArray
      (quoteBody names.length n (.inp j)) = some n := by
  show (match gateBVar? _ (names.length - 1 - j) with
    | some (.signal n) => some n | _ => none) = _
  rw [gateBVar_quote hj]

theorem gateTopWidth_lit {dn : Name} {names : List Name} {n v : Nat} (hv : v < 2 ^ n) :
    gateTopWidth? ((quoteBinders dn names n).map (·.2)).toArray
      (quoteBody names.length n (.lit v)) = some n := by
  have hfn : (quoteBody names.length n (.lit v)).getAppFn =
      .const ``Sparkle.Core.Signal.Signal.pure [.zero] := rfl
  have hback : (quoteBody names.length n (.lit v)).getAppArgs.back? =
      some (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) := rfl
  have hself : (``Sparkle.Core.Signal.Signal.pure == ``Sparkle.Core.Signal.Signal.pure) = true := by
    decide
  rw [gateTopWidth_of_fn (fun i h => by cases h) hfn, hself, if_pos rfl, hback, Option.bind_some,
    litValue_natE n v hv]
  rfl

theorem binE_notBVar (dom : Lean.Expr) (n : Nat) (op : Binary) (qa qb : Lean.Expr) :
    ∀ i, binE dom n op qa qb ≠ .bvar i := fun _ h => Lean.Expr.noConfusion h

theorem binE_fn (dom : Lean.Expr) (n : Nat) (op : Binary) (qa qb : Lean.Expr) :
    (binE dom n op qa qb).getAppFn = .const (binMethod op) [.zero, .zero, .zero] := rfl

theorem binMethod_ne_pure (op : Binary) :
    ((binMethod op) == ``Sparkle.Core.Signal.Signal.pure) = false := by
  cases op <;> decide

theorem gateTopWidth_binE {n : Nat} (op : Binary) (dom qa qb : Lean.Expr) (kinds : Array GateBinder) :
    gateTopWidth? kinds (binE dom n op qa qb) = some n := by
  rw [gateTopWidth_of_fn (binE_notBVar dom n op qa qb) (binE_fn dom n op qa qb),
    binMethod_ne_pure, if_neg Bool.false_ne_true]
  exact (op_checks op dom qa qb n).2.2.2.1

theorem gateTopWidth_bin {dn : Name} {names : List Name} {n : Nat} (op : Binary) (a b : FExpr) :
    gateTopWidth? ((quoteBinders dn names n).map (·.2)).toArray
      (quoteBody names.length n (.bin op a b)) = some n :=
  gateTopWidth_binE op _ _ _ _

theorem gateTopWidth_quote {dn : Name} {names : List Name} {n : Nat} (fe : FExpr)
    (hwf : fe.WF names.length n) :
    gateTopWidth? ((quoteBinders dn names n).map (·.2)).toArray (quoteBody names.length n fe) =
      some n := by
  cases fe with
  | inp j => exact gateTopWidth_inp hwf
  | lit v => exact gateTopWidth_lit hwf
  | bin op a b => exact gateTopWidth_bin op a b

theorem gateBody_quote {dn : Name} {names : List Name} {n : Nat} :
    ∀ fe, fe.WF names.length n →
      gateBody ((quoteBinders dn names n).map (·.2)).toArray n (quoteBody names.length n fe) = true
  | .inp j, hj => by
    show (gateBVar? _ (names.length - 1 - j) == some (.signal n)) = true
    rw [gateBVar_quote hj]; simp
  | .lit v, hv => by
    show gateBody _ n (.app (.app _ _) (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v))) = true
    rw [gateBody.eq_2]
    show (if (``Sparkle.Core.Signal.Signal.pure == ``Sparkle.Core.Signal.Signal.pure) = true then
      (match bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) with
        | some (w, _) => w == n | none => false) else _) = true
    rw [litValue_natE n v hv]; simp
  | .bin op a b, ⟨ha, hb⟩ => by
    obtain ⟨hfn, hop, hk, hw, -, -, hnp⟩ := op_checks op (.bvar names.length)
      (quoteBody names.length n a) (quoteBody names.length n b) n
    show gateBody _ n (binE (.bvar names.length) n op (quoteBody names.length n a)
      (quoteBody names.length n b)) = true
    simp only [binE, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp] at hfn hk hw ⊢
    rw [gateBody.eq_2, hfn]
    simp only [hnp, Bool.false_eq_true, if_false, hop, hk, hw, beq_self_eq_true, Bool.true_and,
      gateBody_quote a ha, gateBody_quote b hb]


/-- The gate accepts every quoted fragment declaration. -/
theorem certifiedShape_quote {d : DefinitionVal} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr} (hv : d.value = quoteDecl dn names n fe) (hwf : fe.WF names.length n) :
    certifiedShape? false [] (.defnInfo d) =
      some (quoteBinders dn names n, quoteBody names.length n fe) := by
  unfold certifiedShape?
  simp only [Bool.false_or, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, hv,
    gatePeel_quoteDecl, gateTopWidth_quote fe hwf, gateBody_quote fe hwf, if_true]

theorem rhoOf_at : ∀ (L : List ((Name × GateBinder) × FVarId)) (vals : Nat → Nat) (j : Nat)
    (nm : Name) (n : Nat) (id : FVarId), (L.map Prod.snd).Nodup →
    L[j]? = some ((nm, .signal n), id) → rhoOf L vals id = some ⟨n, BitVec.ofNat n (vals j)⟩
  | [], _, _, _, _, _, _, h => by simp at h
  | ((nm0, k0), id0) :: rest, vals, j, nm, n, id, hnd, h => by
    obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, rfl⟩ := h
      simp [rhoOf]
    | succ j =>
      have hj : rest[j]? = some ((nm, .signal n), id) := by simpa using h
      have hne : id ≠ id0 := by
        intro he; subst he
        exact hnotin (List.mem_map.mpr ⟨_, List.mem_of_getElem? hj, rfl⟩)
      simp only [rhoOf, if_neg hne]
      exact rhoOf_at rest (fun i => vals (i + 1)) j nm n id hnd' hj

/-- The quotation over the entry's fvars denotes `evalFE` of the binder values. -/
theorem denotes_quote {L : List ((Name × GateBinder) × FVarId)} {vals : Nat → Nat} {n : Nat}
    {dom : Lean.Expr} {inp : Nat → Lean.Expr} {k : Nat}
    (hinp : ∀ j, j < k → ∃ nm id, inp j = .fvar id ∧ L[j + 1]? = some ((nm, .signal n), id))
    (hnd : (L.map Prod.snd).Nodup) :
    ∀ fe, fe.WF k n → Denotes (rhoOf L vals) (quoteF dom n inp fe) n
      (evalFE n (fun j => BitVec.ofNat n (vals (j + 1))) fe)
  | .inp j, hj => by
    obtain ⟨nm, id, he, hL⟩ := hinp j hj
    show Denotes _ (inp j) n _
    rw [he]
    exact Denotes.fvar (rhoOf_at L vals (j + 1) nm n id hnd hL)
  | .lit v, hv => by
    exact Denotes.pureLit (us := [.zero]) (c := mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v))
      rfl rfl (litValue_natE n v hv)
  | .bin op a b, ⟨ha, hb⟩ => by
    have ck := op_checks op dom (quoteF dom n inp a) (quoteF dom n inp b) n
    have da := denotes_quote (vals := vals) (dom := dom) hinp hnd a ha
    have db := denotes_quote (vals := vals) (dom := dom) hinp hnd b hb
    rw [← ck.2.2.2.2.1] at da
    rw [← ck.2.2.2.2.2.1] at db
    exact Denotes.binary (bop := op) ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 da db


/-- For a constant whose value quotes a well-formed `fe`, `CertifiedOutcome`
needs no `Denotes` premise: `out` carries `evalFE` of the inputs. -/
theorem outcome_quote {M : Sparkle.IR.AST.Module} {d : DefinitionVal} {dn : Name}
    {names : List Name} {n : Nat} {fe : FExpr} (hci : CertifiedOutcome (.defnInfo d) M)
    (hv : d.value = quoteDecl dn names n fe) (hwf : fe.WF names.length n) :
      ∃ port : Nat → Option String,
        (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
        (∀ j, j < names.length → ∃ w, port j = some w) ∧
        ∀ (vals : Nat → BitVec n) (mems : MEnv) (initial : Env),
          (∀ j w, j < names.length → port j = some w → initial w = (vals j).toNat) →
          ∃ env, evalAssigns (weOf M) mems M.body initial = some env ∧
            env "out" = (evalFE n vals fe).toNat ∧ "out" ∈ M.outputs.map (·.name) ∧
            (∀ j w, j < names.length → port j = some w →
              ({ name := w, ty := .bitVector n } : Port) ∈ M.inputs) ∧
            PostReady M n ∧
            (∀ p ∈ M.inputs, ∃ j, j < names.length ∧ port j = some p.name ∧
              p.ty = .bitVector n ∧ ({ name := p.name, ty := .bitVector n } : Port) ∈ M.wires) := by
  obtain ⟨ids, hnd, hlen, port0, hdist, hex, hsem⟩ := hci _ _ (certifiedShape_quote hv hwf)
  have hlenB : (quoteBinders dn names n).length = names.length + 1 := by simp [quoteBinders]
  have hbs : ∀ j (hj : j < names.length),
      (quoteBinders dn names n)[j + 1]? = some (names[j], GateBinder.signal n) := by
    intro j hj; simp [quoteBinders, hj]
  have hbs_inv : ∀ i nm n', (quoteBinders dn names n)[i]? = some (nm, GateBinder.signal n') →
      ∃ j, i = j + 1 ∧ j < names.length ∧ n' = n := by
    intro i nm n' hi
    cases i with
    | zero => simp [quoteBinders] at hi
    | succ j =>
      have hi' : (names.map (·, GateBinder.signal n))[j]? = some (nm, GateBinder.signal n') := by
        simpa [quoteBinders] using hi
      rw [List.getElem?_map] at hi'
      cases hj : names[j]? with
      | none => rw [hj] at hi'; cases hi'
      | some x =>
        rw [hj] at hi'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
          GateBinder.signal.injEq] at hi'
        exact ⟨j, rfl, (List.getElem?_eq_some_iff.mp hj).1, hi'.2.symm⟩
  refine ⟨fun j => port0 (j + 1), ?_, ?_, ?_⟩
  · intro j j' w h1 h2
    have := hdist _ _ w h1 h2
    omega
  · intro j hj
    exact hex (j + 1) names[j] n (hbs j hj)
  · intro vals mems initial hinit
    let vals' : Nat → Nat := fun i => (vals (i - 1)).toNat
    have hinit' : ∀ i nm n' w, (quoteBinders dn names n)[i]? = some (nm, GateBinder.signal n') →
        port0 i = some w → initial w = (BitVec.ofNat n' (vals' i)).toNat := by
      intro i nm n' w hi hp
      obtain ⟨j, rfl, hj, rfl⟩ := hbs_inv i nm n' hi
      rw [hinit j w hj hp]
      simp [vals']
    have hxs : ((ids.map Lean.Expr.fvar).toArray).size = names.length + 1 := by
      simp [hlen, hlenB]
    have hL : ((quoteBinders dn names n).zip ids).map Prod.snd = ids :=
      List.map_snd_zip (by rw [hlen]; exact Nat.le_refl _)
    have hinp : ∀ j, j < names.length → ∃ nm id,
        ((ids.map Lean.Expr.fvar).toArray)[j + 1]! = .fvar id ∧
        ((quoteBinders dn names n).zip ids)[j + 1]? = some ((nm, .signal n), id) := by
      intro j hj
      have hlt : j + 1 < ids.length := by rw [hlen, hlenB]; omega
      refine ⟨names[j], ids[j + 1], ?_, ?_⟩
      · simp [hlt]
      · exact List.getElem?_zip_eq_some.mpr ⟨hbs j hj, by simp [hlt]⟩
    have hden := denotes_quote (vals := vals') (dom := ((ids.map Lean.Expr.fvar).toArray)[0]!)
      hinp (by rw [hL]; exact hnd) fe hwf
    have hfun : (fun j => BitVec.ofNat n (vals' (j + 1))) = vals := by
      funext j; simp [vals']
    rw [hfun, ← instFVars_quoteBody hxs fe hwf] at hden
    obtain ⟨env, hev, hout, hmo, hin, hpr, hins⟩ :=
      hsem vals' mems initial hinit' n (evalFE n vals fe) hden
    refine ⟨env, hev, hout, hmo, fun j w hj hp => hin (j + 1) names[j] n w (hbs j hj) hp, hpr, ?_⟩
    intro p hp
    obtain ⟨i, nm, n', hi, hpi, hty, hdecl⟩ := hins p hp
    obtain ⟨j, rfl, hj, rfl⟩ := hbs_inv i nm n' hi
    exact ⟨j, hj, hpi, hty, hdecl⟩

/-- **Items 1–3 at the synthesis entry, for the fragment.** A successful run
of the real entry read a constant `ci` with `getConstInfo declName` IN THE SAME
contexts and state references; if that constant's value quotes a well-formed
fragment term `fe`, the returned module has a distinct input port per input and,
for all input values, drives `out` with `evalFE n vals fe`. -/
theorem fragmentDecl_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ (d : DefinitionVal) (dn : Name) (names : List Name) (n : Nat) (fe : FExpr),
      ci = .defnInfo d → d.value = quoteDecl dn names n fe → fe.WF names.length n →
      ∃ port : Nat → Option String,
        (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
        (∀ j, j < names.length → ∃ w, port j = some w) ∧
        ∀ (vals : Nat → BitVec n) (mems : MEnv) (initial : Env),
          (∀ j w, j < names.length → port j = some w → initial w = (vals j).toNat) →
          ∃ env, evalAssigns (weOf M) mems M.body initial = some env ∧
            env "out" = (evalFE n vals fe).toNat ∧ "out" ∈ M.outputs.map (·.name) ∧
            (∀ j w, j < names.length → port j = some w →
              ({ name := w, ty := .bitVector n } : Port) ∈ M.inputs) ∧
            PostReady M n ∧
            (∀ p ∈ M.inputs, ∃ j, j < names.length ∧ port j = some p.name ∧
              p.ty = .bitVector n ∧ ({ name := p.name, ty := .bitVector n } : Port) ∈ M.wires) := by
  obtain ⟨ci, w1, w2, hget, hci⟩ := synthesizeCombinationalCore_sound h
  refine ⟨ci, w1, w2, hget, fun d dn names n fe hcid hv hwf => ?_⟩
  subst hcid
  exact outcome_quote hci hv hwf

/-- The same with Signals: at every cycle `t`, `out` carries
`(denoteFE n sigs fe).val t`, the Lean meaning. -/
theorem fragmentDecl_sound_signal {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ (d : DefinitionVal) (dn : Name) (names : List Name) (n : Nat) (fe : FExpr),
      ci = .defnInfo d → d.value = quoteDecl dn names n fe → fe.WF names.length n →
      ∃ port : Nat → Option String,
        (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
        (∀ j, j < names.length → ∃ w, port j = some w) ∧
        ∀ {dom : Sparkle.Core.Domain.DomainConfig}
          (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv)
          (initial : Env),
          (∀ j w, j < names.length → port j = some w → initial w = ((sigs j).val t).toNat) →
          ∃ env, evalAssigns (weOf M) mems M.body initial = some env ∧
            env "out" = ((denoteFE n sigs fe).val t).toNat ∧ PostReady M n ∧
            (∀ p ∈ M.inputs, ∃ j, j < names.length ∧ port j = some p.name ∧
              p.ty = .bitVector n ∧ ({ name := p.name, ty := .bitVector n } : Port) ∈ M.wires) ∧
            "out" ∈ M.outputs.map (·.name) ∧
            (∀ j w, j < names.length → port j = some w →
              ({ name := w, ty := .bitVector n } : Port) ∈ M.inputs) := by
  obtain ⟨ci, w1, w2, hget, hci⟩ := fragmentDecl_sound h
  refine ⟨ci, w1, w2, hget, fun d dn names n fe hcid hv hwf => ?_⟩
  obtain ⟨port, hdist, hex, hsem⟩ := hci d dn names n fe hcid hv hwf
  refine ⟨port, hdist, hex, fun sigs t mems initial hinit => ?_⟩
  obtain ⟨env, hev, hout, hmo, hin, hpr, hins⟩ := hsem (fun j => (sigs j).val t) mems initial hinit
  exact ⟨env, hev, by rw [hout, denoteFE_val], hpr, hins, hmo, hin⟩

/-- The ONE fact about Lean's environment the declaration-level statements use,
stated for the contexts and state references of the run: every lookup of
`declName` there returns a definition whose value is `v`. (The Core state sits
behind an `ST.Ref`, so this cannot be derived inside the logic; it is what
"the environment defines `declName := v`" means for `getConstInfo`.) -/
def EnvDefines (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (v : Lean.Expr) : Prop :=
  ∀ w1 ci w2, RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    ∃ d : DefinitionVal, ci = .defnInfo d ∧ d.value = v

/-- A successful run of the real entry for a declaration that the run's own
environment defines as `quoteDecl dn names n fe`: the IR computes the Lean
meaning at every cycle, on distinct input ports. The constant is the one THIS
run read (via `synthesizeCombinationalCore_reads`), not one read elsewhere. -/
theorem fragmentDecl_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) :
    ∃ port : Nat → Option String,
      (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
      (∀ j, j < names.length → ∃ w, port j = some w) ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv)
        (initial : Env),
        (∀ j w, j < names.length → port j = some w → initial w = ((sigs j).val t).toNat) →
        ∃ env, evalAssigns (weOf M) mems M.body initial = some env ∧
          env "out" = ((denoteFE n sigs fe).val t).toNat ∧ PostReady M n ∧
          (∀ p ∈ M.inputs, ∃ j, j < names.length ∧ port j = some p.name ∧
            p.ty = .bitVector n ∧ ({ name := p.name, ty := .bitVector n } : Port) ∈ M.wires) ∧
          "out" ∈ M.outputs.map (·.name) ∧
          (∀ j w, j < names.length → port j = some w →
            ({ name := w, ty := .bitVector n } : Port) ∈ M.inputs) := by
  obtain ⟨ci, w1, w2, hget, hci⟩ := fragmentDecl_sound_signal h
  obtain ⟨d, hcid, hv⟩ := henv w1 ci w2 hget
  exact hci d dn names n fe hcid hv hwf

/-! ## Naming a declaration's value in a theorem -/

section
open Lean Elab Command

/-- The `Expr` that constructs `l`. -/
partial def reflLevel : Level → Except String Lean.Expr
  | .zero => pure (mkConst ``Level.zero)
  | .succ l => return mkApp (mkConst ``Level.succ) (← reflLevel l)
  | l => throw s!"level {l} not supported"

def reflBinderInfo : BinderInfo → Lean.Expr
  | .default => mkConst ``BinderInfo.default
  | .implicit => mkConst ``BinderInfo.implicit
  | .strictImplicit => mkConst ``BinderInfo.strictImplicit
  | .instImplicit => mkConst ``BinderInfo.instImplicit

/-- The `Expr` that constructs `e` (the forms a fragment declaration uses). -/
partial def reflExpr : Lean.Expr → Except String Lean.Expr
  | .bvar i => pure (mkApp (mkConst ``Lean.Expr.bvar) (toExpr i))
  | .const n ls => do
    let ls ← ls.mapM reflLevel
    return mkApp2 (mkConst ``Lean.Expr.const) (toExpr n) (← pure (ls.foldr
      (fun l acc => mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Level) l acc)
      (mkApp (mkConst ``List.nil [.zero]) (mkConst ``Level))))
  | .app f a => return mkApp2 (mkConst ``Lean.Expr.app) (← reflExpr f) (← reflExpr a)
  | .lam n t b bi => do
    let rt ← reflExpr t
    let rb ← reflExpr b
    return mkApp4 (mkConst ``Lean.Expr.lam) (toExpr n) rt rb (reflBinderInfo bi)
  | .lit (.natVal k) =>
    pure (mkApp (mkConst ``Lean.Expr.lit) (mkApp (mkConst ``Literal.natVal) (toExpr k)))
  | e => throw s!"unsupported expression form {e}"

/-- `#def_decl_value v of f` adds `def v : Lean.Expr := <the value of f, as
elaborated>`, so a declaration's value can be named in a theorem. It reads the
same `getConstInfo` the synthesis entry reads; `EnvDefines … f v` is then the
statement that the run's environment is this one. -/
elab "#def_decl_value " n:ident " of " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let ci ← getConstInfo declName
  let some v := ci.value? | throwError "{declName} has no value"
  let r ← match reflExpr v with
    | .ok r => pure r
    | .error msg => throwError msg
  let nm := (← getCurrNamespace) ++ n.getId
  let ty := mkConst ``Lean.Expr
  let dv : DefinitionVal :=
    { name := nm
      levelParams := []
      type := ty
      value := r
      hints := ReducibilityHints.abbrev
      safety := DefinitionSafety.safe }
  liftCoreM <| addDecl (Declaration.defnDecl dv)

end

end Tools.ShippingEntrySoundness
