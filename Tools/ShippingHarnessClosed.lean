import Tools.ShippingMachineCloses

/-! # The harness' module reads its input ports and wires driven earlier

`readsClosedB` (what `closeInsts` asks of a child's body, in `kidsCombB`) for
EVERY run of the harness on a quoted term, from the empty initial body: every
statement of the returned body reads only names of the module's input ports
or names an earlier statement drives.

Two steps, kept apart: the translator's closed-reads invariant (`Cl`: a
statement reads protected names — the names in use before the translation —
or names driven earlier; a wire only reserved is not readable), and, by the
existing `ReadsOK` with `V := "an input port's name"`, that a protected name
a statement reads is an input port (the variables are bound to the ports).
The builder's list is in reverse emission order; the returned body is its
reverse. No closed-reads premise is assumed. -/
namespace Tools.ShippingHarnessClosed
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion Tools.ShippingUnifiedProtection
open Tools.ShippingUnifiedEntrySoundness
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedInvariant (Separate)
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingPostSoundness
open Tools.ShippingCompareLoweringSoundness
open Tools.ShippingModulePrintSoundness Tools.ShippingPrintSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedExecutionSoundness
open Tools.ShippingMixedSourceBridge
open Tools.ShippingMixedPrintSoundness (mixedShape_positive)
open Tools.ShippingUnifiedSpine
open Tools.ShippingBindingsSoundness (visible)

open Tools.ShippingMachineCloses Tools.ShippingHarnessSpine Tools.ShippingMachineEntry
open Sparkle.IR.Machine Sparkle.IR.Reorder

/-! ## `readsClosedB` -/

theorem readsClosedB_append : ∀ (X : List Stmt) (S : List String) (Y : List Stmt),
    readsClosedB S (X ++ Y) = (readsClosedB S X && readsClosedB (S ++ writesOf X) Y)
  | [], S, Y => by simp [readsClosedB, writesOf]
  | st :: X, S, Y => by
    have ih := readsClosedB_append X (S ++ stmtWrites st) Y
    have hw : S ++ writesOf (st :: X) = S ++ stmtWrites st ++ writesOf X := by
      show S ++ (stmtWrites st ++ writesOf X) = _
      rw [List.append_assoc]
    show ((stmtReads st).all (fun n => S.contains n) &&
      readsClosedB (S ++ stmtWrites st) (X ++ Y)) = _
    rw [ih, hw]
    show _ = (((stmtReads st).all (fun n => S.contains n) &&
      readsClosedB (S ++ stmtWrites st) X) && _)
    rw [Bool.and_assoc]

theorem mem_writesOf_reverse {x : String} {X : List Stmt} (h : x ∈ writesOf X) :
    x ∈ writesOf X.reverse := by
  unfold writesOf at h ⊢
  obtain ⟨st, hs, hw⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨st, List.mem_reverse.mpr hs, hw⟩

/-- **From the builder's order to the returned body's.** A closed builder list
whose protected reads are in `S`: its reverse reads names of `S` or names
written before. -/
theorem closed_forward {P : String → Prop} {S : List String} :
    ∀ (BB : List Stmt), ClosedB P BB → (∀ st ∈ BB, ∀ x ∈ stmtReads st, P x → x ∈ S) →
      readsClosedB S BB.reverse = true
  | [], _, _ => rfl
  | st :: post, hc, hP => by
    rw [List.reverse_cons, readsClosedB_append,
      closed_forward post hc.2 (fun s hs => hP s (List.mem_cons_of_mem _ hs)), Bool.true_and]
    show ((stmtReads st).all (fun n => (S ++ writesOf post.reverse).contains n) && true) = true
    rw [Bool.and_true, List.all_eq_true]
    intro x hx
    rw [List.contains_iff_mem]
    rcases hc.1 x hx with hp | hw
    · exact List.mem_append_left _ (hP st (List.mem_cons_self ..) x hx hp)
    · exact List.mem_append_right _ (mem_writesOf_reverse hw)

set_option maxHeartbeats 1000000 in
/-- **The harness' body is closed over its input ports** — for every run of
the harness on a quoted term. -/
theorem harness_closed {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr} {m : Sparkle.IR.AST.Module}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {returned : String}
    {st : CircuitState}
    (run : Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids))
        (entryCompilerState false cache) (CircuitM.init declName.toString) returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (initial : Env)
    (values : Admissible bools bits initial (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString))
    (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (binp vinp : Nat → FVarId)
    (bvals : Nat → Bool) (vvals : (j : Nat) → (w : Nat) → BitVec w)
    {srt : SType} (e : Term srt) (he : e.WF kb kv vw)
    (hbv : ∀ j, j < kb → (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).bools (binp j) = some (bvals j))
    (hvv : ∀ j, j < kv → (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).bits (vinp j) =
        some ⟨vw j, vvals j (vw j)⟩)
    (qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)
    (fresh : ((bs.zip ids).map Prod.snd).Nodup)
    (hpb : ∀ j, j < kb → ∃ (pos : Nat) (b : Name × MixedGateBinder), (bs.zip ids)[pos]? = some (b, binp j) ∧ b.2 ≠ .domain)
    (hpv : ∀ j, j < kv → ∃ (pos : Nat) (b : Name × MixedGateBinder), (bs.zip ids)[pos]? = some (b, vinp j) ∧ b.2 ≠ .domain)
    (hassign : ∀ stmt ∈ m.body, ∃ l r, stmt = Stmt.assign l r) :
    readsClosedB ((inputPorts bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).map (·.name)) m.body = true := by
  let a := start (entryCompilerState false cache) declName.toString
  let p := prepare bools bits (bs.zip ids) a
  have empty := empty_layout (entryCompilerState false cache) declName.toString initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  have leaf := prepare_returns (bs.zip ids) a (bools := bools) (bits := bits) run
  rw [qeq] at leaf
  have separate := prepared.1.separate prepared.2.1
  have hb' : ∀ j, j < kb → inputValues p.bools p.bits (binp j) = some (.bool (bvals j)) :=
    fun j hj => inputValues_bool (hbv j hj)
  have hv' : ∀ j, j < kv → inputValues p.bools p.bits (vinp j) =
      some (.bits (vw j) (vvals j (vw j))) :=
    fun j hj => inputValues_bits separate (hvv j hj)
  obtain ⟨w, sm, ty, tr, outFresh, ht, -⟩ := emitLeaves_single leaf
  have decls := prepare_declarations (bools := bools) (bits := bits) (bs.zip ids) a
    (List.Sublist.refl []) (by intro port hp; cases hp)
  have look := lookup_of_ports prepared.1 prepared.2.1
  let S := (inputPorts bools bits (bs.zip ids) a).map (·.name)
  have st0 : St p.context (inputValues p.bools p.bits)
      (fun id => ∃ (pos : Nat) (b : Name × MixedGateBinder), (bs.zip ids)[pos]? = some (b, id) ∧ b.2 ≠ .domain)
      (fun x => p.state.usedNames.contains x = true) (fun x => x ∈ S) p.state := by
    refine ⟨RecQ.empty (prepared.2.2.2.trans rfl), ?_, fun _ h => h, ?_, ?_, ?_⟩
    · -- every input variable is bound to a wire in use, declared at its value's width
      intro id v hi
      obtain ⟨z0, hz0, hu0⟩ := look.lookup id v hi
      unfold inputValues at hi
      cases hρ : p.bools id with
      | some b =>
        simp only [hρ] at hi
        cases hi
        obtain ⟨z, bound, decl, -⟩ := prepared.1.bool id b hρ
        rw [bound] at hz0
        cases hz0
        exact ⟨_, bound, ⟨_, decl, rfl⟩, hu0⟩
      | none =>
        simp only [hρ] at hi
        cases hβ : p.bits id with
        | none => simp [hβ] at hi
        | some nx =>
          obtain ⟨n, x⟩ := nx
          simp only [hβ, Option.map_some] at hi
          cases hi
          obtain ⟨z, bound, decl, -⟩ := prepared.1.bits id n x hβ
          rw [bound] at hz0
          cases hz0
          exact ⟨_, bound, ⟨_, decl, rfl⟩, hu0⟩
    · intro l r hm
      rw [prepared.2.2.1] at hm
      cases hm
    · -- a bound variable's wire is an input port's
      rintro id z ⟨pos, b, hmem, hk⟩ hz
      have hw := bound_where (bools := bools) (bits := bits) (bs.zip ids) [] a
        (by simpa using fresh) (by intro b hb; cases hb) (by simp [inputPorts])
        (pos := pos) (b := (b, id)) (by simpa using hmem) hk
      simp only [List.append_nil] at hw
      rcases hw with ⟨-, port, hp, hv⟩ | ⟨i, port, -, hp, -⟩
      · rw [hv] at hz
        cases hz
        exact List.mem_map_of_mem hp
      · simp [inputPorts] at hp
    · intro l r hm
      rw [prepared.2.2.1] at hm
      cases hm
  obtain ⟨stm, hext, -, -, hvw, -, hcl⟩ := translateExprToWire_spine (ctx := p.context)
    (inputs := inputValues p.bools p.bits)
    (B := fun id => ∃ (pos : Nat) (b : Name × MixedGateBinder), (bs.zip ids)[pos]? = some (b, id) ∧ b.2 ≠ .domain)
    (P := fun x => p.state.usedNames.contains x = true) (V := fun x => x ∈ S) (dom := dom)
    (bi := binp) (vi := vinp) (ub := fun j => j < kb) (uv := fun j => j < kv) hb' hv'
    hpb hpv e he (uses_of_wf (fun _ h => h) (fun _ h => h) e he) "out" true p.state sm w tr st0
  -- the reads are closed from the empty body on; the result wire is driven or protected
  have c1 := hcl (fun _ => False) ⟨by rw [prepared.2.2.1]; trivial, fun _ h => h.elim⟩
  have bodyEq : m.body = st.module.body.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  have hBB : st.module.body = Stmt.assign "out" (.ref w) :: sm.module.body := by
    rw [ht, emitAssign_body_cons]
    rfl
  rw [bodyEq, hBB]
  refine closed_forward (P := fun x => p.state.usedNames.contains x = true) _ ⟨?_, c1.1⟩ ?_
  · intro x hx
    have hxw : x = w := by simpa [stmtReads, refsOf] using hx
    subst hxw
    rcases c1.2 x (Or.inr rfl) with ⟨rhs, hr⟩ | hp
    · exact Or.inr (mem_writesOf_assign hr)
    · exact Or.inl hp
  · intro stmt hs x hx hp
    rcases List.mem_cons.mp hs with e | hin
    · subst e
      have hxw : x = w := by simpa [stmtReads, refsOf] using hx
      subst hxw
      exact hvw hp
    · obtain ⟨l, r, rfl⟩ := hassign stmt (by
        rw [bodyEq, hBB, List.mem_reverse]
        exact List.mem_cons_of_mem _ hin)
      exact stm.2.2.2.2.2 l r hin x hx hp

end Tools.ShippingHarnessClosed
