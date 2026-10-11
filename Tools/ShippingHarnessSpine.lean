import Tools.ShippingUnifiedExecutionSoundness
import Tools.ShippingUnifiedSpine
import Tools.ShippingSpineOrder

/-! # The spine in the module the certified harness returns

`translateExprToWire_spine` is about the translator on a builder state. Here
it is carried to the module a RUN of the harness returns: the harness starts
from the empty record (so the record invariant holds), every binder is bound
by the port walk, and what the harness adds after the translation — the
output port and `assign out = w` — keeps the translator's statements. -/
namespace Tools.ShippingHarnessSpine
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

/-- **The harness' module has the spine.** For a run of the harness on a
quoted term: the returned body ends in `assign out = w`, and `w` has the links
of the term's expression in that body. -/
theorem harness_spine_at {logProf : String → IO Unit} {declName : Name}
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
      quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e) :
    ∃ B w, m.body = B ++ [.assign "out" (.ref w)] ∧
      (∀ n, SpineQ (fun x => (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.usedNames.contains x = true)
        (fun id => visible (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
          (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings id)
        m.wires m.body n
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e) w) ∧
      -- no statement of the returned body drives an input port
      ∀ port ∈ (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.module.inputs,
        ∀ l r, Stmt.assign l r ∈ m.body → l ≠ port.name := by
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
  have st0 : St p.context (inputValues p.bools p.bits) (fun _ => True)
      (fun x => p.state.usedNames.contains x = true) (fun _ => True) p.state := by
    refine ⟨RecQ.empty (prepared.2.2.2.trans rfl), ?_, fun _ h => h, ?_, fun _ _ _ _ => trivial, ?_⟩
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
    · intro l r hm
      rw [prepared.2.2.1] at hm
      cases hm
  obtain ⟨stm, hext, hsp, -⟩ := translateExprToWire_spine (ctx := p.context)
    (inputs := inputValues p.bools p.bits) (B := fun _ => True)
    (P := fun x => p.state.usedNames.contains x = true) (V := fun _ => True) (dom := dom)
    (bi := binp) (vi := vinp) (ub := fun _ => True) (uv := fun _ => True) hb' hv'
    (fun _ _ => trivial) (fun _ _ => trivial) e he (Uses.top e) "out" true p.state sm w tr st0
  have bodyEq : m.body = st.module.body.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have hwires : ∀ port ∈ sm.module.wires, port ∈ m.wires := by
    intro port hp
    rw [wireEq, List.mem_reverse, ht, emitAssign_wires]
    exact hp
  have hstmts : ∀ stmt ∈ sm.module.body, stmt ∈ m.body := by
    intro stmt hs
    rw [bodyEq, ht, emitAssign_body_cons, List.mem_reverse]
    exact List.mem_cons_of_mem _ hs
  have hsp' := fun n => (hsp n).mono hwires hstmts
  rw [hext.2.1] at hsp'
  refine ⟨(CircuitM.addOutput "out" ty sm).2.module.body.reverse, w, ?_, hsp', ?_⟩
  · rw [bodyEq, ht, emitAssign_body_cons, List.reverse_cons]
  · intro port hp l r hm heq
    have hused : p.state.usedNames.contains port.name = true :=
      prepared.2.1.2 port (decls.1.subset hp)
    rw [bodyEq, ht, emitAssign_body_cons, List.mem_reverse] at hm
    rcases List.mem_cons.mp hm with hout | hin
    · -- the final assign drives `out`, a name not in use when the translator returned
      cases hout
      have := stm.2.2.1 port.name hused
      rw [← heq, outFresh] at this
      cases this
    · exact stm.2.2.2.1 l r hin (heq ▸ hused)

/-- **The per-field order facts on the harness' module.** For a run of the
harness on a packed body whose fields use only the variables of their
position: the builder's body `bodyB` (the returned body is its reverse and the
final `assign out`), the per-field facts `LP` on it, and that none of its
statements drives a name in use before the translation. -/
theorem harness_links_at {logProf : String → IO Unit} {declName : Name}
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
    (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c))
    (he : (Tools.ShippingMachineEntry.packLets fs core).2.WF kb kv vw)
    (hbv : ∀ j, j < kb → (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).bools (binp j) = some (bvals j))
    (hvv : ∀ j, j < kv → (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).bits (vinp j) =
        some ⟨vw j, vvals j (vw j)⟩)
    (qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j))
        (Tools.ShippingMachineEntry.packLets fs core).2)
    {ubk uvk : Nat → Nat → Prop} {Vk : Nat → String → Prop}
    (hmonoV : ∀ k x, Vk k x → Vk (k + 1) x)
    (hbind : ∀ k id z, Tools.ShippingSpineOrder.Bk binp vinp ubk uvk k id →
      visible (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
        (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings id = some z →
      Vk k z)
    (hfields : Tools.ShippingSpineOrder.FieldsOK ubk uvk kb kv vw 0 fs)
    (hcoreU : Uses (ubk fs.length) (uvk fs.length) core) :
    ∃ bodyB w, m.body = bodyB.reverse ++ [.assign "out" (.ref w)] ∧
      Tools.ShippingSpineOrder.LP
        (fun x => (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.usedNames.contains x = true)
        (fun id => visible (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
          (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings id)
        Vk bodyB 0
        (fs.map fun f => quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) f.2) w ∧
      ∀ l r, Stmt.assign l r ∈ bodyB →
        ¬ (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.usedNames.contains l = true := by
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
  have stK : St p.context (inputValues p.bools p.bits)
      (Tools.ShippingSpineOrder.Bk binp vinp ubk uvk 0)
      (fun x => p.state.usedNames.contains x = true) (Vk 0) p.state := by
    refine ⟨RecQ.empty (prepared.2.2.2.trans rfl), ?_, fun _ h => h, ?_,
      fun id z hB hz => hbind 0 id z hB hz, ?_⟩
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
    · intro l r hm
      rw [prepared.2.2.1] at hm
      cases hm
  have st0 : St p.context (inputValues p.bools p.bits) (fun _ => True)
      (fun x => p.state.usedNames.contains x = true) (fun _ => True) p.state := by
    refine ⟨RecQ.empty (prepared.2.2.2.trans rfl), ?_, fun _ h => h, ?_, fun _ _ _ _ => trivial, ?_⟩
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
    · intro l r hm
      rw [prepared.2.2.1] at hm
      cases hm
  obtain ⟨hlp, hextK⟩ := Tools.ShippingSpineOrder.spine_links (ctx := p.context)
    (P := fun x => p.state.usedNames.contains x = true) (dom := dom) hb' hv' hmonoV
    p.state.sourceBindings hbind fs core 0 translateFuelLimit p.state sm w "out" true hfields
    (Tools.ShippingMachineEntry.packLets_wf fs core he) (by simpa using hcoreU) rfl stK tr
  obtain ⟨stm, -, -, -⟩ := translateExprToWire_spine (ctx := p.context)
    (inputs := inputValues p.bools p.bits) (B := fun _ => True)
    (P := fun x => p.state.usedNames.contains x = true) (V := fun _ => True) (dom := dom)
    (bi := binp) (vi := vinp) (ub := fun _ => True) (uv := fun _ => True) hb' hv'
    (fun _ _ => trivial) (fun _ _ => trivial) _ he (Uses.top _) "out" true p.state sm w tr st0
  have bodyEq : m.body = st.module.body.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  refine ⟨sm.module.body, w, ?_, hlp, fun l r hm' => stm.2.2.2.1 l r hm'⟩
  rw [bodyEq, ht, emitAssign_body_cons, List.reverse_cons]
  rfl

end Tools.ShippingHarnessSpine
