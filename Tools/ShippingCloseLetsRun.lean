import Tools.ShippingMachineEntry
import Tools.ShippingHarnessSpine
import Tools.ShippingCloseLetsSplit

/-! # `closeLets`' conditions, from a run of the harness

For a machine shape the transition's source is `packLets fs core`: one
concatenation per `let` field around the core. From ANY run of the certified
harness on it (`transition_spine`):

* condition (1): the returned body ends in `assign out = w`;
* condition (2): from `w`, the spine `letOperands` walks — one
  two-operand concatenation per `let` field.

The translator's expression links (`harness_spine_at`) are membership facts;
that the statement found FIRST by `concatParts?` is that one is the order
invariant of the returned body (`Acyclic`: one driver per wire), which the
harness' soundness already gives. Nothing about the run is assumed beyond
its being a run. -/
namespace Tools.ShippingCloseLetsRun
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.IR.Machine Sparkle.IR.Type
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose Tools.ShippingMachineTrace
open Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSpine Tools.ShippingCloseLetsSplit Tools.ShippingHarnessSpine
open Tools.ShippingSettledSoundness (Acyclic)

/-- A statement driving another wire is not `w`'s link. -/
theorem concatParts?_cons_ne {l : String} {r : Sparkle.IR.AST.Expr} {rest : List Stmt} {w : String}
    (h : l ≠ w) : concatParts? (.assign l r :: rest) w = concatParts? rest w := by
  simp only [concatParts?, List.findSome?_cons]
  split
  · rename_i heq
    split at heq
    · rename_i heq2
      cases heq2
      simp [h] at heq
    · cases heq
  · rfl

/-- In an ordered body, the concatenation statement of `w` that is THERE is
the one `concatParts?` finds: `w` has no other driver. -/
theorem concatParts?_of_mem : ∀ {body : List Stmt} {w a b : String}, Acyclic body →
    link w a b ∈ body → concatParts? body w = some (a, b)
  | st :: rest, w, a, b, ho, hm => by
    cases ho with
    | cons ht hr ha =>
      rename_i l r
      rcases List.mem_cons.mp hm with heq | hin
      · unfold link at heq
        cases heq
        simp [concatParts?]
      · have hw : w ∈ Sparkle.IR.Reorder.writesOf rest := by
          unfold Sparkle.IR.Reorder.writesOf
          exact List.mem_flatMap.mpr ⟨_, hin, by simp [link, Sparkle.IR.Reorder.stmtWrites]⟩
        rw [concatParts?_cons_ne (fun (h : l = w) => ht (by rw [h]; exact hw))]
        exact concatParts?_of_mem ha hin

/-- **Condition (2) from the expression links**: in an ordered body, the links
of a packed term's expression are the spine `letOperands` walks, one link per
`let` field. -/
theorem spine_of_packLets {body : List Stmt} (ho : Acyclic body) {dom : Lean.Expr}
    {bi vi : Nat → Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} :
    ∀ (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)) (w : String),
      (packLets fs core).2.WF kb kv vw →
      (∀ n, SpineQ body n (quote dom bi vi (packLets fs core).2) w) → Spine body fs.length w
  | [], _, _, _, _, _ => trivial
  | f :: rest, c, core, w, hwf, hs => by
    obtain ⟨hf, hrest⟩ := hwf
    have hlo : concatLo? (quote dom bi vi (packLets (f :: rest) core).2) =
        some (quote dom bi vi (packLets rest core).2) :=
      concatLo?_concatE dom _ _ (f.2.wf_pos hf) ((packLets rest core).2.wf_pos hrest)
    obtain ⟨x, y, hm, -⟩ := hs 1 _ hlo
    refine ⟨x, y, concatParts?_of_mem ho hm, spine_of_packLets ho (dom := dom) (bi := bi) (vi := vi) rest core y hrest (fun n => ?_)⟩
    obtain ⟨x', y', hm', hr'⟩ := hs (n + 1) _ hlo
    have := (concatParts?_of_mem ho hm).symm.trans (concatParts?_of_mem ho hm')
    cases this
    exact hr'

/-- **Conditions (1) and (2) of `closeLets`, from a run of the harness** on a
packed machine body: the final `assign out = w`, and the spine from `w` with
one link per `let` field. -/
theorem transition_spine {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr} {m : Sparkle.IR.AST.Module}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {returned : String}
    {st : CircuitState}
    (nd : ids.Nodup) (len : ids.length = bs.length)
    (run : Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids))
        (entryCompilerState false cache) (CircuitM.init declName.toString) returned st)
    (hm : m = (addClockResetIfSequential st.module).finalize)
    (nameLegal : Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true)
    (positive : PositiveBinders bs)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c))
    (he : (packLets fs core).2.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom (fun j => inputExpr bs.length (bpos j))
      (fun j => inputExpr bs.length (vpos j)) (packLets fs core).2) :
    ∃ B w, m.body = B ++ [.assign "out" (.ref w)] ∧ Spine m.body fs.length w ∧
      ∀ port ∈ m.inputs, port.name ∉ Sparkle.IR.Reorder.writesOf m.body := by
  have facts := transition_facts nd len run hm nameLegal he hb hv hbody
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  have zero : SourceInputs declName bs ids cache (fun _ => false) (fun _ n => 0#n)
      (fun _ => 0) := admissible_zero _ _
  obtain ⟨_, _, _, _, simple, _, _, _, base⟩ := facts.1 _ _ _ (fun _ _ => 0) zero
  have order : Acyclic m.body := (base positive).order
  subst hbody
  have hin := facts.2.2 (boolValues ids fun _ => false) (bitValues ids fun _ n => 0#n)
  obtain ⟨B, w, hB, hsp, hnw⟩ := harness_spine_at run hm
    (boolValues ids fun _ => false) (bitValues ids fun _ n => 0#n) (fun _ => 0) zero
    (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
    kb kv vw (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) (fun _ => false) (fun _ n => 0#n)
    (packLets fs core).2 he
    (by
      intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      have bound := (List.getElem_of_getElem? pos).choose
      have lookup := prepare_bool_lookup (bools := boolValues ids fun _ => false)
        (bits := bitValues ids fun _ n => 0#n) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
      simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup)
    (by
      intro j hj
      obtain ⟨name, pos⟩ := hv j hj
      have bound := (List.getElem_of_getElem? pos).choose
      have lookup := prepare_bits_lookup (bools := boolValues ids fun _ => false)
        (bits := bitValues ids fun _ n => 0#n) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
      simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup)
    (by
      apply instantiated_quote _ _ _ he
      · intro j hj
        obtain ⟨name, pos⟩ := hb j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose
      · intro j hj
        obtain ⟨name, pos⟩ := hv j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose)
  refine ⟨B, w, hB, spine_of_packLets order fs core w he hsp, fun port hp hw => ?_⟩
  -- condition (4): an input port is driven by no statement
  unfold Sparkle.IR.Reorder.writesOf at hw
  obtain ⟨stmt, hs, hl⟩ := List.mem_flatMap.mp hw
  obtain ⟨l, r, rfl, -⟩ := simple stmt hs
  have hport : port ∈ (prepare (boolValues ids fun _ => false) (bitValues ids fun _ n => 0#n)
      (bs.zip ids) (start (entryCompilerState false cache) declName.toString)).state.module.inputs := by
    rw [prepare_inputs, ← hin]
    simp only [start, CircuitM.init, Module.empty, List.append_nil, List.mem_reverse]
    exact hp
  have hl' : port.name = l := by simpa [Sparkle.IR.Reorder.stmtWrites] using hl
  exact hnw port hport l r hs hl'.symm

end Tools.ShippingCloseLetsRun
