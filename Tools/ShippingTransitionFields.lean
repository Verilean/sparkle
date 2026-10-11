import Tools.ShippingMachineCloses

/-! # The transition's per-field read facts, for any split of the binders

The setup `transition_closes` builds for the `let` ports, as a theorem of its
own and for ANY split `bs = bsA ++ bsB` of the binders (no domain in `bsB`)
and ANY rule `ok k i` saying which ports of `bsB` field `k` may read: the
harness' module has the input ports `PI ++ ls` (`ls` those of `bsB`, in
order, distinct), its body is the builder's (reversed) and the final
`assign out`, and the per-field facts `LP` hold with "a port of `bsB` is read
only as `ok` allows". With `bsB` = the calls' outputs, the slots and the
`let`s, this covers the calls' output ports. -/
namespace Tools.ShippingTransitionFields
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
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingSpineOrder Tools.ShippingClosedOrder Tools.ShippingCloseLetsRun
open Tools.ShippingMachineCloses
open Sparkle.IR.Reorder

set_option maxHeartbeats 1000000 in
theorem transition_fields {logProf : String → IO Unit} {declName : Name}
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
      (fun j => inputExpr bs.length (vpos j)) (packLets fs core).2)
    {bsA bsB : List (Name × MixedGateBinder)} (hbs : bs = bsA ++ bsB)
    (letKinds : ∀ b ∈ bsB, b.2 ≠ .domain)
    -- which ports of `bsB` field `k` may read, and that the fields' variables obey it
    (ok : Nat → Nat → Prop) (hmono : ∀ k i, ok k i → ok (k + 1) i)
    {ubk uvk : Nat → Nat → Prop}
    (hub : ∀ k q, ubk k q → q < kb ∧ ∀ i, bpos q = bsA.length + i → ok k i)
    (huv : ∀ k q, uvk k q → q < kv ∧ ∀ i, vpos q = bsA.length + i → ok k i)
    (hscope : FieldsOK ubk uvk kb kv vw 0 fs)
    (hcoreU : Uses (ubk fs.length) (uvk fs.length) core) :
    ∃ (PI ls : List Port), m.inputs = PI ++ ls ∧ ls.length = bsB.length ∧
      (ls.map Port.name).Nodup ∧ (∀ p ∈ PI, ∀ q ∈ ls, p.name ≠ q.name) ∧
      (∃ ow, PrintBaseAt ow m) ∧ TypedPostReady m ∧
      ∃ (bodyB : List Stmt) (w : String) (P : String → Prop) (bnd : FVarId → Option String),
        m.body = bodyB.reverse ++ [.assign "out" (.ref w)] ∧
        LP P bnd (fun k x => ∀ (i : Nat) (p : Port), ls[i]? = some p → x = p.name → ok k i) bodyB 0
          (fs.map fun f => quote (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
            (fun j => .fvar (ids[bpos j]!)) (fun j => .fvar (ids[vpos j]!)) f.2) w ∧
        (∀ l r, Stmt.assign l r ∈ bodyB → ¬ P l) ∧ (∀ port ∈ m.inputs, P port.name) := by
  -- the run's facts about the module
  have facts := transition_facts nd len run hm nameLegal he hb hv hbody
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  have zero : SourceInputs declName bs ids cache (fun _ => false) (fun _ n => 0#n)
      (fun _ => 0) := admissible_zero _ _
  obtain ⟨_, _, _, ready, _, _, _, _, base⟩ := facts.1 _ _ _ (fun _ _ => 0) zero
  have pb := base positive
  have hin := facts.2.2 (boolValues ids fun _ => false) (bitValues ids fun _ n => 0#n)
  -- the port walk in two parts
  let a := start (entryCompilerState false cache) declName.toString
  let zb := boolValues ids fun _ => false
  let zv := bitValues ids fun _ n => 0#n
  let L1 := bsA.zip (ids.take bsA.length)
  let L2 := bsB.zip (ids.drop bsA.length)
  have hidsLen : ids.length = bsA.length + bsB.length := by rw [len, hbs, List.length_append]
  have hzip : bs.zip ids = L1 ++ L2 := by
    show bs.zip ids = bsA.zip (ids.take bsA.length) ++ bsB.zip (ids.drop bsA.length)
    conv => lhs; rw [hbs, ← List.take_append_drop bsA.length ids]
    rw [List.zip_append (by simp; omega)]
  have hL1 : L1.length = bsA.length := by simp [L1]; omega
  have hL2 : L2.length = bsB.length := by simp [L2]; omega
  have hL2dom : ∀ b ∈ L2, b.1.2 ≠ .domain := fun b hb' => letKinds b.1 (List.of_mem_zip hb').1
  let PI := inputPorts zb zv L1 a
  let ls := inputPorts zb zv L2 (prepare zb zv L1 a)
  have hinputs : m.inputs = PI ++ ls := by
    rw [hin, hzip, inputPorts_append]
  have lsTypes := inputPorts_types (bools := zb) (bits := zv) L2 (prepare zb zv L1 a) hL2dom
  have lsLen : ls.length = bsB.length := by rw [lsTypes.length_eq, hL2]
  have hdrop : m.inputs.drop (m.inputs.length - bsB.length) = ls := by
    rw [hinputs, List.length_append, lsLen, Nat.add_sub_cancel, List.drop_left]
  have inNodup : ((PI ++ ls).map Port.name).Nodup := hinputs ▸ pb.inputNames
  rw [List.map_append, List.nodup_append] at inNodup
  have ndz : ((L1 ++ L2).map Prod.snd).Nodup := hzip ▸ fresh
  -- where a term variable is bound
  have hwhere : ∀ (pos : Nat) (binder : Name × MixedGateBinder), bs[pos]? = some binder →
      binder.2 ≠ .domain → ∀ z,
      visible (prepare zb zv (bs.zip ids) a).context
        (prepare zb zv (bs.zip ids) a).state.sourceBindings ids[pos]! = some z →
      (pos < bsA.length ∧ ∃ port ∈ PI, z = port.name) ∨
        (∃ i port, pos = bsA.length + i ∧ ls[i]? = some port ∧ z = port.name) := by
    intro pos binder hpos hk z hz
    have hmem : (L1 ++ L2)[pos]? = some (binder, ids[pos]!) := by
      rw [← hzip]
      have bound : pos < bs.length := (List.getElem?_eq_some_iff.mp hpos).1
      exact List.getElem?_zip_eq_some.mpr ⟨hpos, by
        simp [List.getElem?_eq_getElem (show pos < ids.length by omega),
          List.getElem!_eq_getElem?_getD]⟩
    rw [hzip] at hz
    rcases bound_where (bools := zb) (bits := zv) L1 L2 a ndz hL2dom
      (by rw [lsTypes.length_eq]) hmem hk with ⟨hlt, port, hp, hv'⟩ | ⟨i, port, hi, hp, hv'⟩
    · rw [hv'] at hz
      cases hz
      exact Or.inl ⟨hL1 ▸ hlt, port, hp, rfl⟩
    · rw [hv'] at hz
      cases hz
      exact Or.inr ⟨i, port, hL1 ▸ hi, hp, rfl⟩
  have lsNodup : (ls.map Port.name).Nodup := inNodup.2.1
  have lsDisj : ∀ p ∈ PI, ∀ q ∈ ls, p.name ≠ q.name := fun p hp q hq =>
    inNodup.2.2 p.name (List.mem_map_of_mem hp) q.name (List.mem_map_of_mem hq)
  -- the ports a position may read: not the `let` ports from it on
  let Vk : Nat → String → Prop := fun k x => ∀ (i : Nat) (p : Port), ls[i]? = some p → x = p.name → ok k i
  have hbind : ∀ k id z,
      Bk (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) ubk uvk k id →
      visible (prepare zb zv (bs.zip ids) a).context
        (prepare zb zv (bs.zip ids) a).state.sourceBindings id = some z → Vk k z := by
    rintro k id z (⟨q, hu, rfl⟩ | ⟨q, hu, rfl⟩) hz i p hp heq
    · obtain ⟨name, hbq⟩ := hb q (hub k q hu).1
      rcases hwhere (bpos q) (name, .bool) hbq (by simp) z hz with
        ⟨-, port, hport, rfl⟩ | ⟨i', port, hi', hpi, rfl⟩
      · exact absurd heq (lsDisj port hport p (List.mem_of_getElem? hp))
      · have := nodup_index lsNodup hpi hp heq
        subst this
        exact (hub k q hu).2 i' hi'
    · obtain ⟨name, hvq⟩ := hv q (huv k q hu).1
      rcases hwhere (vpos q) (name, .bits (vw q)) hvq (by simp) z hz with
        ⟨-, port, hport, rfl⟩ | ⟨i', port, hi', hpi, rfl⟩
      · exact absurd heq (lsDisj port hport p (List.mem_of_getElem? hp))
      · have := nodup_index lsNodup hpi hp heq
        subst this
        exact (huv k q hu).2 i' hi'
  subst hbody
  obtain ⟨bodyB, w', hbody', hlp, hnw, hused⟩ := harness_links_at run hm zb zv (fun _ => 0) zero
    (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
    kb kv vw (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) (fun _ => false) (fun _ n => 0#n)
    fs core he
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
    (Vk := Vk) (fun k x h i p hp heq => hmono k i (h i p hp heq)) hbind hscope hcoreU
  refine ⟨PI, ls, hinputs, lsLen, lsNodup, lsDisj, ⟨_, pb⟩, ready, bodyB, w', _, _, hbody', hlp, hnw, ?_⟩
  intro port hp
  apply hused
  rw [prepare_inputs, ← hin]
  simp only [start, CircuitM.init, Module.empty, List.append_nil, List.mem_reverse]
  exact hp

end Tools.ShippingTransitionFields
