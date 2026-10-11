import Tools.ShippingCallsAssembly
import Tools.ShippingTransitionClosed

/-! # The transition's facts for the one-output closing, from a harness run

Everything `closeInsts_of_facts` asks of the transition, for a run of the
harness on a packed machine body whose binders are the declaration's, then
the calls' outputs, the slots and the `let`s (`bsB`), under the shape
condition S3 (`okRule`): the ports, the body and its order, allocated names,
the per-`let` facts of whatever `letOperands` returns, the empty design and
the module's name. No closing fact is assumed. -/
namespace Tools.ShippingCallsRun
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

open Tools.ShippingRankRun Tools.ShippingTransitionFields Tools.ShippingTransitionClosed
open Tools.ShippingCloseMachineFacts (named_of_typed)
open Tools.ShippingMachineClose (concatParts?_mem)
open Sparkle.IR.NameHints (Allocated)

theorem okRule_mono {kI n : Nat} {cs : List Nat} {k idx : Nat} (h : okRule kI n cs k idx) :
    okRule kI n cs (k + 1) idx :=
  ⟨fun hlt => by
      obtain ⟨c, hc, hle⟩ := h.1 hlt
      exact ⟨c, hc, by omega⟩,
    fun hge => by
      have := h.2 hge
      omega⟩

set_option maxHeartbeats 2000000 in
theorem transition_calls_facts {logProf : String → IO Unit} {declName : Name}
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
    {kI n K : Nat} {cs : List Nat} (hBlen : bsB.length = kI + n + K)
    (hfsK : fs.length = K)
    (hscope : FieldsOK (fun k q => q < kb ∧ ∀ idx, bpos q = bsA.length + idx → okRule kI n cs k idx)
      (fun k q => q < kv ∧ ∀ idx, vpos q = bsA.length + idx → okRule kI n cs k idx) kb kv vw 0 fs)
    (hcoreU : Uses (fun q => q < kb ∧ ∀ idx, bpos q = bsA.length + idx → okRule kI n cs fs.length idx)
      (fun q => q < kv ∧ ∀ idx, vpos q = bsA.length + idx → okRule kI n cs fs.length idx) core) :
    ∃ (PI ls : List Port) (bodyB : List Stmt) (w : String) (P : String → Prop)
        (bnd : FVarId → Option String),
      m.inputs = PI ++ ls ∧ PI.length = (bsA.filter fun b => b.2 != .domain).length ∧
      ls.length = kI + n + K ∧ (m.inputs.map (·.name)).Nodup ∧ (∀ p ∈ m.inputs, p ∈ m.wires) ∧
      (∀ p ∈ m.wires, Allocated p.name) ∧
      m.body = bodyB.reverse ++ [.assign "out" (.ref w)] ∧ Acyclic m.body ∧
      (∀ l r, Stmt.assign l r ∈ bodyB.reverse → Allocated l ∧ ∀ x ∈ refsOf r, Allocated x) ∧
      (∀ l r, Stmt.assign l r ∈ bodyB → ¬ P l) ∧ (∀ p ∈ m.inputs, P p.name) ∧
      (∀ (al : List (Port × String)) (core' : String),
        letOperands m.body (m.inputs.drop (m.inputs.length - K)) w = some (al, core') →
        ∃ es ws, Facts P bnd
          (fun i x => ∀ (idx : Nat) (p : Port), ls[idx]? = some p → x = p.name →
            okRule kI n cs i idx)
          m.wires m.body bodyB 0 al es ws ∧ al.map (·.1) = ls.drop (kI + n) ∧ Allocated core') ∧
      st.design = (CircuitM.init declName.toString).design ∧ m.name = declName.toString := by
  obtain ⟨B, w1, hB, hspine, -, -⟩ :=
    transition_spine nd len run hm nameLegal positive fs core he hb hv hbody
  obtain ⟨-, -, -, -, hdesign, hname⟩ :=
    transition_closed nd len run hm nameLegal positive (packLets fs core).2 he hb hv hbody
  obtain ⟨PI, ls, hin, hlsLen, hPI, hlsNd, hdisj, ⟨ow, pb⟩, ready, bodyB, w, P, bnd, hbody', hlp, hnw,
      hPin⟩ :=
    transition_fields nd len run hm nameLegal positive fs core he hb hv hbody hbs letKinds
      (okRule kI n cs) (fun k i h => okRule_mono h) (fun k q h => h) (fun k q h => h) hscope hcoreU
  have hsame := hB.symm.trans hbody'
  obtain ⟨hBeq, hweq⟩ := List.append_inj' hsame rfl
  cases hweq
  obtain ⟨hnamed, hwA⟩ := named_of_typed hbody' pb.order ready.typed pb.wireNames
  have hlen' : ls.length = kI + n + K := hlsLen.trans hBlen
  have hdropEq : m.inputs.drop (m.inputs.length - K) = ls.drop (kI + n) := by
    rw [hin, List.length_append, hlen', show PI.length + (kI + n + K) - K = PI.length + (kI + n) by omega,
      List.drop_append, List.drop_eq_nil_of_le (by omega), Nat.add_sub_cancel_left, List.nil_append]
  have hsub : ∀ stmt ∈ bodyB, stmt ∈ m.body := fun stmt hs => by
    rw [hbody']
    exact List.mem_append_left _ (List.mem_reverse.mpr hs)
  obtain ⟨al0, core0, hlo, hmap, hfacts, hcore⟩ := letOperands_facts pb.order hsub (ls.drop (kI + n))
    (fs.map (·.1)) _ 0 w1 (by simp [hlen', hfsK]) hspine hlp (by simp)
  refine ⟨PI, ls, bodyB, w1, P, bnd, hin, hPI, hlen', pb.inputNames, pb.inputWires, pb.wireNames,
    hbody', pb.order, hnamed, hnw, hPin, ?_, hdesign, hname⟩
  intro al core' hops
  rw [hdropEq, hlo] at hops
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hops)
  rw [← h1, ← h2]
  refine ⟨_, _, hfacts, hmap, ?_⟩
  -- without a `let` the core is the packed wire itself
  by_cases hfs : fs = []
  · subst hfs
    have hl0 : ls.drop (kI + n) = [] := by
      apply List.drop_eq_nil_of_le
      simp only [List.length_nil] at hfsK
      omega
    rw [hl0] at hlo
    simp only [letOperands, Option.some.injEq, Prod.mk.injEq] at hlo
    rw [← hlo.2]
    exact hwA
  obtain ⟨x, a, hcp⟩ := hcore (by
    intro h
    have := congrArg List.length h
    simp only [List.length_map, List.length_nil] at this
    exact hfs (List.length_eq_zero_iff.mp this))
  have hm' := concatParts?_mem hcp
  rw [hbody'] at hm'
  rcases List.mem_append.mp hm' with hm' | hm'
  · exact (hnamed _ _ hm').2 core0 (by simp [refsOf, refsOf.refsList])
  · simp at hm'

end Tools.ShippingCallsRun
