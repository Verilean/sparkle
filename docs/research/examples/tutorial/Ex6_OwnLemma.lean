-- Tutorial example 6: the local-lemma path that exists in this snapshot.
--
-- There is NO entry point that lets a user hand a lemma to `#ved_u1` (or any other
-- `#ved_*` entry) so that the automatic proof uses it. What a user CAN do, and what this
-- file checks, is to use the accepted theorem as a lemma in their own Lean development:
-- state a fact about the returned module and prove it from `delay8.ved_u1`.
-- Run from the repository root:
--   lake build Tools.VedU1Entry
--   lake env lean docs/research/examples/tutorial/Ex6_OwnLemma.lean ; echo "exit $?"
import Tools.VedU1Entry

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Semantics Tools.VedU1Contract

def delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0#8 x

#ved_u1 delay8

/-- info: 'delay8.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms delay8.ved_u1

/-- A user's own lemma about the SOURCE (ordinary Lean, no entry involved). -/
theorem delay8_succ (x : Signal defaultDomain (BitVec 8)) (t : Nat) :
    (delay8 x).val (t + 1) = x.val t := rfl

/-- A user's own lemma about the RETURNED MODULE, proved from the accepted theorem
`delay8.ved_u1` (its fifth conjunct, the order-free output statement): on every admissible
input stream, the output of the module's run at time t+1 is the input at time t.
The reset is held at 0 and the data input fits 8 bits: that is `InputsOk`. -/
theorem delay8_ir (ins : Nat → String → Nat)
    (hok : InputsOk delay8.ved_contract delay8.ved_mod ins) (K t : Nat) (ht : t + 1 < K) :
    ∃ envs, runModule (declWidth delay8.ved_mod) delay8.ved_mod.body
        (seedFwd delay8.ved_mod K ins) K (st0 delay8.ved_contract delay8.ved_mod)
        (fun _ _ => 0) = some envs ∧
      ∃ env, envs[t + 1]? = some env ∧ env "out" = ins t "_gen_x" := by
  have hwo : Sparkle.IR.Reorder.woCheck [] delay8.ved_mod.body = true := by decide
  obtain ⟨envs, hrun, hall⟩ := outputs_body delay8.ved_u1.2.2.2.2 hwo ins hok K
  refine ⟨envs, hrun, ?_⟩
  have hmem : (⟨"out", .bitVector 8⟩ : Sparkle.IR.AST.Port) ∈ delay8.ved_contract.outputs :=
    List.Mem.head _
  obtain ⟨env, he, hv⟩ := hall (t + 1) ht _ hmem
  refine ⟨env, he, ?_⟩
  have hb : ins t "_gen_x" < 2 ^ 8 := hok.1 t _ (List.Mem.head _)
  rw [hv]
  simp only [srcOf]
  simp [delay8.ved_contract, contractOf, applyIns, delay8, Signal.register, PTy.sig, PTy.obs,
    OTy.obs, List.zip]
  omega

/-- info: 'delay8_ir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms delay8_ir
