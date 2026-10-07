import Sparkle.Core.Signal
import Sparkle.IR.Semantics
import Tools.SVParser.Lower

/-!
Proof-carrying acceptance for the shared route.  The observable semantics here
is explicitly the SHIPPING PARSER followed by IR execution, not independent
SystemVerilog semantics.  No claim of correctness or completeness of the DSL
reifier, parser, printer, or optimizer is made by this module.

A successful result must carry all three replay proofs and the parse equality.
The soundness theorem composes the parse equality with replay, for every input
trace supplied by a caller and every finite observation horizon.  In particular,
an earlier PROVEN line or a skipped text bridge is not an acceptance certificate.
-/

namespace Tools.CertifiedRoundtrip

open Sparkle.IR.AST Sparkle.IR.Semantics

/-- The observation of the supported single BitVec output. -/
def observe {dom : Sparkle.Core.Domain.DomainConfig} {w : Nat}
    (s : Sparkle.Core.Signal.Signal dom (BitVec w)) : Nat → Nat :=
  fun t => (s.val t).toNat

/-- Exactly the body projection used by the shared generator's parse theorem. -/
def parseBody (text : String) : Except String (List Stmt) :=
  (Tools.SVParser.Lower.parseAndLowerHierarchical text).map
    (fun d => d.modules.foldl (fun acc m => acc ++ m.body) [])

/-- Total success and output agreement, with the existing generator's seeding
discipline. `seed` is indexed by chronological time; `runModule` counts down. -/
def RunCorrect (source : Nat → Nat) (we : WEnv) (body : List Stmt)
    (seed : Nat → Env → Env) (initial : Env) (port : String) : Prop :=
  ∀ K, ∃ envs,
    runModule we body (fun td s => seed (K - 1 - td) s) K initial (fun _ _ => 0)
      = some envs ∧
    ∀ t, t < K → ∃ env, envs[t]? = some env ∧ source t = env port

/-- Lift a whole-step preservation theorem through the shipping runner. This
includes register and memory updates, not only combinational output equality. -/
theorem runModule_congr_step (we : WEnv) (a b : List Stmt)
    (same : ∀ env mems, stepModule we a env mems = stepModule we b env mems)
    (seed : Nat → Env → Env) (K : Nat) (st : Env) (mems : MEnv) :
    runModule we a seed K st mems = runModule we b seed K st mems := by
  induction K generalizing st mems with
  | zero => rfl
  | succ k ih =>
    simp only [runModule, same]
    cases h : stepModule we b (seed k st) mems with
    | none => rfl
    | some result =>
      change ((runModule we a seed k (applyNexts st result.2.1) result.2.2).bind _) =
        ((runModule we b seed k (applyNexts st result.2.1) result.2.2).bind _)
      rw [ih]

theorem RunCorrect.of_stepEq {source : Nat → Nat} {we : WEnv}
    {a b : List Stmt} {seed : Nat → Env → Env} {initial : Env} {port : String}
    (h : RunCorrect source we a seed initial port)
    (same : ∀ env mems, stepModule we a env mems = stepModule we b env mems) :
    RunCorrect source we b seed initial port := by
  intro K
  obtain ⟨envs, hr, ho⟩ := h K
  exact ⟨envs, (runModule_congr_step we a b same _ K initial _).symm.trans hr, ho⟩

/-- Run the exact certified bytes through the shipping parser, then the IR
semantics. Both parser failure and execution failure are explicit failures. -/
def runText (text : String) (we : WEnv) (seed : Nat → Env → Env)
    (initial : Env) (K : Nat) : Except String (List Env) :=
  match parseBody text with
  | .error err => .error err
  | .ok body =>
    match runModule we body (fun td s => seed (K - 1 - td) s) K initial (fun _ _ => 0) with
    | some envs => .ok envs
    | none => .error "certified roundtrip: IR execution failed"

/-- An accepted artifact, tied to a particular source observation. Mandatory
proof fields deliberately leave no representation of a partially accepted chain.
The seed and width environment are part of the contract, not arbitrary SV inputs.
-/
structure Certificate (source : Nat → Nat) where
  text : String
  widths : WEnv
  seed : Nat → Env → Env
  initial : Env
  port : String
  original : List Stmt
  optimized : List Stmt
  reparsed : List Stmt
  original_correct : RunCorrect source widths original seed initial port
  optimized_correct : RunCorrect source widths optimized seed initial port
  parses : parseBody text = .ok reparsed
  reparsed_correct : RunCorrect source widths reparsed seed initial port

/-- Adapter for the existing generated declarations; all body identities and
execution parameters are inferred from their theorem types, not from logs. -/
def ofReplay {source : Nat → Nat} {we : WEnv} {seed : Nat → Env → Env}
    {initial : Env} {port : String} {original optimized reparsed : List Stmt}
    (text : String) (parses : parseBody text = .ok reparsed)
    (hOriginal : RunCorrect source we original seed initial port)
    (hOptimized : RunCorrect source we optimized seed initial port)
    (hReparsed : RunCorrect source we reparsed seed initial port) : Certificate source :=
  ⟨text, we, seed, initial, port, original, optimized, reparsed,
    hOriginal, hOptimized, parses, hReparsed⟩

/-- General semantic preservation for EVERY accepted roundtrip artifact, not
just the test corpus. The parser remains the explicit interpretation of text. -/
theorem Certificate.sound {source : Nat → Nat} (c : Certificate source) (K : Nat) :
    ∃ envs, runText c.text c.widths c.seed c.initial K = .ok envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧ source t = env c.port := by
  obtain ⟨envs, hrun, hout⟩ := c.reparsed_correct K
  refine ⟨envs, ?_, hout⟩
  simp [runText, c.parses, hrun]

/-- A failing producer has no accepted artifact. This theorem applies even to
an unverified producer: its success type must carry the kernel-checked evidence.
It does not establish that production terminates or succeeds on every DSL term. -/
theorem accepted_sound {Input : Type} (source : Input → Nat → Nat)
    (produce : (i : Input) → Except String (Certificate (source i)))
    (i : Input) (c : Certificate (source i)) (_accepted : produce i = .ok c)
    (K : Nat) :
    ∃ envs, runText c.text c.widths c.seed c.initial K = .ok envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧ source i t = env c.port :=
  c.sound K

end Tools.CertifiedRoundtrip
