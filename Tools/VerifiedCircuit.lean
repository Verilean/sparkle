import Tools.VerifiedState
import Sparkle.Core.CircuitMonad

/-! The shipping single-register circuit runner connected to the verified
state compiler. The body obligation is POINTWISE for every possible live signal:
it cannot assume a loop trace or a finished replay theorem. Extracting this
obligation from arbitrary surface syntax is still outside this module. -/

namespace Tools.VerifiedCircuit

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.VerifiedBlock Tools.VerifiedState Tools.CertifiedRoundtrip

abbrev Body (dom : DomainConfig) (r w : Nat) :=
  RegList dom (HList [BitVec r]) (Circuit.SigList dom [BitVec r]) [BitVec r] →
    Circuit dom (Circuit.SigList dom [BitVec r]) (Signal dom (BitVec w))

/-- Exactly the registers and hold accumulator used by runCircuitH. -/
def evaluateBody {dom r w} (body : Body dom r w)
    (live : Signal dom (HList [BitVec r])) :=
  body (mkRegList live [BitVec r] (fun s => s) (fun f => f))
    (mkHolds [BitVec r] live)

/-- Correspondence of one combinational body. The pending write includes the
sampled reset mux, while the output observes the live (old) register value.
Quantifying over EVERY live signal excludes hidden dependencies on earlier or
later register values relative to the declared input trace. -/
def BodyMatches {dom Γ r w} (m : Machine Γ r w) (body : Body dom r w)
    (inputs : Nat → CEnv Γ) (reset : Nat → Bool) : Prop :=
  ∀ (live : Signal dom (HList [BitVec r])) t,
    (evaluateBody body live).1.val t =
      (m.step.denote (pushValue (live.val t).1 (inputs t))).2 ∧
    (evaluateBody body live).2.1.val t =
      (if reset t then m.init else
        (m.step.denote (pushValue (live.val t).1 (inputs t))).1)

/-- General bridge for the actual runner emitted by circuit do. Neither its
loop nor its register semantics is replaced with a custom execution function. -/
theorem runCircuitH_eq {dom Γ r w} (m : Machine Γ r w) (body : Body dom r w)
    (inputs : Nat → CEnv Γ) (reset : Nat → Bool)
    (hbody : BodyMatches m body inputs reset) (t : Nat) :
    (runCircuitH (αs := [BitVec r]) (m.init, ()) body).val t =
      (m.step.denote (pushValue (m.state inputs reset t) (inputs t))).2 := by
  let F : Signal dom (HList [BitVec r]) → Signal dom (HList [BitVec r]) :=
    fun live => packRegister [BitVec r] (m.init, ()) (evaluateBody body live).2
  have state_eq : ∀ u, (Signal.loop F).val u = (m.state inputs reset u, ()) := by
    apply loop_trace
    intro u pre hpre
    cases u with
    | zero => rfl
    | succ n =>
      change ((evaluateBody body pre).2.1.val n, ()) = _
      rw [(hbody pre n).2, hpre n (Nat.lt_succ_self n)]
      rfl
  change (evaluateBody body (Signal.loop F)).1.val t = _
  rw [(hbody (Signal.loop F) t).1, state_eq t]

theorem observe_runCircuitH {dom Γ r w} (m : Machine Γ r w) (body : Body dom r w)
    (inputs : Nat → CEnv Γ) (reset : Nat → Bool)
    (hbody : BodyMatches m body inputs reset) :
    observe (runCircuitH (αs := [BitVec r]) (m.init, ()) body) =
      m.observe inputs reset := by
  funext t
  exact congrArg BitVec.toNat (runCircuitH_eq m body inputs reset hbody t)

/-- Source-to-IR correctness for the shipping runner. All cycles follow from
the compiler theorem and pointwise body correspondence; no per-circuit induction,
SAT certificate, native_decide obligation, or replay hypothesis is required. -/
theorem compileChecked_signal_sound {dom Γ r w} (m : Machine Γ r w)
    (source : Body dom r w) (inputs : Nat → CEnv Γ) (reset : Nat → Bool)
    (hbody : BodyMatches m source inputs reset)
    (we : WEnv) (names : Fin Γ.length → String) (l : Layout)
    (ir : List Stmt) (accepted : m.compileChecked we names l = .ok ir)
    (seed : Nat → Env → Env) (initial : Env)
    (hseed : m.SeedCorrect names l inputs reset seed) (hinit : initial l.reg = m.init.toNat) :
    RunCorrect (observe (runCircuitH (αs := [BitVec r]) (m.init, ()) source))
      we ir seed initial l.output := by
  rw [observe_runCircuitH m source inputs reset hbody]
  exact m.compileChecked_sound we names l ir accepted inputs reset seed initial hseed hinit

/-- An artifact whose indexed source is the real circuit runner. Downstream
evidence is still explicit, as in Machine.certify. -/
def certifyCircuit {dom Γ r w} (m : Machine Γ r w)
    (source : Body dom r w) (inputs : Nat → CEnv Γ) (reset : Nat → Bool)
    (hbody : BodyMatches m source inputs reset)
    (we : WEnv) (names : Fin Γ.length → String) (l : Layout)
    (ir : List Stmt) (accepted : m.compileChecked we names l = .ok ir)
    (seed : Nat → Env → Env) (initial : Env)
    (hseed : m.SeedCorrect names l inputs reset seed) (hinit : initial l.reg = m.init.toNat)
    (text : String) (optimized reparsed : List Stmt)
    (parses : parseBody text = .ok reparsed)
    (hOpt : RunCorrect (m.observe inputs reset) we optimized seed initial l.output)
    (hRT : RunCorrect (m.observe inputs reset) we reparsed seed initial l.output) :
    Certificate (observe (runCircuitH (αs := [BitVec r]) (m.init, ()) source)) :=
  ofReplay text parses
    (compileChecked_signal_sound m source inputs reset hbody we names l ir accepted
      seed initial hseed hinit)
    (by rw [observe_runCircuitH m source inputs reset hbody]; exact hOpt)
    (by rw [observe_runCircuitH m source inputs reset hbody]; exact hRT)

end Tools.VerifiedCircuit
