/-
  `#verify_elab` prototype — closing the LAST open link in the chain.

  User proofs about a `circuit do` definition are statements about the
  Signal shallow semantics (`Signal.loop`'s pure fixpoint).  The M0–M4
  certified statements are about the IR semantics (`evalExpr` /
  `runModule`).  The elaborator between them was TESTED, never proven:
  `#verify_emit` and `#verify_dsl_roundtrip` are both IR↔IR
  congruences, and neither the IR semantics nor the elaborator mention
  `Signal` at all.

  This file proves the link end to end for one circuit, by hand, as
  the feasibility prototype for a `#verify_elab` command:

  * `accEn_zero` / `accEn_step` — the Signal-level cycle recurrence,
    derived from `Signal.loopGo_eq` and the primitive definitions.
    The recipe is circuit-independent:
    `simp only [name, runCircuitH, Signal.loop, Signal.map]`, then ONE
    `rw [Signal.loopGo_eq]` (it self-loops inside `simp`), then `simp`
    over the plumbing with `by_cases` on the conditions.
  * `bridge` — the elaborated register-input cone (verbatim from
    `synthesizeHierarchical`, zero-width HList plumbing included),
    under the PROVEN `evalExpr`, computes exactly that step function.
    Landing on `evalExpr` rather than a goal-generation reflector keeps
    the M4 semantics as the single meaning of the IR.
  * `accEn_elab_trace` — the IR register trace equals the Signal trace
    at every cycle, by induction with BitVec.isLt discharging the
    bridge's bounds.

  What a real `#verify_elab` adds: generating the cone by inlining
  (VerifyEmit's machinery), generating the step lemma and bridge goals,
  and the `envAt`-to-`runModule` settle link (structurally
  `emit_sem_assigns`).  No new mathematics is required — this file is
  the evidence.
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Sparkle.IR.AST Sparkle.IR.Semantics

def accEn (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    acc <~ Signal.mux (en.map (· == 1#1)) (acc + d) acc
    return acc

/- The elaborated register-input cone, inlined over {register, inputs}
   exactly as the elaborator laid it down (including the zero-width
   concat plumbing from the HList state). -/
def cone : Expr :=
  .op .mux
    [ .op .eq [.ref "_gen_en", .const 1 1]
    , .op .add
        [ .slice (.concat [.ref "_tmp_a_5", .const 0 0]) 3 0
        , .ref "_gen_d" ]
    , .slice (.concat [.ref "_tmp_a_5", .const 0 0]) 3 0 ]

def weM : WEnv := fun n =>
  if n == "_tmp_a_5" then 4 else if n == "_gen_d" then 4
  else if n == "_gen_en" then 1 else 0

/- THE BRIDGE: the IR cone under the proven semantics computes exactly
   the Signal step function, value for value. -/
theorem bridge (aV enV dV : Nat)
    (ha : aV < 16) (hen : enV < 2) (hd : dV < 16) :
    evalExpr weM
      (fun n => if n == "_tmp_a_5" then aV
        else if n == "_gen_d" then dV
        else if n == "_gen_en" then enV else 0)
      cone
    = some (if enV = 1 then (aV + dV) % 16 else aV) := by
  simp [cone, evalExpr, evalList, evalOp, weM, mask,
    Sparkle.IR.Semantics.widthOf, evalExpr.go]
  rw [Nat.mod_eq_of_lt ha]

/- Signal-side lemmas (proven in velab2; restated here for a
   self-contained file). -/
theorem accEn_zero (en d) : (accEn en d).val 0 = 0#4 := by
  simp only [accEn, runCircuitH, Signal.loop, Signal.map]
  rw [Signal.loopGo_eq]
  simp [packRegister, Signal.register, Signal.mux, Signal.map,
    bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq]

theorem accEn_step (en d) (t : Nat) :
    (accEn en d).val (t+1)
    = if en.val t == 1#1
      then (accEn en d).val t + d.val t
      else (accEn en d).val t := by
  simp only [accEn, runCircuitH, Signal.loop, Signal.map]
  rw [Signal.loopGo_eq]
  simp [packRegister, Signal.register, Signal.mux, Signal.map,
    bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq,
    Nat.lt_succ_iff]
  by_cases hc : en.val t = 1#1 <;>
    simp [hc, HAdd.hAdd, Functor.map, Seq.seq, Signal.ap, Signal.seq,
      Signal.map]

/- The IR register trace, as the recurrence the proven semantics
   induces: state 0 is the init, state (t+1) is the cone evaluated in
   the cycle-t environment. -/
def envAt (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) (s t : Nat) : Env :=
  fun n => if n == "_tmp_a_5" then s
    else if n == "_gen_d" then (d.val t).toNat
    else if n == "_gen_en" then (en.val t).toNat else 0

def irTrace (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) : Nat → Nat
  | 0 => 0
  | t+1 => (evalExpr weM (envAt en d (irTrace en d t) t) cone).getD 0

/-- **The end-to-end statement**: the elaborated IR's register trace
    under the PROVEN semantics equals the Signal-level trace of the
    `circuit do` definition, at every cycle. -/
theorem accEn_elab_trace (en d) (t : Nat) :
    irTrace en d t = ((accEn en d).val t).toNat := by
  induction t with
  | zero => simp [irTrace, accEn_zero]
  | succ n ih =>
    have hlt : ((accEn en d).val n).toNat < 16 :=
      ((accEn en d).val n).isLt
    have henlt : ((en.val n).toNat) < 2 := (en.val n).isLt
    have hdlt : ((d.val n).toNat) < 16 := (d.val n).isLt
    rw [irTrace, ih]
    unfold envAt
    rw [bridge _ _ _ hlt henlt hdlt]
    rw [accEn_step]
    by_cases hc : en.val n = 1#1
    · simp [hc, BitVec.toNat_add]
    · have : ¬((en.val n).toNat = 1) := by
        intro h
        exact hc (BitVec.eq_of_toNat_eq (by simpa using h))
      simp [hc, this]
