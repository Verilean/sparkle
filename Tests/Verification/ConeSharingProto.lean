/-
  Cone-sharing prototype: the SHARED deep route on `shareX4`, hand-emitted
  in the shape the generator will produce (bench/cone-sharing/emit_shareW.py).

  `shareX_n` chains n wires each read twice, so the inlined cone grows as
  2^n.  On the current (inlined, `Cdo`) route this circuit FAILS at n=4:
  the Signal-side trace theorem hits the 1.6 M heartbeat limit (see the
  baseline table in docs/CertifiedRoundtrip-TODO.md).  On the `CdoW` route
  below every generated lemma is small and the trace theorem closes.

  The recipe, which the generator integration must reproduce:
  * a `CdoW` instance with one wire slot per shared wire;
  * per-wire readers `rw_k` and their one-step equations `rw_k_eq` (rfl,
    each the size of ONE wire's cone), the register step `rd0_succ` in
    terms of the wire readers (rfl), and `outS` (stateSig_eq + rfl);
  * the trace theorem: `rw [← CdoW.elab_general …]`, `congrArg BitVec.toNat`
    (not `congr 1`, whose rfl attempt times out), the usual stage-1 simp,
    then the wire equations as HYPOTHESES (`have f_k := rw_k_eq i m`) —
    never rewritten into the goal — and `bv_decide`, which treats the
    readers as atoms and bitblasts the conjunction linearly on the IR side.

  Both sides are LINEAR (2026-09-14): the DSL side keeps its `have` chain
  (`simp -zeta`), core `extract_lets` lifts it into named local
  definitions (descending, merging the duplicated chain), and per-wire
  `.val` equations tie each definition to its predecessor; the goal
  handed to `bv_decide` is 194 nodes (step case) and 40 nodes (output)
  at n = 4, 8 and 12 alike — measured with a goal-size probe
  (`shareW_trace_lin_diag.tpl`).

  Measured 2026-09-14 (n=4): PROVEN in ~4 s, `lake env lean`, MemoryMax=24G,
  maxHeartbeats 1,600,000 (the generator's own trace-theorem limit, so the
  comparison with the inlined route is at equal limits).  No `sorry`
  fallback: an unclosed goal is a hard error.
-/
import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Tools.DeepElab
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core Tools.DeepElab
set_option maxRecDepth 65536
namespace Sparkle.Tests.ShareW
def shareX4 (i : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    let w0 := a + i
    let w1 := (w0 + w0) ^^^ i
    let w2 := (w1 + w1) ^^^ i
    let w3 := (w2 + w2) ^^^ i
    let w4 := (w3 + w3) ^^^ i
    r <~ w4 + w3
    return w4

/-! hand-emitted SHARED deep route (prototype of the generator's output) -/
def nm : Fin (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).length → String := fun i =>
  match i with
    | ⟨0, _⟩ => "r"
    | ⟨1, _⟩ => "i"
    | ⟨2, _⟩ => "w0"
    | ⟨3, _⟩ => "w1"
    | ⟨4, _⟩ => "w2"
    | ⟨5, _⟩ => "w3"
    | ⟨6, _⟩ => "w4"
def inp (i : Signal defaultDomain (BitVec 8)) :
    ∀ j : Fin ([8] : List Nat).length, Signal defaultDomain (BitVec (([8] : List Nat).get j)) :=
  fun j => match j with | ⟨0, _⟩ => i
theorem inp_at_0 (i : Signal defaultDomain (BitVec 8)) (tv : Nat) : (inp i 0).val tv = i.val tv := rfl
theorem inp_at_mk_0 (i : Signal defaultDomain (BitVec 8)) (tv : Nat) : (inp i ⟨0, by decide⟩).val tv = i.val tv := rfl

def deep : CdoW [8] [8] [8, 8, 8, 8, 8] 8 where
  inits := fun i => match i with | ⟨0, _⟩ => 0#8
  wires := fun j => match j with
    | ⟨0, _⟩ => CExpr.add (CExpr.var ⟨0, by decide⟩) (CExpr.var ⟨1, by decide⟩)
    | ⟨1, _⟩ => CExpr.xor (CExpr.add (CExpr.var ⟨2, by decide⟩) (CExpr.var ⟨2, by decide⟩)) (CExpr.var ⟨1, by decide⟩)
    | ⟨2, _⟩ => CExpr.xor (CExpr.add (CExpr.var ⟨3, by decide⟩) (CExpr.var ⟨3, by decide⟩)) (CExpr.var ⟨1, by decide⟩)
    | ⟨3, _⟩ => CExpr.xor (CExpr.add (CExpr.var ⟨4, by decide⟩) (CExpr.var ⟨4, by decide⟩)) (CExpr.var ⟨1, by decide⟩)
    | ⟨4, _⟩ => CExpr.xor (CExpr.add (CExpr.var ⟨5, by decide⟩) (CExpr.var ⟨5, by decide⟩)) (CExpr.var ⟨1, by decide⟩)
  next := fun i => match i with
    | ⟨0, _⟩ => CExpr.add (CExpr.var ⟨6, by decide⟩) (CExpr.var ⟨5, by decide⟩)
  out := (CExpr.var ⟨6, by decide⟩)

def ρ (i : Signal defaultDomain (BitVec 8)) (s : Nat) : CEnv ([8] ++ [8]) :=
  CEnv.join (CdoW.stateAt deep (fun t j => (inp i j).val t) s) (fun j => (inp i j).val s)
def rd0 (i : Signal defaultDomain (BitVec 8)) (s : Nat) : BitVec 8 :=
  CdoW.stateAt deep (fun t j => (inp i j).val t) s ⟨0, by decide⟩

def rw0 (i : Signal defaultDomain (BitVec 8)) (s : Nat) : BitVec 8 := CdoW.wenv deep (ρ i s) ⟨0, by decide⟩
def rw1 (i : Signal defaultDomain (BitVec 8)) (s : Nat) : BitVec 8 := CdoW.wenv deep (ρ i s) ⟨1, by decide⟩
def rw2 (i : Signal defaultDomain (BitVec 8)) (s : Nat) : BitVec 8 := CdoW.wenv deep (ρ i s) ⟨2, by decide⟩
def rw3 (i : Signal defaultDomain (BitVec 8)) (s : Nat) : BitVec 8 := CdoW.wenv deep (ρ i s) ⟨3, by decide⟩
def rw4 (i : Signal defaultDomain (BitVec 8)) (s : Nat) : BitVec 8 := CdoW.wenv deep (ρ i s) ⟨4, by decide⟩
theorem rw0_eq (i : Signal defaultDomain (BitVec 8)) (s : Nat) : rw0 i s = rd0 i s + i.val s := rfl
theorem rw1_eq (i : Signal defaultDomain (BitVec 8)) (s : Nat) : rw1 i s = (rw0 i s + rw0 i s) ^^^ i.val s := rfl
theorem rw2_eq (i : Signal defaultDomain (BitVec 8)) (s : Nat) : rw2 i s = (rw1 i s + rw1 i s) ^^^ i.val s := rfl
theorem rw3_eq (i : Signal defaultDomain (BitVec 8)) (s : Nat) : rw3 i s = (rw2 i s + rw2 i s) ^^^ i.val s := rfl
theorem rw4_eq (i : Signal defaultDomain (BitVec 8)) (s : Nat) : rw4 i s = (rw3 i s + rw3 i s) ^^^ i.val s := rfl
theorem rd0_zero (i : Signal defaultDomain (BitVec 8)) : rd0 i 0 = 0#8 := rfl
theorem rd0_succ (i : Signal defaultDomain (BitVec 8)) (s : Nat) : rd0 i (s+1) = rw4 i s + rw3 i s := rfl
theorem outS (i : Signal defaultDomain (BitVec 8)) (s : Nat) :
    (CdoW.outSig deep (inp i)).val s = rw4 i s := by
  show CExpr.denote _ _ = _
  rw [CdoW.stateSig_eq]
  rfl
set_option maxHeartbeats 1600000 in
theorem trace (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    ((shareX4 i).val t).toNat =
      (Sparkle.IR.Semantics.evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k))
          (envOfC nm (natJoin
            (natJoin (CdoW.irState deep nm (fun t j => (inp i j).val t) t)
              (fun j => ((inp i j).val t).toNat))
            (CdoW.irWires deep nm (natJoin (CdoW.irState deep nm (fun t j => (inp i j).val t) t)
              (fun j => ((inp i j).val t).toNat)))))
          (CExpr.compile nm (CdoW.out deep))).getD 0 := by
  rw [← CdoW.elab_general deep nm (by decide) (inp i) t]
  refine congrArg BitVec.toNat ?_
  simp -zeta only [shareX4]
  rw [runCircuitH_eq]
  simp -zeta only [outFOf, mkHolds, Signal.map, sigval_add, sigval_xor]
  generalize hL : Signal.loop (loopFOf (dom := Sparkle.Core.Domain.defaultDomain) (αs := [BitVec 8]) (ρ := Signal defaultDomain (BitVec 8)) _ _) = L
  have hLt : ∀ (u : Nat), L.val u = (rd0 i u, ()) := by
    intro u
    rw [← hL]
    refine loop_trace_at _ (fun s => (rd0 i s, ())) ?_ u
    intro u pre hpre
    cases u with
    | zero =>
      simp -zeta [loopFOf, packRegister, Signal.register, Signal.memStep, Circuit.next, Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux, bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq, inp_at_0, inp_at_mk_0]
      all_goals (try simp only [rd0_zero])
      all_goals first | rfl | bv_decide | (simp; done) | fail "cone-sharing prototype: closers exhausted on this goal"
    | succ m =>
      -- LINEAR recipe: keep the DSL `have` chain (zeta off), lift it into
      -- local defs (extract_lets descends and merges equal values), then
      -- reduce the plumbing around the now-opaque wires
      simp -zeta only [loopFOf, packRegister, Signal.register, Signal.memStep, Circuit.next, Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux, bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq, hpre m (Nat.lt_succ_self m)]
      extract_lets a w0 w1 w2 w3 w4 p
      simp only [packRegister, Signal.register, Signal.memStep, Circuit.next, Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux, bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq, sigval_add, sigval_xor, inp_at_0, inp_at_mk_0, hpre m (Nat.lt_succ_self m)]
      all_goals (try simp only [rd0_succ])
      have ea : a.val m = rd0 i m := by simp [a, mkRegList, Signal.map, hpre m (Nat.lt_succ_self m)]
      have e0 : w0.val m = a.val m + i.val m := by simp only [w0, sigval_add]
      have e1 : w1.val m = (w0.val m + w0.val m) ^^^ i.val m := by simp only [w1, sigval_add, sigval_xor]
      have e2 : w2.val m = (w1.val m + w1.val m) ^^^ i.val m := by simp only [w2, sigval_add, sigval_xor]
      have e3 : w3.val m = (w2.val m + w2.val m) ^^^ i.val m := by simp only [w3, sigval_add, sigval_xor]
      have e4 : w4.val m = (w3.val m + w3.val m) ^^^ i.val m := by simp only [w4, sigval_add, sigval_xor]
      -- the pack binding is small (it refers to the wire atoms): unfold it
      -- and push `.val` through; the wires themselves stay opaque
      simp only [p, packRegister, Signal.register, Signal.memStep, Circuit.next, Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux, bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq, sigval_add, sigval_xor]
      have f0 := rw0_eq i m
      have f1 := rw1_eq i m
      have f2 := rw2_eq i m
      have f3 := rw3_eq i m
      have f4 := rw4_eq i m
      all_goals (try simp only [Prod.mk.injEq, and_true])
      all_goals first | bv_decide | fail "cone-sharing prototype (linear): closers exhausted"
  rw [outS]
  -- output side, same linear recipe: keep the `have` chain, lift it, tie the
  -- register read to the reader via hLt, then per-wire `.val` equations
  simp -zeta only [Signal.map, hLt]
  extract_lets ao wo0 wo1 wo2 wo3 wo4
  have eao : ao.val t = rd0 i t := by simp [ao, Signal.map, hLt]
  have eo0 : wo0.val t = ao.val t + i.val t := by simp only [wo0, sigval_add]
  have eo1 : wo1.val t = (wo0.val t + wo0.val t) ^^^ i.val t := by simp only [wo1, sigval_add, sigval_xor]
  have eo2 : wo2.val t = (wo1.val t + wo1.val t) ^^^ i.val t := by simp only [wo2, sigval_add, sigval_xor]
  have eo3 : wo3.val t = (wo2.val t + wo2.val t) ^^^ i.val t := by simp only [wo3, sigval_add, sigval_xor]
  have eo4 : wo4.val t = (wo3.val t + wo3.val t) ^^^ i.val t := by simp only [wo4, sigval_add, sigval_xor]
  simp only [sigval_add, sigval_xor]
  have f0 := rw0_eq i t
  have f1 := rw1_eq i t
  have f2 := rw2_eq i t
  have f3 := rw3_eq i t
  have f4 := rw4_eq i t
  all_goals first | bv_decide | fail "cone-sharing prototype: closers exhausted on this goal"

#print axioms trace

end Sparkle.Tests.ShareW
