/-
  Cone-sharing prototype, REPLAY half: the IR replay chain on the shared
  route for `shareX4`, hand-written in the shape the generator will
  produce (plan step 2 of the staged cone-sharing plan, 2026-09-14).

  What is proven here, on top of `ConeSharingProto`'s Signal-side trace:
  * per-slot G1 glue (`coneEval_*`): the compiled reification of each
    wire / the register / the output evaluates like its elaborated SHARED
    cone (each cone is small — one wire's definition, stopping at the
    other shared wires);
  * the seed `envAt` (registers, inputs AND the deep wire values), its
    bound, and pointwise readers;
  * per wire, in slot order: the settled value equals the shared cone at
    the settled environment (`shared_cone_agrees_at_settled`, with the
    wire's own stop set), hence equals the deep wire value (`wire_w*`);
  * the register step and output step at the seed, by environment
    congruence on the cone's references (registers/inputs by the frame
    lemma, wires by `wire_w*`); `regNexts`;
  * the state-indexed seed `envSt`, its bound, agreement with `envAt` when
    the state matches the spec recurrence, the `stepIter` state trace,
    `signal_fold`, and **`signal_run`** — Signal ≡ `runModule` trace of the
    emitted IR, every cycle.

  Demo-only simplification: every wire of this circuit is 8 bits, so
  `weM := fun _ => 8` with a table listing every defined name at 8 (the
  generator uses the module's real width table).  Axioms: the standard
  three plus `native_decide` / `bv_decide` auxiliaries, checked by the
  policy at the end of the file (no `sorryAx`).
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
    | ⟨0, _⟩ => "_tmp_a_12"
    | ⟨1, _⟩ => "_gen_i"
    | ⟨2, _⟩ => "_tmp_op_a_9"
    | ⟨3, _⟩ => "_tmp_op_a_7"
    | ⟨4, _⟩ => "_tmp_op_a_5"
    | ⟨5, _⟩ => "_tmp_op_a_3"
    | ⟨6, _⟩ => "_tmp_arg1_1"
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



/-! ## IR replay on the shared route (hand-written for n = 4)

Width environment: every wire of this circuit is 8 bits, so the demo uses
`weM := fun _ => 8` with a width table listing every defined name at 8
(the generator uses the module's real table; the theorems only need the
table to agree with `weM`). -/
open Sparkle.IR.AST Sparkle.IR.Semantics Tools.ConeFold

def body : List Stmt := [
  .assign "_tmp_loop_body_14" (.ref "_tmp_a_12"),
  .assign "_tmp_loop_0" (.ref "_tmp_loop_body_14"),
  .assign "_tmp_op_a_10" (.slice (.ref "_tmp_loop_body_14") 7 0),
  .assign "_tmp_op_a_9" (.op .add [.ref "_tmp_op_a_10", .ref "_gen_i"]),
  .assign "_tmp_op_a_8" (.op .add [.ref "_tmp_op_a_9", .ref "_tmp_op_a_9"]),
  .assign "_tmp_op_a_7" (.op .xor [.ref "_tmp_op_a_8", .ref "_gen_i"]),
  .assign "_tmp_op_a_6" (.op .add [.ref "_tmp_op_a_7", .ref "_tmp_op_a_7"]),
  .assign "_tmp_op_a_5" (.op .xor [.ref "_tmp_op_a_6", .ref "_gen_i"]),
  .assign "_tmp_op_a_4" (.op .add [.ref "_tmp_op_a_5", .ref "_tmp_op_a_5"]),
  .assign "_tmp_op_a_3" (.op .xor [.ref "_tmp_op_a_4", .ref "_gen_i"]),
  .assign "_tmp_op_a_2" (.op .add [.ref "_tmp_op_a_3", .ref "_tmp_op_a_3"]),
  .assign "_tmp_arg1_1" (.op .xor [.ref "_tmp_op_a_2", .ref "_gen_i"]),
  .assign "_tmp_reg_input_11" (.op .add [.ref "_tmp_arg1_1", .ref "_tmp_op_a_3"]),
  .assign "_gen_a" (.ref "_tmp_op_a_10"),
  .assign "_gen_w0" (.ref "_tmp_op_a_9"),
  .assign "_tmp_op_a_15" (.ref "_tmp_op_a_8"),
  .assign "_gen_w1" (.ref "_tmp_op_a_7"),
  .assign "_tmp_op_a_16" (.ref "_tmp_op_a_6"),
  .assign "_gen_w2" (.ref "_tmp_op_a_5"),
  .assign "_tmp_op_a_17" (.ref "_tmp_op_a_4"),
  .assign "_gen_w3" (.ref "_tmp_op_a_3"),
  .assign "_tmp_op_a_18" (.ref "_tmp_op_a_2"),
  .assign "_gen_w4" (.ref "_tmp_arg1_1"),
  .assign "out" (.ref "_tmp_arg1_1"),
  .register "_tmp_a_12" "clk" ("rst", .synchronous) (.ref "_tmp_reg_input_11") 0 ]
def weM : WEnv := fun _ => 8
def wtL : List (String × Nat) := [("_tmp_loop_body_14", 8), ("_tmp_loop_0", 8), ("_tmp_op_a_10", 8), ("_tmp_op_a_9", 8), ("_tmp_op_a_8", 8), ("_tmp_op_a_7", 8), ("_tmp_op_a_6", 8), ("_tmp_op_a_5", 8), ("_tmp_op_a_4", 8), ("_tmp_op_a_3", 8), ("_tmp_op_a_2", 8), ("_tmp_arg1_1", 8), ("_tmp_reg_input_11", 8), ("_gen_a", 8), ("_gen_w0", 8), ("_tmp_op_a_15", 8), ("_gen_w1", 8), ("_tmp_op_a_16", 8), ("_gen_w2", 8), ("_tmp_op_a_17", 8), ("_gen_w3", 8), ("_tmp_op_a_18", 8), ("_gen_w4", 8), ("out", 8), ("_tmp_a_12", 8), ("_gen_i", 8)]
def wtM : Std.HashMap String Nat := wtL.foldl (fun m p => m.insert p.1 p.2) {}
def stopL : List String := ["_tmp_a_12", "_gen_i", "_tmp_op_a_9", "_tmp_op_a_7", "_tmp_op_a_5", "_tmp_op_a_3", "_tmp_arg1_1"]
def stopAtM : Std.HashMap String Bool := stopL.foldl (fun h x => h.insert x true) {}
/-- A wire's own cone inlines ITS definition: its stop set excludes the wire. -/
def stopLw (w : String) : List String := stopL.erase w
def stopAtMw (w : String) : Std.HashMap String Bool := (stopLw w).foldl (fun h x => h.insert x true) {}
def dm : Sparkle.IR.Optimize.DefMap := Sparkle.IR.Optimize.buildDefMap body
/-- The shared (stop-set) cone of a wire reference, by evaluation. -/
def coneRawOf (e : Expr) : Expr :=
  match inlineConeT dm stopAtM 10000 e with | .ok c => c | .error _ => .const 0 0
def coneRawOfW (w : String) : Expr :=
  match inlineConeT dm (stopAtMw w) 10000 (.ref w) with | .ok c => c | .error _ => .const 0 0
def coneRaw_r : Expr := coneRawOf (.ref "_tmp_reg_input_11")
def cone_r : Expr := resolveSlicesT wtM 10000 coneRaw_r
def coneRaw_out : Expr := coneRawOf (.ref "out")
def cone_out : Expr := resolveSlicesT wtM 10000 coneRaw_out
def coneRaw_w0 : Expr := coneRawOfW "_tmp_op_a_9"
def cone_w0 : Expr := resolveSlicesT wtM 10000 coneRaw_w0
def coneRaw_w1 : Expr := coneRawOfW "_tmp_op_a_7"
def cone_w1 : Expr := resolveSlicesT wtM 10000 coneRaw_w1
def coneRaw_w2 : Expr := coneRawOfW "_tmp_op_a_5"
def cone_w2 : Expr := resolveSlicesT wtM 10000 coneRaw_w2
def coneRaw_w3 : Expr := coneRawOfW "_tmp_op_a_3"
def cone_w3 : Expr := resolveSlicesT wtM 10000 coneRaw_w3
def coneRaw_w4 : Expr := coneRawOfW "_tmp_arg1_1"
def cone_w4 : Expr := resolveSlicesT wtM 10000 coneRaw_w4

def Γget : Fin (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).length → Nat := fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k
-- the general lemmas instantiate this exact form; keep it syntactic
abbrev weC : WEnv := weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)

-- G1 glue, one lemma per slot: the compiled reification evaluates like
-- the elaborated shared cone, under the full width env
theorem g1_generic (sl : List String) (lhs cone coneRaw : Expr) (eIn : Expr)
    (hnorm : lhs = Tools.ConcatNorm.concatNorm 10000 cone)
    (hns : Tools.ConeFold.noSingle cone = true)
    (hinl : inlineConeT dm (sl.foldl (fun h x => h.insert x true) {}) 10000 eIn = .ok coneRaw)
    (hres : cone = resolveSlicesT wtM 10000 coneRaw)
    (hag : ∀ n ∈ sl, weC n = weM n) (env : Env) :
    evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)) env lhs = evalExpr weM env cone := by
  rw [hnorm, concatNorm_eval _ env 10000 cone hns]
  refine evalExpr_we_congr _ weM env cone ?_
  intro n hn
  have h1 : n ∈ Sparkle.IR.Reorder.refsOf (resolveSlicesT wtM 10000 coneRaw) := by
    rw [← hres]; exact hn
  have href := inlineConeT_refs dm _ 10000 eIn coneRaw hinl n
    (resolveSlicesT_refs wtM 10000 coneRaw n h1)
  have hmem : n ∈ sl := by
    rcases stopFold_mem sl {} n href with h | h
    · exact h
    · simp at h
  exact hag n hmem

theorem hag_stop : ∀ n ∈ stopL, weC n = weM n := by native_decide

theorem coneEval_r0 (env : Env) :
    evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)) env (CExpr.compile nm (CdoW.next deep ⟨0, by decide⟩)) = evalExpr weM env cone_r :=
  g1_generic stopL _ cone_r coneRaw_r (.ref "_tmp_reg_input_11") (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) hag_stop env
theorem coneEval_out (env : Env) :
    evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)) env (CExpr.compile nm (CdoW.out deep)) = evalExpr weM env cone_out :=
  g1_generic stopL _ cone_out coneRaw_out (.ref "out") (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) hag_stop env
theorem coneEval_w0 (env : Env) :
    evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)) env (CExpr.compile nm (CdoW.wires deep ⟨0, by decide⟩)) = evalExpr weM env cone_w0 :=
  g1_generic (stopLw "_tmp_op_a_9") _ cone_w0 coneRaw_w0 (.ref "_tmp_op_a_9") (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (fun n hn => hag_stop n (List.mem_of_mem_erase hn)) env
theorem coneEval_w1 (env : Env) :
    evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)) env (CExpr.compile nm (CdoW.wires deep ⟨1, by decide⟩)) = evalExpr weM env cone_w1 :=
  g1_generic (stopLw "_tmp_op_a_7") _ cone_w1 coneRaw_w1 (.ref "_tmp_op_a_7") (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (fun n hn => hag_stop n (List.mem_of_mem_erase hn)) env
theorem coneEval_w2 (env : Env) :
    evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)) env (CExpr.compile nm (CdoW.wires deep ⟨2, by decide⟩)) = evalExpr weM env cone_w2 :=
  g1_generic (stopLw "_tmp_op_a_5") _ cone_w2 coneRaw_w2 (.ref "_tmp_op_a_5") (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (fun n hn => hag_stop n (List.mem_of_mem_erase hn)) env
theorem coneEval_w3 (env : Env) :
    evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)) env (CExpr.compile nm (CdoW.wires deep ⟨3, by decide⟩)) = evalExpr weM env cone_w3 :=
  g1_generic (stopLw "_tmp_op_a_3") _ cone_w3 coneRaw_w3 (.ref "_tmp_op_a_3") (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (fun n hn => hag_stop n (List.mem_of_mem_erase hn)) env
theorem coneEval_w4 (env : Env) :
    evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)) env (CExpr.compile nm (CdoW.wires deep ⟨4, by decide⟩)) = evalExpr weM env cone_w4 :=
  g1_generic (stopLw "_tmp_arg1_1") _ cone_w4 coneRaw_w4 (.ref "_tmp_arg1_1") (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (fun n hn => hag_stop n (List.mem_of_mem_erase hn)) env

/-! ### The seed, its readers, and its bound -/
def inpF (i : Signal defaultDomain (BitVec 8)) : Nat → CEnv [8] := fun t j => (inp i j).val t
def ρn (i : Signal defaultDomain (BitVec 8)) (t : Nat) : Fin ([8] ++ [8] : List Nat).length → Nat :=
  natJoin (CdoW.irState deep nm (inpF i) t) (fun j => ((inp i j).val t).toNat)
def envAt (i : Signal defaultDomain (BitVec 8)) (t : Nat) : Env :=
  envOfC nm (natJoin (ρn i t) (CdoW.irWires deep nm (ρn i t)))

theorem hinj : ∀ a b : Fin (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).length, nm a = nm b → a = b := by decide

/-- `ρn` is the `toNat` of a BitVec valuation (the spec state joined with the inputs). -/
theorem ρn_eq (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    ρn i t = fun m => (CEnv.join (CdoW.stateAt deep (inpF i) t) (inpF i t) m).toNat := by
  funext m
  unfold ρn
  rw [← natJoin_eq_join]
  congr 1
  funext k
  exact CdoW.irState_eq deep nm hinj (inpF i) t k

theorem seed_bounded (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    ∀ n, envAt i t n < 2 ^ weM n := by
  intro n
  unfold envAt
  apply envOfC_bounded
  intro k
  have hag : ∀ k : Fin (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).length, weM (nm k) = Γget k := by decide
  rw [hag k]
  rw [ρn_eq, CdoW.natJoin_full deep nm hinj]
  exact BitVec.isLt _

theorem envAt_r0 (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    envAt i t "_tmp_a_12" = CdoW.irState deep nm (inpF i) t ⟨0, by decide⟩ := by
  show envOfC nm _ (nm ⟨0, by decide⟩) = _
  rw [envOfC_names nm _ hinj]
  rfl
theorem envAt_i0 (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    envAt i t "_gen_i" = ((inp i ⟨0, by decide⟩).val t).toNat := by
  show envOfC nm _ (nm ⟨1, by decide⟩) = _
  rw [envOfC_names nm _ hinj]
  rfl
theorem envAt_w0 (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    envAt i t "_tmp_op_a_9" = CdoW.irWires deep nm (ρn i t) ⟨0, by decide⟩ := by
  show envOfC nm _ (nm ⟨2, by decide⟩) = _
  rw [envOfC_names nm _ hinj]
  rfl
theorem envAt_w1 (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    envAt i t "_tmp_op_a_7" = CdoW.irWires deep nm (ρn i t) ⟨1, by decide⟩ := by
  show envOfC nm _ (nm ⟨3, by decide⟩) = _
  rw [envOfC_names nm _ hinj]
  rfl
theorem envAt_w2 (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    envAt i t "_tmp_op_a_5" = CdoW.irWires deep nm (ρn i t) ⟨2, by decide⟩ := by
  show envOfC nm _ (nm ⟨4, by decide⟩) = _
  rw [envOfC_names nm _ hinj]
  rfl
theorem envAt_w3 (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    envAt i t "_tmp_op_a_3" = CdoW.irWires deep nm (ρn i t) ⟨3, by decide⟩ := by
  show envOfC nm _ (nm ⟨5, by decide⟩) = _
  rw [envOfC_names nm _ hinj]
  rfl
theorem envAt_w4 (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    envAt i t "_tmp_arg1_1" = CdoW.irWires deep nm (ρn i t) ⟨4, by decide⟩ := by
  show envOfC nm _ (nm ⟨6, by decide⟩) = _
  rw [envOfC_names nm _ hinj]
  rfl
theorem nm_mem_stop : ∀ k : Fin (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).length, nm k ∈ stopL := by decide
theorem envAt_other (i : Signal defaultDomain (BitVec 8)) (t : Nat) (n : String)
    (h : n ∉ stopL) : envAt i t n = 0 := by
  unfold envAt
  apply envOfC_notin
  intro k hk
  exact h (hk ▸ nm_mem_stop k)

/-! ### Settled-environment facts -/
theorem hb1_of (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) :
    ∀ n, env1 n < 2 ^ weM n :=
  evalAssigns_bounded weM _ body _ env1 (memFreeCheck_sound _ (by decide))
    (by native_decide) (seed_bounded i t) hrun

theorem frame_reg (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) : env1 "_tmp_a_12" = envAt i t "_tmp_a_12" :=
  evalAssigns_frame weM _ body _ env1 hrun (memFreeCheck_sound _ (by decide)) _ (by decide)
theorem frame_inp (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) : env1 "_gen_i" = envAt i t "_gen_i" :=
  evalAssigns_frame weM _ body _ env1 hrun (memFreeCheck_sound _ (by decide)) _ (by decide)
theorem frame_rst (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) : env1 "rst" = envAt i t "rst" :=
  evalAssigns_frame weM _ body _ env1 hrun (memFreeCheck_sound _ (by decide)) _ (by decide)

theorem settled_w0 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) :
    evalExpr weM env1 cone_w0 = some (env1 "_tmp_op_a_9") := by
  have h : evalExpr weM env1 (resolveSlicesT wtM 10000 coneRaw_w0) = some (env1 "_tmp_op_a_9") :=
    shared_cone_agrees_at_settled weM (fun _ _ => 0) (stopAtMw "_tmp_op_a_9") wtM
    (Sparkle.IR.Reorder.woCheck_sound [] body (by decide))
    (memFreeCheck_sound _ (by decide)) (noSelfReadCheck_sound _ (by decide)) hrun
    (hwfCheck_sound weM (stopAtMw "_tmp_op_a_9") body (by native_decide))
    (hwt_of_assoc weM wtL (by native_decide)) (hb1_of i t hrun)
    (fuel := 10000) (e := .ref "_tmp_op_a_9") (e' := coneRaw_w0) (hinl := by native_decide) 10000
    (v := env1 "_tmp_op_a_9") (by simp [evalExpr])
  exact h

theorem wire_w0 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) : env1 "_tmp_op_a_9" = envAt i t "_tmp_op_a_9" := by
  have hs := settled_w0 i t hrun
  rw [envAt_w0, CdoW.irWires_eq_at, coneEval_w0]
  have hc : evalExpr weM (envOfC nm (natJoin (ρn i t) (CdoW.irWiresAt deep nm (ρn i t) 0))) cone_w0
      = evalExpr weM env1 cone_w0 := by
    apply Sparkle.IR.Reorder.evalExpr_congr
    intro n hn
    have hsub : ∀ m ∈ Sparkle.IR.Reorder.refsOf cone_w0, m ∈ ["_tmp_a_12", "_gen_i"] := by native_decide
    have hm := hsub n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [frame_reg i t hrun, envAt_r0]
      show envOfC nm _ (nm ⟨0, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
    · rw [frame_inp i t hrun, envAt_i0]
      show envOfC nm _ (nm ⟨1, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
  rw [hc, hs]
  rfl

theorem settled_w1 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) :
    evalExpr weM env1 cone_w1 = some (env1 "_tmp_op_a_7") := by
  have h : evalExpr weM env1 (resolveSlicesT wtM 10000 coneRaw_w1) = some (env1 "_tmp_op_a_7") :=
    shared_cone_agrees_at_settled weM (fun _ _ => 0) (stopAtMw "_tmp_op_a_7") wtM
    (Sparkle.IR.Reorder.woCheck_sound [] body (by decide))
    (memFreeCheck_sound _ (by decide)) (noSelfReadCheck_sound _ (by decide)) hrun
    (hwfCheck_sound weM (stopAtMw "_tmp_op_a_7") body (by native_decide))
    (hwt_of_assoc weM wtL (by native_decide)) (hb1_of i t hrun)
    (fuel := 10000) (e := .ref "_tmp_op_a_7") (e' := coneRaw_w1) (hinl := by native_decide) 10000
    (v := env1 "_tmp_op_a_7") (by simp [evalExpr])
  exact h

theorem wire_w1 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) : env1 "_tmp_op_a_7" = envAt i t "_tmp_op_a_7" := by
  have hs := settled_w1 i t hrun
  rw [envAt_w1, CdoW.irWires_eq_at, coneEval_w1]
  have hc : evalExpr weM (envOfC nm (natJoin (ρn i t) (CdoW.irWiresAt deep nm (ρn i t) 1))) cone_w1
      = evalExpr weM env1 cone_w1 := by
    apply Sparkle.IR.Reorder.evalExpr_congr
    intro n hn
    have hsub : ∀ m ∈ Sparkle.IR.Reorder.refsOf cone_w1, m ∈ ["_tmp_a_12", "_gen_i", "_tmp_op_a_9"] := by native_decide
    have hm := hsub n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [frame_reg i t hrun, envAt_r0]
      show envOfC nm _ (nm ⟨0, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
    · rw [frame_inp i t hrun, envAt_i0]
      show envOfC nm _ (nm ⟨1, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
    · rw [wire_w0 i t hrun, envAt_w0]
      show envOfC nm _ (nm ⟨2, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 1 ⟨0, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨0, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 1 ⟨0, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨0, by decide⟩ (by decide)]
  rw [hc, hs]
  rfl

theorem settled_w2 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) :
    evalExpr weM env1 cone_w2 = some (env1 "_tmp_op_a_5") := by
  have h : evalExpr weM env1 (resolveSlicesT wtM 10000 coneRaw_w2) = some (env1 "_tmp_op_a_5") :=
    shared_cone_agrees_at_settled weM (fun _ _ => 0) (stopAtMw "_tmp_op_a_5") wtM
    (Sparkle.IR.Reorder.woCheck_sound [] body (by decide))
    (memFreeCheck_sound _ (by decide)) (noSelfReadCheck_sound _ (by decide)) hrun
    (hwfCheck_sound weM (stopAtMw "_tmp_op_a_5") body (by native_decide))
    (hwt_of_assoc weM wtL (by native_decide)) (hb1_of i t hrun)
    (fuel := 10000) (e := .ref "_tmp_op_a_5") (e' := coneRaw_w2) (hinl := by native_decide) 10000
    (v := env1 "_tmp_op_a_5") (by simp [evalExpr])
  exact h

theorem wire_w2 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) : env1 "_tmp_op_a_5" = envAt i t "_tmp_op_a_5" := by
  have hs := settled_w2 i t hrun
  rw [envAt_w2, CdoW.irWires_eq_at, coneEval_w2]
  have hc : evalExpr weM (envOfC nm (natJoin (ρn i t) (CdoW.irWiresAt deep nm (ρn i t) 2))) cone_w2
      = evalExpr weM env1 cone_w2 := by
    apply Sparkle.IR.Reorder.evalExpr_congr
    intro n hn
    have hsub : ∀ m ∈ Sparkle.IR.Reorder.refsOf cone_w2, m ∈ ["_tmp_a_12", "_gen_i", "_tmp_op_a_9", "_tmp_op_a_7"] := by native_decide
    have hm := hsub n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · rw [frame_reg i t hrun, envAt_r0]
      show envOfC nm _ (nm ⟨0, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
    · rw [frame_inp i t hrun, envAt_i0]
      show envOfC nm _ (nm ⟨1, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
    · rw [wire_w0 i t hrun, envAt_w0]
      show envOfC nm _ (nm ⟨2, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 2 ⟨0, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨0, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 2 ⟨0, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨0, by decide⟩ (by decide)]
    · rw [wire_w1 i t hrun, envAt_w1]
      show envOfC nm _ (nm ⟨3, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 2 ⟨1, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨1, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 2 ⟨1, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨1, by decide⟩ (by decide)]
  rw [hc, hs]
  rfl

theorem settled_w3 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) :
    evalExpr weM env1 cone_w3 = some (env1 "_tmp_op_a_3") := by
  have h : evalExpr weM env1 (resolveSlicesT wtM 10000 coneRaw_w3) = some (env1 "_tmp_op_a_3") :=
    shared_cone_agrees_at_settled weM (fun _ _ => 0) (stopAtMw "_tmp_op_a_3") wtM
    (Sparkle.IR.Reorder.woCheck_sound [] body (by decide))
    (memFreeCheck_sound _ (by decide)) (noSelfReadCheck_sound _ (by decide)) hrun
    (hwfCheck_sound weM (stopAtMw "_tmp_op_a_3") body (by native_decide))
    (hwt_of_assoc weM wtL (by native_decide)) (hb1_of i t hrun)
    (fuel := 10000) (e := .ref "_tmp_op_a_3") (e' := coneRaw_w3) (hinl := by native_decide) 10000
    (v := env1 "_tmp_op_a_3") (by simp [evalExpr])
  exact h

theorem wire_w3 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) : env1 "_tmp_op_a_3" = envAt i t "_tmp_op_a_3" := by
  have hs := settled_w3 i t hrun
  rw [envAt_w3, CdoW.irWires_eq_at, coneEval_w3]
  have hc : evalExpr weM (envOfC nm (natJoin (ρn i t) (CdoW.irWiresAt deep nm (ρn i t) 3))) cone_w3
      = evalExpr weM env1 cone_w3 := by
    apply Sparkle.IR.Reorder.evalExpr_congr
    intro n hn
    have hsub : ∀ m ∈ Sparkle.IR.Reorder.refsOf cone_w3, m ∈ ["_tmp_a_12", "_gen_i", "_tmp_op_a_9", "_tmp_op_a_7", "_tmp_op_a_5"] := by native_decide
    have hm := hsub n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · rw [frame_reg i t hrun, envAt_r0]
      show envOfC nm _ (nm ⟨0, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
    · rw [frame_inp i t hrun, envAt_i0]
      show envOfC nm _ (nm ⟨1, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
    · rw [wire_w0 i t hrun, envAt_w0]
      show envOfC nm _ (nm ⟨2, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 3 ⟨0, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨0, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 3 ⟨0, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨0, by decide⟩ (by decide)]
    · rw [wire_w1 i t hrun, envAt_w1]
      show envOfC nm _ (nm ⟨3, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 3 ⟨1, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨1, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 3 ⟨1, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨1, by decide⟩ (by decide)]
    · rw [wire_w2 i t hrun, envAt_w2]
      show envOfC nm _ (nm ⟨4, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 3 ⟨2, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨2, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 3 ⟨2, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨2, by decide⟩ (by decide)]
  rw [hc, hs]
  rfl

theorem settled_w4 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) :
    evalExpr weM env1 cone_w4 = some (env1 "_tmp_arg1_1") := by
  have h : evalExpr weM env1 (resolveSlicesT wtM 10000 coneRaw_w4) = some (env1 "_tmp_arg1_1") :=
    shared_cone_agrees_at_settled weM (fun _ _ => 0) (stopAtMw "_tmp_arg1_1") wtM
    (Sparkle.IR.Reorder.woCheck_sound [] body (by decide))
    (memFreeCheck_sound _ (by decide)) (noSelfReadCheck_sound _ (by decide)) hrun
    (hwfCheck_sound weM (stopAtMw "_tmp_arg1_1") body (by native_decide))
    (hwt_of_assoc weM wtL (by native_decide)) (hb1_of i t hrun)
    (fuel := 10000) (e := .ref "_tmp_arg1_1") (e' := coneRaw_w4) (hinl := by native_decide) 10000
    (v := env1 "_tmp_arg1_1") (by simp [evalExpr])
  exact h

theorem wire_w4 (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) : env1 "_tmp_arg1_1" = envAt i t "_tmp_arg1_1" := by
  have hs := settled_w4 i t hrun
  rw [envAt_w4, CdoW.irWires_eq_at, coneEval_w4]
  have hc : evalExpr weM (envOfC nm (natJoin (ρn i t) (CdoW.irWiresAt deep nm (ρn i t) 4))) cone_w4
      = evalExpr weM env1 cone_w4 := by
    apply Sparkle.IR.Reorder.evalExpr_congr
    intro n hn
    have hsub : ∀ m ∈ Sparkle.IR.Reorder.refsOf cone_w4, m ∈ ["_tmp_a_12", "_gen_i", "_tmp_op_a_9", "_tmp_op_a_7", "_tmp_op_a_5", "_tmp_op_a_3"] := by native_decide
    have hm := hsub n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [frame_reg i t hrun, envAt_r0]
      show envOfC nm _ (nm ⟨0, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
    · rw [frame_inp i t hrun, envAt_i0]
      show envOfC nm _ (nm ⟨1, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      rfl
    · rw [wire_w0 i t hrun, envAt_w0]
      show envOfC nm _ (nm ⟨2, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 4 ⟨0, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨0, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 4 ⟨0, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨0, by decide⟩ (by decide)]
    · rw [wire_w1 i t hrun, envAt_w1]
      show envOfC nm _ (nm ⟨3, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 4 ⟨1, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨1, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 4 ⟨1, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨1, by decide⟩ (by decide)]
    · rw [wire_w2 i t hrun, envAt_w2]
      show envOfC nm _ (nm ⟨4, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 4 ⟨2, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨2, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 4 ⟨2, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨2, by decide⟩ (by decide)]
    · rw [wire_w3 i t hrun, envAt_w3]
      show envOfC nm _ (nm ⟨5, by decide⟩) = _
      rw [envOfC_names nm _ hinj]
      show CdoW.irWiresAt deep nm (ρn i t) 4 ⟨3, by decide⟩ = CdoW.irWires deep nm (ρn i t) ⟨3, by decide⟩
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) 4 ⟨3, by decide⟩ (by decide)]
      unfold CdoW.irWires
      rw [CdoW.irWiresAt_stable deep nm (ρn i t) ([8, 8, 8, 8, 8] : List Nat).length ⟨3, by decide⟩ (by decide)]
  rw [hc, hs]
  rfl

theorem step_r (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) {v : Nat}
    (hv : evalExpr weM env1 (.ref "_tmp_reg_input_11") = some v) :
    evalExpr weM (envAt i t) cone_r = some v := by
  have h : evalExpr weM env1 (resolveSlicesT wtM 10000 coneRaw_r) = some v :=
    shared_cone_agrees_at_settled weM (fun _ _ => 0) stopAtM wtM
    (Sparkle.IR.Reorder.woCheck_sound [] body (by decide))
    (memFreeCheck_sound _ (by decide)) (noSelfReadCheck_sound _ (by decide)) hrun
    (hwfCheck_sound weM stopAtM body (by native_decide))
    (hwt_of_assoc weM wtL (by native_decide)) (hb1_of i t hrun)
    (fuel := 10000) (e := .ref "_tmp_reg_input_11") (e' := coneRaw_r) (hinl := by native_decide) 10000 hv
  have hc : evalExpr weM (envAt i t) cone_r = evalExpr weM env1 cone_r := by
    apply Sparkle.IR.Reorder.evalExpr_congr
    intro n hn
    have hsub : ∀ m ∈ Sparkle.IR.Reorder.refsOf cone_r, m ∈ ["_tmp_a_12", "_gen_i", "_tmp_op_a_9", "_tmp_op_a_7", "_tmp_op_a_5", "_tmp_op_a_3", "_tmp_arg1_1"] := by native_decide
    have hm := hsub n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (frame_reg i t hrun).symm
    · exact (frame_inp i t hrun).symm
    · exact (wire_w0 i t hrun).symm
    · exact (wire_w1 i t hrun).symm
    · exact (wire_w2 i t hrun).symm
    · exact (wire_w3 i t hrun).symm
    · exact (wire_w4 i t hrun).symm
  rw [hc]
  exact h

theorem step_out (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) {v : Nat}
    (hv : evalExpr weM env1 (.ref "out") = some v) :
    evalExpr weM (envAt i t) cone_out = some v := by
  have h : evalExpr weM env1 (resolveSlicesT wtM 10000 coneRaw_out) = some v :=
    shared_cone_agrees_at_settled weM (fun _ _ => 0) stopAtM wtM
    (Sparkle.IR.Reorder.woCheck_sound [] body (by decide))
    (memFreeCheck_sound _ (by decide)) (noSelfReadCheck_sound _ (by decide)) hrun
    (hwfCheck_sound weM stopAtM body (by native_decide))
    (hwt_of_assoc weM wtL (by native_decide)) (hb1_of i t hrun)
    (fuel := 10000) (e := .ref "out") (e' := coneRaw_out) (hinl := by native_decide) 10000 hv
  have hc : evalExpr weM (envAt i t) cone_out = evalExpr weM env1 cone_out := by
    apply Sparkle.IR.Reorder.evalExpr_congr
    intro n hn
    have hsub : ∀ m ∈ Sparkle.IR.Reorder.refsOf cone_out, m ∈ ["_tmp_a_12", "_gen_i", "_tmp_op_a_9", "_tmp_op_a_7", "_tmp_op_a_5", "_tmp_op_a_3", "_tmp_arg1_1"] := by native_decide
    have hm := hsub n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (frame_reg i t hrun).symm
    · exact (frame_inp i t hrun).symm
    · exact (wire_w0 i t hrun).symm
    · exact (wire_w1 i t hrun).symm
    · exact (wire_w2 i t hrun).symm
    · exact (wire_w3 i t hrun).symm
    · exact (wire_w4 i t hrun).symm
  rw [hc]
  exact h

theorem regstep (i : Signal defaultDomain (BitVec 8)) (t : Nat) {env1 : Env}
    (hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) = some env1) :
    regNexts weM (fun _ _ => 0) body env1
      = some [("_tmp_a_12", CdoW.irState deep nm (inpF i) (t + 1) ⟨0, by decide⟩)] := by
  have hnext : CdoW.irState deep nm (inpF i) (t + 1) ⟨0, by decide⟩ = env1 "_tmp_reg_input_11" := by
    show (evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).get k)) (envOfC nm (natJoin (ρn i t) (CdoW.irWires deep nm (ρn i t))))
      (CExpr.compile nm (CdoW.next deep ⟨0, by decide⟩))).getD 0 = _
    rw [coneEval_r0]
    show (evalExpr weM (envAt i t) cone_r).getD 0 = _
    rw [step_r i t hrun (v := env1 "_tmp_reg_input_11") (by simp [evalExpr])]
    rfl
  have hrst : env1 "rst" = 0 := by
    rw [frame_rst i t hrun]; exact envAt_other i t "rst" (by decide)
  have hb : env1 "_tmp_reg_input_11" < 2 ^ 8 := hb1_of i t hrun _
  simp only [body, regNexts, evalExpr, Option.bind_eq_bind, Option.bind_some, hrst,
    ne_eq, not_true_eq_false, ↓reduceIte, mask, weM]
  rw [Nat.mod_eq_of_lt hb, hnext]


/-! ### Replay: stepIter / runModule over the shared recurrence -/
def stv (st : String → Nat) : Fin ([8] : List Nat).length → Nat := fun _ => st "_tmp_a_12" % 2 ^ 8
def ρnS (i : Signal defaultDomain (BitVec 8)) (t : Nat) (st : String → Nat) :
    Fin ([8] ++ [8] : List Nat).length → Nat :=
  natJoin (stv st) (fun j => ((inp i j).val t).toNat)
def envSt (i : Signal defaultDomain (BitVec 8)) (t : Nat) (st : String → Nat) : Env :=
  envOfC nm (natJoin (ρnS i t st) (CdoW.irWires deep nm (ρnS i t st)))
def st0 : String → Nat := fun n => if n == "_tmp_a_12" then (CdoW.inits deep ⟨0, by decide⟩).toNat else 0

theorem ρnS_eq (i : Signal defaultDomain (BitVec 8)) (t : Nat) (st : String → Nat) :
    ρnS i t st = fun m => (CEnv.join
      ((fun j => match j with | ⟨0, _⟩ => BitVec.ofNat 8 (st "_tmp_a_12")) : CEnv [8])
      (inpF i t) m).toNat := by
  funext m
  unfold ρnS
  rw [← natJoin_eq_join]
  congr 1
  funext k
  have hk : k = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp k.isLt)
  subst hk
  simp [stv]

theorem envSt_bounded (i : Signal defaultDomain (BitVec 8)) (t : Nat) (st : String → Nat) :
    ∀ n, envSt i t st n < 2 ^ weM n := by
  intro n
  unfold envSt
  apply envOfC_bounded
  intro k
  have hag : ∀ k : Fin (([8] ++ [8]) ++ [8, 8, 8, 8, 8] : List Nat).length, weM (nm k) = Γget k := by decide
  rw [hag k, ρnS_eq, CdoW.natJoin_full deep nm hinj]
  exact BitVec.isLt _

/-- When the state agrees with the spec recurrence, the state-indexed seed IS the seed. -/
theorem henv (i : Signal defaultDomain (BitVec 8)) (t : Nat) (st : String → Nat)
    (hst : st "_tmp_a_12" = CdoW.irState deep nm (inpF i) t ⟨0, by decide⟩) :
    envSt i t st = envAt i t := by
  have hb : CdoW.irState deep nm (inpF i) t ⟨0, by decide⟩ < 2 ^ 8 := by
    rw [CdoW.irState_eq deep nm hinj]; exact BitVec.isLt _
  have hstv : stv st = CdoW.irState deep nm (inpF i) t := by
    funext j
    have hj : j = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp j.isLt)
    subst hj
    show st "_tmp_a_12" % 2 ^ 8 = _
    rw [hst]
    exact Nat.mod_eq_of_lt hb
  unfold envSt envAt ρnS ρn
  rw [hstv]

theorem state_trace (i : Signal defaultDomain (BitVec 8)) : ∀ (t : Nat) {st : String → Nat},
    Tools.ConeFold.stepIter weM body (envSt i) st0 t = some st →
    st "_tmp_a_12" = CdoW.irState deep nm (inpF i) t ⟨0, by decide⟩ := by
  intro t
  induction t with
  | zero =>
    intro st h
    simp only [Tools.ConeFold.stepIter, Option.some_inj] at h
    subst h
    simp [st0, CdoW.irState]
  | succ t ih =>
    intro st' h
    simp only [Tools.ConeFold.stepIter, Option.bind_eq_bind] at h
    cases hprev : Tools.ConeFold.stepIter weM body (envSt i) st0 t with
    | none => rw [hprev] at h; simp at h
    | some st =>
      rw [hprev] at h
      simp only [Option.bind_some] at h
      have ihc := ih hprev
      rw [henv i t st ihc] at h
      simp only [stepModule, Option.bind_eq_bind] at h
      cases hrun : evalAssigns weM (fun _ _ => 0) body (envAt i t) with
      | none => rw [hrun] at h; simp at h
      | some env1 =>
        rw [hrun] at h
        simp only [Option.bind_some] at h
        rw [regstep i t hrun, memNexts_memFree weM body (memFreeCheck_sound _ (by decide))] at h
        simp only [Option.bind_some, Option.some_inj] at h
        subst h
        simp [applyNexts]

theorem signalM (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    ((shareX4 i).val t).toNat = (evalExpr weM (envAt i t) cone_out).getD 0 := by
  rw [trace i t]
  show (evalExpr _ (envOfC nm (natJoin (ρn i t) (CdoW.irWires deep nm (ρn i t))))
    (CExpr.compile nm (CdoW.out deep))).getD 0 = _
  rw [coneEval_out]
  rfl

theorem signal_fold (i : Signal defaultDomain (BitVec 8)) (t : Nat) {st : String → Nat} {env1 : Env}
    (hstep : Tools.ConeFold.stepIter weM body (envSt i) st0 t = some st)
    (hrun : evalAssigns weM (fun _ _ => 0) body (envSt i t st) = some env1) :
    ((shareX4 i).val t).toNat = env1 "out" := by
  have ihc := state_trace i t hstep
  rw [henv i t st ihc] at hrun
  have hout := step_out i t hrun (v := env1 "out") (by simp [evalExpr])
  rw [signalM, hout]
  rfl

theorem signal_run (i : Signal defaultDomain (BitVec 8)) (K : Nat) :
    ∃ envs, runModule weM body (fun td s => envSt i (K - 1 - td) s) K st0 (fun _ _ => 0) = some envs
      ∧ ∀ t, t < K → ∃ env1, envs[t]? = some env1 ∧ ((shareX4 i).val t).toNat = env1 "out" := by
  obtain ⟨envs, henvs⟩ := Option.isSome_iff_exists.mp
    (runModule_isSome weM body (memFreeCheck_sound _ (by decide)) (by native_decide)
      (fun td s => envSt i (K - 1 - td) s) K st0)
  refine ⟨envs, henvs, ?_⟩
  intro t ht
  have henvs' : runModule weM body (fun td s => envSt i (0 + (K - 1 - td)) s) K st0 (fun _ _ => 0) = some envs := by
    rw [runModule_seed_congr weM body K (fun td s => envSt i (0 + (K - 1 - td)) s)
      (fun td s => envSt i (K - 1 - td) s) (fun td htd => by simp only [Nat.zero_add])]
    exact henvs
  obtain ⟨st', env1, hsi, hev, hget⟩ :=
    runModule_stepIter weM body (memFreeCheck_sound _ (by decide)) (envSt i) K 0 st0 envs henvs' t ht
  refine ⟨env1, hget, ?_⟩
  have hsi' : Tools.ConeFold.stepIter weM body (envSt i) st0 t = some st' := by
    rw [stepIter_seed_congr weM body (envSt i) (fun tt s => envSt i (0 + tt) s) st0 t
      (fun tt htt => by simp only [Nat.zero_add])]
    exact hsi
  have hev' : evalAssigns weM (fun _ _ => 0) body (envSt i t st') = some env1 := by
    have h0 : (0 : Nat) + t = t := by omega
    rw [← h0]
    exact hev
  exact signal_fold i t hsi' hev'

/-! ### Axiom policy: standard + native_decide / bv_decide auxiliaries, nothing else -/
open Lean Elab Command in
run_cmd do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let isAux (a : Name) : Bool :=
    a == ``Lean.ofReduceBool ||
    (match a with
     | .str (.str (.str _ "_native") "native_decide") ax => ax.startsWith "ax_"
     | .str (.str (.str _ "_native") "bv_decide") ax => ax.startsWith "ax_"
     | _ => false)
  for thm in [``Sparkle.Tests.ShareW.trace, ``Sparkle.Tests.ShareW.signal_run] do
    let mut n : Nat := 0
    for a in (← collectAxioms thm) do
      if std.contains a then pure ()
      else if isAux a then n := n + 1
      else throwError "CONE-SHARING REPLAY: {thm} depends on disallowed axiom {a}"
    logInfo m!"CONE-SHARING REPLAY OK: {thm} axioms = std + {n} decision-procedure auxiliaries"

end Sparkle.Tests.ShareW
