import Tools.SVParser.VerifyEmit
import Sparkle.IR.ReorderInvariance

/-!
  The SEAM between the two certified arcs.

  Arc 1 (Signal ↔ IR, `Cdo.elab_general` + `#verify_elab_deep`) states
  its conclusion over `evalExpr` of the module's INLINED cones; Arc 2
  (IR ↔ SystemVerilog, `certified_body_trace` / `certified_forward_trace`)
  is stated over `stepModule` — the in-order wire-assignment fold.  To
  compose them, cone evaluation must equal the fold's result:

      evalExpr we env₁ (inlined cone) = env₁ (the wire)

  where `env₁` is the environment `evalAssigns` produces.  Two pieces:

  1. `inlineConeT` — a TOTAL twin of the shipping `partial def
     inlineCone` (Tools/SVParser/VerifyEmit.lean), fuel-primary,
     structurally recursive in the expression under a fixed fuel.
     Per-instance agreement with the shipping function is checked the
     usual way (`#guard` probes; the shipping def has no equations).
  2. The fixpoint lemma: on a well-ordered body (the `WO` of
     Sparkle/IR/ReorderInvariance.lean — every read of a locally
     assigned wire happens after its unique write), the environment
     `evalAssigns` returns satisfies
     `env₁ n = evalExpr we env₁ (rhs n)` for every assigned wire `n`,
     and `inlineConeT` preserves `evalExpr` under any such fixpoint
     environment.
-/

open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Optimize (DefMap)

namespace Tools.ConeFold

-- Total twin of the shipping `inlineCone`.  Fuel decreases exactly
-- where the shipping one decreases it (on `.ref` expansion); the
-- expression shrinks everywhere else, so the pair (fuel, e) is the
-- termination measure.
mutual
def inlineConeT (dm : DefMap) (stopAt : Std.HashMap String Bool) :
    Nat → Expr → Except String Expr
  | fuel, .ref n =>
    if stopAt.contains n then .ok (.ref n)
    else match fuel, dm.get? n with
      | 0, _ => .error s!"cone inlining fuel exhausted at `{n}` (combinational cycle?)"
      | _, none => .error s!"`{n}` is neither an input, a register, nor assigned"
      | fuel + 1, some rhs => inlineConeT dm stopAt fuel rhs
  | fuel, .op o args => do
    .ok (.op o (← inlineConeTL dm stopAt fuel args))
  | fuel, .concat args => do
    .ok (.concat (← inlineConeTL dm stopAt fuel args))
  | fuel, .slice e hi lo => do
    .ok (.slice (← inlineConeT dm stopAt fuel e) hi lo)
  | _, .index .. => .error "memories/dynamic indexing unsupported by #verify_emit (v1)"
  | _, .sliceDim .. => .error "symbolic-width slices unsupported by #verify_emit (v1)"
  | _, e => .ok e

def inlineConeTL (dm : DefMap) (stopAt : Std.HashMap String Bool) :
    Nat → List Expr → Except String (List Expr)
  | _, [] => .ok []
  | fuel, a :: rest => do
    .ok ((← inlineConeT dm stopAt fuel a) :: (← inlineConeTL dm stopAt fuel rest))
end



section Fixpoint

open Sparkle.IR.Reorder

/-- v0 scope: no memory statements (their combinational reads extend
    the environment through a separate mechanism). -/
def memFree : List Stmt → Prop
  | [] => True
  | .memory .. :: _ => False
  | _ :: rest => memFree rest

/-- Outside its write set, the combinational fold does not touch the
    environment (memory-free bodies). -/
theorem evalAssigns_frame (we : WEnv) (mems : MEnv) :
    ∀ (body : List Stmt) (env0 env1 : Env),
    evalAssigns we mems body env0 = some env1 →
    memFree body →
    ∀ n, n ∉ writesOf body → env1 n = env0 n
  | [], env0, env1, h, _, n, _ => by
    simp [evalAssigns] at h; simp [h]
  | .assign l r :: rest, env0, env1, h, hm, n, hn => by
    simp only [evalAssigns, Option.bind_eq_bind] at h
    cases hv : evalExpr we env0 r with
    | none => rw [hv] at h; simp at h
    | some v =>
      rw [hv] at h; simp only [Option.bind_some] at h
      have hn' : n ∉ writesOf rest := fun hc =>
        hn (by simp only [writesOf, List.flatMap_cons, List.mem_append]
               exact Or.inr (by simpa [writesOf] using hc))
      have := evalAssigns_frame we mems rest _ env1 h (by simpa [memFree] using hm) n hn'
      rw [this]
      have hnl : n ≠ l := by
        intro hc; exact hn (by simp [writesOf, stmtWrites, hc])
      simp [hnl]
  | .register o c rs i iv :: rest, env0, env1, h, hm, n, hn => by
    simp only [evalAssigns] at h
    exact evalAssigns_frame we mems rest env0 env1 h
      (by simpa [memFree] using hm) n
      (by simpa [writesOf, stmtWrites] using hn)
  | .memory .. :: _, _, _, _, hm, _, _ => by simp [memFree] at hm
  | .inst .. :: rest, env0, env1, h, hm, n, hn => by
    simp only [evalAssigns] at h
    exact evalAssigns_frame we mems rest env0 env1 h
      (by simpa [memFree] using hm) n
      (by simpa [writesOf, stmtWrites] using hn)

/-- No statement reads a name it writes itself (a combinational
    self-loop).  `WO` does not forbid it, but a topologically-sorted
    combinational body never contains one; the checker side is a
    trivial decidable scan. -/
def noSelfRead : List Stmt → Prop
  | [] => True
  | s :: rest => (∀ n ∈ stmtReads s, n ∉ stmtWrites s) ∧ noSelfRead rest

/-- THE FIXPOINT LEMMA: on a well-ordered, memory-free,
    self-loop-free body, the environment the combinational fold
    produces satisfies every assignment as an equation — evaluating a
    wire's RHS in the FINAL environment gives exactly the wire's final
    value.  This is what lets a fully-inlined cone (which re-evaluates
    those RHSs) agree with the fold. -/
theorem evalAssigns_fixpoint (we : WEnv) (mems : MEnv) :
    ∀ (done : List String) (body : List Stmt) (env0 env1 : Env),
    WO done body →
    memFree body →
    noSelfRead body →
    evalAssigns we mems body env0 = some env1 →
    ∀ l r, Stmt.assign l r ∈ body →
    evalExpr we env1 r = some (env1 l)
  | _, [], _, _, _, _, _, _, l, r, hin => by simp at hin
  | done, s :: rest, env0, env1, hwo, hm, hsr, h, l, r, hin => by
    cases hwo with
    | cons hok hreads hw hrest =>
    cases hin with
    | head =>
      -- the head assignment itself
      simp only [evalAssigns, Option.bind_eq_bind] at h
      cases hv : evalExpr we env0 r with
      | none => rw [hv] at h; simp at h
      | some v =>
        rw [hv] at h; simp only [Option.bind_some] at h
        -- final value of l: the tail never rewrites it
        have hlnotr : l ∉ writesOf rest :=
          (hw l (by simp [stmtWrites])).2
        have hl : env1 l = v := by
          have := evalAssigns_frame we mems rest _ env1 h
            (by simpa [memFree] using hm) l hlnotr
          simp [this]
        -- r's reads are untouched by the head write (no self-read)
        -- and by the tail (WO), so re-evaluating in env1 gives v
        have hre : evalExpr we env1 r = evalExpr we env0 r := by
          apply evalExpr_congr
          intro n hn
          have hn1 : n ∉ writesOf rest := hreads n (by simpa [stmtReads] using hn)
          have := evalAssigns_frame we mems rest _ env1 h
            (by simpa [memFree] using hm) n hn1
          rw [this]
          have hnl : n ≠ l := fun hc => by
            have := hsr.1 n (by simpa [stmtReads] using hn)
            simp [stmtWrites, hc] at this
          simp [hnl]
        rw [hre, hv, hl]
    | tail _ hin' =>
      -- the assignment lives in the tail; step the fold once
      cases s with
      | assign l' r' =>
        simp only [evalAssigns, Option.bind_eq_bind] at h
        cases hv : evalExpr we env0 r' with
        | none => rw [hv] at h; simp at h
        | some v =>
          rw [hv] at h; simp only [Option.bind_some] at h
          exact evalAssigns_fixpoint we mems _ rest _ env1 hrest
            (by simpa [memFree] using hm) hsr.2 h l r hin'
      | register o c rs i iv =>
        simp only [evalAssigns] at h
        exact evalAssigns_fixpoint we mems _ rest _ env1 hrest
          (by simpa [memFree] using hm) hsr.2 h l r hin'
      | memory a b c d e f g i j k m n => simp [memFree] at hm
      | inst a b c =>
        simp only [evalAssigns] at h
        exact evalAssigns_fixpoint we mems _ rest _ env1 hrest
          (by simpa [memFree] using hm) hsr.2 h l r hin'

end Fixpoint

section Preserve

/-- Pointwise width agreement between an argument list and its inlined
    image — the exact shape `widthOf`'s per-operator arms consume.
    (Core has no List.Forall₂; this is that, specialized.) -/
inductive WidthMatch (we : WEnv) : List Expr → List Expr → Prop
  | nil : WidthMatch we [] []
  | cons {a a' as as'} (h : widthOf we a' = widthOf we a)
      (hrest : WidthMatch we as as') : WidthMatch we (a :: as) (a' :: as')

theorem widthOfGo_congr (we : WEnv) :
    ∀ {args args'}, WidthMatch we args args' →
      widthOf.go we args' = widthOf.go we args
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h hrest => by
    simp [widthOf.go, h, widthOfGo_congr we hrest]

theorem inlineConeT_width (dm : DefMap) (stopAt : Std.HashMap String Bool)
    (we : WEnv)
    (hwf : ∀ n rhs, dm.get? n = some rhs → stopAt.contains n = false →
      widthOf we rhs = we n) :
    ∀ fuel e, (∀ e', inlineConeT dm stopAt fuel e = .ok e' →
      widthOf we e' = widthOf we e) := by
  intro fuel e
  induction fuel, e using inlineConeT.induct dm stopAt
    (motive2 := fun fuel args => ∀ args',
      inlineConeTL dm stopAt fuel args = .ok args' →
      WidthMatch we args args') with
  | case1 fuel n hs =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, if_pos] at h
    cases h; rfl
  | case2 n hs =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, if_neg, Bool.false_eq_true, ite_false] at h
    simp at h
  | case3 fuel n hs hdm hf =>
    intro e' h
    match fuel, hf with
    | fuel + 1, _ =>
      rw [inlineConeT.eq_def] at h
      dsimp only at h
      simp only [hs, if_neg, Bool.false_eq_true, ite_false, hdm] at h
      simp at h
  | case4 n hs fuel rhs hdm ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, if_neg, Bool.false_eq_true, ite_false, hdm] at h
    rw [ih e' h]  -- h : inlineConeT dm stopAt fuel rhs = .ok e' verbatim
    rw [hwf n rhs hdm (by simpa using hs)]
    simp [Sparkle.IR.Semantics.widthOf]
  | case5 fuel o args ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases hl : inlineConeTL dm stopAt fuel args with
    | error err => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok args' =>
      rw [hl] at h
      simp [Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      have hm := ih args' hl
      cases o <;>
        (cases hm with
         | nil => rfl
         | cons h1 hrest =>
           cases hrest with
           | nil => simp [Sparkle.IR.Semantics.widthOf, h1]
           | cons h2 hrest2 =>
             cases hrest2 with
             | nil => simp [Sparkle.IR.Semantics.widthOf, h1, h2]
             | cons h3 hrest3 =>
               cases hrest3 with
               | nil => simp [Sparkle.IR.Semantics.widthOf, h1, h2, h3]
               | cons h4 hrest4 =>
                 simp [Sparkle.IR.Semantics.widthOf, h1, h2, h3])
  | case6 fuel args ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases hl : inlineConeTL dm stopAt fuel args with
    | error err => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok args' =>
      rw [hl] at h
      simp [Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Sparkle.IR.Semantics.widthOf, widthOfGo_congr we (ih args' hl)]
  | case7 fuel e hi lo ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases he : inlineConeT dm stopAt fuel e with
    | error err => rw [he] at h; simp [Bind.bind, Except.bind] at h
    | ok e0 =>
      rw [he] at h
      simp [Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Sparkle.IR.Semantics.widthOf]
  | case8 x array idx =>
    intro e' h
    rw [inlineConeT.eq_def] at h; simp at h
  | case9 x expr hi lo =>
    intro e' h
    rw [inlineConeT.eq_def] at h; simp at h
  | case10 x e hne1 hne2 hne3 hne4 hne5 hne6 =>
    intro e' h
    cases e with
    | ref n => exact absurd rfl (hne1 n)
    | op o args => exact absurd rfl (hne2 o args)
    | concat args => exact absurd rfl (hne3 args)
    | slice e hi lo => exact absurd rfl (hne4 e hi lo)
    | index a i => exact absurd rfl (hne5 a i)
    | sliceDim e hi lo => exact absurd rfl (hne6 e hi lo)
    | const v w =>
      rw [inlineConeT.eq_def] at h
      dsimp only at h
      simp at h
      simp [← h]
  | case11 x args' h =>
    rw [inlineConeTL.eq_def] at h
    dsimp only at h
    simp at h
    subst h
    exact .nil
  | case12 fuel a rest iha ihrest args' h =>
    rw [inlineConeTL.eq_def] at h
    dsimp only at h
    cases ha : inlineConeT dm stopAt fuel a with
    | error err => rw [ha] at h; simp [Bind.bind, Except.bind] at h
    | ok a' =>
      rw [ha] at h
      cases hr : inlineConeTL dm stopAt fuel rest with
      | error err => rw [hr] at h; simp [Bind.bind, Except.bind] at h
      | ok rest' =>
        rw [hr] at h
        simp [Bind.bind, Except.bind, pure, Except.pure] at h
        rw [← h]
        exact .cons (iha a' ha) (ihrest rest' hr)

theorem inlineConeTL_width (dm : DefMap) (stopAt : Std.HashMap String Bool)
    (we : WEnv)
    (hwf : ∀ n rhs, dm.get? n = some rhs → stopAt.contains n = false →
      widthOf we rhs = we n) :
    ∀ fuel args, (∀ args', inlineConeTL dm stopAt fuel args = .ok args' →
      WidthMatch we args args') := by
  intro fuel args
  induction fuel, args using inlineConeTL.induct dm stopAt
    (motive1 := fun fuel e => ∀ e',
      inlineConeT dm stopAt fuel e = .ok e' →
      widthOf we e' = widthOf we e) with
  | case1 fuel n hs e' h =>
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, if_pos] at h
    cases h; rfl
  | case2 n hs e' h =>
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, if_neg, Bool.false_eq_true, ite_false] at h
    simp at h
  | case3 fuel n hs hdm hf e' h =>
    match fuel, hf with
    | fuel + 1, _ =>
      rw [inlineConeT.eq_def] at h
      dsimp only at h
      simp only [hs, if_neg, Bool.false_eq_true, ite_false, hdm] at h
      simp at h
  | case4 n hs fuel rhs hdm ih e' h =>
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, if_neg, Bool.false_eq_true, ite_false, hdm] at h
    rw [ih e' h]  -- h : inlineConeT dm stopAt fuel rhs = .ok e' verbatim
    rw [hwf n rhs hdm (by simpa using hs)]
    simp [Sparkle.IR.Semantics.widthOf]
  | case5 fuel o args ih e' h =>
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases hl : inlineConeTL dm stopAt fuel args with
    | error err => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok args' =>
      rw [hl] at h
      simp [Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      have hm := ih args' hl
      cases o <;>
        (cases hm with
         | nil => rfl
         | cons h1 hrest =>
           cases hrest with
           | nil => simp [Sparkle.IR.Semantics.widthOf, h1]
           | cons h2 hrest2 =>
             cases hrest2 with
             | nil => simp [Sparkle.IR.Semantics.widthOf, h1, h2]
             | cons h3 hrest3 =>
               cases hrest3 with
               | nil => simp [Sparkle.IR.Semantics.widthOf, h1, h2, h3]
               | cons h4 hrest4 =>
                 simp [Sparkle.IR.Semantics.widthOf, h1, h2, h3])
  | case6 fuel args ih e' h =>
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases hl : inlineConeTL dm stopAt fuel args with
    | error err => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok args' =>
      rw [hl] at h
      simp [Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Sparkle.IR.Semantics.widthOf, widthOfGo_congr we (ih args' hl)]
  | case7 fuel e hi lo ih e' h =>
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases he : inlineConeT dm stopAt fuel e with
    | error err => rw [he] at h; simp [Bind.bind, Except.bind] at h
    | ok e0 =>
      rw [he] at h
      simp [Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      simp [Sparkle.IR.Semantics.widthOf]
  | case8 x array idx e' h =>
    rw [inlineConeT.eq_def] at h; simp at h
  | case9 x expr hi lo e' h =>
    rw [inlineConeT.eq_def] at h; simp at h
  | case10 x e hne1 hne2 hne3 hne4 hne5 hne6 e' h =>
    cases e with
    | ref n => exact absurd rfl (hne1 n)
    | op o args => exact absurd rfl (hne2 o args)
    | concat args => exact absurd rfl (hne3 args)
    | slice e hi lo => exact absurd rfl (hne4 e hi lo)
    | index a i => exact absurd rfl (hne5 a i)
    | sliceDim e hi lo => exact absurd rfl (hne6 e hi lo)
    | const v w =>
      rw [inlineConeT.eq_def] at h
      dsimp only at h
      simp at h
      simp [← h]
  | case11 x =>
    intro args' h
    rw [inlineConeTL.eq_def] at h
    dsimp only at h
    simp at h
    subst h
    exact .nil
  | case12 fuel a rest iha ihrest =>
    intro args' h
    rw [inlineConeTL.eq_def] at h
    dsimp only at h
    cases ha : inlineConeT dm stopAt fuel a with
    | error err => rw [ha] at h; simp [Bind.bind, Except.bind] at h
    | ok a' =>
      rw [ha] at h
      cases hr : inlineConeTL dm stopAt fuel rest with
      | error err => rw [hr] at h; simp [Bind.bind, Except.bind] at h
      | ok rest' =>
        rw [hr] at h
        simp [Bind.bind, Except.bind, pure, Except.pure] at h
        rw [← h]
        exact .cons (iha a' ha) (ihrest rest' hr)


/-- The concat combiner's running-offset fold reads only the FIRST
    component widths of the zip; width-matched lists fold alike. -/
theorem zipFoldW_congr (we : WEnv) :
    ∀ {as as'}, WidthMatch we as as' → ∀ (vs : List Nat) (acc : Nat),
      ((as'.zip vs).foldl (fun a (p : Expr × Nat) =>
        a + widthOf we p.1) acc)
      = ((as.zip vs).foldl (fun a (p : Expr × Nat) =>
        a + widthOf we p.1) acc)
  | [], [], _, _, _ => rfl
  | _ :: _, _ :: _, .cons h hrest, vs, acc => by
    cases vs with
    | nil => rfl
    | cons v vs' =>
      simp only [List.zip_cons_cons, List.foldl_cons, h]
      exact zipFoldW_congr we hrest vs' _

/-- `evalOp` reads its expression arguments only through `widthOf`
    (not/asr/signed compares) and through the list SHAPE; a
    width-matched replacement list computes the same value. -/
theorem evalOp_congr (we : WEnv) {args args' : List Expr}
    (hm : WidthMatch we args args') (o : Operator) (vals : List Nat)
    (w : Nat) : evalOp we o args' vals w = evalOp we o args vals w := by
  cases o <;>
    (cases hm with
     | nil => rfl
     | cons h1 hrest =>
       cases hrest with
       | nil =>
         (cases vals with
             | nil => simp_all [evalOp]
             | cons v1 t1 =>
               cases t1 with
               | nil => simp_all [evalOp]
               | cons v2 t2 =>
                 cases t2 with
                 | nil => simp_all [evalOp]
                 | cons v3 t3 =>
                   cases t3 with
                   | nil => simp_all [evalOp]
                   | cons v4 t4 => simp_all [evalOp])
       | cons h2 hrest2 =>
         cases hrest2 with
         | nil =>
           (cases vals with
             | nil => simp_all [evalOp]
             | cons v1 t1 =>
               cases t1 with
               | nil => simp_all [evalOp]
               | cons v2 t2 =>
                 cases t2 with
                 | nil => simp_all [evalOp]
                 | cons v3 t3 =>
                   cases t3 with
                   | nil => simp_all [evalOp]
                   | cons v4 t4 => simp_all [evalOp])
         | cons h3 hrest3 =>
           cases hrest3 with
           | nil =>
             (cases vals with
             | nil => simp_all [evalOp]
             | cons v1 t1 =>
               cases t1 with
               | nil => simp_all [evalOp]
               | cons v2 t2 =>
                 cases t2 with
                 | nil => simp_all [evalOp]
                 | cons v3 t3 =>
                   cases t3 with
                   | nil => simp_all [evalOp]
                   | cons v4 t4 => simp_all [evalOp])
           | cons h4 hrest4 =>
             (cases vals with
             | nil => simp_all [evalOp]
             | cons v1 t1 =>
               cases t1 with
               | nil => simp_all [evalOp]
               | cons v2 t2 =>
                 cases t2 with
                 | nil => simp_all [evalOp]
                 | cons v3 t3 =>
                   cases t3 with
                   | nil => simp_all [evalOp]
                   | cons v4 t4 => simp_all [evalOp]))

/-- The concat combiner under a width-matched expression list. -/
theorem evalGo_congr (we : WEnv) :
    ∀ {args args'}, WidthMatch we args args' → ∀ (vals : List Nat),
      evalExpr.go we args' vals = evalExpr.go we args vals
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, .cons h hrest, vals => by
    cases vals with
    | nil => rfl
    | cons v vs =>
      simp only [evalExpr.go, h, zipFoldW_congr we hrest,
        evalGo_congr we hrest]

/-- THE SEAM (expression half): under the fold's fixpoint environment
    (`evalAssigns_fixpoint`) and the assignment-width discipline
    (`hwf` — literally `BFrag.assign`'s condition, where the two
    certified arcs' hypotheses meet), inlining preserves evaluation:
    the fully-inlined cone computes exactly what the wire-by-wire fold
    computed. -/
theorem inlineConeT_eval (dm : DefMap) (stopAt : Std.HashMap String Bool)
    (we : WEnv) (env : Env)
    (hwf : ∀ n rhs, dm.get? n = some rhs → stopAt.contains n = false →
      widthOf we rhs = we n)
    (hfix : ∀ n rhs, dm.get? n = some rhs → stopAt.contains n = false →
      evalExpr we env rhs = some (env n)) :
    ∀ fuel e, (∀ e', inlineConeT dm stopAt fuel e = .ok e' →
      evalExpr we env e' = evalExpr we env e) := by
  intro fuel e
  induction fuel, e using inlineConeT.induct dm stopAt
    (motive2 := fun fuel args => ∀ args',
      inlineConeTL dm stopAt fuel args = .ok args' →
      evalList we env args' = evalList we env args) with
  | case1 fuel n hs =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, if_pos] at h
    cases h; rfl
  | case2 n hs =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, Bool.false_eq_true, ite_false] at h
    simp at h
  | case3 fuel n hs hdm hf =>
    intro e' h
    match fuel, hf with
    | fuel + 1, _ =>
      rw [inlineConeT.eq_def] at h
      dsimp only at h
      simp only [hs, Bool.false_eq_true, ite_false, hdm] at h
      simp at h
  | case4 n hs fuel rhs hdm ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    simp only [hs, Bool.false_eq_true, ite_false, hdm] at h
    rw [ih e' h]
    rw [hfix n rhs hdm (by simpa using hs)]
    simp [evalExpr]
  | case5 fuel o args ih =>
    intro e' h
    have hw := inlineConeT_width dm stopAt we hwf fuel (.op o args) e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases hl : inlineConeTL dm stopAt fuel args with
    | error err => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok args' =>
      rw [hl] at h
      simp [Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      have hm := inlineConeTL_width dm stopAt we hwf fuel args args' hl
      simp only [evalExpr, ih args' hl, hw,
        evalOp_congr we hm o]
  | case6 fuel args ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases hl : inlineConeTL dm stopAt fuel args with
    | error err => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok args' =>
      rw [hl] at h
      simp [Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      have hm := inlineConeTL_width dm stopAt we hwf fuel args args' hl
      simp only [evalExpr, ih args' hl, evalGo_congr we hm]
  | case7 fuel e hi lo ih =>
    intro e' h
    rw [inlineConeT.eq_def] at h
    dsimp only at h
    cases he : inlineConeT dm stopAt fuel e with
    | error err => rw [he] at h; simp [Bind.bind, Except.bind] at h
    | ok e0 =>
      rw [he] at h
      simp [Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      simp only [evalExpr, ih e0 he]
  | case8 x array idx =>
    intro e' h
    rw [inlineConeT.eq_def] at h; dsimp only at h; simp at h
  | case9 x expr hi lo =>
    intro e' h
    rw [inlineConeT.eq_def] at h; dsimp only at h; simp at h
  | case10 x e hne1 hne2 hne3 hne4 hne5 hne6 =>
    intro e' h
    cases e with
    | ref n => exact absurd rfl (hne1 n)
    | op o args => exact absurd rfl (hne2 o args)
    | concat args => exact absurd rfl (hne3 args)
    | slice e hi lo => exact absurd rfl (hne4 e hi lo)
    | index a i => exact absurd rfl (hne5 a i)
    | sliceDim e hi lo => exact absurd rfl (hne6 e hi lo)
    | const v w =>
      rw [inlineConeT.eq_def] at h
      dsimp only at h
      simp at h
      simp [← h]
  | case11 x args' h =>
    rw [inlineConeTL.eq_def] at h
    dsimp only at h
    simp at h
    subst h; rfl
  | case12 fuel a rest iha ihrest args' h =>
    rw [inlineConeTL.eq_def] at h
    dsimp only at h
    cases ha : inlineConeT dm stopAt fuel a with
    | error err => rw [ha] at h; simp [Bind.bind, Except.bind] at h
    | ok a' =>
      rw [ha] at h
      cases hr : inlineConeTL dm stopAt fuel rest with
      | error err => rw [hr] at h; simp [Bind.bind, Except.bind] at h
      | ok rest' =>
        rw [hr] at h
        simp [Bind.bind, Except.bind, pure, Except.pure] at h
        subst h
        simp only [evalList, iha a' ha, ihrest rest' hr]

/-- `buildDefMap` membership: a binding in the def-map came from an
    assign in the body. -/
theorem buildDefMap_mem :
    ∀ (body : List Stmt) (m0 : Sparkle.IR.Optimize.DefMap) (n : String)
      (rhs : Expr),
    (body.foldl (fun m s => match s with
      | .assign lhs r => m.insert lhs r
      | _ => m) m0).get? n = some rhs →
    Stmt.assign n rhs ∈ body ∨ m0.get? n = some rhs
  | [], _, _, _, h => Or.inr h
  | s :: rest, m0, n, rhs, h => by
    cases s with
    | assign l r =>
      rcases buildDefMap_mem rest _ n rhs h with hmem | hget
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · by_cases hln : l = n
        · subst hln
          simp only [Std.HashMap.get?_insert] at hget
          simp at hget
          cases hget
          exact Or.inl (List.mem_cons_self ..)
        · simp only [Std.HashMap.get?_insert] at hget
          simp [hln] at hget
          exact Or.inr hget
    | register o c rs i iv =>
      rcases buildDefMap_mem rest _ n rhs h with hmem | hget
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · exact Or.inr hget
    | memory a b c d e f g i j k mm nn =>
      rcases buildDefMap_mem rest _ n rhs h with hmem | hget
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · exact Or.inr hget
    | inst a b c =>
      rcases buildDefMap_mem rest _ n rhs h with hmem | hget
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · exact Or.inr hget

/-- THE SEAM, composed: on a well-ordered, memory-free, self-loop-free
    body, evaluating a fully-inlined cone in the environment the
    combinational fold produced gives the same value as the original
    expression — the two certified arcs now speak about the same
    numbers.  `hwf` is BFrag.assign's width discipline; everything
    else is decidable per instance. -/
theorem cone_agrees_with_fold (we : WEnv) (mems : MEnv)
    {done : List String} {body : List Stmt} {env0 env1 : Env}
    (stopAt : Std.HashMap String Bool)
    (hWO : Sparkle.IR.Reorder.WO done body)
    (hm : memFree body) (hsr : noSelfRead body)
    (hrun : evalAssigns we mems body env0 = some env1)
    (hwf : ∀ n rhs,
      (Sparkle.IR.Optimize.buildDefMap body).get? n = some rhs →
      stopAt.contains n = false → widthOf we rhs = we n)
    {fuel : Nat} {e e' : Expr}
    (hinl : inlineConeT (Sparkle.IR.Optimize.buildDefMap body)
      stopAt fuel e = .ok e') :
    evalExpr we env1 e' = evalExpr we env1 e := by
  apply inlineConeT_eval _ _ we env1 hwf ?hfix fuel e e' hinl
  case hfix =>
    intro n rhs hget hstop
    have hmem : Stmt.assign n rhs ∈ body := by
      rcases buildDefMap_mem body {} n rhs hget with hmem | hget0
      · exact hmem
      · simp at hget0
    exact evalAssigns_fixpoint we mems done body env0 env1
      hWO hm hsr hrun n rhs hmem

end Preserve

/- ------------------------------------------------------------------ -/
/- Slice-resolution twin (defs only — the theorem stack lives in
   Tools/ConeFoldSlices.lean).  The defs live HERE so the goal
   generators (Tools/VerifyElab.lean, Tools/DeepElab.lean) can call
   the twins directly without an import cycle: the spliced cones are
   then BY CONSTRUCTION the functions the seam theorems cover. -/
section ResolveSlicesDefs

mutual
-- Flatten nested concats (the HList pack nests to the right); twin of
-- the shipping arm's local `let rec flatten`.
def flattenE : Expr → List Expr
  | .concat ps => flattenL ps
  | e => [e]

def flattenL : List Expr → List Expr
  | [] => []
  | a :: rest => flattenE a ++ flattenL rest
end

/-- Twin of the shipping arm's local `widthOfPart` closure. -/
def widthOfPartT (wt : Std.HashMap String Nat) : Expr → Option Nat
  | .const _ w => some w
  | .ref n => wt.get? n
  | .slice _ h l => some (h - l + 1)
  | _ => none

/-- Structural twin of the shipping arm's window-search `for` loop.
    The lists are MSB-first; `acc` is the total width of the REMAINING
    parts, so the head occupies `[acc - w, acc - 1]`. -/
def findWindow (hi lo : Nat) : List Expr → List Nat → Nat → Option Expr
  | p :: ps, w :: ws, acc =>
    if 0 < w ∧ lo ≤ hi ∧ lo = acc - w ∧ hi = acc - 1 then some p
    else if 0 < w ∧ lo ≤ hi ∧ acc - w ≤ lo ∧ hi ≤ acc - 1 then
      some (.slice p (hi - (acc - w)) (lo - (acc - w)))
    else findWindow hi lo ps ws (acc - w)
  | _, _, _ => none

mutual
/-- Total twin of the shipping `partial def resolveSlicesW`
    (Tools/VerifyElab.lean).  Fuel decreases on the self-re-entering
    calls; the expression shrinks on the rest — (fuel, e) is the
    measure, as for `inlineConeT`. -/
def resolveSlicesT (wt : Std.HashMap String Nat) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, .slice (.concat parts0) hi lo =>
    let parts := resolveSlicesTL wt fuel (flattenL parts0)
    match parts.mapM (widthOfPartT wt) with
    | none => .slice (.concat parts) hi lo
    | some ws =>
      match findWindow hi lo parts ws (ws.foldl (· + ·) 0) with
      | some r => r
      | none => .slice (.concat parts) hi lo
  | fuel + 1, .op o args => .op o (resolveSlicesTL wt fuel args)
  | fuel + 1, .concat args => .concat (resolveSlicesTL wt fuel args)
  | fuel + 1, .slice e hi lo =>
    match resolveSlicesT wt fuel e with
    | .concat parts => resolveSlicesT wt fuel (.slice (.concat parts) hi lo)
    | .ref n =>
      if lo == 0 && wt.get? n == some (hi + 1) then .ref n
      else .slice (.ref n) hi lo
    | .slice inner ihi ilo =>
      if ilo + hi ≤ ihi ∧ lo ≤ hi then
        resolveSlicesT wt fuel (.slice inner (ilo + hi) (ilo + lo))
      else .slice (.slice inner ihi ilo) hi lo
    | e' => .slice e' hi lo
  | _, e => e

def resolveSlicesTL (wt : Std.HashMap String Nat) :
    Nat → List Expr → List Expr
  | _, [] => []
  | fuel, a :: rest =>
    resolveSlicesT wt fuel a :: resolveSlicesTL wt fuel rest
end

end ResolveSlicesDefs

end Tools.ConeFold
