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

end Tools.ConeFold
