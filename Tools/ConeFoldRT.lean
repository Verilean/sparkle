import Tools.ConeFoldOpt
import Tools.ConeFoldMem

/-!
  The printed text as translation validation — the 1-bit normal forms.

  The `#verify_elab_deep` shared route replays its chain over two more
  bodies (Tools/DeepElab.lean, `sharedBridge`): the OPTIMIZED body
  (`optimizeModule m`, the module `toVerilog` prints) and the body the
  shipping parser+lowerer reads back from that text.  As on the
  `#verify_elab` route, the bridge is a per-instance SYNTACTIC equality
  of cones after a normaliser with an evaluation-preservation proof.
  `stripMask` (Tools/ConeFoldOpt.lean) handles the optimizer's one
  rewrite.  The printed text introduces two more, MEASURED on
  `crc16CcittHW` (2026-09-14): the printer emits a 1-bit `not x` as
  `1'(x ^ 1'd1)` and the lowerer reads the size cast back as a
  zero-extend-and-slice, so `not [x]` comes back as
  `slice (concat [const 0 1, xor [x, const 1 1]]) 0 0`.  `rtNorm` maps
  both forms to `not [x]`; `rtNorm_eval` proves the value unchanged.

  The slice rule needs the sliced operand's value to fit one bit, which
  `evalExpr_bounded` gives on a bounded environment under the mux
  arm-width side condition (`widthOk`).  The side condition is stated on
  the NORMALISED term, which is what the bridge compares syntactically
  to the original cone — so per instance it is one closed Boolean.
-/

open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.SVParser.RoundtripProof (eval_const_ofNat)

namespace Tools.ConeFold

/-- Peephole at an operator node: a 1-bit `x ^ 1` is `not x`. -/
def rtOp (we : WEnv) (o : Operator) (args : List Expr) : Expr :=
  match o, args with
  | .xor, [x, .const (.ofNat 1) 1] =>
    if widthOf we x == 1 then .op .not [x] else .op .xor [x, .const (.ofNat 1) 1]
  | o, args => .op o args

/-- Peephole at a slice node: the lowered 1-bit size cast
    `{1'b0, x}[0:0]` of a 1-bit `x` is `x`. -/
def rtSlice (we : WEnv) (e : Expr) (hi lo : Nat) : Expr :=
  match e, hi, lo with
  | .concat [.const (.ofNat 0) 1, x], 0, 0 =>
    if widthOf we x == 1 then x else .slice (.concat [.const (.ofNat 0) 1, x]) 0 0
  | e, hi, lo => .slice e hi lo

mutual
/-- Bottom-up normalisation of the printed-text 1-bit forms. -/
def rtNorm (we : WEnv) : Expr → Expr
  | .op o args => rtOp we o (rtNormL we args)
  | .concat args => .concat (rtNormL we args)
  | .slice e hi lo => rtSlice we (rtNorm we e) hi lo
  | e => e
def rtNormL (we : WEnv) : List Expr → List Expr
  | [] => []
  | a :: rest => rtNorm we a :: rtNormL we rest
end

/- ---- width preservation ---- -/

theorem rtOp_width (we : WEnv) (o : Operator) (args : List Expr) :
    widthOf we (rtOp we o args) = widthOf we (.op o args) := by
  unfold rtOp
  split
  · split
    · rename_i h
      simp only [beq_iff_eq] at h
      simp [widthOf, h]
    · rfl
  · rfl

theorem rtSlice_width (we : WEnv) (e : Expr) (hi lo : Nat) :
    widthOf we (rtSlice we e hi lo) = widthOf we (.slice e hi lo) := by
  unfold rtSlice
  split
  · split
    · rename_i h
      simp only [beq_iff_eq] at h
      simp [widthOf, h]
    · rfl
  · rfl

mutual
theorem rtNorm_width (we : WEnv) :
    ∀ e, widthOf we (rtNorm we e) = widthOf we e
  | .op o args => by
    simp only [rtNorm]
    rw [rtOp_width]
    exact widthOf_op_shape _ o (rtNormL_widthMatch we args)
  | .concat args => by
    simp only [rtNorm, widthOf]
    exact widthOfGo_congr _ (rtNormL_widthMatch we args)
  | .slice e hi lo => by
    simp only [rtNorm]
    rw [rtSlice_width]
    simp [widthOf]
  | .const .. => by simp [rtNorm]
  | .ref .. => by simp [rtNorm]
  | .sliceDim .. => by simp [rtNorm]
  | .index .. => by simp [rtNorm]

theorem rtNormL_widthMatch (we : WEnv) :
    ∀ args, WidthMatch we args (rtNormL we args)
  | [] => by simp only [rtNormL]; exact .nil
  | a :: rest => by
    simp only [rtNormL]
    exact .cons (rtNorm_width we a) (rtNormL_widthMatch we rest)
end

/- ---- the side condition flows down through the peepholes ---- -/

theorem rtOp_widthOkL (we : WEnv) (o : Operator) (args : List Expr)
    (h : widthOk we (rtOp we o args) = true) : widthOkL we args = true := by
  unfold rtOp at h
  split at h
  · split at h
    · simp only [widthOk, widthOkL, Bool.and_eq_true] at h ⊢
      exact ⟨h.2.1, trivial, trivial⟩
    · simp only [widthOk, Bool.and_eq_true] at h
      exact h.2
  · simp only [widthOk, Bool.and_eq_true] at h
    exact h.2

theorem rtSlice_widthOk (we : WEnv) (e : Expr) (hi lo : Nat)
    (h : widthOk we (rtSlice we e hi lo) = true) : widthOk we e = true := by
  unfold rtSlice at h
  split at h
  · split at h
    · simp only [widthOk, widthOkL, Bool.and_eq_true]
      exact ⟨trivial, h, trivial⟩
    · simpa [widthOk] using h
  · simpa [widthOk] using h

/- ---- evaluation ---- -/

theorem rtOp_eval (we : WEnv) (env : Env) (o : Operator) (args : List Expr) :
    evalExpr we env (rtOp we o args) = evalExpr we env (.op o args) := by
  unfold rtOp
  split
  · split
    · rename_i x h
      simp only [beq_iff_eq] at h
      cases hx : evalExpr we env x with
      | none => simp [evalExpr, evalList, hx]
      | some a =>
        have hc : evalExpr we env (.const (.ofNat 1) 1) = some 1 :=
          eval_const_ofNat we env 1 1 (by decide)
        rw [show evalExpr we env (.op .not [x])
              = (evalList we env [x]).bind
                  (fun vals => evalOp we .not [x] vals (widthOf we (.op .not [x])))
            from rfl]
        rw [show evalExpr we env (.op .xor [x, .const (.ofNat 1) 1])
              = (evalList we env [x, .const (.ofNat 1) 1]).bind
                  (fun vals => evalOp we .xor [x, .const (.ofNat 1) 1] vals
                    (widthOf we (.op .xor [x, .const (.ofNat 1) 1])))
            from rfl]
        rw [show evalList we env [x] = (evalExpr we env x).bind (fun v => some [v]) from rfl]
        rw [show evalList we env [x, .const (.ofNat 1) 1]
              = (evalExpr we env x).bind (fun v0 =>
                  (evalExpr we env (.const (.ofNat 1) 1)).bind fun v1 => some [v0, v1])
            from rfl]
        rw [hx, hc]
        simp [evalOp, widthOf, h]
    · rfl
  · rfl

theorem rtSlice_eval (we : WEnv) (env : Env) (hb : ∀ n, env n < 2 ^ we n)
    (e : Expr) (hi lo : Nat) (hok : widthOk we (rtSlice we e hi lo) = true) :
    evalExpr we env (rtSlice we e hi lo) = evalExpr we env (.slice e hi lo) := by
  unfold rtSlice at hok ⊢
  split
  · split
    · rename_i x h
      simp only [beq_iff_eq] at h
      simp only [h, BEq.rfl, ite_true] at hok
      cases hx : evalExpr we env x with
      | none => simp [evalExpr, evalList, hx]
      | some v =>
        have hv : v < 2 ^ 1 := h ▸ evalExpr_bounded we env hb x v hok hx
        have hc : evalExpr we env (.const (.ofNat 0) 1) = some 0 :=
          eval_const_ofNat we env 0 1 (by decide)
        have e1 : evalExpr we env (.concat [.const (.ofNat 0) 1, x])
            = some (evalExpr.go we [.const (.ofNat 0) 1, x] [0, v]) := by
          rw [show evalExpr we env (.concat [.const (.ofNat 0) 1, x])
                = (evalList we env [.const (.ofNat 0) 1, x]).bind
                    (fun vals => some (evalExpr.go we [.const (.ofNat 0) 1, x] vals))
              from rfl]
          rw [show evalList we env [.const (.ofNat 0) 1, x]
                = (evalExpr we env (.const (.ofNat 0) 1)).bind (fun v0 =>
                    (evalList we env [x]).bind fun vs => some (v0 :: vs))
              from rfl]
          rw [show evalList we env [x] = (evalExpr we env x).bind (fun v1 => some [v1]) from rfl]
          rw [hc, hx]
          rfl
        rw [show evalExpr we env (.slice (.concat [.const (.ofNat 0) 1, x]) 0 0)
              = (evalExpr we env (.concat [.const (.ofNat 0) 1, x])).bind
                  (fun c => some (mask (0 - 0 + 1) (c >>> 0)))
            from rfl]
        rw [e1]
        simp only [Option.bind_some, Option.some.injEq]
        simp only [evalExpr.go, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
          List.foldl_nil, widthOf, h, mask, Nat.shiftRight_zero, Nat.shiftLeft_zero]
        have h0 : (0 : Nat) % 2 ^ 1 = 0 := by decide
        simp only [h0, Nat.zero_shiftLeft, Nat.zero_or, Nat.or_zero, Nat.zero_add]
        rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hv]
    · rfl
  · rfl

mutual
/-- **Normalisation preserves evaluation** on bounded environments,
    under the mux arm-width side condition on the normalised term. -/
theorem rtNorm_eval (we : WEnv) (env : Env) (hb : ∀ n, env n < 2 ^ we n) :
    ∀ e, widthOk we (rtNorm we e) = true →
      evalExpr we env (rtNorm we e) = evalExpr we env e
  | .op o args, hok => by
    simp only [rtNorm] at hok ⊢
    rw [rtOp_eval]
    have hwm := rtNormL_widthMatch we args
    have hokL : widthOkL we (rtNormL we args) = true := rtOp_widthOkL we o _ hok
    simp only [evalExpr, rtNormL_eval we env hb args hokL, widthOf_op_shape _ o hwm]
    cases evalList we env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [evalOp_congr _ hwm o vals _]
  | .concat args, hok => by
    simp only [rtNorm, widthOk] at hok ⊢
    simp only [evalExpr, rtNormL_eval we env hb args hok]
    cases evalList we env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some,
        evalGo_congr _ (rtNormL_widthMatch we args) vals]
  | .slice e hi lo, hok => by
    simp only [rtNorm] at hok ⊢
    rw [rtSlice_eval we env hb _ hi lo hok]
    have hok' : widthOk we (rtNorm we e) = true := rtSlice_widthOk we _ hi lo hok
    simp only [evalExpr, rtNorm_eval we env hb e hok']
  | .const .., _ => by simp [rtNorm]
  | .ref .., _ => by simp [rtNorm]
  | .sliceDim .., _ => by simp [rtNorm]
  | .index .., _ => by simp [rtNorm]

theorem rtNormL_eval (we : WEnv) (env : Env) (hb : ∀ n, env n < 2 ^ we n) :
    ∀ args, widthOkL we (rtNormL we args) = true →
      evalList we env (rtNormL we args) = evalList we env args
  | [], _ => by simp [rtNormL]
  | a :: rest, hok => by
    simp only [rtNormL, widthOkL, Bool.and_eq_true] at hok ⊢
    simp only [evalList, rtNorm_eval we env hb a hok.1, rtNormL_eval we env hb rest hok.2]
end

/-- The composed per-instance bridge fact: when the normalised,
    mask-stripped cone of the replayed body IS the normalised original
    cone (one `native_decide` per cone), the two cones evaluate alike on
    a bounded environment. -/
theorem rtBridge_eval (wof : String → Option Nat) (env : Env)
    (hb : ∀ n, env n < 2 ^ weW wof n) (cX cO : Expr)
    (heq : rtNorm (weW wof) (stripMask wof cX) = rtNorm (weW wof) cO)
    (hokX : widthOk (weW wof) (rtNorm (weW wof) (stripMask wof cX)) = true)
    (hokO : widthOk (weW wof) (rtNorm (weW wof) cO) = true) :
    evalExpr (weW wof) env cO = evalExpr (weW wof) env cX := by
  rw [← rtNorm_eval _ env hb cO hokO, ← heq, rtNorm_eval _ env hb _ hokX,
    stripMask_eval wof env hb]

/-! ### F2: a LIST-backed stop set

`hwfCheck` / `stopAtFrozenCheck` consult the stop set only through
`contains`, but `Std.HashMap.contains` hashes through `USize` and the
KERNEL cannot reduce it — measured 2026-09-16 on shareX4: `decide`
fails on `stopAtM.contains "_gen_w0" = true` itself, so every checker
keyed on the map is stuck on `native_decide` no matter how simple it
is.  A `List String` stop set with `elem` decides fine, so the checkers
get list-keyed twins here and the SOUNDNESS route stays the existing
HashMap theorems, bridged by `stopOfL_contains` — the generator proves
ONE agreement fact per stop set and keeps using the proven
`hwfCheck_sound` / `stopAtFrozenCheck_sound`.

This does NOT unblock `inlineConeT`'s equations: those also read the
DEFINITION MAP (`dm.get?`), the same `USize` problem one table over.
The cone equations therefore stay `native_decide` until the definition
map is list-backed too — a separate change. -/

/-- The HashMap a list stop set induces (what the generator builds). -/
def stopOfL (l : List String) : Std.HashMap String Bool :=
  l.foldl (fun h x => h.insert x true) {}

/-- List-keyed `hwfCheck`. -/
def hwfCheckL (we : WEnv) (stop : List String) : List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (stop.elem l || widthOf we r == we l) && hwfCheckL we stop rest
  | _ :: rest => hwfCheckL we stop rest

/-- List-keyed `stopAtFrozenCheck`. -/
def stopAtFrozenCheckL (stop : List String) : List Stmt → Bool
  | [] => true
  | s :: rest =>
    (Sparkle.IR.Reorder.stmtWrites s).all (fun n => !stop.elem n)
      && stopAtFrozenCheckL stop rest

/-- **The bridge**, proven per stop set by the generator (`decide` on
    the list side, one `native_decide` for the map side): the two
    lookups agree on every name the body can mention.  Stated over the
    names actually consulted, so it is a closed Boolean. -/
def stopAgreeOn (l : List String) (names : List String) : Prop :=
  ∀ n ∈ names, (stopOfL l).contains n = l.elem n

/-- With agreement on the assign targets, the list checker implies the
    HashMap one's hypothesis — so `hwfCheck_sound` applies unchanged. -/
theorem hwfCheckL_to_hwfCheck (we : WEnv) (l : List String) :
    ∀ (body : List Stmt),
      (∀ n ∈ body.filterMap (fun s => match s with
        | .assign t _ => some t | _ => none), (stopOfL l).contains n = l.elem n) →
      hwfCheckL we l body = true → hwfCheck we (stopOfL l) body = true
  | [], _, _ => rfl
  | .assign t r :: rest, hag, h => by
    simp only [hwfCheckL, Bool.and_eq_true] at h
    simp only [hwfCheck, Bool.and_eq_true]
    refine ⟨?_, hwfCheckL_to_hwfCheck we l rest (fun n hn => hag n (by simp [hn])) h.2⟩
    have ht : (stopOfL l).contains t = l.elem t := hag t (by simp)
    rw [ht]; exact h.1
  | .register .. :: rest, hag, h => by
    simp only [hwfCheckL] at h
    simpa only [hwfCheck] using hwfCheckL_to_hwfCheck we l rest (fun n hn => hag n (by simpa using hn)) h
  | .memory .. :: rest, hag, h => by
    simp only [hwfCheckL] at h
    simpa only [hwfCheck] using hwfCheckL_to_hwfCheck we l rest (fun n hn => hag n (by simpa using hn)) h
  | .inst .. :: rest, hag, h => by
    simp only [hwfCheckL] at h
    simpa only [hwfCheck] using hwfCheckL_to_hwfCheck we l rest (fun n hn => hag n (by simpa using hn)) h

/-- Same for the frozen check, over the names statements WRITE. -/
theorem stopAtFrozenCheckL_to_check (l : List String) :
    ∀ (body : List Stmt),
      (∀ n ∈ body.flatMap Sparkle.IR.Reorder.stmtWrites,
        (stopOfL l).contains n = l.elem n) →
      stopAtFrozenCheckL l body = true → stopAtFrozenCheck (stopOfL l) body = true
  | [], _, _ => rfl
  | s :: rest, hag, h => by
    simp only [stopAtFrozenCheckL, Bool.and_eq_true, List.all_eq_true] at h
    simp only [stopAtFrozenCheck, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun n hn => ?_, stopAtFrozenCheckL_to_check l rest
      (fun n hn => hag n (by
        simp only [List.flatMap_cons, List.mem_append]
        exact .inr hn)) h.2⟩
    have := h.1 n hn
    rw [hag n (by
      simp only [List.flatMap_cons, List.mem_append]
      exact .inl hn)]
    exact this

/-! ### F2: a LIST-backed DEFINITION MAP

`inlineConeT` consumes the definition map only through `dm.get?` — the
same shape the stop set had with `contains`, one table over.  So the
cone equation `inlineConeT dm stop fuel e = .ok cone` can run on a LIST
definition map in the kernel, provided the list lookup agrees with the
HashMap one on the names the walk actually consults.

The agreement cannot be stated over "the names consulted" without
re-running the walk, so it is stated over the WHOLE list of assign
targets (a closed Boolean, and a superset of what any cone reads).  The
generator proves it once per body and rewrites the map argument. -/

/-- List-backed definition map lookup. -/
def dmGetL (l : List (String × Expr)) (n : String) : Option Expr :=
  (l.find? (fun p => p.1 == n)).map (·.2)

/-- The HashMap a list definition map induces (what `buildDefMap`
    builds, as a fold over the body's assigns). -/
def dmOfL (l : List (String × Expr)) : Sparkle.IR.Optimize.DefMap :=
  l.foldl (fun m p => m.insert p.1 p.2) {}

/-- The body's assign targets and right-hand sides, in body order — the
    list `buildDefMap` folds over. -/
def dmListOf : List Stmt → List (String × Expr)
  | [] => []
  | .assign l r :: rest => (l, r) :: dmListOf rest
  | _ :: rest => dmListOf rest

/-- `buildDefMap` IS the fold of `dmListOf` (both walk the body's
    assigns in order, inserting into the same empty map). -/
theorem buildDefMap_eq_dmOfL :
    ∀ (body : List Stmt) (m : Sparkle.IR.Optimize.DefMap),
      body.foldl (fun m s => match s with
        | .assign lhs rhs => m.insert lhs rhs
        | _ => m) m
      = (dmListOf body).foldl (fun m p => m.insert p.1 p.2) m
  | [], _ => rfl
  | .assign l r :: rest, m => by
    simp only [List.foldl_cons, dmListOf]
    exact buildDefMap_eq_dmOfL rest (m.insert l r)
  | .register .. :: rest, m => by
    simp only [List.foldl_cons, dmListOf]; exact buildDefMap_eq_dmOfL rest m
  | .memory .. :: rest, m => by
    simp only [List.foldl_cons, dmListOf]; exact buildDefMap_eq_dmOfL rest m
  | .inst .. :: rest, m => by
    simp only [List.foldl_cons, dmListOf]; exact buildDefMap_eq_dmOfL rest m

theorem buildDefMap_dmOfL (body : List Stmt) :
    Sparkle.IR.Optimize.buildDefMap body = dmOfL (dmListOf body) :=
  buildDefMap_eq_dmOfL body {}

/-- **The cone equation on a list map transfers to the HashMap one**,
    given lookup agreement on every assign target.  `inlineConeT` reads
    the map only at `.ref` nodes through `get?`, so agreeing lookups
    give an identical walk — proven by the walk's own induction. -/
theorem inlineConeT_dm_congr (dm1 dm2 : Sparkle.IR.Optimize.DefMap)
    (stopAt : Std.HashMap String Bool)
    (hag : ∀ n, dm1.get? n = dm2.get? n) :
    ∀ fuel e, inlineConeT dm1 stopAt fuel e = inlineConeT dm2 stopAt fuel e := by
  intro fuel e
  induction fuel, e using inlineConeT.induct dm1 stopAt
    (motive2 := fun fuel args => inlineConeTL dm1 stopAt fuel args
      = inlineConeTL dm2 stopAt fuel args) with
  | case1 fuel n hs =>
    rw [inlineConeT.eq_def, inlineConeT.eq_def]
    simp only [hs, if_pos]
  | case2 n hs =>
    rw [inlineConeT.eq_def, inlineConeT.eq_def]
  | case3 fuel n hs hg hf =>
    rw [inlineConeT.eq_def, inlineConeT.eq_def]
    simp only [hs, Bool.false_eq_true, ← hag n, hg]
  | case4 n hs fuel rhs hg ih =>
    rw [inlineConeT.eq_def, inlineConeT.eq_def]
    simp only [hs, Bool.false_eq_true, ← hag n, hg]
    exact ih
  | case5 fuel o args ih => simp only [inlineConeT, ih]
  | case6 fuel args ih => simp only [inlineConeT, ih]
  | case7 fuel e hi lo ih => simp only [inlineConeT, ih]
  | case8 => simp [inlineConeT]
  | case9 => simp [inlineConeT]
  | case10 x e h1 h2 h3 h4 h5 h6 =>
    cases e with
    | ref n => exact absurd rfl (h1 n)
    | op o args => exact absurd rfl (h2 o args)
    | concat args => exact absurd rfl (h3 args)
    | slice a b c => exact absurd rfl (h4 a b c)
    | index a b => exact absurd rfl (h5 a b)
    | sliceDim a b c => exact absurd rfl (h6 a b c)
    | const v w => rw [inlineConeT.eq_def, inlineConeT.eq_def]
  | case11 => simp [inlineConeTL]
  | case12 fuel a rest ih1 ih2 => simp only [inlineConeTL, ih1, ih2]

/-! ### F2: moving the LOOKUP itself to the list (no new trusted axiom)

The step-4 attempt showed that a list-BUILT `Std.HashMap` is no help:
the kernel cannot reduce the LOOKUP, wherever the map came from.  The
way out is not to ask it to — prove `dm.get? n = dmGetR l n` ONCE from
the HashMap's own `get?_insert` / `getElem?_empty` lemmas (kernel, no
`native_decide`), then rewrite the cone equation's map argument to the
list side with `inlineConeT_dm_congr` and let the kernel run the walk
over the list lookup.

**Duplicate keys.**  `buildDefMap` folds `insert` left to right, so for
a repeated assign target the LAST one wins; `List.find?` returns the
FIRST.  Measured on `[x := 1, x := 2]`: the map gives 2, `find?` gives
1.  So the list lookup must scan from the RIGHT — `dmGetR` below — and
that is exactly what makes the fold induction go through. -/

/-- List lookup with the FOLD's duplicate-key semantics: the last
    binding for a name wins, so scan from the right. -/
def dmGetR (l : List (String × Expr)) (n : String) : Option Expr :=
  match l with
  | [] => none
  | (k, v) :: rest => match dmGetR rest n with
    | some r => some r
    | none => if k == n then some v else none

/-- **Lookup agreement, proven — not evaluated.**  Induction on the
    fold, using only `get?_insert` and `getElem?_empty`.  Generalised
    over the accumulator so the induction is available at every prefix. -/
theorem dmOfL_get?_eq (l : List (String × Expr)) :
    ∀ (m : Sparkle.IR.Optimize.DefMap) (n : String),
      (l.foldl (fun m p => m.insert p.1 p.2) m).get? n
        = match dmGetR l n with
          | some r => some r
          | none => m.get? n := by
  induction l with
  | nil => intro m n; rfl
  | cons hd tl ih =>
    intro m n
    simp only [List.foldl_cons, dmGetR]
    rw [ih (m.insert hd.1 hd.2) n]
    cases hr : dmGetR tl n with
    | some r => rfl
    | none =>
      simp only
      rw [Std.HashMap.get?_insert]
      by_cases hk : hd.1 == n
      · simp [hk]
      · simp [hk]

/-- The shipping map's lookup IS the right-scanning list lookup. -/
theorem buildDefMap_get?_eq (body : List Stmt) (n : String) :
    (Sparkle.IR.Optimize.buildDefMap body).get? n = dmGetR (dmListOf body) n := by
  rw [buildDefMap_dmOfL, dmOfL]
  rw [dmOfL_get?_eq (dmListOf body) {} n]
  cases dmGetR (dmListOf body) n with
  | some r => rfl
  | none => exact Std.HashMap.getElem?_empty

/-- A map whose lookup is defined directly by the list — what the
    kernel CAN reduce.  It is not a `Std.HashMap`; `inlineConeTList`
    below is `inlineConeT` with this in place of the map. -/
def dmListLookup (l : List (String × Expr)) : String → Option Expr := dmGetR l

/-! ### The walk, parameterised by its lookup

`inlineConeT` reads its two tables only as `dm.get? n` and
`stopAt.contains n`.  `inlineConeG` below is the SAME walk with those
two reads as function arguments, so the shipping call and the
list-backed call are one function at two instantiations — no second
copy of the algorithm to keep in step.

`inlineConeT_eq_G` states that the shipping function IS this walk at
the HashMap lookups (`rfl`-level: same recursion, same order), and
`inlineConeG_congr` transports a run between pointwise-equal lookups.
Composing them with `buildDefMap_get?_eq` moves a cone equation onto
the list side, where the kernel can run it — with no new axiom, since
every step is a proven rewrite. -/

mutual
/-- The cone walk with its two table reads as parameters. -/
def inlineConeG (get : String → Option Expr) (stop : String → Bool) :
    Nat → Expr → Except String Expr
  | fuel, .ref n =>
    if stop n then .ok (.ref n)
    else match fuel, get n with
      | 0, _ => .error s!"cone inlining fuel exhausted at `{n}` (combinational cycle?)"
      | _, none => .error s!"`{n}` is neither an input, a register, nor assigned"
      | fuel + 1, some rhs => inlineConeG get stop fuel rhs
  | fuel, .op o args => do
    .ok (.op o (← inlineConeGL get stop fuel args))
  | fuel, .concat args => do
    .ok (.concat (← inlineConeGL get stop fuel args))
  | fuel, .slice e hi lo => do
    .ok (.slice (← inlineConeG get stop fuel e) hi lo)
  | _, .index .. => .error "memories/dynamic indexing unsupported by #verify_emit (v1)"
  | _, .sliceDim .. => .error "symbolic-width slices unsupported by #verify_emit (v1)"
  | _, e => .ok e

def inlineConeGL (get : String → Option Expr) (stop : String → Bool) :
    Nat → List Expr → Except String (List Expr)
  | _, [] => .ok []
  | fuel, a :: rest => do
    .ok ((← inlineConeG get stop fuel a) :: (← inlineConeGL get stop fuel rest))
end

mutual
/-- The shipping walk is the generic walk at the HashMap reads. -/
theorem inlineConeT_eq_G (dm : Sparkle.IR.Optimize.DefMap)
    (stopAt : Std.HashMap String Bool) :
    ∀ fuel e, inlineConeT dm stopAt fuel e
      = inlineConeG (fun n => dm.get? n) (fun n => stopAt.contains n) fuel e
  | fuel, .ref n => by
    rw [inlineConeT.eq_def, inlineConeG.eq_def]
    dsimp only
    by_cases hs : stopAt.contains n
    · simp only [hs, if_pos]
    · simp only [hs, Bool.false_eq_true, if_false]
      cases fuel with
      | zero => cases hg : dm.get? n <;> simp only [hg]
      | succ f =>
        cases hg : dm.get? n with
        | none => simp only [hg]
        | some rhs => simp only [hg]; exact inlineConeT_eq_G dm stopAt f rhs
  | fuel, .op o args => by
    simp only [inlineConeT, inlineConeG, inlineConeTL_eq_GL dm stopAt fuel args]
  | fuel, .concat args => by
    simp only [inlineConeT, inlineConeG, inlineConeTL_eq_GL dm stopAt fuel args]
  | fuel, .slice e hi lo => by
    simp only [inlineConeT, inlineConeG, inlineConeT_eq_G dm stopAt fuel e]
  | _, .index .. => by rw [inlineConeT.eq_def, inlineConeG.eq_def]
  | _, .sliceDim .. => by rw [inlineConeT.eq_def, inlineConeG.eq_def]
  | _, .const .. => by rw [inlineConeT.eq_def, inlineConeG.eq_def]

theorem inlineConeTL_eq_GL (dm : Sparkle.IR.Optimize.DefMap)
    (stopAt : Std.HashMap String Bool) :
    ∀ fuel args, inlineConeTL dm stopAt fuel args
      = inlineConeGL (fun n => dm.get? n) (fun n => stopAt.contains n) fuel args
  | _, [] => by rw [inlineConeTL.eq_def, inlineConeGL.eq_def]
  | fuel, a :: rest => by
    simp only [inlineConeTL, inlineConeGL, inlineConeT_eq_G dm stopAt fuel a,
      inlineConeTL_eq_GL dm stopAt fuel rest]
end

mutual
/-- Pointwise-equal lookups give the same run. -/
theorem inlineConeG_congr (g1 g2 : String → Option Expr) (s1 s2 : String → Bool)
    (hg : ∀ n, g1 n = g2 n) (hs : ∀ n, s1 n = s2 n) :
    ∀ fuel e, inlineConeG g1 s1 fuel e = inlineConeG g2 s2 fuel e
  | fuel, .ref n => by
    rw [inlineConeG.eq_def, inlineConeG.eq_def]
    dsimp only
    rw [hs n]
    by_cases h : s2 n
    · simp only [h, if_pos]
    · simp only [h, Bool.false_eq_true, if_false]
      cases fuel with
      | zero => rw [hg n]
      | succ f =>
        rw [hg n]
        cases g2 n with
        | none => simp only
        | some rhs => simp only; exact inlineConeG_congr g1 g2 s1 s2 hg hs f rhs
  | fuel, .op o args => by
    simp only [inlineConeG, inlineConeGL_congr g1 g2 s1 s2 hg hs fuel args]
  | fuel, .concat args => by
    simp only [inlineConeG, inlineConeGL_congr g1 g2 s1 s2 hg hs fuel args]
  | fuel, .slice e hi lo => by
    simp only [inlineConeG, inlineConeG_congr g1 g2 s1 s2 hg hs fuel e]
  | _, .index .. => by rw [inlineConeG.eq_def, inlineConeG.eq_def]
  | _, .sliceDim .. => by rw [inlineConeG.eq_def, inlineConeG.eq_def]
  | _, .const .. => by rw [inlineConeG.eq_def, inlineConeG.eq_def]

theorem inlineConeGL_congr (g1 g2 : String → Option Expr) (s1 s2 : String → Bool)
    (hg : ∀ n, g1 n = g2 n) (hs : ∀ n, s1 n = s2 n) :
    ∀ fuel args, inlineConeGL g1 s1 fuel args = inlineConeGL g2 s2 fuel args
  | _, [] => by rw [inlineConeGL.eq_def, inlineConeGL.eq_def]
  | fuel, a :: rest => by
    simp only [inlineConeGL, inlineConeG_congr g1 g2 s1 s2 hg hs fuel a,
      inlineConeGL_congr g1 g2 s1 s2 hg hs fuel rest]
end

/-- Stop-set lookup agreement, proven the same way (no `native_decide`). -/
theorem stopOfL_contains_elem (l : List String) :
    ∀ n, (stopOfL l).contains n = l.elem n := by
  have gen : ∀ (l : List String) (m : Std.HashMap String Bool) (n : String),
      (l.foldl (fun h x => h.insert x true) m).contains n
        = (l.elem n || m.contains n) := by
    intro l
    induction l with
    | nil => intro m n; simp
    | cons hd tl ih =>
      intro m n
      simp only [List.foldl_cons, List.elem_cons]
      rw [ih (m.insert hd true) n, Std.HashMap.contains_insert]
      by_cases hk : hd == n
      · have : (n == hd) = true := by
          simp only [beq_iff_eq] at hk ⊢; exact hk.symm
        simp [hk, this]
      · have hne : hd ≠ n := by simpa using hk
        have : (n == hd) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun h => hne h.symm
        simp [hk, this]
  intro n
  rw [stopOfL, gen l {} n]
  simp

/-- The `.ok` test, as a Boolean that never compares error STRINGS.
    `decide` on an `Except String Expr` equation gets stuck on the
    interpolated messages' `Decidable` instance (measured: it fails on a
    two-element literal body), so the kernel is asked this instead. -/
def isOkEq (r : Except String Expr) (e : Expr) : Bool :=
  match r with
  | .ok c => decide (c = e)
  | .error _ => false

theorem eq_ok_of_isOkEq {r : Except String Expr} {e : Expr}
    (h : isOkEq r e = true) : r = .ok e := by
  cases r with
  | error msg => simp [isOkEq] at h
  | ok c =>
    simp only [isOkEq, decide_eq_true_eq] at h
    exact congrArg (fun x => (Except.ok x : Except String Expr)) h

/-- **The cone equation, moved to the list side.**  Everything here is a
    proven rewrite, so a `decide` on the right-hand side discharges the
    shipping statement with NO new trusted axiom. -/
theorem inlineConeT_of_list (body : List Stmt) (stopL : List String)
    (fuel : Nat) (e cone : Expr)
    (h : isOkEq (inlineConeG (dmGetR (dmListOf body)) (fun n => stopL.elem n) fuel e) cone = true) :
    inlineConeT (Sparkle.IR.Optimize.buildDefMap body) (stopOfL stopL) fuel e = .ok cone := by
  rw [inlineConeT_eq_G]
  rw [inlineConeG_congr _ (dmGetR (dmListOf body)) _ (fun n => stopL.elem n)
    (fun n => buildDefMap_get?_eq body n) (fun n => stopOfL_contains_elem stopL n)]
  exact eq_ok_of_isOkEq h

/-! ### A STRUCTURALLY recursive walk, so the kernel can compute

`inlineConeG` (and the shipping `inlineConeT`) recurse on the PAIR
(fuel, expression): fuel drops when a reference is expanded, the
expression shrinks everywhere else.  Lean compiles that by WELL-FOUNDED
recursion, so `#print axioms` shows `propext, Quot.sound` and the
defining equations hold only propositionally — the kernel cannot
compute with it.  MEASURED: `decide` fails even on a two-element
literal table with a reference that stops immediately, while the same
statement IS provable by rewriting with the defining equation
(`tiny_stop` in the tests).  So the obstacle is computation, not truth.

`inlineConeS` below is the same walk written so Lean accepts it
STRUCTURALLY: the outer recursion is on `fuel`, and within one fuel
step an inner structural recursion on the expression handles
`op`/`concat`/`slice`.  Fuel is consumed exactly where the original
consumes it — when a `.ref` is expanded to its definition — so runs
agree including the fuel-exhausted error.  `inlineConeS_eq_G` proves
the agreement, failure behaviour included. -/

mutual
/-- One fuel level: walk the expression STRUCTURALLY.  A reference that
    is not a stop name is handed to `rec`, which owns the fuel — so this
    function recurses only on the expression and Lean accepts it
    structurally (measured: `#print axioms` shows `propext` only, and
    the kernel computes with it). -/
def stepE (get : String → Option Expr) (stop : String → Bool)
    (rec : String → Except String Expr) : Expr → Except String Expr
  | .ref n => if stop n then .ok (.ref n) else rec n
  | .op o args => match stepEL get stop rec args with
    | .ok as => .ok (.op o as)
    | .error e => .error e
  | .concat args => match stepEL get stop rec args with
    | .ok as => .ok (.concat as)
    | .error e => .error e
  | .slice e hi lo => match stepE get stop rec e with
    | .ok e' => .ok (.slice e' hi lo)
    | .error er => .error er
  | .index .. => .error "memories/dynamic indexing unsupported by #verify_emit (v1)"
  | .sliceDim .. => .error "symbolic-width slices unsupported by #verify_emit (v1)"
  | e => .ok e

def stepEL (get : String → Option Expr) (stop : String → Bool)
    (rec : String → Except String Expr) : List Expr → Except String (List Expr)
  | [] => .ok []
  | a :: rest => match stepE get stop rec a with
    | .ok a' => match stepEL get stop rec rest with
      | .ok rest' => .ok (a' :: rest')
      | .error e => .error e
    | .error e => .error e
end

/-- The walk, structural in BOTH recursions: outer on `fuel`, inner on
    the expression.  Fuel is consumed exactly where the original
    consumes it — expanding a `.ref` to its definition — so the runs
    agree, fuel-exhausted error included. -/
def inlineConeS (get : String → Option Expr) (stop : String → Bool) :
    Nat → Expr → Except String Expr
  | 0, e => stepE get stop
      (fun n => .error s!"cone inlining fuel exhausted at `{n}` (combinational cycle?)") e
  | fuel + 1, e => stepE get stop
      (fun n => match get n with
        | none => .error s!"`{n}` is neither an input, a register, nor assigned"
        | some rhs => inlineConeS get stop fuel rhs) e

mutual
/-- `stepE` at the original's own ref-handler IS one level of the
    generic walk. -/
theorem stepE_eq_G (get : String → Option Expr) (stop : String → Bool)
    (fuel : Nat) :
    ∀ e, stepE get stop
        (fun n => match fuel, get n with
          | 0, _ => .error s!"cone inlining fuel exhausted at `{n}` (combinational cycle?)"
          | _, none => .error s!"`{n}` is neither an input, a register, nor assigned"
          | f + 1, some rhs => inlineConeG get stop f rhs) e
      = inlineConeG get stop fuel e
  | .ref n => by
    rw [stepE.eq_def, inlineConeG.eq_def]
  | .op o args => by
    rw [stepE.eq_def, inlineConeG.eq_def]
    dsimp only
    rw [stepEL_eq_GL get stop fuel args]
    cases inlineConeGL get stop fuel args <;> rfl
  | .concat args => by
    rw [stepE.eq_def, inlineConeG.eq_def]
    dsimp only
    rw [stepEL_eq_GL get stop fuel args]
    cases inlineConeGL get stop fuel args <;> rfl
  | .slice e hi lo => by
    rw [stepE.eq_def, inlineConeG.eq_def]
    dsimp only
    rw [stepE_eq_G get stop fuel e]
    cases inlineConeG get stop fuel e <;> rfl
  | .index .. => by rw [stepE.eq_def, inlineConeG.eq_def]
  | .sliceDim .. => by rw [stepE.eq_def, inlineConeG.eq_def]
  | .const .. => by rw [stepE.eq_def, inlineConeG.eq_def]

theorem stepEL_eq_GL (get : String → Option Expr) (stop : String → Bool)
    (fuel : Nat) :
    ∀ args, stepEL get stop
        (fun n => match fuel, get n with
          | 0, _ => .error s!"cone inlining fuel exhausted at `{n}` (combinational cycle?)"
          | _, none => .error s!"`{n}` is neither an input, a register, nor assigned"
          | f + 1, some rhs => inlineConeG get stop f rhs) args
      = inlineConeGL get stop fuel args
  | [] => by rw [stepEL.eq_def, inlineConeGL.eq_def]
  | a :: rest => by
    rw [stepEL.eq_def, inlineConeGL.eq_def]
    dsimp only
    rw [stepE_eq_G get stop fuel a, stepEL_eq_GL get stop fuel rest]
    cases inlineConeG get stop fuel a with
    | error e => rfl
    | ok a' => cases inlineConeGL get stop fuel rest <;> rfl
end

/-- The structural walk agrees with the generic one — same results,
    same errors, same fuel accounting. -/
theorem inlineConeS_eq_G (get : String → Option Expr) (stop : String → Bool) :
    ∀ fuel e, inlineConeS get stop fuel e = inlineConeG get stop fuel e
  | 0, e => by
    rw [inlineConeS.eq_def]
    dsimp only
    rw [← stepE_eq_G get stop 0 e]
  | fuel + 1, e => by
    rw [inlineConeS.eq_def]
    dsimp only
    rw [← stepE_eq_G get stop (fuel + 1) e]
    congr 1
    funext n
    cases get n with
    | none => rfl
    | some rhs => exact inlineConeS_eq_G get stop fuel rhs

/-- **The cone equation on the STRUCTURAL walk over list lookups.**
    Every step from here to the shipping statement is a proven rewrite,
    so `decide` on this discharges it with no new trusted axiom. -/
theorem inlineConeT_of_listS (body : List Stmt) (stopL : List String)
    (fuel : Nat) (e cone : Expr)
    (h : isOkEq (inlineConeS (dmGetR (dmListOf body)) (fun n => stopL.elem n) fuel e) cone = true) :
    inlineConeT (Sparkle.IR.Optimize.buildDefMap body) (stopOfL stopL) fuel e = .ok cone := by
  refine inlineConeT_of_list body stopL fuel e cone ?_
  rw [← inlineConeS_eq_G]
  exact h

/-! ### F2: `resolveSlicesT` — the same two blockers, the same two fixes

`resolveSlicesT` (Tools/ConeFold.lean) reads the width table only as
`wt.get? n` (in `widthOfPartT` and the `.ref` branch) and recurses on
the pair (fuel, expression) with re-entry at the SAME fuel on a rebuilt
slice — so, like `inlineConeT`, it is compiled by well-founded
recursion and the kernel can neither look up nor compute.  The recipe
that worked for the cone walk is reused verbatim: a right-scanning list
lookup with a fold-agreement theorem (`assocGetR`, generic in the value
type), and a fuel-outer structural version whose every sub-call goes
through the previous level (`stepR` / `resolveSlicesS`), tied to the
shipping function by a proven equality. -/

/-- Right-scanning association lookup with the fold's last-wins
    semantics, for any value type. -/
def assocGetR {β : Type} (l : List (String × β)) (n : String) : Option β :=
  match l with
  | [] => none
  | (k, v) :: rest => match assocGetR rest n with
    | some r => some r
    | none => if k == n then some v else none

theorem foldInsert_get?_eq {β : Type} (l : List (String × β)) :
    ∀ (m : Std.HashMap String β) (n : String),
      (l.foldl (fun m p => m.insert p.1 p.2) m).get? n
        = match assocGetR l n with
          | some r => some r
          | none => m.get? n := by
  induction l with
  | nil => intro m n; rfl
  | cons hd tl ih =>
    intro m n
    simp only [List.foldl_cons, assocGetR]
    rw [ih (m.insert hd.1 hd.2) n]
    cases hr : assocGetR tl n with
    | some r => rfl
    | none =>
      simp only
      rw [Std.HashMap.get?_insert]
      by_cases hk : hd.1 == n
      · simp [hk]
      · simp [hk]

/-- The generator's width table (`wtL.foldl insert {}`) looks up as the
    list does.  Proven from `get?_insert` / `getElem?_empty`. -/
theorem wtFold_get?_eq (l : List (String × Nat)) (n : String) :
    (l.foldl (fun m p => m.insert p.1 p.2) ({} : Std.HashMap String Nat)).get? n
      = assocGetR l n := by
  rw [foldInsert_get?_eq l {} n]
  cases assocGetR l n with
  | some r => rfl
  | none => exact Std.HashMap.getElem?_empty

/-- `widthOfPartT` with its one table read as a parameter. -/
def widthOfPartG (get : String → Option Nat) : Expr → Option Nat
  | .const _ w => some w
  | .ref n => get n
  | .slice _ h l => some (h - l + 1)
  | _ => none

theorem widthOfPartT_eq_G (wt : Std.HashMap String Nat) :
    widthOfPartT wt = widthOfPartG (fun n => wt.get? n) := by
  funext e; cases e <;> rfl

/-- One fuel level of slice resolution.  Every call the original makes
    at the next-lower fuel goes through `rec`, so this is not recursive
    at all — the kernel computes it by unfolding. -/
def stepR (get : String → Option Nat) (rec : Expr → Expr) : Expr → Expr
  | .slice e0 hi lo =>
    match e0 with
    | .concat parts0 =>
      let parts := (flattenL parts0).map rec
      match parts.mapM (widthOfPartG get) with
      | none => .slice (.concat parts) hi lo
      | some ws =>
        match findWindow hi lo parts ws (ws.foldl (· + ·) 0) with
        | some r => r
        | none => .slice (.concat parts) hi lo
    | e =>
      match rec e with
      | .concat parts => rec (.slice (.concat parts) hi lo)
      | .ref n => if lo == 0 && get n == some (hi + 1) then .ref n else .slice (.ref n) hi lo
      | .slice inner ihi ilo =>
        if ilo + hi ≤ ihi ∧ lo ≤ hi then rec (.slice inner (ilo + hi) (ilo + lo))
        else .slice (.slice inner ihi ilo) hi lo
      | e' => .slice e' hi lo
  | .op o args => .op o (args.map rec)
  | .concat args => .concat (args.map rec)
  | e => e

/-- Slice resolution, structural in fuel. -/
def resolveSlicesS (get : String → Option Nat) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e => stepR get (resolveSlicesS get fuel) e

/-- Pointwise-equal lookups give the same resolution. -/
theorem resolveSlicesS_congr (g1 g2 : String → Option Nat) (h : ∀ n, g1 n = g2 n) :
    ∀ fuel e, resolveSlicesS g1 fuel e = resolveSlicesS g2 fuel e := by
  have hg : g1 = g2 := funext h
  subst hg
  intro fuel e; rfl

/-- The list twin of the shipping list pass, given the element agreement
    at this fuel. -/
theorem resolveSlicesTL_eq_map (wt : Std.HashMap String Nat) (fuel : Nat)
    (ih : ∀ e, resolveSlicesT wt fuel e = resolveSlicesS (fun n => wt.get? n) fuel e) :
    ∀ l, resolveSlicesTL wt fuel l = l.map (resolveSlicesS (fun n => wt.get? n) fuel)
  | [] => by simp [resolveSlicesTL]
  | a :: rest => by
    simp only [resolveSlicesTL, List.map_cons, ih a, resolveSlicesTL_eq_map wt fuel ih rest]

/-- The `.slice e0 hi lo` arm for a non-concat `e0`: after the per-shape
    reduction lemma, every recursive call is at level `f`, covered by `ih`. -/
theorem rsS_nonConcat (wt : Std.HashMap String Nat) (f : Nat)
    (ih : ∀ e, resolveSlicesT wt f e = resolveSlicesS (fun n => wt.get? n) f e)
    (hi lo : Nat) (e0 : Expr) (hne : ∀ ps, e0 ≠ Expr.concat ps) :
    resolveSlicesT wt (f + 1) (.slice e0 hi lo)
      = stepR (fun n => wt.get? n) (resolveSlicesS (fun n => wt.get? n) f) (.slice e0 hi lo) := by
  rw [rsT_slice_reduce wt f e0 hi lo hne, ih e0]
  -- the outer match of `stepR` on `e0` reduces once `e0` is a constructor
  cases e0 with
  | concat ps => exact absurd rfl (hne ps)
  | const v w => simp only [stepR]; exact rsS_tail wt f ih hi lo _
  | ref m => simp only [stepR]; exact rsS_tail wt f ih hi lo _
  | op o args => simp only [stepR]; exact rsS_tail wt f ih hi lo _
  | slice a b c => simp only [stepR]; exact rsS_tail wt f ih hi lo _
  | sliceDim a b c => simp only [stepR]; exact rsS_tail wt f ih hi lo _
  | index a b => simp only [stepR]; exact rsS_tail wt f ih hi lo _
where
  /-- the inner match on the resolved operand, both sides -/
  rsS_tail (wt : Std.HashMap String Nat) (f : Nat)
      (ih : ∀ e, resolveSlicesT wt f e = resolveSlicesS (fun n => wt.get? n) f e)
      (hi lo : Nat) (r : Expr) :
      (match r with
        | .concat parts => resolveSlicesT wt f (.slice (.concat parts) hi lo)
        | .ref n => if lo == 0 && wt.get? n == some (hi + 1) then .ref n else .slice (.ref n) hi lo
        | .slice inner ihi ilo =>
          if ilo + hi ≤ ihi ∧ lo ≤ hi then resolveSlicesT wt f (.slice inner (ilo + hi) (ilo + lo))
          else .slice (.slice inner ihi ilo) hi lo
        | e' => .slice e' hi lo)
      = (match r with
        | .concat parts => resolveSlicesS (fun n => wt.get? n) f (.slice (.concat parts) hi lo)
        | .ref n => if lo == 0 && (fun n => wt.get? n) n == some (hi + 1) then .ref n else .slice (.ref n) hi lo
        | .slice inner ihi ilo =>
          if ilo + hi ≤ ihi ∧ lo ≤ hi then resolveSlicesS (fun n => wt.get? n) f (.slice inner (ilo + hi) (ilo + lo))
          else .slice (.slice inner ihi ilo) hi lo
        | e' => .slice e' hi lo) := by
    cases r with
    | concat parts => exact ih _
    | ref n => rfl
    | slice inner ihi ilo =>
      dsimp only
      by_cases hc : ilo + hi ≤ ihi ∧ lo ≤ hi
      · rw [if_pos hc, if_pos hc]; exact ih _
      · rw [if_neg hc, if_neg hc]
    | const v w => rfl
    | op o args => rfl
    | sliceDim a b c => rfl
    | index a b => rfl

/-- **The shipping resolver IS the structural one at the HashMap read.**
    Induction on fuel: every call the original makes from level
    `fuel + 1` is at level `fuel` (including the re-entries on rebuilt
    slices), so the induction hypothesis covers all of them; the
    per-shape reduction lemmas `rsT_*` (Tools/ConeFoldSlices.lean)
    expose the arms. -/
theorem resolveSlicesT_eq_S (wt : Std.HashMap String Nat) :
    ∀ fuel e, resolveSlicesT wt fuel e = resolveSlicesS (fun n => wt.get? n) fuel e := by
  intro fuel
  induction fuel with
  | zero => intro e; rw [rsT_zero]; rfl
  | succ f ih =>
    intro e
    have hL := resolveSlicesTL_eq_map wt f ih
    simp only [resolveSlicesS]
    cases e with
    | slice e0 hi lo =>
      cases e0 with
      | concat parts0 =>
        rw [rsT_slice_concat]
        simp only [stepR, hL, widthOfPartT_eq_G]
        -- both sides now print identically; they differ only in the two
        -- functions' compiled `match` auxiliaries, which `rfl` unfolds
        rfl
      | const v w => exact rsS_nonConcat wt f ih hi lo (.const v w) (fun _ h => by cases h)
      | ref n => exact rsS_nonConcat wt f ih hi lo (.ref n) (fun _ h => by cases h)
      | op o args => exact rsS_nonConcat wt f ih hi lo (.op o args) (fun _ h => by cases h)
      | slice a b c => exact rsS_nonConcat wt f ih hi lo (.slice a b c) (fun _ h => by cases h)
      | sliceDim a b c => exact rsS_nonConcat wt f ih hi lo (.sliceDim a b c) (fun _ h => by cases h)
      | index a b => exact rsS_nonConcat wt f ih hi lo (.index a b) (fun _ h => by cases h)
    | op o args => rw [rsT_op]; simp only [stepR, hL]
    | concat args => rw [rsT_concat]; simp only [stepR, hL]
    | const v w => rw [resolveSlicesT.eq_def]; simp [stepR]
    | ref n => rw [resolveSlicesT.eq_def]; simp [stepR]
    | sliceDim a b c => rw [resolveSlicesT.eq_def]; simp [stepR]
    | index a b => rw [resolveSlicesT.eq_def]; simp [stepR]

/-- **Composed:** the generator's width table (a fold of its literal
    list) resolves exactly as the structural resolver over the list
    lookup — every step a proven rewrite, so `decide` on the right-hand
    side discharges facts about the shipping cone. -/
theorem resolveSlicesT_list (wtL : List (String × Nat)) (fuel : Nat) (e : Expr) :
    resolveSlicesT (wtL.foldl (fun m p => m.insert p.1 p.2) {}) fuel e
      = resolveSlicesS (assocGetR wtL) fuel e := by
  rw [resolveSlicesT_eq_S]
  exact resolveSlicesS_congr _ _ (fun n => wtFold_get?_eq wtL n) fuel e

/-- **`bodyWidthOk` implies `hwfCheckL` at EVERY stop set.**  The
    body-wide width discipline (`widthOf we r = we l` for every assign) is
    strictly stronger than what `hwfCheck` asks (that, OR the target is a
    stop name).  MEASURED 2026-09-20 on crc16: the generator proved
    `hwfCheckL we stop body` by kernel `decide` once per stop set — 17
    walks over the 94-statement original body, 87 s and +0.75 GB of the
    run's peak.  `bodyWidthOk we body` is already a kernel fact per body
    (for `evalAssigns_bounded`), so this lemma replaces the 17 walks with
    17 instances of one theorem. -/
theorem hwfCheckL_of_bodyWidthOk (we : WEnv) (stop : List String) :
    ∀ (body : List Stmt), bodyWidthOk we body = true → hwfCheckL we stop body = true
  | [], _ => rfl
  | .assign l r :: rest, h => by
    simp only [bodyWidthOk, Bool.and_eq_true] at h
    simp only [hwfCheckL, Bool.and_eq_true, Bool.or_eq_true]
    exact ⟨Or.inr h.1.2, hwfCheckL_of_bodyWidthOk we stop rest h.2⟩
  | .register .. :: rest, h => by
    simp only [bodyWidthOk] at h
    simpa only [hwfCheckL] using hwfCheckL_of_bodyWidthOk we stop rest h
  | .memory .. :: rest, h => by
    simp only [bodyWidthOk] at h
    simpa only [hwfCheckL] using hwfCheckL_of_bodyWidthOk we stop rest h
  | .inst .. :: rest, h => by
    simp only [bodyWidthOk] at h
    simpa only [hwfCheckL] using hwfCheckL_of_bodyWidthOk we stop rest h

/-! ### F2: `stripMask` with a kernel-computable guard

`stripMask` (Tools/ConeFoldOpt.lean) removes an identity mask
`and [e, const (2^w-1) w]` when `widthOf e = w` AND `sfragCheck wof e`
— the fragment check that lets `sfrag_eval_bounded` prove `e < 2^w`.
MEASURED 2026-09-20: `sfragCheck` is compiled by well-founded recursion
(axioms `Classical.choice, Quot.sound`) and the kernel cannot evaluate
it even on `.ref "_gen_i"`; `maskOf` stalls through it, while
`stripMask` on a mask-free cone computes.  So the mask equations of a
body whose cones carry the optimizer's masks (shareX4's Opt body) were
stuck on `native_decide` for that reason alone.

`stripMaskK` is the same pass with the guard `widthOk (weW wof) e`
(structural, kernel-computable); the bound `e < 2^w` then comes from
the fragment-free `evalExpr_bounded` (Tools/ConeFoldMem.lean) on a
bounded environment — exactly the hypotheses `rtBridge_eval` already
carries.  Nothing else changes; the mask a cone loses is decided by a
width fact instead of a fragment membership. -/

def maskOfK (wof : String → Option Nat) : Expr → Expr
  | .op .and [e, .const c w] =>
    if c == Int.ofNat (2 ^ w - 1) && widthOf (weW wof) e == w
        && widthOk (weW wof) e then e
    else .op .and [e, .const c w]
  | e => e

mutual
def stripMaskK (wof : String → Option Nat) : Expr → Expr
  | .op o args => maskOfK wof (.op o (stripMaskKL wof args))
  | .concat args => .concat (stripMaskKL wof args)
  | .slice e hi lo => .slice (stripMaskK wof e) hi lo
  | e => e
def stripMaskKL (wof : String → Option Nat) : List Expr → List Expr
  | [] => []
  | a :: rest => stripMaskK wof a :: stripMaskKL wof rest
end

theorem maskOfK_width (wof : String → Option Nat) (x : Expr) :
    widthOf (weW wof) (maskOfK wof x) = widthOf (weW wof) x := by
  cases x with
  | op o args =>
    cases o <;> simp only [maskOfK]
    case and =>
      match args with
      | [e, .const c w] =>
        simp only
        split
        · rename_i h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          simp [widthOf, h.1.2]
        · rfl
      | [] => simp
      | [_] => simp
      | [_, .ref _] => simp
      | [_, .op _ _] => simp
      | [_, .concat _] => simp
      | [_, .slice _ _ _] => simp
      | [_, .sliceDim _ _ _] => simp
      | [_, .index _ _] => simp
      | _ :: _ :: _ :: _ => simp
  | _ => simp [maskOfK]

/-- The identity mask evaluates to its operand on bounded environments —
    the bound from `evalExpr_bounded` under the `widthOk` guard. -/
theorem maskOfK_eval (wof : String → Option Nat) (env : Env)
    (hb : Bounded (weW wof) env) (x : Expr) :
    evalExpr (weW wof) env (maskOfK wof x) = evalExpr (weW wof) env x := by
  cases x with
  | op o args =>
    cases o <;> simp only [maskOfK]
    case and =>
      match args with
      | [e, .const c w] =>
        simp only
        split
        · rename_i h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨hc, hw⟩, hok⟩ := h
          subst hc
          cases he : evalExpr (weW wof) env e with
          | none => simp [evalExpr, evalList, he]
          | some v =>
            have hlt : v < 2 ^ w := by
              rw [← hw]
              exact evalExpr_bounded (weW wof) env hb e v hok he
            have hconst : evalExpr (weW wof) env (.const (Int.ofNat (2 ^ w - 1)) w)
                = some (2 ^ w - 1) :=
              eval_const_ofNat _ _ _ _ (by have := Nat.two_pow_pos w; omega)
            have hW : widthOf (weW wof)
                (.op .and [e, .const (Int.ofNat (2 ^ w - 1)) w]) = w := by
              simp [widthOf, hw]
            rw [show evalExpr (weW wof) env
                  (.op .and [e, .const (Int.ofNat (2 ^ w - 1)) w])
                = ((evalList (weW wof) env [e, .const (Int.ofNat (2 ^ w - 1)) w]).bind
                    fun vals => evalOp (weW wof) .and
                      [e, .const (Int.ofNat (2 ^ w - 1)) w] vals
                      (widthOf (weW wof)
                        (.op .and [e, .const (Int.ofNat (2 ^ w - 1)) w])))
                from rfl]
            rw [show evalList (weW wof) env [e, .const (Int.ofNat (2 ^ w - 1)) w]
                = (evalExpr (weW wof) env e).bind fun v0 =>
                    (evalExpr (weW wof) env (.const (Int.ofNat (2 ^ w - 1)) w)).bind
                      fun vc => some [v0, vc]
                from rfl]
            rw [he, hconst, hW]
            simp only [Option.bind_some, evalOp, mask, and_pow_two_sub_one,
              Nat.mod_eq_of_lt hlt]
        · rfl
      | [] => simp
      | [_] => simp
      | [_, .ref _] => simp
      | [_, .op _ _] => simp
      | [_, .concat _] => simp
      | [_, .slice _ _ _] => simp
      | [_, .sliceDim _ _ _] => simp
      | [_, .index _ _] => simp
      | _ :: _ :: _ :: _ => simp
  | _ => simp [maskOfK]

mutual
theorem stripMaskK_width (wof : String → Option Nat) :
    ∀ e, widthOf (weW wof) (stripMaskK wof e) = widthOf (weW wof) e
  | .op o args => by
    simp only [stripMaskK]
    rw [maskOfK_width]
    exact widthOf_op_shape _ o (stripMaskKL_widthMatch wof args)
  | .concat args => by
    simp only [stripMaskK, widthOf]
    exact widthOfGo_congr _ (stripMaskKL_widthMatch wof args)
  | .slice e hi lo => by simp [stripMaskK, widthOf]
  | .const .. => by simp [stripMaskK]
  | .ref .. => by simp [stripMaskK]
  | .sliceDim .. => by simp [stripMaskK]
  | .index .. => by simp [stripMaskK]

theorem stripMaskKL_widthMatch (wof : String → Option Nat) :
    ∀ args, WidthMatch (weW wof) args (stripMaskKL wof args)
  | [] => by simp only [stripMaskKL]; exact .nil
  | a :: rest => by
    simp only [stripMaskKL]
    exact .cons (stripMaskK_width wof a) (stripMaskKL_widthMatch wof rest)
end

mutual
theorem stripMaskK_eval (wof : String → Option Nat) (env : Env)
    (hb : Bounded (weW wof) env) :
    ∀ e, evalExpr (weW wof) env (stripMaskK wof e) = evalExpr (weW wof) env e
  | .op o args => by
    simp only [stripMaskK]
    rw [maskOfK_eval wof env hb]
    have hwm := stripMaskKL_widthMatch wof args
    simp only [evalExpr, stripMaskKL_eval wof env hb args,
      widthOf_op_shape _ o hwm]
    cases evalList (weW wof) env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [evalOp_congr _ hwm o vals _]
  | .concat args => by
    simp only [stripMaskK, evalExpr, stripMaskKL_eval wof env hb args]
    cases evalList (weW wof) env args with
    | none => rfl
    | some vals =>
      simp only [Option.bind_eq_bind, Option.bind_some,
        evalGo_congr _ (stripMaskKL_widthMatch wof args) vals]
  | .slice e hi lo => by
    simp only [stripMaskK, evalExpr, stripMaskK_eval wof env hb e]
  | .const .. => by simp [stripMaskK]
  | .ref .. => by simp [stripMaskK]
  | .sliceDim .. => by simp [stripMaskK]
  | .index .. => by simp [stripMaskK]

theorem stripMaskKL_eval (wof : String → Option Nat) (env : Env)
    (hb : Bounded (weW wof) env) :
    ∀ args, evalList (weW wof) env (stripMaskKL wof args)
      = evalList (weW wof) env args
  | [] => by simp [stripMaskKL]
  | a :: rest => by
    simp only [stripMaskKL, evalList, stripMaskK_eval wof env hb a,
      stripMaskKL_eval wof env hb rest]
end

/-- `rtBridge_eval` with the kernel-computable mask pass. -/
theorem rtBridgeK_eval (wof : String → Option Nat) (env : Env)
    (hb : ∀ n, env n < 2 ^ weW wof n) (cX cO : Expr)
    (heq : rtNorm (weW wof) (stripMaskK wof cX) = rtNorm (weW wof) cO)
    (hokX : widthOk (weW wof) (rtNorm (weW wof) (stripMaskK wof cX)) = true)
    (hokO : widthOk (weW wof) (rtNorm (weW wof) cO) = true) :
    evalExpr (weW wof) env cO = evalExpr (weW wof) env cX := by
  rw [← rtNorm_eval _ env hb cO hokO, ← heq, rtNorm_eval _ env hb _ hokX,
    stripMaskK_eval wof env hb]

-- the crc16 shapes, pinned
#guard rtNorm (fun _ => 1)
  (.slice (.concat [.const (.ofNat 0) 1, .op .xor [.ref "c", .const (.ofNat 1) 1]]) 0 0)
  == .op .not [.ref "c"]
#guard rtNorm (fun _ => 8) (.op .xor [.ref "c", .const (.ofNat 1) 1])
  == .op .xor [.ref "c", .const (.ofNat 1) 1]
#guard rtNorm (fun _ => 1) (.op .xor [.ref "c", .const (.ofNat 1) 1]) == .op .not [.ref "c"]

end Tools.ConeFold
