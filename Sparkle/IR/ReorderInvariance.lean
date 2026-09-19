/-
  Reorder invariance for the step semantics.

  The shipping module lowering topologically re-sorts a module body
  (`topoSortBody`), so the roundtrip image of a body is a PERMUTATION
  of the statement-wise image.  `evalAssigns` folds in order; this file
  proves the fold is invariant under any permutation as long as both
  orders are well-ordered (every read of a locally-assigned name comes
  after its write) and writes are unique — the semantic content of
  "topological order".

  A pleasant structural fact carries the proof: `evalExpr` fails
  (`none`) only on SHAPE (sliceDim/index/unsupported arity), never on
  the environment, so evaluation failure is order-independent for free.
-/
import Sparkle.IR.Semantics

namespace Sparkle.IR.Reorder

open Sparkle.IR.AST
open Sparkle.IR.Semantics

/-- The reference names an expression reads. -/
def refsOf : Expr → List String
  | .const _ _ => []
  | .ref n => [n]
  | .op _ args => refsList args
  | .concat args => refsList args
  | .slice e _ _ => refsOf e
  | .sliceDim e _ _ => refsOf e
  | .index a i => refsOf a ++ refsOf i
where
  refsList : List Expr → List String
    | [] => []
    | a :: rest => refsOf a ++ refsList rest

mutual
/-- Environments agreeing on an expression's refs evaluate it equally
    (widths and the concat combiner are env-free). -/
theorem evalExpr_congr (we : WEnv) (env env' : Env) (e : Expr)
    (h : ∀ n ∈ refsOf e, env n = env' n) :
    evalExpr we env e = evalExpr we env' e := by
  match e with
  | .const v w => rfl
  | .ref n =>
    simp [evalExpr, h n (by simp [refsOf])]
  | .op op args =>
    simp [evalExpr,
      evalList_congr we env env' args (by simpa [refsOf] using h)]
  | .concat args =>
    simp [evalExpr,
      evalList_congr we env env' args (by simpa [refsOf] using h)]
  | .slice e hi lo =>
    simp [evalExpr,
      evalExpr_congr we env env' e (by simpa [refsOf] using h)]
  | .sliceDim _ _ _ => rfl
  | .index _ _ => rfl

theorem evalList_congr (we : WEnv) (env env' : Env) (args : List Expr)
    (h : ∀ n ∈ refsOf.refsList args, env n = env' n) :
    evalList we env args = evalList we env' args := by
  match args with
  | [] => rfl
  | a :: rest =>
    simp [evalList,
      evalExpr_congr we env env' a
        (fun n hn => h n (by simp [refsOf.refsList]; exact Or.inl hn)),
      evalList_congr we env env' rest
        (fun n hn => h n (by simp [refsOf.refsList]; exact Or.inr hn))]
end

/- ------------------------------------------------------------------ -/
/- Statement footprints and well-ordering. -/

/-- Names a statement WRITES during the combinational fold. -/
def stmtWrites : Stmt → List String
  | .assign l _ => [l]
  | .memory _ _ _ _ _ _ _ _ rd cr _ er =>
    if cr then rd :: er.map (·.2) else []
  | _ => []

/-- Names a statement READS during the combinational fold. -/
def stmtReads : Stmt → List String
  | .assign _ r => refsOf r
  | .memory _ _ _ _ _ _ _ ra _ cr _ er =>
    if cr then refsOf ra ++ er.flatMap (fun p => refsOf p.1) else []
  | _ => []

def writesOf (body : List Stmt) : List String := body.flatMap stmtWrites

/-- The reorder fragment: with the open-module semantics (instances
    are no-ops) EVERY statement is in it.  Kept as a def so the
    fragment can narrow again if a closed hierarchical semantics
    lands. -/
def SimpleStmt : Stmt → Prop
  | _ => True

/-- Well-ordered w.r.t. already-evaluated names `done`: every read of a
    locally-written name comes after its (unique) write.  This is the
    semantic content of "topologically sorted". -/
inductive WO : List String → List Stmt → Prop
  | nil {done} : WO done []
  | cons {done s rest}
      (hok : SimpleStmt s)
      (hreads : ∀ n ∈ stmtReads s, n ∉ writesOf rest)
      (hw : ∀ n ∈ stmtWrites s, n ∉ done ∧ n ∉ writesOf rest)
      (hrest : WO (done ++ stmtWrites s) rest) :
      WO done (s :: rest)

theorem writesOf_append (xs ys : List Stmt) :
    writesOf (xs ++ ys) = writesOf xs ++ writesOf ys := by
  simp [writesOf]

/-- Membership in `writesOf` is permutation-invariant. -/
theorem writesOf_perm_mem {xs ys : List Stmt} (hp : xs.Perm ys) (n : String) :
    n ∈ writesOf xs ↔ n ∈ writesOf ys := by
  simp only [writesOf, List.mem_flatMap]
  constructor
  · rintro ⟨st, hst, hn⟩; exact ⟨st, hp.mem_iff.mp hst, hn⟩
  · rintro ⟨st, hst, hn⟩; exact ⟨st, hp.mem_iff.mpr hst, hn⟩

/-- `done` matters only up to membership. -/
theorem WO_done_congr {d1 d2 : List String} {body : List Stmt}
    (hd : ∀ n, n ∈ d1 ↔ n ∈ d2) (h : WO d1 body) : WO d2 body := by
  induction h generalizing d2 with
  | nil => exact WO.nil
  | cons hok hreads hw hrest ih =>
    refine WO.cons hok hreads (fun n hn => ⟨fun hin => (hw n hn).1 ((hd n).mpr hin), (hw n hn).2⟩) ?_
    exact ih (fun n => by simp [hd n])

/- ------------------------------------------------------------------ -/
/- comboReads: the combinational effect of a combo-read memory.  It
   changes exactly its own read-data names (frame), and given
   environments agreeing on its addresses' refs it computes the same
   values (agree) — the two facts the swap lemma needs. -/

theorem comboReads_frame (we : WEnv) (mems : MEnv) (name : String)
    (aw dw : Nat) :
    ∀ (ports : List (Expr × String)) (env r : Env),
    comboReads we mems name aw dw ports env = some r →
    ∀ n, n ∉ ports.map Prod.snd → r n = env n := by
  intro ports
  induction ports with
  | nil =>
    intro env r h n _
    cases h
    rfl
  | cons p rest ih =>
    intro env r h n hn
    obtain ⟨a, rd⟩ := p
    simp only [comboReads, Option.bind_eq_bind] at h
    cases ha : evalExpr we env a with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some av =>
      rw [ha] at h
      simp only [Option.bind_some] at h
      simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [ih _ _ h n hn.2]
      simp [hn.1]

theorem comboReads_agree (we : WEnv) (mems : MEnv) (name : String)
    (aw dw : Nat) :
    ∀ (ports : List (Expr × String)) (env₁ env₂ : Env),
    (∀ n ∈ (ports.flatMap fun p => refsOf p.1), env₁ n = env₂ n) →
    match comboReads we mems name aw dw ports env₁,
          comboReads we mems name aw dw ports env₂ with
    | some r₁, some r₂ => ∀ n ∈ ports.map Prod.snd, r₁ n = r₂ n
    | none, none => True
    | _, _ => False := by
  intro ports
  induction ports with
  | nil => intro env₁ env₂ _; simp [comboReads]
  | cons p rest ih =>
    intro env₁ env₂ hag
    obtain ⟨a, rd⟩ := p
    have hae : evalExpr we env₁ a = evalExpr we env₂ a := by
      apply evalExpr_congr
      intro n hn
      exact hag n
        (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inl hn)
    simp only [comboReads, Option.bind_eq_bind]
    cases ha : evalExpr we env₁ a with
    | none => rw [← hae, ha]; trivial
    | some av =>
      rw [← hae, ha]
      simp only [Option.bind_some]
      have hag' : ∀ n ∈ (rest.flatMap fun p => refsOf p.1),
          (fun m => if m = rd then mask dw (mems name (mask aw av))
            else env₁ m) n
          = (fun m => if m = rd then mask dw (mems name (mask aw av))
            else env₂ m) n := by
        intro n hn
        by_cases hrd : n = rd
        · simp [hrd]
        · simp only [hrd, if_false]
          exact hag n
            (by simp only [List.flatMap_cons, List.mem_append]
                exact Or.inr hn)
      have := ih _ _ hag'
      cases h1 : comboReads we mems name aw dw rest
          (fun m => if m = rd then mask dw (mems name (mask aw av))
            else env₁ m) with
      | none =>
        rw [h1] at this
        cases h2 : comboReads we mems name aw dw rest
            (fun m => if m = rd then mask dw (mems name (mask aw av))
              else env₂ m) with
        | none => trivial
        | some _ => rw [h2] at this; exact absurd this (by simp)
      | some r₁ =>
        rw [h1] at this
        cases h2 : comboReads we mems name aw dw rest
            (fun m => if m = rd then mask dw (mems name (mask aw av))
              else env₂ m) with
        | none => rw [h2] at this; exact absurd this (by simp)
        | some r₂ =>
          rw [h2] at this
          intro n hn
          simp only [List.map_cons, List.mem_cons] at hn
          by_cases hmem : n ∈ rest.map Prod.snd
          · exact this n hmem
          · have hn_rd : n = rd := by
              cases hn with
              | inl h => exact h
              | inr h => exact absurd h hmem
            subst hn_rd
            rw [comboReads_frame we mems name aw dw rest _ r₁ h1 n hmem,
              comboReads_frame we mems name aw dw rest _ r₂ h2 n hmem]
            simp

/- ------------------------------------------------------------------ -/
/- Adjacent-swap machinery. -/

/-- In the v1 fragment, a non-writing statement is a combinational
    no-op. -/
theorem nop_step (we : WEnv) (mems : MEnv) {s : Stmt}
    (hs : SimpleStmt s) (hw : stmtWrites s = []) (rest : List Stmt)
    (env : Env) :
    evalAssigns we mems (s :: rest) env = evalAssigns we mems rest env := by
  match s with
  | .assign l r => simp [stmtWrites] at hw
  | .register _ _ _ _ _ => rfl
  | .memory n aw dw c wa wd wen ra rd cr ew er =>
    have hcr : cr = false := by
      cases cr
      · rfl
      · simp [stmtWrites] at hw
    subst hcr
    rfl
  | .inst _ _ _ => rfl

/-- Rewriting under one leading statement: if two tails agree at every
    environment, so do the bodies with the same head. -/
theorem evalAssigns_cons_congr (we : WEnv) (mems : MEnv) {X Y : List Stmt}
    (h : ∀ env, evalAssigns we mems X env = evalAssigns we mems Y env)
    (p : Stmt) (hp : SimpleStmt p) (env : Env) :
    evalAssigns we mems (p :: X) env = evalAssigns we mems (p :: Y) env := by
  match p with
  | .assign l r =>
    simp only [evalAssigns, Option.bind_eq_bind]
    cases evalExpr we env r with
    | none => rfl
    | some v => simp [h]
  | .register _ _ _ _ _ => exact h env
  | .memory n aw dw c wa wd wen ra rd cr ew er =>
    cases cr with
    | false => exact h env
    | true =>
      simp only [evalAssigns, if_true, Option.bind_eq_bind]
      cases comboReads we mems n aw dw ((ra, rd) :: er) env with
      | none => rfl
      | some env' => simp [h]
  | .inst _ _ _ => exact h env

/-- A no-op in SECOND position can be dropped. -/
theorem nop_second (we : WEnv) (mems : MEnv) {a b : Stmt}
    (hb : SimpleStmt b)
    (ha : SimpleStmt a) (haw : stmtWrites a = [])
    (rest : List Stmt) (env : Env) :
    evalAssigns we mems (b :: a :: rest) env
      = evalAssigns we mems (b :: rest) env :=
  evalAssigns_cons_congr we mems
    (fun env' => nop_step we mems ha haw rest env') b hb env

/-- An assign and a combo-read memory with disjoint footprints
    commute. -/
theorem swap_assign_mem (we : WEnv) (mems : MEnv)
    (la : String) (ra : Expr)
    (nB : String) (awB dwB : Nat) (cB : String)
    (waB wdB wenB raB : Expr) (rdB : String)
    (ewB : List (Expr × Expr × Expr)) (erB : List (Expr × String))
    (hla_refs : la ∉ (((raB, rdB) :: erB).flatMap fun p => refsOf p.1))
    (hla_rds : la ∉ ((raB, rdB) :: erB).map Prod.snd)
    (hrds_ra : ∀ n ∈ ((raB, rdB) :: erB).map Prod.snd, n ∉ refsOf ra)
    (rest : List Stmt) (env0 : Env) :
    evalAssigns we mems (.assign la ra
        :: .memory nB awB dwB cB waB wdB wenB raB rdB true ewB erB :: rest)
        env0
      = evalAssigns we mems
          (.memory nB awB dwB cB waB wdB wenB raB rdB true ewB erB
            :: .assign la ra :: rest) env0 := by
  simp only [evalAssigns, if_true, Option.bind_eq_bind]
  cases hva : evalExpr we env0 ra with
  | none =>
    cases hc0 : comboReads we mems nB awB dwB ((raB, rdB) :: erB) env0 with
    | none => rfl
    | some e2 =>
      have hf1 : evalExpr we e2 ra = evalExpr we env0 ra := by
        apply evalExpr_congr
        intro n hn
        refine comboReads_frame we mems nB awB dwB _ env0 e2 hc0 n ?_
        intro hin
        exact hrds_ra n hin hn
      simp [hf1, hva]
  | some va =>
    simp only [Option.bind_some]
    have hag : ∀ n ∈ (((raB, rdB) :: erB).flatMap fun p => refsOf p.1),
        (fun m => if m = la then va else env0 m) n = env0 n := by
      intro n hn
      have : n ≠ la := fun hEq => hla_refs (hEq ▸ hn)
      simp [this]
    have hrel := comboReads_agree we mems nB awB dwB ((raB, rdB) :: erB)
      (fun m => if m = la then va else env0 m) env0 hag
    cases h1 : comboReads we mems nB awB dwB ((raB, rdB) :: erB)
        (fun m => if m = la then va else env0 m) with
    | none =>
      rw [h1] at hrel
      cases h2 : comboReads we mems nB awB dwB ((raB, rdB) :: erB) env0 with
      | none => rfl
      | some _ => rw [h2] at hrel; exact absurd hrel (by simp)
    | some r1 =>
      rw [h1] at hrel
      cases h2 : comboReads we mems nB awB dwB ((raB, rdB) :: erB) env0 with
      | none => rw [h2] at hrel; exact absurd hrel (by simp)
      | some r2 =>
        rw [h2] at hrel
        have hf1 : evalExpr we r2 ra = evalExpr we env0 ra := by
          apply evalExpr_congr
          intro n hn
          refine comboReads_frame we mems nB awB dwB _ env0 r2 h2 n ?_
          intro hin
          exact hrds_ra n hin hn
        simp only [Option.bind_some]
        rw [hf1, hva]
        simp only [Option.bind_some]
        have henv : r1 = fun n => if n = la then va else r2 n := by
          funext n
          by_cases hrd : n ∈ ((raB, rdB) :: erB).map Prod.snd
          · have h3 := hrel n hrd
            have : n ≠ la := fun hEq => hla_rds (hEq ▸ hrd)
            simp [this, h3]
          · rw [comboReads_frame we mems nB awB dwB _ _ r1 h1 n hrd]
            by_cases hla : n = la
            · simp [hla]
            · rw [comboReads_frame we mems nB awB dwB _ _ r2 h2 n hrd]
              try simp [hla]
        rw [henv]

/-- Two combo-read memories with disjoint footprints commute. -/
theorem swap_mem_mem (we : WEnv) (mems : MEnv)
    (nA : String) (awA dwA : Nat) (cA : String)
    (waA wdA wenA raA : Expr) (rdA : String)
    (ewA : List (Expr × Expr × Expr)) (erA : List (Expr × String))
    (nB : String) (awB dwB : Nat) (cB : String)
    (waB wdB wenB raB : Expr) (rdB : String)
    (ewB : List (Expr × Expr × Expr)) (erB : List (Expr × String))
    (hA_refsB : ∀ n ∈ ((raA, rdA) :: erA).map Prod.snd,
      n ∉ (((raB, rdB) :: erB).flatMap fun p => refsOf p.1))
    (hA_rdsB : ∀ n ∈ ((raA, rdA) :: erA).map Prod.snd,
      n ∉ ((raB, rdB) :: erB).map Prod.snd)
    (hB_refsA : ∀ n ∈ ((raB, rdB) :: erB).map Prod.snd,
      n ∉ (((raA, rdA) :: erA).flatMap fun p => refsOf p.1))
    (rest : List Stmt) (env0 : Env) :
    evalAssigns we mems
        (.memory nA awA dwA cA waA wdA wenA raA rdA true ewA erA
          :: .memory nB awB dwB cB waB wdB wenB raB rdB true ewB erB :: rest)
        env0
      = evalAssigns we mems
          (.memory nB awB dwB cB waB wdB wenB raB rdB true ewB erB
            :: .memory nA awA dwA cA waA wdA wenA raA rdA true ewA erA :: rest)
          env0 := by
  simp only [evalAssigns, if_true, Option.bind_eq_bind]
  cases hA0 : comboReads we mems nA awA dwA ((raA, rdA) :: erA) env0 with
  | none =>
    cases hB0 : comboReads we mems nB awB dwB ((raB, rdB) :: erB) env0 with
    | none => rfl
    | some eB =>
      -- A on eB must fail too (agree: eB matches env0 on A's refs)
      have hagA : ∀ n ∈ (((raA, rdA) :: erA).flatMap fun p => refsOf p.1),
          env0 n = eB n := by
        intro n hn
        refine (comboReads_frame we mems nB awB dwB _ env0 eB hB0 n ?_).symm
        intro hin
        exact hB_refsA n hin hn
      have hrelA := comboReads_agree we mems nA awA dwA ((raA, rdA) :: erA)
        env0 eB hagA
      rw [hA0] at hrelA
      cases hAe : comboReads we mems nA awA dwA ((raA, rdA) :: erA) eB with
      | none => simp only [Option.bind_some]; rw [hAe]; rfl
      | some _ => rw [hAe] at hrelA; exact absurd hrelA (by simp)
  | some eA =>
    simp only [Option.bind_some]
    have hagB : ∀ n ∈ (((raB, rdB) :: erB).flatMap fun p => refsOf p.1),
        eA n = env0 n := by
      intro n hn
      refine comboReads_frame we mems nA awA dwA _ env0 eA hA0 n ?_
      intro hin
      exact hA_refsB n hin hn
    have hrelB := comboReads_agree we mems nB awB dwB ((raB, rdB) :: erB)
      eA env0 hagB
    cases hBA : comboReads we mems nB awB dwB ((raB, rdB) :: erB) eA with
    | none =>
      rw [hBA] at hrelB
      cases hB0 : comboReads we mems nB awB dwB ((raB, rdB) :: erB) env0 with
      | none => rfl
      | some _ => rw [hB0] at hrelB; exact absurd hrelB (by simp)
    | some e2 =>
      rw [hBA] at hrelB
      cases hB0 : comboReads we mems nB awB dwB ((raB, rdB) :: erB) env0 with
      | none => rw [hB0] at hrelB; exact absurd hrelB (by simp)
      | some eB =>
        rw [hB0] at hrelB
        simp only [Option.bind_some]
        have hagA : ∀ n ∈ (((raA, rdA) :: erA).flatMap fun p => refsOf p.1),
            env0 n = eB n := by
          intro n hn
          refine (comboReads_frame we mems nB awB dwB _ env0 eB hB0 n ?_).symm
          intro hin
          exact hB_refsA n hin hn
        have hrelA := comboReads_agree we mems nA awA dwA ((raA, rdA) :: erA)
          env0 eB hagA
        rw [hA0] at hrelA
        cases hAB : comboReads we mems nA awA dwA ((raA, rdA) :: erA) eB with
        | none => rw [hAB] at hrelA; exact absurd hrelA (by simp)
        | some e2' =>
          rw [hAB] at hrelA
          simp only [Option.bind_some]
          have henv : e2 = e2' := by
            funext n
            by_cases hInA : n ∈ ((raA, rdA) :: erA).map Prod.snd
            · -- A's slice: LHS via B-frame back to eA; RHS via A-agree
              have h1 : e2 n = eA n :=
                comboReads_frame we mems nB awB dwB _ eA e2 hBA n
                  (fun hin => hA_rdsB n hInA hin)
              have h2 : e2' n = eA n := (hrelA n hInA).symm
              rw [h1, h2]
            · by_cases hInB : n ∈ ((raB, rdB) :: erB).map Prod.snd
              · have h1 : e2 n = eB n := hrelB n hInB
                have h2 : e2' n = eB n :=
                  comboReads_frame we mems nA awA dwA _ eB e2' hAB n hInA
                rw [h1, h2]
              · have h1 : e2 n = eA n :=
                  comboReads_frame we mems nB awB dwB _ eA e2 hBA n hInB
                have h2 : eA n = env0 n :=
                  comboReads_frame we mems nA awA dwA _ env0 eA hA0 n hInA
                have h3 : e2' n = eB n :=
                  comboReads_frame we mems nA awA dwA _ eB e2' hAB n hInA
                have h4 : eB n = env0 n :=
                  comboReads_frame we mems nB awB dwB _ env0 eB hB0 n hInB
                rw [h1, h2, h3, h4]
          rw [henv]

/-- Adjacent independent statements commute. -/
theorem evalAssigns_swap (we : WEnv) (mems : MEnv) {a b : Stmt}
    (ha : SimpleStmt a) (hb : SimpleStmt b)
    (hwa_rb : ∀ n ∈ stmtWrites a, n ∉ stmtReads b)
    (hwa_wb : ∀ n ∈ stmtWrites a, n ∉ stmtWrites b)
    (hwb_ra : ∀ n ∈ stmtWrites b, n ∉ stmtReads a)
    (rest : List Stmt) (env0 : Env) :
    evalAssigns we mems (a :: b :: rest) env0
      = evalAssigns we mems (b :: a :: rest) env0 := by
  by_cases hea : stmtWrites a = []
  · rw [nop_step we mems ha hea (b :: rest) env0,
      nop_second we mems hb ha hea rest env0]
  · by_cases heb : stmtWrites b = []
    · rw [nop_step we mems hb heb (a :: rest) env0,
        nop_second we mems ha hb heb rest env0]
    · -- both statements write: each is an assign or a combo-read memory
      cases a with
      | register _ _ _ _ _ => exact absurd rfl hea
      | inst _ _ _ => exact absurd rfl hea
      | memory nA awA dwA cA waA wdA wenA raA rdA crA ewA erA =>
        have hcrA : crA = true := by
          cases crA
          · simp [stmtWrites] at hea
          · rfl
        subst hcrA
        cases b with
        | register _ _ _ _ _ => exact absurd rfl heb
        | inst _ _ _ => exact absurd rfl heb
        | assign lb rb =>
          exact (swap_assign_mem we mems lb rb nA awA dwA cA waA wdA wenA
            raA rdA ewA erA
            (fun hin => hwb_ra lb (by simp [stmtWrites])
              (by simpa [stmtReads] using hin))
            (fun hin => hwa_wb lb (by simpa [stmtWrites] using hin)
              (by simp [stmtWrites]))
            (fun n hn hin => hwa_rb n (by simpa [stmtWrites] using hn)
              (by simpa [stmtReads] using hin))
            rest env0).symm
        | memory nB awB dwB cB waB wdB wenB raB rdB crB ewB erB =>
          have hcrB : crB = true := by
            cases crB
            · simp [stmtWrites] at heb
            · rfl
          subst hcrB
          exact swap_mem_mem we mems nA awA dwA cA waA wdA wenA raA rdA
            ewA erA nB awB dwB cB waB wdB wenB raB rdB ewB erB
            (fun n hn hin => hwa_rb n (by simpa [stmtWrites] using hn)
              (by simpa [stmtReads] using hin))
            (fun n hn hin => hwa_wb n (by simpa [stmtWrites] using hn)
              (by simpa [stmtWrites] using hin))
            (fun n hn hin => hwb_ra n (by simpa [stmtWrites] using hn)
              (by simpa [stmtReads] using hin))
            rest env0
      | assign la ra =>
        cases b with
        | register _ _ _ _ _ => exact absurd rfl heb
        | inst _ _ _ => exact absurd rfl heb
        | memory nB awB dwB cB waB wdB wenB raB rdB crB ewB erB =>
          have hcrB : crB = true := by
            cases crB
            · simp [stmtWrites] at heb
            · rfl
          subst hcrB
          exact swap_assign_mem we mems la ra nB awB dwB cB waB wdB wenB
            raB rdB ewB erB
            (fun hin => hwa_rb la (by simp [stmtWrites])
              (by simpa [stmtReads] using hin))
            (fun hin => hwa_wb la (by simp [stmtWrites])
              (by simpa [stmtWrites] using hin))
            (fun n hn hin => hwb_ra n (by simpa [stmtWrites] using hn)
              (by simpa [stmtReads] using hin))
            rest env0
        | assign lb rb =>
          have hlab : la ≠ lb := by
            intro hEq
            exact hwa_wb la (by simp [stmtWrites]) (by simp [stmtWrites, hEq])
          have hla_rb : la ∉ refsOf rb := by
            have := hwa_rb la (by simp [stmtWrites])
            simpa [stmtReads] using this
          have hlb_ra : lb ∉ refsOf ra := by
            have := hwb_ra lb (by simp [stmtWrites])
            simpa [stmtReads] using this
          simp only [evalAssigns, Option.bind_eq_bind]
          cases hva : evalExpr we env0 ra with
          | none =>
            cases hvb : evalExpr we env0 rb with
            | none => rfl
            | some vb =>
              have : evalExpr we (fun n => if n = lb then vb else env0 n) ra
                  = evalExpr we env0 ra := by
                apply evalExpr_congr
                intro n hn
                have : n ≠ lb := fun hEq => hlb_ra (hEq ▸ hn)
                simp [this]
              simp [hvb, this, hva]
          | some va =>
            have hrb' : evalExpr we (fun n => if n = la then va else env0 n) rb
                = evalExpr we env0 rb := by
              apply evalExpr_congr
              intro n hn
              have : n ≠ la := fun hEq => hla_rb (hEq ▸ hn)
              simp [this]
            cases hvb : evalExpr we env0 rb with
            | none => simp [hva, hvb, hrb']
            | some vb =>
              have hra' : evalExpr we (fun n => if n = lb then vb else env0 n) ra
                  = evalExpr we env0 ra := by
                apply evalExpr_congr
                intro n hn
                have : n ≠ lb := fun hEq => hlb_ra (hEq ▸ hn)
                simp [this]
              have henv :
                  (fun n => if n = lb then vb
                    else (fun m => if m = la then va else env0 m) n)
                  = (fun n => if n = la then va
                    else (fun m => if m = lb then vb else env0 m) n) := by
                funext n
                by_cases h1 : n = lb
                · subst h1
                  simp [Ne.symm hlab, hlab]
                · by_cases h2 : n = la <;> simp [h1, h2, hlab]
              simp [hva, hvb, hrb', hra', henv]

/-- Bubble an independent statement to the front. -/
theorem evalAssigns_bubble (we : WEnv) (mems : MEnv) {s : Stmt}
    (hs : SimpleStmt s) :
    ∀ (pre : List Stmt), (∀ p ∈ pre, SimpleStmt p) →
    (∀ p ∈ pre,
      (∀ n ∈ stmtWrites s, n ∉ stmtReads p ∧ n ∉ stmtWrites p)
      ∧ (∀ n ∈ stmtWrites p, n ∉ stmtReads s)) →
    ∀ (post : List Stmt) (env0 : Env),
    evalAssigns we mems (pre ++ s :: post) env0
      = evalAssigns we mems (s :: (pre ++ post)) env0 := by
  intro pre
  induction pre with
  | nil => intro _ _ post env0; rfl
  | cons p pre' ih =>
    intro hok hind post env0
    have hp := hok p (List.mem_cons_self ..)
    have hpind := hind p (List.mem_cons_self ..)
    calc evalAssigns we mems ((p :: pre') ++ s :: post) env0
        = evalAssigns we mems (p :: (s :: (pre' ++ post))) env0 := by
          exact evalAssigns_cons_congr we mems
            (fun env => ih (fun q hq => hok q (List.mem_cons_of_mem _ hq))
              (fun q hq => hind q (List.mem_cons_of_mem _ hq)) post env)
            p hp env0
      _ = evalAssigns we mems (s :: p :: (pre' ++ post)) env0 := by
          exact evalAssigns_swap we mems hp hs
            (fun n hn => (hpind.2 n hn))
            (fun n hn => fun hin => (hpind.1 n hin).2 hn)
            (fun n hn => (hpind.1 n hn).1)
            (pre' ++ post) env0

/- ------------------------------------------------------------------ -/
/- WO projections. -/

theorem WO_all_ok {done body} (h : WO done body) :
    ∀ p ∈ body, SimpleStmt p := by
  induction h with
  | nil => intro p hp; cases hp
  | cons hok _ _ _ ih =>
    intro p hp
    cases hp with
    | head => exact hok
    | tail _ hmem => exact ih p hmem

/-- Everything in `pre` reads and writes nothing that anything AFTER it
    (in particular `s`) writes. -/
theorem WO_middle_indep :
    ∀ {pre : List Stmt} {done : List String} {s : Stmt} {post : List Stmt},
    WO done (pre ++ s :: post) →
    ∀ p ∈ pre,
      (∀ n ∈ stmtReads p, n ∉ stmtWrites s)
      ∧ (∀ n ∈ stmtWrites p, n ∉ stmtWrites s) := by
  intro pre
  induction pre with
  | nil => intro done s post _ p hp; cases hp
  | cons q pre' ih =>
    intro done s post h p hp
    cases h with
    | cons hok hreads hw hrest =>
      cases hp with
      | head =>
        constructor
        · intro n hn
          have := hreads n hn
          simp [writesOf_append, writesOf] at this
          intro hin
          exact this.2.1 hin
        · intro n hn
          have := (hw n hn).2
          simp [writesOf_append, writesOf] at this
          intro hin
          exact this.2.1 hin
      | tail _ hmem => exact ih hrest p hmem

/-- Removing a middle statement (independent of everything before it)
    preserves well-ordering, with its writes marked done. -/
theorem WO_remove_middle :
    ∀ {pre : List Stmt} {done : List String} {s : Stmt} {post : List Stmt},
    WO done (pre ++ s :: post) →
    WO (done ++ stmtWrites s) (pre ++ post) := by
  intro pre
  induction pre with
  | nil =>
    intro done s post h
    cases h with
    | cons hok hreads hw hrest => exact hrest
  | cons q pre' ih =>
    intro done s post h
    cases h with
    | cons hok hreads hw hrest =>
      refine WO.cons hok ?_ ?_ ?_
      · intro n hn
        have := hreads n hn
        simp [writesOf_append, writesOf] at this ⊢
        exact ⟨this.1, this.2.2⟩
      · intro n hn
        have h1 := (hw n hn).1
        have h2 := (hw n hn).2
        simp [writesOf_append, writesOf] at h2 ⊢
        exact ⟨⟨h1, h2.2.1⟩, h2.1, h2.2.2⟩
      · have := ih hrest
        refine WO_done_congr (fun n => ?_) this
        simp only [List.mem_append]
        constructor
        · rintro ((h | h) | h) <;> simp [h]
        · rintro ((h | h) | h) <;> simp [h]

/- ------------------------------------------------------------------ -/
/- The reorder-invariance theorem. -/

/-- **Reorder invariance**: two well-ordered arrangements of the same
    statements fold to the same environment.  This is the semantic
    license for the shipping `topoSortBody`: any topological order of
    the roundtrip image evaluates like the original order. -/
theorem evalAssigns_perm (we : WEnv) (mems : MEnv) :
    ∀ {body body' : List Stmt} {done : List String},
    body.Perm body' → WO done body → WO done body' →
    ∀ env0, evalAssigns we mems body env0 = evalAssigns we mems body' env0
  | [], body', _, hp, _, _, env0 => by
    have : body' = [] := hp.symm.eq_nil
    subst this
    rfl
  | s :: rest, body', done, hp, h1, h2, env0 => by
    have hs_mem : s ∈ body' := hp.mem_iff.mp (List.mem_cons_self ..)
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hs_mem
    have hrest_perm : rest.Perm (pre ++ post) :=
      (hp.trans List.perm_middle).cons_inv
    cases h1 with
    | cons hok hreads hw hrest =>
      have h2' : WO (done ++ stmtWrites s) (pre ++ post) :=
        WO_remove_middle h2
      have hindep := WO_middle_indep h2
      have hokAll := WO_all_ok h2
      rw [evalAssigns_bubble we mems hok pre
        (fun p hp' => hokAll p (by simp [hp']))
        (fun p hp' =>
          ⟨fun n hn =>
            ⟨fun hin => (hindep p hp').1 n hin hn,
             fun hin => (hindep p hp').2 n hin hn⟩,
           fun n hn hin =>
            hreads n hin
              ((writesOf_perm_mem hrest_perm n).mpr
                (by simp only [writesOf, List.mem_flatMap]
                    exact ⟨p, by simp [hp'], hn⟩))⟩)
        post env0]
      exact evalAssigns_cons_congr we mems
        (fun env => evalAssigns_perm we mems hrest_perm hrest h2' env)
        s hok env0

/- ------------------------------------------------------------------ -/
/- Register phase under permutation: contributions concatenate, so the
   result is the SAME MULTISET (a `Perm`); `applyNexts` then agrees
   whenever update names are unique. -/

/-- One statement's contribution to the register-update list. -/
def stmtNexts (we : WEnv) (mems : MEnv) (envF : Env) :
    Stmt → Option (List (String × Nat))
  | .register out _ (rstName, _) input init =>
    (evalExpr we envF input).map fun vin =>
      [(out, if envF rstName ≠ 0 then encodeInit init (we out)
             else mask (we out) vin)]
  | .memory name aw dw _ _ _ _ ra rd cr _ er =>
    if cr then some []
    else syncReadLatches we mems name aw dw ((ra, rd) :: er) envF
  | _ => some []

/-- `regNexts` is the in-order concatenation of contributions. -/
theorem regNexts_cons (we : WEnv) (mems : MEnv) (envF : Env)
    (s : Stmt) (t : List Stmt) :
    regNexts we mems (s :: t) envF
      = (stmtNexts we mems envF s).bind
          (fun c => (regNexts we mems t envF).map (c ++ ·)) := by
  match s with
  | .register out _ (rstName, _) input init =>
    simp only [regNexts, stmtNexts, Option.bind_eq_bind]
    cases evalExpr we envF input with
    | none => rfl
    | some vin =>
      cases regNexts we mems t envF with
      | none => rfl
      | some nexts => rfl
  | .memory name aw dw c wa wd wen ra rd cr ew er =>
    simp only [regNexts, stmtNexts]
    cases cr with
    | true =>
      simp only [if_true]
      cases regNexts we mems t envF with
      | none => rfl
      | some nexts => rfl
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.bind_eq_bind]
      cases syncReadLatches we mems name aw dw ((ra, rd) :: er) envF with
      | none => rfl
      | some latches =>
        cases regNexts we mems t envF with
        | none => rfl
        | some nexts => rfl
  | .assign l r =>
    simp only [regNexts, stmtNexts]
    cases regNexts we mems t envF with
    | none => rfl
    | some nexts => rfl
  | .inst _ _ _ =>
    simp only [regNexts, stmtNexts]
    cases regNexts we mems t envF with
    | none => rfl
    | some nexts => rfl

/-- Permutation relation on optional lists. -/
def OPerm : Option (List α) → Option (List α) → Prop
  | some l, some l' => l.Perm l'
  | none, none => True
  | _, _ => False

theorem OPerm.refl : ∀ (o : Option (List α)), OPerm o o
  | some l => List.Perm.refl l
  | none => trivial

theorem OPerm.trans : ∀ {a b c : Option (List α)},
    OPerm a b → OPerm b c → OPerm a c
  | some _, some _, some _, h1, h2 => List.Perm.trans h1 h2
  | none, none, none, _, _ => trivial

/-- The register-update lists of two permuted bodies are permutations
    of each other (or both fail). -/
theorem regNexts_perm (we : WEnv) (mems : MEnv) (envF : Env)
    {body body' : List Stmt} (hp : body.Perm body') :
    OPerm (regNexts we mems body envF) (regNexts we mems body' envF) := by
  induction hp with
  | nil => exact OPerm.refl _
  | cons x hp ih =>
    rename_i l₁ l₂
    rw [regNexts_cons, regNexts_cons]
    cases hc : stmtNexts we mems envF x with
    | none => trivial
    | some c =>
      cases h1 : regNexts we mems l₁ envF with
      | none =>
        cases h2 : regNexts we mems l₂ envF with
        | none => trivial
        | some n2 => rw [h1, h2] at ih; exact absurd ih (by simp [OPerm])
      | some n1 =>
        cases h2 : regNexts we mems l₂ envF with
        | none => rw [h1, h2] at ih; exact absurd ih (by simp [OPerm])
        | some n2 =>
          rw [h1, h2] at ih
          simpa [OPerm] using (List.Perm.refl c).append ih
  | swap x y l =>
    rw [regNexts_cons, regNexts_cons, regNexts_cons, regNexts_cons]
    cases hx : stmtNexts we mems envF x with
    | none =>
      cases hy : stmtNexts we mems envF y with
      | none => trivial
      | some cy =>
        cases regNexts we mems l envF with
        | none => trivial
        | some n => trivial
    | some cx =>
      cases hy : stmtNexts we mems envF y with
      | none =>
        cases regNexts we mems l envF with
        | none => trivial
        | some n => trivial
      | some cy =>
        cases regNexts we mems l envF with
        | none => trivial
        | some n =>
          -- cy ++ (cx ++ n) permutes to cx ++ (cy ++ n)
          have h3 : (cy ++ (cx ++ n)).Perm (cx ++ (cy ++ n)) := by
            rw [← List.append_assoc, ← List.append_assoc]
            exact (List.perm_append_comm).append_right n
          simpa [OPerm] using h3
  | trans hp1 hp2 ih1 ih2 => exact OPerm.trans ih1 ih2

/-- Two members of a key-nodup pair list with the same key coincide. -/
theorem key_unique {l : List (String × Nat)}
    (hnd : (l.map Prod.fst).Nodup) {q q' : String × Nat}
    (hq : q ∈ l) (hq' : q' ∈ l) (hk : q.1 = q'.1) : q = q' := by
  induction l with
  | nil => cases hq
  | cons p rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    cases hq with
    | head =>
      cases hq' with
      | head => rfl
      | tail _ hmem =>
        exfalso
        have h1 : ∀ x, (q.1, x) ∉ rest := by simpa using hnd.1
        exact h1 q'.2 (by rw [hk]; exact hmem)
    | tail _ hmem =>
      cases hq' with
      | head =>
        exfalso
        have h1 : ∀ x, (q'.1, x) ∉ rest := by simpa using hnd.1
        exact h1 q.2 (by rw [← hk]; exact hmem)
      | tail _ hmem' => exact ih hnd.2 hmem hmem'

/-- `applyNexts` only cares about the update MULTISET when keys are
    unique. -/
theorem applyNexts_perm {l l' : List (String × Nat)} (hp : l.Perm l')
    (hnd : (l.map Prod.fst).Nodup) (st : String → Nat) :
    applyNexts st l = applyNexts st l' := by
  funext n
  unfold applyNexts
  cases hf : l.find? (fun p => p.1 == n) with
  | none =>
    cases hf' : l'.find? (fun p => p.1 == n) with
    | none => rfl
    | some q =>
      have hqm : q ∈ l := hp.mem_iff.mpr (List.mem_of_find?_eq_some hf')
      have := List.find?_eq_none.mp hf q hqm
      exact absurd (List.find?_some hf') this
  | some q =>
    have hqm : q ∈ l := List.mem_of_find?_eq_some hf
    cases hf' : l'.find? (fun p => p.1 == n) with
    | none =>
      have := List.find?_eq_none.mp hf' q (hp.mem_iff.mp hqm)
      exact absurd (List.find?_some hf) this
    | some q' =>
      have hq'm : q' ∈ l := hp.mem_iff.mpr (List.mem_of_find?_eq_some hf')
      have hk : q.1 = q'.1 := by
        have h1 := List.find?_some hf
        have h2 := List.find?_some hf'
        simp only [beq_iff_eq] at h1 h2
        rw [h1, h2]
      rw [key_unique hnd hqm hq'm hk]

/- ------------------------------------------------------------------ -/
/- Memory phase under permutation: write folds on DISTINCT array names
   commute.  Success/failure of a write fold never depends on the
   memory state (only on `envF`), and each fold touches exactly its own
   array slice. -/

/-- Payload evaluation depends on the memory state only through its
    OWN array's slice. -/
theorem evalPayload_mems_congr {we : WEnv} {m₁ m₂ : MEnv} {env : Env}
    {arr : String} {aw dw : Nat}
    (hm : ∀ i, m₁ arr i = m₂ arr i) (e : Expr) :
    evalPayload we m₁ env arr aw dw e = evalPayload we m₂ env arr aw dw e := by
  unfold evalPayload
  -- parametric in the width environment: `evalPayload` now splices
  -- under its own placeholder extension, not the caller's `we`
  have hs : ∀ (w' : WEnv) (reads : List (String × Expr)) (acc : Env),
      spliceReads w' m₁ env arr aw dw reads acc
        = spliceReads w' m₂ env arr aw dw reads acc := by
    intro w' reads
    induction reads with
    | nil => intro acc; rfl
    | cons p rest ih =>
      intro acc
      obtain ⟨ph, idx⟩ := p
      simp only [spliceReads, Option.bind_eq_bind]
      cases evalExpr w' env idx with
      | none => rfl
      | some vi =>
        simp only [Option.bind_some, hm (mask aw vi)]
        exact ih _
  cases hE : extractReads arr e 0 with
  | mk e' rest =>
    cases rest with
    | mk reads k => simp [hs]

/-- One statement's memory-state effect: `mems0` for read resolution is
    the state the statement receives (Verilog nonblocking: payloads see
    the pre-write state — and earlier statements only touch OTHER
    arrays, so this equals the pre-cycle state of the OWN array). -/
def stmtMemUpd (we : WEnv) (envF : Env) : Stmt → MEnv → Option MEnv
  | .memory name aw dw _ wa wd wen _ _ _ ew _ =>
    fun m => memWritePorts we m envF name aw dw ((wa, wd, wen) :: ew) m
  | _ => fun m => some m

theorem memNexts_cons (we : WEnv) (envF : Env) (s : Stmt) (t : List Stmt)
    (mems : MEnv) :
    memNexts we (s :: t) mems envF
      = (stmtMemUpd we envF s mems).bind (fun m' => memNexts we t m' envF) := by
  match s with
  | .memory name aw dw c wa wd wen ra rd cr ew er =>
    simp only [memNexts, stmtMemUpd, Option.bind_eq_bind]
  | .assign _ _ => rfl
  | .register _ _ _ _ _ => rfl
  | .inst _ _ _ => rfl

/-- Success of a write fold does not depend on the THREADED state, and
    tracks the read-resolution state only through the own slice. -/
theorem memWritePorts_isSome (we : WEnv) (env : Env) (name : String)
    (aw dw : Nat) :
    ∀ (ports : List (Expr × Expr × Expr)) (ms₁ ms₂ m₁ m₂ : MEnv),
    (∀ i, ms₁ name i = ms₂ name i) →
    (memWritePorts we ms₁ env name aw dw ports m₁).isSome
      = (memWritePorts we ms₂ env name aw dw ports m₂).isSome := by
  intro ports
  induction ports with
  | nil => intro _ _ m₁ m₂ _; rfl
  | cons p rest ih =>
    intro ms₁ ms₂ m₁ m₂ hms
    obtain ⟨a, d, en⟩ := p
    simp only [memWritePorts, Option.bind_eq_bind,
      evalPayload_mems_congr hms en, evalPayload_mems_congr hms a,
      evalPayload_mems_congr hms d]
    cases evalPayload we ms₂ env name aw dw en with
    | none => rfl
    | some ev =>
    cases evalPayload we ms₂ env name aw dw a with
    | none => rfl
    | some av =>
    cases evalPayload we ms₂ env name aw dw d with
    | none => rfl
    | some dv =>
    simp only [Option.bind_some]
    exact ih _ _ _ _ hms

/-- A write fold leaves every OTHER array untouched. -/
theorem memWritePorts_frame (we : WEnv) (env : Env) (name : String)
    (aw dw : Nat) :
    ∀ (ports : List (Expr × Expr × Expr)) (ms m r : MEnv),
    memWritePorts we ms env name aw dw ports m = some r →
    ∀ nm, nm ≠ name → ∀ i, r nm i = m nm i := by
  intro ports
  induction ports with
  | nil =>
    intro ms m r h nm hnm i
    cases h
    rfl
  | cons p rest ih =>
    intro ms m r h nm hnm i
    obtain ⟨a, d, en⟩ := p
    simp only [memWritePorts, Option.bind_eq_bind] at h
    cases hen : evalPayload we ms env name aw dw en with
    | none => rw [hen] at h; exact absurd h (by simp)
    | some ev =>
    rw [hen] at h
    cases ha : evalPayload we ms env name aw dw a with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some av =>
    rw [ha] at h
    cases hd : evalPayload we ms env name aw dw d with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some dv =>
    rw [hd] at h
    simp only [Option.bind_some] at h
    have := ih _ _ _ h nm hnm i
    rw [this]
    by_cases hev : ev ≠ 0
    · simp [hev, hnm]
    · simp [hev]

/-- A write fold's OWN slice is determined by the incoming own slices
    (both the read-resolution state's and the threaded state's). -/
theorem memWritePorts_slice (we : WEnv) (env : Env) (name : String)
    (aw dw : Nat) :
    ∀ (ports : List (Expr × Expr × Expr)) (ms₁ ms₂ m₁ m₂ r₁ r₂ : MEnv),
    (∀ i, ms₁ name i = ms₂ name i) →
    (∀ i, m₁ name i = m₂ name i) →
    memWritePorts we ms₁ env name aw dw ports m₁ = some r₁ →
    memWritePorts we ms₂ env name aw dw ports m₂ = some r₂ →
    ∀ i, r₁ name i = r₂ name i := by
  intro ports
  induction ports with
  | nil =>
    intro ms₁ ms₂ m₁ m₂ r₁ r₂ _ hm h1 h2 i
    cases h1; cases h2
    exact hm i
  | cons p rest ih =>
    intro ms₁ ms₂ m₁ m₂ r₁ r₂ hms hm h1 h2 i
    obtain ⟨a, d, en⟩ := p
    simp only [memWritePorts, Option.bind_eq_bind] at h1 h2
    rw [evalPayload_mems_congr hms en, evalPayload_mems_congr hms a,
      evalPayload_mems_congr hms d] at h1
    cases hen : evalPayload we ms₂ env name aw dw en with
    | none => rw [hen] at h1; exact absurd h1 (by simp)
    | some ev =>
    rw [hen] at h1 h2
    cases ha : evalPayload we ms₂ env name aw dw a with
    | none => rw [ha] at h1; exact absurd h1 (by simp)
    | some av =>
    rw [ha] at h1 h2
    cases hd : evalPayload we ms₂ env name aw dw d with
    | none => rw [hd] at h1; exact absurd h1 (by simp)
    | some dv =>
    rw [hd] at h1 h2
    simp only [Option.bind_some] at h1 h2
    refine ih _ _ _ _ _ _ hms (fun j => ?_) h1 h2 i
    by_cases hev : ev ≠ 0
    · by_cases hj : j = mask aw av <;> simp [hev, hj, hm j]
    · simp [hev, hm j]

def stmtMemName : Stmt → Option String
  | .memory name _ _ _ _ _ _ _ _ _ _ _ => some name
  | _ => none

/-- Memory effects of two statements with distinct array names commute:
    each fold touches only its own slice, resolves reads only against
    its own slice, and its success is independent of everything else. -/
theorem stmtMemUpd_comm (we : WEnv) (envF : Env) {x y : Stmt}
    (hx : SimpleStmt x) (hy : SimpleStmt y)
    (hname : ∀ nx, stmtMemName x = some nx →
      ∀ ny, stmtMemName y = some ny → nx ≠ ny)
    (m : MEnv) :
    (stmtMemUpd we envF x m).bind (stmtMemUpd we envF y)
      = (stmtMemUpd we envF y m).bind (stmtMemUpd we envF x) := by
  have hid : ∀ {s : Stmt}, stmtMemName s = none →
      ∀ m', stmtMemUpd we envF s m' = some m' := by
    intro s hn m'
    match s with
    | .assign _ _ => rfl
    | .register _ _ _ _ _ => rfl
    | .memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [stmtMemName] at hn
    | .inst _ _ _ => rfl
  cases hxn : stmtMemName x with
  | none =>
    rw [hid hxn m, Option.bind_some]
    cases hyu : stmtMemUpd we envF y m with
    | none => rfl
    | some m' => rw [Option.bind_some, hid hxn m']
  | some nx =>
    cases hyn : stmtMemName y with
    | none =>
      rw [hid hyn m, Option.bind_some]
      cases hxu : stmtMemUpd we envF x m with
      | none => rfl
      | some m' => rw [Option.bind_some, hid hyn m']
    | some ny =>
      have hne : nx ≠ ny := hname nx hxn ny hyn
      cases x with
      | assign _ _ => simp [stmtMemName] at hxn
      | register _ _ _ _ _ => simp [stmtMemName] at hxn
      | inst _ _ _ => simp [stmtMemName] at hxn
      | memory nX awX dwX cX waX wdX wenX raX rdX crX ewX erX =>
      cases y with
      | assign _ _ => simp [stmtMemName] at hyn
      | register _ _ _ _ _ => simp [stmtMemName] at hyn
      | inst _ _ _ => simp [stmtMemName] at hyn
      | memory nY awY dwY cY waY wdY wenY raY rdY crY ewY erY =>
      have hnX : nX = nx := by simpa [stmtMemName] using hxn
      have hnY : nY = ny := by simpa [stmtMemName] using hyn
      subst hnX hnY
      simp only [stmtMemUpd]
      cases hxu : memWritePorts we m envF nX awX dwX
          ((waX, wdX, wenX) :: ewX) m with
      | none =>
        cases hyu : memWritePorts we m envF nY awY dwY
            ((waY, wdY, wenY) :: ewY) m with
        | none => rfl
        | some mY =>
          rw [Option.bind_some]
          have hframeY : ∀ i, mY nX i = m nX i := fun i =>
            memWritePorts_frame we envF nY awY dwY _ m m mY hyu nX hne i
          have := memWritePorts_isSome we envF nX awX dwX
            ((waX, wdX, wenX) :: ewX) m mY m mY (fun i => (hframeY i).symm)
          rw [hxu] at this
          cases hxu2 : memWritePorts we mY envF nX awX dwX
              ((waX, wdX, wenX) :: ewX) mY with
          | none => rfl
          | some _ => rw [hxu2] at this; simp at this
      | some mX =>
        rw [Option.bind_some]
        cases hyu : memWritePorts we m envF nY awY dwY
            ((waY, wdY, wenY) :: ewY) m with
        | none =>
          have hframeX : ∀ i, mX nY i = m nY i := fun i =>
            memWritePorts_frame we envF nX awX dwX _ m m mX hxu nY
              (Ne.symm hne) i
          have := memWritePorts_isSome we envF nY awY dwY
            ((waY, wdY, wenY) :: ewY) m mX m mX (fun i => (hframeX i).symm)
          rw [hyu] at this
          cases hyu2 : memWritePorts we mX envF nY awY dwY
              ((waY, wdY, wenY) :: ewY) mX with
          | none => rfl
          | some _ => rw [hyu2] at this; simp at this
        | some mY =>
          rw [Option.bind_some]
          have hframeX : ∀ i, mX nY i = m nY i := fun i =>
            memWritePorts_frame we envF nX awX dwX _ m m mX hxu nY
              (Ne.symm hne) i
          have hframeY : ∀ i, mY nX i = m nX i := fun i =>
            memWritePorts_frame we envF nY awY dwY _ m m mY hyu nX hne i
          cases hyx : memWritePorts we mX envF nY awY dwY
              ((waY, wdY, wenY) :: ewY) mX with
          | none =>
            have := memWritePorts_isSome we envF nY awY dwY
              ((waY, wdY, wenY) :: ewY) m mX m mX (fun i => (hframeX i).symm)
            rw [hyu, hyx] at this; simp at this
          | some rYX =>
          cases hxy : memWritePorts we mY envF nX awX dwX
              ((waX, wdX, wenX) :: ewX) mY with
          | none =>
            have := memWritePorts_isSome we envF nX awX dwX
              ((waX, wdX, wenX) :: ewX) m mY m mY (fun i => (hframeY i).symm)
            rw [hxu, hxy] at this; simp at this
          | some rXY =>
          congr 1
          funext nm i
          by_cases hnmx : nm = nX
          · subst hnmx
            have h1 : rYX nm i = mX nm i :=
              memWritePorts_frame we envF nY awY dwY _ mX mX rYX hyx nm hne i
            have h3 : ∀ j, rXY nm j = mX nm j :=
              memWritePorts_slice we envF nm awX dwX _ mY m mY m rXY mX
                (fun j => hframeY j) (fun j => hframeY j) hxy hxu
            rw [h1, h3 i]
          · by_cases hnmy : nm = nY
            · subst hnmy
              have h2 : ∀ j, rYX nm j = mY nm j :=
                memWritePorts_slice we envF nm awY dwY _ mX m mX m rYX mY
                  (fun j => hframeX j) (fun j => hframeX j) hyx hyu
              have h3 : rXY nm i = mY nm i :=
                memWritePorts_frame we envF nX awX dwX _ mY mY rXY hxy nm
                  (Ne.symm hne) i
              rw [h2 i, h3]
            · have h1 : rYX nm i = mX nm i :=
                memWritePorts_frame we envF nY awY dwY _ mX mX rYX hyx nm hnmy i
              have h2 : mX nm i = m nm i :=
                memWritePorts_frame we envF nX awX dwX _ m m mX hxu nm hnmx i
              have h3 : rXY nm i = mY nm i :=
                memWritePorts_frame we envF nX awX dwX _ mY mY rXY hxy nm hnmx i
              have h4 : mY nm i = m nm i :=
                memWritePorts_frame we envF nY awY dwY _ m m mY hyu nm hnmy i
              rw [h1, h2, h3, h4]

/-- The memory phase only cares about the statement MULTISET when
    array names are distinct. -/
theorem memNexts_perm (we : WEnv) (envF : Env) {body body' : List Stmt}
    (hp : body.Perm body') :
    (∀ p ∈ body, SimpleStmt p) →
    (body.filterMap stmtMemName).Nodup →
    ∀ mems, memNexts we body mems envF = memNexts we body' mems envF := by
  induction hp with
  | nil => intro _ _ mems; rfl
  | cons x hp ih =>
    rename_i l₁ l₂
    intro hok hnd mems
    rw [memNexts_cons, memNexts_cons]
    cases stmtMemUpd we envF x mems with
    | none => rfl
    | some m' =>
      rw [Option.bind_some, Option.bind_some]
      exact ih (fun p hp' => hok p (List.mem_cons_of_mem _ hp'))
        (by
          cases hx : stmtMemName x with
          | none => simpa [List.filterMap_cons, hx] using hnd
          | some nx =>
            have := hnd
            simp only [List.filterMap_cons, hx, List.nodup_cons] at this
            exact this.2) m'
  | swap x y l =>
    intro hok hnd mems
    simp only [memNexts_cons]
    rw [← Option.bind_assoc, ← Option.bind_assoc,
      stmtMemUpd_comm we envF
        (hok y (by simp)) (hok x (by simp))
        (fun ny hy nx hx => by
          cases hxx : stmtMemName x with
          | none => rw [hxx] at hx; cases hx
          | some nx' =>
            rw [hxx] at hx
            cases hyy : stmtMemName y with
            | none => rw [hyy] at hy; cases hy
            | some ny' =>
              rw [hyy] at hy
              cases hx; cases hy
              have := hnd
              simp only [List.filterMap_cons, hyy, hxx,
                List.nodup_cons, List.mem_cons] at this
              intro hEq
              exact this.1 (Or.inl hEq))
        mems]
  | trans h1 h2 ih1 ih2 =>
    intro hok hnd mems
    rw [ih1 hok hnd mems]
    refine ih2 (fun p hp' => hok p (h1.mem_iff.mpr hp')) ?_ mems
    have hfp := h1.filterMap stmtMemName
    exact hfp.nodup_iff.mp hnd

/- ------------------------------------------------------------------ -/
/- Packaging: one cycle, then whole traces. -/

/-- The keys `regNexts` will emit, in body order. -/
def nextKeys (body : List Stmt) : List String :=
  body.flatMap fun s => match s with
    | .register out _ _ _ _ => [out]
    | .memory _ _ _ _ _ _ _ _ rd cr _ er =>
      if cr then [] else rd :: er.map (·.2)
    | _ => []

theorem syncReadLatches_keys (we : WEnv) (mems : MEnv) (name : String)
    (aw dw : Nat) (envF : Env) :
    ∀ (ports : List (Expr × String)) (l : List (String × Nat)),
    syncReadLatches we mems name aw dw ports envF = some l →
    l.map Prod.fst = ports.map Prod.snd := by
  intro ports
  induction ports with
  | nil => intro l h; cases h; rfl
  | cons p rest ih =>
    intro l h
    obtain ⟨a, rd⟩ := p
    simp only [syncReadLatches, Option.bind_eq_bind] at h
    cases ha : evalExpr we envF a with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some av =>
      rw [ha] at h
      cases hrest : syncReadLatches we mems name aw dw rest envF with
      | none => rw [hrest] at h; exact absurd h (by simp)
      | some latches =>
        rw [hrest] at h
        simp only [Option.bind_some, Option.some_inj] at h
        subst h
        simp [ih latches hrest]

/-- The update list's keys are `nextKeys`, independent of values. -/
theorem regNexts_keys (we : WEnv) (mems : MEnv) (envF : Env) :
    ∀ (body : List Stmt) (l : List (String × Nat)),
    regNexts we mems body envF = some l →
    l.map Prod.fst = nextKeys body := by
  intro body
  induction body with
  | nil => intro l h; cases h; rfl
  | cons s rest ih =>
    intro l h
    match s with
    | .register out _ (rstName, _) input init =>
      simp only [regNexts, Option.bind_eq_bind] at h
      cases hv : evalExpr we envF input with
      | none => rw [hv] at h; exact absurd h (by simp)
      | some vin =>
        rw [hv] at h
        cases hrest : regNexts we mems rest envF with
        | none => rw [hrest] at h; exact absurd h (by simp)
        | some nexts =>
          rw [hrest] at h
          simp only [Option.bind_some, Option.some_inj] at h
          subst h
          simp [nextKeys, List.flatMap_cons, ih nexts hrest]
    | .assign _ _ =>
      simp only [regNexts] at h
      simpa [nextKeys, List.flatMap_cons] using ih l h
    | .memory name aw dw c wa wd wen ra rd cr ew er =>
      simp only [regNexts] at h
      cases cr with
      | true =>
        simp only [if_true] at h
        simpa [nextKeys, List.flatMap_cons] using ih l h
      | false =>
        simp only [Bool.false_eq_true, if_false, Option.bind_eq_bind] at h
        cases hl : syncReadLatches we mems name aw dw ((ra, rd) :: er) envF with
        | none => rw [hl] at h; exact absurd h (by simp)
        | some latches =>
          rw [hl] at h
          cases hrest : regNexts we mems rest envF with
          | none => rw [hrest] at h; exact absurd h (by simp)
          | some nexts =>
            rw [hrest] at h
            simp only [Option.bind_some, Option.some_inj] at h
            subst h
            have hk := syncReadLatches_keys we mems name aw dw envF
              ((ra, rd) :: er) latches hl
            simp [nextKeys, List.flatMap_cons, hk, ih nexts hrest]
    | .inst _ _ _ =>
      simp only [regNexts] at h
      simpa [nextKeys, List.flatMap_cons] using ih l h

/-- Invert one step into its three stages. -/
theorem stepModule_inv {we : WEnv} {body : List Stmt} {env0 : Env}
    {mems : MEnv} {envF : Env} {n : List (String × Nat)} {m : MEnv}
    (h : stepModule we body env0 mems = some (envF, n, m)) :
    evalAssigns we mems body env0 = some envF
    ∧ regNexts we mems body envF = some n
    ∧ memNexts we body mems envF = some m := by
  unfold stepModule at h
  cases hF : evalAssigns we mems body env0 with
  | none => rw [hF] at h; exact absurd h (by simp)
  | some e =>
    rw [hF] at h
    try simp only [Option.bind_eq_bind, Option.bind_some] at h
    cases hR : regNexts we mems body e with
    | none => rw [hR] at h; exact absurd h (by simp)
    | some nn =>
      rw [hR] at h
      try simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hM : memNexts we body mems e with
      | none => rw [hM] at h; exact absurd h (by simp)
      | some mm =>
        rw [hM] at h
        simp only [Option.bind_eq_bind, Option.bind_some,
          Option.some_inj, Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3⟩ := h
        subst h1 h2 h3
        exact ⟨rfl, hR, hM⟩

/-- **One cycle under reordering**: the final env and the memory state
    agree exactly; the register updates agree as a multiset. -/
theorem stepModule_perm (we : WEnv) {body body' : List Stmt}
    (hp : body.Perm body')
    (hWO : WO [] body) (hWO' : WO [] body')
    (hmem : (body.filterMap stmtMemName).Nodup)
    (env0 : Env) (mems : MEnv) :
    match stepModule we body env0 mems, stepModule we body' env0 mems with
    | some (e, n, m), some (e', n', m') => e = e' ∧ n.Perm n' ∧ m = m'
    | none, none => True
    | _, _ => False := by
  have hokAll := WO_all_ok hWO
  have hEnv := evalAssigns_perm we mems hp hWO hWO' env0
  unfold stepModule
  rw [← hEnv]
  cases hF : evalAssigns we mems body env0 with
  | none => trivial
  | some envF =>
    have hReg := regNexts_perm we mems envF hp
    have hMem := memNexts_perm we envF hp hokAll hmem mems
    try simp only [Option.bind_eq_bind, Option.bind_some]
    cases hR : regNexts we mems body envF with
    | none =>
      cases hR' : regNexts we mems body' envF with
      | none => simp
      | some n' => rw [hR, hR'] at hReg; exact absurd hReg (by simp [OPerm])
    | some n =>
      cases hR' : regNexts we mems body' envF with
      | none => rw [hR, hR'] at hReg; exact absurd hReg (by simp [OPerm])
      | some n' =>
        rw [hR, hR'] at hReg
        try simp only [Option.bind_eq_bind, Option.bind_some]
        rw [← hMem]
        cases hM : memNexts we body mems envF with
        | none => simp
        | some m' => simpa [OPerm] using hReg

/-- **Trace equivalence under reordering**: with unique update keys the
    observable trace is identical for any well-ordered arrangement. -/
theorem runModule_perm (we : WEnv) {body body' : List Stmt}
    (hp : body.Perm body')
    (hWO : WO [] body) (hWO' : WO [] body')
    (hmem : (body.filterMap stmtMemName).Nodup)
    (hkeys : (nextKeys body).Nodup)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
    runModule we body seed k st mems = runModule we body' seed k st mems := by
  intro k
  induction k with
  | zero => intro st mems; rfl
  | succ k ih =>
    intro st mems
    have hstep := stepModule_perm we hp hWO hWO' hmem (seed k st) mems
    simp only [runModule, Option.bind_eq_bind]
    cases h1 : stepModule we body (seed k st) mems with
    | none =>
      cases h2 : stepModule we body' (seed k st) mems with
      | none => rfl
      | some p => rw [h1, h2] at hstep; exact absurd hstep (by simp)
    | some p =>
      cases h2 : stepModule we body' (seed k st) mems with
      | none => rw [h1, h2] at hstep; exact absurd hstep (by simp)
      | some p' =>
        rw [h1, h2] at hstep
        obtain ⟨envF, n, m⟩ := p
        obtain ⟨envF', n', m'⟩ := p'
        obtain ⟨hE, hN, hM⟩ := hstep
        subst hE hM
        obtain ⟨hF, hR, _⟩ := stepModule_inv h1
        -- the register updates permute with unique keys → same applyNexts
        have hkeq : applyNexts st n = applyNexts st n' := by
          apply applyNexts_perm hN
          rw [regNexts_keys we mems envF body n hR]
          exact hkeys
        try simp only [Option.bind_eq_bind, Option.bind_some]
        rw [hkeq, ih (applyNexts st n') m]

/- ------------------------------------------------------------------ -/
/- Decidable checkers, so the permutation/well-ordering hypotheses can
   be VALIDATED per module (compile-time #guards + corpus tests) and
   the theorems applied to concrete shipping outputs. -/

deriving instance DecidableEq for Sparkle.IR.Type.DimExpr

mutual
/-- Structural equality on `Expr` (the DERIVED `BEq` is well-founded
    recursion and opaque to both kernel reduction and lawfulness
    proofs, so we roll a structural one and prove it sound). -/
def eqExpr : Expr → Expr → Bool
  | .const v w, .const v' w' => v == v' && w == w'
  | .ref n, .ref n' => n == n'
  | .op o args, .op o' args' => decide (o = o') && eqList args args'
  | .concat args, .concat args' => eqList args args'
  | .slice e hi lo, .slice e' hi' lo' =>
    eqExpr e e' && hi == hi' && lo == lo'
  | .sliceDim e hi lo, .sliceDim e' hi' lo' =>
    eqExpr e e' && decide (hi = hi') && decide (lo = lo')
  | .index a i, .index a' i' => eqExpr a a' && eqExpr i i'
  | _, _ => false

def eqList : List Expr → List Expr → Bool
  | [], [] => true
  | a :: rest, a' :: rest' => eqExpr a a' && eqList rest rest'
  | _, _ => false
end

mutual
theorem eqExpr_iff : ∀ a b : Expr, eqExpr a b = true ↔ a = b
  | .const v w, b => by
    cases b <;> simp [eqExpr, Bool.and_eq_true]
  | .ref n, b => by
    cases b <;> simp [eqExpr]
  | .op o args, b => by
    cases b <;> simp [eqExpr, Bool.and_eq_true, eqList_iff args]
  | .concat args, b => by
    cases b <;> simp [eqExpr, eqList_iff args]
  | .slice e hi lo, b => by
    cases b <;> simp [eqExpr, Bool.and_eq_true, eqExpr_iff e, and_assoc]
  | .sliceDim e hi lo, b => by
    cases b <;> simp [eqExpr, Bool.and_eq_true, eqExpr_iff e, and_assoc]
  | .index a i, b => by
    cases b <;> simp [eqExpr, Bool.and_eq_true, eqExpr_iff a, eqExpr_iff i]

theorem eqList_iff : ∀ (l l' : List Expr), eqList l l' = true ↔ l = l'
  | [], l' => by cases l' <;> simp [eqList]
  | a :: rest, l' => by
    cases l' <;> simp [eqList, Bool.and_eq_true, eqExpr_iff a,
      eqList_iff rest]
end

instance : DecidableEq Expr :=
  fun a b => decidable_of_iff _ (eqExpr_iff a b)

deriving instance DecidableEq for Stmt

/-- Boolean well-ordering check (sound for `WO`). -/
def woCheck (done : List String) : List Stmt → Bool
  | [] => true
  | s :: rest =>
    (stmtReads s).all (fun n => !(writesOf rest).contains n)
    && (stmtWrites s).all (fun n =>
        !done.contains n && !(writesOf rest).contains n)
    && woCheck (done ++ stmtWrites s) rest

theorem woCheck_sound (done : List String) (body : List Stmt)
    (h : woCheck done body = true) : WO done body := by
  induction body generalizing done with
  | nil => exact WO.nil
  | cons s rest ih =>
    simp only [woCheck, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hreads, hw⟩, hrest⟩ := h
    refine WO.cons ?_ ?_ ?_ (ih _ hrest)
    · trivial
    · intro n hn
      have := hreads n hn
      simpa [List.contains_iff_mem] using this
    · intro n hn
      have := hw n hn
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      constructor
      · intro hin
        have h1 := this.1
        simp [List.contains_iff_mem] at h1
        exact h1 hin
      · intro hin
        have h2 := this.2
        simp [List.contains_iff_mem] at h2
        exact h2 hin

/-- Sound (one-directional) permutation check, erase-based. -/
def isPermOf [DecidableEq α] : List α → List α → Bool
  | [], [] => true
  | [], _ :: _ => false
  | a :: rest, l =>
    if a ∈ l then isPermOf rest (l.erase a) else false

theorem isPermOf_sound [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, isPermOf l₁ l₂ = true → l₁.Perm l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => exact List.Perm.refl _
    | cons _ _ => simp [isPermOf] at h
  | cons a rest ih =>
    intro l₂ h
    simp only [isPermOf] at h
    by_cases hmem : a ∈ l₂
    · rw [if_pos hmem] at h
      exact ((ih h).cons a).trans (List.perm_cons_erase hmem).symm
    · rw [if_neg hmem] at h
      cases h

end Sparkle.IR.Reorder
