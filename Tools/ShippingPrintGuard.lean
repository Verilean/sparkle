import Sparkle.IR.PrintGuard
import Sparkle.IR.HierCheck
import Tools.ShippingDesignSVLeaf
import Tools.ShippingSeqSVSoundness

/-! # The print guard's verdict is the proof-side check's (branch `fix/opt-fallback`)

`Sparkle.IR.PrintGuard.printOk` is built from literal copies of the
proof-side definitions (the compiler imports no `Tools` module). Here the
copies are shown EQUAL to the originals, so that

    printOk_sound : printOk m = true →
      seqCheck (wofOf m) (weS m) m.body = true ∧
      (seqNames m.body).all (fun x => declWidth m x == weS m x) = true

— conjuncts 2 and 3 of `textCheckI`.

* `widths_eq`, `weOf_eq`: `Sparkle.IR.PrintCheck.widths m = moduleWof m`,
  and the induced width environments.
* `seqNames_eq`.
* `immuneE_eq`, `isShlLit_eq`, `shlOperand_eq`, `shlSideOK_eq`.
* `ew_eq` (with `gs_eq`, `gm_eq`): `exprWidthT` and its two list folds.
* `sf4_eq`: by the functional induction of the ORIGINAL (`sf4Check.induct`),
  unfolding both sides in each case.
* `seqText_sound`: one-way (the copy refuses memories; the original has a
  memory arm).

Two definitions with the same text in two modules have different matcher
constants: none of the equalities is `rfl`.

UNVERIFIED at the time of writing: this file was not built. The proofs of
`immuneE_eq`, `ew_eq` and `sf4_eq` are written against equation lemmas and
an induction principle that were not seen; each case tries several scripts
(`first`). They are the most likely of this round to need repair. -/
namespace Tools.ShippingPrintGuard
open Sparkle.IR.AST Sparkle.IR.Semantics

/-- The compiler's width map is the emitter's. -/
theorem widths_eq (m : Sparkle.IR.AST.Module) :
    Sparkle.IR.PrintCheck.widths m = Tools.SVParser.RoundtripProof.moduleWof m := by
  funext x
  simp only [Sparkle.IR.PrintCheck.widths, Tools.SVParser.RoundtripProof.moduleWof]
  cases h : (m.wires ++ m.inputs ++ m.outputs).find?
      (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) with
  | none => rfl
  | some p =>
    obtain ⟨nm, ty⟩ := p
    cases ty <;> rfl

/-- The induced width environments agree. -/
theorem weOf_eq (m : Sparkle.IR.AST.Module) :
    Sparkle.IR.PrintGuard.weOf m = Tools.ShippingDesignSV.weS m := by
  funext n
  show (Sparkle.IR.PrintCheck.widths m n).getD 0 =
    (Tools.SVParser.RoundtripProof.moduleWof m n).getD 0
  rw [widths_eq]

theorem seqNames_eq : ∀ body : List Stmt,
    Sparkle.IR.PrintGuard.seqNames body = Tools.ShippingSeqSVSoundness.seqNames body
  | [] => rfl
  | st :: rest => by
    have ih := seqNames_eq rest
    cases st with
    | assign l r =>
      show Sparkle.IR.Reorder.refsOf r ++ Sparkle.IR.PrintGuard.seqNames rest =
        Sparkle.IR.Reorder.refsOf r ++ Tools.ShippingSeqSVSoundness.seqNames rest
      rw [ih]
    | register o c rk i iv =>
      show o :: (Sparkle.IR.Reorder.refsOf i ++ Sparkle.IR.PrintGuard.seqNames rest) =
        o :: (Sparkle.IR.Reorder.refsOf i ++ Tools.ShippingSeqSVSoundness.seqNames rest)
      rw [ih]
    | _ =>
      first
        | exact ih
        | simpa [Sparkle.IR.PrintGuard.seqNames, Tools.ShippingSeqSVSoundness.seqNames] using ih

/-- A Boolean that cannot be `true` is `false`. -/
theorem bool_false_of {b : Bool} (h : b = true → False) : b = false := by
  cases b
  · rfl
  · exact (h rfl).elim

set_option maxHeartbeats 2000000 in
theorem immuneE_eq : ∀ e : Sparkle.IR.AST.Expr,
    Sparkle.IR.PrintGuard.immuneE e = Tools.SVParser.EmitSem.immuneE e := by
  intro e
  induction e using Tools.SVParser.EmitSem.immuneE.induct
  all_goals
    first
      | (rw [Sparkle.IR.PrintGuard.immuneE, Tools.SVParser.EmitSem.immuneE] <;>
          first
            | rfl
            | (simp only [*]; done))
      | (simp only [Sparkle.IR.PrintGuard.immuneE, Tools.SVParser.EmitSem.immuneE, *]; done)
      | (simp_all [Sparkle.IR.PrintGuard.immuneE, Tools.SVParser.EmitSem.immuneE]; done)
      | (apply Eq.trans (bool_false_of ?_) (Eq.symm (bool_false_of ?_)) <;>
          (intro h
           first
             | (rw [Sparkle.IR.PrintGuard.immuneE.eq_def] at h
                split at h <;>
                  first
                    | (simp_all; done)
                    | grind
                    | (simp_all; grind))
             | (rw [Tools.SVParser.EmitSem.immuneE.eq_def] at h
                split at h <;>
                  first
                    | (simp_all; done)
                    | grind
                    | (simp_all; grind))))

theorem isShlLit_eq (e : Sparkle.IR.AST.Expr) :
    Sparkle.IR.PrintGuard.isShlLit e = Tools.SVParser.EmitSem.isShlLit e := by
  unfold Sparkle.IR.PrintGuard.isShlLit Tools.SVParser.EmitSem.isShlLit
  split <;>
    first
      | rfl
      | (split <;>
          first
            | rfl
            | (simp_all; done)
            | grind)

theorem shlOperand_eq (e : Sparkle.IR.AST.Expr) :
    Sparkle.IR.PrintGuard.shlOperand e = Tools.SVParser.EmitSem.shlOperand e := by
  unfold Sparkle.IR.PrintGuard.shlOperand Tools.SVParser.EmitSem.shlOperand
  split <;>
    first
      | rfl
      | (split <;>
          first
            | rfl
            | (simp_all; done)
            | grind)

theorem shlSideOK_eq (we : WEnv) (a b : Sparkle.IR.AST.Expr) :
    Sparkle.IR.PrintGuard.shlSideOK we a b = Tools.SVParser.EmitSem.shlSideOK we a b := by
  unfold Sparkle.IR.PrintGuard.shlSideOK Tools.SVParser.EmitSem.shlSideOK
  split <;>
    first
      | rfl
      | (simp only [immuneE_eq]; done)
      | (simp [immuneE_eq]; done)
      | (split <;>
          first
            | rfl
            | (simp_all [immuneE_eq]; done)
            | grind)

/-- The sum fold agrees when the elements' widths do. -/
theorem gs_of (wof : String → Option Nat) :
    ∀ args : List Sparkle.IR.AST.Expr,
      (∀ a ∈ args, Sparkle.IR.PrintGuard.exprWidthT wof a =
        Tools.SVParser.EmitAst.exprWidthT wof a) →
      Sparkle.IR.PrintGuard.exprWidthT.goSum wof args =
        Tools.SVParser.EmitAst.exprWidthT.goSum wof args
  | [], _ => by
    simp [Sparkle.IR.PrintGuard.exprWidthT.goSum, Tools.SVParser.EmitAst.exprWidthT.goSum]
  | a :: rest, h => by
    have ih := gs_of wof rest (fun x hx => h x (List.Mem.tail _ hx))
    have ha := h a (List.Mem.head _)
    first
      | (simp only [Sparkle.IR.PrintGuard.exprWidthT.goSum,
          Tools.SVParser.EmitAst.exprWidthT.goSum, ha, ih]; done)
      | (simp only [Sparkle.IR.PrintGuard.exprWidthT.goSum,
          Tools.SVParser.EmitAst.exprWidthT.goSum, ha, ih]
         cases Tools.SVParser.EmitAst.exprWidthT wof a <;>
           cases Tools.SVParser.EmitAst.exprWidthT.goSum wof rest <;> rfl)

/-- The max fold agrees when the elements' widths do. -/
theorem gm_of (wof : String → Option Nat) :
    ∀ args : List Sparkle.IR.AST.Expr,
      (∀ a ∈ args, Sparkle.IR.PrintGuard.exprWidthT wof a =
        Tools.SVParser.EmitAst.exprWidthT wof a) →
      Sparkle.IR.PrintGuard.exprWidthT.goMax wof args =
        Tools.SVParser.EmitAst.exprWidthT.goMax wof args
  | [], _ => by
    simp [Sparkle.IR.PrintGuard.exprWidthT.goMax, Tools.SVParser.EmitAst.exprWidthT.goMax]
  | a :: rest, h => by
    have ih := gm_of wof rest (fun x hx => h x (List.Mem.tail _ hx))
    have ha := h a (List.Mem.head _)
    first
      | (simp only [Sparkle.IR.PrintGuard.exprWidthT.goMax,
          Tools.SVParser.EmitAst.exprWidthT.goMax, ha, ih]; done)
      | (simp only [Sparkle.IR.PrintGuard.exprWidthT.goMax,
          Tools.SVParser.EmitAst.exprWidthT.goMax, ha, ih]
         cases Tools.SVParser.EmitAst.exprWidthT wof a <;>
           cases Tools.SVParser.EmitAst.exprWidthT.goMax wof rest <;> rfl)

set_option maxHeartbeats 2000000 in
/-- The two width functions agree on every expression smaller than `n`
(strong induction on the size, so that the list folds can use the fact for
their elements). -/
theorem ew_lt (wof : String → Option Nat) : ∀ (n : Nat) (e : Sparkle.IR.AST.Expr),
    sizeOf e < n →
    Sparkle.IR.PrintGuard.exprWidthT wof e = Tools.SVParser.EmitAst.exprWidthT wof e
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, e, h => by
    have ih : ∀ x : Sparkle.IR.AST.Expr, sizeOf x < n →
        Sparkle.IR.PrintGuard.exprWidthT wof x = Tools.SVParser.EmitAst.exprWidthT wof x :=
      fun x hx => ew_lt wof n x hx
    have ihl : ∀ args : List Sparkle.IR.AST.Expr, sizeOf args ≤ n →
        ∀ a ∈ args, Sparkle.IR.PrintGuard.exprWidthT wof a =
          Tools.SVParser.EmitAst.exprWidthT wof a := by
      intro args hargs a ha
      have := List.sizeOf_lt_of_mem ha
      exact ih a (by omega)
    cases e with
    | const v w => simp [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT]
    | ref x => simp [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT]
    | slice x hi lo =>
      simp [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT]
    | sliceDim x hi lo =>
      simp [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT]
    | index a i => simp [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT]
    | concat args =>
      have hsz : sizeOf args ≤ n := by
        simp only [Sparkle.IR.AST.Expr.concat.sizeOf_spec] at h
        omega
      simp only [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT]
      exact gs_of wof args (ihl args hsz)
    | op o args =>
      have hsz : sizeOf args ≤ n := by
        simp only [Sparkle.IR.AST.Expr.op.sizeOf_spec] at h
        omega
      have hgm := gm_of wof args (ihl args hsz)
      cases o
      all_goals
        first
          | (simp only [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT];
             done)
          | (simp only [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT];
             exact hgm)
          | (rcases args with _ | ⟨c, _ | ⟨t, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩ <;>
              first
                | (simp only [Sparkle.IR.PrintGuard.exprWidthT,
                    Tools.SVParser.EmitAst.exprWidthT]; done)
                | (have ht := ihl _ hsz t (by simp)
                   have hf := ihl _ hsz f (by simp)
                   simp only [Sparkle.IR.PrintGuard.exprWidthT,
                     Tools.SVParser.EmitAst.exprWidthT, ht, hf]
                   cases Tools.SVParser.EmitAst.exprWidthT wof t <;>
                     cases Tools.SVParser.EmitAst.exprWidthT wof f <;> rfl)
                | (simp [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT,
                    ihl _ hsz]; done)
                | (simp_all [Sparkle.IR.PrintGuard.exprWidthT,
                    Tools.SVParser.EmitAst.exprWidthT]; done))
          | (simp_all [Sparkle.IR.PrintGuard.exprWidthT, Tools.SVParser.EmitAst.exprWidthT];
             done)

theorem ew_eq (wof : String → Option Nat) (e : Sparkle.IR.AST.Expr) :
    Sparkle.IR.PrintGuard.exprWidthT wof e = Tools.SVParser.EmitAst.exprWidthT wof e :=
  ew_lt wof (sizeOf e + 1) e (Nat.lt_succ_self _)

/-- Two `all`s over the same attached list with pointwise-equal tests. -/
theorem all_attach_congr {α : Type} (l : List α) (f g : { x // x ∈ l } → Bool)
    (h : ∀ x, f x = g x) : l.attach.all f = l.attach.all g := by
  rw [show f = g from funext h]

set_option maxHeartbeats 8000000 in
/-- **The fragment checks agree.** -/
theorem sf4_eq (wof : String → Option Nat) (we : WEnv) : ∀ e : Sparkle.IR.AST.Expr,
    Sparkle.IR.PrintGuard.sf4 wof we e = Tools.SVParser.EmitSem.sf4Check wof we e := by
  intro e
  induction e using Tools.SVParser.EmitSem.sf4Check.induct wof we
  case case24 args ih =>
    rw [Sparkle.IR.PrintGuard.sf4, Tools.SVParser.EmitSem.sf4Check]
    refine all_attach_congr args _ _ ?_
    intro x
    obtain ⟨a, ha⟩ := x
    have iha := ih a ha
    cases a <;>
      first
        | (simp only [iha, ew_eq]; done)
        | (simp [iha, ew_eq]; done)
  all_goals
    first
      | (rw [Sparkle.IR.PrintGuard.sf4, Tools.SVParser.EmitSem.sf4Check] <;>
          first
            | rfl
            | (simp only [*, immuneE_eq, isShlLit_eq, shlOperand_eq, shlSideOK_eq, ew_eq]; done))
      | (simp only [Sparkle.IR.PrintGuard.sf4, Tools.SVParser.EmitSem.sf4Check, *, immuneE_eq,
          isShlLit_eq, shlOperand_eq, shlSideOK_eq, ew_eq]; done)
      | (simp_all [Sparkle.IR.PrintGuard.sf4, Tools.SVParser.EmitSem.sf4Check, immuneE_eq,
          isShlLit_eq, shlOperand_eq, shlSideOK_eq, ew_eq]; done)
      | (apply Eq.trans (bool_false_of ?_) (Eq.symm (bool_false_of ?_)) <;>
          (intro h
           first
             | (rw [Sparkle.IR.PrintGuard.sf4.eq_def] at h
                split at h <;>
                  first
                    | (simp_all; done)
                    | grind
                    | (simp_all; grind))
             | (rw [Tools.SVParser.EmitSem.sf4Check.eq_def] at h
                split at h <;>
                  first
                    | (simp_all; done)
                    | grind
                    | (simp_all; grind))))

/-- **The statement check's verdict is `seqCheck`'s.** -/
theorem seqText_sound {wof : String → Option Nat} {we : WEnv} :
    ∀ body : List Stmt, Sparkle.IR.PrintGuard.seqText wof we body = true →
      Tools.SVParser.EmitSem.seqCheck wof we body = true
  | [], _ => rfl
  | st :: rest, h => by
    cases st with
    | assign l r =>
      simp only [Sparkle.IR.PrintGuard.seqText, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      rw [sf4_eq] at h4
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, seqText_sound rest h5⟩
    | register o c rk i iv =>
      simp only [Sparkle.IR.PrintGuard.seqText, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := h
      rw [sf4_eq] at h4
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨h2, h3⟩, h4⟩, seqText_sound rest h5⟩
    | inst mn iname conns =>
      simp only [Sparkle.IR.PrintGuard.seqText] at h
      simp only [Tools.SVParser.EmitSem.seqCheck]
      exact seqText_sound rest h
    | memory nm aw dw c wa wd wen ra rd cr ew er =>
      simp [Sparkle.IR.PrintGuard.seqText] at h

/-- **A module passing the print guard passes conjuncts 2 and 3 of
`textCheckI`.** -/
theorem printOk_sound {m : Sparkle.IR.AST.Module}
    (h : Sparkle.IR.PrintGuard.printOk m = true) :
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf m)
        (Tools.ShippingDesignSV.weS m) m.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames m.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingDesignSV.weS m x) = true := by
  unfold Sparkle.IR.PrintGuard.printOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [widths_eq, weOf_eq] at h1
  rw [seqNames_eq, weOf_eq] at h2
  exact ⟨seqText_sound _ h1, h2⟩

end Tools.ShippingPrintGuard
