import Sparkle.IR.PrintCheck
import Sparkle.IR.Semantics
import Sparkle.IR.RegDedup
import Sparkle.IR.ReorderInvariance

/-! # The print guard: an executable check of the emitted-text fragment

`printOk m`: every assignment and register input of `m` is in the forward
fragment of the statement emitter at its declared width, under declared,
sanitize-stable names, and the IR's and the emitter's width tables agree on
the names the body uses. `Sparkle.IR.HierCheck.keepGuarded` keeps an
optimizer candidate only when it passes; otherwise the input module is
shipped (a fallback, never a rejection).

The definitions below are LITERAL COPIES of the proof-side checks
(`Tools/SVParser/EmitSem.lean`: `immuneE`, `isShlLit`, `shlSideOK`,
`shlOperand`, `sf4Check`, `seqCheck` without its memory arm;
`Tools/SVParser/EmitAst.lean`: `exprWidthT`;
`Tools/ShippingSeqSVSoundness.lean`: `seqNames`), made by a script, because
the compiler imports no proof-side module. `Tools/ShippingPrintGuard.lean`
proves that a `true` verdict here is a `true` verdict there. If the
originals change, these copies do not follow.

No proof about them is in this file (one termination lemma apart). -/
namespace Sparkle.IR.PrintGuard
open Sparkle.IR.AST
open Sparkle.IR.Semantics

/-- Total twin of `Sparkle.Backend.Verilog.exprWidthV` (verbatim rules). -/
def exprWidthT (widthOf : String → Option Nat) : Expr → Option Nat
  | .const _ w => some w
  | .ref n => widthOf n
  | .slice _ hi lo => some (hi - lo + 1)
  | .concat args => goSum args
  | .op op args =>
    match op with
    | .eq | .lt_u | .lt_s | .le_u | .le_s | .gt_u | .gt_s | .ge_u | .ge_s =>
      some 1
    | .and | .or | .xor | .not | .add | .sub => goMax args
    | .mux =>
      match args with
      | [_, t, e] =>
        match exprWidthT widthOf t, exprWidthT widthOf e with
        | some x, some y => some (max x y)
        | _, _ => none
      | _ => none
    | _ => none
  | _ => none
where
  goSum : List Expr → Option Nat
    | [] => some 0
    | a :: rest =>
      match exprWidthT widthOf a, goSum rest with
      | some x, some y => some (x + y)
      | _, _ => none
  goMax : List Expr → Option Nat
    | [] => some 1
    | a :: rest =>
      match exprWidthT widthOf a, goMax rest with
      | some x, some y => some (max x y)
      | _, _ => none


/-- IR shapes whose EMISSIONS are context-immune (see `immuneSV`):
    refs, fitting constants, compares, the pinned NOT (a size cast),
    and every slice (all three slice emission arms are idents, ident
    slices, or size casts). -/
def immuneE : Expr → Bool
  | .ref _ => true
  | .const v w => v < ((2 ^ w : Nat) : Int)
  | .op .not [_] => true
  | .op op [a, b] =>
    match op with
    | .eq | .lt_u | .le_u | .gt_u | .ge_u => true
    | .lt_s | .le_s | .gt_s | .ge_s => true
    -- bitwise ops are carry-free: immune operands make the node immune
    | .and | .or | .xor => immuneE a && immuneE b
    | _ => false
  | .op .mux [_, t, f] => immuneE t && immuneE f
  | .slice _ _ _ => true
  -- concat elements are self-determined; the assembly fits its width
  | .concat _ => true
  | _ => false

/-- Is this expression a literal-amount left shift?  A top-level
    definition so its equation lemmas are available to proofs, rather
    than an inline `match` whose splitting leaks side goals. -/
def isShlLit : Expr → Bool
  | .op .shl [_, .const _ _] => true
  | _ => false

/-- Decidable side conditions of `bitwiseShl` on the LEFT operand:
    `a` must BE `x << const k kw` with the rule's conditions met.  The
    sub-fragment check is NOT here — `sf4` supplies it via
    `shlOperand`, so this stays independent of the checker. -/
def shlSideOK (we : WEnv) (a b : Expr) : Bool :=
  match a with
  | .op .shl [x, .const kk kw] =>
    (0 ≤ kk) && (decide (kk.toNat < 2 ^ kw)) && (decide (0 < kw))
      && ((immuneE x
          && (decide (Sparkle.IR.Semantics.widthOf we x + kk.toNat
            ≤ max (Sparkle.IR.Semantics.widthOf we x) kw))
          && (decide (max (Sparkle.IR.Semantics.widthOf we x) kw
            ≤ Sparkle.IR.Semantics.widthOf we b)))
        -- or the sibling is exactly as wide as the shifted value
        || ((decide (kw ≤ Sparkle.IR.Semantics.widthOf we x))
          && (decide (Sparkle.IR.Semantics.widthOf we b
            = Sparkle.IR.Semantics.widthOf we x))))
  | _ => false

/-- The VALUE operand of a literal-amount shift, or the expression
    itself otherwise.  `sf4` recurses through this so the shl
    route's sub-check rides an ordinary structural recursion. -/
def shlOperand : Expr → Expr
  | .op .shl [x, .const _ _] => x
  | e => e

/-- `shlOperand` never grows its argument — what the termination proof
    of `sf4` needs. -/
theorem shlOperand_lt (e : Expr) : sizeOf (shlOperand e) ≤ sizeOf e := by
  unfold shlOperand
  split
  · rename_i x kk kw
    simp
    omega
  · exact Nat.le_refl _

/-- `shlOperand` is the identity off `isShlLit`. -/
theorem shlOperand_id {e : Expr} (h : isShlLit e = false) :
    shlOperand e = e := by
  -- both functions split on the SAME shape, so one `split` covers it
  unfold shlOperand
  split
  · rename_i x kk kw
    simp [isShlLit] at h
  · rfl

/-- Decidable mirror of `SF4` — the per-expression forward-fragment
    membership test the census and gate run.  Soundness below ties a
    `true` verdict to the `emit_sem` theorem. -/
def sf4 (wof : String → Option Nat) (we : WEnv) :
    Expr → Bool
  | .ref n =>
    (Sparkle.Backend.Verilog.sanitizeName n == n)
      && (wof n == some (we n))
  | .const _ w => 0 < w
  | .op .neg [x] => sf4 wof we x
  | .op .not [x] =>
    (exprWidthT wof x
        == some (Sparkle.IR.Semantics.widthOf we x))
      && (0 < Sparkle.IR.Semantics.widthOf we x)
      && sf4 wof we x
  | .op .mux [c, t, f] =>
    (Sparkle.IR.Semantics.widthOf we f
        == Sparkle.IR.Semantics.widthOf we t)
      && sf4 wof we c && sf4 wof we t && sf4 wof we f
  | .op op [a, b] =>
    let wa := Sparkle.IR.Semantics.widthOf we a
    let wb := Sparkle.IR.Semantics.widthOf we b
    -- All THREE recursive calls are made unconditionally and at the
    -- arm's top level, so `sf4.induct` hands out one IH each and
    -- both routes below have what they need.  (`shlOperand a` is `a`
    -- itself unless `a` is a literal-amount shift.)
    -- ONE recursive call on the left, through `shlOperand`.  When `a`
    -- is a literal-amount shift the shl route is the only one that can
    -- fire (`sf4` rejects the shift node itself), and when it is
    -- not, `shlOperand a = a` — so a single call serves both routes.
    -- Recursing on BOTH `a` and `shlOperand a` re-walked the left
    -- subtree at every bitwise level: 249 nodes became 19.7 M calls.
    let chkL := sf4 wof we (shlOperand a)
    let chkB := sf4 wof we b
    let notShl : Bool := !isShlLit a
    let perOp := ((wa == max wa wb) || immuneE a)
      && ((wb == max wa wb) || immuneE b)
      && notShl && chkL && chkB
    match op with
    -- a bitwise node over a literal-amount shift rides `bitwiseShl`:
    -- the shift carries only a VALUE claim (`shl_val_at`), which is
    -- all a bitwise parent needs
    | .and | .or | .xor =>
      perOp || (shlSideOK we a b && chkL && chkB)
    | .add | .sub | .mul => perOp
    | .eq | .lt_u | .le_u | .gt_u | .ge_u => perOp
    -- SHR's width is its value operand's, so no width condition;
    -- SHL still takes the generic max
    -- these arms reuse `chkL`; `notShl` makes it a check on `a` itself
    | .shl => (wb ≤ wa) && notShl && chkL && chkB
    | .shr => notShl && chkL && chkB
    | .lt_s | .le_s | .gt_s | .ge_s =>
      ((exprWidthT wof a == some wa)
        && (exprWidthT wof b == some wb)
        && (0 < max wa wb) && perOp) ||
      ((exprWidthT wof a == some wa)
        && (exprWidthT wof b == none)
        && (wb ≤ wa) && ((wb == wa) || immuneE b) && (0 < wa)
        && notShl && chkL && chkB)
    | _ => false
  | .concat args =>
    args.attach.all fun ⟨e, _⟩ =>
      sf4 wof we e &&
      (match e with
       | .op _ _ =>
         (exprWidthT wof e
             == some (Sparkle.IR.Semantics.widthOf we e))
           && (0 < Sparkle.IR.Semantics.widthOf we e)
       | _ => true)
  | .slice (.concat [.const 0 w, x]) hi lo =>
    -- canonical cast encode, or the general-slice route over the concat
    ((lo == 0) && (hi + 1 == w) && (0 < w) && sf4 wof we x
      && ((w ≤ Sparkle.IR.Semantics.widthOf we x) || immuneE x)) ||
    (!(lo == 0 && hi + 1 == w) && (lo ≤ hi) && (lo < 2 ^ 32)
      && sf4 wof we (.concat [.const 0 w, x])
      && ((hi + 1 - lo
            ≤ Sparkle.IR.Semantics.widthOf we (.concat [.const 0 w, x]))
        || immuneE (.concat [.const 0 w, x])))
  | .slice (.ref n) hi lo =>
    ((Sparkle.Backend.Verilog.sanitizeName n == n)
      && (wof n == some (we n))
      && (lo ≤ hi) && (hi < we n) && !(lo == 0 && hi + 1 == we n)) ||
    ((Sparkle.Backend.Verilog.sanitizeName n == n)
      && (wof n == some (we n)) && (lo == 0) && (hi + 1 == we n))
  | .slice x hi lo =>
    (lo ≤ hi) && (lo < 2 ^ 32) && sf4 wof we x
      && ((hi + 1 - lo ≤ Sparkle.IR.Semantics.widthOf we x)
        || immuneE x)
  | _ => false
decreasing_by all_goals
  first
  | (simp_wf
     have := List.sizeOf_lt_of_mem ‹_ ∈ _›
     omega)
  | (simp_wf; omega)
  | -- the `shlOperand a` recursion: never larger than `a`
    (simp_wf; exact Nat.lt_of_le_of_lt (shlOperand_lt _) (by omega))

/-- The statement check: assignments and registers in the fragment at their
declared widths; instances are not tested; a memory is refused. -/
def seqText (wof : String → Option Nat) (we : WEnv) :
    List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (Sparkle.Backend.Verilog.sanitizeName l == l)
      && (wof l == some (we l))
      && (Sparkle.IR.Semantics.widthOf we r == we l)
      && sf4 wof we r
      && seqText wof we rest
  | .register out _ _ input _ :: rest =>
    (wof out == some (we out))
      && (Sparkle.IR.Semantics.widthOf we input == we out)
      && sf4 wof we input
      && seqText wof we rest
  | .memory .. :: _ => false
  | .inst _ _ _ :: rest => seqText wof we rest

/-- The names whose widths a run of the body reads. -/
def seqNames : List Stmt → List String
  | [] => []
  | .assign _ r :: rest => Sparkle.IR.Reorder.refsOf r ++ seqNames rest
  | .register o _ _ i _ :: rest => o :: (Sparkle.IR.Reorder.refsOf i ++ seqNames rest)
  | _ :: rest => seqNames rest

/-- The emitter's induced width of a name (0 when undeclared). -/
def weOf (m : Module) : WEnv := fun n => (Sparkle.IR.PrintCheck.widths m n).getD 0

/-- **The print guard.** -/
def printOk (m : Module) : Bool :=
  seqText (Sparkle.IR.PrintCheck.widths m) (weOf m) m.body &&
    (seqNames m.body).all fun x => Sparkle.IR.RegDedup.declWidth m x == weOf m x

end Sparkle.IR.PrintGuard
