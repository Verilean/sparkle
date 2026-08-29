/-
  Certified-roundtrip spike: `lower (emit x) = x`, proven, for a fragment.

  This file calibrates the cost of the full theorem
      ⟦ parse (emit x) ⟧ = ⟦ x ⟧
  by proving the STRICTEST version (syntactic equality, no semantics
  needed) for the fragment of the IR where the emitter and the lowerer
  are mutual inverses on the nose: refs, non-negative sized constants,
  and the 1:1 binary operators (and/or/xor/add/mul) plus mux.

  Architecture — verified core, validated shell:

  * The shipping `lowerExpr` is a `partial def`: Lean generates NO
    unfolding equations for it, so no theorem can mention it.  The same
    holds for the emitter and parser (73 `partial def`s on the path).
    The proof therefore speaks about TOTAL twins (`emitFrag`,
    `lowerFrag`) whose equations mirror the shipping code line for line,
    and the shipping code is tied to the twins by executable
    cross-checks (`#guard` below runs at compile time; ParserTest keeps
    the string layer honest end-to-end).

  * `emitFrag` works at the AST level (`Expr → SVExpr`), not strings:
    the string layer (`render`/`parse`) is a separate printer-parser
    inverse obligation.  Splitting there is what makes the interesting
    half — "does the TRANSLATION lose meaning?" — provable by structural
    induction.  Every silent bug the XiangShan campaign found in the
    emit/lower pair (dropped slice offsets, self-determined concat
    widths, context-widened `~`) lives in exactly the layer this
    theorem covers; none of them lived in tokenization.

  * The theorem here is SYNTACTIC (`= x`, not `≈ x`).  It only holds on
    the 1:1 fragment — the full IR needs the semantic statement against
    `Sparkle.IR.Semantics.evalExpr`, because lowering normalizes
    (bit-selects become shr+mask+slice, size casts become
    slice-of-concat, signed compares become the bias form, …).
-/

import Sparkle.IR.Semantics
import Tools.SVParser.Lower
import Tools.SVParser.EmitAst

namespace Tools.SVParser.RoundtripProof

open Sparkle.IR.AST
open Tools.SVParser.AST
open Tools.SVParser.Lower

/-- AST-level emission for the 1:1 fragment: what `Backend.Verilog`'s
    string emitter produces for these constructors, reified as the
    parser's AST.  `none` = outside the fragment. -/
def emitFrag : Expr → Option SVExpr
  | .ref n => some (.ident n)
  | .const v w =>
    -- The emitter prints `w'd<v>` for v ≥ 0; negatives take a different
    -- (two's-complement encode) path and join the fragment later.
    if h : 0 ≤ v then some (.lit (.decimal (some w) v.toNat)) else none
  | .op .and [a, b] => do some (.binary .bitAnd (← emitFrag a) (← emitFrag b))
  | .op .or  [a, b] => do some (.binary .bitOr  (← emitFrag a) (← emitFrag b))
  | .op .xor [a, b] => do some (.binary .bitXor (← emitFrag a) (← emitFrag b))
  | .op .add [a, b] => do some (.binary .add    (← emitFrag a) (← emitFrag b))
  | .op .mul [a, b] => do some (.binary .mul    (← emitFrag a) (← emitFrag b))
  | .op .mux [c, t, f] =>
    do some (.ternary (← emitFrag c) (← emitFrag t) (← emitFrag f))
  | _ => none

/-- Total twin of the shipping `lowerExpr`, restricted to the fragment.
    Each equation is copied VERBATIM from `Lower.lean` (the `.lit`
    equation from `literalToConst`, the `.binary` fall-through from
    line 407, `.ternary` from the line below it); the `#guard`s at the
    bottom hold the two implementations together. -/
def lowerFrag : SVExpr → Option Expr
  | .lit (.decimal (some w) v) => some (.const (Int.ofNat v) w)
  | .ident name => some (.ref name)
  | .binary .bitAnd a b => do some (.op .and [← lowerFrag a, ← lowerFrag b])
  | .binary .bitOr  a b => do some (.op .or  [← lowerFrag a, ← lowerFrag b])
  | .binary .bitXor a b => do some (.op .xor [← lowerFrag a, ← lowerFrag b])
  | .binary .add    a b => do some (.op .add [← lowerFrag a, ← lowerFrag b])
  | .binary .mul    a b => do some (.op .mul [← lowerFrag a, ← lowerFrag b])
  | .ternary c t f =>
    do some (.op .mux [← lowerFrag c, ← lowerFrag t, ← lowerFrag f])
  | _ => none

/-- The fragment, as a predicate: exactly the domain of `emitFrag`. -/
inductive Frag : Expr → Prop
  | ref (n : String) : Frag (.ref n)
  | const (v : Int) (w : Nat) (h : 0 ≤ v) : Frag (.const v w)
  | and  {a b} : Frag a → Frag b → Frag (.op .and [a, b])
  | or   {a b} : Frag a → Frag b → Frag (.op .or  [a, b])
  | xor  {a b} : Frag a → Frag b → Frag (.op .xor [a, b])
  | add  {a b} : Frag a → Frag b → Frag (.op .add [a, b])
  | mul  {a b} : Frag a → Frag b → Frag (.op .mul [a, b])
  | mux  {c t f} : Frag c → Frag t → Frag f → Frag (.op .mux [c, t, f])

/-- **The roundtrip theorem** (fragment, syntactic): emitting to the
    Verilog AST and lowering back is the identity.  Structural induction
    over the fragment; each case is definitional unfolding. -/
theorem lower_emit_id {e : Expr} (h : Frag e) :
    (emitFrag e).bind lowerFrag = some e := by
  induction h with
  | ref n => rfl
  | const v w hv =>
    simp [emitFrag, dif_pos hv, lowerFrag, Int.toNat_of_nonneg hv]
  | and ha hb iha ihb =>
    obtain ⟨ea, hea, hla⟩ := Option.bind_eq_some_iff.mp iha
    obtain ⟨eb, heb, hlb⟩ := Option.bind_eq_some_iff.mp ihb
    simp [emitFrag, hea, heb, lowerFrag, hla, hlb]
  | or ha hb iha ihb =>
    obtain ⟨ea, hea, hla⟩ := Option.bind_eq_some_iff.mp iha
    obtain ⟨eb, heb, hlb⟩ := Option.bind_eq_some_iff.mp ihb
    simp [emitFrag, hea, heb, lowerFrag, hla, hlb]
  | xor ha hb iha ihb =>
    obtain ⟨ea, hea, hla⟩ := Option.bind_eq_some_iff.mp iha
    obtain ⟨eb, heb, hlb⟩ := Option.bind_eq_some_iff.mp ihb
    simp [emitFrag, hea, heb, lowerFrag, hla, hlb]
  | add ha hb iha ihb =>
    obtain ⟨ea, hea, hla⟩ := Option.bind_eq_some_iff.mp iha
    obtain ⟨eb, heb, hlb⟩ := Option.bind_eq_some_iff.mp ihb
    simp [emitFrag, hea, heb, lowerFrag, hla, hlb]
  | mul ha hb iha ihb =>
    obtain ⟨ea, hea, hla⟩ := Option.bind_eq_some_iff.mp iha
    obtain ⟨eb, heb, hlb⟩ := Option.bind_eq_some_iff.mp ihb
    simp [emitFrag, hea, heb, lowerFrag, hla, hlb]
  | mux hc ht hf ihc iht ihf =>
    obtain ⟨ec, hec, hlc⟩ := Option.bind_eq_some_iff.mp ihc
    obtain ⟨et, het, hlt⟩ := Option.bind_eq_some_iff.mp iht
    obtain ⟨ef, hef, hlf⟩ := Option.bind_eq_some_iff.mp ihf
    simp [emitFrag, hec, het, hef, lowerFrag, hlc, hlt, hlf]

/- Validated shell: hold the total twin to the SHIPPING `partial def`
   `lowerExpr` on representative fragment members.  These run at compile
   time; if someone edits `lowerExpr`'s fragment equations without
   updating `lowerFrag`, the build fails here. -/

private def chk (sv : SVExpr) : Bool :=
  lowerFrag sv == some (lowerExpr sv)

#guard chk (.ident "a")
#guard chk (.lit (.decimal (some 8) 42))
#guard chk (.binary .bitAnd (.ident "a") (.ident "b"))
#guard chk (.binary .bitOr (.lit (.decimal (some 4) 3)) (.ident "x"))
#guard chk (.binary .bitXor (.binary .add (.ident "p") (.ident "q"))
                            (.binary .mul (.ident "r") (.ident "s")))
#guard chk (.ternary (.ident "c") (.ident "t") (.ident "f"))


/- ------------------------------------------------------------------ -/
/- M2 calibration: the first NON-1:1 case.

   The emitter prints `.op .not [x]` as `w'(x ^ w'(2^w-1))`, and the
   lowerer turns each size cast into `slice (concat [0_w, ·]) (w-1) 0` —
   so the roundtrip of a NOT is not syntactic identity but the IR
   expression `notEncode` below.  This lemma proves the encoding is
   SEMANTICALLY the NOT, which is the shape every non-1:1 case of the
   full roundtrip theorem will take. -/

open Sparkle.IR.Semantics in
/-- The image of `.op .not [x]` under emit-then-lower. -/
def notEncode (x : Sparkle.IR.AST.Expr) (w : Nat) : Sparkle.IR.AST.Expr :=
  .slice (.concat [.const 0 w,
    .op .xor [x,
      .slice (.concat [.const 0 w, .const (Int.ofNat (2 ^ w - 1)) 32]) (w - 1) 0]])
    (w - 1) 0

/- The `w ≤ 32` hypothesis below is not an artifact: it flushed out a
   real width-annotation inconsistency.  `literalToConst` gives every
   BARE literal width 32, so for w > 32 the emitted mask `w'(2^w-1)`
   lowers to `.const (2^w-1) 32` — a value wider than its annotation.
   The executables agree anyway (Int values are carried in full and the
   re-emitter prints the full value: a 40-bit `~d` round-trips to
   `d ^ 40'hffffffffff` and co-sims clean), but the FORMAL semantics
   masks a const to its annotated width, so such IR is outside the
   well-formed fragment.  Resolution belongs to M1/M2: either lowering
   annotates bare literals `max 32 (bits needed)`, or well-formedness
   (const values fit their widths) becomes a standing hypothesis. -/
open Sparkle.IR.Semantics in
theorem notEncode_sem (we : WEnv) (env : Env) (x : Sparkle.IR.AST.Expr) (w : Nat)
    (hw : Sparkle.IR.Semantics.widthOf we x = w)
    (hw32 : w ≤ 32) (hw0 : 0 < w) (v : Nat)
    (hx : evalExpr we env x = some v) :
    evalExpr we env (notEncode x w) = evalExpr we env (.op .not [x]) := by
  have hp : 0 < 2 ^ w := Nat.two_pow_pos w
  have hM32 : 2 ^ w - 1 < 4294967296 := by
    have h32 : (2 : Nat) ^ w ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hw32
    have : (2 : Nat) ^ 32 = 4294967296 := by decide
    omega
  have hw1 : w - 1 + 1 = w := by omega
  have hmm : ∀ a n : Nat, a % n % n = a % n :=
    fun a n => Nat.mod_mod_of_dvd a (Nat.dvd_refl n)
  simp [notEncode, evalExpr, evalList, evalOp, evalExpr.go, widthOf,
    widthOf.go, hx, hw, hw1, mask, hmm,
    Nat.shiftRight_zero, Nat.zero_shiftLeft, Nat.mod_self]
  -- One arithmetic goal remains: the sized-literal encode of 2^w-1
  -- through Int and the 32-bit container reduces to 2^w-1 itself.
  generalize hMdef : 2 ^ w - 1 = M at hM32 ⊢
  have hMw : M % 2 ^ w = M := Nat.mod_eq_of_lt (by omega)
  have hInt : ((M : Int) % 4294967296).toNat = M := by omega
  simp [hInt, Nat.mod_eq_of_lt hM32, hMw, hmm]

/- ------------------------------------------------------------------ -/
/- M2, expression layer: the SEMANTIC roundtrip theorem, against the
   REAL `emitAstExpr` (the M0 artifact), for a fragment closing over
   refs, fitting constants, the 1:1 binaries, mux — and NOT, the first
   normalizing case, discharged via `notEncode_sem`.

   Statement shape: emit-then-lower yields SOME expression e' that
   (a) has the same semantic width and (b) the same value as e.  Width
   preservation must ride in the induction motive: `evalOp` masks by
   the CONTEXT width (max of argument widths), so a rewritten child
   with a different width would change the parent's meaning even with
   equal values. -/

open Tools.SVParser.EmitAst

/- Total lowering twin, extended to the images `emitAstExpr` produces:
   bare (width-`none`) decimals lower at 32 bits, and a size cast
   expands to `slice (concat [0_w, ·]) (w-1) 0` — both verbatim from
   the shipping `literalToConst` / `lowerExpr`; slice/concat/unary-neg
   are the 1:1 shipping equations. -/
mutual
/-- See the section comment. -/
def lowerT : SVExpr → Option Sparkle.IR.AST.Expr
  | .lit (.decimal (some w) v) => some (.const (Int.ofNat v) w)
  | .lit (.decimal none v) => some (.const (Int.ofNat v) 32)
  | .ident name => some (.ref name)
  | .sizeCast w a => do
    some (.slice (.concat [.const 0 w, ← lowerT a]) (w - 1) 0)
  | .unary .neg a => do some (.op .neg [← lowerT a])
  | .slice e hi lo => do some (.slice (← lowerT e) hi lo)
  | .concat args => do some (.concat (← lowerTList args))
  | .binary .bitAnd a b => do some (.op .and [← lowerT a, ← lowerT b])
  | .binary .bitOr  a b => do some (.op .or  [← lowerT a, ← lowerT b])
  | .binary .bitXor a b => do some (.op .xor [← lowerT a, ← lowerT b])
  | .binary .add    a b => do some (.op .add [← lowerT a, ← lowerT b])
  | .binary .sub    a b => do some (.op .sub [← lowerT a, ← lowerT b])
  | .binary .mul    a b => do some (.op .mul [← lowerT a, ← lowerT b])
  | .binary .eq     a b => do some (.op .eq  [← lowerT a, ← lowerT b])
  | .binary .lt     a b => do some (.op .lt_u [← lowerT a, ← lowerT b])
  | .binary .le     a b => do some (.op .le_u [← lowerT a, ← lowerT b])
  | .binary .gt     a b => do some (.op .gt_u [← lowerT a, ← lowerT b])
  | .binary .ge     a b => do some (.op .ge_u [← lowerT a, ← lowerT b])
  | .binary .shl    a b => do some (.op .shl [← lowerT a, ← lowerT b])
  | .binary .shr    a b => do some (.op .shr [← lowerT a, ← lowerT b])
  | .ternary c t f => do
    some (.op .mux [← lowerT c, ← lowerT t, ← lowerT f])
  | _ => none

def lowerTList : List SVExpr → Option (List Sparkle.IR.AST.Expr)
  | [] => some []
  | a :: rest => do some ((← lowerT a) :: (← lowerTList rest))
end

-- Tie the new arms to the shipping lowerExpr.
#guard (lowerT (.lit (.decimal none 63)) == some (lowerExpr (.lit (.decimal none 63))))
#guard (lowerT (.sizeCast 6 (.ident "x")) == some (lowerExpr (.sizeCast 6 (.ident "x"))))
#guard (lowerT (.binary .sub (.ident "a") (.ident "b"))
        == some (lowerExpr (.binary .sub (.ident "a") (.ident "b"))))
#guard (lowerT (.binary .shr (.ident "a") (.ident "b"))
        == some (lowerExpr (.binary .shr (.ident "a") (.ident "b"))))
#guard (lowerT (.binary .eq (.ident "a") (.ident "b"))
        == some (lowerExpr (.binary .eq (.ident "a") (.ident "b"))))
#guard (lowerT (.unary .neg (.ident "a")) == some (lowerExpr (.unary .neg (.ident "a"))))
#guard (lowerT (.slice (.ident "a") 3 1) == some (lowerExpr (.slice (.ident "a") 3 1)))
#guard (lowerT (.concat [.ident "a", .ident "b"])
        == some (lowerExpr (.concat [.ident "a", .ident "b"])))

open Sparkle.IR.Semantics in
/-- The image of a slice-of-COMPOUND under emit-then-lower (`n'(E)` for
    `lo = 0`, `n'((E) >> lo)` otherwise, then size-cast expansion).
    Semantically the original slice — near-definitional because the
    concat combiner already masks each element to its width. -/
theorem sliceEncode_sem (we : WEnv) (env : Env) (x : Sparkle.IR.AST.Expr)
    (hi lo : Nat) (hlo : lo ≤ hi)
    -- the slice must lie within its operand (the proof needs the concat
    -- combiner's element mask `% 2^widthOf x` to be absorbed by the
    -- slice's own `% 2^(hi+1)`), and lo must fit the 32-bit literal
    (hwid : hi < Sparkle.IR.Semantics.widthOf we x)
    (hhi : hi < 4294967296) (v : Nat)
    (hx : evalExpr we env x = some v) :
    evalExpr we env
      (.slice (.concat [.const 0 (hi + 1 - lo),
        if lo == 0 then x else .op .shr [x, .const (Int.ofNat lo) 32]])
        (hi + 1 - lo - 1) 0)
      = evalExpr we env (.slice x hi lo) := by
  have hn : hi + 1 - lo - 1 + 1 = hi + 1 - lo := by omega
  have hmm : ∀ a n : Nat, a % n % n = a % n :=
    fun a n => Nat.mod_mod_of_dvd a (Nat.dvd_refl n)
  have hdvd : ∀ a b : Nat, a ≤ b → ∀ v : Nat, v % 2 ^ b % 2 ^ a = v % 2 ^ a :=
    fun a b hab v => Nat.mod_mod_of_dvd v (Nat.pow_dvd_pow 2 hab)
  by_cases h0 : lo = 0
  · subst h0
    simp [evalExpr, evalList, evalOp, evalExpr.go, widthOf, widthOf.go,
      hx, hn, mask, hmm, Nat.shiftRight_zero, Nat.zero_shiftLeft,
      Nat.mod_self, hdvd (hi + 1) (Sparkle.IR.Semantics.widthOf we x)
        (by omega)]
  · have hne : (lo == 0) = false := by simp [h0]
    have hlo32 : ((lo : Int) % 4294967296).toNat % 4294967296 = lo := by
      omega
    simp [hne, evalExpr, evalList, evalOp, evalExpr.go, widthOf, widthOf.go,
      hx, hn, mask, hmm, Nat.shiftRight_zero, Nat.zero_shiftLeft,
      Nat.mod_self, hlo32,
      hdvd (hi + 1 - lo) (max (Sparkle.IR.Semantics.widthOf we x) 32)
        (by omega),
      show hi - lo + 1 = hi + 1 - lo from by omega]

open Sparkle.IR.Semantics in
/-- The semantic fragment (see `roundtrip_sem`). -/
inductive SFrag (wof : String → Option Nat) (we : WEnv) (env : Env) :
    Sparkle.IR.AST.Expr → Prop
  | ref (n : String) (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n)) : SFrag wof we env (.ref n)
  | const (v : Int) (w : Nat) (h0 : 0 ≤ v) (hw : 0 < w) :
      SFrag wof we env (.const v w)
  | binop (op : Sparkle.IR.AST.Operator) {a b}
      (hop : (binOpOf op).isSome)
      (ha : SFrag wof we env a) (hb : SFrag wof we env b) :
      SFrag wof we env (.op op [a, b])
  | mux {c t f} (hc : SFrag wof we env c) (ht : SFrag wof we env t)
      (hf : SFrag wof we env f) : SFrag wof we env (.op .mux [c, t, f])
  | neg {x} (hx : SFrag wof we env x) : SFrag wof we env (.op .neg [x])
  | not {x} (w : Nat)
      (hwT : EmitAst.exprWidthT wof x = some w)
      (hwS : Sparkle.IR.Semantics.widthOf we x = w)
      (hw32 : w ≤ 32) (hw0 : 0 < w)
      (hx : SFrag wof we env x) : SFrag wof we env (.op .not [x])
  | sliceRefKeep (n : String) (hi lo : Nat)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      -- the shipping elision does NOT fire: either an unknown width, or
      -- lo ≠ 0, or a strictly partial select
      (hkeep : wof n = none ∨ ¬(lo = 0 ∧ we n ≤ hi + 1))
      (hw : wof n = none ∨ wof n = some (we n)) :
      SFrag wof we env (.slice (.ref n) hi lo)
  | sliceRefElide (n : String) (hi : Nat)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n))
      -- EXACT full-width select only: `hi + 1 > width` also elides in the
      -- shipping emitter but SHRINKS the expression's width, which can
      -- shift sibling layout in a concat — deliberately outside the
      -- fragment (recorded as a suspect to test).
      (hexact : hi + 1 = we n)
      (henv : env n < 2 ^ we n) :
      SFrag wof we env (.slice (.ref n) hi 0)
  | sliceCompound {x} (hi lo : Nat) (hlo : lo ≤ hi)
      (hwid : hi < Sparkle.IR.Semantics.widthOf we x)
      (hhi : hi < 4294967296)
      (hcomp : ∀ n, x ≠ .ref n)
      (hx : SFrag wof we env x) : SFrag wof we env (.slice x hi lo)

open Sparkle.IR.Semantics in
set_option maxHeartbeats 3200000 in
/-- **The semantic roundtrip theorem** (expression layer, fragment):
    emitting through the real `emitAstExpr` and lowering back yields an
    expression with the SAME width and the SAME value. -/
theorem roundtrip_sem {wof : String → Option Nat} {we : WEnv} {env : Env}
    {e : Sparkle.IR.AST.Expr} (h : SFrag wof we env e) :
    ∃ e', (emitAstExpr wof e).bind lowerT = some e'
      ∧ Sparkle.IR.Semantics.widthOf we e' = Sparkle.IR.Semantics.widthOf we e
      ∧ evalExpr we env e' = evalExpr we env e := by
  induction h with
  | ref n hs hw =>
    exact ⟨.ref n, by simp [emitAstExpr, hs, lowerT], rfl, rfl⟩
  | const v w h0 hw =>
    refine ⟨.const v w, ?_, rfl, rfl⟩
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    have hnl : ¬ v < 0 := by omega
    simp [emitAstExpr, hne, if_neg hnl, lowerT, Int.toNat_of_nonneg h0]
  | binop op hop ha hb iha ihb =>
    rename_i a b
    obtain ⟨a', hea, hwa, hva⟩ := iha
    obtain ⟨b', heb, hwb, hvb⟩ := ihb
    obtain ⟨ea, hea1, hea2⟩ := Option.bind_eq_some_iff.mp hea
    obtain ⟨eb, heb1, heb2⟩ := Option.bind_eq_some_iff.mp heb
    obtain ⟨sop, hsop⟩ := Option.isSome_iff_exists.mp hop
    refine ⟨.op op [a', b'], ?_, ?_, ?_⟩
    · cases op <;> simp only [binOpOf] at hsop <;> cases hsop <;>
        simp_all [emitAstExpr, lowerT, binOpOf]
    · cases op <;> simp_all [Sparkle.IR.Semantics.widthOf, binOpOf]
    · cases hA : evalExpr we env a <;> cases hB : evalExpr we env b <;>
        cases op <;> simp only [binOpOf] at hsop <;> cases hsop <;>
        simp_all [evalExpr, evalList, evalOp, Sparkle.IR.Semantics.widthOf,
          binOpOf]
  | mux hc ht hf ihc iht ihf =>
    rename_i c t f
    obtain ⟨c', hec, hwc, hvc⟩ := ihc
    obtain ⟨t', het, hwt, hvt⟩ := iht
    obtain ⟨f', hef, hwf, hvf⟩ := ihf
    obtain ⟨ec, hec1, hec2⟩ := Option.bind_eq_some_iff.mp hec
    obtain ⟨et, het1, het2⟩ := Option.bind_eq_some_iff.mp het
    obtain ⟨ef, hef1, hef2⟩ := Option.bind_eq_some_iff.mp hef
    refine ⟨.op .mux [c', t', f'], ?_, ?_, ?_⟩
    · simp_all [emitAstExpr, lowerT]
    · simp_all [Sparkle.IR.Semantics.widthOf]
    · cases hC : evalExpr we env c <;> cases hT : evalExpr we env t <;>
        cases hF : evalExpr we env f <;>
        simp_all [evalExpr, evalList, evalOp, Sparkle.IR.Semantics.widthOf]
  | neg hx ih =>
    rename_i x
    obtain ⟨x', hex, hwx, hvx⟩ := ih
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hex
    refine ⟨.op .neg [x'], ?_, ?_, ?_⟩
    · simp_all [emitAstExpr, lowerT]
    · simp_all [Sparkle.IR.Semantics.widthOf]
    · cases hX : evalExpr we env x <;>
        simp_all [evalExpr, evalList, evalOp, Sparkle.IR.Semantics.widthOf]
  | not w hwT hwS hw32 hw0 hx ih =>
    rename_i x
    obtain ⟨x', hex, hwx, hvx⟩ := ih
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hex
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    refine ⟨notEncode x' w, ?_, ?_, ?_⟩
    · simp [emitAstExpr, hex1, hwT, hne, lowerT, hex2, notEncode]
    · simp [notEncode, Sparkle.IR.Semantics.widthOf]; omega
    · cases hval : evalExpr we env x with
      | none =>
        have hval' : evalExpr we env x' = none := by rw [hvx, hval]
        rw [show evalExpr we env (.op .not [x])
              = ((evalList we env [x]).bind fun vals =>
                  evalOp we .not [x] vals
                    (Sparkle.IR.Semantics.widthOf we (.op .not [x]))) from rfl]
        simp only [evalList, hval, Option.bind_eq_bind]
        simp [notEncode, evalExpr, evalList, hval']
      | some v =>
        have hval' : evalExpr we env x' = some v := by rw [hvx, hval]
        have := notEncode_sem we env x' w (by rw [hwx, hwS]) hw32 hw0 v hval'
        rw [this]
        simp [evalExpr, evalList, evalOp, hval, hval', hwx]
  | sliceRefKeep n hi lo hs hkeep hw =>
    refine ⟨.slice (.ref n) hi lo, ?_, rfl, rfl⟩
    rcases hw with hw | hw
    · simp [emitAstExpr, hs, hw, lowerT]
    · rcases hkeep with hk | hk
      · rw [hk] at hw; cases hw
      · have hb : (lo == 0 && decide (hi + 1 ≥ we n)) = false := by
          simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne,
            decide_eq_false_iff_not]
          omega
        simp [emitAstExpr, hs, hw, hb, lowerT]
  | sliceRefElide n hi hs hw hexact henv =>
    refine ⟨.ref n, ?_, ?_, ?_⟩
    · have hb : ((0 : Nat) == 0 && decide (hi + 1 ≥ we n)) = true := by
        have : hi + 1 ≥ we n := Nat.le_of_eq hexact.symm
        simp [this]
      simp only [emitAstExpr, hs, hw, hb, if_true]
      simp [lowerT]
    · simp only [Sparkle.IR.Semantics.widthOf, Nat.sub_zero]; omega
    · simp [evalExpr, mask, Nat.sub_zero, hexact, Nat.mod_eq_of_lt henv]
  | sliceCompound hi lo hlo hwid hhi hcomp hx ih =>
    rename_i x
    obtain ⟨x', hex, hwx, hvx⟩ := ih
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hex
    cases hval : evalExpr we env x with
    | none =>
      have hval' : evalExpr we env x' = none := by rw [hvx, hval]
      refine ⟨.slice (.concat [.const 0 (hi + 1 - lo),
        if lo == 0 then x' else .op .shr [x', .const (Int.ofNat lo) 32]])
        (hi + 1 - lo - 1) 0, ?_, ?_, ?_⟩
      · cases x <;> simp_all [emitAstExpr, lowerT] <;>
          first
            | (exact absurd rfl (hcomp _))
            | (by_cases h0 : lo = 0 <;> simp_all [lowerT])
      · simp [Sparkle.IR.Semantics.widthOf]; omega
      · by_cases h0 : lo = 0 <;>
          simp_all [evalExpr, evalList, evalOp, evalExpr.go]
    | some v =>
      have hval' : evalExpr we env x' = some v := by rw [hvx, hval]
      refine ⟨.slice (.concat [.const 0 (hi + 1 - lo),
        if lo == 0 then x' else .op .shr [x', .const (Int.ofNat lo) 32]])
        (hi + 1 - lo - 1) 0, ?_, ?_, ?_⟩
      · cases x <;> simp_all [emitAstExpr, lowerT] <;>
          first
            | (exact absurd rfl (hcomp _))
            | (by_cases h0 : lo = 0 <;> simp_all [lowerT])
      · simp [Sparkle.IR.Semantics.widthOf]; omega
      · rw [sliceEncode_sem we env x' hi lo hlo (by rw [hwx]; omega) hhi v hval']
        simp [evalExpr, hvx]

end Tools.SVParser.RoundtripProof
