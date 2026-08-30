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
import Sparkle.IR.ReorderInvariance
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
    .op .xor [x, .const (Int.ofNat (2 ^ w - 1)) w]])
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
  have hw1 : w - 1 + 1 = w := by omega
  have hmm : ∀ a n : Nat, a % n % n = a % n :=
    fun a n => Nat.mod_mod_of_dvd a (Nat.dvd_refl n)
  simp [notEncode, evalExpr, evalList, evalOp, evalExpr.go, widthOf,
    hx, hw, hw1, mask, hmm,
    Nat.shiftRight_zero, Nat.zero_shiftLeft]
  -- residue: the Int-encode of the sized mask literal is 2^w-1 itself
  have hcast : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by push_cast; rfl
  rw [hcast]
  generalize (2 : Nat) ^ w = P at hp ⊢
  have hMe : (((P - 1 : Nat) : Int) % ((P : Nat) : Int)).toNat % P = P - 1 := by
    have h1 : ((P - 1 : Nat) : Int) % ((P : Nat) : Int) = ((P - 1 : Nat) : Int) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [h1, Int.toNat_natCast]
    omega
  rw [hMe]

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
  | .lit (.hex (some w) v) => some (.const (Int.ofNat v) w)
  | .ident name => some (.ref name)
  | .sizeCast w a => do
    some (.slice (.concat [.const 0 w, ← lowerT a]) (w - 1) 0)
  | .unary .neg a => do some (.op .neg [← lowerT a])
  -- NOTE: no `.unary .bitNot` arm.  The emitter's width-UNKNOWN NOT
  -- (`~x`) lowers on the shipping side to `xor(x, -1, 32)` and is then
  -- rewritten by the width-inference pass `narrowMaskConstants` to
  -- `xor(x, -1, w)` — mirroring that needs the width ENVIRONMENT and a
  -- semantic narrowing lemma (the standing Bool-not finding), so those
  -- statements stay outside the twin for now (Test 68 counts them as
  -- outside-the-fragment).
  | .unary .signed a => lowerT a
  | .binary .asr a b => do some (.op .asr [← lowerT a, ← lowerT b])
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
#guard (lowerT (.lit (.hex (some 8) 255)) == some (lowerExpr (.lit (.hex (some 8) 255))))
#guard (lowerT (.unary .signed (.ident "a")) == some (lowerExpr (.unary .signed (.ident "a"))))
#guard (lowerT (.binary .asr (.unary .signed (.ident "a")) (.unary .signed (.ident "b")))
        == some (lowerExpr (.binary .asr (.unary .signed (.ident "a")) (.unary .signed (.ident "b")))))
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
/-- Head/tail decomposition of concat evaluation (the head stays an
    opaque `evalExpr` application, so hypotheses about it keep
    rewriting after the unfold). -/
theorem eval_concat_cons (we : WEnv) (env : Env)
    (x : Sparkle.IR.AST.Expr) (xs : List Sparkle.IR.AST.Expr) :
    evalExpr we env (.concat (x :: xs))
      = (evalExpr we env x).bind fun v =>
          (evalList we env xs).bind fun vs =>
            some (evalExpr.go we (x :: xs) (v :: vs)) := by
  simp only [evalExpr, evalList, Option.bind_eq_bind]
  cases evalExpr we env x <;>
    cases hxs : evalList we env xs <;> simp [hxs]

open Sparkle.IR.Semantics in
/-- Evaluation of a lowered size cast `w'(x)` whose operand has exactly
    width `w`: the identity mask. -/
theorem castEncode_sem (we : WEnv) (env : Env) (x : Sparkle.IR.AST.Expr)
    (w : Nat) (hwx : Sparkle.IR.Semantics.widthOf we x = w) (hw0 : 0 < w)
    (v : Nat) (hx : evalExpr we env x = some v) :
    evalExpr we env (.slice (.concat [.const 0 w, x]) (w - 1) 0)
      = some (mask w v) := by
  have hn : w - 1 + 1 = w := by omega
  have hmm : ∀ a n : Nat, a % n % n = a % n :=
    fun a n => Nat.mod_mod_of_dvd a (Nat.dvd_refl n)
  simp [evalExpr, evalList, evalOp, evalExpr.go, widthOf, widthOf.go,
    hx, hwx, hn, mask, hmm, Nat.shiftRight_zero, Nat.zero_shiftLeft,
    Nat.mod_self]

open Sparkle.IR.Semantics in
theorem evalList_length {we env} : ∀ {args : List Sparkle.IR.AST.Expr}
    {vs : List Nat}, evalList we env args = some vs → vs.length = args.length
  | [], vs, h => by simp [evalList] at h; simp [← h]
  | a :: rest, vs, h => by
    simp only [evalList, Option.bind_eq_bind] at h
    cases hA : evalExpr we env a with
    | none => rw [hA] at h; simp at h
    | some v =>
      rw [hA] at h
      cases hR : evalList we env rest with
      | none => rw [hR] at h; simp at h
      | some vs' =>
        rw [hR] at h
        simp only [Option.bind_some] at h
        cases h
        simp [evalList_length hR]

open Sparkle.IR.Semantics in
/-- The concat combiner's running offset (a zip-fold over widths) is the
    plain width sum whenever the value list is long enough. -/
theorem restW_eq (we : WEnv) : ∀ (as : List Sparkle.IR.AST.Expr)
    (vs : List Nat), as.length ≤ vs.length →
    ((as.zip vs).foldl (fun acc (p : Sparkle.IR.AST.Expr × Nat) =>
        acc + Sparkle.IR.Semantics.widthOf we p.1) 0)
      = Sparkle.IR.Semantics.widthOf.go we as := by
  -- foldl with a running accumulator: generalize it first.
  suffices h : ∀ (as : List Sparkle.IR.AST.Expr) (vs : List Nat), as.length ≤ vs.length →
      ∀ acc, ((as.zip vs).foldl (fun a (p : Sparkle.IR.AST.Expr × Nat) =>
          a + Sparkle.IR.Semantics.widthOf we p.1) acc)
        = acc + Sparkle.IR.Semantics.widthOf.go we as by
    intro as vs hlen
    simpa using h as vs hlen 0
  intro as
  induction as with
  | nil => intro vs _ acc; simp [Sparkle.IR.Semantics.widthOf.go]
  | cons a rest ih =>
    intro vs hlen acc
    cases vs with
    | nil => simp at hlen
    | cons v vs' =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih vs' (by simpa using hlen)]
      simp [Sparkle.IR.Semantics.widthOf.go]
      omega

/-- Flipping the sign bit, arithmetically: for `v < 2^w`, XOR with the
    top bit adds it below the midpoint and subtracts it above.  Proven by
    div/mod decomposition at the bit boundary (`xor_div_two_pow` /
    `xor_mod_two_pow`), with the quotient confined to {0,1}. -/
theorem xor_top_bit (w : Nat) (hw0 : 0 < w) (v : Nat) (hv : v < 2 ^ w) :
    v ^^^ 2 ^ (w - 1)
      = if v < 2 ^ (w - 1) then v + 2 ^ (w - 1) else v - 2 ^ (w - 1) := by
  have h2 : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
    have : w - 1 + 1 = w := by omega
    calc 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ (w - 1) * 2 := by omega
    _ = 2 ^ (w - 1 + 1) := (Nat.pow_succ 2 (w - 1)).symm
    _ = 2 ^ w := by rw [this]
  have hpos : 0 < 2 ^ (w - 1) := Nat.two_pow_pos (w - 1)
  have hdm := Nat.div_add_mod (v ^^^ 2 ^ (w - 1)) (2 ^ (w - 1))
  have hmod : (v ^^^ 2 ^ (w - 1)) % 2 ^ (w - 1) = v % 2 ^ (w - 1) := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  have hdiv : (v ^^^ 2 ^ (w - 1)) / 2 ^ (w - 1) = v / 2 ^ (w - 1) ^^^ 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self hpos]
  have hq : v / 2 ^ (w - 1) = 0 ∨ v / 2 ^ (w - 1) = 1 := by
    have h3 : v / 2 ^ (w - 1) < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_two]
      omega
    -- (`omega` treats division by a non-constant as an opaque atom and
    -- loses the connection; discharge by direct case analysis instead)
    match h : v / 2 ^ (w - 1), h3 with
    | 0, _ => exact Or.inl rfl
    | 1, _ => exact Or.inr rfl
  have hvdm := Nat.div_add_mod v (2 ^ (w - 1))
  have hvm : v % 2 ^ (w - 1) < 2 ^ (w - 1) := Nat.mod_lt _ hpos
  rw [hdiv, hmod] at hdm
  rcases hq with hq | hq
  · have h1 : v / 2 ^ (w - 1) ^^^ 1 = 1 := by rw [hq]; rfl
    rw [hq] at hvdm
    rw [h1] at hdm
    have hlt : v < 2 ^ (w - 1) := by omega
    rw [if_pos hlt]
    omega
  · have h1 : v / 2 ^ (w - 1) ^^^ 1 = 0 := by rw [hq]; rfl
    rw [hq] at hvdm
    rw [h1] at hdm
    have hge : ¬ v < 2 ^ (w - 1) := by omega
    rw [if_neg hge]
    omega

open Sparkle.IR.Semantics in
/-- The bias encoding of signed comparison: XOR-ing the sign bit into
    both operands turns two's-complement order into unsigned order. -/
theorem bias_lt (w : Nat) (hw0 : 0 < w) (va vb : Nat)
    (ha : va < 2 ^ w) (hb : vb < 2 ^ w) :
    ((va ^^^ 2 ^ (w - 1)) < (vb ^^^ 2 ^ (w - 1)))
      ↔ (toSigned w va < toSigned w vb) := by
  have h2 : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
    have hww : w - 1 + 1 = w := by omega
    calc 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ (w - 1) * 2 := by omega
    _ = 2 ^ (w - 1 + 1) := (Nat.pow_succ 2 (w - 1)).symm
    _ = 2 ^ w := by rw [hww]
  rw [xor_top_bit w hw0 va ha, xor_top_bit w hw0 vb hb]
  unfold toSigned
  -- keep the two powers as LINKED Nat atoms (omega loses the h+h=g
  -- relation once casts turn one of them into an Int power)
  generalize hh : 2 ^ (w - 1) = hb2 at *
  generalize hg : 2 ^ w = g at *
  by_cases hva : va < hb2 <;> by_cases hvb : vb < hb2 <;>
    simp [hva, hvb] <;> omega

open Sparkle.IR.Semantics in
theorem bias_le (w : Nat) (hw0 : 0 < w) (va vb : Nat)
    (ha : va < 2 ^ w) (hb : vb < 2 ^ w) :
    ((va ^^^ 2 ^ (w - 1)) ≤ (vb ^^^ 2 ^ (w - 1)))
      ↔ (toSigned w va ≤ toSigned w vb) := by
  have h2 : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
    have hww : w - 1 + 1 = w := by omega
    calc 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ (w - 1) * 2 := by omega
    _ = 2 ^ (w - 1 + 1) := (Nat.pow_succ 2 (w - 1)).symm
    _ = 2 ^ w := by rw [hww]
  rw [xor_top_bit w hw0 va ha, xor_top_bit w hw0 vb hb]
  unfold toSigned
  generalize hh : 2 ^ (w - 1) = hb2 at *
  generalize hg : 2 ^ w = g at *
  by_cases hva : va < hb2 <;> by_cases hvb : vb < hb2 <;>
    simp [hva, hvb] <;> omega

theorem encodeConst_lt (v : Int) (w : Nat) (hw : 0 < w) :
    Tools.SVParser.EmitAst.encodeConst v w < 2 ^ w := by
  unfold Tools.SVParser.EmitAst.encodeConst
  have hg : (0 : Int) < ((2 ^ w : Nat) : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  have h1 := Int.emod_lt_of_pos (v % ((2 ^ w : Nat) : Int) + ((2 ^ w : Nat) : Int)) hg
  have h2 := Int.emod_nonneg (v % ((2 ^ w : Nat) : Int) + ((2 ^ w : Nat) : Int))
    (by omega : ((2 ^ w : Nat) : Int) ≠ 0)
  omega

open Sparkle.IR.Semantics in
/-- Any constant evaluates to its two's-complement encode. -/
theorem eval_const_encode (we : WEnv) (env : Env) (v : Int) (w : Nat) :
    evalExpr we env (.const v w) = some (mask w (Tools.SVParser.EmitAst.encodeConst v w)) := by
  simp [evalExpr, Tools.SVParser.EmitAst.encodeConst]

open Sparkle.IR.Semantics in
/-- A fitting non-negative constant evaluates to itself. -/
theorem eval_const_ofNat (we : WEnv) (env : Env) (v w : Nat)
    (h : v < 2 ^ w) :
    evalExpr we env (.const (Int.ofNat v) w) = some v := by
  simp only [evalExpr, mask]
  have h1 : Int.ofNat v % ((2 ^ w : Nat) : Int) = Int.ofNat v :=
    Int.emod_eq_of_lt (Int.ofNat_nonneg _) (by exact Int.ofNat_lt.mpr h)
  have h2 : (Int.ofNat v + ((2 ^ w : Nat) : Int)) % ((2 ^ w : Nat) : Int)
      = Int.ofNat v % ((2 ^ w : Nat) : Int) := Int.add_emod_right _ _
  rw [h1, h2, h1]
  simp [Nat.mod_eq_of_lt h]

open Sparkle.IR.Semantics in
/-- Two-operand decomposition of op evaluation with OPAQUE operand
    evaluations (same rationale as `eval_concat_cons`). -/
theorem eval_binop_pair (we : WEnv) (env : Env)
    (op : Sparkle.IR.AST.Operator) (x y : Sparkle.IR.AST.Expr) :
    evalExpr we env (.op op [x, y])
      = (evalExpr we env x).bind fun vx =>
          (evalExpr we env y).bind fun vy =>
            evalOp we op [x, y] [vx, vy]
              (Sparkle.IR.Semantics.widthOf we (.op op [x, y])) := by
  simp only [evalExpr, evalList, Option.bind_eq_bind]
  cases evalExpr we env x <;> cases evalExpr we env y <;> simp

open Sparkle.IR.Semantics in
/-- Three-operand mux decomposition with opaque part evaluations
    (`evalOp` for mux ignores the context width, so the result form is
    baked in). -/
theorem eval_mux3 (we : WEnv) (env : Env) (c t f : Sparkle.IR.AST.Expr) :
    evalExpr we env (.op .mux [c, t, f])
      = (evalExpr we env c).bind fun vc =>
          (evalExpr we env t).bind fun vt =>
            (evalExpr we env f).bind fun vf =>
              some (if vc ≠ 0 then vt else vf) := by
  simp only [evalExpr, evalList, Option.bind_eq_bind]
  cases evalExpr we env c <;> cases evalExpr we env t <;>
    cases evalExpr we env f <;> simp [evalOp]

open Sparkle.IR.Semantics in
/-- Evaluation of one BIASED operand of the emitted signed compare:
    `(z & (2^w-1)) ^ 2^(w-1)` computes the sign-bit flip. -/
theorem biasOperand_sem (we : WEnv) (env : Env) (z : Sparkle.IR.AST.Expr)
    (w : Nat) (hw0 : 0 < w) (hwz : Sparkle.IR.Semantics.widthOf we z = w)
    (v : Nat) (hv : v < 2 ^ w) (hz : evalExpr we env z = some v) :
    evalExpr we env
      (.op .xor [.op .and [z, .const (Int.ofNat (2 ^ w - 1)) w],
                 .const (Int.ofNat (2 ^ (w - 1))) w])
      = some (v ^^^ 2 ^ (w - 1)) := by
  have hM : 2 ^ w - 1 < 2 ^ w := by
    have := Nat.two_pow_pos w; omega
  have hSB : 2 ^ (w - 1) < 2 ^ w :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hxor : v ^^^ 2 ^ (w - 1) < 2 ^ w :=
    Nat.xor_lt_two_pow hv hSB
  have hMc := eval_const_ofNat we env (2 ^ w - 1) w hM
  have hSBc := eval_const_ofNat we env (2 ^ (w - 1)) w hSB
  rw [eval_binop_pair we env .xor
        (.op .and [z, .const (Int.ofNat (2 ^ w - 1)) w])
        (.const (Int.ofNat (2 ^ (w - 1))) w),
      eval_binop_pair we env .and z (.const (Int.ofNat (2 ^ w - 1)) w),
      hz, hMc, hSBc]
  simp [evalOp, Sparkle.IR.Semantics.widthOf, hwz, Nat.max_self, mask,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt hxor]

open Sparkle.IR.Semantics in
/-- The semantic fragment (see `roundtrip_sem`). -/
inductive SFrag (wof : String → Option Nat) (we : WEnv) (env : Env) :
    Sparkle.IR.AST.Expr → Prop
  | ref (n : String) (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n)) : SFrag wof we env (.ref n)
  | const (v : Int) (w : Nat) (hw : 0 < w) :
      SFrag wof we env (.const v w)
  | binop (op : Sparkle.IR.AST.Operator) {a b}
      (hop : (binOpOf op).isSome)
      (ha : SFrag wof we env a) (hb : SFrag wof we env b) :
      SFrag wof we env (.op op [a, b])
  | mux {c t f}
      -- the arms agree in width: `evalOp` passes the selected arm
      -- through UNMASKED while `widthOf` reports the then-arm's width,
      -- so a wider else-arm would break value boundedness
      (hwf : Sparkle.IR.Semantics.widthOf we f
        = Sparkle.IR.Semantics.widthOf we t)
      (hc : SFrag wof we env c) (ht : SFrag wof we env t)
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
      -- and the select is IN RANGE, so the part-select arm fires (an
      -- over-wide select emits its zero-extension as a cast instead)
      (hin : wof n = none ∨ hi < we n)
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
  | concatNil : SFrag wof we env (.concat [])
  | concatCons {a rest}
      -- op-typed elements get a size cast on emission; its width must be
      -- the element's semantic width for the cast to be an identity
      (hopw : ∀ o as, a = Sparkle.IR.AST.Expr.op o as →
          ∃ w, EmitAst.exprWidthT wof a = some w ∧ 0 < w ∧
            Sparkle.IR.Semantics.widthOf we a = w)
      (ha : SFrag wof we env a)
      (hrest : SFrag wof we env (.concat rest)) :
      SFrag wof we env (.concat (a :: rest))
  | asr {x y}
      -- concat operands take the sign-extend ENCODE branch of the
      -- shipping `$signed` lowering; everything else passes through
      (hncx : ∀ l, x ≠ .concat l) (hncy : ∀ l, y ≠ .concat l)
      (hx : SFrag wof we env x) (hy : SFrag wof we env y) :
      SFrag wof we env (.op .asr [x, y])
  | cmpS (op : Sparkle.IR.AST.Operator)
      (hop : op = .lt_s ∨ op = .le_s ∨ op = .gt_s ∨ op = .ge_s)
      {x y} (w : Nat)
      (hwTx : EmitAst.exprWidthT wof x = some w)
      (hwTy : EmitAst.exprWidthT wof y = some w)
      (hwSx : Sparkle.IR.Semantics.widthOf we x = w)
      (hwSy : Sparkle.IR.Semantics.widthOf we y = w)
      (hw0 : 0 < w)
      (hbx : ∀ v, evalExpr we env x = some v → v < 2 ^ w)
      (hby : ∀ v, evalExpr we env y = some v → v < 2 ^ w)
      (hx : SFrag wof we env x) (hy : SFrag wof we env y) :
      SFrag wof we env (.op op [x, y])
  | sliceCompound {x} (hi lo : Nat) (hlo : lo ≤ hi)
      (hwid : hi < Sparkle.IR.Semantics.widthOf we x)
      (hhi : hi < 4294967296)
      (hcomp : ∀ n, x ≠ .ref n)
      -- the CANONICAL cast-encode shape `slice (concat [0_w, y]) (w-1) 0`
      -- has its own constructor (castEnc, below — the emitter inverts
      -- it to `w'(y)`); every other slice-of-concat takes the general
      -- compound arm and is covered HERE
      (hncast : ∀ w y, x = .concat [.const 0 w, y] →
        ¬(lo = 0 ∧ hi + 1 = w))
      (hx : SFrag wof we env x) : SFrag wof we env (.slice x hi lo)
  | castEnc {y} (w : Nat) (hw0 : 0 < w)
      (hy : SFrag wof we env y) :
      SFrag wof we env (.slice (.concat [.const 0 w, y]) (w - 1) 0)

open Sparkle.IR.Semantics in
/-- **Value boundedness on the fragment**: under a width-bounded
    environment, every fragment expression evaluates within its width.
    The base fact of the bounded-env refinement — it discharges the
    env-dependent side conditions (signed-compare bounds, exact-elide
    range) from `Bounded` alone. -/
theorem sfrag_eval_bounded {wof : String → Option Nat} {we : WEnv}
    {env : Env} {e : Sparkle.IR.AST.Expr}
    (h : SFrag wof we env e) (hb : Bounded we env) :
    ∀ v, evalExpr we env e = some v → v < 2 ^ widthOf we e := by
  have hmask : ∀ w x, mask w x < 2 ^ w :=
    fun w x => Nat.mod_lt _ (Nat.two_pow_pos w)
  induction h with
  | ref n hs hw =>
    intro v hv
    simp only [evalExpr, Option.some_inj] at hv
    subst hv
    simpa [widthOf] using hb n
  | const cv w hw =>
    intro v hv
    simp only [evalExpr, Option.some_inj] at hv
    subst hv
    simpa [widthOf] using hmask w _
  | binop op hop ha hb' iha ihb =>
    rename_i a b
    intro v hv
    obtain ⟨sop, hsop⟩ := Option.isSome_iff_exists.mp hop
    rw [show evalExpr we env (.op op [a, b])
          = ((evalList we env [a, b]).bind fun vals =>
              evalOp we op [a, b] vals (widthOf we (.op op [a, b])))
        from rfl] at hv
    cases hA : evalExpr we env a with
    | none => simp [evalList, hA] at hv
    | some va =>
    cases hB : evalExpr we env b with
    | none => simp [evalList, hA, hB] at hv
    | some vb =>
    simp only [evalList, hA, hB, Option.bind_some, Option.bind_eq_bind] at hv
    cases op <;> simp only [binOpOf] at hsop <;> cases hsop <;>
      simp only [evalOp, Option.some_inj] at hv <;> subst hv <;>
      first
        | exact hmask _ _
        | (split <;> simp [widthOf])
        | -- shr: unmasked, but bounded by its left operand
          (have h1 : va >>> vb ≤ va := by
            rw [Nat.shiftRight_eq_div_pow]
            exact Nat.div_le_self _ _
           have h2 : va < 2 ^ widthOf we a := iha va hA
           have h3 : (2 : Nat) ^ widthOf we a
               ≤ 2 ^ widthOf we (.op .shr [a, b]) := by
             apply Nat.pow_le_pow_right (by omega)
             simp only [widthOf]
             omega
           omega)
  | mux hwfw hc ht hf ihc iht ihf =>
    rename_i c t f
    intro v hv
    rw [show evalExpr we env (.op .mux [c, t, f])
          = ((evalList we env [c, t, f]).bind fun vals =>
              evalOp we .mux [c, t, f] vals
                (widthOf we (.op .mux [c, t, f]))) from rfl] at hv
    cases hC : evalExpr we env c with
    | none => simp [evalList, hC] at hv
    | some vc =>
    cases hT : evalExpr we env t with
    | none => simp [evalList, hC, hT] at hv
    | some vt =>
    cases hF : evalExpr we env f with
    | none => simp [evalList, hC, hT, hF] at hv
    | some vf =>
    simp only [evalList, hC, hT, hF, Option.bind_some, Option.bind_eq_bind,
      evalOp, Option.some_inj] at hv
    subst hv
    have h1 := iht vt hT
    have h2 := ihf vf hF
    rw [hwfw] at h2
    simp only [widthOf]
    split <;> assumption
  | neg hx ihx =>
    rename_i x
    intro v hv
    rw [show evalExpr we env (.op .neg [x])
          = ((evalList we env [x]).bind fun vals =>
              evalOp we .neg [x] vals (widthOf we (.op .neg [x])))
        from rfl] at hv
    cases hX : evalExpr we env x with
    | none => simp [evalList, hX] at hv
    | some vx =>
    simp only [evalList, hX, Option.bind_some, Option.bind_eq_bind,
      evalOp, Option.some_inj] at hv
    subst hv
    exact hmask _ _
  | not w hwT hwS hw32 hw0 hx ihx =>
    rename_i x
    intro v hv
    rw [show evalExpr we env (.op .not [x])
          = ((evalList we env [x]).bind fun vals =>
              evalOp we .not [x] vals (widthOf we (.op .not [x])))
        from rfl] at hv
    cases hX : evalExpr we env x with
    | none => simp [evalList, hX] at hv
    | some vx =>
    simp only [evalList, hX, Option.bind_some, Option.bind_eq_bind,
      evalOp, Option.some_inj] at hv
    subst hv
    simpa [widthOf] using hmask (widthOf we x) _
  | sliceRefKeep n hi lo hs hkeep hin hw =>
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind, Option.bind_some,
      Option.some_inj] at hv
    subst hv
    simpa [widthOf] using hmask (hi - lo + 1) _
  | sliceRefElide n hi hs hw hexact henv =>
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind, Option.bind_some,
      Option.some_inj] at hv
    subst hv
    simpa [widthOf] using hmask (hi - 0 + 1) _
  | concatNil =>
    intro v hv
    simp only [evalExpr, evalList, Option.bind_eq_bind, Option.bind_some,
      Option.some_inj] at hv
    subst hv
    simp [widthOf, evalExpr.go, widthOf.go]
  | concatCons hopw ha hrest iha ihrest =>
    rename_i a rest
    intro v hv
    rw [show evalExpr we env (.concat (a :: rest))
          = ((evalList we env (a :: rest)).bind fun vals =>
              some (evalExpr.go we (a :: rest) vals)) from rfl] at hv
    cases hA : evalExpr we env a with
    | none => simp [evalList, hA] at hv
    | some va =>
    cases hR : evalList we env rest with
    | none => simp [evalList, hA, hR] at hv
    | some vrest =>
    simp only [evalList, hA, hR, Option.bind_some, Option.bind_eq_bind,
      Option.some_inj] at hv
    subst hv
    have hlen : rest.length ≤ vrest.length := by
      rw [evalList_length hR]
      omega
    have hrw := restW_eq we rest vrest hlen
    have hgo : evalExpr.go we rest vrest < 2 ^ widthOf.go we rest := by
      have := ihrest (evalExpr.go we rest vrest)
        (by simp [evalExpr, evalList, hR])
      simpa [widthOf] using this
    simp only [evalExpr.go, hrw, widthOf, widthOf.go]
    -- (mask wa va) <<< restW ||| go rest < 2^(wa + restW)
    have h1 : (mask (widthOf we a) va) <<< (widthOf.go we rest)
        < 2 ^ (widthOf we a + widthOf.go we rest) := by
      rw [Nat.shiftLeft_eq, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_le (hmask _ _) (Nat.le_refl _)
        (Nat.two_pow_pos _)
    have h2 : evalExpr.go we rest vrest
        < 2 ^ (widthOf we a + widthOf.go we rest) := by
      calc evalExpr.go we rest vrest < 2 ^ widthOf.go we rest := hgo
        _ ≤ 2 ^ (widthOf we a + widthOf.go we rest) :=
          Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.or_lt_two_pow h1 h2
  | asr hncx hncy hx hy ihx ihy =>
    rename_i x y
    intro v hv
    rw [show evalExpr we env (.op .asr [x, y])
          = ((evalList we env [x, y]).bind fun vals =>
              evalOp we .asr [x, y] vals (widthOf we (.op .asr [x, y])))
        from rfl] at hv
    cases hX : evalExpr we env x with
    | none => simp [evalList, hX] at hv
    | some vx =>
    cases hY : evalExpr we env y with
    | none => simp [evalList, hX, hY] at hv
    | some vy =>
    simp only [evalList, hX, hY, Option.bind_some, Option.bind_eq_bind,
      evalOp, Option.some_inj] at hv
    subst hv
    have h1 := hmask (widthOf we x) (Int.toNat
      ((toSigned (widthOf we x) vx >>> vy) % ((2 ^ widthOf we x : Nat) : Int)))
    have h2 : (2 : Nat) ^ widthOf we x
        ≤ 2 ^ widthOf we (.op .asr [x, y]) := by
      apply Nat.pow_le_pow_right (by omega)
      simp only [widthOf]
      omega
    omega
  | cmpS op hop hwTx hwTy hwSx hwSy hw0 hbx hby hx hy ihx ihy =>
    rename_i x y w
    intro v hv
    rcases hop with h | h | h | h <;> subst h <;>
    · rw [show ∀ o, evalExpr we env (.op o [x, y])
            = ((evalList we env [x, y]).bind fun vals =>
                evalOp we o [x, y] vals (widthOf we (.op o [x, y])))
          from fun _ => rfl] at hv
      cases hX : evalExpr we env x with
      | none => simp [evalList, hX] at hv
      | some vx =>
      cases hY : evalExpr we env y with
      | none => simp [evalList, hX, hY] at hv
      | some vy =>
      simp only [evalList, hX, hY, Option.bind_some, Option.bind_eq_bind,
        evalOp, Option.some_inj] at hv
      subst hv
      split <;> simp [widthOf]
  | sliceCompound hi lo hlo hwid hhi hcomp hnc hx ihx =>
    rename_i x
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨_, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    simpa [widthOf] using hmask (hi - lo + 1) _
  | castEnc w hw0 hy ihy =>
    rename_i y
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨_, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    simpa [widthOf] using hmask (w - 1 - 0 + 1) _

/-- The emitter's GENERAL compound-slice arm fires for every non-ref
    operand except the canonical cast-encode shape (whose arm is the
    inversion `w'(y)`). -/
theorem emitAst_slice_general {wof : String → Option Nat}
    {x : Sparkle.IR.AST.Expr} (hi lo : Nat)
    (hcomp : ∀ n, x ≠ .ref n)
    (hncast : ∀ w y, x = .concat [.const 0 w, y] →
      ¬(lo = 0 ∧ hi + 1 = w)) :
    Tools.SVParser.EmitAst.emitAstExpr wof (.slice x hi lo)
      = (Tools.SVParser.EmitAst.emitAstExpr wof x).bind fun inner =>
          if lo == 0 then some (.sizeCast (hi + 1) inner)
          else some (.sizeCast (hi + 1 - lo)
            (.binary .shr inner (.lit (.decimal none lo)))) := by
  have hgen : ∀ (e : Sparkle.IR.AST.Expr),
      (do
        let inner ← Tools.SVParser.EmitAst.emitAstExpr wof e
        let n := hi + 1 - lo
        if lo == 0 then some (Tools.SVParser.AST.SVExpr.sizeCast n inner)
        else some (.sizeCast n (.binary .shr inner (.lit (.decimal none lo)))))
      = (Tools.SVParser.EmitAst.emitAstExpr wof e).bind fun inner =>
          if lo == 0 then some (.sizeCast (hi + 1) inner)
          else some (.sizeCast (hi + 1 - lo)
            (.binary .shr inner (.lit (.decimal none lo)))) := by
    intro e
    cases Tools.SVParser.EmitAst.emitAstExpr wof e with
    | none => rfl
    | some inner =>
      by_cases h0 : lo = 0
      · simp [h0, Nat.sub_zero]
      · simp [h0]
  match x, hcomp, hncast with
  | .const v w, _, _ => exact Eq.trans (by rfl) (hgen _)
  | .op o args, _, _ => exact Eq.trans (by rfl) (hgen _)
  | .slice y hi2 lo2, _, _ => exact Eq.trans (by rfl) (hgen _)
  | .sliceDim y hi2 lo2, _, _ => exact Eq.trans (by rfl) (hgen _)
  | .index a i, _, _ => exact Eq.trans (by rfl) (hgen _)
  | .ref n, hcomp, _ => exact absurd rfl (hcomp n)
  | .concat [], _, _ => exact Eq.trans (by rfl) (hgen _)
  | .concat [a], _, _ =>
    rw [Tools.SVParser.EmitAst.emitAstExpr.eq_def]
    split <;>
      first
        | exact hgen _
        | (rename_i heq
           first
             | injection heq with he hh hl
             | obtain ⟨he, hh, hl⟩ := heq
           subst he hh hl
           refine Eq.trans ?_ (hgen _)
           rfl)
        | simp_all
  | .concat (a :: b :: c :: rest), _, _ =>
    rw [Tools.SVParser.EmitAst.emitAstExpr.eq_def]
    split <;>
      first
        | exact hgen _
        | (rename_i heq
           first
             | injection heq with he hh hl
             | obtain ⟨he, hh, hl⟩ := heq
           subst he hh hl
           refine Eq.trans ?_ (hgen _)
           rfl)
        | simp_all
  | .concat [a, b], _, hncast =>
    match a, hncast with
    | .ref _, _ | .op _ _, _ | .concat _, _ | .slice _ _ _, _
    | .sliceDim _ _ _, _ | .index _ _, _ => exact Eq.trans (by rfl) (hgen _)
    | .const v w, hncast =>
      by_cases hv : v = 0
      · subst hv
        have hng : (lo == 0 && hi + 1 == w) = false := by
          have := hncast w b rfl
          simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
          by_cases hl0 : lo = 0
          · right; intro hEq; exact this ⟨hl0, hEq⟩
          · left; exact hl0
        show Tools.SVParser.EmitAst.emitAstExpr wof
            (.slice (.concat [.const 0 w, b]) hi lo) = _
        rw [show Tools.SVParser.EmitAst.emitAstExpr wof
            (.slice (.concat [.const 0 w, b]) hi lo)
          = if (lo == 0 && hi + 1 == w) = true then do
              some (.sizeCast w (← Tools.SVParser.EmitAst.emitAstExpr wof b))
            else do
              let inner ← Tools.SVParser.EmitAst.emitAstExpr wof
                (.concat [.const 0 w, b])
              let n := hi + 1 - lo
              if lo == 0 then some (.sizeCast n inner)
              else some (.sizeCast n
                (.binary .shr inner (.lit (.decimal none lo))))
          from rfl]
        rw [if_neg (by simp [hng])]
        exact Eq.trans (by rfl) (hgen _)
      · rw [Tools.SVParser.EmitAst.emitAstExpr.eq_def]
        split <;>
          first
            | exact hgen _
            | (rename_i heq
               first
                 | injection heq with he hh hl
                 | obtain ⟨he, hh, hl⟩ := heq
               subst he hh hl
               refine Eq.trans ?_ (hgen _)
               rfl)
            | simp_all

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
  | const v w hw =>
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    by_cases h0 : v < 0
    · -- negative: emitted as sized-hex two's complement; semantically
      -- the same constant
      refine ⟨.const (Int.ofNat (Tools.SVParser.EmitAst.encodeConst v w)) w, ?_, rfl, ?_⟩
      · simp [emitAstExpr, hne, if_pos h0, lowerT]
      · have henc := encodeConst_lt v w hw
        rw [eval_const_ofNat we env _ w henc, eval_const_encode,
          mask, Nat.mod_eq_of_lt henc]
    · refine ⟨.const v w, ?_, rfl, rfl⟩
      have h0' : 0 ≤ v := by omega
      simp [emitAstExpr, hne, if_neg h0, lowerT, Int.toNat_of_nonneg h0']
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
  | mux hwfw hc ht hf ihc iht ihf =>
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
  | concatNil =>
    exact ⟨.concat [],
      by simp [emitAstExpr, emitConcatElems, lowerT, lowerTList], rfl, rfl⟩
  | concatCons hopw ha hrest iha ihrest =>
    rename_i a rest
    obtain ⟨a', hea, hwa, hva⟩ := iha
    obtain ⟨r', her, hwr, hvr⟩ := ihrest
    obtain ⟨ea, hea1, hea2⟩ := Option.bind_eq_some_iff.mp hea
    obtain ⟨er, her1, her2⟩ := Option.bind_eq_some_iff.mp her
    obtain ⟨es, hes1, rfl⟩ : ∃ es, emitConcatElems wof rest = some es
        ∧ er = SVExpr.concat es := by
      cases hE : emitConcatElems wof rest with
      | none => simp [emitAstExpr, hE] at her1
      | some es =>
        simp only [emitAstExpr, hE, Option.bind_some] at her1
        exact ⟨es, rfl, (Option.some_inj.mp her1).symm⟩
    obtain ⟨rls, hrls1, rfl⟩ : ∃ rls, lowerTList es = some rls
        ∧ r' = Sparkle.IR.AST.Expr.concat rls := by
      cases hL : lowerTList es with
      | none => simp [lowerT, hL] at her2
      | some rls =>
        simp only [lowerT, hL, Option.bind_some] at her2
        exact ⟨rls, rfl, (Option.some_inj.mp her2).symm⟩
    -- aggregate width of the rest-lists
    have hgoW : Sparkle.IR.Semantics.widthOf.go we rls
        = Sparkle.IR.Semantics.widthOf.go we rest := by
      simpa [Sparkle.IR.Semantics.widthOf] using hwr
    -- rest evaluation transfer (both directions, some and none)
    have hrestEval : ∀ vs, evalList we env rest = some vs →
        ∃ vs2, evalList we env rls = some vs2
          ∧ evalExpr.go we rls vs2 = evalExpr.go we rest vs := by
      intro vs hR
      have hcr : evalExpr we env (.concat rest)
          = some (evalExpr.go we rest vs) := by
        simp [evalExpr, hR]
      have h2 := hvr.trans hcr
      cases hL : evalList we env rls with
      | none => simp [evalExpr, hL] at h2
      | some vs2 =>
        simp only [evalExpr, hL, Option.bind_eq_bind, Option.bind_some,
          Option.some_inj] at h2
        exact ⟨vs2, rfl, h2⟩
    have hrestNone : evalList we env rest = none →
        evalList we env rls = none := by
      intro hR
      have hcr : evalExpr we env (.concat rest) = none := by
        simp [evalExpr, hR]
      have h2 := hvr.trans hcr
      cases hL : evalList we env rls with
      | none => rfl
      | some vs2 => simp [evalExpr, hL] at h2
    by_cases hop : ∃ o as, a = Sparkle.IR.AST.Expr.op o as
    · -- op-typed head: emitted with a size cast
      obtain ⟨o, as, rfl⟩ := hop
      obtain ⟨w, hwT, hw0, hwS⟩ := hopw o as rfl
      have hwa' : Sparkle.IR.Semantics.widthOf we a' = w := by
        rw [hwa, hwS]
      refine ⟨.concat (.slice (.concat [.const 0 w, a']) (w - 1) 0 :: rls),
        ?_, ?_, ?_⟩
      · have hif : (if w > 0 then SVExpr.sizeCast w ea else ea)
            = SVExpr.sizeCast w ea := if_pos hw0
        simp [emitAstExpr, emitConcatElems, hea1, hes1, hwT, hif, lowerT,
          lowerTList, hea2, hrls1]
      · simp only [Sparkle.IR.Semantics.widthOf, widthOf.go, hgoW]
        have h1 : w - 1 - 0 + 1 = w := by omega
        rw [h1, hwS]
      · cases hA : evalExpr we env (.op o as) with
        | none =>
          have hA' : evalExpr we env a' = none := by rw [hva, hA]
          have hEnc : evalExpr we env
              (.slice (.concat [.const 0 w, a']) (w - 1) 0) = none := by
            simp [evalExpr, evalList, hA']
          rw [eval_concat_cons, eval_concat_cons, hA, hEnc]
          simp
        | some v =>
          have hA' : evalExpr we env a' = some v := by rw [hva, hA]
          have hcast := castEncode_sem we env a' w hwa' hw0 v hA'
          cases hR : evalList we env rest with
          | none =>
            have hRls := hrestNone hR
            rw [eval_concat_cons, eval_concat_cons, hA, hcast, hR, hRls]
            simp
          | some vs =>
            obtain ⟨vs2, hRls, hgo⟩ := hrestEval vs hR
            have hlen2 : rls.length ≤ vs2.length := by
              have := evalList_length hRls; omega
            have hlenR : rest.length ≤ vs.length := by
              have := evalList_length hR; omega
            have hw1 : w - 1 + 1 = w := by omega
            have hw1' : w - 1 - 0 + 1 = w := by omega
            have hmm : ∀ x n : Nat, x % n % n = x % n :=
              fun x n => Nat.mod_mod_of_dvd x (Nat.dvd_refl n)
            rw [eval_concat_cons, eval_concat_cons, hA, hcast, hR, hRls]
            simp only [Option.bind_eq_bind, Option.bind_some,
              Option.some_inj]
            simp only [evalExpr.go, restW_eq we rls vs2 hlen2,
              restW_eq we rest vs hlenR, hgoW, hgo,
              Sparkle.IR.Semantics.widthOf, hw1, hw1', hwS, mask, hmm]
    · -- plain head: emitted 1:1
      refine ⟨.concat (a' :: rls), ?_, ?_, ?_⟩
      · cases a <;>
          first
            | (exact absurd ⟨_, _, rfl⟩ hop)
            | simp_all [emitAstExpr, emitConcatElems, lowerT, lowerTList]
      · simp only [Sparkle.IR.Semantics.widthOf, widthOf.go, hgoW, hwa]
      · cases hA : evalExpr we env a with
        | none =>
          have hA' : evalExpr we env a' = none := by rw [hva, hA]
          rw [eval_concat_cons, eval_concat_cons, hA, hA']
          simp
        | some v =>
          have hA' : evalExpr we env a' = some v := by rw [hva, hA]
          cases hR : evalList we env rest with
          | none =>
            have hRls := hrestNone hR
            rw [eval_concat_cons, eval_concat_cons, hA, hA', hR, hRls]
            simp
          | some vs =>
            obtain ⟨vs2, hRls, hgo⟩ := hrestEval vs hR
            have hlen2 : rls.length ≤ vs2.length := by
              have := evalList_length hRls; omega
            have hlenR : rest.length ≤ vs.length := by
              have := evalList_length hR; omega
            rw [eval_concat_cons, eval_concat_cons, hA, hA', hR, hRls]
            simp only [Option.bind_eq_bind, Option.bind_some,
              Option.some_inj]
            simp only [evalExpr.go, restW_eq we rls vs2 hlen2,
              restW_eq we rest vs hlenR, hgoW, hgo, hwa]
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
  | sliceRefKeep n hi lo hs hkeep hin hw =>
    refine ⟨.slice (.ref n) hi lo, ?_, rfl, rfl⟩
    rcases hw with hw | hw
    · simp [emitAstExpr, hs, hw, lowerT]
    · rcases hkeep with hk | hk
      · rw [hk] at hw; cases hw
      · rcases hin with hin | hin
        · rw [hin] at hw; cases hw
        · have hb : (lo == 0 && hi + 1 == we n) = false := by
            simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
            omega
          simp [emitAstExpr, hs, hw, hb, hin, lowerT]
  | sliceRefElide n hi hs hw hexact henv =>
    refine ⟨.ref n, ?_, ?_, ?_⟩
    · have hb : ((0 : Nat) == 0 && hi + 1 == we n) = true := by
        simp [hexact]
      simp only [emitAstExpr, hs, hw, hb, if_true]
      simp [lowerT]
    · simp only [Sparkle.IR.Semantics.widthOf, Nat.sub_zero]; omega
    · simp [evalExpr, mask, Nat.sub_zero, hexact, Nat.mod_eq_of_lt henv]
  | asr hncx hncy hx hy ihx ihy =>
    rename_i x y
    obtain ⟨x', hex, hwx, hvx⟩ := ihx
    obtain ⟨y', hey, hwy, hvy⟩ := ihy
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hex
    obtain ⟨ey, hey1, hey2⟩ := Option.bind_eq_some_iff.mp hey
    refine ⟨.op .asr [x', y'], ?_, ?_, ?_⟩
    · simp [emitAstExpr, hex1, hey1, lowerT, hex2, hey2]
    · simp_all [Sparkle.IR.Semantics.widthOf]
    · cases hA : evalExpr we env x <;> cases hB : evalExpr we env y <;>
        simp_all [evalExpr, evalList, evalOp, Sparkle.IR.Semantics.widthOf]
  | cmpS op hop w hwTx hwTy hwSx hwSy hw0 hbx hby hx hy ihx ihy =>
    rename_i x y
    obtain ⟨x', hex, hwx, hvx⟩ := ihx
    obtain ⟨y', hey, hwy, hvy⟩ := ihy
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hex
    obtain ⟨ey, hey1, hey2⟩ := Option.bind_eq_some_iff.mp hey
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    have hwx' : Sparkle.IR.Semantics.widthOf we x' = w := by rw [hwx, hwSx]
    have hwy' : Sparkle.IR.Semantics.widthOf we y' = w := by rw [hwy, hwSy]
    rcases hop with rfl | rfl | rfl | rfl
    · -- lt_s
      refine ⟨.op .lt_u
          [.op .xor [.op .and [x', .const (Int.ofNat (2 ^ w - 1)) w],
                     .const (Int.ofNat (2 ^ (w - 1))) w],
           .op .xor [.op .and [y', .const (Int.ofNat (2 ^ w - 1)) w],
                     .const (Int.ofNat (2 ^ (w - 1))) w]], ?_, ?_, ?_⟩
      · simp [emitAstExpr, hex1, hey1, hwTx, hwTy, hne, Nat.max_self,
          lowerT, hex2, hey2]
      · rfl
      · cases hA : evalExpr we env x with
        | none =>
          have hA' : evalExpr we env x' = none := by rw [hvx, hA]
          simp [evalExpr, evalList, hA, hA']
        | some vx =>
          have hA' : evalExpr we env x' = some vx := by rw [hvx, hA]
          have hvxb := hbx vx hA
          cases hB : evalExpr we env y with
          | none =>
            have hB' : evalExpr we env y' = none := by rw [hvy, hB]
            simp [evalExpr, evalList, evalOp, hA, hA', hB, hB']
          | some vy =>
            have hB' : evalExpr we env y' = some vy := by rw [hvy, hB]
            have hvyb := hby vy hB
            have hbx1 := biasOperand_sem we env x' w hw0 hwx' vx hvxb hA'
            have hby1 := biasOperand_sem we env y' w hw0 hwy' vy hvyb hB'
            have hcond : ((vx ^^^ 2 ^ (w - 1)) < (vy ^^^ 2 ^ (w - 1))) = (toSigned w vx < toSigned w vy) :=
              propext (bias_lt w hw0 vx vy hvxb hvyb)
            rw [eval_binop_pair we env Operator.lt_u
                  (.op .xor [.op .and [x', .const (Int.ofNat (2 ^ w - 1)) w],
                             .const (Int.ofNat (2 ^ (w - 1))) w])
                  (.op .xor [.op .and [y', .const (Int.ofNat (2 ^ w - 1)) w],
                             .const (Int.ofNat (2 ^ (w - 1))) w]),
                eval_binop_pair we env Operator.lt_s x y,
                hbx1, hby1, hA, hB]
            simp [evalOp, hwSx, hwSy, Nat.max_self, hcond]
    · -- le_s
      refine ⟨.op .le_u
          [.op .xor [.op .and [x', .const (Int.ofNat (2 ^ w - 1)) w],
                     .const (Int.ofNat (2 ^ (w - 1))) w],
           .op .xor [.op .and [y', .const (Int.ofNat (2 ^ w - 1)) w],
                     .const (Int.ofNat (2 ^ (w - 1))) w]], ?_, ?_, ?_⟩
      · simp [emitAstExpr, hex1, hey1, hwTx, hwTy, hne, Nat.max_self,
          lowerT, hex2, hey2]
      · rfl
      · cases hA : evalExpr we env x with
        | none =>
          have hA' : evalExpr we env x' = none := by rw [hvx, hA]
          simp [evalExpr, evalList, hA, hA']
        | some vx =>
          have hA' : evalExpr we env x' = some vx := by rw [hvx, hA]
          have hvxb := hbx vx hA
          cases hB : evalExpr we env y with
          | none =>
            have hB' : evalExpr we env y' = none := by rw [hvy, hB]
            simp [evalExpr, evalList, evalOp, hA, hA', hB, hB']
          | some vy =>
            have hB' : evalExpr we env y' = some vy := by rw [hvy, hB]
            have hvyb := hby vy hB
            have hbx1 := biasOperand_sem we env x' w hw0 hwx' vx hvxb hA'
            have hby1 := biasOperand_sem we env y' w hw0 hwy' vy hvyb hB'
            have hcond : ((vx ^^^ 2 ^ (w - 1)) ≤ (vy ^^^ 2 ^ (w - 1))) = (toSigned w vx ≤ toSigned w vy) :=
              propext (bias_le w hw0 vx vy hvxb hvyb)
            rw [eval_binop_pair we env Operator.le_u
                  (.op .xor [.op .and [x', .const (Int.ofNat (2 ^ w - 1)) w],
                             .const (Int.ofNat (2 ^ (w - 1))) w])
                  (.op .xor [.op .and [y', .const (Int.ofNat (2 ^ w - 1)) w],
                             .const (Int.ofNat (2 ^ (w - 1))) w]),
                eval_binop_pair we env Operator.le_s x y,
                hbx1, hby1, hA, hB]
            simp [evalOp, hwSx, hwSy, Nat.max_self, hcond]
    · -- gt_s
      refine ⟨.op .gt_u
          [.op .xor [.op .and [x', .const (Int.ofNat (2 ^ w - 1)) w],
                     .const (Int.ofNat (2 ^ (w - 1))) w],
           .op .xor [.op .and [y', .const (Int.ofNat (2 ^ w - 1)) w],
                     .const (Int.ofNat (2 ^ (w - 1))) w]], ?_, ?_, ?_⟩
      · simp [emitAstExpr, hex1, hey1, hwTx, hwTy, hne, Nat.max_self,
          lowerT, hex2, hey2]
      · rfl
      · cases hA : evalExpr we env x with
        | none =>
          have hA' : evalExpr we env x' = none := by rw [hvx, hA]
          simp [evalExpr, evalList, hA, hA']
        | some vx =>
          have hA' : evalExpr we env x' = some vx := by rw [hvx, hA]
          have hvxb := hbx vx hA
          cases hB : evalExpr we env y with
          | none =>
            have hB' : evalExpr we env y' = none := by rw [hvy, hB]
            simp [evalExpr, evalList, evalOp, hA, hA', hB, hB']
          | some vy =>
            have hB' : evalExpr we env y' = some vy := by rw [hvy, hB]
            have hvyb := hby vy hB
            have hbx1 := biasOperand_sem we env x' w hw0 hwx' vx hvxb hA'
            have hby1 := biasOperand_sem we env y' w hw0 hwy' vy hvyb hB'
            have hcond : ((vy ^^^ 2 ^ (w - 1)) < (vx ^^^ 2 ^ (w - 1))) = (toSigned w vy < toSigned w vx) :=
              propext (bias_lt w hw0 vy vx hvyb hvxb)
            rw [eval_binop_pair we env Operator.gt_u
                  (.op .xor [.op .and [x', .const (Int.ofNat (2 ^ w - 1)) w],
                             .const (Int.ofNat (2 ^ (w - 1))) w])
                  (.op .xor [.op .and [y', .const (Int.ofNat (2 ^ w - 1)) w],
                             .const (Int.ofNat (2 ^ (w - 1))) w]),
                eval_binop_pair we env Operator.gt_s x y,
                hbx1, hby1, hA, hB]
            simp [evalOp, hwSx, hwSy, Nat.max_self, hcond]
    · -- ge_s
      refine ⟨.op .ge_u
          [.op .xor [.op .and [x', .const (Int.ofNat (2 ^ w - 1)) w],
                     .const (Int.ofNat (2 ^ (w - 1))) w],
           .op .xor [.op .and [y', .const (Int.ofNat (2 ^ w - 1)) w],
                     .const (Int.ofNat (2 ^ (w - 1))) w]], ?_, ?_, ?_⟩
      · simp [emitAstExpr, hex1, hey1, hwTx, hwTy, hne, Nat.max_self,
          lowerT, hex2, hey2]
      · rfl
      · cases hA : evalExpr we env x with
        | none =>
          have hA' : evalExpr we env x' = none := by rw [hvx, hA]
          simp [evalExpr, evalList, hA, hA']
        | some vx =>
          have hA' : evalExpr we env x' = some vx := by rw [hvx, hA]
          have hvxb := hbx vx hA
          cases hB : evalExpr we env y with
          | none =>
            have hB' : evalExpr we env y' = none := by rw [hvy, hB]
            simp [evalExpr, evalList, evalOp, hA, hA', hB, hB']
          | some vy =>
            have hB' : evalExpr we env y' = some vy := by rw [hvy, hB]
            have hvyb := hby vy hB
            have hbx1 := biasOperand_sem we env x' w hw0 hwx' vx hvxb hA'
            have hby1 := biasOperand_sem we env y' w hw0 hwy' vy hvyb hB'
            have hcond : ((vy ^^^ 2 ^ (w - 1)) ≤ (vx ^^^ 2 ^ (w - 1))) = (toSigned w vy ≤ toSigned w vx) :=
              propext (bias_le w hw0 vy vx hvyb hvxb)
            rw [eval_binop_pair we env Operator.ge_u
                  (.op .xor [.op .and [x', .const (Int.ofNat (2 ^ w - 1)) w],
                             .const (Int.ofNat (2 ^ (w - 1))) w])
                  (.op .xor [.op .and [y', .const (Int.ofNat (2 ^ w - 1)) w],
                             .const (Int.ofNat (2 ^ (w - 1))) w]),
                eval_binop_pair we env Operator.ge_s x y,
                hbx1, hby1, hA, hB]
            simp [evalOp, hwSx, hwSy, Nat.max_self, hcond]
  | sliceCompound hi lo hlo hwid hhi hcomp hncast hx ih =>
    rename_i x
    obtain ⟨x', hex, hwx, hvx⟩ := ih
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hex
    cases hval : evalExpr we env x with
    | none =>
      have hval' : evalExpr we env x' = none := by rw [hvx, hval]
      refine ⟨.slice (.concat [.const 0 (hi + 1 - lo),
        if lo == 0 then x' else .op .shr [x', .const (Int.ofNat lo) 32]])
        (hi + 1 - lo - 1) 0, ?_, ?_, ?_⟩
      · rw [emitAst_slice_general hi lo hcomp hncast]
        cases hE : Tools.SVParser.EmitAst.emitAstExpr wof x with
        | none => rw [hE] at hex1; cases hex1
        | some ex0 =>
          have : ex0 = ex := by rw [hE] at hex1; injection hex1
          subst this
          by_cases h0 : lo = 0 <;> simp_all [lowerT]
      · simp [Sparkle.IR.Semantics.widthOf]; omega
      · by_cases h0 : lo = 0 <;>
          simp_all [evalExpr, evalList, evalOp, evalExpr.go]
    | some v =>
      have hval' : evalExpr we env x' = some v := by rw [hvx, hval]
      refine ⟨.slice (.concat [.const 0 (hi + 1 - lo),
        if lo == 0 then x' else .op .shr [x', .const (Int.ofNat lo) 32]])
        (hi + 1 - lo - 1) 0, ?_, ?_, ?_⟩
      · rw [emitAst_slice_general hi lo hcomp hncast]
        cases hE : Tools.SVParser.EmitAst.emitAstExpr wof x with
        | none => rw [hE] at hex1; cases hex1
        | some ex0 =>
          have : ex0 = ex := by rw [hE] at hex1; injection hex1
          subst this
          by_cases h0 : lo = 0 <;> simp_all [lowerT]
      · simp [Sparkle.IR.Semantics.widthOf]; omega
      · rw [sliceEncode_sem we env x' hi lo hlo (by rw [hwx]; omega) hhi v hval']
        simp [evalExpr, hvx]
  | castEnc w hw0 hy ihy =>
    rename_i y
    obtain ⟨y', hey, hwy, hvy⟩ := ihy
    obtain ⟨ey, hey1, hey2⟩ := Option.bind_eq_some_iff.mp hey
    have hww : w - 1 + 1 = w := by omega
    refine ⟨.slice (.concat [.const 0 w, y']) (w - 1) 0, ?_, ?_, ?_⟩
    · simp [emitAstExpr, hey1, hww, lowerT, hey2]
    · simp [Sparkle.IR.Semantics.widthOf]
    · cases hv : evalExpr we env y with
      | none => simp [evalExpr, evalList, hvy, hv]
      | some v => simp [evalExpr, evalList, evalExpr.go, hvy, hv, hwy]


/- ------------------------------------------------------------------ -/
/- M1/M2, statement layer: the lowering twin for the ITEM sub-language
   `emitAstStmt` produces, and the per-statement roundtrip images.

   The shipping lowering turns our emitted register

       always_ff @(posedge clk or posedge rst)
         if (rst) out <= init; else out <= input;

   into `.register out clk (rst, async) (mux [¬rst, input', init']) init`
   — the reset arm FOLDED INTO the input expression.  Two consequences
   the theorems below make precise:

   * the mux-guarded input is equivalent to `regNexts`' reset-mux ONLY
     when the reset is 1-bit (for wider rst, `~rst ≠ 0` even under
     reset) — a WIDTH side condition, not a formality;
   * the init constant comes back ENCODED (`Int.ofNat (encodeConst …)`),
     equal under `encodeInit`. -/

/-- Item-level lowering twin for the emitted sub-language: continuous
    assigns and the always-if register shape. -/
def lowerTItem : SVModuleItem → Option (List Sparkle.IR.AST.Stmt)
  | .contAssign (.ident l) rhs => do
    some [.assign l (← lowerT rhs)]
  | .alwaysBlock (.posedge clk)
      [.ifElse (.ident rst)
        [.nonblockAssign (.ident out1) initE]
        [.nonblockAssign (.ident out2) inputE]] => do
    if out1 ≠ out2 then none else
    let init' ← lowerT initE
    let input' ← lowerT inputE
    match init' with
    | .const iv _ =>
      -- the shipping pipeline's post-optimize stripResetMux pass removes
      -- the redundant reset mux, so the image register carries the
      -- lowered input DIRECTLY (near-identity roundtrip)
      some [.register out1 clk (rst, .asynchronous) input' iv]
    | _ => none
  | .wireDecl _ _ none => some []       -- declaration only
  | .wireDecl _ _ (some _) => some []   -- register initializer (guarded)
  | _ => none

-- Twin ties against the SHIPPING module lowering, via the probe module:
-- emit → parse → lower must agree with emitAstStmt → lowerTItem.
private def probeStmtM : Sparkle.IR.AST.Module := {
  name := "pstmt"
  inputs := [⟨"clock", .bit⟩, ⟨"rst", .bit⟩, ⟨"a", .bitVector 8⟩]
  outputs := [⟨"q", .bitVector 8⟩]
  wires := [⟨"w", .bitVector 8⟩, ⟨"r", .bitVector 8⟩, ⟨"q", .bitVector 8⟩]
  body := [
    .assign "w" (.op .add [.ref "a", .ref "r"]),
    .register "r" "clock" ("rst", .asynchronous) (.ref "w") 3,
    .assign "q" (.ref "r")]
  assertions := [] }

private def chkStmtTwin : Bool := Id.run do
  -- shipping path
  let shipped :=
    match Tools.SVParser.Lower.parseAndLowerHierarchical
        (Sparkle.Backend.Verilog.emitModule probeStmtM) with
    | .ok d => d.modules.foldl
        (fun acc (m : Sparkle.IR.AST.Module) => acc ++ m.body) []
    | .error _ => []
  -- twin path
  let wof : String → Option Nat := fun n =>
    ((probeStmtM.wires ++ probeStmtM.inputs ++ probeStmtM.outputs).find? (fun p =>
      Sparkle.Backend.Verilog.sanitizeName p.name == n)).bind fun p =>
      match p.ty with
      | .bitVector w => some w
      | .bit => some 1
      | _ => none
  let twinned : Option (List Sparkle.IR.AST.Stmt) := do
    let mut out : List Sparkle.IR.AST.Stmt := []
    for st in probeStmtM.body do
      let items ← Tools.SVParser.EmitAst.emitAstStmt wof probeStmtM.wires st
      for it in items do
        out := out ++ (← lowerTItem it)
    some out
  -- shipping reorders (assigns first, registers after) and may add the
  -- optimizer's touches; compare as SETS of statements
  match twinned with
  | none => false
  | some tw =>
    tw.all (fun st => shipped.contains st)
      && shipped.all (fun st => tw.contains st)

#guard chkStmtTwin


/- ------------------------------------------------------------------ -/
/- The module-level roundtrip theorem (assign+register bodies).

   Pleasant discovery: NO reset-width or boundedness side conditions are
   needed.  `regNexts` reads the reset from the post-elaboration env
   directly, so the image's redundant `mux(¬rst, …)` guard is consistent
   by construction: under reset both sides take their INIT fields, and
   out of reset the mux picks the input branch (the `¬rst ≠ 0` test is
   satisfied for rst = 0 at ANY width).  The width worry only applies to
   semantics that derive reset behavior from the mux alone. -/

/-- One port expression through emit∘lower. -/
def lowerPort (wof : String → Option Nat) (e : Sparkle.IR.AST.Expr) :
    Option Sparkle.IR.AST.Expr :=
  (Tools.SVParser.EmitAst.emitAstExpr wof e).bind lowerT

/-- Write ports through emit∘lower, in order (structural recursion so
    proofs can rewrite it). -/
def lowerWritePorts (wof : String → Option Nat) :
    List (Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr) →
    Option (List (Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr
      × Sparkle.IR.AST.Expr))
  | [] => some []
  | (a, d, en) :: rest => do
    let a' ← lowerPort wof a
    let d' ← lowerPort wof d
    let en' ← lowerPort wof en
    some ((a', d', en') :: (← lowerWritePorts wof rest))

/-- Read ports through emit∘lower.  A COMBO read whose target trips the
    `isArrayName` heuristic is dropped by the shipping scan
    (`exprToName` returns none) — outside the twin. -/
def lowerReadPorts (wof : String → Option Nat) (cr : Bool) :
    List (Sparkle.IR.AST.Expr × String) →
    Option (List (Sparkle.IR.AST.Expr × String))
  | [] => some []
  | (a, r) :: rest =>
    if cr && Tools.SVParser.Lower.isArrayName
        (Sparkle.Backend.Verilog.sanitizeName r) then none
    else do
      let a' ← lowerPort wof a
      some ((a', Sparkle.Backend.Verilog.sanitizeName r)
        :: (← lowerReadPorts wof cr rest))

/-- The shipping claim sentinel, transparently: `e == Expr.const 0 1`
    (the derived `Expr.beq` is well-founded recursion and opaque to
    kernel reduction, so proofs need this match form). -/
def isConst01 : Sparkle.IR.AST.Expr → Bool
  | .const v w => v == 0 && w == 1
  | _ => false

/-- The shipping claim fold, on its drop-free domain: the first port
    claims the dedicated fields, the rest are extra ports in order.
    A FIRST port whose lowered enable is literally `1'h0` with more
    ports following is outside the twin: the shipping fold re-claims
    over it (the port never fires, so dropping it is semantically
    inert, but the twin does not model the drop). -/
def claimWritesT
    (ports : List (Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr
      × Sparkle.IR.AST.Expr)) :
    Option ((Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr
        × Sparkle.IR.AST.Expr)
      × List (Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr
        × Sparkle.IR.AST.Expr)) :=
  match ports with
  | [] => none
  | p :: rest =>
    if isConst01 p.2.2 && !rest.isEmpty then none
    else some (p, rest)

/-- Image of a `.memory` statement through emit∘lower: the shipping
    reconstruction result on the emitted item group (array regDecl +
    read assigns/latches + guarded-write always block), as a twin. -/
def memImage (wof : String → Option Nat) :
    Sparkle.IR.AST.Stmt → Option Sparkle.IR.AST.Stmt
  | .memory name aw dw clk wa wd wen ra rd cr ew er => do
    let writesI ← lowerWritePorts wof ((wa, wd, wen) :: ew)
    let (w0, extraW) ← claimWritesT writesI
    let readsI ← lowerReadPorts wof cr ((ra, rd) :: er)
    match readsI with
    | [] => none
    | (ra0, rd0) :: extraR =>
      -- the emitted decl is `logic [dw-1:0] M [0:2^aw-1]` for dw > 1
      -- and `logic M [0:2^aw-1]` otherwise; `widthToBits` reads dw
      -- back with floor 1, and `log2 (2^aw)` reads aw back exactly
      some (.memory (Sparkle.Backend.Verilog.sanitizeName name) aw
        (if dw ≤ 1 then 1 else dw)
        (Sparkle.Backend.Verilog.sanitizeName clk)
        w0.1 w0.2.1 w0.2.2 ra0 rd0 cr extraW extraR)
  | _ => none

open Sparkle.IR.Semantics in
/-- The statement-level roundtrip image: emit, then lower, at the AST
    level.  Memories are multi-item groups reconstructed by a global
    scan, so their image is the dedicated `memImage` twin. -/
def stmtImage (wof : String → Option Nat)
    (wires : List Sparkle.IR.AST.Port) (st : Sparkle.IR.AST.Stmt) :
    Option (List Sparkle.IR.AST.Stmt) :=
  match st with
  | .memory n aw dw clk wa wd wen ra rd cr ew er =>
    (memImage wof (.memory n aw dw clk wa wd wen ra rd cr ew er)).map
      (fun x => [x])
  | st => do
    let items ← Tools.SVParser.EmitAst.emitAstStmt wof wires st
    let ls ← items.mapM lowerTItem
    some ls.flatten

-- Memory twin ties against the SHIPPING pipeline on probe modules:
-- emit → parse → lower must equal the memImage stmt exactly.
private def chkMemTwin (m : Sparkle.IR.AST.Module) : Bool :=
  let shipped :=
    match Tools.SVParser.Lower.parseAndLowerHierarchical
        (Sparkle.Backend.Verilog.emitModule m) with
    | .ok d => d.modules.foldl
        (fun acc (lm : Sparkle.IR.AST.Module) => acc ++ lm.body) []
    | .error _ => []
  let wof : String → Option Nat := fun n =>
    ((m.wires ++ m.inputs ++ m.outputs).find? (fun p =>
      Sparkle.Backend.Verilog.sanitizeName p.name == n)).bind fun p =>
      match p.ty with
      | .bitVector w => some w
      | .bit => some 1
      | _ => none
  match m.body with
  | [st] =>
    match stmtImage wof m.wires st with
    | some img => img == shipped
    | none => false
  | _ => false

private def probeMemCombo : Sparkle.IR.AST.Module := {
  name := "pmemc"
  inputs := [⟨"clock", .bit⟩, ⟨"wa", .bitVector 2⟩, ⟨"wd", .bitVector 8⟩,
             ⟨"wen", .bit⟩, ⟨"ra", .bitVector 2⟩]
  outputs := [⟨"rdata", .bitVector 8⟩]
  wires := [⟨"rdata", .bitVector 8⟩]
  body := [.memory "Mem" 2 8 "clock" (.ref "wa") (.ref "wd") (.ref "wen")
    (.ref "ra") "rdata" true [] []]
  assertions := [] }

private def probeMemMulti : Sparkle.IR.AST.Module := {
  name := "pmemm"
  inputs := [⟨"clock", .bit⟩, ⟨"wa", .bitVector 2⟩, ⟨"wd", .bitVector 8⟩,
             ⟨"wen", .bit⟩, ⟨"wa2", .bitVector 2⟩, ⟨"wd2", .bitVector 8⟩,
             ⟨"wen2", .bit⟩, ⟨"ra", .bitVector 2⟩, ⟨"ra2", .bitVector 2⟩]
  outputs := [⟨"rdata", .bitVector 8⟩, ⟨"rdata2", .bitVector 8⟩]
  wires := [⟨"rdata", .bitVector 8⟩, ⟨"rdata2", .bitVector 8⟩]
  body := [.memory "Mem" 2 8 "clock" (.ref "wa") (.ref "wd") (.ref "wen")
    (.ref "ra") "rdata" true
    [(.ref "wa2", .ref "wd2", .ref "wen2")] [(.ref "ra2", "rdata2")]]
  assertions := [] }

private def probeMemSync : Sparkle.IR.AST.Module := {
  name := "pmems"
  inputs := [⟨"clock", .bit⟩, ⟨"wa", .bitVector 2⟩, ⟨"wd", .bitVector 8⟩,
             ⟨"wen", .bit⟩, ⟨"ra", .bitVector 2⟩]
  outputs := [⟨"rdata", .bitVector 8⟩]
  wires := [⟨"rdata", .bitVector 8⟩]
  body := [.memory "Mem" 2 8 "clock" (.ref "wa") (.ref "wd") (.ref "wen")
    (.ref "ra") "rdata" false [] []]
  assertions := [] }

private def probeMemSync2 : Sparkle.IR.AST.Module := {
  name := "pmems2"
  inputs := [⟨"clock", .bit⟩, ⟨"wa", .bitVector 2⟩, ⟨"wd", .bitVector 8⟩,
             ⟨"wen", .bit⟩, ⟨"ra", .bitVector 2⟩, ⟨"ra2", .bitVector 2⟩]
  outputs := [⟨"rdata", .bitVector 8⟩, ⟨"rdata2", .bitVector 8⟩]
  wires := [⟨"rdata", .bitVector 8⟩, ⟨"rdata2", .bitVector 8⟩]
  body := [.memory "Mem" 2 8 "clock" (.ref "wa") (.ref "wd") (.ref "wen")
    (.ref "ra") "rdata" false [] [(.ref "ra2", "rdata2")]]
  assertions := [] }

#guard chkMemTwin probeMemCombo
#guard chkMemTwin probeMemMulti
#guard chkMemTwin probeMemSync
#guard chkMemTwin probeMemSync2

def bodyImage (wof : String → Option Nat)
    (wires : List Sparkle.IR.AST.Port) :
    List Sparkle.IR.AST.Stmt → Option (List Sparkle.IR.AST.Stmt)
  | [] => some []
  | st :: rest => do
    some ((← stmtImage wof wires st) ++ (← bodyImage wof wires rest))

open Sparkle.IR.Semantics in
/-- The init constant survives the emit/lower encode up to `encodeInit`. -/
theorem encodeInit_image (v : Int) (w : Nat) :
    encodeInit (Int.ofNat (Tools.SVParser.EmitAst.encodeConst v w)) w = encodeInit v w := by
  unfold encodeInit Tools.SVParser.EmitAst.encodeConst
  have hg : (0 : Int) < ((2 ^ w : Nat) : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  have h2 := Int.emod_nonneg (v % ((2 ^ w : Nat) : Int) + ((2 ^ w : Nat) : Int))
    (by omega : ((2 ^ w : Nat) : Int) ≠ 0)
  have h3 := Int.emod_lt_of_pos (v % ((2 ^ w : Nat) : Int) + ((2 ^ w : Nat) : Int)) hg
  generalize hE : (v % ((2 ^ w : Nat) : Int) + ((2 ^ w : Nat) : Int))
      % ((2 ^ w : Nat) : Int) = E at *
  -- LHS: encode of the already-encoded value; the inner value is in
  -- [0, 2^w), so every mod is the identity
  have hEeq : Int.ofNat E.toNat = E := Int.toNat_of_nonneg h2
  have hEmod : E % ((2 ^ w : Nat) : Int) = E := Int.emod_eq_of_lt h2 h3
  rw [hEeq, hEmod, Int.add_emod_right, hEmod]

open Sparkle.IR.Semantics in
/-- The nonnegative-init image likewise. -/
theorem encodeInit_image_nonneg (v : Int) (w : Nat) (h0 : 0 ≤ v) :
    encodeInit (Int.ofNat v.toNat) w = encodeInit v w := by
  unfold encodeInit
  have : Int.ofNat v.toNat = v := Int.toNat_of_nonneg h0
  rw [this]


open Sparkle.IR.Semantics in
/-- `claimWritesT` inversion: on its domain the port list is
    preserved verbatim. -/
theorem claimWritesT_inv {ports w0 extraW}
    (h : claimWritesT ports = some (w0, extraW)) :
    ports = w0 :: extraW := by
  match ports with
  | [] => simp [claimWritesT] at h
  | p :: rest =>
    simp only [claimWritesT] at h
    by_cases hc : (isConst01 p.2.2 && !rest.isEmpty) = true
    · rw [if_pos hc] at h; exact absurd h (by simp)
    · rw [if_neg hc] at h
      cases h
      rfl

/-- `memImage` inversion: the lowering stages succeeded, the write
    ports came through verbatim, and the image is the reconstructed
    memory statement. -/
theorem memImage_inv {wof : String → Option Nat}
    {name clk rd : String} {aw dw : Nat} {cr : Bool}
    {wa wd wen ra : Sparkle.IR.AST.Expr}
    {ew : List (Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr
      × Sparkle.IR.AST.Expr)}
    {er : List (Sparkle.IR.AST.Expr × String)}
    {mi : Sparkle.IR.AST.Stmt}
    (h : memImage wof (.memory name aw dw clk wa wd wen ra rd cr ew er)
      = some mi) :
    ∃ w0a w0d w0e extraW ra0 rd0 extraR,
      lowerWritePorts wof ((wa, wd, wen) :: ew)
        = some ((w0a, w0d, w0e) :: extraW)
      ∧ lowerReadPorts wof cr ((ra, rd) :: er) = some ((ra0, rd0) :: extraR)
      ∧ mi = .memory (Sparkle.Backend.Verilog.sanitizeName name) aw
          (if dw ≤ 1 then 1 else dw)
          (Sparkle.Backend.Verilog.sanitizeName clk)
          w0a w0d w0e ra0 rd0 cr extraW extraR := by
  simp only [memImage, Option.bind_eq_bind] at h
  cases hW : lowerWritePorts wof ((wa, wd, wen) :: ew) with
  | none => rw [hW] at h; exact absurd h (by simp)
  | some writes' =>
    rw [hW] at h
    simp only [Option.bind_some] at h
    cases hCl : claimWritesT writes' with
    | none => rw [hCl] at h; exact absurd h (by simp)
    | some pw =>
      obtain ⟨⟨w0a, w0d, w0e⟩, extraW⟩ := pw
      rw [hCl] at h
      simp only [Option.bind_some] at h
      cases hR : lowerReadPorts wof cr ((ra, rd) :: er) with
      | none => rw [hR] at h; exact absurd h (by simp)
      | some readsI =>
        rw [hR] at h
        simp only [Option.bind_some] at h
        cases readsI with
        | nil => exact absurd h (by simp)
        | cons r0 extraR =>
          obtain ⟨ra0, rd0⟩ := r0
          refine ⟨w0a, w0d, w0e, extraW, ra0, rd0, extraR, ?_, rfl, ?_⟩
          · rw [claimWritesT_inv hCl]
          · simp only [Option.some_inj] at h
            exact h.symm

open Sparkle.IR.Semantics in
/-- Pointwise semantic preservation of lowered write ports: the write
    phase computes the same memory update. -/
theorem lowerWritePorts_sem {wof : String → Option Nat} {we : WEnv}
    (ports : List (Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr
      × Sparkle.IR.AST.Expr)) :
    ∀ {ports'}, lowerWritePorts wof ports = some ports' →
    (∀ p ∈ ports, (∀ env, Bounded we env → SFrag wof we env p.1)
      ∧ (∀ env, Bounded we env → SFrag wof we env p.2.1)
      ∧ (∀ env, Bounded we env → SFrag wof we env p.2.2)) →
    ∀ env, Bounded we env → ∀ name aw dw mems,
      memWritePorts we env name aw dw ports' mems
        = memWritePorts we env name aw dw ports mems := by
  induction ports with
  | nil =>
    intro ports' h _
    simp only [lowerWritePorts] at h
    cases h
    intro env _ name aw dw mems
    rfl
  | cons p rest ih =>
    intro ports' h hf
    obtain ⟨a, d, en⟩ := p
    simp only [lowerWritePorts, Option.bind_eq_bind] at h
    cases hA : lowerPort wof a with
    | none => rw [hA] at h; exact absurd h (by simp)
    | some a' =>
    rw [hA] at h
    cases hD : lowerPort wof d with
    | none => rw [hD] at h; exact absurd h (by simp)
    | some d' =>
    rw [hD] at h
    cases hEn : lowerPort wof en with
    | none => rw [hEn] at h; exact absurd h (by simp)
    | some en' =>
    rw [hEn] at h
    cases hRest : lowerWritePorts wof rest with
    | none => rw [hRest] at h; exact absurd h (by simp)
    | some rest' =>
    rw [hRest] at h
    simp only [Option.bind_some, Option.some_inj] at h
    subst h
    have hfp := hf (a, d, en) (List.mem_cons_self ..)
    unfold lowerPort at hA hD hEn
    have hva : ∀ env, Bounded we env →
        evalExpr we env a' = evalExpr we env a := by
      intro env hbe
      obtain ⟨x3, hb3, _, hv3⟩ := roundtrip_sem (hfp.1 env hbe)
      rw [hA] at hb3
      cases hb3
      exact hv3
    have hvd : ∀ env, Bounded we env →
        evalExpr we env d' = evalExpr we env d := by
      intro env hbe
      obtain ⟨x3, hb3, _, hv3⟩ := roundtrip_sem (hfp.2.1 env hbe)
      rw [hD] at hb3
      cases hb3
      exact hv3
    have hven : ∀ env, Bounded we env →
        evalExpr we env en' = evalExpr we env en := by
      intro env hbe
      obtain ⟨x3, hb3, _, hv3⟩ := roundtrip_sem (hfp.2.2 env hbe)
      rw [hEn] at hb3
      cases hb3
      exact hv3
    intro env hbe name aw dw mems
    simp only [memWritePorts, Option.bind_eq_bind, hva env hbe,
      hvd env hbe, hven env hbe]
    cases evalExpr we env en with
    | none => rfl
    | some ev =>
    cases evalExpr we env a with
    | none => rfl
    | some av =>
    cases evalExpr we env d with
    | none => rfl
    | some dv =>
    simp only [Option.bind_some]
    exact ih hRest (fun q hq => hf q (List.mem_cons_of_mem _ hq))
      env hbe name aw dw _

open Sparkle.IR.Semantics in
/-- Pointwise semantic preservation of lowered COMBO read ports: the
    combinational read phase extends the env identically. -/
theorem lowerReadPorts_sem_combo {wof : String → Option Nat} {we : WEnv}
    (dw : Nat)
    (ports : List (Sparkle.IR.AST.Expr × String)) :
    ∀ {ports'}, lowerReadPorts wof true ports = some ports' →
    (∀ p ∈ ports, (∀ env, Bounded we env → SFrag wof we env p.1)
      ∧ Sparkle.Backend.Verilog.sanitizeName p.2 = p.2
      ∧ we p.2 = dw) →
    ∀ mems name aw env, Bounded we env →
      comboReads we mems name aw dw ports' env
        = comboReads we mems name aw dw ports env := by
  induction ports with
  | nil =>
    intro ports' h _
    simp only [lowerReadPorts] at h
    cases h
    intro mems name aw env _
    rfl
  | cons p rest ih =>
    intro ports' h hf
    obtain ⟨a, r⟩ := p
    have hfp := hf (a, r) (List.mem_cons_self ..)
    simp only [lowerReadPorts, Option.bind_eq_bind] at h
    by_cases hna : (true && Tools.SVParser.Lower.isArrayName
        (Sparkle.Backend.Verilog.sanitizeName r)) = true
    · rw [if_pos hna] at h; exact absurd h (by simp)
    · rw [if_neg hna] at h
      cases hA : lowerPort wof a with
      | none => rw [hA] at h; exact absurd h (by simp)
      | some a' =>
      rw [hA] at h
      cases hRest : lowerReadPorts wof true rest with
      | none => rw [hRest] at h; exact absurd h (by simp)
      | some rest' =>
      rw [hRest] at h
      simp only [Option.bind_some, Option.some_inj] at h
      subst h
      unfold lowerPort at hA
      have hva : ∀ env, Bounded we env →
          evalExpr we env a' = evalExpr we env a := by
        intro env hbe
        obtain ⟨x3, hb3, _, hv3⟩ := roundtrip_sem (hfp.1 env hbe)
        rw [hA] at hb3
        cases hb3
        exact hv3
      intro mems name aw env hbe
      simp only [comboReads, Option.bind_eq_bind, hva env hbe, hfp.2.1]
      cases hev : evalExpr we env a with
      | none => rfl
      | some av =>
      simp only [Option.bind_some]
      refine ih hRest (fun q hq => hf q (List.mem_cons_of_mem _ hq))
        mems name aw _ ?_
      intro n
      by_cases hn : n = r
      · subst hn
        rw [hfp.2.2]
        simp [mask, Nat.mod_lt _ (Nat.two_pow_pos dw)]
      · simpa [hn] using hbe n

open Sparkle.IR.Semantics in
/-- Pointwise semantic preservation of lowered SYNC read ports: the
    latch phase computes the same update list. -/
theorem lowerReadPorts_sem_sync {wof : String → Option Nat} {we : WEnv}
    (ports : List (Sparkle.IR.AST.Expr × String)) :
    ∀ {ports'}, lowerReadPorts wof false ports = some ports' →
    (∀ p ∈ ports, (∀ env, Bounded we env → SFrag wof we env p.1)
      ∧ Sparkle.Backend.Verilog.sanitizeName p.2 = p.2) →
    ∀ mems name aw dw env, Bounded we env →
      syncReadLatches we mems name aw dw ports' env
        = syncReadLatches we mems name aw dw ports env := by
  induction ports with
  | nil =>
    intro ports' h _
    simp only [lowerReadPorts] at h
    cases h
    intro mems name aw dw env _
    rfl
  | cons p rest ih =>
    intro ports' h hf
    obtain ⟨a, r⟩ := p
    have hfp := hf (a, r) (List.mem_cons_self ..)
    simp only [lowerReadPorts, Bool.false_and, Bool.false_eq_true,
      if_false, Option.bind_eq_bind] at h
    cases hA : lowerPort wof a with
    | none => rw [hA] at h; exact absurd h (by simp)
    | some a' =>
    rw [hA] at h
    cases hRest : lowerReadPorts wof false rest with
    | none => rw [hRest] at h; exact absurd h (by simp)
    | some rest' =>
    rw [hRest] at h
    simp only [Option.bind_some, Option.some_inj] at h
    subst h
    unfold lowerPort at hA
    have hva : ∀ env, Bounded we env →
        evalExpr we env a' = evalExpr we env a := by
      intro env hbe
      obtain ⟨x3, hb3, _, hv3⟩ := roundtrip_sem (hfp.1 env hbe)
      rw [hA] at hb3
      cases hb3
      exact hv3
    intro mems name aw dw env hbe
    simp only [syncReadLatches, Option.bind_eq_bind, hva env hbe, hfp.2,
      ih hRest (fun q hq => hf q (List.mem_cons_of_mem _ hq))
        mems name aw dw env hbe]

open Sparkle.IR.Semantics in
/-- The module-body fragment: assigns, registers, and single-port
    memories whose expressions are (env-uniformly) in the expression
    fragment, with sanitize-fixed names and width agreement between the
    declared reset width and the semantic width. -/
inductive BFrag (wof : String → Option Nat) (we : WEnv)
    (wires : List Sparkle.IR.AST.Port) : List Sparkle.IR.AST.Stmt → Prop
  | nil : BFrag wof we wires []
  | assign {l x rest}
      (hs : Sparkle.Backend.Verilog.sanitizeName l = l)
      -- width agreement: the stored value is masked at the RHS width,
      -- so this is what keeps the environment BOUNDED through the fold
      (hwl : Sparkle.IR.Semantics.widthOf we x = we l)
      (hx : ∀ env, Sparkle.IR.Semantics.Bounded we env →
        SFrag wof we env x)
      (hrest : BFrag wof we wires rest) :
      BFrag wof we wires (.assign l x :: rest)
  | reg {out clk rst kind x init rest}
      (hso : Sparkle.Backend.Verilog.sanitizeName out = out)
      (hsc : Sparkle.Backend.Verilog.sanitizeName clk = clk)
      (hsr : Sparkle.Backend.Verilog.sanitizeName rst = rst)
      (hx : ∀ env, Sparkle.IR.Semantics.Bounded we env →
        SFrag wof we env x)
      (hrw : Tools.SVParser.EmitAst.regResetWidth wires out = we out)
      (hw0 : 0 < we out)
      (hwrst : 0 < we rst)
      (hrest : BFrag wof we wires rest) :
      BFrag wof we wires (.register out clk (rst, kind) x init :: rest)
  | mem {name : String} {aw dw : Nat} {clk : String}
      {wa wd wen ra : Sparkle.IR.AST.Expr} {rd : String} {cr : Bool}
      {ew : List (Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr
        × Sparkle.IR.AST.Expr)}
      {er : List (Sparkle.IR.AST.Expr × String)} {rest}
      (hsn : Sparkle.Backend.Verilog.sanitizeName name = name)
      (hsc : Sparkle.Backend.Verilog.sanitizeName clk = clk)
      (hwp : ∀ p ∈ (wa, wd, wen) :: ew,
        (∀ env, Sparkle.IR.Semantics.Bounded we env → SFrag wof we env p.1)
        ∧ (∀ env, Sparkle.IR.Semantics.Bounded we env → SFrag wof we env p.2.1)
        ∧ (∀ env, Sparkle.IR.Semantics.Bounded we env → SFrag wof we env p.2.2))
      (hrp : ∀ p ∈ (ra, rd) :: er,
        (∀ env, Sparkle.IR.Semantics.Bounded we env → SFrag wof we env p.1)
        ∧ Sparkle.Backend.Verilog.sanitizeName p.2 = p.2
        -- read data lands masked at dw, so boundedness needs the
        -- declared width to BE dw
        ∧ we p.2 = dw)
      (hdw : 0 < dw)
      (hrest : BFrag wof we wires rest) :
      BFrag wof we wires
        (.memory name aw dw clk wa wd wen ra rd cr ew er :: rest)

/-- Decompose the image of a cons body: a statement image followed by
    the rest's image. -/
theorem cons_image_shape {wof wires} {st : Sparkle.IR.AST.Stmt}
    {rest body' : List Sparkle.IR.AST.Stmt}
    (hI : bodyImage wof wires (st :: rest) = some body') :
    ∃ img rest', stmtImage wof wires st = some img
      ∧ bodyImage wof wires rest = some rest' ∧ body' = img ++ rest' := by
  simp only [bodyImage, Option.bind_eq_bind] at hI
  cases hS : stmtImage wof wires st with
  | none => rw [hS] at hI; simp at hI
  | some img =>
    rw [hS] at hI
    cases hR : bodyImage wof wires rest with
    | none => rw [hR] at hI; simp at hI
    | some rest' =>
      rw [hR] at hI
      simp only [Option.bind_some, Option.some_inj] at hI
      exact ⟨img, rest', rfl, rfl, hI.symm⟩

open Sparkle.IR.Semantics in
theorem bounded_zero (we : WEnv) : Bounded we (fun _ => 0) :=
  fun _ => Nat.two_pow_pos _

open Sparkle.IR.Semantics in
/-- Combinational reads preserve boundedness when the read-data widths
    agree with the declared data width. -/
theorem comboReads_bounded {we : WEnv} {mems : MEnv} {name : String}
    {aw dw : Nat} :
    ∀ {ports : List (Sparkle.IR.AST.Expr × String)},
    (∀ p ∈ ports, we p.2 = dw) →
    ∀ {env env' : Env}, Bounded we env →
    comboReads we mems name aw dw ports env = some env' →
    Bounded we env' := by
  intro ports
  induction ports with
  | nil =>
    intro _ env env' hb h
    cases h
    exact hb
  | cons p rest ih =>
    intro hw env env' hb h
    obtain ⟨a, rd⟩ := p
    simp only [comboReads, Option.bind_eq_bind] at h
    cases ha : evalExpr we env a with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some av =>
      rw [ha] at h
      simp only [Option.bind_some] at h
      refine ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)) ?_ h
      intro n
      by_cases hn : n = rd
      · subst hn
        have := hw (a, n) (List.mem_cons_self ..)
        simp only at this
        rw [this]
        simp [Nat.mod_lt _ (Nat.two_pow_pos dw), mask]
      · simpa [hn] using hb n

open Sparkle.IR.Semantics in
/-- The combinational fold preserves boundedness on fragment bodies:
    every assign stores a masked value at an agreeing width, and every
    combo read lands masked at the declared data width. -/
theorem evalAssigns_bounded {wof we wires} (mems : MEnv)
    {body : List Sparkle.IR.AST.Stmt} (hB : BFrag wof we wires body) :
    ∀ {env0 envF : Env}, Bounded we env0 →
    evalAssigns we mems body env0 = some envF → Bounded we envF := by
  induction hB with
  | nil =>
    intro env0 envF hb h
    cases h
    exact hb
  | assign hs hwl hx hrest ih =>
    rename_i l x rest
    intro env0 envF hb h
    simp only [evalAssigns, Option.bind_eq_bind] at h
    cases hv : evalExpr we env0 x with
    | none => rw [hv] at h; exact absurd h (by simp)
    | some v =>
      rw [hv] at h
      simp only [Option.bind_some] at h
      refine ih ?_ h
      intro n
      by_cases hn : n = l
      · subst hn
        have := sfrag_eval_bounded (hx env0 hb) hb v hv
        rw [hwl] at this
        simpa using this
      · simpa [hn] using hb n
  | reg hso hsc hsr hx hrw hw0 hwrst hrest ih =>
    intro env0 envF hb h
    simp only [evalAssigns] at h
    exact ih hb h
  | mem hsn hsc hwp hrp hdw hrest ih =>
    rename_i name aw dw clk wa wd wen ra rd cr ew er rest
    intro env0 envF hb h
    simp only [evalAssigns] at h
    cases cr with
    | false => exact ih hb h
    | true =>
      simp only [if_true, Option.bind_eq_bind] at h
      cases hc : comboReads we mems name aw dw ((ra, rd) :: er) env0 with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some env1 =>
        rw [hc] at h
        simp only [Option.bind_some] at h
        refine ih ?_ h
        exact comboReads_bounded
          (fun p hp => (hrp p hp).2.2) hb hc

open Sparkle.IR.Semantics in
/-- Combinational phase: the image body folds to the same environment. -/
theorem fold_eq {wof we wires} (mems : MEnv)
    {body body' : List Sparkle.IR.AST.Stmt}
    (hB : BFrag wof we wires body)
    (hI : bodyImage wof wires body = some body') :
    ∀ env0, Bounded we env0 →
      evalAssigns we mems body' env0 = evalAssigns we mems body env0 := by
  induction hB generalizing body' with
  | nil =>
    intro env0 _
    simp only [bodyImage] at hI
    cases hI
    rfl
  | assign hs hwl hx hrest ih =>
    rename_i l x rest
    obtain ⟨x'', hbind, hwid, _⟩ :=
      roundtrip_sem (hx (fun _ => 0) (bounded_zero we))
    have hval : ∀ env, Bounded we env →
        evalExpr we env x'' = evalExpr we env x := by
      intro env hbe
      obtain ⟨x3, hb3, _, hv3⟩ := roundtrip_sem (hx env hbe)
      rw [hbind] at hb3
      cases hb3
      exact hv3
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hbind
    obtain ⟨img, hImg, rest', hRest, rfl⟩ :
        ∃ img, stmtImage wof wires (.assign l x) = some img
          ∧ ∃ rest', bodyImage wof wires rest = some rest'
          ∧ body' = img ++ rest' := by
      simp only [bodyImage, Option.bind_eq_bind] at hI
      cases hS : stmtImage wof wires (.assign l x) with
      | none => rw [hS] at hI; simp at hI
      | some img =>
        rw [hS] at hI
        cases hR : bodyImage wof wires rest with
        | none => rw [hR] at hI; simp at hI
        | some rest' =>
          rw [hR] at hI
          simp only [Option.bind_some, Option.some_inj] at hI
          exact ⟨img, rfl, rest', rfl, hI.symm⟩
    have hImgEq : img = [.assign l x''] := by
      simp [stmtImage, Tools.SVParser.EmitAst.emitAstStmt, hex1, hs,
        lowerTItem, hex2] at hImg
      exact hImg.symm
    subst hImgEq
    intro env0 hb0
    simp only [List.cons_append, List.nil_append, evalAssigns,
      Option.bind_eq_bind, hval env0 hb0]
    cases hv : evalExpr we env0 x with
    | none => rfl
    | some v =>
      refine ih hRest _ ?_
      intro n
      by_cases hn : n = l
      · subst hn
        have := sfrag_eval_bounded (hx env0 hb0) hb0 v hv
        rw [hwl] at this
        simpa using this
      · simpa [hn] using hb0 n
  | reg hso hsc hsr hx hrw hw0 hwrst hrest ih =>
    rename_i out clk rst kind x init rest
    obtain ⟨x'', hbind, hwid, _⟩ :=
      roundtrip_sem (hx (fun _ => 0) (bounded_zero we))
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hbind
    obtain ⟨img, hImg, rest', hRest, rfl⟩ :
        ∃ img, stmtImage wof wires (.register out clk (rst, kind) x init)
            = some img
          ∧ ∃ rest', bodyImage wof wires rest = some rest'
          ∧ body' = img ++ rest' := by
      simp only [bodyImage, Option.bind_eq_bind] at hI
      cases hS : stmtImage wof wires (.register out clk (rst, kind) x init) with
      | none => rw [hS] at hI; simp at hI
      | some img =>
        rw [hS] at hI
        cases hR : bodyImage wof wires rest with
        | none => rw [hR] at hI; simp at hI
        | some rest' =>
          rw [hR] at hI
          simp only [Option.bind_some, Option.some_inj] at hI
          exact ⟨img, rfl, rest', rfl, hI.symm⟩
    -- the image register: mux-guarded input, encoded init
    have hne : (we out == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    obtain ⟨iv, hivShape⟩ :
        ∃ iv, img = [.register out clk (rst, .asynchronous) x'' iv] := by
      by_cases hneg : init < 0
      · refine ⟨Int.ofNat (Tools.SVParser.EmitAst.encodeConst init (we out)),
          ?_⟩
        simp [stmtImage, Tools.SVParser.EmitAst.emitAstStmt,
          show Tools.SVParser.EmitAst.regResetWidth wires out = we out from hrw,
          Tools.SVParser.EmitAst.emitAstExpr, hso, hsc, hsr,
          hex1, hne, if_pos hneg, lowerTItem, lowerT, hex2] at hImg
        exact hImg.symm
      · refine ⟨max init 0, ?_⟩
        simp [stmtImage, Tools.SVParser.EmitAst.emitAstStmt,
          show Tools.SVParser.EmitAst.regResetWidth wires out = we out from hrw,
          Tools.SVParser.EmitAst.emitAstExpr, hso, hsc, hsr,
          hex1, hne, if_neg hneg, lowerTItem, lowerT, hex2] at hImg
        exact hImg.symm
    subst hivShape
    intro env0 hb0
    simp only [List.cons_append, List.nil_append, evalAssigns]
    exact ih hRest env0 hb0
  | mem hsn hsc hwp hrp hdw hrest ih =>
    rename_i name aw dw clk wa wd wen ra rd cr ew er rest
    obtain ⟨img, rest', hImg, hRest, rfl⟩ := cons_image_shape hI
    simp only [stmtImage] at hImg
    obtain ⟨mi, hMI, hIL⟩ := Option.map_eq_some_iff.mp hImg
    obtain ⟨w0a, w0d, w0e, extraW, ra0, rd0, extraR, hW, hR, rfl⟩ :=
      memImage_inv hMI
    have hdw' : (if dw ≤ 1 then 1 else dw) = dw := by
      by_cases hh : dw ≤ 1
      · simp [hh]; omega
      · simp [hh]
    rw [hsn, hsc, hdw'] at hIL
    subst hIL
    intro env0 hb0
    simp only [List.cons_append, List.nil_append, evalAssigns]
    cases cr with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      exact ih hRest env0 hb0
    | true =>
      simp only [if_true, Option.bind_eq_bind,
        lowerReadPorts_sem_combo dw _ hR hrp mems name aw env0 hb0]
      cases hc : comboReads we mems name aw dw ((ra, rd) :: er) env0 with
      | none => rfl
      | some envX =>
        simp only [Option.bind_some]
        exact ih hRest envX
          (comboReads_bounded (fun p hp => (hrp p hp).2.2) hb0 hc)

open Sparkle.IR.Semantics in
/-- Register phase: the image body computes the same next-state list. -/
theorem regNexts_eq {wof we wires} (mems : MEnv)
    {body body' : List Sparkle.IR.AST.Stmt}
    (hB : BFrag wof we wires body)
    (hI : bodyImage wof wires body = some body') :
    ∀ envF, Bounded we envF →
      regNexts we mems body' envF = regNexts we mems body envF := by
  induction hB generalizing body' with
  | nil =>
    intro envF _
    simp only [bodyImage] at hI
    cases hI
    rfl
  | assign hs hwl hx hrest ih =>
    rename_i l x rest
    obtain ⟨x'', hbind, _, _⟩ :=
      roundtrip_sem (hx (fun _ => 0) (bounded_zero we))
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hbind
    obtain ⟨img, hImg, rest', hRest, rfl⟩ :
        ∃ img, stmtImage wof wires (.assign l x) = some img
          ∧ ∃ rest', bodyImage wof wires rest = some rest'
          ∧ body' = img ++ rest' := by
      simp only [bodyImage, Option.bind_eq_bind] at hI
      cases hS : stmtImage wof wires (.assign l x) with
      | none => rw [hS] at hI; simp at hI
      | some img =>
        rw [hS] at hI
        cases hR : bodyImage wof wires rest with
        | none => rw [hR] at hI; simp at hI
        | some rest' =>
          rw [hR] at hI
          simp only [Option.bind_some, Option.some_inj] at hI
          exact ⟨img, rfl, rest', rfl, hI.symm⟩
    have hImgEq : img = [.assign l x''] := by
      simp [stmtImage, Tools.SVParser.EmitAst.emitAstStmt, hex1, hs,
        lowerTItem, hex2] at hImg
      exact hImg.symm
    subst hImgEq
    intro envF hbF
    simp only [List.cons_append, List.nil_append, regNexts]
    exact ih hRest envF hbF
  | reg hso hsc hsr hx hrw hw0 hwrst hrest ih =>
    rename_i out clk rst kind x init rest
    obtain ⟨x'', hbind, hwid, _⟩ :=
      roundtrip_sem (hx (fun _ => 0) (bounded_zero we))
    have hval : ∀ env, Bounded we env →
        evalExpr we env x'' = evalExpr we env x := by
      intro env hbe
      obtain ⟨x3, hb3, _, hv3⟩ := roundtrip_sem (hx env hbe)
      rw [hbind] at hb3
      cases hb3
      exact hv3
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hbind
    obtain ⟨img, hImg, rest', hRest, rfl⟩ :
        ∃ img, stmtImage wof wires (.register out clk (rst, kind) x init)
            = some img
          ∧ ∃ rest', bodyImage wof wires rest = some rest'
          ∧ body' = img ++ rest' := by
      simp only [bodyImage, Option.bind_eq_bind] at hI
      cases hS : stmtImage wof wires (.register out clk (rst, kind) x init) with
      | none => rw [hS] at hI; simp at hI
      | some img =>
        rw [hS] at hI
        cases hR : bodyImage wof wires rest with
        | none => rw [hR] at hI; simp at hI
        | some rest' =>
          rw [hR] at hI
          simp only [Option.bind_some, Option.some_inj] at hI
          exact ⟨img, rfl, rest', rfl, hI.symm⟩
    have hne : (we out == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    obtain ⟨iv, hivShape, hivEnc⟩ :
        ∃ iv, img = [.register out clk (rst, .asynchronous) x'' iv]
          ∧ encodeInit iv (we out) = encodeInit init (we out) := by
      by_cases hneg : init < 0
      · refine ⟨Int.ofNat (Tools.SVParser.EmitAst.encodeConst init (we out)),
          ?_, encodeInit_image init (we out)⟩
        simp [stmtImage, Tools.SVParser.EmitAst.emitAstStmt,
          show Tools.SVParser.EmitAst.regResetWidth wires out = we out from hrw,
          Tools.SVParser.EmitAst.emitAstExpr, hso, hsc, hsr,
          hex1, hne, if_pos hneg, lowerTItem, lowerT, hex2] at hImg
        exact hImg.symm
      · have hmax : (max init 0 : Int) = init := by omega
        refine ⟨max init 0, ?_, by rw [hmax]⟩
        simp [stmtImage, Tools.SVParser.EmitAst.emitAstStmt,
          show Tools.SVParser.EmitAst.regResetWidth wires out = we out from hrw,
          Tools.SVParser.EmitAst.emitAstExpr, hso, hsc, hsr,
          hex1, hne, if_neg hneg, lowerTItem, lowerT, hex2] at hImg
        exact hImg.symm
    subst hivShape
    intro envF hbF
    simp only [List.cons_append, List.nil_append, regNexts,
      Option.bind_eq_bind]
    -- the image register carries the roundtripped input DIRECTLY (the
    -- shipping stripResetMux pass removed the redundant reset mux);
    -- inits agree up to encode
    rw [hval envF hbF]
    cases hX : evalExpr we envF x with
    | none => simp
    | some vx =>
      simp only [Option.bind_some]
      simp [ih hRest envF hbF, hivEnc]
  | mem hsn hsc hwp hrp hdw hrest ih =>
    rename_i name aw dw clk wa wd wen ra rd cr ew er rest
    obtain ⟨img, rest', hImg, hRest, rfl⟩ := cons_image_shape hI
    simp only [stmtImage] at hImg
    obtain ⟨mi, hMI, hIL⟩ := Option.map_eq_some_iff.mp hImg
    obtain ⟨w0a, w0d, w0e, extraW, ra0, rd0, extraR, hW, hR, rfl⟩ :=
      memImage_inv hMI
    have hdw' : (if dw ≤ 1 then 1 else dw) = dw := by
      by_cases hh : dw ≤ 1
      · simp [hh]; omega
      · simp [hh]
    rw [hsn, hsc, hdw'] at hIL
    subst hIL
    intro envF hbF
    simp only [List.cons_append, List.nil_append, regNexts]
    cases cr with
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.bind_eq_bind,
        lowerReadPorts_sem_sync _ hR
          (fun p hp => ⟨(hrp p hp).1, (hrp p hp).2.1⟩)
          mems name aw dw envF hbF]
      cases syncReadLatches we mems name aw dw ((ra, rd) :: er) envF with
      | none => rfl
      | some latches =>
        simp only [Option.bind_some, ih hRest envF hbF]
    | true =>
      simp only [if_true]
      exact ih hRest envF hbF

open Sparkle.IR.Semantics in
/-- Memory phase: the image body computes the same post-write memory
    state. -/
theorem memNexts_eq {wof we wires} {body body' : List Sparkle.IR.AST.Stmt}
    (hB : BFrag wof we wires body)
    (hI : bodyImage wof wires body = some body') :
    ∀ mems envF, Bounded we envF →
      memNexts we body' mems envF = memNexts we body mems envF := by
  induction hB generalizing body' with
  | nil =>
    intro mems envF _
    simp only [bodyImage] at hI
    cases hI
    rfl
  | assign hs hwl hx hrest ih =>
    rename_i l x rest
    obtain ⟨img, rest', hImg, hRest, rfl⟩ := cons_image_shape hI
    obtain ⟨x'', hbind, _, _⟩ :=
      roundtrip_sem (hx (fun _ => 0) (bounded_zero we))
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hbind
    have hImgEq : img = [.assign l x''] := by
      simp [stmtImage, Tools.SVParser.EmitAst.emitAstStmt, hex1, hs,
        lowerTItem, hex2] at hImg
      exact hImg.symm
    subst hImgEq
    intro mems envF hbF
    simp only [List.cons_append, List.nil_append, memNexts]
    exact ih hRest mems envF hbF
  | reg hso hsc hsr hx hrw hw0 hwrst hrest ih =>
    rename_i out clk rst kind x init rest
    obtain ⟨img, rest', hImg, hRest, rfl⟩ := cons_image_shape hI
    obtain ⟨x'', hbind, _, _⟩ :=
      roundtrip_sem (hx (fun _ => 0) (bounded_zero we))
    obtain ⟨ex, hex1, hex2⟩ := Option.bind_eq_some_iff.mp hbind
    have hne : (we out == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    obtain ⟨iv, hivShape⟩ :
        ∃ iv, img = [.register out clk (rst, .asynchronous) x'' iv] := by
      by_cases hneg : init < 0
      · refine ⟨Int.ofNat (Tools.SVParser.EmitAst.encodeConst init (we out)),
          ?_⟩
        simp [stmtImage, Tools.SVParser.EmitAst.emitAstStmt,
          show Tools.SVParser.EmitAst.regResetWidth wires out = we out from hrw,
          Tools.SVParser.EmitAst.emitAstExpr, hso, hsc, hsr,
          hex1, hne, if_pos hneg, lowerTItem, lowerT, hex2] at hImg
        exact hImg.symm
      · refine ⟨max init 0, ?_⟩
        simp [stmtImage, Tools.SVParser.EmitAst.emitAstStmt,
          show Tools.SVParser.EmitAst.regResetWidth wires out = we out from hrw,
          Tools.SVParser.EmitAst.emitAstExpr, hso, hsc, hsr,
          hex1, hne, if_neg hneg, lowerTItem, lowerT, hex2] at hImg
        exact hImg.symm
    subst hivShape
    intro mems envF hbF
    simp only [List.cons_append, List.nil_append, memNexts]
    exact ih hRest mems envF hbF
  | mem hsn hsc hwp hrp hdw hrest ih =>
    rename_i name aw dw clk wa wd wen ra rd cr ew er rest
    obtain ⟨img, rest', hImg, hRest, rfl⟩ := cons_image_shape hI
    simp only [stmtImage] at hImg
    obtain ⟨mi, hMI, hIL⟩ := Option.map_eq_some_iff.mp hImg
    obtain ⟨w0a, w0d, w0e, extraW, ra0, rd0, extraR, hW, hR, rfl⟩ :=
      memImage_inv hMI
    have hdw' : (if dw ≤ 1 then 1 else dw) = dw := by
      by_cases hh : dw ≤ 1
      · simp [hh]; omega
      · simp [hh]
    rw [hsn, hsc, hdw'] at hIL
    subst hIL
    intro mems envF hbF
    simp only [List.cons_append, List.nil_append, memNexts,
      Option.bind_eq_bind,
      lowerWritePorts_sem _ hW hwp envF hbF name aw dw mems]
    cases memWritePorts we envF name aw dw ((wa, wd, wen) :: ew) mems with
    | none => rfl
    | some memsX =>
      simp only [Option.bind_some]
      exact ih hRest memsX envF hbF

open Sparkle.IR.Semantics in
/-- **The module-level roundtrip theorem** (assign+register bodies):
    one cycle of the emit-then-lower image is one cycle of the original —
    the final environment, the register updates, and the memory state. -/
theorem step_roundtrip {wof we wires} {body body' : List Sparkle.IR.AST.Stmt}
    (hB : BFrag wof we wires body)
    (hI : bodyImage wof wires body = some body') (env0 : Env)
    (hb0 : Bounded we env0) (mems : MEnv) :
    stepModule we body' env0 mems = stepModule we body env0 mems := by
  unfold stepModule
  rw [fold_eq mems hB hI env0 hb0]
  cases hF : evalAssigns we mems body env0 with
  | none => rfl
  | some envF =>
    have hbF : Bounded we envF := evalAssigns_bounded mems hB hb0 hF
    simp [regNexts_eq mems hB hI envF hbF, memNexts_eq hB hI mems envF hbF]

open Sparkle.IR.Semantics in
/-- **Trace equivalence**: the image body produces the same observable
    trace for any number of cycles, any initial state, and any input
    seeding discipline — the multi-cycle corollary of `step_roundtrip`,
    by induction on the cycle count. -/
theorem trace_roundtrip {wof we wires} {body body' : List Sparkle.IR.AST.Stmt}
    (hB : BFrag wof we wires body)
    (hI : bodyImage wof wires body = some body')
    (seed : Nat → (String → Nat) → Env)
    (hseed : ∀ t st, Bounded we (seed t st)) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
      runModule we body' seed k st mems
        = runModule we body seed k st mems := by
  intro k
  induction k with
  | zero => intro st mems; rfl
  | succ k ih =>
    intro st mems
    simp only [runModule, Option.bind_eq_bind,
      step_roundtrip hB hI (seed k st) (hseed k st) mems]
    cases stepModule we body (seed k st) mems with
    | none => rfl
    | some p => simp [ih]

/- ------------------------------------------------------------------ -/
/- Module-boundary composition: the shipping module lowering re-sorts
   the body, so its output is (validated to be) a well-ordered
   PERMUTATION of the statement-wise image; reorder invariance then
   lifts step/trace roundtrip over the whole pipeline. -/

open Sparkle.IR.Semantics Sparkle.IR.Reorder in
/-- The checkable side conditions bundled as one boolean: `body'` is a
    permutation of `bimg`, both are well-ordered, memory names and
    update keys are unique. -/
def bodyReorderCheck (body' bimg : List Sparkle.IR.AST.Stmt) : Bool :=
  isPermOf body' bimg
  && woCheck [] body'
  && woCheck [] bimg
  && decide ((body'.filterMap stmtMemName).Nodup)
  && decide ((nextKeys body').Nodup)

open Sparkle.IR.Semantics Sparkle.IR.Reorder in
/-- **Full-pipeline trace roundtrip**: if the shipping lowering's
    output `body'` passes `bodyReorderCheck` against the statement-wise
    image of `body`, it produces the SAME TRACE as `body` — for any
    cycle count, seeding, and initial state. -/
theorem body_trace_roundtrip {wof we wires}
    {body bimg body' : List Sparkle.IR.AST.Stmt}
    (hB : BFrag wof we wires body)
    (hI : bodyImage wof wires body = some bimg)
    (hchk : bodyReorderCheck body' bimg = true)
    (seed : Nat → (String → Nat) → Env)
    (hseed : ∀ t st, Bounded we (seed t st))
    (k : Nat) (st : String → Nat) (mems : MEnv) :
    runModule we body' seed k st mems = runModule we body seed k st mems := by
  simp only [bodyReorderCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨hperm, hwo1⟩, hwo2⟩, hmem⟩, hkeys⟩ := hchk
  rw [runModule_perm we (isPermOf_sound hperm) (woCheck_sound _ _ hwo1)
      (woCheck_sound _ _ hwo2) hmem hkeys seed k st mems]
  exact trace_roundtrip hB hI seed hseed k st mems

/-- Is this statement inside the reorder fragment?  (Boolean twin of
    `SimpleStmt` — everything except instances.) -/
def simpleStmtB : Sparkle.IR.AST.Stmt → Bool
  | .inst _ _ _ => false
  | _ => true

/-- Verdicts of the per-module end-to-end validation. -/
inductive TraceCheck where
  /-- the trace theorem's checkable hypotheses HOLD for the shipping
      output -/
  | ok
  /-- the shipping output differs from the raw image, but matches once
      the image passes through the same shipping optimizer — the module
      sits behind the optimizer boundary (covered by `#verify_emit`
      translation validation, not by the trace theorem) -/
  | optRewritten
  /-- outside the fragment (an image-less statement or an instance) -/
  | outside
  /-- genuine mismatch -/
  | bad
  deriving Repr, DecidableEq

/-- End-to-end validation for one module: run the SHIPPING pipeline on
    the module's own emission and check its output against the
    statement-wise twin image with `bodyReorderCheck`. -/
def bodyTraceCheck (m : Sparkle.IR.AST.Module) : TraceCheck :=
  let wof : String → Option Nat := fun n =>
    ((m.wires ++ m.inputs ++ m.outputs).find? (fun p =>
      Sparkle.Backend.Verilog.sanitizeName p.name == n)).bind fun p =>
      match p.ty with
      | .bitVector w => some w
      | .bit => some 1
      | _ => none
  if !(m.body.all simpleStmtB) then .outside
  else
    match (m.body.mapM (stmtImage wof m.wires)).map List.flatten with
    | none => .outside
    | some bimg =>
      match Tools.SVParser.Lower.parseAndLowerHierarchical
          (Sparkle.Backend.Verilog.emitModule m) with
      | .error _ => .bad
      | .ok d =>
        let body' := d.modules.foldl
          (fun acc (lm : Sparkle.IR.AST.Module) => acc ++ lm.body) []
        if bodyReorderCheck body' bimg then .ok
        else
          -- classify: does the image agree once optimized the same way?
          let imgDesign : Sparkle.IR.AST.Design :=
            { topModule := m.name, modules := [{ m with body := bimg }] }
          let opt := Tools.SVParser.Lower.stripResetMuxDesign
            (Sparkle.IR.Optimize.optimizeDesign imgDesign)
          let bimgOpt := opt.modules.foldl
            (fun acc (lm : Sparkle.IR.AST.Module) => acc ++ lm.body) []
          if Sparkle.IR.Reorder.isPermOf body' bimgOpt then .optRewritten
          else .bad

/- ------------------------------------------------------------------ -/
/- Coverage census: a decidable mirror of the env-independent SFrag /
   BFrag constructors.  `we` is INDUCED from the width oracle
   (`(wof n).getD 0`), which discharges the wof/we agreement conditions
   by construction.  The env-dependent constructors (sliceRefElide's
   env bound, cmpS's value bounds) are excluded — they are unusable in
   the env-UNIFORM form BFrag needs anyway (future work: a bounded-env
   refinement, since every write in the semantics is masked).
   Census-only for now: the soundness bridge (sfragCheck → ∀ env,
   SFrag) is mechanical and deferred. -/

open Sparkle.IR.Semantics in
mutual
def sfragCheck (wof : String → Option Nat) : Sparkle.IR.AST.Expr → Bool
  | .ref n =>
    Sparkle.Backend.Verilog.sanitizeName n == n && (wof n).isSome
  | .const _ w => decide (0 < w)
  | .op .mux [c, t, f] =>
    decide (widthOf (fun n => (wof n).getD 0) f
      = widthOf (fun n => (wof n).getD 0) t)
    && sfragCheck wof c && sfragCheck wof t && sfragCheck wof f
  | .op .neg [x] => sfragCheck wof x
  | .op .not [x] =>
    (match Tools.SVParser.EmitAst.exprWidthT wof x with
     | some w =>
       decide (widthOf (fun n => (wof n).getD 0) x = w)
         && decide (w ≤ 32) && decide (0 < w)
     | none => false)
    && sfragCheck wof x
  | .op .asr [x, y] =>
    (match x with | .concat _ => false | _ => true)
    && (match y with | .concat _ => false | _ => true)
    && sfragCheck wof x && sfragCheck wof y
  | .op op [a, b] =>
    (if op = .lt_s ∨ op = .le_s ∨ op = .gt_s ∨ op = .ge_s then
      -- signed compares: value bounds come from Bounded via
      -- sfrag_eval_bounded; only the width agreements are checked
      (match Tools.SVParser.EmitAst.exprWidthT wof a,
             Tools.SVParser.EmitAst.exprWidthT wof b with
       | some w, some w' =>
         w == w'
         && decide (widthOf (fun n => (wof n).getD 0) a = w)
         && decide (widthOf (fun n => (wof n).getD 0) b = w)
         && decide (0 < w)
       | _, _ => false)
    else (Tools.SVParser.EmitAst.binOpOf op).isSome)
    && sfragCheck wof a && sfragCheck wof b
  | .slice (.ref n) hi lo =>
    Sparkle.Backend.Verilog.sanitizeName n == n
    && ((wof n).isNone
        || (lo == 0 && hi + 1 == (wof n).getD 0)  -- exact elide (Bounded)
        || (!(lo == 0 && (wof n).getD 0 ≤ hi + 1)
            && decide (hi < (wof n).getD 0)))
  | .slice (.concat [.const 0 w, y]) hi lo =>
    if lo == 0 && hi + 1 == w then decide (0 < w) && sfragCheck wof y
    else
      -- non-canonical: the general compound-slice arm fires
      decide (lo ≤ hi)
      && decide (hi < widthOf (fun n => (wof n).getD 0)
          (.concat [.const 0 w, y]))
      && decide (hi < 4294967296)
      && sfragCheck wof (.concat [.const 0 w, y])
  | .slice x hi lo =>
    (match x with
     | .ref _ => false
     | _ => true)
    && decide (lo ≤ hi)
    && decide (hi < widthOf (fun n => (wof n).getD 0) x)
    && decide (hi < 4294967296)
    && sfragCheck wof x
  | .concat args => sfragCheckList wof args
  | _ => false

def sfragCheckList (wof : String → Option Nat) :
    List Sparkle.IR.AST.Expr → Bool
  | [] => true
  | a :: rest =>
    (match a with
     | .op _ _ =>
       match Tools.SVParser.EmitAst.exprWidthT wof a with
       | some w =>
         decide (0 < w)
           && decide (widthOf (fun n => (wof n).getD 0) a = w)
       | none => false
     | _ => true)
    && sfragCheck wof a && sfragCheckList wof rest
end

open Sparkle.IR.Semantics in
/-- Decidable mirror of BFrag (census). -/
def bfragCheck (wof : String → Option Nat)
    (wires : List Sparkle.IR.AST.Port) :
    List Sparkle.IR.AST.Stmt → Bool
  | [] => true
  | .assign l x :: rest =>
    Sparkle.Backend.Verilog.sanitizeName l == l
    && decide (Sparkle.IR.Semantics.widthOf (fun n => (wof n).getD 0) x
        = (wof l).getD 0)
    && sfragCheck wof x && bfragCheck wof wires rest
  | .register out clk (rst, _) x _ :: rest =>
    Sparkle.Backend.Verilog.sanitizeName out == out
    && Sparkle.Backend.Verilog.sanitizeName clk == clk
    && Sparkle.Backend.Verilog.sanitizeName rst == rst
    && sfragCheck wof x
    && decide (Tools.SVParser.EmitAst.regResetWidth wires out
        = (wof out).getD 0)
    && decide (0 < (wof out).getD 0)
    && decide (0 < (wof rst).getD 0)
    && bfragCheck wof wires rest
  | .memory name _ dw clk wa wd wen ra rd _ ew er :: rest =>
    Sparkle.Backend.Verilog.sanitizeName name == name
    && Sparkle.Backend.Verilog.sanitizeName clk == clk
    && ((wa, wd, wen) :: ew).all (fun p =>
        sfragCheck wof p.1 && sfragCheck wof p.2.1
          && sfragCheck wof p.2.2)
    && ((ra, rd) :: er).all (fun p =>
        sfragCheck wof p.1
          && (Sparkle.Backend.Verilog.sanitizeName p.2 == p.2)
          && decide ((wof p.2).getD 0 = dw))
    && decide (0 < dw)
    && bfragCheck wof wires rest
  | .inst _ _ _ :: _ => false

/-- The module's width oracle: wires and ports, by sanitized name —
    the same map the shipping statement emitter uses. -/
def moduleWof (m : Sparkle.IR.AST.Module) : String → Option Nat := fun n =>
  ((m.wires ++ m.inputs ++ m.outputs).find? (fun p =>
    Sparkle.Backend.Verilog.sanitizeName p.name == n)).bind fun p =>
    match p.ty with
    | .bitVector w => some w
    | .bit => some 1
    | _ => none

/-- Census verdict for one module: is its body fully inside the PROVEN
    semantic fragment (BFrag with the induced width env)? -/
def semFragCheck (m : Sparkle.IR.AST.Module) : Bool :=
  bfragCheck (moduleWof m) m.wires m.body

open Sparkle.IR.Semantics in
/-- The checker's GENERAL slice arm fires on every slice-of-concat
    except the canonical cast-encode shape. -/
theorem sfragCheck_slice_concat_general {wof : String → Option Nat}
    (args : List Sparkle.IR.AST.Expr) (hi lo : Nat)
    (hne : ∀ w y, args ≠ [Sparkle.IR.AST.Expr.const 0 w, y]) :
    sfragCheck wof (.slice (.concat args) hi lo)
      = (decide (lo ≤ hi)
        && decide (hi < widthOf (fun n => (wof n).getD 0) (.concat args))
        && decide (hi < 4294967296)
        && sfragCheck wof (.concat args)) := by
  match args, hne with
  | [], _ => rfl
  | [a], _ =>
    rw [sfragCheck.eq_def]
    split <;>
      first
        | rfl
        | simp_all
        | (rename_i heq
           injection heq with he hh hl
           subst he hh hl
           rfl)
  | a :: b :: c :: rest, _ =>
    rw [sfragCheck.eq_def]
    split <;>
      first
        | rfl
        | simp_all
        | (rename_i heq
           injection heq with he hh hl
           subst he hh hl
           rfl)
  | [a, b], hne =>
    match a, hne with
    | .ref _, _ | .op _ _, _ | .concat _, _ | .slice _ _ _, _
    | .sliceDim _ _ _, _ | .index _ _, _ =>
      rw [sfragCheck.eq_def]
      split <;>
        first
          | rfl
          | simp_all
          | (rename_i heq
             injection heq with he hh hl
             subst he hh hl
             rfl)
    | .const v w, hne =>
      by_cases hv : v = 0
      · subst hv
        exact absurd rfl (hne w b)
      · rw [sfragCheck.eq_def]
        split <;>
          first
            | rfl
            | simp_all
            | (rename_i heq
               injection heq with he hh hl
               subst he hh hl
               rfl)

open Sparkle.IR.Semantics in
/-- Soundness of the census checker: a checked expression is in the
    semantic fragment, for EVERY environment, with the width env
    induced from the oracle.  Proved by the checker's own functional
    induction, so the case split matches the checker arm for arm. -/
theorem sfragCheck_sound (wof : String → Option Nat)
    (e : Sparkle.IR.AST.Expr) (h : sfragCheck wof e = true) :
    ∀ env, Bounded (fun n => (wof n).getD 0) env →
      SFrag wof (fun n => (wof n).getD 0) env e := by
  revert h
  induction e using sfragCheck.induct (motive_2 := fun args =>
    sfragCheckList wof args = true →
    ∀ env, Bounded (fun n => (wof n).getD 0) env →
      SFrag wof (fun n => (wof n).getD 0) env (.concat args)) with
  | case1 n =>
    intro h env _
    simp only [sfragCheck, Bool.and_eq_true, beq_iff_eq,
      Option.isSome_iff_exists] at h
    obtain ⟨hs, w, hw⟩ := h
    exact SFrag.ref n hs (by simp [hw])
  | case2 v w =>
    intro h env _
    simp only [sfragCheck, decide_eq_true_eq] at h
    exact SFrag.const v w h
  | case3 c t f ihc iht ihf =>
    intro h env hbe
    simp only [sfragCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact SFrag.mux h.1.1.1 (ihc h.1.1.2 env hbe) (iht h.1.2 env hbe)
      (ihf h.2 env hbe)
  | case4 x ihx =>
    intro h env hbe
    exact SFrag.neg (ihx h env hbe)
  | case5 x ihx =>
    intro h env hbe
    simp only [sfragCheck, Bool.and_eq_true] at h
    obtain ⟨hcond, hx⟩ := h
    cases hwT : Tools.SVParser.EmitAst.exprWidthT wof x with
    | none => rw [hwT] at hcond; cases hcond
    | some w =>
      rw [hwT] at hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact SFrag.not w hwT hcond.1.1 hcond.1.2 hcond.2
        (ihx hx env hbe)
  | case6 x y ihx ihy =>
    intro h env hbe
    simp only [sfragCheck, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hnx, hny⟩, hx⟩, hy⟩ := h
    refine SFrag.asr ?_ ?_ (ihx hx env hbe) (ihy hy env hbe)
    · intro l hEq; subst hEq; simp at hnx
    · intro l hEq; subst hEq; simp at hny
  | case7 op a b hne iha ihb =>
    intro h env hbe
    simp only [sfragCheck, Bool.and_eq_true] at h
    have hop := h.1.1
    have ha := h.1.2
    have hb' := h.2
    by_cases hsg : op = .lt_s ∨ op = .le_s ∨ op = .gt_s ∨ op = .ge_s
    · rw [if_pos hsg] at hop
      cases hwa : Tools.SVParser.EmitAst.exprWidthT wof a with
      | none => rw [hwa] at hop; cases hop
      | some w =>
      cases hwb : Tools.SVParser.EmitAst.exprWidthT wof b with
      | none => rw [hwa, hwb] at hop; cases hop
      | some w' =>
      rw [hwa, hwb] at hop
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hop
      obtain ⟨⟨⟨hww, hwsa⟩, hwsb⟩, hw0⟩ := hop
      subst hww
      have hfa := iha ha env hbe
      have hfb := ihb hb' env hbe
      exact SFrag.cmpS op hsg w hwa hwb hwsa hwsb hw0
        (fun v hv => by
          have := sfrag_eval_bounded hfa hbe v hv
          rwa [hwsa] at this)
        (fun v hv => by
          have := sfrag_eval_bounded hfb hbe v hv
          rwa [hwsb] at this)
        hfa hfb
    · rw [if_neg hsg] at hop
      exact SFrag.binop op hop (iha ha env hbe) (ihb hb' env hbe)
  | case8 n hi lo =>
    intro h env hbe
    simp only [sfragCheck, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hs, hkeep⟩ := h
    cases hw : wof n with
    | none =>
      exact SFrag.sliceRefKeep n hi lo hs (Or.inl hw) (Or.inl hw)
        (Or.inl hw)
    | some w =>
      rw [hw] at hkeep
      simp only [Option.isNone_some, Bool.false_or, Bool.or_eq_true,
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        beq_iff_eq, Option.getD_some] at hkeep
      cases hkeep with
      | inl helide =>
        -- exact full-width select: the ELIDE constructor, its range
        -- condition discharged by Bounded
        obtain ⟨hlo, hhw⟩ := helide
        subst hlo
        have henv : env n < 2 ^ ((fun m => (wof m).getD 0) n) := hbe n
        rw [show ((fun m => (wof m).getD 0) n) = w by simp [hw]] at henv
        have := SFrag.sliceRefElide (wof := wof)
          (we := fun m => (wof m).getD 0) (env := env) n hi hs
          (by simp [hw]) (by simp [hw]; omega) (by simp [hw]; omega)
        exact this
      | inr hkeep =>
        refine SFrag.sliceRefKeep n hi lo hs (Or.inr ?_)
          (Or.inr (by simpa [hw] using hkeep.2)) (Or.inr (by simp [hw]))
        intro ⟨h0, hle⟩
        rcases Bool.and_eq_false_iff.mp hkeep.1 with hlo0 | hgt
        · simp [h0] at hlo0
        · simp only [decide_eq_false_iff_not] at hgt
          exact hgt (by simpa [hw] using hle)
  | case9 w y hi lo hguard ihy =>
    intro h env hbe
    simp only [Bool.and_eq_true, beq_iff_eq] at hguard
    obtain ⟨hlo, hhw⟩ := hguard
    subst hlo
    have hhi : hi = w - 1 := by omega
    subst hhi
    simp only [sfragCheck] at h
    rw [if_pos (by simp [hhw])] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact SFrag.castEnc w h.1 (ihy h.2 env hbe)
  | case10 w y hi lo hguard ihc =>
    intro h env hbe
    simp only [sfragCheck] at h
    rw [if_neg hguard] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine SFrag.sliceCompound hi lo h.1.1.1 h.1.1.2 h.1.2
      (fun _ hEq => nomatch hEq)
      (fun w' y' hEq hand => ?_) (ihc h.2 env hbe)
    -- the guard is FALSE, so the canonical-shape condition cannot hold
    have hww : w' = w := by
      injection hEq with hl
      injection hl with h1 _
      injection h1 with _ hww
      omega
    subst hww
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff,
      beq_eq_false_iff_ne] at hguard
    rcases hguard with h0 | hw'
    · exact h0 hand.1
    · exact hw' hand.2
  | case11 x hi lo hne1 hne2 ihx =>
    intro h env hbe
    cases x with
    | ref n => exact absurd rfl (hne1 n)
    | concat args =>
      rw [sfragCheck_slice_concat_general args hi lo
        (fun w y hEq => hne2 w y (by rw [hEq]))] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact SFrag.sliceCompound hi lo h.1.1.1 h.1.1.2 h.1.2
        (fun _ hEq => nomatch hEq)
        (fun w' y' hEq _ => hne2 w' y' hEq)
        (ihx h.2 env hbe)
    | const v w =>
      simp only [sfragCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      exact SFrag.sliceCompound hi lo h.1.1.1.2 h.1.1.2 h.1.2
        (fun _ hEq => nomatch hEq) (fun _ _ hEq => nomatch hEq)
        (SFrag.const v w h.2)
    | op o args =>
      simp only [sfragCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      exact SFrag.sliceCompound hi lo h.1.1.1.2 h.1.1.2 h.1.2
        (fun _ hEq => nomatch hEq) (fun _ _ hEq => nomatch hEq)
        (ihx h.2 env hbe)
    | slice y hi2 lo2 =>
      simp only [sfragCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      exact SFrag.sliceCompound hi lo h.1.1.1.2 h.1.1.2 h.1.2
        (fun _ hEq => nomatch hEq) (fun _ _ hEq => nomatch hEq)
        (ihx h.2 env hbe)
    | sliceDim y hi2 lo2 => simp [sfragCheck] at h
    | index a i => simp [sfragCheck] at h
  | case12 args ih =>
    intro h env hbe
    exact ih h env hbe
  | case13 t d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 =>
    intro h env _
    exfalso
    cases t with
    | ref n => exact absurd rfl (d1 n)
    | const v w => exact absurd rfl (d2 v w)
    | op o args =>
      match o, args with
      | .mux, [c, t', f] => exact absurd rfl (d3 c t' f)
      | .neg, [x] => exact absurd rfl (d4 x)
      | .not, [x] => exact absurd rfl (d5 x)
      | .asr, [x, y] => exact absurd rfl (d6 x y)
      | o, [a, b] => exact absurd rfl (d7 o a b)
      | o, [] => simp [sfragCheck] at h
      | o, [a] => simp [sfragCheck] at h
      | o, a :: b :: c :: rest => simp [sfragCheck] at h
    | slice x hi lo => exact absurd rfl (d10 x hi lo)
    | concat args => exact absurd rfl (d11 args)
    | sliceDim x hi lo => simp [sfragCheck] at h
    | index a i => simp [sfragCheck] at h
  | case14 =>
    exact SFrag.concatNil
  | case15 a rest iha ihrest =>
    rename_i h env hbe
    simp only [sfragCheckList, Bool.and_eq_true] at h
    obtain ⟨⟨hopw, ha⟩, hrest⟩ := h
    refine SFrag.concatCons ?_ (iha ha env hbe) (ihrest hrest env hbe)
    intro o as hEq
    subst hEq
    cases hwT : Tools.SVParser.EmitAst.exprWidthT wof (.op o as) with
    | none => rw [hwT] at hopw; cases hopw
    | some w =>
      rw [hwT] at hopw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hopw
      exact ⟨w, rfl, hopw.1, hopw.2⟩

open Sparkle.IR.Semantics in
/-- Soundness of the body census checker. -/
theorem bfragCheck_sound (wof : String → Option Nat)
    (wires : List Sparkle.IR.AST.Port) :
    ∀ (body : List Sparkle.IR.AST.Stmt), bfragCheck wof wires body = true →
    BFrag wof (fun n => (wof n).getD 0) wires body
  | [], _ => BFrag.nil
  | .assign l x :: rest, h => by
    simp only [bfragCheck, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    exact BFrag.assign h.1.1.1 h.1.1.2
      (fun env hbe => sfragCheck_sound wof x h.1.2 env hbe)
      (bfragCheck_sound wof wires rest h.2)
  | .register out clk (rst, kind) x init :: rest, h => by
    simp only [bfragCheck, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hso, hsc⟩, hsr⟩, hx⟩, hrw⟩, hw0⟩, hwrst⟩, hrest⟩ := h
    exact BFrag.reg hso hsc hsr
      (fun env hbe => sfragCheck_sound wof x hx env hbe) hrw hw0 hwrst
      (bfragCheck_sound wof wires rest hrest)
  | .memory name aw dw clk wa wd wen ra rd cr ew er :: rest, h => by
    simp only [bfragCheck, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hsn, hsc⟩, hwp⟩, hrp⟩, hdw⟩, hrest⟩ := h
    refine BFrag.mem hsn hsc ?_ ?_ hdw
      (bfragCheck_sound wof wires rest hrest)
    · intro p hp
      have := hwp p hp
      try simp only [Bool.and_eq_true] at this
      exact ⟨fun env hbe => sfragCheck_sound wof p.1 this.1.1 env hbe,
        fun env hbe => sfragCheck_sound wof p.2.1 this.1.2 env hbe,
        fun env hbe => sfragCheck_sound wof p.2.2 this.2 env hbe⟩
    · intro p hp
      have := hrp p hp
      try simp only [Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at this
      exact ⟨fun env hbe => sfragCheck_sound wof p.1 this.1.1 env hbe,
        this.1.2, this.2⟩
  | .inst _ _ _ :: _, h => by simp [bfragCheck] at h

open Sparkle.IR.Semantics Sparkle.IR.Reorder in
/-- **The capstone**: a module that passes the semantic-fragment census
    and whose shipping-lowered image passes the reorder check produces
    the SAME TRACE as the original — every hypothesis here is decidable
    and is exactly what Test 68 evaluates corpus-wide. -/
theorem certified_body_trace (m : Sparkle.IR.AST.Module)
    {bimg body' : List Sparkle.IR.AST.Stmt}
    (hcert : semFragCheck m = true)
    (hI : bodyImage (moduleWof m) m.wires m.body = some bimg)
    (hchk : bodyReorderCheck body' bimg = true)
    (seed : Nat → (String → Nat) → Env)
    (hseed : ∀ t st,
      Bounded (fun n => (moduleWof m n).getD 0) (seed t st))
    (k : Nat) (st : String → Nat) (mems : MEnv) :
    runModule (fun n => (moduleWof m n).getD 0) body' seed k st mems
      = runModule (fun n => (moduleWof m n).getD 0) m.body seed k st mems :=
  body_trace_roundtrip
    (bfragCheck_sound (moduleWof m) m.wires m.body hcert) hI hchk
    seed hseed k st mems

-- Validation on the probes (register bodies and memories of both read
-- kinds, single- and multi-port).
#guard bodyTraceCheck probeStmtM == .ok
#guard semFragCheck probeStmtM
#guard semFragCheck probeMemSync
#guard semFragCheck probeMemCombo
#guard bodyTraceCheck probeMemSync == .ok
#guard bodyTraceCheck probeMemSync2 == .ok
#guard bodyTraceCheck probeMemCombo == .ok
#guard bodyTraceCheck probeMemMulti == .ok

end Tools.SVParser.RoundtripProof
