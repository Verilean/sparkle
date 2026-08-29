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

end Tools.SVParser.RoundtripProof
