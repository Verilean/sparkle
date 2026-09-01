/-
  M4, first fragment: DIRECT forward correctness of the emitter.

      evalSV wof env (widthOf we e) (emitAstExpr wof e) = evalExpr we env e

  — the IR value of a fragment expression equals the VERILOG value of
  its emission, evaluated by the SystemVerilog-subset semantics at the
  assignment context width (which the module fragment's width-agreement
  conditions pin to `widthOf we e`).  This is the statement that removes
  the PARSER from the trusted base for the emit direction.

  The v0 fragment deliberately requires WIDTH-UNIFORM operands on
  arithmetic (`widthOf a = widthOf b`) and mux arms: Verilog evaluates
  context-determined operands at the CONTEXT width, so a bare
  mixed-width nested addition keeps its inner carry where the IR
  semantics masks per node — the emitter does not (yet) pin binop
  operands, so mixed widths sit outside this fragment (recorded as the
  M4 opening investigation).
-/
import Tools.SVParser.EmitAst
import Tools.SVParser.SVSemantics

namespace Tools.SVParser.EmitSem

open Tools.SVParser.AST
open Tools.SVParser.SVSemantics
open Sparkle.IR.AST
open Sparkle.IR.Semantics

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

/-- v0 forward fragment: refs, fitting constants, width-uniform
    unsigned arithmetic/bitwise, width-uniform mux, and the pinned
    NOT. -/
inductive SF4 (wof : String → Option Nat) (we : WEnv) : Expr → Prop
  | ref (n : String)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n)) : SF4 wof we (.ref n)
  | const (v : Int) (w : Nat) (hw : 0 < w) :
      SF4 wof we (.const v w)
  | binop (op : Operator)
      (hop : op = .and ∨ op = .or ∨ op = .xor ∨ op = .add
        ∨ op = .sub ∨ op = .mul)
      {a b : Expr}
      -- each operand either IS the max width (evaluating it at the
      -- node's context is exactly the IH) or has a context-immune
      -- emission (zero-extension changes nothing — a Nat value is its
      -- own zero-extension)
      (hA : Sparkle.IR.Semantics.widthOf we a
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE a = true)
      (hB : Sparkle.IR.Semantics.widthOf we b
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE b = true)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | mux {c t f : Expr}
      (hwf : Sparkle.IR.Semantics.widthOf we f
        = Sparkle.IR.Semantics.widthOf we t)
      (hc : SF4 wof we c) (ht : SF4 wof we t) (hf : SF4 wof we f) :
      SF4 wof we (.op .mux [c, t, f])
  | not {x : Expr} (w : Nat)
      (hwT : Tools.SVParser.EmitAst.exprWidthT wof x = some w)
      (hwS : Sparkle.IR.Semantics.widthOf we x = w)
      (hw0 : 0 < w)
      (hx : SF4 wof we x) : SF4 wof we (.op .not [x])
  | neg {x : Expr} (hx : SF4 wof we x) :
      SF4 wof we (.op .neg [x])
  | cmpU (op : Operator)
      (hop : op = .eq ∨ op = .lt_u ∨ op = .le_u ∨ op = .gt_u
        ∨ op = .ge_u)
      {a b : Expr}
      -- Verilog sizes comparison operands to their own max; each
      -- operand either IS the max width or is context-immune
      (hA : Sparkle.IR.Semantics.widthOf we a
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE a = true)
      (hB : Sparkle.IR.Semantics.widthOf we b
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE b = true)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | cmpS (op : Operator)
      (hop : op = .lt_s ∨ op = .le_s ∨ op = .gt_s ∨ op = .ge_s)
      {a b : Expr}
      -- the emitter's bias encoding `((x&m)^sb) OP ((y&m)^sb)` needs
      -- the emitter's width computation to agree with the IR's
      (hwTa : Tools.SVParser.EmitAst.exprWidthT wof a
        = some (Sparkle.IR.Semantics.widthOf we a))
      (hwTb : Tools.SVParser.EmitAst.exprWidthT wof b
        = some (Sparkle.IR.Semantics.widthOf we b))
      (hA : Sparkle.IR.Semantics.widthOf we a
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE a = true)
      (hB : Sparkle.IR.Semantics.widthOf we b
          = max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)
        ∨ immuneE b = true)
      (hw0 : 0 < max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b))
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | cmpS1 (op : Operator)
      (hop : op = .lt_s ∨ op = .le_s ∨ op = .gt_s ∨ op = .ge_s)
      {a b : Expr}
      -- the emitter cannot width the RIGHT operand (a mul/shift): it
      -- biases at the LEFT operand's width, which must therefore BE
      -- the comparison width
      (hwTa : Tools.SVParser.EmitAst.exprWidthT wof a
        = some (Sparkle.IR.Semantics.widthOf we a))
      (hwTb : Tools.SVParser.EmitAst.exprWidthT wof b = none)
      (hwba : Sparkle.IR.Semantics.widthOf we b
        ≤ Sparkle.IR.Semantics.widthOf we a)
      (hB : Sparkle.IR.Semantics.widthOf we b
          = Sparkle.IR.Semantics.widthOf we a
        ∨ immuneE b = true)
      (hw0 : 0 < Sparkle.IR.Semantics.widthOf we a)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])
  | sliceRef (n : String) (hi lo : Nat)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n))
      (hlo : lo ≤ hi) (hhi : hi < we n)
      -- the exact full-width slice is the ELIDED emission — see
      -- `sliceRefFull`
      (hne : ¬(lo = 0 ∧ hi + 1 = we n)) :
      SF4 wof we (.slice (.ref n) hi lo)
  | sliceRefFull (n : String) (hi : Nat)
      (hs : Sparkle.Backend.Verilog.sanitizeName n = n)
      (hw : wof n = some (we n))
      (hfull : hi + 1 = we n) :
      SF4 wof we (.slice (.ref n) hi 0)
  | concat {args : List Expr}
      (hall : ∀ e, e ∈ args → SF4 wof we e)
      -- op-typed elements get the emitter's width-pinning size cast;
      -- the pin is faithful when the emitter's width matches the IR's
      (hpin : ∀ e, e ∈ args → ∀ op as, e = .op op as →
        Tools.SVParser.EmitAst.exprWidthT wof e
          = some (Sparkle.IR.Semantics.widthOf we e)
        ∧ 0 < Sparkle.IR.Semantics.widthOf we e) :
      SF4 wof we (.concat args)
  | castEnc {x : Expr} (w : Nat) (hw0 : 0 < w)
      (hx : SF4 wof we x)
      -- Verilog evaluates a cast's argument at the CAST width: a
      -- DOWN-cast evaluates it at its own width (safe for any
      -- fragment shape); an UP-cast widens the context, which is only
      -- faithful for context-immune emissions.
      (hsafe : w ≤ Sparkle.IR.Semantics.widthOf we x
        ∨ immuneE x = true) :
      SF4 wof we (.slice (.concat [.const 0 w, x]) (w - 1) 0)
  | sliceGen {x : Expr} (hi lo : Nat)
      (hcomp : ∀ n, x ≠ .ref n)
      (hncast : ∀ w y, x = .concat [.const 0 w, y] →
        ¬(lo = 0 ∧ hi + 1 = w))
      (hlo : lo ≤ hi)
      (hlo32 : lo < 2 ^ 32)
      (hx : SF4 wof we x)
      -- the emitted `n'((E) >> lo)` puts E in an n-bit-or-wider
      -- context; safe when the select stays inside the value, or when
      -- the emission is context-immune
      (hsafe : hi + 1 - lo ≤ Sparkle.IR.Semantics.widthOf we x
        ∨ immuneE x = true) :
      SF4 wof we (.slice x hi lo)
  | bitwiseShl (op : Operator)
      (hop : op = .and ∨ op = .or ∨ op = .xor)
      {a c : Expr} (k kw : Nat)
      -- `(a << 32'd k) OP c` — the shift carries only a VALUE claim
      -- (`shl_val_at`), which is all a bitwise parent needs.
      (ha : SF4 wof we a) (himmA : immuneE a = true)
      (hk : k < 2 ^ kw) (hkw : 0 < kw)
      (hfit : Sparkle.IR.Semantics.widthOf we a + k
        ≤ max (Sparkle.IR.Semantics.widthOf we a) kw)
      (hc : SF4 wof we c)
      -- the OTHER operand DOMINATES: at least as wide as the shift's
      -- IR width.  That is what keeps the parent's `widthSV` (a max)
      -- equal to the parent's `widthOf` (also a max) even though the
      -- shift's two widths disagree.
      (hDom : max (Sparkle.IR.Semantics.widthOf we a) kw
        ≤ Sparkle.IR.Semantics.widthOf we c) :
      SF4 wof we (.op op [.op .shl [a, .const (Int.ofNat k) kw], c])
  | shiftOp (op : Operator) (hop : op = .shl ∨ op = .shr)
      {a b : Expr}
      -- SHR's width IS its value operand's (the formal rule matches
      -- Verilog's self-determined one), so it enters unconditionally;
      -- SHL still takes the generic max, so its amount must be no
      -- wider than the value for the two width rules to coincide.
      (hwb : op = .shr ∨ Sparkle.IR.Semantics.widthOf we b
        ≤ Sparkle.IR.Semantics.widthOf we a)
      (ha : SF4 wof we a) (hb : SF4 wof we b) :
      SF4 wof we (.op op [a, b])

/-- Emission shapes whose value is CONTEXT-IMMUNE: evaluating at any
    width ≥ their own gives the same value.  These are exactly the
    shapes that carry their own mask (casts, slices, fitting literals,
    0/1-valued compares) or are bounded by declaration (idents under a
    width-respecting environment). -/
def immuneSV : SVExpr → Bool
  | .ident _ => true
  | .lit (.decimal (some w) v) => v < 2 ^ w
  | .lit (.hex (some w) v) => v < 2 ^ w
  | .sizeCast _ _ => true
  | .slice (.ident _) _ _ => true
  | .binary .eq _ _ | .binary .lt _ _ | .binary .le _ _
  | .binary .gt _ _ | .binary .ge _ _ => true
  -- a concat is immune outright: its elements are SELF-determined
  -- (evaluated at context 0 inside `goConcat`), and the assembled
  -- value fits the total width, so the outer context mask is inert
  | .concat _ => true
  -- bitwise ops are carry-free: with immune (hence width-bounded)
  -- operands, widening the context adds no bits
  | .binary .bitAnd a b => immuneSV a && immuneSV b
  | .binary .bitOr a b => immuneSV a && immuneSV b
  | .binary .bitXor a b => immuneSV a && immuneSV b
  -- a ternary just selects one of its (context-determined) arms; if
  -- both are immune, so is the selection
  | .ternary _ t f => immuneSV t && immuneSV f
  | _ => false

/-- `goConcat`'s assembly fits the total width (each element is masked
    to its own width before shifting into place). -/
private theorem goConcat_lt {wof : String → Option Nat} {env : SEnv} :
    ∀ (svs : List SVExpr) (tw v : Nat),
      widthSV.go wof svs = some tw →
      goConcat wof env svs = some v → v < 2 ^ tw := by
  intro svs
  induction svs with
  | nil =>
    intro tw v hw hv
    simp only [widthSV.go, Option.some_inj] at hw
    simp only [goConcat, Option.some_inj] at hv
    subst hw; subst hv
    simp
  | cons a rest ih =>
    intro tw v hw hv
    simp only [widthSV.go, Option.bind_eq_bind] at hw
    obtain ⟨wa, hwa, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨wr, hwr, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    simp only [goConcat, Option.bind_eq_bind] at hv
    obtain ⟨wa', hwa', hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, hva, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wr', hwr', hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vr, hvr, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    rw [hwa] at hwa'
    rw [hwr] at hwr'
    simp only [Option.some_inj] at hwa' hwr'
    subst hwa'; subst hwr'
    have h1 : mask wa va < 2 ^ wa := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : mask wa va <<< wr < 2 ^ (wa + wr) := by
      rw [Nat.shiftLeft_eq, Nat.pow_add]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
    have h3 : vr < 2 ^ (wa + wr) :=
      Nat.lt_of_lt_of_le (ih wr vr hwr hvr)
        (Nat.pow_le_pow_right (by omega) (by omega))
    exact Nat.or_lt_two_pow h2 h3

/-- Context-immunity, semantically: an immune emission evaluates the
    same at every width ≥ its own (and its value fits its width).
    This is what makes the self-determined boundaries (cast arguments,
    comparison operands) safe to UP-size — the extra context bits
    never materialize. -/
private theorem evalAt_immune_all {wof : String → Option Nat}
    {env : SEnv}
    (hb : ∀ n wn, wof n = some wn → env n < 2 ^ wn) :
    ∀ (sv : SVExpr) (w : Nat), immuneSV sv = true →
      widthSV wof sv = some w →
      (∀ v, evalAt wof env w sv = some v → v < 2 ^ w)
      ∧ (∀ W, w ≤ W → evalAt wof env W sv = evalAt wof env w sv)
  | .ident n, w, _, hw => by
    simp only [widthSV] at hw
    have hbn := hb n w hw
    constructor
    · intro v hv
      simp only [evalAt, hw, Option.bind_eq_bind, Option.bind_some,
        Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp only [evalAt, hw, Option.bind_eq_bind, Option.bind_some]
      simp [mask, Nat.mod_eq_of_lt hbn,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hbn hpow)]
  | .lit (.decimal (some w') v), w, himm, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    simp only [immuneSV, decide_eq_true_eq] at himm
    constructor
    · intro u hu
      simp only [evalAt, litVal, Option.some_inj] at hu
      subst hu
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w' ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp [evalAt, litVal, mask, Nat.mod_eq_of_lt himm,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le himm hpow)]
  | .lit (.hex (some w') v), w, himm, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    simp only [immuneSV, decide_eq_true_eq] at himm
    constructor
    · intro u hu
      simp only [evalAt, litVal, Option.some_inj] at hu
      subst hu
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w' ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp [evalAt, litVal, mask, Nat.mod_eq_of_lt himm,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le himm hpow)]
  | .sizeCast w' a, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨u, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w' ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp only [evalAt]
      cases hv : evalSV wof env w' a with
      | none => simp [hv]
      | some v =>
        have hlt : v % 2 ^ w' < 2 ^ w' := Nat.mod_lt _ (Nat.two_pow_pos _)
        simp [hv, mask, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow),
          Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), Nat.mod_eq_of_lt hlt]
  | .slice (.ident n) hi lo, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨wn, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      by_cases hc : lo ≤ hi ∧ hi < wn
      · simp only [if_pos hc, Option.some_inj] at hv
        subst hv
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · simp [if_neg hc] at hv
    · intro W hW
      have hpow : (2 : Nat) ^ (hi - lo + 1) ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by omega) hW
      simp only [evalAt]
      cases hwn : wof n with
      | none => simp [hwn]
      | some wn =>
        by_cases hc : lo ≤ hi ∧ hi < wn
        · have hlt : (env n >>> lo) % 2 ^ (hi - lo + 1)
              < 2 ^ (hi - lo + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
          simp [hwn, hc, mask,
            Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow),
            Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), Nat.mod_eq_of_lt hlt]
        · simp [hwn, hc]
  | .binary .eq a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .binary .lt a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .binary .le a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .binary .gt a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .binary .ge a b, w, _, hw => by
    simp only [widthSV, Option.some_inj] at hw
    subst hw
    refine ⟨?_, fun W _ => by simp only [evalAt]⟩
    intro v hv
    simp only [evalAt] at hv
    obtain ⟨wa, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨wb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    split <;> omega
  | .concat svs, w, _, hw => by
    simp only [widthSV] at hw
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨u, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      have hpow : (2 : Nat) ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hW
      simp only [evalAt]
      cases hv : goConcat wof env svs with
      | none => simp [hv]
      | some v =>
        have hlt := goConcat_lt svs w v hw hv
        simp [hv, mask, Nat.mod_eq_of_lt hlt,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)]
  | .ternary c t f, w, himm, hw => by
    simp only [immuneSV, Bool.and_eq_true] at himm
    obtain ⟨himmT, himmF⟩ := himm
    simp only [widthSV, Option.bind_eq_bind] at hw
    obtain ⟨wt, hwt, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨wf, hwf, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    obtain ⟨bndT, stbT⟩ := evalAt_immune_all hb t wt himmT hwt
    obtain ⟨bndF, stbF⟩ := evalAt_immune_all hb f wf himmF hwf
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨vc, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      by_cases hc : vc ≠ 0
      · rw [if_pos hc, stbT (max wt wf) (Nat.le_max_left _ _)] at hv
        exact Nat.lt_of_lt_of_le (bndT v hv)
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
      · rw [if_neg hc, stbF (max wt wf) (Nat.le_max_right _ _)] at hv
        exact Nat.lt_of_lt_of_le (bndF v hv)
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    · intro W hW
      simp only [evalAt]
      rw [stbT W (Nat.le_trans (Nat.le_max_left _ _) hW),
          stbF W (Nat.le_trans (Nat.le_max_right _ _) hW),
          stbT (max wt wf) (Nat.le_max_left _ _),
          stbF (max wt wf) (Nat.le_max_right _ _)]
  | .binary .bitAnd a b, w, himm, hw => by
    simp only [immuneSV, Bool.and_eq_true] at himm
    obtain ⟨himmA, himmB⟩ := himm
    simp only [widthSV, Option.bind_eq_bind] at hw
    obtain ⟨sa, hsa, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨sb, hsb, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    obtain ⟨bndA, stbA⟩ := evalAt_immune_all hb a sa himmA hsa
    obtain ⟨bndB, stbB⟩ := evalAt_immune_all hb b sb himmB hsb
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      simp only [evalAt]
      rw [stbA W (Nat.le_trans (Nat.le_max_left _ _) hW),
          stbB W (Nat.le_trans (Nat.le_max_right _ _) hW),
          stbA (max sa sb) (Nat.le_max_left _ _),
          stbB (max sa sb) (Nat.le_max_right _ _)]
      cases hva : evalAt wof env sa a with
      | none => simp [hva]
      | some va =>
      cases hvb : evalAt wof env sb b with
      | none => simp [hva, hvb]
      | some vb =>
      have hlt : va &&& vb < 2 ^ max sa sb :=
        Nat.lt_of_le_of_lt Nat.and_le_left
          (Nat.lt_of_lt_of_le (bndA va hva)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
      have hpow : (2 : Nat) ^ max sa sb ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by omega) hW
      simp [hva, hvb, mask, Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)]
  | .binary .bitOr a b, w, himm, hw => by
    simp only [immuneSV, Bool.and_eq_true] at himm
    obtain ⟨himmA, himmB⟩ := himm
    simp only [widthSV, Option.bind_eq_bind] at hw
    obtain ⟨sa, hsa, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨sb, hsb, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    obtain ⟨bndA, stbA⟩ := evalAt_immune_all hb a sa himmA hsa
    obtain ⟨bndB, stbB⟩ := evalAt_immune_all hb b sb himmB hsb
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      simp only [evalAt]
      rw [stbA W (Nat.le_trans (Nat.le_max_left _ _) hW),
          stbB W (Nat.le_trans (Nat.le_max_right _ _) hW),
          stbA (max sa sb) (Nat.le_max_left _ _),
          stbB (max sa sb) (Nat.le_max_right _ _)]
      cases hva : evalAt wof env sa a with
      | none => simp [hva]
      | some va =>
      cases hvb : evalAt wof env sb b with
      | none => simp [hva, hvb]
      | some vb =>
      have hlt : va ||| vb < 2 ^ max sa sb :=
        Nat.or_lt_two_pow
          (Nat.lt_of_lt_of_le (bndA va hva)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
          (Nat.lt_of_lt_of_le (bndB vb hvb)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)))
      have hpow : (2 : Nat) ^ max sa sb ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by omega) hW
      simp [hva, hvb, mask, Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)]
  | .binary .bitXor a b, w, himm, hw => by
    simp only [immuneSV, Bool.and_eq_true] at himm
    obtain ⟨himmA, himmB⟩ := himm
    simp only [widthSV, Option.bind_eq_bind] at hw
    obtain ⟨sa, hsa, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨sb, hsb, hw⟩ := Option.bind_eq_some_iff.mp hw
    simp only [Option.some_inj] at hw
    subst hw
    obtain ⟨bndA, stbA⟩ := evalAt_immune_all hb a sa himmA hsa
    obtain ⟨bndB, stbB⟩ := evalAt_immune_all hb b sb himmB hsb
    constructor
    · intro v hv
      simp only [evalAt] at hv
      obtain ⟨va, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨vb, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [Option.some_inj] at hv
      subst hv
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · intro W hW
      simp only [evalAt]
      rw [stbA W (Nat.le_trans (Nat.le_max_left _ _) hW),
          stbB W (Nat.le_trans (Nat.le_max_right _ _) hW),
          stbA (max sa sb) (Nat.le_max_left _ _),
          stbB (max sa sb) (Nat.le_max_right _ _)]
      cases hva : evalAt wof env sa a with
      | none => simp [hva]
      | some va =>
      cases hvb : evalAt wof env sb b with
      | none => simp [hva, hvb]
      | some vb =>
      have hlt : va ^^^ vb < 2 ^ max sa sb :=
        Nat.xor_lt_two_pow
          (Nat.lt_of_lt_of_le (bndA va hva)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
          (Nat.lt_of_lt_of_le (bndB vb hvb)
            (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)))
      have hpow : (2 : Nat) ^ max sa sb ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by omega) hW
      simp [hva, hvb, mask, Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hpow)]

/-- The stability face of `evalAt_immune_all` (the shape the fragment
    proofs consume). -/
private theorem evalAt_immune {wof : String → Option Nat} {env : SEnv}
    {sv : SVExpr} {w : Nat}
    (himm : immuneSV sv = true)
    (hw : widthSV wof sv = some w)
    (hb : ∀ n wn, wof n = some wn → env n < 2 ^ wn) :
    ∀ W, w ≤ W → evalAt wof env W sv = evalAt wof env w sv :=
  (evalAt_immune_all hb sv w himm hw).2

/-- v0 fragment expressions always evaluate (their shapes are total in
    `evalExpr`). -/
theorem sf4_eval_isSome {wof : String → Option Nat} {we : WEnv}
    {e : Expr} (h : SF4 wof we e) :
    ∀ env, (evalExpr we env e).isSome := by
  induction h with
  | ref n hs hw => intro env; simp [evalExpr]
  | const v w hw => intro env; simp [evalExpr]
  | binop op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | mux hwf hc ht hf ihc iht ihf =>
    rename_i c t f
    intro env
    obtain ⟨vc, hvc⟩ := Option.isSome_iff_exists.mp (ihc env)
    obtain ⟨vt, hvt⟩ := Option.isSome_iff_exists.mp (iht env)
    obtain ⟨vf, hvf⟩ := Option.isSome_iff_exists.mp (ihf env)
    simp [evalExpr, evalList, hvc, hvt, hvf, evalOp]
  | not w hwT hwS hw0 hx ihx =>
    rename_i x
    intro env
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp (ihx env)
    simp [evalExpr, evalList, hvx, evalOp]
  | neg hx ihx =>
    rename_i x
    intro env
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp (ihx env)
    simp [evalExpr, evalList, hvx, evalOp]
  | cmpU op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]
  | sliceRef n hi lo hs hw hlo hhi hne =>
    intro env; simp [evalExpr]
  | sliceRefFull n hi hs hw hfull =>
    intro env; simp [evalExpr]
  | concat hall hpin ihall =>
    rename_i args
    intro env
    have : ∀ (as : List Expr), (∀ e, e ∈ as → (evalExpr we env e).isSome)
        → (evalList we env as).isSome := by
      intro as
      induction as with
      | nil => intro _; simp [evalList]
      | cons a rest ih =>
        intro hmem
        obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp
          (hmem a (List.mem_cons_self ..))
        obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp
          (ih fun e he => hmem e (List.mem_cons_of_mem _ he))
        simp [evalList, hva, hvs]
    obtain ⟨vals, hvals⟩ := Option.isSome_iff_exists.mp
      (this args fun e he => ihall e he env)
    simp [evalExpr, hvals]
  | castEnc w hw0 hx hsafe ihx =>
    rename_i x
    intro env
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp (ihx env)
    simp [evalExpr, evalList, hvx]
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    rename_i x
    intro env
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp (ihx env)
    simp [evalExpr, hvx]
  | bitwiseShl op hop k kw ha himmA hk hkw hfit hc hDom iha ihc =>
    rename_i a c
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vc, hvc⟩ := Option.isSome_iff_exists.mp (ihc env)
    rcases hop with h | h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvc, evalOp]
  | shiftOp op hop hwb ha hb iha ihb =>
    rename_i a b
    intro env
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp (iha env)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp (ihb env)
    rcases hop with h | h <;> subst h <;>
      simp [evalExpr, evalList, hva, hvb, evalOp]

private theorem evalList_length {we : WEnv} {env : Env} :
    ∀ (as : List Expr) (vs : List Nat),
      evalList we env as = some vs → vs.length = as.length := by
  intro as
  induction as with
  | nil => intro vs h; simp [evalList] at h; simp [← h]
  | cons a rest ih =>
    intro vs h
    simp only [evalList, Option.bind_eq_bind] at h
    obtain ⟨va, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vr, hvr, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some_inj] at h
    subst h
    simp [ih vr hvr]

private theorem zip_foldl_width {we : WEnv} :
    ∀ (as : List Expr) (vs : List Nat) (acc : Nat),
      as.length = vs.length →
      (as.zip vs).foldl (fun acc (p : Expr × Nat) =>
        acc + Sparkle.IR.Semantics.widthOf we p.1) acc
      = acc + Sparkle.IR.Semantics.widthOf.go we as := by
  intro as
  induction as with
  | nil =>
    intro vs acc _
    simp [Sparkle.IR.Semantics.widthOf.go]
  | cons a rest ih =>
    intro vs acc hlen
    cases vs with
    | nil => simp at hlen
    | cons v vrest =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih vrest _ (by simpa using hlen),
        Sparkle.IR.Semantics.widthOf.go]
      omega

private theorem evalOp_mask_bound {we : WEnv} {op : Operator}
    {args : List Expr} {vals : List Nat} {w v : Nat}
    (hop : op = .and ∨ op = .or ∨ op = .xor ∨ op = .add
      ∨ op = .sub ∨ op = .mul)
    (h : evalOp we op args vals w = some v) : v < 2 ^ w := by
  rcases hop with h' | h' | h' | h' | h' | h' <;> subst h' <;>
  · match vals, h with
    | [a, b], h =>
      simp only [evalOp, Option.some_inj] at h
      subst h
      exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The IR's MSB-first assembly fits the total width (no boundedness
    of the values needed — `go` masks each element itself). -/
private theorem evalExpr_go_lt {we : WEnv} :
    ∀ (args : List Expr) (vals : List Nat),
      args.length = vals.length →
      Sparkle.IR.Semantics.evalExpr.go we args vals
        < 2 ^ Sparkle.IR.Semantics.widthOf.go we args := by
  intro args
  induction args with
  | nil =>
    intro vals _
    simp [Sparkle.IR.Semantics.evalExpr.go,
      Sparkle.IR.Semantics.widthOf.go]
  | cons a rest ih =>
    intro vals hlen
    cases vals with
    | nil => simp at hlen
    | cons v vrest =>
      simp only [Sparkle.IR.Semantics.evalExpr.go,
        Sparkle.IR.Semantics.widthOf.go]
      rw [zip_foldl_width rest vrest 0 (by simpa using hlen)]
      simp only [Nat.zero_add]
      have h1 : mask (Sparkle.IR.Semantics.widthOf we a) v
          < 2 ^ Sparkle.IR.Semantics.widthOf we a :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have h2 : mask (Sparkle.IR.Semantics.widthOf we a) v
            <<< Sparkle.IR.Semantics.widthOf.go we rest
          < 2 ^ (Sparkle.IR.Semantics.widthOf we a
              + Sparkle.IR.Semantics.widthOf.go we rest) := by
        rw [Nat.shiftLeft_eq, Nat.pow_add]
        exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
      have h3 : Sparkle.IR.Semantics.evalExpr.go we rest vrest
          < 2 ^ (Sparkle.IR.Semantics.widthOf we a
              + Sparkle.IR.Semantics.widthOf.go we rest) :=
        Nat.lt_of_lt_of_le (ih vrest (by simpa using hlen))
          (Nat.pow_le_pow_right (by omega) (by omega))
      exact Nat.or_lt_two_pow h2 h3

/-- Element-wise alignment of the emitter's concat with the IR's:
    same total width, same MSB-first assembly, and the assembled value
    fits its total width (so the context mask at the top is inert). -/
private theorem concat_elems_sem {wof : String → Option Nat} {we : WEnv}
    {env : Env} :
    ∀ (args : List Expr) (svs : List SVExpr),
      (∀ e, e ∈ args → (evalExpr we env e).isSome) →
      (∀ e, e ∈ args → ∀ sv,
        Tools.SVParser.EmitAst.emitAstExpr wof e = some sv →
          widthSV wof sv = some (Sparkle.IR.Semantics.widthOf we e)
          ∧ evalAt wof env (Sparkle.IR.Semantics.widthOf we e) sv
              = evalExpr we env e) →
      (∀ e, e ∈ args → ∀ op as, e = .op op as →
        Tools.SVParser.EmitAst.exprWidthT wof e
          = some (Sparkle.IR.Semantics.widthOf we e)
        ∧ 0 < Sparkle.IR.Semantics.widthOf we e) →
      Tools.SVParser.EmitAst.emitConcatElems wof args = some svs →
      widthSV.go wof svs
          = some (Sparkle.IR.Semantics.widthOf.go we args)
      ∧ ∃ vals, evalList we env args = some vals
        ∧ goConcat wof env svs
            = some (Sparkle.IR.Semantics.evalExpr.go we args vals)
        ∧ Sparkle.IR.Semantics.evalExpr.go we args vals
            < 2 ^ Sparkle.IR.Semantics.widthOf.go we args := by
  intro args
  induction args with
  | nil =>
    intro svs _ _ _ hemit
    simp only [Tools.SVParser.EmitAst.emitConcatElems,
      Option.some_inj] at hemit
    subst hemit
    exact ⟨by simp [widthSV.go, Sparkle.IR.Semantics.widthOf.go],
      [], by simp [evalList],
      by simp [goConcat, Sparkle.IR.Semantics.evalExpr.go],
      by simp [Sparkle.IR.Semantics.evalExpr.go,
        Sparkle.IR.Semantics.widthOf.go, Nat.zero_lt_one]⟩
  | cons a rest ih =>
    intro svs hsome hsem hpin hemit
    obtain ⟨vA, hvA⟩ := Option.isSome_iff_exists.mp
      (hsome a (List.mem_cons_self ..))
    -- the assembly, abstracted over the (possibly cast-pinned) head:
    -- any head emission with the right width whose value agrees with
    -- the IR element up to its own mask assembles correctly
    have finish : ∀ (ca : SVExpr) (es : List SVExpr),
        Tools.SVParser.EmitAst.emitConcatElems wof rest = some es →
        widthSV wof ca = some (Sparkle.IR.Semantics.widthOf we a) →
        (∃ va, evalSV wof env 0 ca = some va
          ∧ mask (Sparkle.IR.Semantics.widthOf we a) va
            = mask (Sparkle.IR.Semantics.widthOf we a) vA) →
        widthSV.go wof (ca :: es)
            = some (Sparkle.IR.Semantics.widthOf.go we (a :: rest))
        ∧ ∃ vals, evalList we env (a :: rest) = some vals
          ∧ goConcat wof env (ca :: es)
              = some (Sparkle.IR.Semantics.evalExpr.go we (a :: rest) vals)
          ∧ Sparkle.IR.Semantics.evalExpr.go we (a :: rest) vals
              < 2 ^ Sparkle.IR.Semantics.widthOf.go we (a :: rest) := by
      rintro ca es hes htw ⟨va, hva, hmva⟩
      obtain ⟨hwgo, vals, hvals, hgo, hbnd⟩ := ih es
        (fun e he => hsome e (List.mem_cons_of_mem _ he))
        (fun e he => hsem e (List.mem_cons_of_mem _ he))
        (fun e he => hpin e (List.mem_cons_of_mem _ he))
        hes
      have hlen := evalList_length rest vals hvals
      refine ⟨?_, vA :: vals, ?_, ?_, ?_⟩
      · simp only [widthSV.go, htw, hwgo, Option.bind_eq_bind,
          Option.bind_some, Sparkle.IR.Semantics.widthOf.go]
      · simp [evalList, hvA, hvals]
      · simp only [goConcat, htw, hva, hwgo, hgo, Option.bind_eq_bind,
          Option.bind_some, Option.some_inj,
          Sparkle.IR.Semantics.evalExpr.go]
        rw [zip_foldl_width rest vals 0 hlen.symm, hmva]
        simp
      · simp only [Sparkle.IR.Semantics.evalExpr.go,
          Sparkle.IR.Semantics.widthOf.go]
        rw [zip_foldl_width rest vals 0 hlen.symm]
        simp only [Nat.zero_add]
        have h1 : mask (Sparkle.IR.Semantics.widthOf we a) vA
            < 2 ^ Sparkle.IR.Semantics.widthOf we a :=
          Nat.mod_lt _ (Nat.two_pow_pos _)
        have h2 : mask (Sparkle.IR.Semantics.widthOf we a) vA
              <<< Sparkle.IR.Semantics.widthOf.go we rest
            < 2 ^ (Sparkle.IR.Semantics.widthOf we a
                + Sparkle.IR.Semantics.widthOf.go we rest) := by
          rw [Nat.shiftLeft_eq, Nat.pow_add]
          exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
        have h3 : Sparkle.IR.Semantics.evalExpr.go we rest vals
            < 2 ^ (Sparkle.IR.Semantics.widthOf we a
                + Sparkle.IR.Semantics.widthOf.go we rest) :=
          Nat.lt_of_lt_of_le hbnd
            (Nat.pow_le_pow_right (by omega) (by omega))
        exact Nat.or_lt_two_pow h2 h3
    cases a
    case op op' as' =>
      obtain ⟨hpT, hp0⟩ := hpin _ (List.mem_cons_self ..) op' as' rfl
      simp only [Tools.SVParser.EmitAst.emitConcatElems, hpT,
        Option.bind_eq_bind] at hemit
      obtain ⟨ea, hea, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      obtain ⟨es, hes, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      simp only [Option.some_inj] at hemit
      rw [if_pos hp0] at hemit
      subst hemit
      obtain ⟨hwea, hvea⟩ := hsem _ (List.mem_cons_self ..) ea hea
      refine finish _ es hes (by simp [widthSV]) ?_
      refine ⟨mask (Sparkle.IR.Semantics.widthOf we (.op op' as'))
        (mask (Sparkle.IR.Semantics.widthOf we (.op op' as')) vA),
        ?_, by simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]⟩
      unfold evalSV
      simp only [widthSV, Option.bind_eq_bind, Option.bind_some,
        Nat.max_eq_right (Nat.zero_le _), evalAt]
      unfold evalSV
      simp [hwea, hvea, hvA]
    all_goals
      (simp only [Tools.SVParser.EmitAst.emitConcatElems,
         Option.bind_eq_bind] at hemit;
       obtain ⟨ea, hea, hemit⟩ := Option.bind_eq_some_iff.mp hemit;
       obtain ⟨es, hes, hemit⟩ := Option.bind_eq_some_iff.mp hemit;
       simp only [Option.some_inj] at hemit;
       subst hemit;
       obtain ⟨hwea, hvea⟩ := hsem _ (List.mem_cons_self ..) ea hea;
       refine finish ea es hes hwea ⟨vA, ?_, rfl⟩;
       unfold evalSV;
       simp [hwea, hvea, hvA])

/-- XORing the top bit of a `w`-bit value adds the bias when the bit
    is clear and removes it when set — the classic biased encoding. -/
private theorem xor_top_bit {w v : Nat} (hw : 0 < w) (hv : v < 2 ^ w) :
    v ^^^ 2 ^ (w - 1)
      = if v < 2 ^ (w - 1) then v + 2 ^ (w - 1) else v - 2 ^ (w - 1) := by
  have h2 : (2 : Nat) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hpos : 0 < (2 : Nat) ^ (w - 1) := Nat.two_pow_pos _
  have hdiv : (v ^^^ 2 ^ (w - 1)) / 2 ^ (w - 1)
      = v / 2 ^ (w - 1) ^^^ 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self hpos]
  have hmod : (v ^^^ 2 ^ (w - 1)) % 2 ^ (w - 1) = v % 2 ^ (w - 1) := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  have hda := Nat.div_add_mod (v ^^^ 2 ^ (w - 1)) (2 ^ (w - 1))
  have hdv := Nat.div_add_mod v (2 ^ (w - 1))
  rw [hdiv, hmod] at hda
  have hmv : v % 2 ^ (w - 1) < 2 ^ (w - 1) := Nat.mod_lt _ hpos
  have hxlt : v ^^^ 2 ^ (w - 1) < 2 ^ w :=
    Nat.xor_lt_two_pow hv (by omega)
  by_cases hcase : v < 2 ^ (w - 1)
  · have hd0 : v / 2 ^ (w - 1) = 0 := Nat.div_eq_of_lt hcase
    rw [hd0] at hda
    have hx1 : (0 : Nat) ^^^ 1 = 1 := rfl
    rw [hx1] at hda
    have hm0 : v % 2 ^ (w - 1) = v := Nat.mod_eq_of_lt hcase
    rw [hm0] at hda
    rw [if_pos hcase]
    omega
  · have hd1 : v / 2 ^ (w - 1) = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
    rw [hd1] at hda
    have hx0 : (1 : Nat) ^^^ 1 = 0 := rfl
    rw [hx0] at hda
    rw [hd1] at hdv
    rw [if_neg hcase]
    omega

/-- Unsigned comparison of biased values IS signed comparison. -/
private theorem biased_lt {w a b : Nat} (hw : 0 < w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    ((a ^^^ 2 ^ (w - 1)) < (b ^^^ 2 ^ (w - 1)))
      ↔ toSigned w a < toSigned w b := by
  rw [xor_top_bit hw ha, xor_top_bit hw hb]
  have h2 : (2 : Nat) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  unfold toSigned
  by_cases hA : a < 2 ^ (w - 1) <;> by_cases hB : b < 2 ^ (w - 1) <;>
    simp only [if_pos, if_neg, hA, hB, if_true, if_false] <;>
    omega

private theorem biased_le {w a b : Nat} (hw : 0 < w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    ((a ^^^ 2 ^ (w - 1)) ≤ (b ^^^ 2 ^ (w - 1)))
      ↔ toSigned w a ≤ toSigned w b := by
  rw [xor_top_bit hw ha, xor_top_bit hw hb]
  have h2 : (2 : Nat) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  unfold toSigned
  by_cases hA : a < 2 ^ (w - 1) <;> by_cases hB : b < 2 ^ (w - 1) <;>
    simp only [if_pos, if_neg, hA, hB, if_true, if_false] <;>
    omega

/-- Fragment values are width-bounded: under a bounded environment,
    every fragment expression evaluates below 2^its-width.  (The one
    rule that does not mask its own result is `mux` — its arms carry
    the bound.) -/
theorem sf4_bounded {wof : String → Option Nat} {we : WEnv} {e : Expr}
    (h : SF4 wof we e) {env : Env} (hbe : Bounded we env) :
    ∀ v, evalExpr we env e = some v
      → v < 2 ^ Sparkle.IR.Semantics.widthOf we e := by
  induction h with
  | ref n hs hw =>
    intro v hv
    simp only [evalExpr, Option.some_inj] at hv
    subst hv
    simpa [Sparkle.IR.Semantics.widthOf] using hbe n
  | const v' w hw =>
    intro v hv
    simp only [evalExpr, Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | binop op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    exact evalOp_mask_bound hop hv
  | mux hwf hc ht hf ihc iht ihf =>
    rename_i c t f
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [evalList, Option.bind_eq_bind] at hvals
    obtain ⟨vc, hvc, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    obtain ⟨vrest, hvrest, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    obtain ⟨vt, hvt, hvrest⟩ := Option.bind_eq_some_iff.mp hvrest
    obtain ⟨vrest2, hvrest2, hvrest⟩ := Option.bind_eq_some_iff.mp hvrest
    obtain ⟨vf, hvf, hvrest2⟩ := Option.bind_eq_some_iff.mp hvrest2
    obtain ⟨vnil, hvnil, hvrest2⟩ := Option.bind_eq_some_iff.mp hvrest2
    simp only [evalList, Option.some_inj] at hvnil
    subst hvnil
    simp only [Option.some_inj] at hvrest2 hvrest hvals
    subst hvrest2; subst hvrest; subst hvals
    simp only [evalOp, Option.some_inj] at hv
    have hWt : Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])
        = Sparkle.IR.Semantics.widthOf we t := by
      simp [Sparkle.IR.Semantics.widthOf]
    rw [hWt]
    subst hv
    by_cases h0 : vc ≠ 0
    · rw [if_pos h0]; exact iht vt hvt
    · rw [if_neg h0]; exact hwf ▸ ihf vf hvf
  | not w hwT hwS hw0 hx ihx =>
    rename_i x
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [evalList, Option.bind_eq_bind] at hvals
    obtain ⟨vx, hvx, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    obtain ⟨vnil, hvnil, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    simp only [evalList, Option.some_inj] at hvnil
    subst hvnil
    simp only [Option.some_inj] at hvals
    subst hvals
    simp only [evalOp, Option.some_inj] at hv
    subst hv
    have : Sparkle.IR.Semantics.widthOf we (.op .not [x])
        = Sparkle.IR.Semantics.widthOf we x := by
      simp [Sparkle.IR.Semantics.widthOf]
    rw [this]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | neg hx ihx =>
    rename_i x
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [evalList, Option.bind_eq_bind] at hvals
    obtain ⟨vx, hvx, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    obtain ⟨vnil, hvnil, hvals⟩ := Option.bind_eq_some_iff.mp hvals
    simp only [evalList, Option.some_inj] at hvnil
    subst hvnil
    simp only [Option.some_inj] at hvals
    subst hvals
    simp only [evalOp, Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | cmpU op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro v hv
    rcases hop with h' | h' | h' | h' | h' <;> subst h' <;>
    · simp only [evalExpr, Option.bind_eq_bind] at hv
      obtain ⟨vals, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      match vals, hv with
      | [x, y], hv =>
        simp only [evalOp, Option.some_inj] at hv
        subst hv
        simp only [Sparkle.IR.Semantics.widthOf]
        split <;> omega
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    rename_i a b
    intro v hv
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [evalExpr, Option.bind_eq_bind] at hv
      obtain ⟨vals, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      match vals, hv with
      | [x, y], hv =>
        simp only [evalOp, Option.some_inj] at hv
        subst hv
        simp only [Sparkle.IR.Semantics.widthOf]
        split <;> omega
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    rename_i a b
    intro v hv
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [evalExpr, Option.bind_eq_bind] at hv
      obtain ⟨vals, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      match vals, hv with
      | [x, y], hv =>
        simp only [evalOp, Option.some_inj] at hv
        subst hv
        simp only [Sparkle.IR.Semantics.widthOf]
        split <;> omega
  | sliceRef n hi lo hs hw hlo hhi hne =>
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind, Option.bind_some,
      Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | sliceRefFull n hi hs hw hfull =>
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind, Option.bind_some,
      Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | concat hall hpin ihall =>
    rename_i args
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    have := evalExpr_go_lt (we := we) args vals
      (evalList_length args vals hvals).symm
    simpa [Sparkle.IR.Semantics.widthOf] using this
  | castEnc w hw0 hx hsafe ihx =>
    rename_i x
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vin, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    rename_i x
    intro v hv
    simp only [evalExpr, Option.bind_eq_bind] at hv
    obtain ⟨vin, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    simp only [Option.some_inj] at hv
    subst hv
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | bitwiseShl op hop k kw ha himmA hk hkw hfit hc hDom iha ihc =>
    rename_i a c
    intro v hv
    rcases hop with h' | h' | h' <;> subst h' <;>
    · simp only [evalExpr, Option.bind_eq_bind] at hv
      obtain ⟨vals, _, hv⟩ := Option.bind_eq_some_iff.mp hv
      match vals, hv with
      | [x, y], hv =>
        simp only [evalOp, Option.some_inj] at hv
        subst hv
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | shiftOp op hop hwb ha hb iha ihb =>
    rename_i a b
    intro v hv
    rcases hop with h' | h' <;> subst h' <;>
    · simp only [evalExpr, Option.bind_eq_bind] at hv
      obtain ⟨vals, hvals, hv⟩ := Option.bind_eq_some_iff.mp hv
      simp only [evalList, Option.bind_eq_bind] at hvals
      obtain ⟨va, hva, hvals⟩ := Option.bind_eq_some_iff.mp hvals
      obtain ⟨vrest, hvrest, hvals⟩ := Option.bind_eq_some_iff.mp hvals
      obtain ⟨vb, hvb, hvrest⟩ := Option.bind_eq_some_iff.mp hvrest
      obtain ⟨vnil, hvnil, hvrest⟩ := Option.bind_eq_some_iff.mp hvrest
      simp only [evalList, Option.some_inj] at hvnil
      subst hvnil
      simp only [Option.some_inj] at hvrest hvals
      subst hvrest; subst hvals
      simp only [evalOp, Option.some_inj] at hv
      subst hv
      first
      | exact Nat.mod_lt _ (Nat.two_pow_pos _)
      | · -- shr: the result only loses bits
          have hba := iha va hva
          calc va >>> vb ≤ va := Nat.shiftRight_le va vb
            _ < 2 ^ Sparkle.IR.Semantics.widthOf we a := hba
            _ ≤ 2 ^ Sparkle.IR.Semantics.widthOf we (.op .shr [a, b]) := by
                simp [Sparkle.IR.Semantics.widthOf]

/-- Emissions of `immuneE` fragment shapes are context-immune
    (`immuneSV`) — the bridge from the IR-level side condition to the
    semantic stability lemma. -/
private theorem emit_immune {wof : String → Option Nat} {we : WEnv}
    {e : Expr} (h : SF4 wof we e) :
    immuneE e = true →
    ∀ sv, Tools.SVParser.EmitAst.emitAstExpr wof e = some sv →
      immuneSV sv = true := by
  induction h with
  | ref n hs hw =>
    intro himm sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs,
      Option.some_inj] at hsv
    subst hsv; rfl
  | const v w hw =>
    intro himm sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [immuneE, decide_eq_true_eq] at himm
    have h2 : (0 : Int) < ((2 ^ w : Nat) : Int) :=
      Int.natCast_pos.mpr (Nat.two_pow_pos w)
    by_cases hneg : v < 0
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_pos hneg, Option.some_inj] at hsv
      subst hsv
      simp only [immuneSV, decide_eq_true_eq,
        Tools.SVParser.EmitAst.encodeConst]
      have hlt := Int.emod_lt_of_pos
        (b := ((2 ^ w : Nat) : Int))
        ((v % ((2 ^ w : Nat) : Int)) + ((2 ^ w : Nat) : Int)) h2
      have hge := Int.emod_nonneg
        (b := ((2 ^ w : Nat) : Int))
        ((v % ((2 ^ w : Nat) : Int)) + ((2 ^ w : Nat) : Int))
        (Int.ne_of_gt h2)
      have hcast : ((((v % ((2 ^ w : Nat) : Int))
            + ((2 ^ w : Nat) : Int)) % ((2 ^ w : Nat) : Int)).toNat
            : Int) < ((2 ^ w : Nat) : Int) := by
        rw [Int.toNat_of_nonneg hge]; exact hlt
      exact Int.ofNat_lt.mp hcast
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_neg hneg, Option.some_inj] at hsv
      subst hsv
      simp only [immuneSV, decide_eq_true_eq]
      have hcast : ((v.toNat : Int)) < ((2 ^ w : Nat) : Int) := by
        rw [Int.toNat_of_nonneg (Int.not_lt.mp hneg)]; exact himm
      exact Int.ofNat_lt.mp hcast
  | binop op hop hA hB ha hb iha ihb =>
    intro himm sv hsv
    rcases hop with h' | h' | h' | h' | h' | h' <;> subst h' <;>
    first
    | (exfalso; simp [immuneE] at himm; done)
    | (simp only [immuneE, Bool.and_eq_true] at himm
       obtain ⟨himmA, himmB⟩ := himm
       simp only [Tools.SVParser.EmitAst.emitAstExpr,
         Option.bind_eq_bind] at hsv
       obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
       obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
       simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
         Option.some_inj] at hsv
       subst hsv
       simp only [immuneSV, Bool.and_eq_true]
       exact ⟨iha himmA sva hsa, ihb himmB svb hsb⟩)
  | mux hwf hc ht hf ihc iht ihf =>
    intro himm sv hsv
    simp only [immuneE, Bool.and_eq_true] at himm
    obtain ⟨himmT, himmF⟩ := himm
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svc, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svt, hst, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svf, hsf, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    simp only [immuneSV, Bool.and_eq_true]
    exact ⟨iht himmT svt hst, ihf himmF svf hsf⟩
  | not w hwT hwS hw0 hx ihx =>
    intro himm sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hwT, hne,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [hne, Bool.false_eq_true, if_false,
      Option.some_inj] at hsv
    subst hsv; rfl
  | neg hx ihx =>
    intro himm sv hsv
    exfalso
    simp [immuneE] at himm
  | cmpU op hop hA hB ha hb iha ihb =>
    intro himm sv hsv
    rcases hop with h' | h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv; rfl
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    intro himm sv hsv
    rename_i a b
    have hne : (max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b) == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hwTa, hwTb, hne,
        Bool.false_eq_true, if_false, Option.bind_eq_bind] at hsv
      obtain ⟨sva, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Option.some_inj] at hsv
      subst hsv
      rfl
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    intro himm sv hsv
    rename_i a b
    have hne : (Sparkle.IR.Semantics.widthOf we a == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hwTa, hwTb, hne,
        Bool.false_eq_true, if_false, Option.bind_eq_bind] at hsv
      obtain ⟨sva, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Option.some_inj] at hsv
      subst hsv
      rfl
  | sliceRef n hi lo hs hw hlo hhi hne' =>
    intro himm sv hsv
    have helide : (lo == 0 && hi + 1 == we n) = false := by
      rcases Nat.eq_zero_or_pos lo with h0 | h0
      · subst h0
        have : hi + 1 ≠ we n := fun hc => hne' ⟨rfl, hc⟩
        simp [this]
      · simp [Nat.pos_iff_ne_zero.mp h0]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      Bool.false_eq_true, if_false, if_pos hhi,
      Option.some_inj] at hsv
    subst hsv; rfl
  | sliceRefFull n hi hs hw hfull =>
    intro himm sv hsv
    have helide : (0 == 0 && hi + 1 == we n) = true := by simp [hfull]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      if_true, Option.some_inj] at hsv
    subst hsv; rfl
  | concat hall hpin ihall =>
    intro himm sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svs, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv; rfl
  | castEnc w hw0 hx hsafe ihx =>
    intro himm sv hsv
    have hsucc : w - 1 + 1 = w := Nat.sub_add_cancel hw0
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hsucc,
      beq_self_eq_true, Bool.and_self, if_true,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv; rfl
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    intro himm sv hsv
    rw [Tools.SVParser.EmitAst.emitAst_slice_general hi lo hcomp
      hncast] at hsv
    obtain ⟨inner, _, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    by_cases h0 : lo == 0 <;> simp only [h0, if_true, if_false,
      Bool.false_eq_true, Option.some_inj] at hsv <;> subst hsv <;> rfl
  | bitwiseShl op hop k kw ha himmA hk hkw hfit hc hDom iha ihc =>
    intro himm sv hsv
    exfalso
    rcases hop with h' | h' | h' <;> subst h' <;> simp [immuneE] at himm
  | shiftOp op hop hwb ha hb iha ihb =>
    intro himm sv hsv
    exfalso
    rcases hop with h' | h' <;> subst h' <;> simp [immuneE] at himm

/-- The bias-encoded operand `((x & m) ^ sb)` at context `W` reads
    exactly `vx ^^^ 2^(W-1)`, where `vx` is the operand's IR value. -/
private theorem biased_operand_sem {wof : String → Option Nat}
    {we : WEnv} {env : Env} {x : Expr} {sve : SVExpr} {vx : Nat}
    (W : Nat)
    (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn)
    (hx : SF4 wof we x)
    (hsx : Tools.SVParser.EmitAst.emitAstExpr wof x = some sve)
    (hwx : widthSV wof sve = some (Sparkle.IR.Semantics.widthOf we x))
    (hvxAt : evalAt wof env (Sparkle.IR.Semantics.widthOf we x) sve
      = evalExpr we env x)
    (hcond : Sparkle.IR.Semantics.widthOf we x = W ∨ immuneE x = true)
    (hWx : Sparkle.IR.Semantics.widthOf we x ≤ W)
    (hW0 : 0 < W)
    (hvx : evalExpr we env x = some vx) :
    widthSV wof (SVExpr.binary .bitXor
        (.binary .bitAnd sve (.lit (.hex (some W) (2 ^ W - 1))))
        (.lit (.hex (some W) (2 ^ (W - 1)))))
      = some W
    ∧ evalAt wof env W (SVExpr.binary .bitXor
        (.binary .bitAnd sve (.lit (.hex (some W) (2 ^ W - 1))))
        (.lit (.hex (some W) (2 ^ (W - 1)))))
      = some (vx ^^^ 2 ^ (W - 1))
    ∧ vx < 2 ^ W := by
  have hvW : vx < 2 ^ W :=
    Nat.lt_of_lt_of_le (sf4_bounded hx hbe vx hvx)
      (Nat.pow_le_pow_right (by omega) hWx)
  have hval : evalAt wof env W sve = some vx := by
    rcases hcond with hEq | himm
    · rw [← hEq, hvxAt]; exact hvx
    · rw [evalAt_immune (emit_immune hx himm sve hsx) hwx hbw W hWx,
        hvxAt]
      exact hvx
  refine ⟨?_, ?_, hvW⟩
  · simp [widthSV, hwx, Nat.max_eq_right hWx]
  · have hm1 : (2 : Nat) ^ W - 1 < 2 ^ W := by
      have := Nat.two_pow_pos W
      omega
    have hsb : (2 : Nat) ^ (W - 1) < 2 ^ W :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hand : vx &&& 2 ^ W - 1 = vx :=
      Nat.and_two_pow_sub_one_of_lt_two_pow hvW
    have hxor : vx ^^^ 2 ^ (W - 1) < 2 ^ W :=
      Nat.xor_lt_two_pow hvW hsb
    simp only [evalAt, litVal, hval, Option.bind_eq_bind,
      Option.bind_some, Option.some_inj]
    simp [mask, Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hsb,
      Nat.mod_eq_of_lt hvW, Nat.mod_eq_of_lt hxor, hand]

/- ---- Literal-amount left shifts: a VALUE claim, no width claim ---- -/

private theorem const_val_of_lt {k kw : Nat} (hk : k < 2 ^ kw) :
    (((k : Int) % ((2 ^ kw : Nat) : Int)) % ((2 ^ kw : Nat) : Int)).toNat
      % 2 ^ kw = k := by
  have hkI : (k : Int) < ((2 ^ kw : Nat) : Int) := Int.ofNat_lt.mpr hk
  have h1 : ((k : Int) % ((2 ^ kw : Nat) : Int)) = (k : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg k) hkI
  rw [h1, h1, Int.toNat_natCast, Nat.mod_eq_of_lt hk]

/-- **A literal-amount left shift computes the right VALUE at any
    sufficiently wide context** — without its self-determined width
    matching the IR's.

    `x << 32'd k` cannot ride `emit_sem`'s induction: the emission's
    width is the value operand's (Verilog's self-determined rule) while
    the IR's is the max with the amount's, so the induction invariant
    `widthSV = widthOf` is simply false here.  But a BITWISE parent
    never needs it: `evalAt`'s and/or/xor arms evaluate their operands
    at the PARENT's context width and never consult `widthSV`.

    `hfit` (the shifted value fits the node's width) is what makes the
    node's own mask inert under the parent's wider one.  Measured on
    the corpus: 40 of the 46 memory-side shifts satisfy it, and all 6
    that do not live in `array_128x38`, which is out for an unrelated
    reason anyway. -/
private theorem shl_val_at {wof : String → Option Nat} {we : WEnv} {env : Env}
    {a : Expr} {k kw : Nat} {sva : SVExpr}
    (ha : SF4 wof we a) (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn)
    (hk : k < 2 ^ kw) (himm : immuneE a = true)
    -- the shift must FIT its node width: only then is the node's own
    -- mask inert under a wider one
    (hfit : Sparkle.IR.Semantics.widthOf we a + k
      ≤ max (Sparkle.IR.Semantics.widthOf we a) kw)
    (hsa : Tools.SVParser.EmitAst.emitAstExpr wof a = some sva)
    (hwa : widthSV wof sva = some (Sparkle.IR.Semantics.widthOf we a))
    (hva : evalAt wof env (Sparkle.IR.Semantics.widthOf we a) sva
      = evalExpr we env a) :
    ∀ W, max (Sparkle.IR.Semantics.widthOf we a) kw ≤ W →
      evalAt wof env W
        (SVExpr.binary .shl sva (.lit (.decimal (some kw) k)))
      = (evalExpr we env (.op .shl [a, .const (Int.ofNat k) kw])).map
          (mask W) := by
  intro W hW
  obtain ⟨va, hva'⟩ := Option.isSome_iff_exists.mp (sf4_eval_isSome ha env)
  -- IR side
  have hIR : evalExpr we env (.op .shl [a, .const (Int.ofNat k) kw])
      = some (mask (max (Sparkle.IR.Semantics.widthOf we a) kw)
          (va <<< k)) := by
    simp only [evalExpr, evalList, hva', Option.bind_eq_bind,
      Option.bind_some, evalOp, Sparkle.IR.Semantics.widthOf,
      Option.some_inj, Int.ofNat_eq_natCast, Int.add_emod_right, mask]
    rw [const_val_of_lt hk]
  rw [hIR, Option.map_some]
  -- SV side
  have hamt : evalSV wof env 0 (SVExpr.lit (.decimal (some kw) k))
      = some k := by
    unfold evalSV
    simp [widthSV, evalAt, litVal, mask, Nat.mod_eq_of_lt hk]
  simp only [evalAt, hamt, Option.bind_eq_bind, Option.bind_some]
  have hvalA : evalAt wof env W sva = some va := by
    rw [evalAt_immune (emit_immune ha himm sva hsa) hwa hbw W (by omega),
      hva]
    exact hva'
  rw [hvalA]
  simp only [Option.bind_some, Option.some_inj]
  -- mask W (va <<< k) = mask W (mask (max wa kw) (va <<< k))
  -- the shifted value fits the node width, so the node's mask is a
  -- no-op and the outer mask at W agrees
  have hbnd : va < 2 ^ Sparkle.IR.Semantics.widthOf we a :=
    sf4_bounded ha hbe va hva'
  have hfits : va <<< k
      < 2 ^ max (Sparkle.IR.Semantics.widthOf we a) kw := by
    rw [Nat.shiftLeft_eq]
    calc va * 2 ^ k
        < 2 ^ Sparkle.IR.Semantics.widthOf we a * 2 ^ k :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos k)).mpr hbnd
      _ = 2 ^ (Sparkle.IR.Semantics.widthOf we a + k) :=
          (Nat.pow_add 2 _ k).symm
      _ ≤ 2 ^ max (Sparkle.IR.Semantics.widthOf we a) kw :=
          Nat.pow_le_pow_right (by omega) hfit
  simp [mask, Nat.mod_eq_of_lt hfits,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hfits
      (Nat.pow_le_pow_right (by omega) hW))]

/-- **Forward correctness, v0**: the emitted form has the same
    self-determined width AND, evaluated at the IR width as context,
    the same value as the IR expression. -/
theorem emit_sem {wof : String → Option Nat} {we : WEnv} {env : Env}
    {e : Expr} (h : SF4 wof we e) (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn) :
    ∀ sv, Tools.SVParser.EmitAst.emitAstExpr wof e = some sv →
      widthSV wof sv = some (Sparkle.IR.Semantics.widthOf we e)
      ∧ evalAt wof env (Sparkle.IR.Semantics.widthOf we e) sv
          = evalExpr we env e := by
  induction h with
  | ref n hs hw =>
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs,
      Option.some_inj] at hsv
    subst hsv
    refine ⟨by simp [widthSV, hw, Sparkle.IR.Semantics.widthOf], ?_⟩
    simp only [evalAt, hw, Option.bind_eq_bind, Option.bind_some,
      evalExpr, Sparkle.IR.Semantics.widthOf]
    have := hbe n
    simp [mask, Nat.mod_eq_of_lt this]
  | const v w hw =>
    intro sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    by_cases hneg : v < 0
    · -- negative: sized-hex two's complement — the emission carries the
      -- IR encode LITERALLY (`encodeConst` is the same formula), so the
      -- two masked values coincide definitionally.
      simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_pos hneg, Option.some_inj] at hsv
      subst hsv
      refine ⟨by simp [widthSV, Sparkle.IR.Semantics.widthOf], ?_⟩
      simp [evalAt, litVal, evalExpr, Sparkle.IR.Semantics.widthOf,
        Tools.SVParser.EmitAst.encodeConst]
    · -- nonnegative (fitting or not): both sides reduce `v` mod 2^w —
      -- the SV side by the context mask on the raw decimal, the IR side
      -- inside its two's-complement encode.
      simp only [Tools.SVParser.EmitAst.emitAstExpr, hne,
        if_neg hneg, Option.some_inj] at hsv
      subst hsv
      refine ⟨by simp [widthSV, hne, Sparkle.IR.Semantics.widthOf], ?_⟩
      simp only [evalAt, litVal, evalExpr, Sparkle.IR.Semantics.widthOf]
      congr 1
      rcases Int.eq_ofNat_of_zero_le (Int.not_lt.mp hneg) with ⟨n, rfl⟩
      have h2 : (0 : Int) < ((2 ^ w : Nat) : Int) :=
        Int.natCast_pos.mpr (Nat.two_pow_pos w)
      rw [Int.add_emod_right]
      have hmm : ∀ m : Nat, (m : Int) % ((2 ^ w : Nat) : Int)
          = ((m % 2 ^ w : Nat) : Int) := fun m => by omega
      rw [hmm n, hmm (n % 2 ^ w), Int.toNat_natCast, Int.toNat_natCast]
      simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  | bitwiseShl op hop k kw ha himmA hk hkw hfit hc hDom iha ihc =>
    rename_i a c
    intro sv hsv
    have hWshl : Sparkle.IR.Semantics.widthOf we
        (.op .shl [a, .const (Int.ofNat k) kw])
        = max (Sparkle.IR.Semantics.widthOf we a) kw := by
      simp [Sparkle.IR.Semantics.widthOf]
    have hle : Sparkle.IR.Semantics.widthOf we a
        ≤ Sparkle.IR.Semantics.widthOf we c := by omega
    rcases hop with h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svc, hsc, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwc, hvc⟩ := ihc svc hsc
      -- the shift's emission, decomposed
      obtain ⟨sva, hsa, hsb'⟩ := Option.bind_eq_some_iff.mp hsb
      have hnn : ¬((Int.ofNat k : Int) < 0) := by
        simp [Int.ofNat_eq_natCast]
      have hkwne : ((kw == 0) = true) = False := by
        simp only [beq_iff_eq, eq_iff_iff, iff_false]; omega
      simp only [hnn, if_false, hkwne, if_false,
        Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsb'
      obtain ⟨hwa, hva⟩ := iha sva hsa
      constructor
      · -- widths: the shl emission is `widthOf a` wide, c dominates
        rw [← hsb']
        simp only [widthSV, hwa, hwc, Option.bind_eq_bind,
          Option.bind_some, Sparkle.IR.Semantics.widthOf,
          Option.some_inj]
        omega
      · -- values: the parent evaluates both operands at ITS width
        have hWn : max (max (Sparkle.IR.Semantics.widthOf we a) kw)
            (Sparkle.IR.Semantics.widthOf we c)
            = Sparkle.IR.Semantics.widthOf we c := by omega
        simp only [Sparkle.IR.Semantics.widthOf, hWn]
        obtain ⟨va2, hva2⟩ := Option.isSome_iff_exists.mp
          (sf4_eval_isSome ha env)
        have hvb' : evalExpr we env
            (.op .shl [a, .const (Int.ofNat k) kw])
            = some (mask (max (Sparkle.IR.Semantics.widthOf we a) kw)
                (va2 <<< k)) := by
          simp only [evalExpr, evalList, hva2, Option.bind_eq_bind,
            Option.bind_some, evalOp, Sparkle.IR.Semantics.widthOf,
            Option.some_inj, Int.ofNat_eq_natCast, Int.add_emod_right,
            mask]
          rw [const_val_of_lt hk]
        obtain ⟨vc, hvcv⟩ := Option.isSome_iff_exists.mp
          (sf4_eval_isSome hc env)
        have hvbAt := shl_val_at ha hbe hbw hk himmA hfit hsa hwa hva
          (Sparkle.IR.Semantics.widthOf we c) (by omega)
        -- svb IS the emitted shl, so rewrite the goal's operand to it
        -- and apply the value lemma there
        have htn : (Int.ofNat k).toNat = k := by
          simp [Int.ofNat_eq_natCast]
        rw [htn] at hsb'
        rw [hsb'] at hvbAt
        simp only [evalAt, Option.bind_eq_bind, hvbAt, hvb',
          Option.map_some, Option.bind_some, hvc, hvcv, evalList,
          Option.bind_some, evalOp, Option.some_inj]
        -- the inner mask (at the shl's width) is absorbed: it lands
        -- below `widthOf c`, so the outer mask is a no-op on it
        have habs : ∀ x : Nat,
            x % 2 ^ max (Sparkle.IR.Semantics.widthOf we a) kw
              % 2 ^ Sparkle.IR.Semantics.widthOf we c
            = x % 2 ^ max (Sparkle.IR.Semantics.widthOf we a) kw := by
          intro x
          exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
            (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.pow_le_pow_right (by omega) (by omega)))
        simp only [mask, habs]
        -- unfold the IR side: both operand values are in hand
        have hlist : evalList we env
            [.op .shl [a, .const (Int.ofNat k) kw], c]
            = some [mask (max (Sparkle.IR.Semantics.widthOf we a) kw)
                (va2 <<< k), vc] := by
          simp only [evalList, Option.bind_eq_bind]
          rw [hvb', hvcv]
          simp
        simp only [evalExpr, Option.bind_eq_bind]
        rw [hlist]
        simp [evalOp, Sparkle.IR.Semantics.widthOf, hWn, mask, habs]

  | binop op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    rcases hop with h | h | h | h | h | h <;> subst h <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      -- each operand at the node's context (the max) reads its IR
      -- value: the max-width side by the IH directly, an immune side
      -- by stability
      have hA' : evalAt wof env
            (max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)) sva
          = evalExpr we env a := by
        rcases hA with hw' | himm
        · rw [← hw']; exact hva
        · rw [evalAt_immune (emit_immune ha himm sva hsa) hwa hbw _
            (Nat.le_max_left _ _)]
          exact hva
      have hB' : evalAt wof env
            (max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)) svb
          = evalExpr we env b := by
        rcases hB with hw' | himm
        · rw [← hw']; exact hvb
        · rw [evalAt_immune (emit_immune hb himm svb hsb) hwb hbw _
            (Nat.le_max_right _ _)]
          exact hvb
      constructor
      · simp only [widthSV, hwa, hwb, Option.bind_eq_bind,
          Option.bind_some, Sparkle.IR.Semantics.widthOf]
      · rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        cases hAv : evalExpr we env a with
        | none =>
          exact absurd hAv (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome ha env))
        | some va =>
        cases hBv : evalExpr we env b with
        | none =>
          exact absurd hBv (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome hb env))
        | some vb =>
        rw [hAv] at hA'
        rw [hBv] at hB'
        simp only [Sparkle.IR.Semantics.widthOf, evalAt,
          Option.bind_eq_bind, hA', hB', Option.bind_some, evalList,
          hAv, hBv, evalOp, Option.some_inj]
  | mux hwf hc ht hf ihc iht ihf =>
    rename_i c t f
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svc, hsc, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svt, hst, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨svf, hsf, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwc, hvc⟩ := ihc svc hsc
    obtain ⟨hwt, hvt⟩ := iht svt hst
    obtain ⟨hwff, hvf⟩ := ihf svf hsf
    constructor
    · simp [widthSV, hwt, hwff, Sparkle.IR.Semantics.widthOf, hwf,
        Nat.max_self]
    · -- condition is self-determined; arms inherit the context width
      have hW : Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])
          = Sparkle.IR.Semantics.widthOf we t := by
        simp [Sparkle.IR.Semantics.widthOf]
      rw [hW]
      simp only [evalAt, evalSV, Option.bind_eq_bind, hwc,
        Option.bind_some, Nat.max_eq_right (Nat.zero_le _), hvc]
      rw [show evalExpr we env (.op .mux [c, t, f])
            = ((evalList we env [c, t, f]).bind fun vals =>
                evalOp we .mux [c, t, f] vals
                  (Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])))
          from rfl]
      cases hC : evalExpr we env c with
      | none => simp [evalList, hC]
      | some vc =>
      cases hT : evalExpr we env t with
      | none =>
        exact absurd hT (Option.isSome_iff_ne_none.mp
          (sf4_eval_isSome ht env))
      | some vt =>
      cases hF : evalExpr we env f with
      | none =>
        exact absurd hF (Option.isSome_iff_ne_none.mp
          (sf4_eval_isSome hf env))
      | some vf =>
      simp only [evalList, hC, hT, hF, Option.bind_some,
        Option.bind_eq_bind, evalOp, Option.some_inj]
      have hvf' : evalAt wof env (Sparkle.IR.Semantics.widthOf we t) svf
          = evalExpr we env f := hwf ▸ hvf
      by_cases hvc0 : vc ≠ 0
      · rw [if_pos hvc0, if_pos hvc0, hvt, hT]
      · rw [if_neg hvc0, if_neg hvc0, hvf', hF]
  | not w hwT hwS hw0 hx ihx =>
    rename_i x
    intro sv hsv
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hwT, hne,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, hsx, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [hne, Bool.false_eq_true, if_false,
      Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwx, hvx⟩ := ihx svx hsx
    have hW : Sparkle.IR.Semantics.widthOf we (.op .not [x]) = w := by
      simp [Sparkle.IR.Semantics.widthOf, hwS]
    constructor
    · simp [widthSV, hW]
    · rw [hW]
      -- the emitted `w'(x ^ w'dM)`: cast boundary puts the xor in a
      -- w-bit context, and everything is width w
      simp only [evalAt, evalSV, Option.bind_eq_bind, widthSV, hwx,
        hwS, Option.bind_some, Nat.max_self,
        Nat.max_eq_right (Nat.le_refl w)]
      rw [show evalExpr we env (.op .not [x])
            = ((evalList we env [x]).bind fun vals =>
                evalOp we .not [x] vals
                  (Sparkle.IR.Semantics.widthOf we (.op .not [x])))
          from rfl]
      cases hX : evalExpr we env x with
      | none => simp [evalList, hX, hvx, hwS ▸ hvx]
      | some vx =>
      simp only [evalList, hX, Option.bind_some, Option.bind_eq_bind,
        evalOp, Option.some_inj, litVal]
      rw [hwS] at hvx
      simp only [hvx, hX, Option.bind_some]
      -- mask w (mask w (vx ^^^ mask w (2^w-1))) = mask w (vx ^^^ (2^w-1))
      have hm : mask w ((2 : Nat) ^ w - 1) = 2 ^ w - 1 := by
        have := Nat.two_pow_pos w
        simp [mask, Nat.mod_eq_of_lt (by omega)]
      simp [mask, hm, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), hwS]
  | neg hx ihx =>
    rename_i x
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, hsx, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwx, hvx⟩ := ihx svx hsx
    have hW : Sparkle.IR.Semantics.widthOf we (.op .neg [x])
        = Sparkle.IR.Semantics.widthOf we x := by
      simp [Sparkle.IR.Semantics.widthOf]
    constructor
    · simp [widthSV, hwx, hW]
    · rw [hW]
      -- both sides: mask w (2^w - mask w v) at w = widthOf x
      rw [show evalExpr we env (.op .neg [x])
            = ((evalList we env [x]).bind fun vals =>
                evalOp we .neg [x] vals
                  (Sparkle.IR.Semantics.widthOf we (.op .neg [x])))
          from rfl]
      cases hX : evalExpr we env x with
      | none =>
        exact absurd hX (Option.isSome_iff_ne_none.mp
          (sf4_eval_isSome hx env))
      | some vx =>
      rw [hX] at hvx
      simp only [evalAt, hvx, Option.bind_eq_bind, Option.bind_some,
        evalList, hX, evalOp, Sparkle.IR.Semantics.widthOf,
        Option.some_inj]
  | cmpU op hop hA hB ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    rcases hop with h | h | h | h | h <;> subst h <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      -- comparison operands are SELF-determined: they size to their
      -- own max.  Width agreement pins that to the IH's width; when
      -- instead both emissions are context-immune, up-sizing to the
      -- max is inert (evalAt_immune).
      have hA' : evalAt wof env
            (max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)) sva
          = evalExpr we env a := by
        rcases hA with hw' | himm
        · rw [← hw']; exact hva
        · rw [evalAt_immune (emit_immune ha himm sva hsa) hwa hbw _
            (Nat.le_max_left _ _)]
          exact hva
      have hB' : evalAt wof env
            (max (Sparkle.IR.Semantics.widthOf we a)
              (Sparkle.IR.Semantics.widthOf we b)) svb
          = evalExpr we env b := by
        rcases hB with hw' | himm
        · rw [← hw']; exact hvb
        · rw [evalAt_immune (emit_immune hb himm svb hsb) hwb hbw _
            (Nat.le_max_right _ _)]
          exact hvb
      constructor
      · simp [widthSV, Sparkle.IR.Semantics.widthOf]
      · rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        cases hA : evalExpr we env a with
        | none =>
          exact absurd hA (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome ha env))
        | some va =>
        cases hB : evalExpr we env b with
        | none =>
          exact absurd hB (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome hb env))
        | some vb =>
        simp only [evalAt, hwa, hwb, Option.bind_eq_bind,
          Option.bind_some, hA', hB', hA, hB,
          evalList, evalOp, Option.some_inj]
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    have hne : (max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b) == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hwTa, hwTb, hne,
        Bool.false_eq_true, if_false, Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      obtain ⟨vA, hvA⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome ha env)
      obtain ⟨vB, hvB⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome hb env)
      obtain ⟨hWa, hVa, hbndA⟩ := biased_operand_sem
        (max (Sparkle.IR.Semantics.widthOf we a)
          (Sparkle.IR.Semantics.widthOf we b))
        hbe hbw ha hsa hwa hva hA (Nat.le_max_left _ _) hw0 hvA
      obtain ⟨hWb, hVb, hbndB⟩ := biased_operand_sem
        (max (Sparkle.IR.Semantics.widthOf we a)
          (Sparkle.IR.Semantics.widthOf we b))
        hbe hbw hb hsb hwb hvb hB (Nat.le_max_right _ _) hw0 hvB
      constructor
      · simp [widthSV, Sparkle.IR.Semantics.widthOf]
      · rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        simp only [evalList, hvA, hvB, Option.bind_eq_bind,
          Option.bind_some, evalOp]
        -- make the biased operands opaque so unfolding `evalAt` stops
        -- at the comparison arm
        obtain ⟨A, hAdef⟩ : ∃ A, SVExpr.binary .bitXor
            (.binary .bitAnd sva (.lit (.hex
              (some (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b)))
              (2 ^ max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b) - 1))))
            (.lit (.hex
              (some (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b)))
              (2 ^ (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b) - 1)))) = A :=
          ⟨_, rfl⟩
        obtain ⟨B, hBdef⟩ : ∃ B, SVExpr.binary .bitXor
            (.binary .bitAnd svb (.lit (.hex
              (some (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b)))
              (2 ^ max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b) - 1))))
            (.lit (.hex
              (some (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b)))
              (2 ^ (max (Sparkle.IR.Semantics.widthOf we a)
                (Sparkle.IR.Semantics.widthOf we b) - 1)))) = B :=
          ⟨_, rfl⟩
        rw [hAdef] at hWa hVa
        rw [hBdef] at hWb hVb
        rw [hAdef, hBdef]
        simp only [evalAt, hWa, hWb, Option.bind_eq_bind,
          Option.bind_some, Nat.max_self, hVa, hVb, Option.some_inj]
        first
        | (simp only [biased_lt hw0 hbndA hbndB])
        | (simp only [biased_le hw0 hbndA hbndB])
        | (simp only [biased_lt hw0 hbndB hbndA])
        | (simp only [biased_le hw0 hbndB hbndA])
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    have hne : (Sparkle.IR.Semantics.widthOf we a == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    have hmaxw : max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b)
        = Sparkle.IR.Semantics.widthOf we a := Nat.max_eq_left hwba
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr, hwTa, hwTb, hne,
        Bool.false_eq_true, if_false, Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb, hvb⟩ := ihb svb hsb
      obtain ⟨vA, hvA⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome ha env)
      obtain ⟨vB, hvB⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome hb env)
      obtain ⟨hWa, hVa, hbndA⟩ := biased_operand_sem
        (Sparkle.IR.Semantics.widthOf we a)
        hbe hbw ha hsa hwa hva (Or.inl rfl) (Nat.le_refl _) hw0 hvA
      obtain ⟨hWb, hVb, hbndB⟩ := biased_operand_sem
        (Sparkle.IR.Semantics.widthOf we a)
        hbe hbw hb hsb hwb hvb hB hwba hw0 hvB
      constructor
      · simp [widthSV, Sparkle.IR.Semantics.widthOf]
      · rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        simp only [evalList, hvA, hvB, Option.bind_eq_bind,
          Option.bind_some, evalOp, hmaxw]
        obtain ⟨A, hAdef⟩ : ∃ A, SVExpr.binary .bitXor
            (.binary .bitAnd sva (.lit (.hex
              (some (Sparkle.IR.Semantics.widthOf we a))
              (2 ^ Sparkle.IR.Semantics.widthOf we a - 1))))
            (.lit (.hex
              (some (Sparkle.IR.Semantics.widthOf we a))
              (2 ^ (Sparkle.IR.Semantics.widthOf we a - 1)))) = A :=
          ⟨_, rfl⟩
        obtain ⟨B, hBdef⟩ : ∃ B, SVExpr.binary .bitXor
            (.binary .bitAnd svb (.lit (.hex
              (some (Sparkle.IR.Semantics.widthOf we a))
              (2 ^ Sparkle.IR.Semantics.widthOf we a - 1))))
            (.lit (.hex
              (some (Sparkle.IR.Semantics.widthOf we a))
              (2 ^ (Sparkle.IR.Semantics.widthOf we a - 1)))) = B :=
          ⟨_, rfl⟩
        rw [hAdef] at hWa hVa
        rw [hBdef] at hWb hVb
        rw [hAdef, hBdef]
        simp only [evalAt, hWa, hWb, Option.bind_eq_bind,
          Option.bind_some, Nat.max_self, hVa, hVb, Option.some_inj]
        first
        | (simp only [biased_lt hw0 hbndA hbndB])
        | (simp only [biased_le hw0 hbndA hbndB])
        | (simp only [biased_lt hw0 hbndB hbndA])
        | (simp only [biased_le hw0 hbndB hbndA])
  | sliceRef n hi lo hs hw hlo hhi hne =>
    intro sv hsv
    -- unfold the emitter on the non-castEnc, non-elided, in-range slice
    have helide : (lo == 0 && hi + 1 == we n) = false := by
      rcases Nat.eq_zero_or_pos lo with h0 | h0
      · subst h0
        have : hi + 1 ≠ we n := fun hc => hne ⟨rfl, hc⟩
        simp [this]
      · simp [Nat.pos_iff_ne_zero.mp h0]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      Bool.false_eq_true, if_false, if_pos hhi,
      Option.some_inj] at hsv
    subst hsv
    constructor
    · simp [widthSV, Sparkle.IR.Semantics.widthOf]
    · simp only [Sparkle.IR.Semantics.widthOf, evalAt, hw,
        Option.bind_eq_bind, Option.bind_some, evalExpr,
        if_pos (And.intro hlo hhi)]
      simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  | concat hall hpin ihall =>
    rename_i args
    intro sv hsv
    simp only [Tools.SVParser.EmitAst.emitAstExpr,
      Option.bind_eq_bind] at hsv
    obtain ⟨svs, hsvs, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    have hsome : ∀ e, e ∈ args → (evalExpr we env e).isSome :=
      fun e he => sf4_eval_isSome (hall e he) env
    obtain ⟨hwgo, vals, hvals, hgo, hbnd⟩ :=
      concat_elems_sem args svs hsome (fun e he => ihall e he) hpin hsvs
    constructor
    · simpa [widthSV, Sparkle.IR.Semantics.widthOf] using hwgo
    · simp only [evalAt, Option.bind_eq_bind, hgo, Option.bind_some,
        evalExpr, hvals, Sparkle.IR.Semantics.widthOf,
        Option.some_inj]
      simp [mask, Nat.mod_eq_of_lt hbnd]
  | castEnc w hw0 hx hsafe ihx =>
    rename_i x
    intro sv hsv
    have hsucc : w - 1 + 1 = w := Nat.sub_add_cancel hw0
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hsucc,
      beq_self_eq_true, Bool.and_self, if_true,
      Option.bind_eq_bind] at hsv
    obtain ⟨svx, hsx, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    simp only [Option.some_inj] at hsv
    subst hsv
    obtain ⟨hwx, hvx⟩ := ihx svx hsx
    obtain ⟨vx, hvxv⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hx env)
    have hW : Sparkle.IR.Semantics.widthOf we
        (.slice (.concat [.const 0 w, x]) (w - 1) 0) = w := by
      simp [Sparkle.IR.Semantics.widthOf, hsucc]
    constructor
    · simp [widthSV, hW]
    · rw [hW]
      -- SV side: the cast's argument sees a w-bit context
      have hstab : evalAt wof env
            (max w (Sparkle.IR.Semantics.widthOf we x)) svx
          = some vx := by
        rcases hsafe with hle | himm
        · rw [Nat.max_eq_right hle, hvx]; exact hvxv
        · rw [evalAt_immune (emit_immune hx himm svx hsx) hwx hbw _
            (Nat.le_max_right _ _), hvx]
          exact hvxv
      have hSV : evalAt wof env w (.sizeCast w svx)
          = some (mask w (mask w vx)) := by
        simp only [evalAt]
        unfold evalSV
        simp [hwx, hstab]
      rw [hSV]
      -- IR side: slice of the zero-extension concat
      have hc0 : evalExpr we env (.const 0 w) = some 0 := by
        simp only [evalExpr, Option.some_inj]
        simp [Int.zero_emod, Int.zero_add, Int.emod_self, mask]
      have hIR : evalExpr we env
          (.slice (.concat [.const 0 w, x]) (w - 1) 0)
          = some (mask w (mask (Sparkle.IR.Semantics.widthOf we x) vx)) := by
        simp only [evalExpr, evalList, hc0, hvxv, Option.bind_eq_bind,
          Option.bind_some, Option.some_inj,
          Sparkle.IR.Semantics.evalExpr.go]
        simp [mask, Nat.shiftRight_zero, Nat.shiftLeft_eq, hsucc,
          Nat.zero_mod, Nat.sub_zero]
      rw [hIR, Option.some_inj]
      -- mask w (mask w vx) = mask w (mask wx vx)
      rcases hsafe with hle | himm
      · -- down/equal cast: both collapse to mask w vx
        simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _),
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hle)]
      · -- up-cast of an immune shape: the value already fits its width
        have hb := sf4_bounded hx hbe vx hvxv
        simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _),
          Nat.mod_eq_of_lt hb]
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    rename_i x
    intro sv hsv
    rw [Tools.SVParser.EmitAst.emitAst_slice_general hi lo hcomp
      hncast] at hsv
    obtain ⟨inner, hsx, hsv⟩ := Option.bind_eq_some_iff.mp hsv
    obtain ⟨hwx, hvx⟩ := ihx inner hsx
    obtain ⟨vx, hvxv⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hx env)
    have hn : hi + 1 - lo = hi - lo + 1 := by omega
    have hW : Sparkle.IR.Semantics.widthOf we (.slice x hi lo)
        = hi - lo + 1 := by simp [Sparkle.IR.Semantics.widthOf]
    -- the cast's argument (the value, possibly shifted) sees a context
    -- of max(cast width, its own); both hsafe branches pin the value
    have hstab : ∀ W', Sparkle.IR.Semantics.widthOf we x ≤ W' →
        (W' = max (hi + 1 - lo) (Sparkle.IR.Semantics.widthOf we x)) →
        evalAt wof env W' inner = some vx := by
      intro W' _ hmax
      rcases hsafe with hle | himm
      · rw [hmax, Nat.max_eq_right hle, hvx]; exact hvxv
      · rw [hmax, evalAt_immune (emit_immune hx himm inner hsx) hwx
          hbw _ (Nat.le_max_right _ _), hvx]
        exact hvxv
    have hIR : evalExpr we env (.slice x hi lo)
        = some (mask (hi - lo + 1) (vx >>> lo)) := by
      simp [evalExpr, hvxv]
    by_cases h0 : lo = 0
    · subst h0
      simp only [if_pos rfl, beq_self_eq_true, if_true,
        Option.some_inj] at hsv
      subst hsv
      constructor
      · simp [widthSV, hW, Nat.sub_zero]
      · rw [hW]
        simp only [Nat.sub_zero, evalAt]
        unfold evalSV
        simp only [hwx, Option.bind_eq_bind, Option.bind_some]
        rw [hstab _ (Nat.le_max_right _ _) (by simp)]
        rw [hIR, Option.bind_some, Option.some_inj]
        simp [mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _),
          Nat.shiftRight_zero, Nat.sub_zero]
    · have h0' : (lo == 0) = false := by simp [h0]
      simp only [h0', Bool.false_eq_true, if_false,
        Option.some_inj] at hsv
      subst hsv
      constructor
      · simp [widthSV, hW, hn]
      · rw [hW]
        simp only [evalAt]
        unfold evalSV
        simp only [widthSV, hwx, Option.bind_eq_bind, Option.bind_some]
        -- expose the shift arm, then pin the shifted value:
        -- E at max(n, wx), then >>> lo
        simp only [evalAt, Option.bind_eq_bind]
        rw [hstab _ (Nat.le_max_right _ _) rfl]
        have hamt : evalSV wof env 0 (.lit (.decimal none lo))
            = some lo := by
          unfold evalSV
          simp [widthSV, evalAt, litVal, mask, Nat.mod_eq_of_lt hlo32]
        rw [hamt, hIR]
        simp [hn, mask, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  | shiftOp op hop hwb ha hb iha ihb =>
    rename_i a b
    intro sv hsv
    have hmax : op = .shl →
        max (Sparkle.IR.Semantics.widthOf we a)
          (Sparkle.IR.Semantics.widthOf we b)
        = Sparkle.IR.Semantics.widthOf we a := by
      intro hshl
      rcases hwb with hs | hle
      · rw [hshl] at hs; exact absurd hs (by simp)
      · exact Nat.max_eq_left hle
    rcases hop with h | h <;> subst h <;>
    · simp only [Tools.SVParser.EmitAst.emitAstExpr,
        Option.bind_eq_bind] at hsv
      obtain ⟨sva, hsa, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      obtain ⟨svb, hsb, hsv⟩ := Option.bind_eq_some_iff.mp hsv
      simp only [Tools.SVParser.EmitAst.binOpOf, Option.bind_some,
        Option.some_inj] at hsv
      subst hsv
      obtain ⟨hwa, hva⟩ := iha sva hsa
      obtain ⟨hwb', hvb⟩ := ihb svb hsb
      -- the amount is self-determined at its own width — exactly the
      -- IH's evaluation
      have hamt : evalSV wof env 0 svb = evalExpr we env b := by
        unfold evalSV
        simp [hwb', hvb]
      constructor
      · first
        | simp only [widthSV, hwa, Sparkle.IR.Semantics.widthOf,
            hmax rfl]
        | simp only [widthSV, hwa, Sparkle.IR.Semantics.widthOf]
      · rw [show Sparkle.IR.Semantics.widthOf we (.op _ [a, b])
            = Sparkle.IR.Semantics.widthOf we a from by
          first
          | simp [Sparkle.IR.Semantics.widthOf, hmax rfl]
          | simp [Sparkle.IR.Semantics.widthOf]]
        rw [show evalExpr we env (.op _ [a, b])
              = ((evalList we env [a, b]).bind fun vals =>
                  evalOp we _ [a, b] vals
                    (Sparkle.IR.Semantics.widthOf we (.op _ [a, b])))
            from rfl]
        cases hA : evalExpr we env a with
        | none =>
          exact absurd hA (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome ha env))
        | some va =>
        cases hB : evalExpr we env b with
        | none =>
          exact absurd hB (Option.isSome_iff_ne_none.mp
            (sf4_eval_isSome hb env))
        | some vb =>
        rw [hA] at hva
        rw [hB] at hamt
        first
        | simp only [evalAt, hva, hamt, Option.bind_eq_bind,
            Option.bind_some, evalList, hA, hB, evalOp,
            Sparkle.IR.Semantics.widthOf, hmax rfl, Option.some_inj]
        | simp only [evalAt, hva, hamt, Option.bind_eq_bind,
            Option.bind_some, evalList, hA, hB, evalOp,
            Sparkle.IR.Semantics.widthOf, Option.some_inj]
  | sliceRefFull n hi hs hw hfull =>
    intro sv hsv
    have helide : (0 == 0 && hi + 1 == we n) = true := by simp [hfull]
    simp only [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide,
      if_true, Option.some_inj] at hsv
    subst hsv
    constructor
    · simp [widthSV, hw, Sparkle.IR.Semantics.widthOf, hfull]
    · simp only [Sparkle.IR.Semantics.widthOf, evalAt, hw,
        Option.bind_eq_bind, Option.bind_some, evalExpr,
        Nat.sub_zero, Option.some_inj]
      simp [Nat.shiftRight_zero]

private theorem emitConcatElems_isSome {wof : String → Option Nat} :
    ∀ (args : List Expr),
      (∀ e, e ∈ args → (Tools.SVParser.EmitAst.emitAstExpr wof e).isSome) →
      (Tools.SVParser.EmitAst.emitConcatElems wof args).isSome := by
  intro args
  induction args with
  | nil => intro _; simp [Tools.SVParser.EmitAst.emitConcatElems]
  | cons a rest ih =>
    intro hall
    obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp
      (hall a (List.mem_cons_self ..))
    obtain ⟨es, hes⟩ := Option.isSome_iff_exists.mp
      (ih fun e he => hall e (List.mem_cons_of_mem _ he))
    simp [Tools.SVParser.EmitAst.emitConcatElems, hea, hes]

/-- Fragment expressions always EMIT: the emitter is total on `SF4`.
    (Together with `emit_sem` this upgrades the per-expression theorem
    from "if it emits, it is right" to "it emits, and is right".) -/
theorem sf4_emit_isSome {wof : String → Option Nat} {we : WEnv}
    {e : Expr} (h : SF4 wof we e) :
    (Tools.SVParser.EmitAst.emitAstExpr wof e).isSome := by
  induction h with
  | ref n hs hw => simp [Tools.SVParser.EmitAst.emitAstExpr, hs]
  | const v w hw =>
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    by_cases hneg : v < 0 <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hne, hneg]
  | binop op hop hA hB ha hb iha ihb =>
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    rcases hop with h' | h' | h' | h' | h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb,
        Tools.SVParser.EmitAst.binOpOf]
  | mux hwf hc ht hf ihc iht ihf =>
    obtain ⟨svc, hsc⟩ := Option.isSome_iff_exists.mp ihc
    obtain ⟨svt, hst⟩ := Option.isSome_iff_exists.mp iht
    obtain ⟨svf, hsf⟩ := Option.isSome_iff_exists.mp ihf
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsc, hst, hsf]
  | not w hwT hwS hw0 hx ihx =>
    obtain ⟨svx, hsx⟩ := Option.isSome_iff_exists.mp ihx
    have hne : (w == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsx, hwT, hne]
  | neg hx ihx =>
    obtain ⟨svx, hsx⟩ := Option.isSome_iff_exists.mp ihx
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsx]
  | cmpU op hop hA hB ha hb iha ihb =>
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    rcases hop with h' | h' | h' | h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb,
        Tools.SVParser.EmitAst.binOpOf]
  | cmpS op hop hwTa hwTb hA hB hw0 ha hb iha ihb =>
    rename_i a b
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    have hne : (max (Sparkle.IR.Semantics.widthOf we a)
        (Sparkle.IR.Semantics.widthOf we b) == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb, hwTa, hwTb,
        hne]
  | cmpS1 op hop hwTa hwTb hwba hB hw0 ha hb iha ihb =>
    rename_i a b
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    have hne : (Sparkle.IR.Semantics.widthOf we a == 0) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    rcases hop with h' | h' | h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb, hwTa, hwTb,
        hne]
  | sliceRef n hi lo hs hw hlo hhi hne =>
    have helide : (lo == 0 && hi + 1 == we n) = false := by
      rcases Nat.eq_zero_or_pos lo with h0 | h0
      · subst h0
        have : hi + 1 ≠ we n := fun hc => hne ⟨rfl, hc⟩
        simp [this]
      · simp [Nat.pos_iff_ne_zero.mp h0]
    simp [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide, hhi]
  | sliceRefFull n hi hs hw hfull =>
    have helide : (0 == 0 && hi + 1 == we n) = true := by simp [hfull]
    simp [Tools.SVParser.EmitAst.emitAstExpr, hs, hw, helide, hfull]
  | concat hall hpin ihall =>
    rename_i args
    obtain ⟨svs, hsvs⟩ := Option.isSome_iff_exists.mp
      (emitConcatElems_isSome args fun e he => ihall e he)
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsvs]
  | castEnc w hw0 hx hsafe ihx =>
    obtain ⟨svx, hsx⟩ := Option.isSome_iff_exists.mp ihx
    have hsucc : w - 1 + 1 = w := Nat.sub_add_cancel hw0
    simp [Tools.SVParser.EmitAst.emitAstExpr, hsucc, hsx]
  | sliceGen hi lo hcomp hncast hlo hlo32 hx hsafe ihx =>
    obtain ⟨svx, hsx⟩ := Option.isSome_iff_exists.mp ihx
    rw [Tools.SVParser.EmitAst.emitAst_slice_general hi lo hcomp
      hncast]
    by_cases h0 : lo == 0 <;> simp [hsx, h0]
  | bitwiseShl op hop k kw ha himmA hk hkw hfit hc hDom iha ihc =>
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svc, hsc⟩ := Option.isSome_iff_exists.mp ihc
    rcases hop with h' | h' | h' <;> subst h' <;>
      (simp only [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsc,
         Tools.SVParser.EmitAst.binOpOf, Option.bind_eq_bind,
         Option.bind_some]
       split <;> simp [hsa, hsc, Tools.SVParser.EmitAst.binOpOf])
  | shiftOp op hop hwb ha hb iha ihb =>
    obtain ⟨sva, hsa⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨svb, hsb⟩ := Option.isSome_iff_exists.mp ihb
    rcases hop with h' | h' <;> subst h' <;>
      simp [Tools.SVParser.EmitAst.emitAstExpr, hsa, hsb,
        Tools.SVParser.EmitAst.binOpOf]

/-- Is this expression a literal-amount left shift?  A top-level
    definition so its equation lemmas are available to proofs, rather
    than an inline `match` whose splitting leaks side goals. -/
def isShlLit : Expr → Bool
  | .op .shl [_, .const _ _] => true
  | _ => false

/-- Decidable side conditions of `bitwiseShl` on the LEFT operand:
    `a` must BE `x << const k kw` with the rule's conditions met.  The
    sub-fragment check is NOT here — `sf4Check` supplies it via
    `shlOperand`, so this stays independent of the checker. -/
def shlSideOK (we : WEnv) (a b : Expr) : Bool :=
  match a with
  | .op .shl [x, .const kk kw] =>
    (0 ≤ kk) && (decide (kk.toNat < 2 ^ kw)) && (decide (0 < kw))
      && (decide (Sparkle.IR.Semantics.widthOf we x + kk.toNat
            ≤ max (Sparkle.IR.Semantics.widthOf we x) kw))
      && immuneE x
      && (decide (max (Sparkle.IR.Semantics.widthOf we x) kw
            ≤ Sparkle.IR.Semantics.widthOf we b))
  | _ => false

/-- The VALUE operand of a literal-amount shift, or the expression
    itself otherwise.  `sf4Check` recurses through this so the shl
    route's sub-check rides an ordinary structural recursion. -/
def shlOperand : Expr → Expr
  | .op .shl [x, .const _ _] => x
  | e => e

/-- `shlOperand` never grows its argument — what the termination proof
    of `sf4Check` needs. -/
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


/-- Soundness of the side test: with the operand's fragment fact, the
    `bitwiseShl` rule applies. -/
theorem shlSideOK_sound {wof : String → Option Nat} {we : WEnv}
    {a b : Expr}
    (hfa : SF4 wof we (shlOperand a))
    (h : shlSideOK we a b = true)
    (hfb : SF4 wof we b) (op : Operator)
    (hop : op = .and ∨ op = .or ∨ op = .xor) :
    SF4 wof we (.op op [a, b]) := by
  match a, h, hfa with
  | .op .shl [x, .const kk kw], h, hfa =>
    simp only [shlSideOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hnn, hk⟩, hkw⟩, hfit⟩, himm⟩, hdom⟩ := h
    simp only [shlOperand] at hfa
    obtain ⟨k, hkdef⟩ : ∃ k : Nat, kk = Int.ofNat k := by
      refine ⟨kk.toNat, ?_⟩
      simp only [Int.ofNat_eq_natCast]
      omega
    subst hkdef
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast] at hk hfit
    exact SF4.bitwiseShl op hop k kw hfa himm hk hkw hfit hfb hdom

/-- Decidable mirror of `SF4` — the per-expression forward-fragment
    membership test the census and gate run.  Soundness below ties a
    `true` verdict to the `emit_sem` theorem. -/
def sf4Check (wof : String → Option Nat) (we : WEnv) :
    Expr → Bool
  | .ref n =>
    (Sparkle.Backend.Verilog.sanitizeName n == n)
      && (wof n == some (we n))
  | .const _ w => 0 < w
  | .op .neg [x] => sf4Check wof we x
  | .op .not [x] =>
    (Tools.SVParser.EmitAst.exprWidthT wof x
        == some (Sparkle.IR.Semantics.widthOf we x))
      && (0 < Sparkle.IR.Semantics.widthOf we x)
      && sf4Check wof we x
  | .op .mux [c, t, f] =>
    (Sparkle.IR.Semantics.widthOf we f
        == Sparkle.IR.Semantics.widthOf we t)
      && sf4Check wof we c && sf4Check wof we t && sf4Check wof we f
  | .op op [a, b] =>
    let wa := Sparkle.IR.Semantics.widthOf we a
    let wb := Sparkle.IR.Semantics.widthOf we b
    -- All THREE recursive calls are made unconditionally and at the
    -- arm's top level, so `sf4Check.induct` hands out one IH each and
    -- both routes below have what they need.  (`shlOperand a` is `a`
    -- itself unless `a` is a literal-amount shift.)
    -- ONE recursive call on the left, through `shlOperand`.  When `a`
    -- is a literal-amount shift the shl route is the only one that can
    -- fire (`sf4Check` rejects the shift node itself), and when it is
    -- not, `shlOperand a = a` — so a single call serves both routes.
    -- Recursing on BOTH `a` and `shlOperand a` re-walked the left
    -- subtree at every bitwise level: 249 nodes became 19.7 M calls.
    let chkL := sf4Check wof we (shlOperand a)
    let chkB := sf4Check wof we b
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
      ((Tools.SVParser.EmitAst.exprWidthT wof a == some wa)
        && (Tools.SVParser.EmitAst.exprWidthT wof b == some wb)
        && (0 < max wa wb) && perOp) ||
      ((Tools.SVParser.EmitAst.exprWidthT wof a == some wa)
        && (Tools.SVParser.EmitAst.exprWidthT wof b == none)
        && (wb ≤ wa) && ((wb == wa) || immuneE b) && (0 < wa)
        && notShl && chkL && chkB)
    | _ => false
  | .concat args =>
    args.attach.all fun ⟨e, _⟩ =>
      sf4Check wof we e &&
      (match e with
       | .op _ _ =>
         (Tools.SVParser.EmitAst.exprWidthT wof e
             == some (Sparkle.IR.Semantics.widthOf we e))
           && (0 < Sparkle.IR.Semantics.widthOf we e)
       | _ => true)
  | .slice (.concat [.const 0 w, x]) hi lo =>
    -- canonical cast encode, or the general-slice route over the concat
    ((lo == 0) && (hi + 1 == w) && (0 < w) && sf4Check wof we x
      && ((w ≤ Sparkle.IR.Semantics.widthOf we x) || immuneE x)) ||
    (!(lo == 0 && hi + 1 == w) && (lo ≤ hi) && (lo < 2 ^ 32)
      && sf4Check wof we (.concat [.const 0 w, x])
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
    (lo ≤ hi) && (lo < 2 ^ 32) && sf4Check wof we x
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

set_option maxHeartbeats 1600000 in
/-- Soundness of the mirror: a `true` verdict puts the expression in
    the proven forward fragment, so `emit_sem` applies to it. -/
theorem sf4Check_sound {wof : String → Option Nat} {we : WEnv} :
    ∀ {e : Expr}, sf4Check wof we e = true → SF4 wof we e := by
  intro e h
  induction e using sf4Check.induct wof we
  case case1 n =>
    simp only [sf4Check, Bool.and_eq_true, beq_iff_eq] at h
    exact SF4.ref n h.1 h.2
  case case2 v w =>
    simp only [sf4Check, decide_eq_true_eq] at h
    exact SF4.const v w h
  case case3 x ih =>
    simp only [sf4Check] at h
    exact SF4.neg (ih h)
  case case4 x ih =>
    simp only [sf4Check, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    exact SF4.not _ h.1.1 rfl h.1.2 (ih h.2)
  case case5 c t f ihc iht ihf =>
    simp only [sf4Check, Bool.and_eq_true, beq_iff_eq] at h
    exact SF4.mux h.1.1.1 (ihc h.1.1.2) (iht h.1.2) (ihf h.2)
  case case6 l r ihL ihR =>
    rw [sf4Check] at h
    simp only [Bool.or_eq_true] at h
    rcases h with hper | hshl
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hper
      obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := hper
      -- `notShl` says `l` is not a literal-amount shift, so
      -- `shlOperand l = l` and the IH applies to `l` directly
      have hid : shlOperand l = l :=
        shlOperand_id (by simpa using hns)
      rw [hid] at hcl ihL
      exact SF4.binop _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
    · simp only [Bool.and_eq_true] at hshl
      exact shlSideOK_sound (ihL hshl.1.2) hshl.1.1 (ihR hshl.2) _
        (by simp)
  case case7 l r ihL ihR =>
    rw [sf4Check] at h
    simp only [Bool.or_eq_true] at h
    rcases h with hper | hshl
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hper
      obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := hper
      -- `notShl` says `l` is not a literal-amount shift, so
      -- `shlOperand l = l` and the IH applies to `l` directly
      have hid : shlOperand l = l :=
        shlOperand_id (by simpa using hns)
      rw [hid] at hcl ihL
      exact SF4.binop _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
    · simp only [Bool.and_eq_true] at hshl
      exact shlSideOK_sound (ihL hshl.1.2) hshl.1.1 (ihR hshl.2) _
        (by simp)
  case case8 l r ihL ihR =>
    rw [sf4Check] at h
    simp only [Bool.or_eq_true] at h
    rcases h with hper | hshl
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hper
      obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := hper
      -- `notShl` says `l` is not a literal-amount shift, so
      -- `shlOperand l = l` and the IH applies to `l` directly
      have hid : shlOperand l = l :=
        shlOperand_id (by simpa using hns)
      rw [hid] at hcl ihL
      exact SF4.binop _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
    · simp only [Bool.and_eq_true] at hshl
      exact shlSideOK_sound (ihL hshl.1.2) hshl.1.1 (ihR hshl.2) _
        (by simp)
  case case9 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.binop _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
  case case10 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.binop _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
  case case11 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.binop _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
  case case12 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.cmpU _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
  case case13 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.cmpU _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
  case case14 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.cmpU _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
  case case15 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.cmpU _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
  case case16 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hwA, hwB⟩, hns⟩, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.cmpU _ (by simp) hwA hwB (ihL hcl) (ihR hcb)
  case case17 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hwb, hns⟩, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.shiftOp _ (Or.inl rfl) (Or.inr hwb) (ihL hcl) (ihR hcb)
  case case18 l r ihL ihR =>
    simp only [sf4Check, Bool.and_eq_true] at h
    obtain ⟨⟨hns, hcl⟩, hcb⟩ := h
    have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
    rw [hid] at hcl ihL
    exact SF4.shiftOp _ (Or.inr rfl) (Or.inl rfl) (ihL hcl) (ihR hcb)
  case case19 l r ihL ihR =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    rcases h with
      ⟨⟨⟨hwTa, hwTb⟩, hmax0⟩, ⟨⟨⟨hpA, hpB⟩, hns⟩, hchka⟩, hchkb⟩ |
      ⟨⟨⟨⟨⟨⟨⟨hwTa, hwTbn⟩, hba⟩, hBor⟩, h0⟩, hns⟩, hchka⟩, hchkb⟩
    · have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
      rw [hid] at hchka ihL
      exact SF4.cmpS _ (by simp) hwTa hwTb hpA hpB hmax0
        (ihL hchka) (ihR hchkb)
    · have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
      rw [hid] at hchka ihL
      exact SF4.cmpS1 _ (by simp) hwTa hwTbn hba hBor h0
        (ihL hchka) (ihR hchkb)
  case case20 l r ihL ihR =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    rcases h with
      ⟨⟨⟨hwTa, hwTb⟩, hmax0⟩, ⟨⟨⟨hpA, hpB⟩, hns⟩, hchka⟩, hchkb⟩ |
      ⟨⟨⟨⟨⟨⟨⟨hwTa, hwTbn⟩, hba⟩, hBor⟩, h0⟩, hns⟩, hchka⟩, hchkb⟩
    · have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
      rw [hid] at hchka ihL
      exact SF4.cmpS _ (by simp) hwTa hwTb hpA hpB hmax0
        (ihL hchka) (ihR hchkb)
    · have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
      rw [hid] at hchka ihL
      exact SF4.cmpS1 _ (by simp) hwTa hwTbn hba hBor h0
        (ihL hchka) (ihR hchkb)
  case case21 l r ihL ihR =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    rcases h with
      ⟨⟨⟨hwTa, hwTb⟩, hmax0⟩, ⟨⟨⟨hpA, hpB⟩, hns⟩, hchka⟩, hchkb⟩ |
      ⟨⟨⟨⟨⟨⟨⟨hwTa, hwTbn⟩, hba⟩, hBor⟩, h0⟩, hns⟩, hchka⟩, hchkb⟩
    · have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
      rw [hid] at hchka ihL
      exact SF4.cmpS _ (by simp) hwTa hwTb hpA hpB hmax0
        (ihL hchka) (ihR hchkb)
    · have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
      rw [hid] at hchka ihL
      exact SF4.cmpS1 _ (by simp) hwTa hwTbn hba hBor h0
        (ihL hchka) (ihR hchkb)
  case case22 l r ihL ihR =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    rcases h with
      ⟨⟨⟨hwTa, hwTb⟩, hmax0⟩, ⟨⟨⟨hpA, hpB⟩, hns⟩, hchka⟩, hchkb⟩ |
      ⟨⟨⟨⟨⟨⟨⟨hwTa, hwTbn⟩, hba⟩, hBor⟩, h0⟩, hns⟩, hchka⟩, hchkb⟩
    · have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
      rw [hid] at hchka ihL
      exact SF4.cmpS _ (by simp) hwTa hwTb hpA hpB hmax0
        (ihL hchka) (ihR hchkb)
    · have hid : shlOperand l = l := shlOperand_id (by simpa using hns)
      rw [hid] at hchka ihL
      exact SF4.cmpS1 _ (by simp) hwTa hwTbn hba hBor h0
        (ihL hchka) (ihR hchkb)
  case case23 =>
    exfalso
    rw [sf4Check.eq_def] at h
    split at h <;>
      first
      | (simp_all; done)
      | grind
      | (simp_all; grind)
  case case24 args ih =>
    simp only [sf4Check, List.all_eq_true, List.mem_attach,
      true_implies, Subtype.forall, Bool.and_eq_true] at h
    refine SF4.concat (fun e he => ih e he (h e he).1) ?_
    intro e he op as heq
    obtain ⟨-, hpin⟩ := h e he
    subst heq
    simpa [beq_iff_eq, decide_eq_true_eq] using hpin
  case case25 w x hi lo ih2 ih1 =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    rcases h with h | h
    · obtain ⟨⟨⟨⟨hlo, hhi⟩, hw0⟩, hchk⟩, hsafe⟩ := h
      subst hlo
      have : hi = w - 1 := by omega
      subst this
      exact SF4.castEnc w hw0 (ih2 hchk) (by
        rcases hsafe with hle | himm
        · exact Or.inl hle
        · exact Or.inr himm)
    · obtain ⟨⟨⟨⟨hne, hlohi⟩, hlo32⟩, hchk⟩, hsafe⟩ := h
      refine SF4.sliceGen hi lo (fun n hn => by simp at hn)
        (fun w' y heq => ?_) hlohi hlo32 (ih1 (by simp only [sf4Check]; exact hchk)) (by
          rcases hsafe with hle | himm
          · exact Or.inl hle
          · exact Or.inr himm)
      -- the non-canonical guard survives the concat injectivity
      obtain ⟨he1, he2⟩ := by
        simpa using heq
      subst he1
      intro ⟨hl0, hh1⟩
      subst hl0
      simp_all
  case case26 n hi lo =>
    simp only [sf4Check, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    rcases h with h | h
    · obtain ⟨⟨⟨⟨hs, hw⟩, hlo⟩, hhi⟩, hne⟩ := h
      refine SF4.sliceRef n hi lo hs hw hlo hhi ?_
      intro ⟨hl0, hh1⟩
      subst hl0
      simp [hh1] at hne
    · obtain ⟨⟨⟨hs, hw⟩, hlo⟩, hhi⟩ := h
      subst hlo
      exact SF4.sliceRefFull n hi hs hw hhi
  case case27 x hi lo hncast hcomp ih =>
    simp only [sf4Check, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨hlohi, hlo32⟩, hchk⟩, hsafe⟩ := h
    exact SF4.sliceGen hi lo (fun n hn => absurd hn (by
        intro hc; exact hcomp n hc))
      (fun w' y heq => absurd heq (by
        intro hc; exact hncast w' y hc))
      hlohi hlo32 (ih hchk) (by
        rcases hsafe with hle | himm
        · exact Or.inl hle
        · exact Or.inr himm)
  case case28 =>
    exfalso
    rw [sf4Check.eq_def] at h
    split at h <;>
      first
      | (simp_all; done)
      | grind
      | (simp_all; grind)

/-- The headline form: at the assignment context width (which the
    module fragment's width-agreement conditions supply), the emitted
    Verilog computes the IR value. -/
theorem emit_sem_evalSV {wof : String → Option Nat} {we : WEnv}
    {env : Env} {e : Expr} (h : SF4 wof we e) (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn)
    {sv : SVExpr}
    (hsv : Tools.SVParser.EmitAst.emitAstExpr wof e = some sv) :
    evalSV wof env (Sparkle.IR.Semantics.widthOf we e) sv
      = evalExpr we env e := by
  obtain ⟨hw, hv⟩ := emit_sem h hbe hbw sv hsv
  unfold evalSV
  simp [hw, Nat.max_self, hv]

/- ------------------------------------------------------------------ -/
/- The memory layer: combinational read ports and write ports.          -/

mutual
/-- No array-read (`.index`) nodes anywhere.  For a memory port
    expression this rules out reads of the memory being written, which
    is what makes `evalPayload` collapse to plain `evalExpr` (the
    read-modify-write splice has nothing to splice). -/
def idxFree : Expr → Bool
  | .index _ _ => false
  | .op _ args => idxFreeL args
  | .concat args => idxFreeL args
  | .slice x _ _ => idxFree x
  | .sliceDim x _ _ => idxFree x
  | _ => true

/-- List lift of `idxFree`. -/
def idxFreeL : List Expr → Bool
  | [] => true
  | a :: rest => idxFree a && idxFreeL rest
end

/-- On index-free expressions the RMW read extraction is the identity,
    so `evalPayload` is just `evalExpr`. -/
theorem evalPayload_of_idxFree {we : WEnv} {mems : Sparkle.IR.Semantics.MEnv}
    {env : Env} {arr : String} {aw dw : Nat} {e : Expr}
    (h : idxFree e = true) :
    Sparkle.IR.Semantics.evalPayload we mems env arr aw dw e
      = evalExpr we env e := by
  have hid : ∀ (x : Expr), idxFree x = true →
      ∀ a k, Sparkle.IR.Semantics.extractReads a x k = (x, [], k) := by
    intro x
    induction x using idxFree.induct (motive_2 := fun l =>
        idxFreeL l = true →
        ∀ a k, Sparkle.IR.Semantics.extractReadsList a l k = (l, [], k)) with
    | case1 a i => intro h; cases h
    | case2 o args ih =>
      intro h a k
      simp only [idxFree] at h
      simp [Sparkle.IR.Semantics.extractReads, ih h a k]
    | case3 args ih =>
      intro h a k
      simp only [idxFree] at h
      simp [Sparkle.IR.Semantics.extractReads, ih h a k]
    | case4 x hi lo ih =>
      intro h a k
      simp only [idxFree] at h
      simp [Sparkle.IR.Semantics.extractReads, ih h a k]
    | case5 x hi lo ih =>
      intro h a k
      simp [Sparkle.IR.Semantics.extractReads]
    | case6 x h1 h2 h3 h4 h5 =>
      intro _ a k
      cases x with
      | ref n => rfl
      | const v w => rfl
      | op o args => exact absurd rfl (h2 o args)
      | concat args => exact absurd rfl (h3 args)
      | slice y hi lo => exact absurd rfl (h4 y hi lo)
      | sliceDim y d i => exact absurd rfl (h5 y d i)
      | index y i => exact absurd rfl (h1 y i)
    | case7 =>
      rename_i _ ar k
      rfl
    | case8 a rest ih1 ih2 =>
      rename_i h ar k
      simp only [idxFreeL, Bool.and_eq_true] at h
      simp [Sparkle.IR.Semantics.extractReadsList, ih1 h.1 ar k,
        ih2 h.2 ar k]
  simp [Sparkle.IR.Semantics.evalPayload, hid e h,
    Sparkle.IR.Semantics.spliceReads]

/-- Verilog's combinational read port: `assign rd = Mem[addr];` — the
    address is evaluated self-determined (it indexes an array), the
    fetched word truncated into the read target's width. -/
def comboReadsSV (wof : String → Option Nat) (mems : Sparkle.IR.Semantics.MEnv)
    (name : String) (aw dw : Nat) :
    List (SVExpr × String) → SEnv → Option SEnv
  | [], env => some env
  | (a, rd) :: rest, env => do
    let av ← evalSV wof env aw a
    comboReadsSV wof mems name aw dw rest
      (fun n => if n = rd then mask dw (mems name (mask aw av)) else env n)

/-- Verilog's write port inside `always_ff`: `if (en) Mem[a] <= d;` —
    a later port overwrites an earlier one at the same address. -/
def memWritePortsSV (wof : String → Option Nat) (env : SEnv)
    (name : String) (aw dw : Nat) :
    List (SVExpr × SVExpr × SVExpr) → Sparkle.IR.Semantics.MEnv →
    Option Sparkle.IR.Semantics.MEnv
  | [], m => some m
  | (a, d, en) :: rest, m => do
    let ev ← evalSV wof env 1 en
    let av ← evalSV wof env aw a
    let dv ← evalSV wof env dw d
    memWritePortsSV wof env name aw dw rest
      (if ev ≠ 0 then
        (fun nm i => if nm = name ∧ i = mask aw av then mask dw dv
                     else m nm i)
       else m)

/-- Port-list check: each port expression is in the fragment, is
    index-free (no read of the memory being written — that is the RMW
    layer), and its IR width matches the port's declared width. -/
def portCheck (wof : String → Option Nat) (we : WEnv) (w : Nat)
    (e : Expr) : Bool :=
  idxFree e && (Sparkle.IR.Semantics.widthOf we e == w) && sf4Check wof we e

/-- Every read port of one memory is checkable and its target is a
    declared name wide enough for the fetched word. -/
def readPortsCheck (wof : String → Option Nat) (we : WEnv)
    (aw dw : Nat) (ports : List (Expr × String)) : Bool :=
  ports.all fun p => portCheck wof we aw p.1 && (wof p.2 == some (we p.2))
    && (decide (dw ≤ we p.2))

/- --- Read-modify-write payloads (`Mem[a] <= Mem[a] & ~m | d;`) ---- -/

mutual
/-- The SV mirror of `extractReads`: pull each read of the memory's OWN
    array out of the emitted payload, replacing it with the SAME
    placeholder name the IR uses.  Verilog's nonblocking RHS reads the
    pre-write state, which is exactly what the placeholder is bound to.
    (`sanitizeName` is the identity on `__memread_*`, so the emitted
    placeholder and the IR's agree.) -/
def extractReadsSV (arr : String) : SVExpr → Nat → (SVExpr × List (String × SVExpr) × Nat)
  | .index (.ident a) idx, k =>
    if a = arr then
      (.ident s!"__memread_{arr}_{k}", [(s!"__memread_{arr}_{k}", idx)], k + 1)
    else (.index (.ident a) idx, [], k)
  | .binary o a b, k =>
    let (a', l1, k1) := extractReadsSV arr a k
    let (b', l2, k2) := extractReadsSV arr b k1
    (.binary o a' b', l1 ++ l2, k2)
  | .unary o a, k =>
    let (a', l, k') := extractReadsSV arr a k
    (.unary o a', l, k')
  | .ternary c t f, k =>
    let (c', l1, k1) := extractReadsSV arr c k
    let (t', l2, k2) := extractReadsSV arr t k1
    let (f', l3, k3) := extractReadsSV arr f k2
    (.ternary c' t' f', l1 ++ l2 ++ l3, k3)
  | .sizeCast w a, k =>
    let (a', l, k') := extractReadsSV arr a k
    (.sizeCast w a', l, k')
  | .concat args, k =>
    let (args', l, k') := extractReadsListSV arr args k
    (.concat args', l, k')
  | .slice x hi lo, k =>
    let (x', l, k') := extractReadsSV arr x k
    (.slice x' hi lo, l, k')
  | e, k => (e, [], k)

def extractReadsListSV (arr : String) :
    List SVExpr → Nat → (List SVExpr × List (String × SVExpr) × Nat)
  | [], k => ([], [], k)
  | a :: rest, k =>
    let (a', l1, k1) := extractReadsSV arr a k
    let (rest', l2, k2) := extractReadsListSV arr rest k1
    (a' :: rest', l1 ++ l2, k2)
end

/-- The SV mirror of `spliceReads`: bind each placeholder to the
    pre-write word at its (self-determined) address. -/
def spliceReadsSV (wof : String → Option Nat)
    (mems : Sparkle.IR.Semantics.MEnv) (env : SEnv)
    (arr : String) (aw dw : Nat) :
    List (String × SVExpr) → SEnv → Option SEnv
  | [], acc => some acc
  | (ph, idx) :: rest, acc => do
    let vi ← evalSV wof env aw idx
    spliceReadsSV wof mems env arr aw dw rest
      (fun n => if n = ph then mask dw (mems arr (mask aw vi)) else acc n)

/-- Evaluate an emitted memory payload at width `W`. -/
def evalPayloadSV (wof : String → Option Nat)
    (mems : Sparkle.IR.Semantics.MEnv) (env : SEnv)
    (arr : String) (aw dw W : Nat) (sv : SVExpr) : Option Nat :=
  let (sv', reads, _) := extractReadsSV arr sv 0
  do evalSV wof (← spliceReadsSV wof mems env arr aw dw reads env) W sv'

/-- The width map extended with a memory's read placeholders, each at
    the memory's data width.  `extractReads` introduces at most `n`
    placeholders numbered `0 .. n-1`, so extending for a bound `n`
    covers every payload with at most `n` own-array reads. -/
def wofWithReads (wof : String → Option Nat) (arr : String) (dw n : Nat) :
    String → Option Nat :=
  fun x =>
    if (List.range n).any (fun k => x == s!"__memread_{arr}_{k}")
    then some dw else wof x

/-- The value environment extended the same way (the pre-write words). -/
def weWithReads (we : WEnv) (arr : String) (dw n : Nat) : WEnv :=
  fun x =>
    if (List.range n).any (fun k => x == s!"__memread_{arr}_{k}")
    then dw else we x

/-- A memory port payload that may READ its own array: check the
    stripped form and each extracted address, under the width map
    extended with the read placeholders.

    `portCheck`'s `idxFree` requirement is the special case with no
    reads; this generalizes it to the read-modify-write payloads
    firtool emits for byte strobes. -/
def payloadCheck (wof : String → Option Nat) (we : WEnv)
    (arr : String) (aw dw w : Nat) (e : Expr) : Bool :=
  let (e', reads, k) := Sparkle.IR.Semantics.extractReads arr e 0
  let wof' := wofWithReads wof arr dw k
  let we' := weWithReads we arr dw k
  idxFree e'
    && (Sparkle.IR.Semantics.widthOf we' e' == w)
    && sf4Check wof' we' e'
    -- The extracted ADDRESSES are checked under the PLAIN maps: they
    -- contain no placeholders (extraction pulled the reads out), and
    -- `payload_agree`'s `hpair` evaluates them there, because the IR's
    -- own splice does.  Checking them under the extended maps left a
    -- gap exactly at that hypothesis.
    && reads.all (fun p =>
         idxFree p.2
           && (Sparkle.IR.Semantics.widthOf we p.2 == aw)
           && sf4Check wof we p.2)

/- Structural equality on the emitted syntax.  `SVExpr`'s DERIVED
   `BEq` has no `LawfulBEq` instance and `DecidableEq` will not derive
   for it (nested inductive), so a `==` verdict yields no propositional
   equality — which makes it useless inside a proof.  The leaf types
   are non-recursive, so those derive fine. -/
deriving instance DecidableEq for SVLiteral
deriving instance DecidableEq for SVUnaryOp
deriving instance DecidableEq for SVBinOp

mutual
/-- Structural equality on `SVExpr` (the derived `BEq` has no
    `LawfulBEq`, and `DecidableEq` will not derive for this nested
    inductive, so roll a structural one and prove it sound). -/
def eqSV : SVExpr → SVExpr → Bool
  | .lit l, .lit l' => decide (l = l')
  | .ident n, .ident n' => n == n'
  | .unary o a, .unary o' a' => decide (o = o') && eqSV a a'
  | .binary o a b, .binary o' a' b' =>
    decide (o = o') && eqSV a a' && eqSV b b'
  | .ternary c t f, .ternary c' t' f' =>
    eqSV c c' && eqSV t t' && eqSV f f'
  | .index a i, .index a' i' => eqSV a a' && eqSV i i'
  | .slice e hi lo, .slice e' hi' lo' =>
    eqSV e e' && decide (hi = hi') && decide (lo = lo')
  | .partSelectPlus e b w, .partSelectPlus e' b' w' =>
    eqSV e e' && eqSV b b' && eqSV w w'
  | .concat args, .concat args' => eqSVList args args'
  | .repeat_ c v, .repeat_ c' v' => eqSV c c' && eqSV v v'
  | .sizeCast w a, .sizeCast w' a' => decide (w = w') && eqSV a a'
  | _, _ => false

def eqSVList : List SVExpr → List SVExpr → Bool
  | [], [] => true
  | a :: rest, a' :: rest' => eqSV a a' && eqSVList rest rest'
  | _, _ => false
end

mutual
theorem eqSV_iff : ∀ a b : SVExpr, eqSV a b = true ↔ a = b
  | .lit l, b => by cases b <;> simp [eqSV]
  | .ident n, b => by cases b <;> simp [eqSV]
  | .unary o a, b => by
    cases b <;> simp [eqSV, Bool.and_eq_true, eqSV_iff a, and_assoc]
  | .binary o a c, b => by
    cases b <;> simp [eqSV, Bool.and_eq_true, eqSV_iff a, eqSV_iff c,
      and_assoc]
  | .ternary c t f, b => by
    cases b <;> simp [eqSV, Bool.and_eq_true, eqSV_iff c, eqSV_iff t,
      eqSV_iff f, and_assoc]
  | .index a i, b => by
    cases b <;> simp [eqSV, Bool.and_eq_true, eqSV_iff a, eqSV_iff i]
  | .slice e hi lo, b => by
    cases b <;> simp [eqSV, Bool.and_eq_true, eqSV_iff e, and_assoc]
  | .partSelectPlus e bs w, b => by
    cases b <;> simp [eqSV, Bool.and_eq_true, eqSV_iff e, eqSV_iff bs,
      eqSV_iff w, and_assoc]
  | .concat args, b => by
    cases b <;> simp [eqSV, eqSVList_iff args]
  | .repeat_ c v, b => by
    cases b <;> simp [eqSV, Bool.and_eq_true, eqSV_iff c, eqSV_iff v]
  | .sizeCast w a, b => by
    cases b <;> simp [eqSV, Bool.and_eq_true, eqSV_iff a, and_assoc]

theorem eqSVList_iff : ∀ (l l' : List SVExpr), eqSVList l l' = true ↔ l = l'
  | [], l' => by cases l' <;> simp [eqSVList]
  | a :: rest, l' => by
    cases l' <;> simp [eqSVList, Bool.and_eq_true, eqSV_iff a,
      eqSVList_iff rest]
end

/-- `payloadCheck` plus the COMMUTATION of emission with extraction:
    emitting the whole payload and then splitting it on the SV side
    yields the emission of the IR-side stripped form, with the read
    lists pairing name for name.

    Commutation is decidable — it is an equality of emitted syntax — so
    it is checked here rather than proven over all shapes.  Measured on
    the corpus it holds for both byte-strobe arrays: same placeholder
    count, same numbering, identical stripped emissions. -/
def payloadCheckC (wof : String → Option Nat) (we : WEnv)
    (arr : String) (aw dw w : Nat) (e : Expr) : Bool :=
  payloadCheck wof we arr aw dw w e &&
  (let (e', readsIR, k) := Sparkle.IR.Semantics.extractReads arr e 0
   let wof' := wofWithReads wof arr dw k
   -- The WHOLE payload is emitted under the caller's own map (it has
   -- no placeholders in it), while the STRIPPED form needs the
   -- extended one — the placeholders are exactly what extraction put
   -- there.  Using the extended map for both would leave a gap between
   -- this check and what a caller can supply.
   match Tools.SVParser.EmitAst.emitAstExpr wof e,
         Tools.SVParser.EmitAst.emitAstExpr wof' e' with
   | some svWhole, some svStripped =>
     let (svStripped', readsSV, k2) := extractReadsSV arr svWhole 0
     eqSV svStripped' svStripped && (k2 == k)
       && (readsSV.length == readsIR.length)
       -- each read must pair NAME for name AND each SV address must be
       -- the emission of its IR counterpart.  Checking only the names
       -- left the address VALUES unrelated, so `payload_agree`'s
       -- `hpair` could not be discharged from a passing verdict.
       && ((readsIR.zip readsSV).all fun pq =>
             (pq.1.1 == pq.2.1)
             && (match Tools.SVParser.EmitAst.emitAstExpr wof pq.1.2 with
                 | some sa => eqSV sa pq.2.2
                 | none => false))
   | _, _ => false)

/-- The emitter's read-port list for one memory. -/
def emitReadPorts (wof : String → Option Nat) :
    List (Expr × String) → Option (List (SVExpr × String))
  | [] => some []
  | (a, rd) :: rest => do
    let sa ← Tools.SVParser.EmitAst.emitAstExpr wof a
    let others ← emitReadPorts wof rest
    some ((sa, rd) :: others)

/-- The emitter's write-port list for one memory. -/
def emitWritePorts (wof : String → Option Nat) :
    List (Expr × Expr × Expr) → Option (List (SVExpr × SVExpr × SVExpr))
  | [] => some []
  | (a, d, en) :: rest => do
    let sa ← Tools.SVParser.EmitAst.emitAstExpr wof a
    let sd ← Tools.SVParser.EmitAst.emitAstExpr wof d
    let sen ← Tools.SVParser.EmitAst.emitAstExpr wof en
    let others ← emitWritePorts wof rest
    some ((sa, sd, sen) :: others)

set_option maxHeartbeats 800000 in
/-- **Forward correctness, combinational read ports**: the emitted
    `assign rd = Mem[addr];` chain lands in the same environment as the
    IR's `comboReads`, and preserves the width invariants. -/
theorem emit_sem_comboReads {wof : String → Option Nat} {we : WEnv}
    (mems : Sparkle.IR.Semantics.MEnv) (name : String) (aw dw : Nat) :
    ∀ (ports : List (Expr × String)) (env : Env),
      readPortsCheck wof we aw dw ports = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ svports env',
        emitReadPorts wof ports = some svports
        ∧ Sparkle.IR.Semantics.comboReads we mems name aw dw ports env
            = some env'
        ∧ comboReadsSV wof mems name aw dw svports env = some env'
        ∧ Bounded we env'
        ∧ (∀ n wn, wof n = some wn → env' n < 2 ^ wn) := by
  intro ports
  induction ports with
  | nil => intro env _ hbe hbw; exact ⟨[], env, rfl, rfl, rfl, hbe, hbw⟩
  | cons p rest ih =>
    obtain ⟨a, rd⟩ := p
    intro env hchk hbe hbw
    simp only [readPortsCheck, List.all_cons, Bool.and_eq_true,
      portCheck, beq_iff_eq, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨hidx, hwa⟩, hfr⟩, hwrd⟩, hdwrd⟩ := hchk.1
    have hSF := sf4Check_sound hfr
    obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hSF env)
    obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSF)
    -- the fetched word fits `dw`, hence the read target's width
    have hfit : mask dw (mems name (mask aw av)) < 2 ^ dw :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hbe' : Bounded we
        (fun n => if n = rd then mask dw (mems name (mask aw av))
                  else env n) := by
      intro n
      by_cases hn : n = rd <;> simp [hn]
      · exact Nat.lt_of_lt_of_le hfit
          (Nat.pow_le_pow_right (by omega) (hn ▸ hdwrd))
      · exact hbe n
    have hbw' : ∀ n wn, wof n = some wn →
        (fun n => if n = rd then mask dw (mems name (mask aw av))
                  else env n) n < 2 ^ wn := by
      intro n wn hn
      by_cases hnr : n = rd <;> simp [hnr]
      · subst hnr
        rw [hn] at hwrd
        simp only [Option.some_inj] at hwrd
        exact Nat.lt_of_lt_of_le hfit
          (Nat.pow_le_pow_right (by omega) (hwrd ▸ hdwrd))
      · exact hbw n wn hn
    have htail : readPortsCheck wof we aw dw rest = true := by
      simp only [readPortsCheck, List.all_eq_true]
      intro x hx
      have h2 := hchk.2
      simp only [List.all_eq_true] at h2
      exact h2 x hx
    obtain ⟨svrest, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
      ih _ htail hbe' hbw'
    refine ⟨(sa, rd) :: svrest, env', ?_, ?_, ?_, hbe'', hbw''⟩
    · simp [emitReadPorts, hsa, hemit]
    · simp [Sparkle.IR.Semantics.comboReads, hav, hIR]
    · have hval : evalSV wof env aw sa = some av := by
        rw [← hwa, emit_sem_evalSV hSF hbe hbw hsa]
        exact hav
      simp only [comboReadsSV, hval, Option.bind_eq_bind,
        Option.bind_some]
      exact hSV

/-- The IR's and Verilog's read splices agree, given that each
    address's emission computes its IR value at the address width.
    Stated over PAIRED read lists so the induction runs on one
    structure. -/
theorem splice_agree {wof : String → Option Nat} {we : WEnv}
    {mems : MEnv} {env : Env} {arr : String} {aw dw : Nat}
    (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn) :
    ∀ (readsIR : List (String × Expr)) (readsSV : List (String × SVExpr)),
      -- paired, name for name, with each SV address the emission of the
      -- IR one and its value right at width `aw`
      readsIR.length = readsSV.length →
      (∀ i (hi : i < readsIR.length) (hj : i < readsSV.length),
        (readsIR[i]'hi).1 = (readsSV[i]'hj).1
        ∧ evalSV wof env aw (readsSV[i]'hj).2
            = evalExpr we env (readsIR[i]'hi).2) →
      ∀ acc, spliceReads we mems env arr aw dw readsIR acc
        = spliceReadsSV wof mems env arr aw dw readsSV acc := by
  intro readsIR
  induction readsIR with
  | nil =>
    intro readsSV hlen _ acc
    cases readsSV with
    | nil => rfl
    | cons p ps => simp at hlen
  | cons p ps ih =>
    intro readsSV hlen hpair acc
    cases readsSV with
    | nil => simp at hlen
    | cons q qs =>
      obtain ⟨hname, hval⟩ := hpair 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at hname hval
      simp only [spliceReads, spliceReadsSV, hval, hname,
        Option.bind_eq_bind]
      cases hv : evalExpr we env p.2 with
      | none => simp [hv]
      | some vi =>
        simp only [hv, Option.bind_some]
        exact ih qs (by simpa using hlen)
          (fun i hi hj => by
            have := hpair (i+1) (by simpa using hi) (by simpa using hj)
            simpa using this) _

/-- Boundedness lifts to the placeholder-extended environment exactly
    when the ambient environment's value at each placeholder name fits
    `dw`.  Placeholder names are synthetic (`__memread_arr_k`), so a
    real environment holds 0 there and the condition is trivial — but
    it IS a condition, and saying so is what lets the address lemmas
    fire under the extended maps. -/
theorem bounded_withReads {we : WEnv} {env : Env} {arr : String}
    {dw k : Nat} (hbe : Bounded we env)
    (hph : ∀ n, (List.range k).any
        (fun j => n == s!"__memread_{arr}_{j}") → env n < 2 ^ dw) :
    Bounded (weWithReads we arr dw k) env := by
  intro n
  unfold weWithReads
  by_cases hb : (List.range k).any (fun j => n == s!"__memread_{arr}_{j}")
  · simp only [hb, if_pos]
    exact hph n hb
  · simp only [hb, if_neg]
    exact hbe n

/-- The same lift for the `wof`-indexed bound. -/
theorem bw_withReads {wof : String → Option Nat} {env : Env}
    {arr : String} {dw k : Nat}
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn)
    (hph : ∀ n, (List.range k).any
        (fun j => n == s!"__memread_{arr}_{j}") → env n < 2 ^ dw) :
    ∀ n wn, wofWithReads wof arr dw k n = some wn → env n < 2 ^ wn := by
  intro n wn hn
  unfold wofWithReads at hn
  by_cases hb : (List.range k).any (fun j => n == s!"__memread_{arr}_{j}")
  · simp only [hb, if_pos, Option.some_inj] at hn
    subst hn
    exact hph n hb
  · simp only [hb, if_neg] at hn
    exact hbw n wn hn

/-- `payloadCheck`, unpacked over explicit split components (no `let`
    in the statement, so callers can rewrite freely). -/
theorem payloadCheck_parts {wof : String → Option Nat} {we : WEnv}
    {arr : String} {aw dw w : Nat} {e e' : Expr}
    {reads : List (String × Expr)} {k : Nat}
    (hsplit : extractReads arr e 0 = (e', reads, k))
    (h : payloadCheck wof we arr aw dw w e = true) :
    idxFree e' = true
    ∧ Sparkle.IR.Semantics.widthOf (weWithReads we arr dw k) e' = w
    ∧ sf4Check (wofWithReads wof arr dw k) (weWithReads we arr dw k) e'
        = true
    -- addresses are checked under the PLAIN maps (they hold no
    -- placeholders, and that is where `hpair` evaluates them)
    ∧ ∀ p ∈ reads, idxFree p.2 = true
        ∧ Sparkle.IR.Semantics.widthOf we p.2 = aw
        ∧ sf4Check wof we p.2 = true := by
  rw [payloadCheck, hsplit] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hidx, hw⟩, hfr⟩, hreads⟩ := h
  refine ⟨hidx, hw, hfr, ?_⟩
  intro p hp
  have hp2 := hreads p hp
  exact ⟨hp2.1.1, hp2.1.2, hp2.2⟩

/-- An extracted address's emission computes its IR value at the
    address width — `emit_sem_evalSV` under the placeholder-extended
    maps, which is what `payloadCheck` verifies the address satisfies. -/
theorem addr_agree {wof : String → Option Nat} {we : WEnv} {env : Env}
    {aw : Nat} {idx : Expr} {svi : SVExpr}
    (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn)
    (hw : Sparkle.IR.Semantics.widthOf we idx = aw)
    (hfr : sf4Check wof we idx = true)
    (hemit : Tools.SVParser.EmitAst.emitAstExpr wof idx = some svi) :
    evalSV wof env aw svi = evalExpr we env idx := by
  rw [← hw]
  exact emit_sem_evalSV (sf4Check_sound hfr) hbe hbw hemit

/-- The spliced environment is still width-bounded under the extended
    maps.  This is what lets `emit_sem_evalSV` fire on the stripped
    form, and hence what `payload_agree`'s `hval` rests on: the splice
    writes `mask dw (mems …)` into each placeholder, and the extended
    maps declare placeholders at exactly `dw`, so the bound holds by
    construction.  The hypothesis that every spliced name IS such a
    placeholder is how `extractReads` builds the list. -/
theorem splice_bounded {wof : String → Option Nat} {we : WEnv}
    {mems : MEnv} {env : Env} {arr : String} {aw dw k : Nat} :
    ∀ (reads : List (String × Expr)) (acc : Env),
      -- every spliced name IS a placeholder of this array (which is
      -- how `extractReads` builds the list)
      (∀ p ∈ reads, weWithReads we arr dw k p.1 = dw
        ∧ wofWithReads wof arr dw k p.1 = some dw) →
      Bounded (weWithReads we arr dw k) acc →
      (∀ n wn, wofWithReads wof arr dw k n = some wn → acc n < 2 ^ wn) →
      ∀ spl, spliceReads we mems env arr aw dw reads acc = some spl →
        Bounded (weWithReads we arr dw k) spl
        ∧ (∀ n wn, wofWithReads wof arr dw k n = some wn → spl n < 2 ^ wn) := by
  intro reads
  induction reads with
  | nil =>
    intro acc hph hbe hbw spl hs
    simp only [spliceReads, Option.some_inj] at hs
    subst hs
    exact ⟨hbe, hbw⟩
  | cons p rest ih =>
    intro acc hph hbe hbw spl hs
    obtain ⟨hwph, hwofph⟩ := hph p (List.mem_cons_self ..)
    simp only [spliceReads, Option.bind_eq_bind] at hs
    obtain ⟨vi, hvi, hs⟩ := Option.bind_eq_some_iff.mp hs
    -- the updated accumulator: the placeholder gets a dw-masked word
    refine ih _ (fun q hq => hph q (List.mem_cons_of_mem _ hq)) ?_ ?_ spl hs
    · intro n
      by_cases hn : n = p.1
      · simp only [hn, if_pos rfl, hwph]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · simp only [if_neg hn]; exact hbe n
    · intro n wn hn
      by_cases hnp : n = p.1
      · subst hnp
        rw [hwofph] at hn
        simp only [Option.some_inj] at hn
        subst hn
        simp only [if_pos rfl]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · simp only [if_neg hnp]; exact hbw n wn hn

/-- **Read-modify-write payloads agree.**  A byte-strobe write value
    reads the array it writes, so `evalPayload` resolves those reads
    against the PRE-write state before evaluating.  Verilog's
    nonblocking RHS does the same, and `evalPayloadSV` mirrors it with
    the same placeholder names.

    The hypotheses are: emission commutes with extraction (the stripped
    emission is the emission of the stripped form, and the read lists
    pair up name-for-name), plus the stripped form's own forward
    correctness.  Commutation is measured true on both corpus RMW
    arrays — same placeholder count and numbering, identical stripped
    emissions. -/
theorem payload_agree {wof : String → Option Nat} {we : WEnv}
    {mems : MEnv} {env : Env} {arr : String} {aw dw W : Nat}
    {e : Expr} {sv sv' : SVExpr}
    -- the IR split (k first: the extended maps mention it)
    (e' : Expr) (readsIR : List (String × Expr)) (k : Nat)
    (hsplitIR : extractReads arr e 0 = (e', readsIR, k))
    -- Everything below is stated in the PLACEHOLDER-EXTENDED maps.
    -- That is forced, not chosen: the stripped form contains the
    -- placeholders, so its own forward correctness — and hence the
    -- conclusion, which evaluates it — can only live there.  Stating
    -- `hval` over the plain maps made it unsatisfiable by any caller.
    (hbeX : Bounded (weWithReads we arr dw k) env)
    (hbwX : ∀ n wn, wofWithReads wof arr dw k n = some wn
      → env n < 2 ^ wn)
    -- the SV split of the WHOLE emission
    (readsSV : List (String × SVExpr)) (k2 : Nat)
    (hsplitSV : extractReadsSV arr sv 0 = (sv', readsSV, k2))
    -- commutation: the stripped emission IS the emission of the
    -- stripped form, and the reads pair up
    (hstrip : Tools.SVParser.EmitAst.emitAstExpr
      (wofWithReads wof arr dw k) e' = some sv')
    (hlen : readsIR.length = readsSV.length)
    (hpair : ∀ i (hi : i < readsIR.length) (hj : i < readsSV.length),
      (readsIR[i]'hi).1 = (readsSV[i]'hj).1
      ∧ evalSV (wofWithReads wof arr dw k) env aw (readsSV[i]'hj).2
          = evalExpr (weWithReads we arr dw k) env (readsIR[i]'hi).2)
    (hval : ∀ spl,
      spliceReads (weWithReads we arr dw k) mems env arr aw dw readsIR env
        = some spl
      → evalSV (wofWithReads wof arr dw k) spl W sv'
          = evalExpr (weWithReads we arr dw k) spl e') :
    evalPayloadSV (wofWithReads wof arr dw k) mems env arr aw dw W sv
      = evalPayload (weWithReads we arr dw k) mems env arr aw dw e := by
  unfold evalPayloadSV evalPayload
  rw [hsplitIR, hsplitSV]
  simp only []
  rw [← splice_agree hbeX hbwX readsIR readsSV hlen hpair env]
  cases hs : spliceReads (weWithReads we arr dw k) mems env arr aw dw
      readsIR env with
  | none => simp [hs]
  | some spl => simp [hs, hval spl hs]

set_option maxHeartbeats 800000 in
/-- **Forward correctness, write ports**: the emitted `always_ff`
    guarded stores produce the same memory state as the IR's
    `memWritePorts` (index-free ports, so the RMW splice is inert). -/
theorem emit_sem_writePorts {wof : String → Option Nat} {we : WEnv}
    (mems0 : Sparkle.IR.Semantics.MEnv) (name : String) (aw dw : Nat) :
    ∀ (ports : List (Expr × Expr × Expr)) (env : Env)
      (m : Sparkle.IR.Semantics.MEnv),
      (ports.all fun p => portCheck wof we aw p.1
        && portCheck wof we dw p.2.1
        && portCheck wof we 1 p.2.2) = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ svports m',
        emitWritePorts wof ports = some svports
        ∧ Sparkle.IR.Semantics.memWritePorts we mems0 env name aw dw
            ports m = some m'
        ∧ memWritePortsSV wof env name aw dw svports m = some m' := by
  intro ports
  induction ports with
  | nil => intro env m _ _ _; exact ⟨[], m, rfl, rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨a, d, en⟩ := p
    intro env m hchk hbe hbw
    simp only [List.all_cons, Bool.and_eq_true, portCheck,
      beq_iff_eq] at hchk
    obtain ⟨⟨⟨⟨hidxA, hwa⟩, hfrA⟩, ⟨⟨hidxD, hwd⟩, hfrD⟩⟩,
      ⟨⟨hidxE, hwe⟩, hfrE⟩⟩ := hchk.1
    have hSFa := sf4Check_sound hfrA
    have hSFd := sf4Check_sound hfrD
    have hSFe := sf4Check_sound hfrE
    obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hSFa env)
    obtain ⟨dv, hdv⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hSFd env)
    obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.mp
      (sf4_eval_isSome hSFe env)
    obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSFa)
    obtain ⟨sd, hsd⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSFd)
    obtain ⟨sen, hsen⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSFe)
    obtain ⟨svrest, m', hemit, hIR, hSV⟩ := ih env _ hchk.2 hbe hbw
    refine ⟨(sa, sd, sen) :: svrest, m', ?_, ?_, ?_⟩
    · simp [emitWritePorts, hsa, hsd, hsen, hemit]
    · simp only [Sparkle.IR.Semantics.memWritePorts,
        evalPayload_of_idxFree hidxE, evalPayload_of_idxFree hidxA,
        evalPayload_of_idxFree hidxD, hev, hav, hdv,
        Option.bind_eq_bind, Option.bind_some]
      exact hIR
    · have hvA : evalSV wof env aw sa = some av := by
        rw [← hwa, emit_sem_evalSV hSFa hbe hbw hsa]; exact hav
      have hvD : evalSV wof env dw sd = some dv := by
        rw [← hwd, emit_sem_evalSV hSFd hbe hbw hsd]; exact hdv
      have hvE : evalSV wof env 1 sen = some ev := by
        rw [← hwe, emit_sem_evalSV hSFe hbe hbw hsen]; exact hev
      simp only [memWritePortsSV, hvA, hvD, hvE, Option.bind_eq_bind,
        Option.bind_some]
      exact hSV

/-- A payload-aware SV write-port model: every port expression is
    evaluated as a PAYLOAD against the pre-write state, which on
    index-free expressions is plain `evalSV`.  This is what a
    byte-strobe write needs — its data reads the array being written,
    and Verilog's nonblocking RHS sees the pre-write words. -/
def memWritePortsSVP (wof : String → Option Nat)
    (mems0 : MEnv) (env : SEnv) (name : String) (aw dw : Nat) :
    List (SVExpr × SVExpr × SVExpr) → MEnv → Option MEnv
  | [], m => some m
  | (a, d, en) :: rest, m => do
    let ev ← evalPayloadSV wof mems0 env name aw dw 1 en
    let av ← evalPayloadSV wof mems0 env name aw dw aw a
    let dv ← evalPayloadSV wof mems0 env name aw dw dw d
    memWritePortsSVP wof mems0 env name aw dw rest
      (if ev ≠ 0 then
        (fun nm i => if nm = name ∧ i = mask aw av then mask dw dv
                     else m nm i)
       else m)

/-- **Forward correctness of write ports, payload form.**  Each port
    carries its own payload agreement as a hypothesis — exactly what
    `payload_agree` produces and what `payloadCheck` verifies per
    instance.  Unlike `emit_sem_writePorts` this places no `idxFree`
    demand, so it covers the read-modify-write payloads firtool emits
    for byte strobes. -/
theorem emit_sem_writePortsP {wof : String → Option Nat} {we : WEnv}
    (mems0 : MEnv) (name : String) (aw dw : Nat) :
    ∀ (ports : List (Expr × Expr × Expr))
      (svports : List (SVExpr × SVExpr × SVExpr)) (env : Env)
      (m : MEnv),
      emitWritePorts wof ports = some svports →
      ports.length = svports.length →
      -- per-port payload agreement, for all three operands
      (∀ i (hi : i < ports.length) (hj : i < svports.length),
        evalPayloadSV wof mems0 env name aw dw aw (svports[i]'hj).1
          = evalPayload we mems0 env name aw dw (ports[i]'hi).1
        ∧ evalPayloadSV wof mems0 env name aw dw dw (svports[i]'hj).2.1
            = evalPayload we mems0 env name aw dw (ports[i]'hi).2.1
        ∧ evalPayloadSV wof mems0 env name aw dw 1 (svports[i]'hj).2.2
            = evalPayload we mems0 env name aw dw (ports[i]'hi).2.2) →
      memWritePortsSVP wof mems0 env name aw dw svports m
        = memWritePorts we mems0 env name aw dw ports m := by
  intro ports
  induction ports with
  | nil =>
    intro svports env m hemit hlen _
    cases svports with
    | nil => rfl
    | cons q qs => simp at hlen
  | cons p rest ih =>
    intro svports env m hemit hlen hagree
    cases svports with
    | nil => simp at hlen
    | cons q qs =>
      obtain ⟨hA, hD, hE⟩ := hagree 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at hA hD hE
      simp only [memWritePortsSVP, memWritePorts, hA, hD, hE,
        Option.bind_eq_bind]
      cases hev : evalPayload we mems0 env name aw dw p.2.2 with
      | none => simp [hev]
      | some ev =>
      cases hav : evalPayload we mems0 env name aw dw p.1 with
      | none => simp [hev, hav]
      | some av =>
      cases hdv : evalPayload we mems0 env name aw dw p.2.1 with
      | none => simp [hev, hav, hdv]
      | some dv =>
      simp only [hev, hav, hdv, Option.bind_some]
      -- the emitter's list decomposes
      simp only [emitWritePorts, Option.bind_eq_bind] at hemit
      obtain ⟨sa, hsa, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      obtain ⟨sd, hsd, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      obtain ⟨sen, hsen, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      obtain ⟨others, hoth, hemit⟩ := Option.bind_eq_some_iff.mp hemit
      simp only [Option.some_inj] at hemit
      -- the emitter's cons matches the given cons
      have hq : q = (sa, sd, sen) ∧ qs = others := by
        have h := hemit
        simp only [List.cons.injEq] at h
        exact ⟨h.1.symm, h.2.symm⟩
      exact ih qs env _ (hq.2 ▸ hoth)
        (by simpa using hlen)
        (fun i hi hj => by
          have := hagree (i+1) (by simpa using hi) (by simpa using hj)
          simpa using this)

/- ------------------------------------------------------------------ -/
/- The statement layer: the combinational phase of a module.           -/

/-- One step of the emitted combinational program: a continuous
    assignment, or one memory's combinational read ports. -/
inductive CombStep where
  | assign (lhs : String) (rhs : SVExpr)
  | reads (name : String) (aw dw : Nat) (ports : List (SVExpr × String))

/-- The combinational program the emitter prints: `assign l = E;` for
    each assign, and `assign rd = Mem[addr];` for each
    combinationally-read memory.  Registers, instances and sync-read
    memories contribute nothing to this phase. -/
def emitAssigns (wof : String → Option Nat) :
    List Stmt → Option (List CombStep)
  | [] => some []
  | .assign l r :: rest => do
    let sv ← Tools.SVParser.EmitAst.emitAstExpr wof r
    let others ← emitAssigns wof rest
    some (.assign l sv :: others)
  | .register _ _ _ _ _ :: rest => emitAssigns wof rest
  | .memory name aw dw _ _ _ _ ra rd cr _ er :: rest =>
    if cr then do
      let ports ← emitReadPorts wof ((ra, rd) :: er)
      let others ← emitAssigns wof rest
      some (.reads name aw dw ports :: others)
    else emitAssigns wof rest
  | .inst _ _ _ :: rest => emitAssigns wof rest

/-- Verilog's combinational fold: each continuous assignment evaluates
    its RHS at its LHS's declared width (the assignment context) and
    truncates into the target; each read port fetches its word. -/
def evalAssignsSV (wof : String → Option Nat)
    (mems : Sparkle.IR.Semantics.MEnv) :
    List CombStep → SEnv → Option SEnv
  | [], env => some env
  | .assign n sv :: rest, env => do
    let w ← wof n
    let v ← evalSV wof env w sv
    evalAssignsSV wof mems rest
      (fun m => if m = n then mask w v else env m)
  | .reads name aw dw ports :: rest, env => do
    let env' ← comboReadsSV wof mems name aw dw ports env
    evalAssignsSV wof mems rest env'

/-- Per-body forward-fragment check: every assign's RHS is in the
    fragment, agrees in width with its LHS, and the LHS is a declared,
    sanitize-fixed name; a combinationally-read memory's read ports are
    checkable (index-free addresses at the address width, targets wide
    enough); registers, instances and sync-read memories are
    combinationally inert. -/
def assignsCheck (wof : String → Option Nat) (we : WEnv) :
    List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (Sparkle.Backend.Verilog.sanitizeName l == l)
      && (wof l == some (we l))
      && (Sparkle.IR.Semantics.widthOf we r == we l)
      && sf4Check wof we r
      && assignsCheck wof we rest
  | .register _ _ _ _ _ :: rest => assignsCheck wof we rest
  | .memory _ aw dw _ _ _ _ ra rd cr _ er :: rest =>
    (!cr || readPortsCheck wof we aw dw ((ra, rd) :: er))
      && assignsCheck wof we rest
  | .inst _ _ _ :: rest => assignsCheck wof we rest

set_option maxHeartbeats 800000 in
/-- **Forward correctness, statement layer**: on a checked body, the
    emitter's assign list EXISTS and Verilog's in-order assignment fold
    computes exactly the IR's `evalAssigns` — the whole combinational
    phase of the module agrees, and the result environment stays
    width-bounded on both counts. -/
theorem emit_sem_assigns {wof : String → Option Nat} {we : WEnv}
    (mems : Sparkle.IR.Semantics.MEnv) :
    ∀ (body : List Stmt) (env : Env),
      assignsCheck wof we body = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ pairs env',
        emitAssigns wof body = some pairs
        ∧ Sparkle.IR.Semantics.evalAssigns we mems body env = some env'
        ∧ evalAssignsSV wof mems pairs env = some env'
        ∧ Bounded we env'
        ∧ (∀ n wn, wof n = some wn → env' n < 2 ^ wn) := by
  intro body
  induction body with
  | nil =>
    intro env _ hbe hbw
    exact ⟨[], env, rfl, rfl, rfl, hbe, hbw⟩
  | cons st rest ih =>
    intro env hchk hbe hbw
    cases st with
    | assign l r =>
      simp only [assignsCheck, Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨⟨hs, hwl⟩, hwr⟩, hfr⟩, hrest⟩ := hchk
      have hSF := sf4Check_sound hfr
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome hSF env)
      obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
        (sf4_emit_isSome hSF)
      have hvlt : v < 2 ^ we l :=
        hwr ▸ sf4_bounded hSF hbe v hv
      -- the two updated environments are the SAME function
      have henv : (fun m => if m = l then mask (we l) v else env m)
          = (fun m => if m = l then v else env m) := by
        funext m
        by_cases hm : m = l <;>
          simp [hm, mask, Nat.mod_eq_of_lt hvlt]
      have hbe' : Bounded we (fun m => if m = l then v else env m) := by
        intro m
        by_cases hm : m = l <;> simp [hm]
        · exact hvlt
        · exact hbe m
      have hbw' : ∀ n wn, wof n = some wn →
          (fun m => if m = l then v else env m) n < 2 ^ wn := by
        intro n wn hn
        by_cases hm : n = l <;> simp [hm]
        · subst hm
          rw [hn] at hwl
          simp only [Option.some_inj] at hwl
          exact hwl ▸ hvlt
        · exact hbw n wn hn
      obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
        ih _ hrest hbe' hbw'
      refine ⟨.assign l sv :: pairs, env', ?_, ?_, ?_, hbe'', hbw''⟩
      · simp [emitAssigns, hsv, hemit]
      · simp [Sparkle.IR.Semantics.evalAssigns, hv, hIR]
      · -- SV: the LHS width is declared; the RHS at that width is the
        -- IR value (width agreement rewrites the context)
        have hval : evalSV wof env (we l) sv = some v := by
          rw [← hwr]
          rw [emit_sem_evalSV hSF hbe hbw hsv]
          exact hv
        simp only [evalAssignsSV, hwl, hval, Option.bind_eq_bind,
          Option.bind_some]
        rw [henv]
        exact hSV
    | register n w clk x init =>
      simp only [assignsCheck] at hchk
      obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
        ih env hchk hbe hbw
      exact ⟨pairs, env', by simpa [emitAssigns] using hemit,
        by simpa [Sparkle.IR.Semantics.evalAssigns] using hIR,
        hSV, hbe'', hbw''⟩
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [assignsCheck, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true] at hchk
      obtain ⟨hmem, hrest⟩ := hchk
      by_cases hcr : cr
      · -- combinational read ports: they ARE part of this phase
        subst hcr
        have hports : readPortsCheck wof we aw dw ((ra, rd) :: er) = true := by
          rcases hmem with h | h
          · exact absurd h (by simp)
          · exact h
        obtain ⟨svports, envR, hemitR, hIRR, hSVR, hbeR, hbwR⟩ :=
          emit_sem_comboReads mems nm aw dw ((ra, rd) :: er) env hports
            hbe hbw
        obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
          ih envR hrest hbeR hbwR
        refine ⟨.reads nm aw dw svports :: pairs, env', ?_, ?_, ?_,
          hbe'', hbw''⟩
        · simp [emitAssigns, hemitR, hemit]
        · simp [Sparkle.IR.Semantics.evalAssigns, hIRR, hIR]
        · simp [evalAssignsSV, hSVR, hSV]
      · simp only [hcr] at hmem
        obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
          ih env hrest hbe hbw
        exact ⟨pairs, env', by simpa [emitAssigns, hcr] using hemit,
          by simpa [Sparkle.IR.Semantics.evalAssigns, hcr] using hIR,
          hSV, hbe'', hbw''⟩
    | inst nm md conns =>
      simp only [assignsCheck] at hchk
      obtain ⟨pairs, env', hemit, hIR, hSV, hbe'', hbw''⟩ :=
        ih env hchk hbe hbw
      exact ⟨pairs, env', by simpa [emitAssigns] using hemit,
        by simpa [Sparkle.IR.Semantics.evalAssigns] using hIR,
        hSV, hbe'', hbw''⟩

/- ------------------------------------------------------------------ -/
/- The sequential layer and the cycle-trace capstone.                   -/

/-- The register tuples the emitter prints as always-blocks:
    (target, reset name, next-value emission, reset value). -/
def emitRegs (wof : String → Option Nat) :
    List Stmt → Option (List (String × String × SVExpr × Int))
  | [] => some []
  | .register out _ (rstName, _) input init :: rest => do
    let sv ← Tools.SVParser.EmitAst.emitAstExpr wof input
    let others ← emitRegs wof rest
    some ((out, rstName, sv, init) :: others)
  | .assign _ _ :: rest => emitRegs wof rest
  | .memory _ _ _ _ _ _ _ _ _ _ _ _ :: rest => emitRegs wof rest
  | .inst _ _ _ :: rest => emitRegs wof rest

/-- Verilog's register phase: each always-block reads the SETTLED
    combinational environment, applies its reset mux, and truncates
    the next value into the register's declared width. -/
def regNextsSV (wof : String → Option Nat) :
    List (String × String × SVExpr × Int) → SEnv →
    Option (List (String × Nat))
  | [], _ => some []
  | (out, rst, svin, init) :: rest, env => do
    let w ← wof out
    let v ← evalSV wof env w svin
    let nexts ← regNextsSV wof rest env
    some ((out, if env rst ≠ 0
      then Sparkle.IR.Semantics.encodeInit init w
      else mask w v) :: nexts)

/-- The sequential fragment check: the combinational conditions, plus
    every register's next value in the fragment at the register's
    width under a declared name — and NO memories (their ports are the
    next layer). -/
def seqCheck (wof : String → Option Nat) (we : WEnv) :
    List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (Sparkle.Backend.Verilog.sanitizeName l == l)
      && (wof l == some (we l))
      && (Sparkle.IR.Semantics.widthOf we r == we l)
      && sf4Check wof we r
      && seqCheck wof we rest
  | .register out _ _ input _ :: rest =>
    (wof out == some (we out))
      && (Sparkle.IR.Semantics.widthOf we input == we out)
      && sf4Check wof we input
      && seqCheck wof we rest
  -- a combinationally-read memory: read ports feed the combinational
  -- phase, write ports the sequential one (sync-read memories latch
  -- into register-like state, which is the next layer)
  | .memory _ aw dw _ wa wd wen ra rd cr ew er :: rest =>
    cr && readPortsCheck wof we aw dw ((ra, rd) :: er)
      && (((wa, wd, wen) :: ew).all fun p =>
            portCheck wof we aw p.1 && portCheck wof we dw p.2.1
              && portCheck wof we 1 p.2.2)
      && seqCheck wof we rest
  | .inst _ _ _ :: rest => seqCheck wof we rest

/-- `seqCheck` implies the combinational-phase check. -/
theorem seqCheck_assigns {wof : String → Option Nat} {we : WEnv} :
    ∀ {body : List Stmt}, seqCheck wof we body = true →
      assignsCheck wof we body = true := by
  intro body
  induction body with
  | nil => intro _; rfl
  | cons st rest ih =>
    intro h
    cases st with
    | assign l r =>
      simp only [seqCheck, Bool.and_eq_true] at h
      simp only [assignsCheck, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
    | register _ _ _ _ _ =>
      simp only [seqCheck, Bool.and_eq_true] at h
      simpa [assignsCheck] using ih h.2
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [seqCheck, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hcr, hrd⟩, _⟩, hrest⟩ := h
      simp only [assignsCheck, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨Or.inr hrd, ih hrest⟩
    | inst _ _ _ =>
      simp only [seqCheck] at h
      simpa [assignsCheck] using ih h

/-- The emitter's memory-write program: one entry per memory. -/
def emitMemWrites (wof : String → Option Nat) :
    List Stmt → Option (List (String × Nat × Nat ×
      List (SVExpr × SVExpr × SVExpr)))
  | [] => some []
  | .memory name aw dw _ wa wd wen _ _ _ ew _ :: rest => do
    let ports ← emitWritePorts wof ((wa, wd, wen) :: ew)
    let others ← emitMemWrites wof rest
    some ((name, aw, dw, ports) :: others)
  | .assign _ _ :: rest => emitMemWrites wof rest
  | .register _ _ _ _ _ :: rest => emitMemWrites wof rest
  | .inst _ _ _ :: rest => emitMemWrites wof rest

/-- Verilog's memory-update phase: run each memory's write ports in the
    settled environment. -/
def memNextsSV (wof : String → Option Nat) :
    List (String × Nat × Nat × List (SVExpr × SVExpr × SVExpr)) →
    Sparkle.IR.Semantics.MEnv → SEnv → Option Sparkle.IR.Semantics.MEnv
  | [], mems, _ => some mems
  | (name, aw, dw, ports) :: rest, mems, env => do
    let mems' ← memWritePortsSV wof env name aw dw ports mems
    memNextsSV wof rest mems' env

set_option maxHeartbeats 800000 in
/-- **Forward correctness, memory phase**: the emitted `always_ff`
    stores produce the same memory state as the IR's `memNexts`. -/
theorem emit_sem_memNexts {wof : String → Option Nat} {we : WEnv} :
    ∀ (body : List Stmt) (mems : Sparkle.IR.Semantics.MEnv) (env : Env),
      seqCheck wof we body = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ prog mems',
        emitMemWrites wof body = some prog
        ∧ Sparkle.IR.Semantics.memNexts we body mems env = some mems'
        ∧ memNextsSV wof prog mems env = some mems' := by
  intro body
  induction body with
  | nil => intro mems env _ _ _; exact ⟨[], mems, rfl, rfl, rfl⟩
  | cons st rest ih =>
    intro mems env hchk hbe hbw
    cases st with
    | assign l r =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih mems env hchk.2 hbe hbw
      exact ⟨prog, mems', by simpa [emitMemWrites] using hemit,
        by simpa [Sparkle.IR.Semantics.memNexts] using hIR, hSV⟩
    | register _ _ _ _ _ =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih mems env hchk.2 hbe hbw
      exact ⟨prog, mems', by simpa [emitMemWrites] using hemit,
        by simpa [Sparkle.IR.Semantics.memNexts] using hIR, hSV⟩
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨⟨⟨_, _⟩, hwp⟩, hrest⟩ := hchk
      obtain ⟨svports, m1, hemitW, hIRW, hSVW⟩ :=
        emit_sem_writePorts mems nm aw dw ((wa, wd, wen) :: ew) env mems
          hwp hbe hbw
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih m1 env hrest hbe hbw
      refine ⟨(nm, aw, dw, svports) :: prog, mems', ?_, ?_, ?_⟩
      · simp [emitMemWrites, hemitW, hemit]
      · simp [Sparkle.IR.Semantics.memNexts, hIRW, hIR]
      · simp [memNextsSV, hSVW, hSV]
    | inst _ _ _ =>
      simp only [seqCheck] at hchk
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih mems env hchk hbe hbw
      exact ⟨prog, mems', by simpa [emitMemWrites] using hemit,
        by simpa [Sparkle.IR.Semantics.memNexts] using hIR, hSV⟩

/-- **Forward correctness, register phase**: on a checked body, the
    emitter's register list exists and Verilog's always-block fold in
    the settled environment computes exactly the IR's `regNexts`. -/
theorem emit_sem_regs {wof : String → Option Nat} {we : WEnv}
    (mems : Sparkle.IR.Semantics.MEnv) :
    ∀ (body : List Stmt) (env : Env),
      seqCheck wof we body = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ regs nexts,
        emitRegs wof body = some regs
        ∧ Sparkle.IR.Semantics.regNexts we mems body env = some nexts
        ∧ regNextsSV wof regs env = some nexts := by
  intro body
  induction body with
  | nil => intro env _ _ _; exact ⟨[], [], rfl, rfl, rfl⟩
  | cons st rest ih =>
    intro env hchk hbe hbw
    cases st with
    | assign l r =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨regs, nexts, hemit, hIR, hSV⟩ := ih env hchk.2 hbe hbw
      exact ⟨regs, nexts, by simpa [emitRegs] using hemit,
        by simpa [Sparkle.IR.Semantics.regNexts] using hIR, hSV⟩
    | register out clk rstK input init =>
      obtain ⟨rstName, kind⟩ := rstK
      simp only [seqCheck, Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨hwo, hwi⟩, hfr⟩, hrest⟩ := hchk
      have hSF := sf4Check_sound hfr
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
        (sf4_eval_isSome hSF env)
      obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
        (sf4_emit_isSome hSF)
      obtain ⟨regs, nexts, hemit, hIR, hSV⟩ := ih env hrest hbe hbw
      have hval : evalSV wof env (we out) sv = some v := by
        rw [← hwi, emit_sem_evalSV hSF hbe hbw hsv]
        exact hv
      refine ⟨(out, rstName, sv, init) :: regs,
        (out, if env rstName ≠ 0
          then Sparkle.IR.Semantics.encodeInit init (we out)
          else mask (we out) v) :: nexts, ?_, ?_, ?_⟩
      · simp [emitRegs, hsv, hemit]
      · simp [Sparkle.IR.Semantics.regNexts, hv, hIR]
      · simp [regNextsSV, hwo, hval, hSV]
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [seqCheck, Bool.and_eq_true] at hchk
      obtain ⟨⟨⟨hcr, _⟩, _⟩, hrest⟩ := hchk
      obtain ⟨regs, nexts, hemit, hIR, hSV⟩ := ih env hrest hbe hbw
      -- a COMBINATIONALLY-read memory contributes no register updates
      refine ⟨regs, nexts, by simpa [emitRegs] using hemit, ?_, hSV⟩
      simpa [Sparkle.IR.Semantics.regNexts, hcr] using hIR
    | inst _ _ _ =>
      simp only [seqCheck] at hchk
      obtain ⟨regs, nexts, hemit, hIR, hSV⟩ := ih env hchk hbe hbw
      exact ⟨regs, nexts, by simpa [emitRegs] using hemit,
        by simpa [Sparkle.IR.Semantics.regNexts] using hIR, hSV⟩

/-- The Verilog trace: elaborate the assigns, step the registers,
    recurse — the mirror of `runModule` for a memory-free module. -/
def runModuleSV (wof : String → Option Nat)
    (pairs : List CombStep)
    (regs : List (String × String × SVExpr × Int))
    (mprog : List (String × Nat × Nat × List (SVExpr × SVExpr × SVExpr)))
    (seed : Nat → (String → Nat) → SEnv) :
    Nat → (String → Nat) → Sparkle.IR.Semantics.MEnv → Option (List SEnv)
  | 0, _, _ => some []
  | k + 1, st, mems => do
    let envF ← evalAssignsSV wof mems pairs (seed k st)
    let nexts ← regNextsSV wof regs envF
    let mems' ← memNextsSV wof mprog mems envF
    let rest ← runModuleSV wof pairs regs mprog seed k
      (Sparkle.IR.Semantics.applyNexts st nexts) mems'
    some (envF :: rest)

set_option maxHeartbeats 800000 in
/-- **The M4 capstone — the forward trace theorem.**  For a module
    body in the sequential fragment, and ANY seeding discipline that
    respects the declared widths, the emitted Verilog — under the
    SystemVerilog-subset semantics — produces the SAME cycle-by-cycle
    trace as the IR, for every cycle count.  On these modules the
    emitter is out of the trusted base in the forward direction. -/
theorem certified_forward_trace {wof : String → Option Nat} {we : WEnv}
    {body : List Stmt}
    (hchk : seqCheck wof we body = true)
    (seed : Nat → (String → Nat) → Env)
    (hseed : ∀ t st, Bounded we (seed t st)
      ∧ ∀ n wn, wof n = some wn → seed t st n < 2 ^ wn) :
    ∃ pairs regs mprog,
      emitAssigns wof body = some pairs
      ∧ emitRegs wof body = some regs
      ∧ emitMemWrites wof body = some mprog
      ∧ ∀ (k : Nat) (st : String → Nat)
          (mems : Sparkle.IR.Semantics.MEnv),
          Sparkle.IR.Semantics.runModule we body seed k st mems
            = runModuleSV wof pairs regs mprog seed k st mems := by
  -- the emissions exist (any bounded env will do to instantiate the
  -- phase theorems; take the seed at 0)
  obtain ⟨pairs0, env0', hemitA, _, _, _, _⟩ :=
    emit_sem_assigns (fun _ _ => 0) body (seed 0 fun _ => 0)
      (seqCheck_assigns hchk) (hseed 0 _).1 (hseed 0 _).2
  obtain ⟨regs0, _, hemitR, _, _⟩ :=
    emit_sem_regs (fun _ _ => 0) body (seed 0 fun _ => 0) hchk
      (hseed 0 _).1 (hseed 0 _).2
  obtain ⟨mprog0, _, hemitM, _, _⟩ :=
    emit_sem_memNexts body (fun _ _ => 0) (seed 0 fun _ => 0) hchk
      (hseed 0 _).1 (hseed 0 _).2
  refine ⟨pairs0, regs0, mprog0, hemitA, hemitR, hemitM, ?_⟩
  intro k
  induction k with
  | zero =>
    intro st mems
    rfl
  | succ k ihk =>
    intro st mems
    obtain ⟨pairs, envF, hemitA', hIRA, hSVA, hbeF, hbwF⟩ :=
      emit_sem_assigns mems body (seed k st)
        (seqCheck_assigns hchk) (hseed k st).1 (hseed k st).2
    rw [hemitA] at hemitA'
    simp only [Option.some_inj] at hemitA'
    subst hemitA'
    obtain ⟨regs, nexts, hemitR', hIRR, hSVR⟩ :=
      emit_sem_regs mems body envF hchk hbeF hbwF
    rw [hemitR] at hemitR'
    simp only [Option.some_inj] at hemitR'
    subst hemitR'
    obtain ⟨mprog, mems', hemitM', hIRM, hSVM⟩ :=
      emit_sem_memNexts body mems envF hchk hbeF hbwF
    rw [hemitM] at hemitM'
    simp only [Option.some_inj] at hemitM'
    subst hemitM'
    simp only [Sparkle.IR.Semantics.runModule,
      Sparkle.IR.Semantics.stepModule, runModuleSV, hIRA, hSVA, hIRR,
      hSVR, hIRM, hSVM, Option.bind_eq_bind, Option.bind_some]
    rw [ihk (Sparkle.IR.Semantics.applyNexts st nexts) mems']

/- ------------------------------------------------------------------ -/
/- Module-level packaging: discharging the width hypotheses.           -/

/-- The value-width environment a module induces from its width map —
    the one `moduleWof`-based census uses. -/
def weOf (wof : String → Option Nat) : WEnv := fun n => (wof n).getD 0

/-- Under the induced environment the two width hypotheses of the M4
    theorems are literally the same statement, so a caller supplies
    ONE.  (`wof n = some wn` forces `weOf wof n = wn`.) -/
theorem bounded_iff_wof {wof : String → Option Nat} {env : Env}
    (hbe : Bounded (weOf wof) env) :
    ∀ n wn, wof n = some wn → env n < 2 ^ wn := by
  intro n wn hn
  have := hbe n
  simpa [weOf, hn] using this

/-- **The M4 capstone, module form.**  One width hypothesis on the
    seeding discipline (values fit their declared widths), and the
    emitted Verilog's trace IS the IR's, for every cycle count. -/
theorem certified_forward_trace_module {wof : String → Option Nat}
    {body : List Stmt}
    (hchk : seqCheck wof (weOf wof) body = true)
    (seed : Nat → (String → Nat) → Env)
    (hseed : ∀ t st, Bounded (weOf wof) (seed t st)) :
    ∃ pairs regs mprog,
      emitAssigns wof body = some pairs
      ∧ emitRegs wof body = some regs
      ∧ emitMemWrites wof body = some mprog
      ∧ ∀ (k : Nat) (st : String → Nat)
          (mems : Sparkle.IR.Semantics.MEnv),
          Sparkle.IR.Semantics.runModule (weOf wof) body seed k st mems
            = runModuleSV wof pairs regs mprog seed k st mems :=
  certified_forward_trace hchk seed
    (fun t st => ⟨hseed t st, bounded_iff_wof (hseed t st)⟩)

end Tools.SVParser.EmitSem
