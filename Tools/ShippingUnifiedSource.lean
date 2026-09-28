import Tools.ShippingVectorMuxRecursion

/-! A single source language for mutually nested Bool/BitVec expressions.
This module describes source meanings and quotation, not compiler correctness.
In particular, a new source constructor does not extend the shipping endpoint
until its recursive translation contract is connected. -/
namespace Tools.ShippingUnifiedSource
open Lean Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingMuxTypeSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingVectorMuxRecursion

inductive SType where
  | bool | bits
  deriving DecidableEq

abbrev SType.Type (n : Nat) : SType → Type
  | .bool => Bool
  | .bits => BitVec n

def SType.width (n : Nat) : SType → Nat
  | .bool => 1
  | .bits => n

def SType.quoteType (n : Nat) : SType → Lean.Expr
  | .bool => .const ``Bool []
  | .bits => bitVecE n

/-- Unlike BExpr/FExpr/VExpr, both sorts recurse into each other. -/
inductive Term : SType → Type where
  | boolInput (j : Nat) : Term .bool
  | bitsInput (j : Nat) : Term .bits
  | boolLit (b : Bool) : Term .bool
  | bitsLit (v : Nat) : Term .bits
  | binary (op : Binary) (a b : Term .bits) : Term .bits
  | compare (op : SignalCompareKind) (a b : Term .bits) : Term .bool
  | boolBinary (op : SignalBoolBinKind) (a b : Term .bool) : Term .bool
  | boolNot (a : Term .bool) : Term .bool
  | boolEq (a b : Term .bool) : Term .bool
  | mux {s : SType} (c : Term .bool) (a b : Term s) : Term s

def Term.WF (kb kv n : Nat) : {s : SType} → Term s → Prop
  | _, .boolInput j => j < kb
  | _, .bitsInput j => j < kv
  | _, .boolLit _ => True
  | _, .bitsLit v => v < 2 ^ n
  | _, .binary _ a b => a.WF kb kv n ∧ b.WF kb kv n
  | _, .compare _ a b => a.WF kb kv n ∧ b.WF kb kv n
  | _, .boolBinary _ a b => a.WF kb kv n ∧ b.WF kb kv n
  | _, .boolNot a => a.WF kb kv n
  | _, .boolEq a b => a.WF kb kv n ∧ b.WF kb kv n
  | _, .mux c a b => c.WF kb kv n ∧ a.WF kb kv n ∧ b.WF kb kv n

def eval (n : Nat) (bools : Nat → Bool) (bits : Nat → BitVec n) : {s : SType} → Term s → s.Type n
  | _, .boolInput j => bools j
  | _, .bitsInput j => bits j
  | _, .boolLit b => b
  | _, .bitsLit v => BitVec.ofNat n v
  | _, .binary op a b => op.apply (eval n bools bits a) (eval n bools bits b)
  | _, .compare op a b => compareValue op (eval n bools bits a) (eval n bools bits b)
  | _, .boolBinary op a b => boolBinValue op (eval n bools bits a) (eval n bools bits b)
  | _, .boolNot a => !(eval n bools bits a)
  | _, .boolEq a b => eval n bools bits a == eval n bools bits b
  | _, .mux c a b => if eval n bools bits c then eval n bools bits a else eval n bools bits b

def denote {dom : DomainConfig} (n : Nat) (bools : Nat → Signal dom Bool)
    (bits : Nat → Signal dom (BitVec n)) : {s : SType} → Term s → Signal dom (s.Type n)
  | _, .boolInput j => bools j
  | _, .bitsInput j => bits j
  | _, .boolLit b => Signal.pure b
  | _, .bitsLit v => Signal.pure (BitVec.ofNat n v)
  | _, .binary op a b => binSig op (denote n bools bits a) (denote n bools bits b)
  | _, .compare op a b => match op with
      | .ult => Signal.ult (denote n bools bits a) (denote n bools bits b)
      | .ule => Signal.ule (denote n bools bits a) (denote n bools bits b)
      | .slt => Signal.slt (denote n bools bits a) (denote n bools bits b)
      | .sle => Signal.sle (denote n bools bits a) (denote n bools bits b)
      | .eq => Signal.beq (denote n bools bits a) (denote n bools bits b)
  | _, .boolBinary op a b => match op with
      | .band => denote n bools bits a &&& denote n bools bits b
      | .bor => denote n bools bits a ||| denote n bools bits b
      | .bxor => denote n bools bits a ^^^ denote n bools bits b
  | _, .boolNot a => ~~~(denote n bools bits a)
  | _, .boolEq a b => Signal.beq (denote n bools bits a) (denote n bools bits b)
  | _, .mux c a b => Signal.mux (denote n bools bits c) (denote n bools bits a) (denote n bools bits b)

theorem denote_val {dom : DomainConfig} (n : Nat) (bools : Nat → Signal dom Bool)
    (bits : Nat → Signal dom (BitVec n)) (tick : Nat) : ∀ {s} (e : Term s),
    (denote n bools bits e).val tick = eval n (fun j => (bools j).val tick) (fun j => (bits j).val tick) e
  | _, .boolInput _ => rfl
  | _, .bitsInput _ => rfl
  | _, .boolLit _ => rfl
  | _, .bitsLit _ => rfl
  | _, .binary op a b => by
    have step : (denote n bools bits (.binary op a b)).val tick =
        op.apply ((denote n bools bits a).val tick) ((denote n bools bits b).val tick) := by cases op <;> rfl
    rw [step, denote_val, denote_val]; rfl
  | _, .compare op a b => by
    have step : (denote n bools bits (.compare op a b)).val tick =
        compareValue op ((denote n bools bits a).val tick) ((denote n bools bits b).val tick) := by cases op <;> rfl
    rw [step, denote_val, denote_val]; rfl
  | _, .boolBinary op a b => by
    have step : (denote n bools bits (.boolBinary op a b)).val tick =
        boolBinValue op ((denote n bools bits a).val tick) ((denote n bools bits b).val tick) := by cases op <;> rfl
    rw [step, denote_val, denote_val]; rfl
  | _, .boolNot a => by
    change (!(denote n bools bits a).val tick) = _
    rw [denote_val]; rfl
  | _, .boolEq a b => by
    change ((denote n bools bits a).val tick == (denote n bools bits b).val tick) = _
    rw [denote_val, denote_val]; rfl
  | _, .mux c a b => by
    change (if (denote n bools bits c).val tick then (denote n bools bits a).val tick else
      (denote n bools bits b).val tick) = _
    rw [denote_val, denote_val, denote_val]; rfl

def quote (dom : Lean.Expr) (n : Nat) (bools bits : Nat → Lean.Expr) : {s : SType} → Term s → Lean.Expr
  | _, .boolInput j => bools j
  | _, .bitsInput j => bits j
  | _, .boolLit b => literalE dom b
  | _, .bitsLit v => quoteF dom n bits (.lit v)
  | _, .binary op a b => binE dom n op (quote dom n bools bits a) (quote dom n bools bits b)
  | _, .compare op a b => compareE op dom n (quote dom n bools bits a) (quote dom n bools bits b)
  | _, .boolBinary op a b => boolBinE op dom (quote dom n bools bits a) (quote dom n bools bits b)
  | _, .boolNot a => boolNotE dom (quote dom n bools bits a)
  | _, .boolEq a b => boolEqE dom (quote dom n bools bits a) (quote dom n bools bits b)
  | s, .mux c a b => muxE dom (s.quoteType n) (quote dom n bools bits c)
      (quote dom n bools bits a) (quote dom n bools bits b)

def ofF : FExpr → Term .bits
  | .inp j => .bitsInput j
  | .lit v => .bitsLit v
  | .bin op a b => .binary op (ofF a) (ofF b)

def ofB : BExpr → Term .bool
  | .inp j => .boolInput j
  | .lit b => .boolLit b
  | .compare op a b => .compare op (ofF a) (ofF b)
  | .boolBin op a b => .boolBinary op (ofB a) (ofB b)
  | .boolNot a => .boolNot (ofB a)
  | .boolEq a b => .boolEq (ofB a) (ofB b)
  | .mux c a b => .mux (ofB c) (ofB a) (ofB b)

def ofV : VExpr → Term .bits
  | .arith e => ofF e
  | .mux c a b => .mux (ofB c) (ofV a) (ofV b)

theorem quote_ofF (dom n bi vi) (e : FExpr) : quote dom n bi vi (ofF e) = quoteF dom n vi e := by
  induction e <;> simp_all [ofF, quote, quoteF]
theorem quote_ofB (dom n bi vi) (e : BExpr) : quote dom n bi vi (ofB e) = quoteB dom n bi vi e := by
  induction e <;> simp_all [ofB, quote, quoteB, quote_ofF, literalE, boolName, SType.quoteType]
theorem quote_ofV (dom n bi vi) (e : VExpr) : quote dom n bi vi (ofV e) = quoteV dom n bi vi e := by
  induction e <;> simp_all [ofV, quote, quoteV, quote_ofF, quote_ofB, SType.quoteType]

theorem eval_ofF (n bi vi) (e : FExpr) : eval n bi vi (ofF e) = evalFE n vi e := by
  induction e <;> simp_all [ofF, eval, evalFE]
theorem eval_ofB (n bi vi) (e : BExpr) : eval n bi vi (ofB e) = evalB n bi vi e := by
  induction e <;> simp_all [ofB, eval, evalB, eval_ofF]
theorem eval_ofV (n bi vi) (e : VExpr) : eval n bi vi (ofV e) = evalV n bi vi e := by
  induction e <;> simp_all [ofV, eval, evalV, eval_ofF, eval_ofB]

theorem wf_ofF (kb kv n) (e : FExpr) : (ofF e).WF kb kv n ↔ e.WF kv n := by
  induction e <;> simp_all [ofF, Term.WF, FExpr.WF]
theorem wf_ofB (kb kv n) (e : BExpr) : (ofB e).WF kb kv n ↔ e.WF kb kv n := by
  induction e <;> simp_all [ofB, Term.WF, BExpr.WF, wf_ofF]
theorem wf_ofV (kb kv n) (e : VExpr) : (ofV e).WF kb kv n ↔ e.WF kb kv n := by
  induction e <;> simp_all [ofV, Term.WF, VExpr.WF, wf_ofF, wf_ofB]

theorem instFVars_quote (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr) (n : Nat)
    (bi vi : Nat → Lean.Expr) : ∀ {s} (e : Term s),
    instFVars xs d (quote dom n bi vi e) =
      quote (instFVars xs d dom) n (fun j => instFVars xs d (bi j)) (fun j => instFVars xs d (vi j)) e
  | _, .boolInput _ => rfl
  | _, .bitsInput _ => rfl
  | _, .boolLit b => by cases b <;> rfl
  | _, .bitsLit _ => rfl
  | _, .binary op a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom n bi vi a)))
      (instFVars xs d (quote dom n bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]; cases op <;> rfl
  | _, .compare op a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom n bi vi a)))
      (instFVars xs d (quote dom n bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]; cases op <;> rfl
  | _, .boolBinary op a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom n bi vi a)))
      (instFVars xs d (quote dom n bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]; cases op <;> rfl
  | _, .boolNot a => by
    show Lean.Expr.app (instFVars xs d _) (instFVars xs d (quote dom n bi vi a)) = _
    rw [instFVars_quote]; rfl
  | _, .boolEq a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom n bi vi a)))
      (instFVars xs d (quote dom n bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]; rfl
  | s, .mux c a b => by
    show Lean.Expr.app (.app (.app (instFVars xs d _) (instFVars xs d (quote dom n bi vi c)))
      (instFVars xs d (quote dom n bi vi a))) (instFVars xs d (quote dom n bi vi b)) = _
    rw [instFVars_quote, instFVars_quote, instFVars_quote]; cases s <;> rfl

theorem quote_congr {dom n kb kv} {bi bi' vi vi' : Nat → Lean.Expr}
    (hb : ∀ j, j < kb → bi j = bi' j) (hv : ∀ j, j < kv → vi j = vi' j) :
    ∀ {s} (e : Term s), e.WF kb kv n → quote dom n bi vi e = quote dom n bi' vi' e
  | _, .boolInput j, hj => hb j hj
  | _, .bitsInput j, hj => hv j hj
  | _, .boolLit _, _ => rfl
  | _, .bitsLit _, _ => rfl
  | _, .binary op a b, ⟨ha, hb'⟩ => by simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .compare op a b, ⟨ha, hb'⟩ => by simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .boolBinary op a b, ⟨ha, hb'⟩ => by simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .boolNot a, ha => by simp only [quote, quote_congr hb hv a ha]
  | _, .boolEq a b, ⟨ha, hb'⟩ => by simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | s, .mux c a b, ⟨hc, ha, hb'⟩ => by
    simp only [quote, quote_congr hb hv c hc, quote_congr hb hv a ha, quote_congr hb hv b hb']

end Tools.ShippingUnifiedSource
