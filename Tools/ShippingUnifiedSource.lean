import Tools.ShippingVectorMuxRecursion

/-! A single source language for mutually nested Bool/BitVec expressions with
per-operation widths: different subtrees may use different positive BitVec
widths, while each canonical operation keeps a common operand width. This
module describes source meanings and quotation, not compiler correctness. -/
namespace Tools.ShippingUnifiedSource
open Lean Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingMuxTypeSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingVectorMuxRecursion

inductive SType where
  | bool
  | bits (w : Nat)
  deriving DecidableEq

abbrev SType.Type : SType → Type
  | .bool => Bool
  | .bits w => BitVec w

def SType.width : SType → Nat
  | .bool => 1
  | .bits w => w

def SType.quoteType : SType → Lean.Expr
  | .bool => .const ``Bool []
  | .bits w => bitVecE w

/-- The value of a two-level Bool body. -/
def appBool2Value : AppBool2 → Bool → Bool → Bool
  | .andNot, x, y => x && !y
  | .notAnd, x, y => !x && y
  | .nor, x, y => !(x || y)

/-- Both sorts recurse into each other; every BitVec node carries its width. -/
inductive Term : SType → Type where
  | boolInput (j : Nat) : Term .bool
  | bitsInput (w j : Nat) : Term (.bits w)
  | boolLit (b : Bool) : Term .bool
  | bitsLit (w v : Nat) : Term (.bits w)
  /-- A numeric literal `(v : BitVec w)` — `Signal.pure 5` at the library's
  `OfNat` instance, as opposed to `bitsLit`'s `Signal.pure 5#w`. -/
  | bitsNum (w v : Nat) : Term (.bits w)
  | binary (op : Binary) {w : Nat} (a b : Term (.bits w)) : Term (.bits w)
  | compare (op : SignalCompareKind) {w : Nat} (a b : Term (.bits w)) : Term .bool
  | boolBinary (op : SignalBoolBinKind) (a b : Term .bool) : Term .bool
  | boolNot (a : Term .bool) : Term .bool
  | boolEq (a b : Term .bool) : Term .bool
  | mux {s : SType} (c : Term .bool) (a b : Term s) : Term s
  | setw {w : Nat} (w' : Nat) (a : Term (.bits w)) : Term (.bits w')
  /-- A slice: `a.map (fun x => BitVec.extractLsb' start len x)`. `nm` is the
  lambda's binder name as it stands in the declaration (a hygienic macro name
  for `(BitVec.extractLsb' start len ·)`); it carries no meaning. -/
  | slice (nm : Lean.Name) (start len : Nat) {w : Nat} (a : Term (.bits w)) : Term (.bits len)
  /-- A concatenation `a ++ b` of two Signals: `a` in the high bits. -/
  | concat {m n : Nat} (a : Term (.bits m)) (b : Term (.bits n)) : Term (.bits (m + n))
  /-- A concatenation with a literal high operand: `v#k ++ b`. -/
  | concatLitHi (k v : Nat) {n : Nat} (b : Term (.bits n)) : Term (.bits (k + n))
  /-- A concatenation with a literal low operand: `a ++ v#k`. -/
  | concatLitLo {m : Nat} (a : Term (.bits m)) (k v : Nat) : Term (.bits (m + k))
  /-- Zero-extension by a literal prefix inside a map:
  `a.map (fun v => BitVec.append (0#k) v)`. `nm` is the lambda's binder name. -/
  | zextMap (nm : Lean.Name) (k : Nat) {n : Nat} (a : Term (.bits n)) : Term (.bits (k + n))
  /-- A slice written with `<$>`: `(fun x => BitVec.extractLsb' start len x) <$> a`. -/
  | sliceF (nm : Lean.Name) (start len : Nat) {w : Nat} (a : Term (.bits w)) : Term (.bits len)
  /-- A comparison lifted through the Signal applicative: `(BitVec.ule · ·) <$> a <*> b`. -/
  | appCompare (op : SignalCompareKind) {w : Nat} (a b : Term (.bits w)) : Term .bool
  /-- A Bool operator lifted through the Signal applicative: `(· && ·) <$> a <*> b`. -/
  | appBool (op : SignalBoolBinKind) (a b : Term .bool) : Term .bool
  /-- A two-level Bool body lifted through the Signal applicative:
  `(fun x y => x && !y) <$> a <*> b`, `!x && y`, `!(x || y)`. -/
  | appBool2 (f : AppBool2) (a b : Term .bool) : Term .bool

/-- Inputs are positions into the prepared binder lists; `vw` assigns each
BitVec input its declared width. Positivity is carried at BitVec leaves. -/
def Term.WF (kb kv : Nat) (vw : Nat → Nat) : {s : SType} → Term s → Prop
  | _, .boolInput j => j < kb
  | _, .bitsInput w j => j < kv ∧ vw j = w ∧ 0 < w
  | _, .boolLit _ => True
  | _, .bitsLit w v => v < 2 ^ w ∧ 0 < w
  | _, .bitsNum w v => v < 2 ^ w ∧ 0 < w
  | _, .binary _ a b => a.WF kb kv vw ∧ b.WF kb kv vw
  | _, .compare _ a b => a.WF kb kv vw ∧ b.WF kb kv vw
  | _, .boolBinary _ a b => a.WF kb kv vw ∧ b.WF kb kv vw
  | _, .boolNot a => a.WF kb kv vw
  | _, .boolEq a b => a.WF kb kv vw ∧ b.WF kb kv vw
  | _, .mux c a b => c.WF kb kv vw ∧ a.WF kb kv vw ∧ b.WF kb kv vw
  | _, .setw w' a => a.WF kb kv vw ∧ 0 < w'
  | _, .appCompare _ a b => a.WF kb kv vw ∧ b.WF kb kv vw
  | _, .appBool _ a b => a.WF kb kv vw ∧ b.WF kb kv vw
  | _, .appBool2 _ a b => a.WF kb kv vw ∧ b.WF kb kv vw
  | _, .slice _ start len (w := w) a => a.WF kb kv vw ∧ 0 < len ∧ start + len ≤ w
  | _, .concat a b => a.WF kb kv vw ∧ b.WF kb kv vw
  | _, .concatLitHi k v b => b.WF kb kv vw ∧ 0 < k ∧ v < 2 ^ k
  | _, .concatLitLo a k v => a.WF kb kv vw ∧ 0 < k ∧ v < 2 ^ k
  | _, .zextMap _ k a => a.WF kb kv vw ∧ 0 < k
  | _, .sliceF _ start len (w := w) a => a.WF kb kv vw ∧ 0 < len ∧ start + len ≤ w

/-- Every well-formed BitVec term has a positive width. -/
theorem Term.wf_pos {kb kv : Nat} {vw : Nat → Nat} :
    ∀ {w : Nat} (e : Term (.bits w)), e.WF kb kv vw → 0 < w
  | _, .bitsInput _ _, h => h.2.2
  | _, .bitsLit _ _, h => h.2
  | _, .bitsNum _ _, h => h.2
  | _, .binary _ a _, h => a.wf_pos h.1
  | _, .mux _ a _, h => a.wf_pos h.2.1
  | _, .setw _ _, h => h.2
  | _, .slice _ _ _ _, h => h.2.1
  | _, .concat a _, h => Nat.add_pos_left (a.wf_pos h.1) _
  | _, .concatLitHi _ _ _, h => Nat.add_pos_left h.2.1 _
  | _, .concatLitLo _ _ _, h => Nat.add_pos_right _ h.2.1
  | _, .zextMap _ _ _, h => Nat.add_pos_left h.2 _
  | _, .sliceF _ _ _ _, h => h.2.1

def eval (bools : Nat → Bool) (bits : (j : Nat) → (w : Nat) → BitVec w) :
    {s : SType} → Term s → s.Type
  | _, .boolInput j => bools j
  | _, .bitsInput w j => bits j w
  | _, .boolLit b => b
  | _, .bitsLit w v => BitVec.ofNat w v
  | _, .bitsNum w v => BitVec.ofNat w v
  | _, .binary op a b => op.apply (eval bools bits a) (eval bools bits b)
  | _, .compare op a b => compareValue op (eval bools bits a) (eval bools bits b)
  | _, .boolBinary op a b => boolBinValue op (eval bools bits a) (eval bools bits b)
  | _, .boolNot a => !(eval bools bits a)
  | _, .boolEq a b => eval bools bits a == eval bools bits b
  | _, .mux c a b => if eval bools bits c then eval bools bits a else eval bools bits b
  | _, .setw w' a => BitVec.setWidth w' (eval bools bits a)
  | _, .appCompare op a b => compareValue op (eval bools bits a) (eval bools bits b)
  | _, .appBool op a b => boolBinValue op (eval bools bits a) (eval bools bits b)
  | _, .appBool2 f a b => appBool2Value f (eval bools bits a) (eval bools bits b)
  | _, .slice _ start len a => BitVec.extractLsb' start len (eval bools bits a)
  | _, .concat a b => eval bools bits a ++ eval bools bits b
  | _, .concatLitHi k v b => BitVec.ofNat k v ++ eval bools bits b
  | _, .concatLitLo a k v => eval bools bits a ++ BitVec.ofNat k v
  | _, .zextMap _ k a => BitVec.append (BitVec.ofNat k 0) (eval bools bits a)
  | _, .sliceF _ start len a => BitVec.extractLsb' start len (eval bools bits a)

def denote {dom : DomainConfig} (bools : Nat → Signal dom Bool)
    (bits : (j : Nat) → (w : Nat) → Signal dom (BitVec w)) :
    {s : SType} → Term s → Signal dom (s.Type)
  | _, .boolInput j => bools j
  | _, .bitsInput w j => bits j w
  | _, .boolLit b => Signal.pure b
  | _, .bitsLit w v => Signal.pure (BitVec.ofNat w v)
  | _, .bitsNum w v => Signal.pure (BitVec.ofNat w v)
  | _, .binary op a b => binSig op (denote bools bits a) (denote bools bits b)
  | _, .compare op a b => match op with
      | .ult => Signal.ult (denote bools bits a) (denote bools bits b)
      | .ule => Signal.ule (denote bools bits a) (denote bools bits b)
      | .slt => Signal.slt (denote bools bits a) (denote bools bits b)
      | .sle => Signal.sle (denote bools bits a) (denote bools bits b)
      | .eq => Signal.beq (denote bools bits a) (denote bools bits b)
  | _, .boolBinary op a b => match op with
      | .band => denote bools bits a &&& denote bools bits b
      | .bor => denote bools bits a ||| denote bools bits b
      | .bxor => denote bools bits a ^^^ denote bools bits b
  | _, .boolNot a => ~~~(denote bools bits a)
  | _, .boolEq a b => Signal.beq (denote bools bits a) (denote bools bits b)
  | _, .mux c a b => Signal.mux (denote bools bits c) (denote bools bits a) (denote bools bits b)
  | _, .setw w' a => Signal.map (BitVec.setWidth w') (denote bools bits a)
  | _, .appCompare op a b =>
      Signal.ap (Signal.map (fun x y => compareValue op x y) (denote bools bits a))
        (denote bools bits b)
  | _, .appBool op a b =>
      Signal.ap (Signal.map (fun x y => boolBinValue op x y) (denote bools bits a))
        (denote bools bits b)
  | _, .appBool2 f a b =>
      Signal.ap (Signal.map (fun x y => appBool2Value f x y) (denote bools bits a))
        (denote bools bits b)
  | _, .slice _ start len a =>
      Signal.map (fun x => BitVec.extractLsb' start len x) (denote bools bits a)
  | _, .concat a b => denote bools bits a ++ denote bools bits b
  | _, .concatLitHi k v b => BitVec.ofNat k v ++ denote bools bits b
  | _, .concatLitLo a k v => denote bools bits a ++ BitVec.ofNat k v
  | _, .zextMap _ k a =>
      Signal.map (fun v => BitVec.append (BitVec.ofNat k 0) v) (denote bools bits a)
  | _, .sliceF _ start len a =>
      (fun x => BitVec.extractLsb' start len x) <$> denote bools bits a

theorem denote_val {dom : DomainConfig} (bools : Nat → Signal dom Bool)
    (bits : (j : Nat) → (w : Nat) → Signal dom (BitVec w)) (tick : Nat) : ∀ {s} (e : Term s),
    (denote bools bits e).val tick =
      eval (fun j => (bools j).val tick) (fun j w => (bits j w).val tick) e
  | _, .boolInput _ => rfl
  | _, .bitsInput _ _ => rfl
  | _, .boolLit _ => rfl
  | _, .bitsLit _ _ => rfl
  | _, .bitsNum _ _ => rfl
  | _, .binary op a b => by
    have step : (denote bools bits (.binary op a b)).val tick =
        op.apply ((denote bools bits a).val tick) ((denote bools bits b).val tick) := by
      cases op <;> rfl
    rw [step, denote_val, denote_val]; rfl
  | _, .compare op a b => by
    have step : (denote bools bits (.compare op a b)).val tick =
        compareValue op ((denote bools bits a).val tick) ((denote bools bits b).val tick) := by
      cases op <;> rfl
    rw [step, denote_val, denote_val]; rfl
  | _, .boolBinary op a b => by
    have step : (denote bools bits (.boolBinary op a b)).val tick =
        boolBinValue op ((denote bools bits a).val tick) ((denote bools bits b).val tick) := by
      cases op <;> rfl
    rw [step, denote_val, denote_val]; rfl
  | _, .boolNot a => by
    change (!(denote bools bits a).val tick) = _
    rw [denote_val]; rfl
  | _, .boolEq a b => by
    change ((denote bools bits a).val tick == (denote bools bits b).val tick) = _
    rw [denote_val, denote_val]; rfl
  | _, .mux c a b => by
    change (if (denote bools bits c).val tick then (denote bools bits a).val tick else
      (denote bools bits b).val tick) = _
    rw [denote_val, denote_val, denote_val]; rfl
  | _, .setw w' a => by
    change BitVec.setWidth w' ((denote bools bits a).val tick) = _
    rw [denote_val]; rfl
  | _, .appCompare op a b => by
    change compareValue op ((denote bools bits a).val tick) ((denote bools bits b).val tick) = _
    rw [denote_val, denote_val]; rfl
  | _, .appBool op a b => by
    change boolBinValue op ((denote bools bits a).val tick) ((denote bools bits b).val tick) = _
    rw [denote_val, denote_val]; rfl
  | _, .appBool2 f a b => by
    change appBool2Value f ((denote bools bits a).val tick) ((denote bools bits b).val tick) = _
    rw [denote_val, denote_val]; rfl
  | _, .slice _ start len a => by
    change BitVec.extractLsb' start len ((denote bools bits a).val tick) = _
    rw [denote_val]; rfl
  | _, .concat a b => by
    change (denote bools bits a).val tick ++ (denote bools bits b).val tick = _
    rw [denote_val, denote_val]; rfl
  | _, .concatLitHi k v b => by
    change BitVec.ofNat k v ++ (denote bools bits b).val tick = _
    rw [denote_val]; rfl
  | _, .concatLitLo a k v => by
    change (denote bools bits a).val tick ++ BitVec.ofNat k v = _
    rw [denote_val]; rfl
  | _, .zextMap _ k a => by
    change BitVec.append (BitVec.ofNat k 0) ((denote bools bits a).val tick) = _
    rw [denote_val]; rfl
  | _, .sliceF _ start len a => by
    change BitVec.extractLsb' start len ((denote bools bits a).val tick) = _
    rw [denote_val]; rfl

/-- The canonical width-changing map node: `Signal.map (BitVec.setWidth w') a`
    exactly as dot-notation elaborates it (a partial application, no lambda). -/
def setwE (dom : Lean.Expr) (w w' : Nat) (a : Lean.Expr) : Lean.Expr :=
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero]) dom (bitVecE w) (bitVecE w')
    (mkApp2 (.const ``BitVec.setWidth []) (natE w) (natE w')) a

/-- A numeric `BitVec` literal as it elaborates: `@OfNat.ofNat (BitVec w) v
    (BitVec.instOfNat)`. -/
def numLitE (w v : Nat) : Lean.Expr :=
  mkApp3 (.const ``OfNat.ofNat [.zero]) (bitVecE w) (.lit (.natVal v))
    (mkApp2 (.const ``BitVec.instOfNat []) (natE w) (.lit (.natVal v)))

/-- `Signal.pure` of a numeric literal. -/
def numSigE (dom : Lean.Expr) (w v : Nat) : Lean.Expr :=
  mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (bitVecE w) (numLitE w v)

theorem litValue_numLitE (n v : Nat) (h : v < 2 ^ n) :
    bitVecLitValue? (numLitE n v) = some (n, v) := by
  have e : bitVecLitValue? (numLitE n v) = (if v < 2 ^ n then some (n, v) else none) := rfl
  rw [e, if_pos h]

/-- The function of an applicative lift, with the canonical binder names the
    front end gives it: `fun x1 x2 => body` over element type `ty`. -/
def appLamE (ty body : Lean.Expr) : Lean.Expr :=
  .lam `x1 ty (.lam `x2 ty body .default) .default

/-- `Signal.ap (Signal.map (fun x1 x2 => body) a) b` at element type `ty` and
    result `Bool`: the form the front end normalises `f <$> a <*> b` to. -/
def appE (dom ty body a b : Lean.Expr) : Lean.Expr :=
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.ap [.zero]) dom ty (.const ``Bool [])
    (mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero]) dom ty
      (.forallE `a ty (.const ``Bool []) .default) (appLamE ty body) a) b

/-- The value-level comparison applied to the two bound variables. -/
def appCompareBodyE (op : SignalCompareKind) (w : Nat) : Lean.Expr :=
  match op with
  | .ult => mkApp3 (.const ``BitVec.ult []) (natE w) (.bvar 1) (.bvar 0)
  | .ule => mkApp3 (.const ``BitVec.ule []) (natE w) (.bvar 1) (.bvar 0)
  | .slt => mkApp3 (.const ``BitVec.slt []) (natE w) (.bvar 1) (.bvar 0)
  | .sle => mkApp3 (.const ``BitVec.sle []) (natE w) (.bvar 1) (.bvar 0)
  | .eq => mkApp4 (.const ``BEq.beq [.zero]) (bitVecE w)
      (mkApp2 (.const ``instBEqOfDecidableEq [.zero]) (bitVecE w)
        (mkApp (.const ``instDecidableEqBitVec []) (natE w))) (.bvar 1) (.bvar 0)

/-- The value-level Bool operator applied to the two bound variables. -/
def appBoolBodyE (op : SignalBoolBinKind) : Lean.Expr :=
  match op with
  | .band => mkApp2 (.const ``Bool.and []) (.bvar 1) (.bvar 0)
  | .bor => mkApp2 (.const ``Bool.or []) (.bvar 1) (.bvar 0)
  | .bxor => mkApp2 (.const ``Bool.xor []) (.bvar 1) (.bvar 0)

def appCompareE (op : SignalCompareKind) (dom : Lean.Expr) (w : Nat) (a b : Lean.Expr) :
    Lean.Expr :=
  appE dom (bitVecE w) (appCompareBodyE op w) a b

def appBoolE (op : SignalBoolBinKind) (dom a b : Lean.Expr) : Lean.Expr :=
  appE dom (.const ``Bool []) (appBoolBodyE op) a b

/-- The two-level Bool body applied to the two bound variables. -/
def appBool2BodyE (f : AppBool2) : Lean.Expr :=
  match f with
  | .andNot => mkApp2 (.const ``Bool.and []) (.bvar 1) (.app (.const ``Bool.not []) (.bvar 0))
  | .notAnd => mkApp2 (.const ``Bool.and []) (.app (.const ``Bool.not []) (.bvar 1)) (.bvar 0)
  | .nor => .app (.const ``Bool.not []) (mkApp2 (.const ``Bool.or []) (.bvar 1) (.bvar 0))

def appBool2E (f : AppBool2) (dom a b : Lean.Expr) : Lean.Expr :=
  appE dom (.const ``Bool []) (appBool2BodyE f) a b

/-- The canonical slice map: `Signal.map (fun nm => BitVec.extractLsb' start
    len nm) a` over a `w`-bit source, exactly as dot-notation elaborates it. -/
def sliceE (dom : Lean.Expr) (nm : Lean.Name) (w start len : Nat) (a : Lean.Expr) : Lean.Expr :=
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero]) dom (bitVecE w) (bitVecE len)
    (.lam nm (bitVecE w)
      (mkApp4 (.const ``BitVec.extractLsb' []) (natE w) (natE start) (natE len) (.bvar 0))
      .default) a

/-- The canonical concatenation: `a ++ b` at the library's Signal instance,
    with the result width as the literal of `m + n` (the front end folds the
    sum the elaborator writes). -/
def concatE (dom : Lean.Expr) (m n : Nat) (a b : Lean.Expr) : Lean.Expr :=
  mkApp6 (.const ``HAppend.hAppend [.zero, .zero, .zero]) (sigT dom m) (sigT dom n)
    (sigT dom (m + n))
    (mkApp3 (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat []) dom (natE m)
      (natE n)) a b

/-- The literal `v#k`. -/
def litE (k v : Nat) : Lean.Expr := mkApp2 (.const ``BitVec.ofNat []) (natE k) (natE v)

/-- `v#k ++ b` at the library's literal-high instance (whose implicit
    arguments are the literal's width, the domain, the Signal's width). -/
def concatLitHiE (dom : Lean.Expr) (k v n : Nat) (b : Lean.Expr) : Lean.Expr :=
  mkApp6 (.const ``HAppend.hAppend [.zero, .zero, .zero]) (bitVecE k) (sigT dom n)
    (sigT dom (k + n))
    (mkApp3 (.const ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat []) (natE k) dom
      (natE n)) (litE k v) b

/-- `a ++ v#k` at the library's literal-low instance. -/
def concatLitLoE (dom : Lean.Expr) (m k v : Nat) (a : Lean.Expr) : Lean.Expr :=
  mkApp6 (.const ``HAppend.hAppend [.zero, .zero, .zero]) (sigT dom m) (bitVecE k)
    (sigT dom (m + k))
    (mkApp3 (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat_1 []) dom (natE m)
      (natE k)) a (litE k v)

/-- `Signal.map (fun nm => BitVec.append (0#k) nm) a` over an `n`-bit source,
    the result width the literal of `k + n`. -/
def zextMapE (dom : Lean.Expr) (nm : Lean.Name) (k n : Nat) (a : Lean.Expr) : Lean.Expr :=
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero]) dom (bitVecE n) (bitVecE (k + n))
    (.lam nm (bitVecE n)
      (mkApp4 (.const ``BitVec.append []) (natE k) (natE n) (litE k 0) (.bvar 0)) .default) a

/-- `(fun nm => BitVec.extractLsb' start len nm) <$> a` at the library's
    `Functor` instance. -/
def sliceFE (dom : Lean.Expr) (nm : Lean.Name) (w start len : Nat) (a : Lean.Expr) : Lean.Expr :=
  mkApp6 (.const ``Functor.map [.zero, .zero])
    (.app (.const ``Sparkle.Core.Signal.Signal [.zero]) dom)
    (.app (.const ``Sparkle.Core.Signal.instFunctorSignal [.zero]) dom)
    (bitVecE w) (bitVecE len)
    (.lam nm (bitVecE w)
      (mkApp4 (.const ``BitVec.extractLsb' []) (natE w) (natE start) (natE len) (.bvar 0))
      .default) a

def quote (dom : Lean.Expr) (bools bits : Nat → Lean.Expr) : {s : SType} → Term s → Lean.Expr
  | _, .boolInput j => bools j
  | _, .bitsInput _ j => bits j
  | _, .boolLit b => literalE dom b
  | _, .bitsLit w v => quoteF dom w bits (.lit v)
  | _, .bitsNum w v => numSigE dom w v
  | _, .binary op (w := w) a b => binE dom w op (quote dom bools bits a) (quote dom bools bits b)
  | _, .compare op (w := w) a b => compareE op dom w (quote dom bools bits a) (quote dom bools bits b)
  | _, .boolBinary op a b => boolBinE op dom (quote dom bools bits a) (quote dom bools bits b)
  | _, .boolNot a => boolNotE dom (quote dom bools bits a)
  | _, .boolEq a b => boolEqE dom (quote dom bools bits a) (quote dom bools bits b)
  | s, .mux c a b => muxE dom s.quoteType (quote dom bools bits c)
      (quote dom bools bits a) (quote dom bools bits b)
  | _, .setw (w := w) w' a => setwE dom w w' (quote dom bools bits a)
  | _, .appCompare op (w := w) a b =>
      appCompareE op dom w (quote dom bools bits a) (quote dom bools bits b)
  | _, .appBool op a b => appBoolE op dom (quote dom bools bits a) (quote dom bools bits b)
  | _, .appBool2 f a b => appBool2E f dom (quote dom bools bits a) (quote dom bools bits b)
  | _, .slice nm start len (w := w) a => sliceE dom nm w start len (quote dom bools bits a)
  | _, .concat (m := m) (n := n) a b =>
      concatE dom m n (quote dom bools bits a) (quote dom bools bits b)
  | _, .concatLitHi k v (n := n) b => concatLitHiE dom k v n (quote dom bools bits b)
  | _, .concatLitLo (m := m) a k v => concatLitLoE dom m k v (quote dom bools bits a)
  | _, .zextMap nm k (n := n) a => zextMapE dom nm k n (quote dom bools bits a)
  | _, .sliceF nm start len (w := w) a => sliceFE dom nm w start len (quote dom bools bits a)

/-- Uniform-width embeddings of the three previous source languages. -/
def ofF (n : Nat) : FExpr → Term (.bits n)
  | .inp j => .bitsInput n j
  | .lit v => .bitsLit n v
  | .bin op a b => .binary op (ofF n a) (ofF n b)

def ofB (n : Nat) : BExpr → Term .bool
  | .inp j => .boolInput j
  | .lit b => .boolLit b
  | .compare op a b => .compare op (ofF n a) (ofF n b)
  | .boolBin op a b => .boolBinary op (ofB n a) (ofB n b)
  | .boolNot a => .boolNot (ofB n a)
  | .boolEq a b => .boolEq (ofB n a) (ofB n b)
  | .mux c a b => .mux (ofB n c) (ofB n a) (ofB n b)

def ofV (n : Nat) : VExpr → Term (.bits n)
  | .arith e => ofF n e
  | .mux c a b => .mux (ofB n c) (ofV n a) (ofV n b)

theorem quote_ofF (dom : Lean.Expr) (n : Nat) (bi vi : Nat → Lean.Expr) (e : FExpr) :
    quote dom bi vi (ofF n e) = quoteF dom n vi e := by
  induction e <;> simp_all [ofF, quote, quoteF]
theorem quote_ofB (dom : Lean.Expr) (n : Nat) (bi vi : Nat → Lean.Expr) (e : BExpr) :
    quote dom bi vi (ofB n e) = quoteB dom n bi vi e := by
  induction e <;> simp_all [ofB, quote, quoteB, quote_ofF, literalE, boolName, SType.quoteType]
theorem quote_ofV (dom : Lean.Expr) (n : Nat) (bi vi : Nat → Lean.Expr) (e : VExpr) :
    quote dom bi vi (ofV n e) = quoteV dom n bi vi e := by
  induction e <;> simp_all [ofV, quote, quoteV, quote_ofF, quote_ofB, SType.quoteType]

theorem eval_ofF (n : Nat) (bi : Nat → Bool) (vi : (j : Nat) → (w : Nat) → BitVec w) (e : FExpr) :
    eval bi vi (ofF n e) = evalFE n (fun j => vi j n) e := by
  induction e <;> simp_all [ofF, eval, evalFE]
theorem eval_ofB (n : Nat) (bi : Nat → Bool) (vi : (j : Nat) → (w : Nat) → BitVec w) (e : BExpr) :
    eval bi vi (ofB n e) = evalB n bi (fun j => vi j n) e := by
  induction e <;> simp_all [ofB, eval, evalB, eval_ofF]
theorem eval_ofV (n : Nat) (bi : Nat → Bool) (vi : (j : Nat) → (w : Nat) → BitVec w) (e : VExpr) :
    eval bi vi (ofV n e) = evalV n bi (fun j => vi j n) e := by
  induction e <;> simp_all [ofV, eval, evalV, eval_ofF, eval_ofB]

theorem wf_ofF (kb kv n : Nat) (hn : 0 < n) (e : FExpr) (he : e.WF kv n) :
    (ofF n e).WF kb kv (fun _ => n) := by
  induction e <;> simp_all [ofF, Term.WF, FExpr.WF]
theorem wf_ofB (kb kv n : Nat) (hn : 0 < n) (e : BExpr) (he : e.WF kb kv n) :
    (ofB n e).WF kb kv (fun _ => n) := by
  induction e <;> simp_all [ofB, Term.WF, BExpr.WF, wf_ofF]
theorem wf_ofV (kb kv n : Nat) (hn : 0 < n) (e : VExpr) (he : e.WF kb kv n) :
    (ofV n e).WF kb kv (fun _ => n) := by
  induction e <;> simp_all [ofV, Term.WF, VExpr.WF, wf_ofF, wf_ofB]

theorem instFVars_quote (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr)
    (bi vi : Nat → Lean.Expr) : ∀ {s} (e : Term s),
    instFVars xs d (quote dom bi vi e) =
      quote (instFVars xs d dom) (fun j => instFVars xs d (bi j)) (fun j => instFVars xs d (vi j)) e
  | _, .boolInput _ => rfl
  | _, .bitsInput _ _ => rfl
  | _, .boolLit b => by cases b <;> rfl
  | _, .bitsLit _ _ => rfl
  | _, .bitsNum _ _ => rfl
  | _, .binary op a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)))
      (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]; cases op <;> rfl
  | _, .compare op a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)))
      (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]; cases op <;> rfl
  | _, .boolBinary op a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)))
      (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]; cases op <;> rfl
  | _, .boolNot a => by
    show Lean.Expr.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)) = _
    rw [instFVars_quote]; rfl
  | _, .boolEq a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)))
      (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]; rfl
  | s, .mux c a b => by
    show Lean.Expr.app (.app (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi c)))
      (instFVars xs d (quote dom bi vi a))) (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote, instFVars_quote, instFVars_quote]; cases s <;> rfl
  | _, .setw _ a => by
    show Lean.Expr.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)) = _
    rw [instFVars_quote]; rfl
  | _, .appCompare op a b => by
    show Lean.Expr.app (.app (instFVars xs d _)
        (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a))))
      (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]
    cases op <;> simp [quote, appCompareE, appE, appLamE, appCompareBodyE, instFVars,
      bitVecE, natE, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp]
  | _, .appBool op a b => by
    show Lean.Expr.app (.app (instFVars xs d _)
        (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a))))
      (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]
    cases op <;> simp [quote, appBoolE, appE, appLamE, appBoolBodyE, instFVars,
      mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp]
  | _, .appBool2 f a b => by
    show Lean.Expr.app (.app (instFVars xs d _)
        (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a))))
      (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]
    cases f <;> simp [quote, appBool2E, appE, appLamE, appBool2BodyE, instFVars,
      mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp]
  | _, .slice nm start len a => by
    show Lean.Expr.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)) = _
    rw [instFVars_quote]
    simp [quote, sliceE, instFVars, bitVecE, natE, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp]
  | _, .concat a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)))
      (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote, instFVars_quote]
    simp [quote, concatE, instFVars, sigT, natE, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB,
      mkApp]
  | _, .concatLitHi k v b => by
    show Lean.Expr.app (instFVars xs d _) (instFVars xs d (quote dom bi vi b)) = _
    rw [instFVars_quote]
    simp [quote, concatLitHiE, litE, instFVars, sigT, bitVecE, natE, mkApp6, mkApp5, mkApp4,
      mkApp3, mkApp2, mkAppB, mkApp]
  | _, .concatLitLo a k v => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)))
      (instFVars xs d _) = _
    rw [instFVars_quote]
    simp [quote, concatLitLoE, litE, instFVars, sigT, bitVecE, natE, mkApp6, mkApp5, mkApp4,
      mkApp3, mkApp2, mkAppB, mkApp]
  | _, .zextMap nm k a => by
    show Lean.Expr.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)) = _
    rw [instFVars_quote]
    simp [quote, zextMapE, litE, instFVars, bitVecE, natE, mkApp5, mkApp4, mkApp3, mkApp2,
      mkAppB, mkApp]
  | _, .sliceF nm start len a => by
    show Lean.Expr.app (instFVars xs d _) (instFVars xs d (quote dom bi vi a)) = _
    rw [instFVars_quote]
    simp [quote, sliceFE, instFVars, bitVecE, natE, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2,
      mkAppB, mkApp]

theorem quote_congr {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bi bi' vi vi' : Nat → Lean.Expr}
    (hb : ∀ j, j < kb → bi j = bi' j) (hv : ∀ j, j < kv → vi j = vi' j) :
    ∀ {s} (e : Term s), e.WF kb kv vw → quote dom bi vi e = quote dom bi' vi' e
  | _, .boolInput j, hj => hb j hj
  | _, .bitsInput _ j, hj => hv j hj.1
  | _, .boolLit _, _ => rfl
  | _, .bitsLit _ _, _ => rfl
  | _, .bitsNum _ _, _ => rfl
  | _, .binary op a b, h => by
    obtain ⟨ha, hb'⟩ := h
    simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .compare op a b, h => by
    obtain ⟨ha, hb'⟩ := h
    simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .boolBinary op a b, h => by
    obtain ⟨ha, hb'⟩ := h
    simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .boolNot a, ha => by simp only [quote, quote_congr hb hv a ha]
  | _, .boolEq a b, h => by
    obtain ⟨ha, hb'⟩ := h
    simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | s, .mux c a b, h => by
    obtain ⟨hc, ha, hb'⟩ := h
    simp only [quote, quote_congr hb hv c hc, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .setw _ a, h => by simp only [quote, quote_congr hb hv a h.1]
  | _, .appCompare op a b, h => by
    obtain ⟨ha, hb'⟩ := h
    simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .appBool op a b, h => by
    obtain ⟨ha, hb'⟩ := h
    simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .appBool2 f a b, h => by
    obtain ⟨ha, hb'⟩ := h
    simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .slice _ _ _ a, h => by simp only [quote, quote_congr hb hv a h.1]
  | _, .concat a b, h => by
    obtain ⟨ha, hb'⟩ := h
    simp only [quote, quote_congr hb hv a ha, quote_congr hb hv b hb']
  | _, .concatLitHi _ _ b, h => by simp only [quote, quote_congr hb hv b h.1]
  | _, .concatLitLo a _ _, h => by simp only [quote, quote_congr hb hv a h.1]
  | _, .zextMap _ _ a, h => by simp only [quote, quote_congr hb hv a h.1]
  | _, .sliceF _ _ _ a, h => by simp only [quote, quote_congr hb hv a h.1]

end Tools.ShippingUnifiedSource
