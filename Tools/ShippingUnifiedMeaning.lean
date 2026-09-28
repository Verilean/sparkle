import Tools.ShippingUnifiedSource

/-! Deterministic source meanings for the actual Lean expressions stored in
shipping cache records. Bool and BitVec share one relation; their widths cannot
be confused by a cache hit. This is not yet a recursive compiler contract. -/
namespace Tools.ShippingUnifiedMeaning
open Lean Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingScalarSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingMuxTypeSoundness

inductive Kind where
  | bool
  | bits (n : Nat)
  deriving DecidableEq, BEq

def Kind.width : Kind → Nat
  | .bool => 1
  | .bits n => n

inductive Value where
  | bool (b : Bool)
  | bits (n : Nat) (v : BitVec n)

def Value.kind : Value → Kind
  | .bool _ => .bool
  | .bits n _ => .bits n

def Value.toNat : Value → Nat
  | .bool b => encodeBool b
  | .bits _ v => v.toNat

theorem Value.bounded (v : Value) : v.toNat < 2 ^ v.kind.width := by
  cases v with
  | bool b => exact encodeBool_lt b
  | bits n v => exact v.isLt

def pack : (s : SType) → s.Type → Value
  | .bool, b => .bool b
  | .bits w, v => .bits w v

inductive BinOp where
  | bits (op : Binary) (n : Nat)
  | compare (op : SignalCompareKind) (n : Nat)
  | bool (op : SignalBoolBinKind)
  | boolEq

def BinOp.run : BinOp → Value → Value → Option Value
  | .bits op n, .bits k a, .bits l b =>
    if k == n && l == n then some (.bits n (op.apply (BitVec.ofNat n a.toNat) (BitVec.ofNat n b.toNat))) else none
  | .compare op n, .bits k a, .bits l b =>
    if k == n && l == n then some (.bool (compareValue op (BitVec.ofNat n a.toNat) (BitVec.ofNat n b.toNat))) else none
  | .bool op, .bool a, .bool b => some (.bool (boolBinValue op a b))
  | .boolEq, .bool a, .bool b => some (.bool (a == b))
  | _, _, _ => none

def muxValue (kind : Kind) : Value → Value → Value → Option Value
  | .bool c, a, b => if a.kind = kind ∧ b.kind = kind then some (if c then a else b) else none
  | _, _, _ => none

/-- Width change on a BitVec value: zero-extension or truncation. -/
def setwValue (w w' : Nat) : Value → Option Value
  | .bits k v => if h : k = w then some (.bits w' (BitVec.setWidth w' (h ▸ v))) else none
  | _ => none

inductive Node where
  | input (id : FVarId)
  | value (v : Value)
  | binary (op : BinOp) (a b : Lean.Expr)
  | boolNot (a : Lean.Expr)
  | mux (kind : Kind) (c a b : Lean.Expr)
  | setw (w w' : Nat) (a : Lean.Expr)

def binaryOfName? : Name → Option Binary
  | ``HAdd.hAdd => some .add
  | ``HSub.hSub => some .sub
  | ``HMul.hMul => some .mul
  | ``HAnd.hAnd => some .and
  | ``HOr.hOr => some .or
  | ``HXor.hXor => some .xor
  | ``HShiftLeft.hShiftLeft => some .shl
  | ``HShiftRight.hShiftRight => some .shr
  | _ => none

def orderedOfName? : Name → Option SignalCompareKind
  | ``Sparkle.Core.Signal.Signal.ult => some .ult
  | ``Sparkle.Core.Signal.Signal.ule => some .ule
  | ``Sparkle.Core.Signal.Signal.slt => some .slt
  | ``Sparkle.Core.Signal.Signal.sle => some .sle
  | _ => none

/-- Pure syntax view. Operator instances and literal widths are checked using
shipping recognizers; no MetaM type query or runtime environment oracle. -/
def view : Lean.Expr → Option Node
  | .fvar id => some (.input id)
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
      (.const ``Bool.true _) => some (.value (.bool true))
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) (.const ``Bool _))
      (.const ``Bool.false _) => some (.value (.bool false))
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) _) lit =>
      (bitVecLitValue? lit).map fun (n, v) => .value (.bits n (BitVec.ofNat n v))
  | e@(.app (.app (.app (.app (.app (.app (.const m _) _) _) _) inst) a) b) =>
    match signalBoolBinKind? m inst with
    | some op => some (.binary (.bool op) a b)
    | none => match binaryOfName? m, canonicalSignalBinKinds m e.getAppArgs,
        canonicalSignalBitVecWidth e.getAppArgs with
      | some op, some (true, true), some n => some (.binary (.bits op n) a b)
      | _, _, _ => none
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.beq _) ty) _) inst) a) b =>
    if isBoolEquality ty inst then some (.binary .boolEq a b) else
      ((bitVecEqualityWidth? ty inst).bind canonicalNatLitValue?).map fun n => .binary (.compare .eq n) a b
  | e@(.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.mux _) _) _) c) a) b) =>
    match canonicalMuxType? e with
    | some .bit => some (Node.mux .bool c a b)
    | some (.bitVector n) => some (Node.mux (.bits n) c a b)
    | _ => none
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) _)
      (.app (.const ``BitVec _) wsE)) (.app (.const ``BitVec _) wtE))
      (.app (.app (.const ``BitVec.setWidth _) wsE') wtE')) a => do
    let ws ← canonicalNatLitValue? wsE
    let wt ← canonicalNatLitValue? wtE
    let ws' ← canonicalNatLitValue? wsE'
    let wt' ← canonicalNatLitValue? wtE'
    if ws' == ws && wt' == wt then pure (.setw ws wt a) else none
  | .app (.app (.app (.app (.const m _) _) w) a) b => do
    let op ← orderedOfName? m
    let n ← canonicalNatLitValue? w
    pure (.binary (.compare op n) a b)
  | .app (.app (.app (.const ``Complement.complement _) _)
      (.app (.const ``Sparkle.Core.Signal.instComplementSignalBool _) _)) a => some (.boolNot a)
  | _ => none

/-- A single recursive relation allows comparison operands to contain vector
muxes whose conditions in turn contain comparisons and arbitrary Bool logic. -/
inductive Meaning (inputs : FVarId → Option Value) : Lean.Expr → Value → Prop where
  | input {e id v} : view e = some (.input id) → inputs id = some v → Meaning inputs e v
  | value {e v} : view e = some (.value v) → Meaning inputs e v
  | binary {e op a b va vb v} : view e = some (.binary op a b) →
      Meaning inputs a va → Meaning inputs b vb → op.run va vb = some v → Meaning inputs e v
  | boolNot {e a b} : view e = some (.boolNot a) → Meaning inputs a (.bool b) → Meaning inputs e (.bool (!b))
  | mux {e kind c a b vc va vb v} : view e = some (.mux kind c a b) →
      Meaning inputs c vc → Meaning inputs a va → Meaning inputs b vb →
      muxValue kind vc va vb = some v → Meaning inputs e v
  | setw {e w w' a va v} : view e = some (.setw w w' a) →
      Meaning inputs a va → setwValue w w' va = some v → Meaning inputs e v

/-- Even across the two sorts and different widths, a recorded expression has
one source value. This is the key cache-insertion obligation. -/
theorem Meaning.deterministic {inputs e a b} (ha : Meaning inputs e a) (hb : Meaning inputs e b) : a = b := by
  induction ha generalizing b <;> cases hb <;> grind

open Tools.ShippingBoolLiteralSoundness

theorem view_boolLit (dom : Lean.Expr) (b : Bool) :
    view (literalE dom b) = some (.value (.bool b)) := by cases b <;> rfl

theorem view_bitsLit (dom : Lean.Expr) (n v : Nat) (hv : v < 2 ^ n) (vi : Nat → Lean.Expr) :
    view (quoteF dom n vi (.lit v)) = some (.value (.bits n (BitVec.ofNat n v))) := by
  change (bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v))).map _ = _
  rw [litValue_natE n v hv]; rfl

theorem view_binary (dom a b : Lean.Expr) (n : Nat) (op : Binary) :
    view (binE dom n op a b) = some (.binary (.bits op n) a b) := by
  have kinds := (op_checks op dom a b n).2.2.1
  have width := (op_checks op dom a b n).2.2.2.1
  have bool : signalBoolBinKind? (binMethod op) (mkApp2 (.const (binInst op) []) dom (natE n)) = none := by
    cases op <;> rfl
  have step : view (binE dom n op a b) =
      (match signalBoolBinKind? (binMethod op) (mkApp2 (.const (binInst op) []) dom (natE n)) with
      | some k => some (.binary (.bool k) a b)
      | none => match binaryOfName? (binMethod op), canonicalSignalBinKinds (binMethod op) (binE dom n op a b).getAppArgs,
          canonicalSignalBitVecWidth (binE dom n op a b).getAppArgs with
        | some k, some (true, true), some n => some (.binary (.bits k n) a b)
        | _, _, _ => none) := by
    simp only [binE, mkApp6, mkApp4, mkApp2, mkAppB, mkApp, view]
  rw [step, bool, kinds, width]
  cases op <;> rfl

theorem view_compare (dom a b : Lean.Expr) (n : Nat) (op : SignalCompareKind) :
    view (compareE op dom n a b) = some (.binary (.compare op n) a b) := by
  cases op <;> simp [view, compareE, compareName, mkApp2, mkApp3, mkAppB, mkApp,
    orderedOfName?, isBoolEquality, bitVecEqualityWidth?, canonicalNatLitValue?_natE]

theorem view_boolBinary (dom a b : Lean.Expr) (op : SignalBoolBinKind) :
    view (boolBinE op dom a b) = some (.binary (.bool op) a b) := by cases op <;> rfl

theorem view_boolNot (dom a : Lean.Expr) : view (boolNotE dom a) = some (.boolNot a) := rfl

theorem view_setw (dom a : Lean.Expr) (w w' : Nat) :
    view (setwE dom w w' a) = some (.setw w w' a) := by
  change (do
    let ws ← canonicalNatLitValue? (natE w)
    let wt ← canonicalNatLitValue? (natE w')
    let ws' ← canonicalNatLitValue? (natE w)
    let wt' ← canonicalNatLitValue? (natE w')
    if ws' == ws && wt' == wt then pure (Node.setw ws wt a) else none) = _
  rw [canonicalNatLitValue?_natE, canonicalNatLitValue?_natE]
  simp

theorem view_boolEq (dom a b : Lean.Expr) : view (boolEqE dom a b) = some (.binary .boolEq a b) := rfl

def kindOf : SType → Kind
  | .bool => .bool
  | .bits w => .bits w

theorem pack_kind (s : SType) (v : s.Type) : (pack s v).kind = kindOf s := by cases s <;> rfl

theorem view_mux (dom c a b : Lean.Expr) (s : SType) :
    view (muxE dom s.quoteType c a b) = some (.mux (kindOf s) c a b) := by
  cases s with
  | bool => rfl
  | bits w =>
    change (match canonicalMuxType? (muxE dom (bitVecE w) c a b) with
      | some .bit => some (Node.mux .bool c a b)
      | some (.bitVector n) => some (Node.mux (.bits n) c a b)
      | _ => none) = _
    rw [canonicalMuxType?_bitVec]; rfl

/-- Full source/library connection for the new recursive domain. This says
what quoted sources mean, not that the compiler already preserves them. -/
theorem meaning_quote {inputs : FVarId → Option Value} {dom : Lean.Expr} {kb kv : Nat}
    {vw : Nat → Nat} {bi vi : Nat → FVarId} {bools : Nat → Bool}
    {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j)))) :
    ∀ {s} (e : Term s), e.WF kb kv vw →
      Meaning inputs (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e)
        (pack s (eval bools bits e))
  | _, .boolInput j, hj => .input rfl (hb j hj)
  | _, .bitsInput w j, hj => by
    cases hj.2.1
    exact .input rfl (hv j hj.1)
  | _, .boolLit b, _ => .value (view_boolLit dom b)
  | _, .bitsLit w v, hv => .value (view_bitsLit dom w v hv.1 _)
  | _, .binary op (w := w) a b, ⟨ha, hb'⟩ => by
    apply Meaning.binary (view_binary dom _ _ w op) (meaning_quote hb hv a ha) (meaning_quote hb hv b hb')
    simp [BinOp.run, pack, eval]
  | _, .compare op (w := w) a b, ⟨ha, hb'⟩ => by
    apply Meaning.binary (view_compare dom _ _ w op) (meaning_quote hb hv a ha) (meaning_quote hb hv b hb')
    simp [BinOp.run, pack, eval]
  | _, .boolBinary op a b, ⟨ha, hb'⟩ =>
    .binary (view_boolBinary dom _ _ op) (meaning_quote hb hv a ha) (meaning_quote hb hv b hb') rfl
  | _, .boolNot a, ha => .boolNot (view_boolNot dom _) (meaning_quote hb hv a ha)
  | _, .boolEq a b, ⟨ha, hb'⟩ =>
    .binary (view_boolEq dom _ _) (meaning_quote hb hv a ha) (meaning_quote hb hv b hb') rfl
  | s, .mux c a b, ⟨hc, ha, hb'⟩ => by
    apply Meaning.mux (view_mux dom _ _ _ s) (meaning_quote hb hv c hc)
      (meaning_quote hb hv a ha) (meaning_quote hb hv b hb')
    cases s <;> cases h : eval bools bits c <;> simp [muxValue, pack, Value.kind, kindOf, eval, h]
  | _, .setw (w := w) w' a, h => by
    apply Meaning.setw (view_setw dom _ w w') (meaning_quote hb hv a h.1)
    simp [setwValue, pack, eval]

theorem bool_bits_disjoint {inputs e b n v}
    (hb : Meaning inputs e (.bool b)) (hv : Meaning inputs e (.bits n v)) : False := by
  have impossible := hb.deterministic hv
  cases impossible

/-- Adapter for the actual mixed input preparation already used at the entry. -/
def inputValues (bools : BoolValuation) (bits : Tools.ShippingTranslateSoundness.Valuation)
    (id : FVarId) : Option Value :=
  match bools id with
  | some b => some (.bool b)
  | none => (bits id).map fun ⟨n, v⟩ => .bits n v

theorem inputValues_bool {bools bits id b} (h : bools id = some b) :
    inputValues bools bits id = some (.bool b) := by simp [inputValues, h]

theorem inputValues_bits {bools bits id n v}
    (separate : Tools.ShippingMixedInvariant.Separate bools bits) (h : bits id = some ⟨n, v⟩) :
    inputValues bools bits id = some (.bits n v) := by
  cases hb : bools id with
  | none => simp [inputValues, hb, h]
  | some b => have impossible := separate id b hb; rw [h] at impossible; cases impossible

theorem meaning_quote_mixed {ρ β dom kb kv} {vw : Nat → Nat} {bi vi : Nat → FVarId}
    {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (separate : Tools.ShippingMixedInvariant.Separate ρ β)
    (hb : ∀ j, j < kb → ρ (bi j) = some (bools j))
    (hv : ∀ j, j < kv → β (vi j) = some ⟨vw j, bits j (vw j)⟩)
    {s} (e : Term s) (wf : e.WF kb kv vw) :
    Meaning (inputValues ρ β) (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e)
      (pack s (eval bools bits e)) :=
  meaning_quote (fun j hj => inputValues_bool (hb j hj))
    (fun j hj => inputValues_bits separate (hv j hj)) e wf

end Tools.ShippingUnifiedMeaning
