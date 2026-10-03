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

/-- A slice of a BitVec value: bits `start + len - 1 … start`. -/
def sliceValue (w start len : Nat) : Value → Option Value
  | .bits k v => if h : k = w then some (.bits len (BitVec.extractLsb' start len (h ▸ v))) else none
  | _ => none

/-- Concatenation of two BitVec values: the first in the high bits. -/
def concatValue (m n : Nat) : Value → Value → Option Value
  | .bits k a, .bits l b =>
    if h : k = m ∧ l = n then some (.bits (m + n) ((h.1 ▸ a) ++ (h.2 ▸ b))) else none
  | _, _ => none

inductive Node where
  | input (id : FVarId)
  | value (v : Value)
  | binary (op : BinOp) (a b : Lean.Expr)
  | boolNot (a : Lean.Expr)
  | mux (kind : Kind) (c a b : Lean.Expr)
  | setw (w w' : Nat) (a : Lean.Expr)
  | slice (w start len : Nat) (a : Lean.Expr)
  | concat (m n : Nat) (a b : Lean.Expr)

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

/-- The domain argument of a `Signal.ap` application. -/
def appDomE : Lean.Expr → Lean.Expr
  | .app (.app (.app (.app (.app _ dom) _) _) _) _ => dom
  | e => e

/-- A two-level Bool body views as its two operators, the inner one on an
operand that is the canonical Signal-level form of the inner application. -/
def appBool2Node (f : AppBool2) (dom a b : Lean.Expr) : Node :=
  match f with
  | .andNot => .binary (.bool .band) a (boolNotE dom b)
  | .notAnd => .binary (.bool .band) (boolNotE dom a) b
  | .nor => .boolNot (boolBinE .bor dom a b)

/-- An applicative-lifted Bool-result operator views as the node of the
operator it lifts: `(BitVec.ule · ·) <$> a <*> b` IS the comparison of `a`
and `b`, pointwise. The shape is read by the shipping recogniser. -/
def appView? (e : Lean.Expr) : Option Node :=
  match appBoolOp? e with
  | some (.compare op n, a, b) => some (.binary (.compare op n) a b)
  | some (.bool op, a, b) => some (.binary (.bool op) a b)
  | some (.two f, a, b) => some (appBool2Node f (appDomE e) a b)
  | none => none

/-- A literal operand, as the Signal it is: `Signal.pure v#k`. -/
def litSigE (dom : Lean.Expr) (k v : Nat) : Lean.Expr :=
  mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom
    (mkApp (.const ``BitVec []) (natE k)) (mkApp2 (.const ``BitVec.ofNat []) (natE k) (natE v))

/-- The six-argument shapes beside the canonical operators, read by the
shipping recognisers: a concatenation — both operands Signals, or one a
literal, which views as the constant Signal of that literal — and the `<$>`
slice. -/
def concatView? (e a b : Lean.Expr) : Option Node :=
  match canonicalConcat? e with
  | some (m, k, _, _) => some (.concat m k a b)
  | none =>
    match canonicalConcatLit? e with
    | some (true, k, v, w, dom, _) => some (.concat k w (litSigE dom k v) b)
    | some (false, k, v, w, dom, _) => some (.concat w k a (litSigE dom k v))
    | none =>
      match canonicalSliceF? e with
      | some (ws, start, len, _) => some (.slice ws start len b)
      | none => none

/-- The shapes read by the shipping recognisers of later arms: the canonical
slice map, then the applicative-lifted operators. -/
def tailView? (e : Lean.Expr) : Option Node :=
  match canonicalSlice? e with
  | some (ws, start, len, a) => some (.slice ws start len a)
  | none =>
    match canonicalZextMap? e with
    | some (ws, k, a) => some (.setw ws (k + ws) a)
    | none => appView? e

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
      | _, _, _ => concatView? e a b
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
  | e => tailView? e

/-- The source function of each linked child declaration, on packed values.
`none` outside the child's typed domain. -/
class ChildSem where
  childSem : Name → List Value → Option Value

/-- By default no declaration has a linked meaning: the flat source domain. -/
instance (priority := low) noChildSem : ChildSem := ⟨fun _ _ => none⟩

set_option linter.unusedSectionVars false

variable [ChildSem]

/-- A single recursive relation allows comparison operands to contain vector
muxes whose conditions in turn contain comparisons and arbitrary Bool logic.
An instance call (an application the pure view does not recognize) means
the linked child's source function of its arguments' meanings. -/
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
  | slice {e w start len a va v} : view e = some (.slice w start len a) →
      Meaning inputs a va → sliceValue w start len va = some v → Meaning inputs e v
  | concat {e m n a b va vb v} : view e = some (.concat m n a b) →
      Meaning inputs a va → Meaning inputs b vb → concatValue m n va vb = some v →
      Meaning inputs e v
  | inst {e mn lvls dom args vs v} : view e = none → e.getAppFn = .const mn lvls →
      instSpineArgs e = dom :: args → vs.length = args.length →
      (∀ i (ha : i < args.length) (hv : i < vs.length),
        Meaning inputs (args[i]'ha) (vs[i]'hv)) →
      ChildSem.childSem mn vs = some v → Meaning inputs e v

/-- Even across the two sorts and different widths, a recorded expression has
one source value. This is the key cache-insertion obligation. -/
theorem Meaning.deterministic {inputs e a b} (ha : Meaning inputs e a) (hb : Meaning inputs e b) : a = b := by
  induction ha generalizing b with
  | inst hview hfn hsp hlen hargs hsem ih =>
    cases hb with
    | inst hview' hfn' hsp' hlen' hargs' hsem' =>
      have hc := Lean.Expr.const.inj (hfn.symm.trans hfn')
      have hs := List.cons.inj (hsp.symm.trans hsp')
      obtain ⟨hmn, -⟩ := hc
      obtain ⟨-, hargsEq⟩ := hs
      subst hmn hargsEq
      have hvs := List.ext_getElem (hlen.trans hlen'.symm) (fun i h1 h2 =>
        ih i (by rw [← hlen]; exact h1) h1 (hargs' i (by rw [← hlen]; exact h1) h2))
      subst hvs
      exact Option.some.inj (hsem.symm.trans hsem')
    | _ => simp_all
  | _ => cases hb <;> grind

open Tools.ShippingBoolLiteralSoundness

theorem view_boolLit (dom : Lean.Expr) (b : Bool) :
    view (literalE dom b) = some (.value (.bool b)) := by cases b <;> rfl

theorem view_bitsLit (dom : Lean.Expr) (n v : Nat) (hv : v < 2 ^ n) (vi : Nat → Lean.Expr) :
    view (quoteF dom n vi (.lit v)) = some (.value (.bits n (BitVec.ofNat n v))) := by
  change (bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v))).map _ = _
  rw [litValue_natE n v hv]; rfl

theorem view_bitsNum (dom : Lean.Expr) (n v : Nat) (hv : v < 2 ^ n) :
    view (numSigE dom n v) = some (.value (.bits n (BitVec.ofNat n v))) := by
  change (bitVecLitValue? (numLitE n v)).map _ = _
  rw [litValue_numLitE n v hv]; rfl

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
        | _, _, _ => concatView? (binE dom n op a b) a b) := by
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

theorem appBoolBody?_compare (op : SignalCompareKind) (n : Nat) :
    appBoolBody? (bitVecE n) (appCompareBodyE op n) = some (.compare op n) := by
  cases op <;> simp [appBoolBody?, appCompareBodyE, bitVecE, mkApp4, mkApp3, mkApp2, mkAppB,
    mkApp, bitVecEqualityWidth?, canonicalNatLitValue?_natE]

theorem appBoolBody?_bool (op : SignalBoolBinKind) :
    appBoolBody? (.const ``Bool []) (appBoolBodyE op) = some (.bool op) := by
  cases op <;> rfl

theorem appBoolOp?_appE (dom ty body a b : Lean.Expr) :
    appBoolOp? (appE dom ty body a b) = (appBoolBody? ty body).map (·, a, b) := rfl

theorem appBoolOp?_appCompareE (dom a b : Lean.Expr) (n : Nat) (op : SignalCompareKind) :
    appBoolOp? (appCompareE op dom n a b) = some (.compare op n, a, b) := by
  rw [appCompareE, appBoolOp?_appE, appBoolBody?_compare]; rfl

theorem appBoolOp?_appBoolE (dom a b : Lean.Expr) (op : SignalBoolBinKind) :
    appBoolOp? (appBoolE op dom a b) = some (.bool op, a, b) := by
  rw [appBoolE, appBoolOp?_appE, appBoolBody?_bool]; rfl

theorem view_appE (dom ty body a b : Lean.Expr) :
    view (appE dom ty body a b) = appView? (appE dom ty body a b) := rfl

theorem appBoolBody?_two (f : AppBool2) :
    appBoolBody? (.const ``Bool []) (appBool2BodyE f) = some (.two f) := by
  cases f <;> rfl

theorem appBoolOp?_appBool2E (dom a b : Lean.Expr) (f : AppBool2) :
    appBoolOp? (appBool2E f dom a b) = some (.two f, a, b) := by
  rw [appBool2E, appBoolOp?_appE, appBoolBody?_two]; rfl

theorem appDomE_appE (dom ty body a b : Lean.Expr) : appDomE (appE dom ty body a b) = dom := rfl

theorem canonicalSlice?_sliceE (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr)
    {w start len : Nat} (hlen : 0 < len) (hr : start + len ≤ w) :
    canonicalSlice? (sliceE dom nm w start len a) = some (w, start, len, a) := by
  simp only [sliceE, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, bitVecE,
    canonicalSlice?, canonicalNatLitValue?_natE]
  simp [hlen, hr]

theorem view_slice (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr)
    {w start len : Nat} (hlen : 0 < len) (hr : start + len ≤ w) :
    view (sliceE dom nm w start len a) = some (.slice w start len a) := by
  have fall : view (sliceE dom nm w start len a) = tailView? (sliceE dom nm w start len a) := rfl
  rw [fall, tailView?, canonicalSlice?_sliceE dom nm a hlen hr]

theorem canonicalConcat?_concatE (dom a b : Lean.Expr) {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    canonicalConcat? (concatE dom m n a b) = some (m, n, a, b) := by
  simp only [concatE, sigT, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp,
    canonicalConcat?, canonicalNatLitValue?_natE]
  simp [hm, hn]

set_option maxHeartbeats 1000000 in
/-- A concatenation is read by the generic operator arm's fall-through. -/
theorem view_concatE_fall (dom a b : Lean.Expr) (m n : Nat) :
    view (concatE dom m n a b) = concatView? (concatE dom m n a b) a b := rfl

theorem view_concat (dom a b : Lean.Expr) {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    view (concatE dom m n a b) = some (.concat m n a b) := by
  rw [view_concatE_fall, concatView?, canonicalConcat?_concatE dom a b hm hn]

set_option maxHeartbeats 1000000 in
theorem canonicalConcat?_hiE (dom b : Lean.Expr) (k v n : Nat) :
    canonicalConcat? (concatLitHiE dom k v n b) = none := rfl

set_option maxHeartbeats 1000000 in
theorem canonicalConcat?_loE (dom a : Lean.Expr) (m k v : Nat) :
    canonicalConcat? (concatLitLoE dom m k v a) = none := rfl

theorem canonicalConcatLit?_hiE (dom b : Lean.Expr) {k v n : Nat} (hk : 0 < k) (hv : v < 2 ^ k)
    (hn : 0 < n) :
    canonicalConcatLit? (concatLitHiE dom k v n b) = some (true, k, v, n, dom, b) := by
  simp only [concatLitHiE, litE, sigT, bitVecE, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB,
    mkApp, canonicalConcatLit?, canonicalNatLitValue?_natE]
  simp [hk, hv, hn]

theorem canonicalConcatLit?_loE (dom a : Lean.Expr) {m k v : Nat} (hk : 0 < k) (hv : v < 2 ^ k)
    (hm : 0 < m) :
    canonicalConcatLit? (concatLitLoE dom m k v a) = some (false, k, v, m, dom, a) := by
  simp only [concatLitLoE, litE, sigT, bitVecE, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB,
    mkApp, canonicalConcatLit?, canonicalNatLitValue?_natE]
  simp [hk, hv, hm]

set_option maxHeartbeats 1000000 in
theorem view_hiE_fall (dom b : Lean.Expr) (k v n : Nat) :
    view (concatLitHiE dom k v n b) =
      concatView? (concatLitHiE dom k v n b) (litE k v) b := rfl

set_option maxHeartbeats 1000000 in
theorem view_loE_fall (dom a : Lean.Expr) (m k v : Nat) :
    view (concatLitLoE dom m k v a) =
      concatView? (concatLitLoE dom m k v a) a (litE k v) := rfl

theorem view_concatLitHi (dom b : Lean.Expr) {k v n : Nat} (hk : 0 < k) (hv : v < 2 ^ k)
    (hn : 0 < n) :
    view (concatLitHiE dom k v n b) = some (.concat k n (litSigE dom k v) b) := by
  rw [view_hiE_fall, concatView?, canonicalConcat?_hiE, canonicalConcatLit?_hiE dom b hk hv hn]

theorem view_concatLitLo (dom a : Lean.Expr) {m k v : Nat} (hk : 0 < k) (hv : v < 2 ^ k)
    (hm : 0 < m) :
    view (concatLitLoE dom m k v a) = some (.concat m k a (litSigE dom k v)) := by
  rw [view_loE_fall, concatView?, canonicalConcat?_loE, canonicalConcatLit?_loE dom a hk hv hm]

theorem sixArgShape?_concatE (dom a b : Lean.Expr) {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    sixArgShape? (concatE dom m n a b) = some (m + n, some m, some n) := by
  rw [sixArgShape?, canonicalConcat?_concatE dom a b hm hn]

theorem sixArgShape?_hiE (dom b : Lean.Expr) {k v n : Nat} (hk : 0 < k) (hv : v < 2 ^ k)
    (hn : 0 < n) : sixArgShape? (concatLitHiE dom k v n b) = some (k + n, none, some n) := by
  rw [sixArgShape?, canonicalConcat?_hiE, canonicalConcatLit?_hiE dom b hk hv hn]

theorem sixArgShape?_loE (dom a : Lean.Expr) {m k v : Nat} (hk : 0 < k) (hv : v < 2 ^ k)
    (hm : 0 < m) : sixArgShape? (concatLitLoE dom m k v a) = some (m + k, some m, none) := by
  rw [sixArgShape?, canonicalConcat?_loE, canonicalConcatLit?_loE dom a hk hv hm]

/-! ### The zero-extending map and the `<$>` slice -/

theorem canonicalZextMap?_zextMapE (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr)
    {k n : Nat} (hk : 0 < k) (hn : 0 < n) :
    canonicalZextMap? (zextMapE dom nm k n a) = some (n, k, a) := by
  simp only [zextMapE, litE, bitVecE, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp,
    canonicalZextMap?, canonicalNatLitValue?_natE]
  simp [hk, hn]

set_option maxHeartbeats 1000000 in
theorem view_zextMapE_fall (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr) (k n : Nat) :
    view (zextMapE dom nm k n a) = tailView? (zextMapE dom nm k n a) := rfl

set_option maxHeartbeats 1000000 in
theorem canonicalSlice?_zextMapE (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr) (k n : Nat) :
    canonicalSlice? (zextMapE dom nm k n a) = none := rfl

theorem view_zextMap (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr) {k n : Nat}
    (hk : 0 < k) (hn : 0 < n) :
    view (zextMapE dom nm k n a) = some (.setw n (k + n) a) := by
  rw [view_zextMapE_fall, tailView?, canonicalSlice?_zextMapE,
    canonicalZextMap?_zextMapE dom nm a hk hn]

/-- A literal zero prefix is the zero-extension. -/
theorem setWidth_eq_zero_append (k : Nat) {n : Nat} (x : BitVec n) :
    BitVec.setWidth (k + n) x = BitVec.append (BitVec.ofNat k 0) x := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toNat < 2 ^ (k + n) :=
    Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  simp [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.mod_eq_of_lt hx]

theorem canonicalSliceF?_sliceFE (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr)
    {w start len : Nat} (hlen : 0 < len) (hr : start + len ≤ w) :
    canonicalSliceF? (sliceFE dom nm w start len a) = some (w, start, len, a) := by
  simp only [sliceFE, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, bitVecE,
    canonicalSliceF?, canonicalNatLitValue?_natE]
  simp [hlen, hr]

set_option maxHeartbeats 1000000 in
theorem canonicalConcat?_sliceFE (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr)
    (w start len : Nat) : canonicalConcat? (sliceFE dom nm w start len a) = none := rfl

set_option maxHeartbeats 1000000 in
theorem canonicalConcatLit?_sliceFE (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr)
    (w start len : Nat) : canonicalConcatLit? (sliceFE dom nm w start len a) = none := rfl

theorem sixArgShape?_sliceFE (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr)
    {w start len : Nat} (hlen : 0 < len) (hr : start + len ≤ w) :
    sixArgShape? (sliceFE dom nm w start len a) = some (len, none, some w) := by
  rw [sixArgShape?, canonicalConcat?_sliceFE, canonicalConcatLit?_sliceFE,
    canonicalSliceF?_sliceFE dom nm a hlen hr]

/-- The lambda of the `<$>` slice, the fifth argument of the application. -/
def sliceLamE (nm : Lean.Name) (w start len : Nat) : Lean.Expr :=
  .lam nm (bitVecE w)
    (mkApp4 (.const ``BitVec.extractLsb' []) (natE w) (natE start) (natE len) (.bvar 0))
    .default

set_option maxHeartbeats 1000000 in
theorem view_sliceFE_fall (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr)
    (w start len : Nat) :
    view (sliceFE dom nm w start len a) =
      concatView? (sliceFE dom nm w start len a) (sliceLamE nm w start len) a := rfl

theorem view_sliceF (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr)
    {w start len : Nat} (hlen : 0 < len) (hr : start + len ≤ w) :
    view (sliceFE dom nm w start len a) = some (.slice w start len a) := by
  rw [view_sliceFE_fall, concatView?, canonicalConcat?_sliceFE, canonicalConcatLit?_sliceFE,
    canonicalSliceF?_sliceFE dom nm a hlen hr]

/-- The literal's constant Signal means the literal. -/
theorem meaning_litSigE {inputs : FVarId → Option Value} (dom : Lean.Expr) {k v : Nat}
    (hv : v < 2 ^ k) : Meaning inputs (litSigE dom k v) (.bits k (BitVec.ofNat k v)) :=
  .value (view_bitsLit dom k v hv (fun _ => dom))

theorem view_appCompare (dom a b : Lean.Expr) (n : Nat) (op : SignalCompareKind) :
    view (appCompareE op dom n a b) = some (.binary (.compare op n) a b) := by
  rw [appCompareE, view_appE]
  show appView? (appCompareE op dom n a b) = _
  simp [appView?, appBoolOp?_appCompareE]

theorem view_appBool (dom a b : Lean.Expr) (op : SignalBoolBinKind) :
    view (appBoolE op dom a b) = some (.binary (.bool op) a b) := by
  rw [appBoolE, view_appE]
  show appView? (appBoolE op dom a b) = _
  simp [appView?, appBoolOp?_appBoolE]

theorem view_appBool2 (dom a b : Lean.Expr) (f : AppBool2) :
    view (appBool2E f dom a b) = some (appBool2Node f dom a b) := by
  rw [appBool2E, view_appE]
  show appView? (appBool2E f dom a b) = _
  have hd : appDomE (appBool2E f dom a b) = dom := appDomE_appE ..
  simp [appView?, appBoolOp?_appBool2E, hd]

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

/-- Full source/library connection for the recursive domain over ARBITRARY
leaf expressions: whatever the leaves mean, the quoted cone means its
evaluation at those meanings. This says what quoted sources mean, not that
the compiler already preserves them. -/
theorem meaning_quote_leaves {inputs : FVarId → Option Value} {dom : Lean.Expr} {kb kv : Nat}
    {vw : Nat → Nat} {bE vE : Nat → Lean.Expr} {bools : Nat → Bool}
    {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j)))) :
    ∀ {s} (e : Term s), e.WF kb kv vw →
      Meaning inputs (quote dom bE vE e) (pack s (eval bools bits e))
  | _, .boolInput j, hj => hb j hj
  | _, .bitsInput w j, hj => by
    cases hj.2.1
    exact hv j hj.1
  | _, .boolLit b, _ => .value (view_boolLit dom b)
  | _, .bitsLit w v, hv => .value (view_bitsLit dom w v hv.1 _)
  | _, .bitsNum w v, hv => .value (view_bitsNum dom w v hv.1)
  | _, .binary op (w := w) a b, ⟨ha, hb'⟩ => by
    apply Meaning.binary (view_binary dom _ _ w op) (meaning_quote_leaves hb hv a ha) (meaning_quote_leaves hb hv b hb')
    simp [BinOp.run, pack, eval]
  | _, .compare op (w := w) a b, ⟨ha, hb'⟩ => by
    apply Meaning.binary (view_compare dom _ _ w op) (meaning_quote_leaves hb hv a ha) (meaning_quote_leaves hb hv b hb')
    simp [BinOp.run, pack, eval]
  | _, .boolBinary op a b, ⟨ha, hb'⟩ =>
    .binary (view_boolBinary dom _ _ op) (meaning_quote_leaves hb hv a ha) (meaning_quote_leaves hb hv b hb') rfl
  | _, .boolNot a, ha => .boolNot (view_boolNot dom _) (meaning_quote_leaves hb hv a ha)
  | _, .boolEq a b, ⟨ha, hb'⟩ =>
    .binary (view_boolEq dom _ _) (meaning_quote_leaves hb hv a ha) (meaning_quote_leaves hb hv b hb') rfl
  | s, .mux c a b, ⟨hc, ha, hb'⟩ => by
    apply Meaning.mux (view_mux dom _ _ _ s) (meaning_quote_leaves hb hv c hc)
      (meaning_quote_leaves hb hv a ha) (meaning_quote_leaves hb hv b hb')
    cases s <;> cases h : eval bools bits c <;> simp [muxValue, pack, Value.kind, kindOf, eval, h]
  | _, .setw (w := w) w' a, h => by
    apply Meaning.setw (view_setw dom _ w w') (meaning_quote_leaves hb hv a h.1)
    simp [setwValue, pack, eval]
  | _, .appCompare op (w := w) a b, ⟨ha, hb'⟩ => by
    apply Meaning.binary (view_appCompare dom _ _ w op) (meaning_quote_leaves hb hv a ha)
      (meaning_quote_leaves hb hv b hb')
    simp [BinOp.run, pack, eval]
  | _, .appBool op a b, ⟨ha, hb'⟩ =>
    .binary (view_appBool dom _ _ op) (meaning_quote_leaves hb hv a ha)
      (meaning_quote_leaves hb hv b hb') rfl
  | _, .appBool2 f a b, ⟨ha, hb'⟩ => by
    have ma := meaning_quote_leaves (dom := dom) hb hv a ha
    have mb := meaning_quote_leaves (dom := dom) hb hv b hb'
    cases f
    · exact .binary (view_appBool2 dom _ _ .andNot) ma (.boolNot (view_boolNot dom _) mb) rfl
    · exact .binary (view_appBool2 dom _ _ .notAnd) (.boolNot (view_boolNot dom _) ma) mb rfl
    · exact .boolNot (view_appBool2 dom _ _ .nor)
        (.binary (view_boolBinary dom _ _ .bor) ma mb rfl)
  | _, .slice nm start len (w := w) a, ⟨ha, hlen, hr⟩ => by
    apply Meaning.slice (view_slice dom nm _ hlen hr) (meaning_quote_leaves hb hv a ha)
    simp [sliceValue, pack, eval]
  | _, .concat a b, h => by
    obtain ⟨ha, hb'⟩ := h
    apply Meaning.concat (view_concat dom _ _ (a.wf_pos ha) (b.wf_pos hb'))
      (meaning_quote_leaves hb hv a ha) (meaning_quote_leaves hb hv b hb')
    simp [concatValue, pack, eval]
  | _, .concatLitHi k v b, h => by
    obtain ⟨hb', hk, hlt⟩ := h
    apply Meaning.concat (view_concatLitHi dom _ hk hlt (b.wf_pos hb'))
      (meaning_litSigE dom hlt) (meaning_quote_leaves hb hv b hb')
    simp [concatValue, pack, eval]
  | _, .concatLitLo a k v, h => by
    obtain ⟨ha, hk, hlt⟩ := h
    apply Meaning.concat (view_concatLitLo dom _ hk hlt (a.wf_pos ha))
      (meaning_quote_leaves hb hv a ha) (meaning_litSigE dom hlt)
    simp [concatValue, pack, eval]
  | _, .zextMap nm k a, h => by
    obtain ⟨ha, hk⟩ := h
    apply Meaning.setw (view_zextMap dom nm _ hk (a.wf_pos ha)) (meaning_quote_leaves hb hv a ha)
    simp [setwValue, pack, eval, setWidth_eq_zero_append]
  | _, .sliceF nm start len (w := w) a, ⟨ha, hlen, hr⟩ => by
    apply Meaning.slice (view_sliceF dom nm _ hlen hr) (meaning_quote_leaves hb hv a ha)
    simp [sliceValue, pack, eval]

/-- The input-binder instance: leaves are prepared free variables. -/
theorem meaning_quote {inputs : FVarId → Option Value} {dom : Lean.Expr} {kb kv : Nat}
    {vw : Nat → Nat} {bi vi : Nat → FVarId} {bools : Nat → Bool}
    {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j))))
    {s} (e : Term s) (wf : e.WF kb kv vw) :
    Meaning inputs (quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e)
      (pack s (eval bools bits e)) :=
  meaning_quote_leaves (fun j hj => .input rfl (hb j hj))
    (fun j hj => .input rfl (hv j hj)) e wf

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
