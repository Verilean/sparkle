import Tools.ShippingReaderInputs

/-! # Seven more node kinds for the term reader (G3)

`readTerm2` is `readTerm` with seven more node kinds, added from OUTSIDE the
core reader: its node reader is `readNode2 = readNode, else readNodeX`, and
its soundness is the same induction (`readWith_induct`) with one more case
list.

Kinds added (constructors of `Term`): `bitsNum`, `setw`, `slice`, `zextMap`,
`sliceF`, `concatLitHi`, `concatLitLo`.

What is proved
* `readTerm2_sound`: for every expression, a term `readTerm2` returns quotes
  back to the expression and is well formed.
* `readTerm2_expr_sound`: the same under binders with the structural domain
  test; its only hypothesis is the reading.

What is NOT proved here
* The three applicative lifts `appCompare`, `appBool`, `appBool2` are NOT
  read. Their quotation is `Signal.ap dom ty Bool (Signal.map dom ty π fn a) b`:
  the first operand `a` is an argument of an ARGUMENT of the node, and the
  reader hands a node only the readings of its own arguments
  (`Arg = Lean.Expr × Option AnyTerm`). Reading them needs the argument
  record to carry the reading of an argument's last argument as well (a
  third component of `goWith`'s result) — a change of the core reader, not
  done.
* Completeness of `readTerm2` on the seven kinds, and that `readTerm2`
  extends `readTerm` (it tries `readNode` first, but an argument position
  the core reader does not read may be read by the extension, so the
  argument lists differ; no theorem). -/
namespace Tools.ShippingReaderNodes2
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingReaderTerm Tools.ShippingReaderInputs
open Tools.ShippingMixedSourceBridge (inputExpr)

/-! ## Destructors -/

def lvl2 : List Lean.Level → Bool
  | [.zero, .zero] => true
  | _ => false

theorem lvl2_sound {ls : List Lean.Level} (h : lvl2 ls = true) : ls = [.zero, .zero] := by
  revert h
  unfold lvl2
  split
  · intro _; rfl
  · intro h; cases h

/-- `e` is the numeric literal `numLitE w v`. -/
def numLitOf? (w : Nat) : Lean.Expr → Option Nat
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) ty) (.lit (.natVal v)))
      (.app (.app (.const ``BitVec.instOfNat []) wE) (.lit (.natVal v'))) =>
    if bitVecE? ty = some w ∧ natE? wE = some w ∧ v' = v then some v else none
  | _ => none

theorem numLitOf?_sound {w v : Nat} {e : Lean.Expr} (h : numLitOf? w e = some v) :
    e = numLitE w v := by
  revert h
  unfold numLitOf?
  split
  · intro h
    split at h
    · rename_i g
      obtain ⟨h1, h2, h3⟩ := g
      cases h
      subst h3
      obtain rfl := bitVecE?_sound h1
      obtain rfl := natE?_sound h2
      rfl
    · cases h
  · intro h; cases h

/-- `BitVec.setWidth w w'`, partially applied. -/
def setwFn (w w' : Nat) : Lean.Expr :=
  .app (.app (.const ``BitVec.setWidth []) (natE w)) (natE w')

def isSetwFn (w w' : Nat) : Lean.Expr → Bool
  | .app (.app (.const ``BitVec.setWidth []) wE) wE' =>
    decide (natE? wE = some w ∧ natE? wE' = some w')
  | _ => false

theorem isSetwFn_sound {w w' : Nat} {e : Lean.Expr} (h : isSetwFn w w' e = true) :
    e = setwFn w w' := by
  revert h
  unfold isSetwFn
  split
  · intro h
    obtain ⟨h1, h2⟩ := of_decide_eq_true h
    obtain rfl := natE?_sound h1
    obtain rfl := natE?_sound h2
    rfl
  · intro h; cases h

/-- `fun nm => BitVec.extractLsb' start len nm` over a `w`-bit argument. -/
def sliceFn (nm : Lean.Name) (w start len : Nat) : Lean.Expr :=
  .lam nm (bitVecE w)
    (.app (.app (.app (.app (.const ``BitVec.extractLsb' []) (natE w)) (natE start))
      (natE len)) (.bvar 0)) .default

/-- The binder name and the start of a slice lambda at widths `w`, `len`. -/
def sliceLam? (w len : Nat) : Lean.Expr → Option (Lean.Name × Nat)
  | .lam nm ty (.app (.app (.app (.app (.const ``BitVec.extractLsb' []) wE) sE) lE)
      (.bvar 0)) .default =>
    if bitVecE? ty = some w ∧ natE? wE = some w ∧ natE? lE = some len then
      (natE? sE).bind fun s => some (nm, s)
    else none
  | _ => none

theorem sliceLam?_sound {w len st : Nat} {nm : Lean.Name} {e : Lean.Expr}
    (h : sliceLam? w len e = some (nm, st)) : e = sliceFn nm w st len := by
  revert h
  unfold sliceLam?
  split
  · intro h
    split at h
    · rename_i g
      obtain ⟨h1, h2, h3⟩ := g
      obtain ⟨s', hs, hb1⟩ := Option.bind_eq_some_iff.mp h
      cases hb1
      obtain rfl := bitVecE?_sound h1
      obtain rfl := natE?_sound h2
      obtain rfl := natE?_sound h3
      obtain rfl := natE?_sound hs
      rfl
    · cases h
  · intro h; cases h

/-- `fun nm => BitVec.append (0#k) nm` over an `n`-bit argument. -/
def zextFn (nm : Lean.Name) (k n : Nat) : Lean.Expr :=
  .lam nm (bitVecE n)
    (.app (.app (.app (.app (.const ``BitVec.append []) (natE k)) (natE n)) (litE k 0))
      (.bvar 0)) .default

/-- The binder name and the prefix width of a zero-extension lambda. -/
def zextLam? (n : Nat) : Lean.Expr → Option (Lean.Name × Nat)
  | .lam nm ty (.app (.app (.app (.app (.const ``BitVec.append []) kE) nE) lit)
      (.bvar 0)) .default =>
    if bitVecE? ty = some n ∧ natE? nE = some n then
      (natE? kE).bind fun k => if litOf? k lit = some 0 then some (nm, k) else none
    else none
  | _ => none

theorem zextLam?_sound {n k : Nat} {nm : Lean.Name} {e : Lean.Expr}
    (h : zextLam? n e = some (nm, k)) : e = zextFn nm k n := by
  revert h
  unfold zextLam?
  split
  · intro h
    split at h
    · rename_i g
      obtain ⟨h1, h2⟩ := g
      obtain ⟨k', hk, hb1⟩ := Option.bind_eq_some_iff.mp h
      split at hb1
      · rename_i hl
        cases hb1
        obtain rfl := bitVecE?_sound h1
        obtain rfl := natE?_sound h2
        obtain rfl := natE?_sound hk
        obtain rfl := litOf?_sound hl
        rfl
      · cases hb1
    · cases h
  · intro h; cases h

section
variable {cfg : Cfg}

/-- `Signal dom`, the functor. -/
def isSigHead (cfg : Cfg) : Lean.Expr → Bool
  | .app (.const ``Sparkle.Core.Signal.Signal [.zero]) d => cfg.isDom d
  | _ => false

theorem isSigHead_sound (hs : cfg.Sound) {e : Lean.Expr} (h : isSigHead cfg e = true) :
    e = .app (.const ``Sparkle.Core.Signal.Signal [.zero]) cfg.dom := by
  revert h
  unfold isSigHead
  split
  · intro h
    obtain rfl := hs.domEq _ h
    rfl
  · intro h; cases h

/-- The library's `Functor (Signal dom)` instance. -/
def isFunctorInst (cfg : Cfg) : Lean.Expr → Bool
  | .app (.const ``Sparkle.Core.Signal.instFunctorSignal [.zero]) d => cfg.isDom d
  | _ => false

theorem isFunctorInst_sound (hs : cfg.Sound) {e : Lean.Expr}
    (h : isFunctorInst cfg e = true) :
    e = .app (.const ``Sparkle.Core.Signal.instFunctorSignal [.zero]) cfg.dom := by
  revert h
  unfold isFunctorInst
  split
  · intro h
    obtain rfl := hs.domEq _ h
    rfl
  · intro h; cases h

/-- The literal-high concatenation instance at widths `k`, `n`. -/
def isHiInst (cfg : Cfg) (k n : Nat) : Lean.Expr → Bool
  | .app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat []) kE) d)
      nE => decide (natE? kE = some k ∧ cfg.isDom d = true ∧ natE? nE = some n)
  | _ => false

theorem isHiInst_sound (hs : cfg.Sound) {k n : Nat} {e : Lean.Expr}
    (h : isHiInst cfg k n e = true) :
    e = .app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat [])
      (natE k)) cfg.dom) (natE n) := by
  revert h
  unfold isHiInst
  split
  · intro h
    obtain ⟨hk, hd, hn⟩ := of_decide_eq_true h
    obtain rfl := natE?_sound hk
    obtain rfl := hs.domEq _ hd
    obtain rfl := natE?_sound hn
    rfl
  · intro h; cases h

/-- The literal-low concatenation instance at widths `m`, `k`. -/
def isLoInst (cfg : Cfg) (m k : Nat) : Lean.Expr → Bool
  | .app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat_1 []) d)
      mE) kE => decide (cfg.isDom d = true ∧ natE? mE = some m ∧ natE? kE = some k)
  | _ => false

theorem isLoInst_sound (hs : cfg.Sound) {m k : Nat} {e : Lean.Expr}
    (h : isLoInst cfg m k e = true) :
    e = .app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat_1 [])
      cfg.dom) (natE m)) (natE k) := by
  revert h
  unfold isLoInst
  split
  · intro h
    obtain ⟨hd, hm, hk⟩ := of_decide_eq_true h
    obtain rfl := hs.domEq _ hd
    obtain rfl := natE?_sound hm
    obtain rfl := natE?_sound hk
    rfl
  · intro h; cases h

/-! ## Three arguments: `Signal.pure` of a numeric literal -/

def readBitsNum (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 : Lean.Expr) :
    Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.pure ∧ lvl1 ls = true ∧ cfg.isDom x0 = true then
    (bitVecE? x1).bind fun w => (numLitOf? w x2).bind fun v =>
      if v < 2 ^ w ∧ 0 < w then some (⟨.bits w, .bitsNum w v⟩ : AnyTerm) else none
  else none

theorem readBitsNum_sound (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} {r : AnyTerm}
    (h : readBitsNum cfg c ls x0 x1 x2 = some r) :
    Reads cfg r (.app (.app (.app (.const c ls) x0) x1) x2) := by
  unfold readBitsNum at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0⟩ := g
    obtain ⟨w, hw, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    split at hb2
    · rename_i g2
      subst hc
      obtain rfl := lvl1_sound hls
      obtain rfl := hs.domEq _ h0
      obtain rfl := bitVecE?_sound hw
      obtain rfl := numLitOf?_sound hv
      cases hb2
      exact ⟨rfl, g2⟩
    · cases hb2
  · cases h

/-! ## Five arguments: `Signal.map` -/

/-- `Signal.map (BitVec.setWidth w') a`. -/
def readSetw (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 x3 : Lean.Expr)
    (r4 : Option AnyTerm) : Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.map ∧ lvl1 ls = true ∧ cfg.isDom x0 = true then
    (bitVecE? x1).bind fun w => (bitVecE? x2).bind fun w' =>
      if isSetwFn w w' x3 = true ∧ 0 < w' then
        (r4.bind (asBits w)).bind fun a => some (⟨.bits w', .setw w' a⟩ : AnyTerm)
      else none
  else none

theorem readSetw_sound (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr} {r4 : Option AnyTerm} {r : AnyTerm}
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (h : readSetw cfg c ls x0 x1 x2 x3 r4 = some r) :
    Reads cfg r (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) := by
  unfold readSetw at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0⟩ := g
    obtain ⟨w, hw, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w', hw', hb2⟩ := Option.bind_eq_some_iff.mp hb1
    split at hb2
    · rename_i g2
      obtain ⟨hf, hpos⟩ := g2
      obtain ⟨a, ha, hb3⟩ := Option.bind_eq_some_iff.mp hb2
      obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
      obtain rfl := asBits_some _ _ hab
      obtain ⟨qa, wa⟩ := ih4 _ hra
      subst hc
      obtain rfl := lvl1_sound hls
      obtain rfl := hs.domEq _ h0
      obtain rfl := bitVecE?_sound hw
      obtain rfl := bitVecE?_sound hw'
      obtain rfl := isSetwFn_sound hf
      cases hb3
      subst qa
      exact ⟨rfl, And.intro wa hpos⟩
    · cases hb2
  · cases h

/-- `Signal.map (fun x => BitVec.extractLsb' start len x) a`. -/
def readSlice (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 x3 : Lean.Expr)
    (r4 : Option AnyTerm) : Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.map ∧ lvl1 ls = true ∧ cfg.isDom x0 = true then
    (bitVecE? x1).bind fun w => (bitVecE? x2).bind fun len =>
      (sliceLam? w len x3).bind fun p =>
        if 0 < len ∧ p.2 + len ≤ w then
          (r4.bind (asBits w)).bind fun a =>
            some (⟨.bits len, .slice p.1 p.2 len a⟩ : AnyTerm)
        else none
  else none

theorem readSlice_sound (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr} {r4 : Option AnyTerm} {r : AnyTerm}
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (h : readSlice cfg c ls x0 x1 x2 x3 r4 = some r) :
    Reads cfg r (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) := by
  unfold readSlice at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0⟩ := g
    obtain ⟨w, hw, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨len, hlen, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨p, hp, hb3⟩ := Option.bind_eq_some_iff.mp hb2
    obtain ⟨nm, st⟩ := p
    split at hb3
    · rename_i g2
      obtain ⟨a, ha, hb4⟩ := Option.bind_eq_some_iff.mp hb3
      obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
      obtain rfl := asBits_some _ _ hab
      obtain ⟨qa, wa⟩ := ih4 _ hra
      subst hc
      obtain rfl := lvl1_sound hls
      obtain rfl := hs.domEq _ h0
      obtain rfl := bitVecE?_sound hw
      obtain rfl := bitVecE?_sound hlen
      obtain rfl := sliceLam?_sound hp
      cases hb4
      subst qa
      exact ⟨rfl, And.intro wa g2⟩
    · cases hb3
  · cases h

/-- `Signal.map (fun v => BitVec.append (0#k) v) a`. -/
def readZext (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 x3 : Lean.Expr)
    (r4 : Option AnyTerm) : Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.map ∧ lvl1 ls = true ∧ cfg.isDom x0 = true then
    (bitVecE? x1).bind fun n => (zextLam? n x3).bind fun p =>
      if bitVecE? x2 = some (p.2 + n) ∧ 0 < p.2 then
        (r4.bind (asBits n)).bind fun a =>
          some (⟨.bits (p.2 + n), .zextMap p.1 p.2 a⟩ : AnyTerm)
      else none
  else none

theorem readZext_sound (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr} {r4 : Option AnyTerm} {r : AnyTerm}
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (h : readZext cfg c ls x0 x1 x2 x3 r4 = some r) :
    Reads cfg r (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) := by
  unfold readZext at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0⟩ := g
    obtain ⟨n, hn, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨p, hp, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨nm, k⟩ := p
    split at hb2
    · rename_i g2
      obtain ⟨h2, hpos⟩ := g2
      obtain ⟨a, ha, hb3⟩ := Option.bind_eq_some_iff.mp hb2
      obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
      obtain rfl := asBits_some _ _ hab
      obtain ⟨qa, wa⟩ := ih4 _ hra
      subst hc
      obtain rfl := lvl1_sound hls
      obtain rfl := hs.domEq _ h0
      obtain rfl := bitVecE?_sound hn
      obtain rfl := bitVecE?_sound h2
      obtain rfl := zextLam?_sound hp
      cases hb3
      subst qa
      exact ⟨rfl, And.intro wa hpos⟩
    · cases hb2
  · cases h

/-! ## Six arguments -/

/-- `(fun x => BitVec.extractLsb' start len x) <$> a`. -/
def readSliceF (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level)
    (x0 x1 x2 x3 x4 : Lean.Expr) (r5 : Option AnyTerm) : Option AnyTerm :=
  if c = ``Functor.map ∧ lvl2 ls = true ∧ isSigHead cfg x0 = true ∧
      isFunctorInst cfg x1 = true then
    (bitVecE? x2).bind fun w => (bitVecE? x3).bind fun len =>
      (sliceLam? w len x4).bind fun p =>
        if 0 < len ∧ p.2 + len ≤ w then
          (r5.bind (asBits w)).bind fun a =>
            some (⟨.bits len, .sliceF p.1 p.2 len a⟩ : AnyTerm)
        else none
  else none

theorem readSliceF_sound (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 x5 : Lean.Expr} {r5 : Option AnyTerm}
    {r : AnyTerm}
    (ih5 : ∀ r', r5 = some r' → Reads cfg r' x5)
    (h : readSliceF cfg c ls x0 x1 x2 x3 x4 r5 = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) := by
  unfold readSliceF at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0, h1⟩ := g
    obtain ⟨w, hw, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨len, hlen, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨p, hp, hb3⟩ := Option.bind_eq_some_iff.mp hb2
    obtain ⟨nm, st⟩ := p
    split at hb3
    · rename_i g2
      obtain ⟨a, ha, hb4⟩ := Option.bind_eq_some_iff.mp hb3
      obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
      obtain rfl := asBits_some _ _ hab
      obtain ⟨qa, wa⟩ := ih5 _ hra
      subst hc
      obtain rfl := lvl2_sound hls
      obtain rfl := isSigHead_sound hs h0
      obtain rfl := isFunctorInst_sound hs h1
      obtain rfl := bitVecE?_sound hw
      obtain rfl := bitVecE?_sound hlen
      obtain rfl := sliceLam?_sound hp
      cases hb4
      subst qa
      exact ⟨rfl, And.intro wa g2⟩
    · cases hb3
  · cases h

/-- `v#k ++ b`: a literal high operand. -/
def readConcatHi (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level)
    (x0 x1 x2 x3 x4 : Lean.Expr) (r5 : Option AnyTerm) : Option AnyTerm :=
  if c = ``HAppend.hAppend ∧ lvl3 ls = true then
    (bitVecE? x0).bind fun k => (sigBitsT? cfg x1).bind fun n =>
      (litOf? k x4).bind fun v =>
        if sigBitsT? cfg x2 = some (k + n) ∧ isHiInst cfg k n x3 = true ∧ 0 < k ∧
            v < 2 ^ k then
          (r5.bind (asBits n)).bind fun b =>
            some (⟨.bits (k + n), .concatLitHi k v b⟩ : AnyTerm)
        else none
  else none

theorem readConcatHi_sound (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 x5 : Lean.Expr} {r5 : Option AnyTerm}
    {r : AnyTerm}
    (ih5 : ∀ r', r5 = some r' → Reads cfg r' x5)
    (h : readConcatHi cfg c ls x0 x1 x2 x3 x4 r5 = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) := by
  unfold readConcatHi at h
  split at h
  · rename_i g
    obtain ⟨hc, hls⟩ := g
    obtain ⟨k, hk, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨n, hn, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨v, hv, hb3⟩ := Option.bind_eq_some_iff.mp hb2
    split at hb3
    · rename_i g2
      obtain ⟨h2, h3, hkpos, hvlt⟩ := g2
      obtain ⟨b, hb, hb4⟩ := Option.bind_eq_some_iff.mp hb3
      obtain ⟨rb, hrb, hbb⟩ := Option.bind_eq_some_iff.mp hb
      obtain rfl := asBits_some _ _ hbb
      obtain ⟨qb, wb⟩ := ih5 _ hrb
      subst hc
      obtain rfl := lvl3_sound hls
      obtain rfl := bitVecE?_sound hk
      obtain rfl := sigBitsT?_sound hs hn
      obtain rfl := sigBitsT?_sound hs h2
      obtain rfl := isHiInst_sound hs h3
      obtain rfl := litOf?_sound hv
      cases hb4
      subst qb
      exact ⟨rfl, And.intro wb (And.intro hkpos hvlt)⟩
    · cases hb3
  · cases h

/-- `a ++ v#k`: a literal low operand. -/
def readConcatLo (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level)
    (x0 x1 x2 x3 x5 : Lean.Expr) (r4 : Option AnyTerm) : Option AnyTerm :=
  if c = ``HAppend.hAppend ∧ lvl3 ls = true then
    (sigBitsT? cfg x0).bind fun m => (bitVecE? x1).bind fun k =>
      (litOf? k x5).bind fun v =>
        if sigBitsT? cfg x2 = some (m + k) ∧ isLoInst cfg m k x3 = true ∧ 0 < k ∧
            v < 2 ^ k then
          (r4.bind (asBits m)).bind fun a =>
            some (⟨.bits (m + k), .concatLitLo a k v⟩ : AnyTerm)
        else none
  else none

theorem readConcatLo_sound (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 x5 : Lean.Expr} {r4 : Option AnyTerm}
    {r : AnyTerm}
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (h : readConcatLo cfg c ls x0 x1 x2 x3 x5 r4 = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) := by
  unfold readConcatLo at h
  split at h
  · rename_i g
    obtain ⟨hc, hls⟩ := g
    obtain ⟨m, hm, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨k, hk, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨v, hv, hb3⟩ := Option.bind_eq_some_iff.mp hb2
    split at hb3
    · rename_i g2
      obtain ⟨h2, h3, hkpos, hvlt⟩ := g2
      obtain ⟨a, ha, hb4⟩ := Option.bind_eq_some_iff.mp hb3
      obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
      obtain rfl := asBits_some _ _ hab
      obtain ⟨qa, wa⟩ := ih4 _ hra
      subst hc
      obtain rfl := lvl3_sound hls
      obtain rfl := sigBitsT?_sound hs hm
      obtain rfl := bitVecE?_sound hk
      obtain rfl := sigBitsT?_sound hs h2
      obtain rfl := isLoInst_sound hs h3
      obtain rfl := litOf?_sound hv
      cases hb4
      subst qa
      exact ⟨rfl, And.intro wa (And.intro hkpos hvlt)⟩
    · cases hb3
  · cases h

/-! ## The extended reader -/

/-- The seven added kinds, by the number of arguments. -/
def readNodeX (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) : List Arg → Option AnyTerm
  | [x0, x1, x2] => readBitsNum cfg c ls x0.1 x1.1 x2.1
  | [x0, x1, x2, x3, x4] =>
    alt (readSetw cfg c ls x0.1 x1.1 x2.1 x3.1 x4.2)
      (alt (readSlice cfg c ls x0.1 x1.1 x2.1 x3.1 x4.2)
        (readZext cfg c ls x0.1 x1.1 x2.1 x3.1 x4.2))
  | [x0, x1, x2, x3, x4, x5] =>
    alt (readSliceF cfg c ls x0.1 x1.1 x2.1 x3.1 x4.1 x5.2)
      (alt (readConcatHi cfg c ls x0.1 x1.1 x2.1 x3.1 x4.1 x5.2)
        (readConcatLo cfg c ls x0.1 x1.1 x2.1 x3.1 x5.1 x4.2))
  | _ => none

theorem readNodeX_sound (hs : cfg.Sound) {c : Lean.Name} {ls : List Lean.Level}
    {args : List Arg} {r : AnyTerm}
    (ha : ∀ p, p ∈ args → ∀ r', p.2 = some r' → Reads cfg r' p.1)
    (h : readNodeX cfg c ls args = some r) : Reads cfg r (apps (.const c ls) args) := by
  revert ha h
  unfold readNodeX
  split
  · rename_i x0 x1 x2
    intro _ h
    exact readBitsNum_sound hs h
  · rename_i x0 x1 x2 x3 x4
    intro ha h
    rcases alt_some h with h1 | h1
    · exact readSetw_sound hs (ha x4 (by simp)) h1
    · rcases alt_some h1 with h2 | h2
      · exact readSlice_sound hs (ha x4 (by simp)) h2
      · exact readZext_sound hs (ha x4 (by simp)) h2
  · rename_i x0 x1 x2 x3 x4 x5
    intro ha h
    rcases alt_some h with h1 | h1
    · exact readSliceF_sound hs (ha x5 (by simp)) h1
    · rcases alt_some h1 with h2 | h2
      · exact readConcatHi_sound hs (ha x5 (by simp)) h2
      · exact readConcatLo_sound hs (ha x4 (by simp)) h2
  · intro _ h
    cases h

/-- The node reader of the core kinds, else of the added kinds. -/
def readNode2 (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (args : List Arg) :
    Option AnyTerm :=
  alt (readNode cfg c ls args) (readNodeX cfg c ls args)

theorem readNode2_sound (hs : cfg.Sound) {c : Lean.Name} {ls : List Lean.Level}
    {args : List Arg} {r : AnyTerm}
    (ha : ∀ p, p ∈ args → ∀ r', p.2 = some r' → Reads cfg r' p.1)
    (h : readNode2 cfg c ls args = some r) : Reads cfg r (apps (.const c ls) args) := by
  unfold readNode2 at h
  rcases alt_some h with h1 | h1
  · exact readNode_sound hs ha h1
  · exact readNodeX_sound hs ha h1

end

/-- **The extended reader**: eighteen node kinds. -/
def readTerm2 (cfg : Cfg) (e : Lean.Expr) : Option AnyTerm :=
  readWith (readInput cfg) (readNode2 cfg) e

theorem readTerm2_reads (cfg : Cfg) (hs : cfg.Sound) (e : Lean.Expr) (r : AnyTerm)
    (h : readTerm2 cfg e = some r) : Reads cfg r e :=
  readWith_induct (readInput cfg) (readNode2 cfg) (Reads cfg)
    (fun _ _ h => readInput_sound hs h) (fun _ _ _ _ ha h => readNode2_sound hs ha h) e r h

/-- **Soundness of the extended reader**, for every expression. -/
theorem readTerm2_sound (cfg : Cfg) (hs : cfg.Sound) (e : Lean.Expr) (r : AnyTerm)
    (h : readTerm2 cfg e = some r) :
    quote cfg.dom cfg.bools cfg.bits r.2 = e ∧ r.2.WF cfg.kb cfg.kv cfg.vw :=
  ⟨(readTerm2_reads cfg hs e r h).eq, (readTerm2_reads cfg hs e r h).wf⟩

/-- Soundness of the extended reader under binders, with the structural
domain test: the reading is the only hypothesis. -/
theorem readTerm2_expr_sound (dom : Lean.Expr) (ks : List MixedGateBinder)
    (e : Lean.Expr) (r : AnyTerm)
    (h : readTerm2 (kindsCfg dom (isExpr dom) ks) e = some r) :
    quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) r.2 = e ∧
      r.2.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0) :=
  readTerm2_sound (kindsCfg dom (isExpr dom) ks)
    (kindsCfg_sound dom (isExpr dom) (isExpr_sound dom) ks) e r h

end Tools.ShippingReaderNodes2
