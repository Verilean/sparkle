import Tools.ShippingUnifiedSource

/-! # Reader soundness for the unified source terms (G3, syntactic half)

The endpoints of the certified routes are stated on `quote dom bools bits t`
for a typed term `t : Term s` (`Tools.ShippingUnifiedSource`). Until now the
link "the body the front end hands on IS such a quotation" is established per
declaration: the generator reads a term with the `partial`, unchecked
`Tools.ShippingMachineCommand.unq` and the kernel then checks one `Eq.refl`
(`f.machine_body`, `f.gate_peel`). Nothing quantifies over bodies.

This file has a TOTAL reader `readTerm`, a kernel-reducible function on
`Lean.Expr` by structural recursion, and proves for EVERY expression `e`:

  `readTerm cfg e = some ⟨s, t⟩ → quote cfg.dom cfg.bools cfg.bits t = e ∧ t.WF …`

(`readTerm_sound`). The proof is ONE induction on the expression
(`go_induct` / `readTerm_induct`), generic in the property: a node kind is a case
of `readNode` plus one lemma about a non-recursive function; the induction is
not touched when a kind is added.

What is proved
* `readTerm_induct`: the induction principle of the reader, for any property
  `P : AnyTerm → Lean.Expr → Prop` closed under the leaf reader and the node
  reader.
* `readTerm_sound`: the quotation of the term read is the expression, and the
  term is well formed (`Term.WF`), for the node kinds below.
* Node kinds covered (constructors of `Term`): `boolInput`, `bitsInput`,
  `boolLit`, `bitsLit`, `boolNot`, `mux` (both sorts), `binary` (the eight
  operators), `boolBinary`, `compare` (`ult ule slt sle` and `eq`), `boolEq`,
  `concat`.

What is NOT proved here
* Node kinds not yet read (the reader returns `none` on them): `bitsNum`,
  `setw`, `slice`, `sliceF`, `zextMap`, `concatLitHi`, `concatLitLo`,
  `appCompare`, `appBool`, `appBool2`. Each is one more `readX` /
  `readX_sound` pair and one more `alt` in `read3` … `read6`.
* Completeness (`readTerm cfg (quote … t) = some ⟨s, t⟩` for well-formed `t`):
  not stated. Without it nothing says the reader accepts what the compiler
  accepts.
* Nothing about the compiler's own recognisers (`unifiedGateRoot`, …): they
  do not pin the domain argument, the universe levels or the type arguments
  of a node (wildcards), so "accepted ⟹ a quotation" is FALSE for them as
  stated (docs/parallel/G3-reader.md, §3). `readTerm` pins every position
  `quote` writes.
* Nothing about `machineShape?` (it calls `partial` functions), nor about the
  MEANING of a quotation (`quote t` elaborates to `denote t`): that is
  reflection of Lean's elaboration, per declaration by `rfl` today.

The leaf tables (`Cfg.inBool`, `Cfg.inBits`, `Cfg.isDom`) are parameters with
a stated contract `Cfg.Sound`; `Tools.ShippingReaderInputs` discharges it for
the numbering the machine endpoints use. -/
namespace Tools.ShippingReaderTerm
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingMuxTypeSoundness

/-- A typed term of either sort. -/
abbrev AnyTerm := Σ s : SType, Term s

/-! ## Small tools -/

theorem none_ne {α : Type} {r : α} {Q : Prop} (h : (none : Option α) = some r) : Q := by
  cases h

/-- The first reading that succeeds. -/
def alt {α : Type} (a b : Option α) : Option α :=
  match a with
  | some r => some r
  | none => b

theorem alt_some {α : Type} {a b : Option α} {r : α} (h : alt a b = some r) :
    a = some r ∨ b = some r := by
  cases a with
  | none => exact Or.inr h
  | some x => exact Or.inl h

def asBool : AnyTerm → Option (Term .bool)
  | ⟨.bool, t⟩ => some t
  | ⟨.bits _, _⟩ => none

theorem asBool_some : ∀ (r : AnyTerm) (t : Term .bool), asBool r = some t → r = ⟨.bool, t⟩
  | ⟨.bool, u⟩, t, h => by
    have h' : some u = some t := h
    cases h'
    rfl
  | ⟨.bits _, _⟩, _, h => none_ne h

/-- A term at a width equal to the expected one. -/
def castBits {w w' : Nat} (h : w' = w) (t : Term (.bits w')) : Term (.bits w) := h ▸ t

def asBits (w : Nat) : AnyTerm → Option (Term (.bits w))
  | ⟨.bits w', t⟩ => if h : w' = w then some (castBits h t) else none
  | ⟨.bool, _⟩ => none

theorem asBits_some {w : Nat} :
    ∀ (r : AnyTerm) (t : Term (.bits w)), asBits w r = some t → r = ⟨.bits w, t⟩
  | ⟨.bool, _⟩, _, h => none_ne h
  | ⟨.bits w', u⟩, t, h => by
    have h' : (if hw : w' = w then some (castBits hw u) else none) = some t := h
    split at h'
    · rename_i hw
      subst hw
      cases h'
      rfl
    · cases h'

/-! ## Exact syntactic destructors

Each returns the data of an expression only when the expression is EXACTLY
the form `quote` writes: head constant, universe levels, every argument. -/

def lvl0 : List Lean.Level → Bool
  | [] => true
  | _ => false

theorem lvl0_sound {ls : List Lean.Level} (h : lvl0 ls = true) : ls = [] := by
  revert h
  unfold lvl0
  split
  · intro _; rfl
  · intro h; cases h

def lvl1 : List Lean.Level → Bool
  | [.zero] => true
  | _ => false

theorem lvl1_sound {ls : List Lean.Level} (h : lvl1 ls = true) : ls = [.zero] := by
  revert h
  unfold lvl1
  split
  · intro _; rfl
  · intro h; cases h

def lvl3 : List Lean.Level → Bool
  | [.zero, .zero, .zero] => true
  | _ => false

theorem lvl3_sound {ls : List Lean.Level} (h : lvl3 ls = true) :
    ls = [.zero, .zero, .zero] := by
  revert h
  unfold lvl3
  split
  · intro _; rfl
  · intro h; cases h

/-- `e` is `natE n`. -/
def natE? : Lean.Expr → Option Nat
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
      (.app (.const ``instOfNatNat []) (.lit (.natVal k))) => if k = n then some n else none
  | _ => none

theorem natE?_sound {e : Lean.Expr} {n : Nat} (h : natE? e = some n) : e = natE n := by
  revert h
  unfold natE?
  split
  · intro h
    split at h
    · rename_i hk
      cases h
      subst hk
      rfl
    · cases h
  · intro h; cases h

/-- `e` is `bitVecE n`. -/
def bitVecE? : Lean.Expr → Option Nat
  | .app (.const ``BitVec []) wE => natE? wE
  | _ => none

theorem bitVecE?_sound {e : Lean.Expr} {n : Nat} (h : bitVecE? e = some n) :
    e = bitVecE n := by
  revert h
  unfold bitVecE?
  split
  · intro h
    obtain rfl := natE?_sound h
    rfl
  · intro h; cases h

/-- `e` is the closed constant `n`. -/
def isConst (n : Lean.Name) : Lean.Expr → Bool
  | .const c [] => decide (c = n)
  | _ => false

theorem isConst_sound {n : Lean.Name} {e : Lean.Expr} (h : isConst n e = true) :
    e = .const n [] := by
  revert h
  unfold isConst
  split
  · intro h
    exact congrArg (fun c => Lean.Expr.const c []) (of_decide_eq_true h)
  · intro h; cases h

/-- `e` is the literal `v#w`. -/
def litOf? (w : Nat) : Lean.Expr → Option Nat
  | .app (.app (.const ``BitVec.ofNat []) wE) vE =>
    if natE? wE = some w then natE? vE else none
  | _ => none

theorem litOf?_sound {w v : Nat} {e : Lean.Expr} (h : litOf? w e = some v) :
    e = litE w v := by
  revert h
  unfold litOf?
  split
  · intro h
    split at h
    · rename_i hw
      obtain rfl := natE?_sound hw
      obtain rfl := natE?_sound h
      rfl
    · cases h
  · intro h; cases h

/-- The standard `BEq Bool` instance, as `boolEqE` writes it. -/
def boolBEqE : Lean.Expr :=
  .app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Bool []))
    (.const ``instDecidableEqBool [])

def isBoolBEq : Lean.Expr → Bool
  | .app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Bool []))
      (.const ``instDecidableEqBool []) => true
  | _ => false

theorem isBoolBEq_sound {e : Lean.Expr} (h : isBoolBEq e = true) : e = boolBEqE := by
  revert h
  unfold isBoolBEq
  split
  · intro _; rfl
  · intro h; cases h

/-- The standard `BEq (BitVec w)` instance, as `compareE .eq` writes it. -/
def bitsBEqE (w : Nat) : Lean.Expr :=
  .app (.app (.const ``instBEqOfDecidableEq [.zero]) (bitVecE w))
    (.app (.const ``instDecidableEqBitVec []) (natE w))

def bitsBEq? : Lean.Expr → Option Nat
  | .app (.app (.const ``instBEqOfDecidableEq [.zero]) ty)
      (.app (.const ``instDecidableEqBitVec []) wE) =>
    (bitVecE? ty).bind fun w => if natE? wE = some w then some w else none
  | _ => none

theorem bitsBEq?_sound {e : Lean.Expr} {w : Nat} (h : bitsBEq? e = some w) :
    e = bitsBEqE w := by
  revert h
  unfold bitsBEq?
  split
  · intro h
    obtain ⟨w', hty, hb1⟩ := Option.bind_eq_some_iff.mp h
    split at hb1
    · rename_i hw
      cases hb1
      obtain rfl := bitVecE?_sound hty
      obtain rfl := natE?_sound hw
      rfl
    · cases hb1
  · intro h; cases h

/-- The comparison a head constant names (the four ordered ones; equality is
`Signal.beq`, read by its own node). -/
def cmpOf? (c : Lean.Name) : Option SignalCompareKind :=
  if c = ``Sparkle.Core.Signal.Signal.ult then some .ult
  else if c = ``Sparkle.Core.Signal.Signal.ule then some .ule
  else if c = ``Sparkle.Core.Signal.Signal.slt then some .slt
  else if c = ``Sparkle.Core.Signal.Signal.sle then some .sle
  else none

theorem cmpOf?_sound {c : Lean.Name} {op : SignalCompareKind} (h : cmpOf? c = some op) :
    c = compareName op ∧ op ≠ .eq := by
  unfold cmpOf? at h
  split at h
  · rename_i hc
    cases h
    exact ⟨hc, fun e => by cases e⟩
  · split at h
    · rename_i hc
      cases h
      exact ⟨hc, fun e => by cases e⟩
    · split at h
      · rename_i hc
        cases h
        exact ⟨hc, fun e => by cases e⟩
      · split at h
        · rename_i hc
          cases h
          exact ⟨hc, fun e => by cases e⟩
        · cases h

/-- The BitVec operator a method constant names. -/
def binOf? (c : Lean.Name) : Option Binary :=
  [Binary.add, .sub, .mul, .and, .or, .xor, .shr, .shl].find? fun op =>
    decide (binMethod op = c)

theorem binOf?_sound {c : Lean.Name} {op : Binary} (h : binOf? c = some op) :
    binMethod op = c := by
  unfold binOf? at h
  have hp := List.find?_some h
  simpa using hp

/-- The Bool operator a method constant names. -/
def boolBinOf? (c : Lean.Name) : Option SignalBoolBinKind :=
  [SignalBoolBinKind.band, .bor, .bxor].find? fun k => decide (signalBoolBinName k = c)

theorem boolBinOf?_sound {c : Lean.Name} {k : SignalBoolBinKind} (h : boolBinOf? c = some k) :
    signalBoolBinName k = c := by
  unfold boolBinOf? at h
  have hp := List.find?_some h
  simpa using hp

/-! ## The reader's parameters -/

/-- What the reader is told about the context of a body: the domain
expression every node mentions and a test for it, the expressions of the
Bool / BitVec inputs (`quote`'s `bools` / `bits`), the input a loose bound
variable is (`inBool`, `inBits`: the input's number, and its width), and the
bounds `Term.WF` is stated with. -/
structure Cfg where
  dom : Lean.Expr
  bools : Nat → Lean.Expr
  bits : Nat → Lean.Expr
  isDom : Lean.Expr → Bool
  inBool : Nat → Option Nat
  inBits : Nat → Option (Nat × Nat)
  kb : Nat
  kv : Nat
  vw : Nat → Nat

/-- The contract of the leaf tables. It speaks about the domain test and the
input numbering only, not about any body. -/
structure Cfg.Sound (cfg : Cfg) : Prop where
  domEq : ∀ d, cfg.isDom d = true → d = cfg.dom
  boolIn : ∀ i j, cfg.inBool i = some j → cfg.bools j = .bvar i ∧ j < cfg.kb
  bitsIn : ∀ i w j, cfg.inBits i = some (w, j) →
    cfg.bits j = .bvar i ∧ j < cfg.kv ∧ cfg.vw j = w ∧ 0 < w

/-- `r` is a reading of `e`: `e` is the quotation of `r`, and `r` is well
formed. -/
structure Reads (cfg : Cfg) (r : AnyTerm) (e : Lean.Expr) : Prop where
  eq : quote cfg.dom cfg.bools cfg.bits r.2 = e
  wf : r.2.WF cfg.kb cfg.kv cfg.vw

/-! ## Destructors that mention the domain -/

/-- `Signal dom Bool`. -/
def sigBoolT (dom : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``Sparkle.Core.Signal.Signal [.zero]) dom) (.const ``Bool [])

def isSigBoolT (cfg : Cfg) : Lean.Expr → Bool
  | .app (.app (.const ``Sparkle.Core.Signal.Signal [.zero]) d) (.const ``Bool []) =>
    cfg.isDom d
  | _ => false

theorem isSigBoolT_sound {cfg : Cfg} (hs : cfg.Sound) {e : Lean.Expr}
    (h : isSigBoolT cfg e = true) : e = sigBoolT cfg.dom := by
  revert h
  unfold isSigBoolT
  split
  · intro h
    obtain rfl := hs.domEq _ h
    rfl
  · intro h; cases h

/-- `e` is `sigT dom n` (`Signal dom (BitVec n)`). -/
def sigBitsT? (cfg : Cfg) : Lean.Expr → Option Nat
  | .app (.app (.const ``Sparkle.Core.Signal.Signal [.zero]) d) t =>
    if cfg.isDom d = true then bitVecE? t else none
  | _ => none

theorem sigBitsT?_sound {cfg : Cfg} (hs : cfg.Sound) {e : Lean.Expr} {n : Nat}
    (h : sigBitsT? cfg e = some n) : e = sigT cfg.dom n := by
  revert h
  unfold sigBitsT?
  split
  · intro h
    split at h
    · rename_i hd
      obtain rfl := hs.domEq _ hd
      obtain rfl := bitVecE?_sound h
      rfl
    · cases h
  · intro h; cases h

/-- `e` is the instance constant `n` at the domain. -/
def isInstDom (cfg : Cfg) (n : Lean.Name) : Lean.Expr → Bool
  | .app (.const c []) d => decide (c = n ∧ cfg.isDom d = true)
  | _ => false

theorem isInstDom_sound {cfg : Cfg} (hs : cfg.Sound) {n : Lean.Name} {e : Lean.Expr}
    (h : isInstDom cfg n e = true) : e = .app (.const n []) cfg.dom := by
  revert h
  unfold isInstDom
  split
  · intro h
    obtain ⟨hc, hd⟩ := of_decide_eq_true h
    subst hc
    obtain rfl := hs.domEq _ hd
    rfl
  · intro h; cases h

/-- `e` is the instance constant `n` at the domain and a literal width. -/
def instDomNat? (cfg : Cfg) (n : Lean.Name) : Lean.Expr → Option Nat
  | .app (.app (.const c []) d) wE =>
    if c = n ∧ cfg.isDom d = true then natE? wE else none
  | _ => none

theorem instDomNat?_sound {cfg : Cfg} (hs : cfg.Sound) {n : Lean.Name} {e : Lean.Expr}
    {w : Nat} (h : instDomNat? cfg n e = some w) :
    e = .app (.app (.const n []) cfg.dom) (natE w) := by
  revert h
  unfold instDomNat?
  split
  · intro h
    split at h
    · rename_i g
      obtain ⟨hc, hd⟩ := g
      subst hc
      obtain rfl := hs.domEq _ hd
      obtain rfl := natE?_sound h
      rfl
    · cases h
  · intro h; cases h

/-- `e` is the Signal concatenation instance at the domain and widths `m`,
`n`. -/
def isConcatInst (cfg : Cfg) (m n : Nat) : Lean.Expr → Bool
  | .app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat []) d) mE)
      nE => decide (cfg.isDom d = true ∧ natE? mE = some m ∧ natE? nE = some n)
  | _ => false

theorem isConcatInst_sound {cfg : Cfg} (hs : cfg.Sound) {m n : Nat} {e : Lean.Expr}
    (h : isConcatInst cfg m n e = true) :
    e = .app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat [])
      cfg.dom) (natE m)) (natE n) := by
  revert h
  unfold isConcatInst
  split
  · intro h
    obtain ⟨hd, hm, hn⟩ := of_decide_eq_true h
    obtain rfl := hs.domEq _ hd
    obtain rfl := natE?_sound hm
    obtain rfl := natE?_sound hn
    rfl
  · intro h; cases h

/-! ## Leaves -/

/-- A loose bound variable: a Bool input or a BitVec input. -/
def readInput (cfg : Cfg) (i : Nat) : Option AnyTerm :=
  alt ((cfg.inBool i).bind fun j => some (⟨.bool, .boolInput j⟩ : AnyTerm))
    ((cfg.inBits i).bind fun wj => some (⟨.bits wj.1, .bitsInput wj.1 wj.2⟩ : AnyTerm))

theorem readInput_sound {cfg : Cfg} (hs : cfg.Sound) {i : Nat} {r : AnyTerm}
    (h : readInput cfg i = some r) : Reads cfg r (.bvar i) := by
  unfold readInput at h
  rcases alt_some h with h | h
  · obtain ⟨j, hj, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    obtain ⟨q, lt⟩ := hs.boolIn i j hj
    exact ⟨q, lt⟩
  · obtain ⟨wj, hj, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, j⟩ := wj
    cases h
    obtain ⟨q, lt⟩ := hs.bitsIn i w j hj
    exact ⟨q, lt⟩

/-! ## Nodes of three arguments -/

/-- `Signal.pure true` / `Signal.pure false`. -/
def readBoolLit (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 : Lean.Expr) :
    Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.pure ∧ lvl1 ls = true ∧ cfg.isDom x0 = true ∧
      isConst ``Bool x1 = true then
    if isConst ``Bool.true x2 = true then some ⟨.bool, .boolLit true⟩
    else if isConst ``Bool.false x2 = true then some ⟨.bool, .boolLit false⟩
    else none
  else none

theorem readBoolLit_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} {r : AnyTerm}
    (h : readBoolLit cfg c ls x0 x1 x2 = some r) :
    Reads cfg r (.app (.app (.app (.const c ls) x0) x1) x2) := by
  unfold readBoolLit at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0, h1⟩ := g
    subst hc
    obtain rfl := lvl1_sound hls
    obtain rfl := hs.domEq _ h0
    obtain rfl := isConst_sound h1
    split at h
    · rename_i h2
      obtain rfl := isConst_sound h2
      cases h
      exact ⟨rfl, trivial⟩
    · split at h
      · rename_i h2
        obtain rfl := isConst_sound h2
        cases h
        exact ⟨rfl, trivial⟩
      · cases h
  · cases h

/-- `Signal.pure v#w`. -/
def readBitsLit (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 : Lean.Expr) :
    Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.pure ∧ lvl1 ls = true ∧ cfg.isDom x0 = true then
    (bitVecE? x1).bind fun w => (litOf? w x2).bind fun v =>
      if v < 2 ^ w ∧ 0 < w then some (⟨.bits w, .bitsLit w v⟩ : AnyTerm) else none
  else none

theorem readBitsLit_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} {r : AnyTerm}
    (h : readBitsLit cfg c ls x0 x1 x2 = some r) :
    Reads cfg r (.app (.app (.app (.const c ls) x0) x1) x2) := by
  unfold readBitsLit at h
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
      obtain rfl := litOf?_sound hv
      cases hb2
      exact ⟨rfl, g2⟩
    · cases hb2
  · cases h

/-- `~~~a` on a Bool Signal. -/
def readBoolNot (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 : Lean.Expr)
    (r2 : Option AnyTerm) : Option AnyTerm :=
  if c = ``Complement.complement ∧ lvl1 ls = true ∧ isSigBoolT cfg x0 = true ∧
      isInstDom cfg ``Sparkle.Core.Signal.instComplementSignalBool x1 = true then
    (r2.bind asBool).bind fun a => some (⟨.bool, .boolNot a⟩ : AnyTerm)
  else none

theorem readBoolNot_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} {r2 : Option AnyTerm} {r : AnyTerm}
    (ih2 : ∀ r', r2 = some r' → Reads cfg r' x2)
    (h : readBoolNot cfg c ls x0 x1 r2 = some r) :
    Reads cfg r (.app (.app (.app (.const c ls) x0) x1) x2) := by
  unfold readBoolNot at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0, h1⟩ := g
    obtain ⟨a, ha, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
    obtain rfl := asBool_some _ _ hab
    obtain ⟨qa, wa⟩ := ih2 _ hra
    subst hc
    obtain rfl := lvl1_sound hls
    obtain rfl := isSigBoolT_sound hs h0
    obtain rfl := isInstDom_sound hs h1
    cases hb1
    subst qa
    exact ⟨rfl, wa⟩
  · cases h

def read3 (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 : Lean.Expr)
    (r2 : Option AnyTerm) : Option AnyTerm :=
  alt (readBoolLit cfg c ls x0 x1 x2)
    (alt (readBitsLit cfg c ls x0 x1 x2) (readBoolNot cfg c ls x0 x1 r2))

theorem read3_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} {r2 : Option AnyTerm} {r : AnyTerm}
    (ih2 : ∀ r', r2 = some r' → Reads cfg r' x2)
    (h : read3 cfg c ls x0 x1 x2 r2 = some r) :
    Reads cfg r (.app (.app (.app (.const c ls) x0) x1) x2) := by
  unfold read3 at h
  rcases alt_some h with h | h
  · exact readBoolLit_sound hs h
  · rcases alt_some h with h | h
    · exact readBitsLit_sound hs h
    · exact readBoolNot_sound hs ih2 h

/-! ## Nodes of four arguments -/

/-- `Signal.ult a b`, `ule`, `slt`, `sle` at a literal width. -/
def readCompare (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 : Lean.Expr)
    (r2 r3 : Option AnyTerm) : Option AnyTerm :=
  if lvl0 ls = true ∧ cfg.isDom x0 = true then
    (cmpOf? c).bind fun op => (natE? x1).bind fun w =>
      (r2.bind (asBits w)).bind fun a => (r3.bind (asBits w)).bind fun b =>
        some (⟨.bool, .compare op a b⟩ : AnyTerm)
  else none

theorem readCompare_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr} {r2 r3 : Option AnyTerm} {r : AnyTerm}
    (ih2 : ∀ r', r2 = some r' → Reads cfg r' x2)
    (ih3 : ∀ r', r3 = some r' → Reads cfg r' x3)
    (h : readCompare cfg c ls x0 x1 r2 r3 = some r) :
    Reads cfg r (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) := by
  unfold readCompare at h
  split at h
  · rename_i g
    obtain ⟨hls, h0⟩ := g
    obtain ⟨op, hop, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, hw, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨a, ha, hb3⟩ := Option.bind_eq_some_iff.mp hb2
    obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
    obtain rfl := asBits_some _ _ hab
    obtain ⟨b, hb, hb4⟩ := Option.bind_eq_some_iff.mp hb3
    obtain ⟨rb, hrb, hbb⟩ := Option.bind_eq_some_iff.mp hb
    obtain rfl := asBits_some _ _ hbb
    obtain ⟨qa, wa⟩ := ih2 _ hra
    obtain ⟨qb, wb⟩ := ih3 _ hrb
    obtain ⟨hc, hne⟩ := cmpOf?_sound hop
    subst hc
    obtain rfl := lvl0_sound hls
    obtain rfl := hs.domEq _ h0
    obtain rfl := natE?_sound hw
    cases hb4
    subst qa
    subst qb
    cases op <;> first
      | exact absurd rfl hne
      | exact ⟨rfl, And.intro wa wb⟩
  · cases h

/-! ## Nodes of five arguments -/

/-- `Signal.mux c a b` at `Bool`. -/
def readMuxBool (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 : Lean.Expr)
    (r2 r3 r4 : Option AnyTerm) : Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.mux ∧ lvl1 ls = true ∧ cfg.isDom x0 = true ∧
      isConst ``Bool x1 = true then
    (r2.bind asBool).bind fun cnd => (r3.bind asBool).bind fun a =>
      (r4.bind asBool).bind fun b => some (⟨.bool, .mux cnd a b⟩ : AnyTerm)
  else none

theorem readMuxBool_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr} {r2 r3 r4 : Option AnyTerm}
    {r : AnyTerm}
    (ih2 : ∀ r', r2 = some r' → Reads cfg r' x2)
    (ih3 : ∀ r', r3 = some r' → Reads cfg r' x3)
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (h : readMuxBool cfg c ls x0 x1 r2 r3 r4 = some r) :
    Reads cfg r (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) := by
  unfold readMuxBool at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0, h1⟩ := g
    obtain ⟨cnd, hcn, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rc, hrc, hcb⟩ := Option.bind_eq_some_iff.mp hcn
    obtain rfl := asBool_some _ _ hcb
    obtain ⟨a, ha, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
    obtain rfl := asBool_some _ _ hab
    obtain ⟨b, hb, hb3⟩ := Option.bind_eq_some_iff.mp hb2
    obtain ⟨rb, hrb, hbb⟩ := Option.bind_eq_some_iff.mp hb
    obtain rfl := asBool_some _ _ hbb
    obtain ⟨qc, wc⟩ := ih2 _ hrc
    obtain ⟨qa, wa⟩ := ih3 _ hra
    obtain ⟨qb, wb⟩ := ih4 _ hrb
    subst hc
    obtain rfl := lvl1_sound hls
    obtain rfl := hs.domEq _ h0
    obtain rfl := isConst_sound h1
    cases hb3
    subst qc
    subst qa
    subst qb
    exact ⟨rfl, And.intro wc (And.intro wa wb)⟩
  · cases h

/-- `Signal.mux c a b` at `BitVec w`. -/
def readMuxBits (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 : Lean.Expr)
    (r2 r3 r4 : Option AnyTerm) : Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.mux ∧ lvl1 ls = true ∧ cfg.isDom x0 = true then
    (bitVecE? x1).bind fun w => (r2.bind asBool).bind fun cnd =>
      (r3.bind (asBits w)).bind fun a => (r4.bind (asBits w)).bind fun b =>
        some (⟨.bits w, .mux cnd a b⟩ : AnyTerm)
  else none

theorem readMuxBits_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr} {r2 r3 r4 : Option AnyTerm}
    {r : AnyTerm}
    (ih2 : ∀ r', r2 = some r' → Reads cfg r' x2)
    (ih3 : ∀ r', r3 = some r' → Reads cfg r' x3)
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (h : readMuxBits cfg c ls x0 x1 r2 r3 r4 = some r) :
    Reads cfg r (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) := by
  unfold readMuxBits at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0⟩ := g
    obtain ⟨w, hw, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cnd, hcn, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨rc, hrc, hcb⟩ := Option.bind_eq_some_iff.mp hcn
    obtain rfl := asBool_some _ _ hcb
    obtain ⟨a, ha, hb3⟩ := Option.bind_eq_some_iff.mp hb2
    obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
    obtain rfl := asBits_some _ _ hab
    obtain ⟨b, hb, hb4⟩ := Option.bind_eq_some_iff.mp hb3
    obtain ⟨rb, hrb, hbb⟩ := Option.bind_eq_some_iff.mp hb
    obtain rfl := asBits_some _ _ hbb
    obtain ⟨qc, wc⟩ := ih2 _ hrc
    obtain ⟨qa, wa⟩ := ih3 _ hra
    obtain ⟨qb, wb⟩ := ih4 _ hrb
    subst hc
    obtain rfl := lvl1_sound hls
    obtain rfl := hs.domEq _ h0
    obtain rfl := bitVecE?_sound hw
    cases hb4
    subst qc
    subst qa
    subst qb
    exact ⟨rfl, And.intro wc (And.intro wa wb)⟩
  · cases h

/-- `Signal.beq a b` at `Bool` with the standard instance. -/
def readBoolEq (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 : Lean.Expr)
    (r3 r4 : Option AnyTerm) : Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.beq ∧ lvl0 ls = true ∧ isConst ``Bool x0 = true ∧
      cfg.isDom x1 = true ∧ isBoolBEq x2 = true then
    (r3.bind asBool).bind fun a => (r4.bind asBool).bind fun b =>
      some (⟨.bool, .boolEq a b⟩ : AnyTerm)
  else none

theorem readBoolEq_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr} {r3 r4 : Option AnyTerm}
    {r : AnyTerm}
    (ih3 : ∀ r', r3 = some r' → Reads cfg r' x3)
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (h : readBoolEq cfg c ls x0 x1 x2 r3 r4 = some r) :
    Reads cfg r (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) := by
  unfold readBoolEq at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0, h1, h2⟩ := g
    obtain ⟨a, ha, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
    obtain rfl := asBool_some _ _ hab
    obtain ⟨b, hb, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨rb, hrb, hbb⟩ := Option.bind_eq_some_iff.mp hb
    obtain rfl := asBool_some _ _ hbb
    obtain ⟨qa, wa⟩ := ih3 _ hra
    obtain ⟨qb, wb⟩ := ih4 _ hrb
    subst hc
    obtain rfl := lvl0_sound hls
    obtain rfl := isConst_sound h0
    obtain rfl := hs.domEq _ h1
    obtain rfl := isBoolBEq_sound h2
    cases hb2
    subst qa
    subst qb
    exact ⟨rfl, And.intro wa wb⟩
  · cases h

/-- `Signal.beq a b` at `BitVec w` with the standard instance. -/
def readBitsEq (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 : Lean.Expr)
    (r3 r4 : Option AnyTerm) : Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.beq ∧ lvl0 ls = true ∧ cfg.isDom x1 = true then
    (bitVecE? x0).bind fun w =>
      if bitsBEq? x2 = some w then
        (r3.bind (asBits w)).bind fun a => (r4.bind (asBits w)).bind fun b =>
          some (⟨.bool, .compare .eq a b⟩ : AnyTerm)
      else none
  else none

theorem readBitsEq_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr} {r3 r4 : Option AnyTerm}
    {r : AnyTerm}
    (ih3 : ∀ r', r3 = some r' → Reads cfg r' x3)
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (h : readBitsEq cfg c ls x0 x1 x2 r3 r4 = some r) :
    Reads cfg r (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) := by
  unfold readBitsEq at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h1⟩ := g
    obtain ⟨w, hw, hb1⟩ := Option.bind_eq_some_iff.mp h
    split at hb1
    · rename_i h2
      obtain ⟨a, ha, hb2⟩ := Option.bind_eq_some_iff.mp hb1
      obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
      obtain rfl := asBits_some _ _ hab
      obtain ⟨b, hb, hb3⟩ := Option.bind_eq_some_iff.mp hb2
      obtain ⟨rb, hrb, hbb⟩ := Option.bind_eq_some_iff.mp hb
      obtain rfl := asBits_some _ _ hbb
      obtain ⟨qa, wa⟩ := ih3 _ hra
      obtain ⟨qb, wb⟩ := ih4 _ hrb
      subst hc
      obtain rfl := lvl0_sound hls
      obtain rfl := hs.domEq _ h1
      obtain rfl := bitVecE?_sound hw
      obtain rfl := bitsBEq?_sound h2
      cases hb3
      subst qa
      subst qb
      exact ⟨rfl, And.intro wa wb⟩
    · cases hb1
  · cases h

def read5 (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 : Lean.Expr)
    (r2 r3 r4 : Option AnyTerm) : Option AnyTerm :=
  alt (readMuxBool cfg c ls x0 x1 r2 r3 r4)
    (alt (readMuxBits cfg c ls x0 x1 r2 r3 r4)
      (alt (readBoolEq cfg c ls x0 x1 x2 r3 r4) (readBitsEq cfg c ls x0 x1 x2 r3 r4)))

theorem read5_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr} {r2 r3 r4 : Option AnyTerm}
    {r : AnyTerm}
    (ih2 : ∀ r', r2 = some r' → Reads cfg r' x2)
    (ih3 : ∀ r', r3 = some r' → Reads cfg r' x3)
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (h : read5 cfg c ls x0 x1 x2 r2 r3 r4 = some r) :
    Reads cfg r (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) := by
  unfold read5 at h
  rcases alt_some h with h | h
  · exact readMuxBool_sound hs ih2 ih3 ih4 h
  · rcases alt_some h with h | h
    · exact readMuxBits_sound hs ih2 ih3 ih4 h
    · rcases alt_some h with h | h
      · exact readBoolEq_sound hs ih3 ih4 h
      · exact readBitsEq_sound hs ih3 ih4 h

/-! ## Nodes of six arguments -/

/-- A canonical BitVec operator `a op b` at one literal width. -/
def readBinary (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 x3 : Lean.Expr)
    (r4 r5 : Option AnyTerm) : Option AnyTerm :=
  if lvl3 ls = true then
    (binOf? c).bind fun op => (sigBitsT? cfg x0).bind fun w =>
      if sigBitsT? cfg x1 = some w ∧ sigBitsT? cfg x2 = some w ∧
          instDomNat? cfg (binInst op) x3 = some w then
        (r4.bind (asBits w)).bind fun a => (r5.bind (asBits w)).bind fun b =>
          some (⟨.bits w, .binary op a b⟩ : AnyTerm)
      else none
  else none

theorem readBinary_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 x5 : Lean.Expr} {r4 r5 : Option AnyTerm}
    {r : AnyTerm}
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (ih5 : ∀ r', r5 = some r' → Reads cfg r' x5)
    (h : readBinary cfg c ls x0 x1 x2 x3 r4 r5 = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) := by
  unfold readBinary at h
  split at h
  · rename_i hls
    obtain ⟨op, hop, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, h0, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    split at hb2
    · rename_i g
      obtain ⟨h1, h2, h3⟩ := g
      obtain ⟨a, ha, hb3⟩ := Option.bind_eq_some_iff.mp hb2
      obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
      obtain rfl := asBits_some _ _ hab
      obtain ⟨b, hb, hb4⟩ := Option.bind_eq_some_iff.mp hb3
      obtain ⟨rb, hrb, hbb⟩ := Option.bind_eq_some_iff.mp hb
      obtain rfl := asBits_some _ _ hbb
      obtain ⟨qa, wa⟩ := ih4 _ hra
      obtain ⟨qb, wb⟩ := ih5 _ hrb
      have hm := binOf?_sound hop
      subst hm
      obtain rfl := lvl3_sound hls
      obtain rfl := sigBitsT?_sound hs h0
      obtain rfl := sigBitsT?_sound hs h1
      obtain rfl := sigBitsT?_sound hs h2
      obtain rfl := instDomNat?_sound hs h3
      cases hb4
      subst qa
      subst qb
      exact ⟨rfl, And.intro wa wb⟩
    · cases hb2
  · cases h

/-- A canonical Bool operator `a &&& b`, `|||`, `^^^`. -/
def readBoolBinary (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level)
    (x0 x1 x2 x3 : Lean.Expr) (r4 r5 : Option AnyTerm) : Option AnyTerm :=
  if lvl3 ls = true ∧ isSigBoolT cfg x0 = true ∧ isSigBoolT cfg x1 = true ∧
      isSigBoolT cfg x2 = true then
    (boolBinOf? c).bind fun k =>
      if isInstDom cfg (signalBoolBinInst k) x3 = true then
        (r4.bind asBool).bind fun a => (r5.bind asBool).bind fun b =>
          some (⟨.bool, .boolBinary k a b⟩ : AnyTerm)
      else none
  else none

theorem readBoolBinary_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 x5 : Lean.Expr} {r4 r5 : Option AnyTerm}
    {r : AnyTerm}
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (ih5 : ∀ r', r5 = some r' → Reads cfg r' x5)
    (h : readBoolBinary cfg c ls x0 x1 x2 x3 r4 r5 = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) := by
  unfold readBoolBinary at h
  split at h
  · rename_i g
    obtain ⟨hls, h0, h1, h2⟩ := g
    obtain ⟨k, hk, hb1⟩ := Option.bind_eq_some_iff.mp h
    split at hb1
    · rename_i h3
      obtain ⟨a, ha, hb2⟩ := Option.bind_eq_some_iff.mp hb1
      obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
      obtain rfl := asBool_some _ _ hab
      obtain ⟨b, hb, hb3⟩ := Option.bind_eq_some_iff.mp hb2
      obtain ⟨rb, hrb, hbb⟩ := Option.bind_eq_some_iff.mp hb
      obtain rfl := asBool_some _ _ hbb
      obtain ⟨qa, wa⟩ := ih4 _ hra
      obtain ⟨qb, wb⟩ := ih5 _ hrb
      have hm := boolBinOf?_sound hk
      subst hm
      obtain rfl := lvl3_sound hls
      obtain rfl := isSigBoolT_sound hs h0
      obtain rfl := isSigBoolT_sound hs h1
      obtain rfl := isSigBoolT_sound hs h2
      obtain rfl := isInstDom_sound hs h3
      cases hb3
      subst qa
      subst qb
      exact ⟨rfl, And.intro wa wb⟩
    · cases hb1
  · cases h

/-- A concatenation `a ++ b` of two BitVec Signals, the result width the
literal of the sum. -/
def readConcat (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 x3 : Lean.Expr)
    (r4 r5 : Option AnyTerm) : Option AnyTerm :=
  if c = ``HAppend.hAppend ∧ lvl3 ls = true then
    (sigBitsT? cfg x0).bind fun m => (sigBitsT? cfg x1).bind fun n =>
      if sigBitsT? cfg x2 = some (m + n) ∧ isConcatInst cfg m n x3 = true then
        (r4.bind (asBits m)).bind fun a => (r5.bind (asBits n)).bind fun b =>
          some (⟨.bits (m + n), .concat a b⟩ : AnyTerm)
      else none
  else none

theorem readConcat_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 x5 : Lean.Expr} {r4 r5 : Option AnyTerm}
    {r : AnyTerm}
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (ih5 : ∀ r', r5 = some r' → Reads cfg r' x5)
    (h : readConcat cfg c ls x0 x1 x2 x3 r4 r5 = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) := by
  unfold readConcat at h
  split at h
  · rename_i g
    obtain ⟨hc, hls⟩ := g
    obtain ⟨m, h0, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨n, h1, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    split at hb2
    · rename_i g2
      obtain ⟨h2, h3⟩ := g2
      obtain ⟨a, ha, hb3⟩ := Option.bind_eq_some_iff.mp hb2
      obtain ⟨ra, hra, hab⟩ := Option.bind_eq_some_iff.mp ha
      obtain rfl := asBits_some _ _ hab
      obtain ⟨b, hb, hb4⟩ := Option.bind_eq_some_iff.mp hb3
      obtain ⟨rb, hrb, hbb⟩ := Option.bind_eq_some_iff.mp hb
      obtain rfl := asBits_some _ _ hbb
      obtain ⟨qa, wa⟩ := ih4 _ hra
      obtain ⟨qb, wb⟩ := ih5 _ hrb
      subst hc
      obtain rfl := lvl3_sound hls
      obtain rfl := sigBitsT?_sound hs h0
      obtain rfl := sigBitsT?_sound hs h1
      obtain rfl := sigBitsT?_sound hs h2
      obtain rfl := isConcatInst_sound hs h3
      cases hb4
      subst qa
      subst qb
      exact ⟨rfl, And.intro wa wb⟩
    · cases hb2
  · cases h

def read6 (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 x3 : Lean.Expr)
    (r4 r5 : Option AnyTerm) : Option AnyTerm :=
  alt (readBinary cfg c ls x0 x1 x2 x3 r4 r5)
    (alt (readBoolBinary cfg c ls x0 x1 x2 x3 r4 r5) (readConcat cfg c ls x0 x1 x2 x3 r4 r5))

theorem read6_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name}
    {ls : List Lean.Level} {x0 x1 x2 x3 x4 x5 : Lean.Expr} {r4 r5 : Option AnyTerm}
    {r : AnyTerm}
    (ih4 : ∀ r', r4 = some r' → Reads cfg r' x4)
    (ih5 : ∀ r', r5 = some r' → Reads cfg r' x5)
    (h : read6 cfg c ls x0 x1 x2 x3 r4 r5 = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) := by
  unfold read6 at h
  rcases alt_some h with h | h
  · exact readBinary_sound hs ih4 ih5 h
  · rcases alt_some h with h | h
    · exact readBoolBinary_sound hs ih4 ih5 h
    · exact readConcat_sound hs ih4 ih5 h

/-! ## The reader

An application is read from its spine: the head constant, and every argument
with its own reading. The recursion is on the expression, one constructor at
a time; the node kinds live in the non-recursive `readNode`. -/

/-- An argument of a node and its reading. -/
abbrev Arg := Lean.Expr × Option AnyTerm

/-- `f` applied to the arguments. -/
def apps : Lean.Expr → List Arg → Lean.Expr
  | f, [] => f
  | f, p :: rest => apps (.app f p.1) rest

/-- A constant applied to arguments, by the number of arguments. -/
def readNode (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) : List Arg → Option AnyTerm
  | [x0, x1, x2] => read3 cfg c ls x0.1 x1.1 x2.1 x2.2
  | [x0, x1, x2, x3] => readCompare cfg c ls x0.1 x1.1 x2.2 x3.2
  | [x0, x1, x2, x3, x4] => read5 cfg c ls x0.1 x1.1 x2.1 x2.2 x3.2 x4.2
  | [x0, x1, x2, x3, x4, x5] => read6 cfg c ls x0.1 x1.1 x2.1 x3.1 x4.2 x5.2
  | _ => none

theorem readNode_sound {cfg : Cfg} (hs : cfg.Sound) {c : Lean.Name} {ls : List Lean.Level}
    {args : List Arg} {r : AnyTerm}
    (ha : ∀ p, p ∈ args → ∀ r', p.2 = some r' → Reads cfg r' p.1)
    (h : readNode cfg c ls args = some r) : Reads cfg r (apps (.const c ls) args) := by
  revert ha h
  unfold readNode
  split
  · rename_i x0 x1 x2
    intro ha h
    exact read3_sound hs (ha x2 (by simp)) h
  · rename_i x0 x1 x2 x3
    intro ha h
    exact readCompare_sound hs (ha x2 (by simp)) (ha x3 (by simp)) h
  · rename_i x0 x1 x2 x3 x4
    intro ha h
    exact read5_sound hs (ha x2 (by simp)) (ha x3 (by simp)) (ha x4 (by simp)) h
  · rename_i x0 x1 x2 x3 x4 x5
    intro ha h
    exact read6_sound hs (ha x4 (by simp)) (ha x5 (by simp)) h
  · intro _ h
    cases h

/-- The reading of an expression (first component), and the reading of the
expression applied to further arguments (second component). -/
def go (cfg : Cfg) : Lean.Expr → Option AnyTerm × (List Arg → Option AnyTerm)
  | .bvar i => (readInput cfg i, fun _ => none)
  | .const c ls => (none, fun args => readNode cfg c ls args)
  | .app f a =>
    let gf := (go cfg f).2
    let ra := (go cfg a).1
    (gf [(a, ra)], fun args => gf ((a, ra) :: args))
  | _ => (none, fun _ => none)

/-- **The reader.** Total, by structural recursion on the expression; no
type inference, no environment. -/
def readTerm (cfg : Cfg) (e : Lean.Expr) : Option AnyTerm := (go cfg e).1

/-- **The reader's induction.** A property of readings that holds of the
leaves the leaf reader accepts and passes through the node reader holds of
every reading — of the expression itself and of the expression applied to
arguments that have it. -/
theorem go_induct (cfg : Cfg) (P : AnyTerm → Lean.Expr → Prop)
    (leaf : ∀ i r, readInput cfg i = some r → P r (.bvar i))
    (node : ∀ c ls (args : List Arg) r,
      (∀ p, p ∈ args → ∀ r', p.2 = some r' → P r' p.1) →
      readNode cfg c ls args = some r → P r (apps (.const c ls) args))
    (e : Lean.Expr) :
    (∀ r, (go cfg e).1 = some r → P r e) ∧
    (∀ (args : List Arg) r, (∀ p, p ∈ args → ∀ r', p.2 = some r' → P r' p.1) →
      (go cfg e).2 args = some r → P r (apps e args)) := by
  induction e with
  | bvar i => exact ⟨fun r h => leaf i r h, fun _ _ _ h => none_ne h⟩
  | const c ls => exact ⟨fun _ h => none_ne h, fun args r ha h => node c ls args r ha h⟩
  | app f a ihf iha =>
    refine ⟨fun r h => ?_, fun args r ha h => ?_⟩
    · have hx : ∀ p, p ∈ [((a, (go cfg a).1) : Arg)] → ∀ r', p.2 = some r' → P r' p.1 := by
        intro p hp r' hr'
        have hp' : p = (a, (go cfg a).1) := List.mem_singleton.mp hp
        subst hp'
        exact iha.1 r' hr'
      exact ihf.2 [(a, (go cfg a).1)] r hx h
    · have hx : ∀ p, p ∈ ((a, (go cfg a).1) : Arg) :: args →
          ∀ r', p.2 = some r' → P r' p.1 := by
        intro p hp r' hr'
        rcases List.mem_cons.mp hp with hp' | hp'
        · subst hp'
          exact iha.1 r' hr'
        · exact ha p hp' r' hr'
      exact ihf.2 ((a, (go cfg a).1) :: args) r hx h
  | _ => exact ⟨fun _ h => none_ne h, fun _ _ _ h => none_ne h⟩

theorem readTerm_induct (cfg : Cfg) (P : AnyTerm → Lean.Expr → Prop)
    (leaf : ∀ i r, readInput cfg i = some r → P r (.bvar i))
    (node : ∀ c ls (args : List Arg) r,
      (∀ p, p ∈ args → ∀ r', p.2 = some r' → P r' p.1) →
      readNode cfg c ls args = some r → P r (apps (.const c ls) args))
    (e : Lean.Expr) (r : AnyTerm) (h : readTerm cfg e = some r) : P r e :=
  (go_induct cfg P leaf node e).1 r h

/-- Every reading is a reading (`Reads`). -/
theorem readTerm_reads (cfg : Cfg) (hs : cfg.Sound) (e : Lean.Expr) (r : AnyTerm)
    (h : readTerm cfg e = some r) : Reads cfg r e :=
  readTerm_induct cfg (Reads cfg) (fun _ _ h => readInput_sound hs h)
    (fun _ _ _ _ ha h => readNode_sound hs ha h) e r h

/-- **Reader soundness.** For every expression: if the reader returns a term,
the expression is the quotation of that term, and the term is well formed.
No premise about the expression. -/
theorem readTerm_sound (cfg : Cfg) (hs : cfg.Sound) (e : Lean.Expr) (r : AnyTerm)
    (h : readTerm cfg e = some r) :
    quote cfg.dom cfg.bools cfg.bits r.2 = e ∧ r.2.WF cfg.kb cfg.kv cfg.vw :=
  ⟨(readTerm_reads cfg hs e r h).eq, (readTerm_reads cfg hs e r h).wf⟩

end Tools.ShippingReaderTerm
