import Tools.ShippingReaderNodes2

/-! # The reader on the applicative lifts (`appCompare`, `appBool`, `appBool2`) (G3)

The three kinds the eighteen-kind reader (`readTerm2`) does not read quote to

    Signal.ap dom ty Bool (Signal.map dom ty (ty → Bool) (fun x1 x2 => body) a) b

Their first operand `a` is the last argument of the node's fourth ARGUMENT,
and `goWith` hands a node the readings of its own arguments only.

## How it is done here — and how that differs from the announced design

Round 11 announced a third `goWith` component (the reading of an argument's
last argument). That changes `Arg`, `goWith`, `goWith_induct` and every
projection in seven files that are built and integrated. This file reaches
the same node WITHOUT touching them, by LEVELS:

* `readNode3 sub cfg`: the eighteen kinds, else the applicative node, whose
  first operand is read by a given reader `sub` applied to the operand's
  EXPRESSION (the node has it: it is the argument of its fourth argument);
* `readN cfg 0 = readTerm2 cfg`, and
  `readN cfg (k+1) = readWith (readInput cfg) (readNode3 (readN cfg k) cfg)`.

So level `k+1` reads an applicative lift whose FIRST operand level `k`
reads; the second operand and every other position are read at the same
level. Level `k` therefore reads every body in which applicative lifts are
nested at most `k` deep THROUGH FIRST OPERANDS (a lift inside a second
operand, a mux arm, … costs no level). Cost: an operand at depth `d` of
such a chain is read once per level above it — at most `(k+1) ·` the size.

The node reader is strict: the constant, the level list, the domain (the
configuration's test), the two type arguments, and the WHOLE head of the
fourth argument (`Signal.map dom ty (ty → Bool) (fun x1 x2 => body)`,
binder names and binder infos included) are compared with what `quote`
writes, by the compiler's structural `exprDecEq`; the operator is the one
whose quoted head it is.

Proved
* `readN_reads` / `readN_sound`: for EVERY level, configuration with sound
  leaf tables and expression — a returned term quotes back to the expression
  and is well formed. No premise about the expression.
* `readN_expr_sound`: the same under binders with the structural domain
  test: the reading is the only hypothesis.

NOT proved here
* completeness on the three kinds (`readN cfg k (quote … t) = some t` for a
  term of lift depth `≤ k`), and with it injectivity of `quote` on all 21
  kinds;
* that `readN cfg (k+1)` extends `readN cfg k` (a reading at a lower level
  is the reading at every higher level). Expected — `readNode3` tries the
  eighteen kinds first and the kinds' head constants are disjoint — but it
  needs a monotonicity lemma for `goWith` in the node reader;
* that the hierarchical recognisers' other shapes are read (instance leaves,
  register / memory roots): unchanged.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingReaderApp
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingReaderTerm Tools.ShippingReaderInputs Tools.ShippingReaderNodes2
open Tools.ShippingMixedSourceBridge (inputExpr)

/-! ## Structural equality, and choosing an operator by its quoted head -/

/-- Structural equality of expressions (the compiler's `exprDecEq`). -/
def eqE (a b : Lean.Expr) : Bool :=
  @decide (a = b) (Sparkle.Compiler.ExprDecEq.exprDecEq a b)

theorem eqE_sound {a b : Lean.Expr} (h : eqE a b = true) : a = b :=
  @of_decide_eq_true (a = b) (Sparkle.Compiler.ExprDecEq.exprDecEq a b) h

/-- The first key of the list whose expression `f` is. -/
def pickBy {α : Type} (g : α → Lean.Expr) (f : Lean.Expr) : List α → Option α
  | [] => none
  | x :: rest => if eqE f (g x) = true then some x else pickBy g f rest

theorem pickBy_sound {α : Type} {g : α → Lean.Expr} {f : Lean.Expr} :
    ∀ (l : List α) (x : α), pickBy g f l = some x → f = g x
  | [], _, h => none_ne h
  | y :: rest, x, h => by
    have h' : (if eqE f (g y) = true then some y else pickBy g f rest) = some x := h
    split at h'
    · rename_i hg
      cases h'
      exact eqE_sound hg
    · exact pickBy_sound rest x h'

/-- The head of an applicative lift's first operand:
`Signal.map dom ty (ty → Bool) (fun x1 x2 => body)`, as `appE` writes it. -/
def mapHeadE (dom ty body : Lean.Expr) : Lean.Expr :=
  Lean.mkApp4 (.const ``Sparkle.Core.Signal.Signal.map [.zero]) dom ty
    (.forallE `a ty (.const ``Bool []) .default) (appLamE ty body)

/-- `appE`, with the node and the head of its fourth argument apart. -/
theorem appE_eq (dom ty body a b : Lean.Expr) :
    appE dom ty body a b =
      .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap [.zero]) dom) ty)
        (.const ``Bool [])) (.app (mapHeadE dom ty body) a)) b := rfl

/-- The Bool operator whose lifted head `f` is. -/
def boolOp? (dom f : Lean.Expr) : Option SignalBoolBinKind :=
  pickBy (fun op => mapHeadE dom (.const ``Bool []) (appBoolBodyE op)) f [.band, .bor, .bxor]

theorem boolOp?_sound {dom f : Lean.Expr} {op : SignalBoolBinKind}
    (h : boolOp? dom f = some op) : f = mapHeadE dom (.const ``Bool []) (appBoolBodyE op) :=
  pickBy_sound (g := fun op => mapHeadE dom (.const ``Bool []) (appBoolBodyE op))
    [.band, .bor, .bxor] op h

/-- The two-level Bool body whose lifted head `f` is. -/
def bool2Op? (dom f : Lean.Expr) : Option AppBool2 :=
  pickBy (fun op => mapHeadE dom (.const ``Bool []) (appBool2BodyE op)) f
    [.andNot, .notAnd, .nor]

theorem bool2Op?_sound {dom f : Lean.Expr} {op : AppBool2}
    (h : bool2Op? dom f = some op) : f = mapHeadE dom (.const ``Bool []) (appBool2BodyE op) :=
  pickBy_sound (g := fun op => mapHeadE dom (.const ``Bool []) (appBool2BodyE op))
    [.andNot, .notAnd, .nor] op h

/-- The comparison at width `w` whose lifted head `f` is. -/
def cmpOp? (dom : Lean.Expr) (w : Nat) (f : Lean.Expr) : Option SignalCompareKind :=
  pickBy (fun op => mapHeadE dom (bitVecE w) (appCompareBodyE op w)) f
    [.ult, .ule, .slt, .sle, .eq]

theorem cmpOp?_sound {dom f : Lean.Expr} {w : Nat} {op : SignalCompareKind}
    (h : cmpOp? dom w f = some op) : f = mapHeadE dom (bitVecE w) (appCompareBodyE op w) :=
  pickBy_sound (g := fun op => mapHeadE dom (bitVecE w) (appCompareBodyE op w))
    [.ult, .ule, .slt, .sle, .eq] op h

/-- The function and the argument of an application. -/
def lastApp? : Lean.Expr → Option (Lean.Expr × Lean.Expr)
  | .app f a => some (f, a)
  | _ => none

theorem lastApp?_sound {e : Lean.Expr} {fa : Lean.Expr × Lean.Expr}
    (h : lastApp? e = some fa) : e = .app fa.1 fa.2 := by
  revert h
  unfold lastApp?
  split
  · intro h
    cases h
    rfl
  · intro h; cases h

section
variable {cfg : Cfg}

/-! ## The three kinds, after the node's constant, levels, domain and result
type are known. `x1` is the element type, `f` the head of the fourth
argument, `ra` / `rb` the readings of the operands. -/

def readApBool (cfg : Cfg) (x1 f : Lean.Expr) (ra rb : Option AnyTerm) : Option AnyTerm :=
  if isConst ``Bool x1 = true then
    (boolOp? cfg.dom f).bind fun op =>
      (ra.bind asBool).bind fun a => (rb.bind asBool).bind fun b =>
        some (⟨.bool, .appBool op a b⟩ : AnyTerm)
  else none

theorem readApBool_sound {x1 f a b : Lean.Expr} {ra rb : Option AnyTerm} {r : AnyTerm}
    (iha : ∀ r', ra = some r' → Reads cfg r' a)
    (ihb : ∀ r', rb = some r' → Reads cfg r' b)
    (h : readApBool cfg x1 f ra rb = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap [.zero]) cfg.dom) x1)
        (.const ``Bool [])) (.app f a)) b) := by
  unfold readApBool at h
  split at h
  · rename_i g
    obtain ⟨op, hop, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ta, hta, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨ra', hra, hab⟩ := Option.bind_eq_some_iff.mp hta
    obtain rfl := asBool_some _ _ hab
    obtain ⟨tb, htb, hb3⟩ := Option.bind_eq_some_iff.mp hb2
    obtain ⟨rb', hrb, hbb⟩ := Option.bind_eq_some_iff.mp htb
    obtain rfl := asBool_some _ _ hbb
    obtain ⟨qa, wa⟩ := iha _ hra
    obtain ⟨qb, wb⟩ := ihb _ hrb
    obtain rfl := isConst_sound g
    obtain rfl := boolOp?_sound hop
    cases hb3
    subst qa
    subst qb
    exact ⟨rfl, And.intro wa wb⟩
  · cases h

def readApBool2 (cfg : Cfg) (x1 f : Lean.Expr) (ra rb : Option AnyTerm) : Option AnyTerm :=
  if isConst ``Bool x1 = true then
    (bool2Op? cfg.dom f).bind fun op =>
      (ra.bind asBool).bind fun a => (rb.bind asBool).bind fun b =>
        some (⟨.bool, .appBool2 op a b⟩ : AnyTerm)
  else none

theorem readApBool2_sound {x1 f a b : Lean.Expr} {ra rb : Option AnyTerm} {r : AnyTerm}
    (iha : ∀ r', ra = some r' → Reads cfg r' a)
    (ihb : ∀ r', rb = some r' → Reads cfg r' b)
    (h : readApBool2 cfg x1 f ra rb = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap [.zero]) cfg.dom) x1)
        (.const ``Bool [])) (.app f a)) b) := by
  unfold readApBool2 at h
  split at h
  · rename_i g
    obtain ⟨op, hop, hb1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ta, hta, hb2⟩ := Option.bind_eq_some_iff.mp hb1
    obtain ⟨ra', hra, hab⟩ := Option.bind_eq_some_iff.mp hta
    obtain rfl := asBool_some _ _ hab
    obtain ⟨tb, htb, hb3⟩ := Option.bind_eq_some_iff.mp hb2
    obtain ⟨rb', hrb, hbb⟩ := Option.bind_eq_some_iff.mp htb
    obtain rfl := asBool_some _ _ hbb
    obtain ⟨qa, wa⟩ := iha _ hra
    obtain ⟨qb, wb⟩ := ihb _ hrb
    obtain rfl := isConst_sound g
    obtain rfl := bool2Op?_sound hop
    cases hb3
    subst qa
    subst qb
    exact ⟨rfl, And.intro wa wb⟩
  · cases h

def readApCmp (cfg : Cfg) (x1 f : Lean.Expr) (ra rb : Option AnyTerm) : Option AnyTerm :=
  (bitVecE? x1).bind fun w => (cmpOp? cfg.dom w f).bind fun op =>
    (ra.bind (asBits w)).bind fun a => (rb.bind (asBits w)).bind fun b =>
      some (⟨.bool, .appCompare op a b⟩ : AnyTerm)

theorem readApCmp_sound {x1 f a b : Lean.Expr} {ra rb : Option AnyTerm} {r : AnyTerm}
    (iha : ∀ r', ra = some r' → Reads cfg r' a)
    (ihb : ∀ r', rb = some r' → Reads cfg r' b)
    (h : readApCmp cfg x1 f ra rb = some r) :
    Reads cfg r
      (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap [.zero]) cfg.dom) x1)
        (.const ``Bool [])) (.app f a)) b) := by
  unfold readApCmp at h
  obtain ⟨w, hw, hb0⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨op, hop, hb1⟩ := Option.bind_eq_some_iff.mp hb0
  obtain ⟨ta, hta, hb2⟩ := Option.bind_eq_some_iff.mp hb1
  obtain ⟨ra', hra, hab⟩ := Option.bind_eq_some_iff.mp hta
  obtain rfl := asBits_some _ _ hab
  obtain ⟨tb, htb, hb3⟩ := Option.bind_eq_some_iff.mp hb2
  obtain ⟨rb', hrb, hbb⟩ := Option.bind_eq_some_iff.mp htb
  obtain rfl := asBits_some _ _ hbb
  obtain ⟨qa, wa⟩ := iha _ hra
  obtain ⟨qb, wb⟩ := ihb _ hrb
  obtain rfl := bitVecE?_sound hw
  obtain rfl := cmpOp?_sound hop
  cases hb3
  subst qa
  subst qb
  exact ⟨rfl, And.intro wa wb⟩

/-- An applicative lift, given the head `f` of its fourth argument and the
readings of its two operands. -/
def readAp (cfg : Cfg) (c : Lean.Name) (ls : List Lean.Level) (x0 x1 x2 f : Lean.Expr)
    (ra rb : Option AnyTerm) : Option AnyTerm :=
  if c = ``Sparkle.Core.Signal.Signal.ap ∧ lvl1 ls = true ∧ cfg.isDom x0 = true ∧
      isConst ``Bool x2 = true then
    alt (readApBool cfg x1 f ra rb) (alt (readApBool2 cfg x1 f ra rb) (readApCmp cfg x1 f ra rb))
  else none

theorem readAp_sound (hs : cfg.Sound) {c : Lean.Name} {ls : List Lean.Level}
    {x0 x1 x2 f a b : Lean.Expr} {ra rb : Option AnyTerm} {r : AnyTerm}
    (iha : ∀ r', ra = some r' → Reads cfg r' a)
    (ihb : ∀ r', rb = some r' → Reads cfg r' b)
    (h : readAp cfg c ls x0 x1 x2 f ra rb = some r) :
    Reads cfg r (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) (.app f a)) b) := by
  unfold readAp at h
  split at h
  · rename_i g
    obtain ⟨hc, hls, h0, h2⟩ := g
    subst hc
    obtain rfl := lvl1_sound hls
    obtain rfl := hs.domEq _ h0
    obtain rfl := isConst_sound h2
    rcases alt_some h with h1 | h1
    · exact readApBool_sound iha ihb h1
    · rcases alt_some h1 with h3 | h3
      · exact readApBool2_sound iha ihb h3
      · exact readApCmp_sound iha ihb h3
  · cases h

/-- The applicative node: five arguments, the fourth an application whose
argument `sub` reads. -/
def readApNode (sub : Lean.Expr → Option AnyTerm) (cfg : Cfg) (c : Lean.Name)
    (ls : List Lean.Level) : List Arg → Option AnyTerm
  | [x0, x1, x2, x3, x4] =>
    (lastApp? x3.1).bind fun fa => readAp cfg c ls x0.1 x1.1 x2.1 fa.1 (sub fa.2) x4.2
  | _ => none

theorem readApNode_sound (hs : cfg.Sound) {sub : Lean.Expr → Option AnyTerm}
    (hsub : ∀ e r, sub e = some r → Reads cfg r e) {c : Lean.Name} {ls : List Lean.Level}
    {args : List Arg} {r : AnyTerm}
    (ha : ∀ p, p ∈ args → ∀ r', p.2 = some r' → Reads cfg r' p.1)
    (h : readApNode sub cfg c ls args = some r) : Reads cfg r (apps (.const c ls) args) := by
  revert ha h
  unfold readApNode
  split
  · rename_i x0 x1 x2 x3 x4
    intro ha h
    obtain ⟨fa, hfa, hb1⟩ := Option.bind_eq_some_iff.mp h
    have he : x3.1 = .app fa.1 fa.2 := lastApp?_sound hfa
    have hr : Reads cfg r
        (.app (.app (.app (.app (.app (.const c ls) x0.1) x1.1) x2.1) (.app fa.1 fa.2)) x4.1) :=
      readAp_sound hs (ra := sub fa.2) (rb := x4.2) (fun r' hr' => hsub _ _ hr')
        (ha x4 (by simp)) hb1
    have e1 : apps (.const c ls) [x0, x1, x2, x3, x4] =
        .app (.app (.app (.app (.app (.const c ls) x0.1) x1.1) x2.1) x3.1) x4.1 := rfl
    have e2 : apps (.const c ls) [x0, x1, x2, x3, x4] =
        .app (.app (.app (.app (.app (.const c ls) x0.1) x1.1) x2.1) (.app fa.1 fa.2)) x4.1 :=
      e1.trans (congrArg
        (fun z => Lean.Expr.app (.app (.app (.app (.app (.const c ls) x0.1) x1.1) x2.1) z) x4.1) he)
    rw [e2]
    exact hr
  · intro _ h
    cases h

/-- The eighteen kinds, else the applicative lifts with first operands read
by `sub`. -/
def readNode3 (sub : Lean.Expr → Option AnyTerm) (cfg : Cfg) (c : Lean.Name)
    (ls : List Lean.Level) (args : List Arg) : Option AnyTerm :=
  alt (readNode2 cfg c ls args) (readApNode sub cfg c ls args)

theorem readNode3_sound (hs : cfg.Sound) {sub : Lean.Expr → Option AnyTerm}
    (hsub : ∀ e r, sub e = some r → Reads cfg r e) {c : Lean.Name} {ls : List Lean.Level}
    {args : List Arg} {r : AnyTerm}
    (ha : ∀ p, p ∈ args → ∀ r', p.2 = some r' → Reads cfg r' p.1)
    (h : readNode3 sub cfg c ls args = some r) : Reads cfg r (apps (.const c ls) args) := by
  unfold readNode3 at h
  rcases alt_some h with h1 | h1
  · exact readNode2_sound hs ha h1
  · exact readApNode_sound hs hsub ha h1

end

/-- **The reader by levels**: twenty-one node kinds; level `k` reads
applicative lifts nested at most `k` deep through first operands. -/
def readN (cfg : Cfg) : Nat → Lean.Expr → Option AnyTerm
  | 0 => readTerm2 cfg
  | k + 1 => readWith (readInput cfg) (readNode3 (readN cfg k) cfg)

theorem readN_reads (cfg : Cfg) (hs : cfg.Sound) :
    ∀ (k : Nat) (e : Lean.Expr) (r : AnyTerm), readN cfg k e = some r → Reads cfg r e
  | 0, e, r, h => readTerm2_reads cfg hs e r h
  | k + 1, e, r, h =>
    readWith_induct (readInput cfg) (readNode3 (readN cfg k) cfg) (Reads cfg)
      (fun _ _ h => readInput_sound hs h)
      (fun _ _ _ _ ha h => readNode3_sound hs (readN_reads cfg hs k) ha h) e r h

/-- **Soundness of the reader at every level**, for every expression. -/
theorem readN_sound (cfg : Cfg) (hs : cfg.Sound) (k : Nat) (e : Lean.Expr) (r : AnyTerm)
    (h : readN cfg k e = some r) :
    quote cfg.dom cfg.bools cfg.bits r.2 = e ∧ r.2.WF cfg.kb cfg.kv cfg.vw :=
  ⟨(readN_reads cfg hs k e r h).eq, (readN_reads cfg hs k e r h).wf⟩

/-- Soundness under binders, with the structural domain test: the reading is
the only hypothesis. -/
theorem readN_expr_sound (dom : Lean.Expr) (ks : List MixedGateBinder) (k : Nat)
    (e : Lean.Expr) (r : AnyTerm)
    (h : readN (kindsCfg dom (isExpr dom) ks) k e = some r) :
    quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) r.2 = e ∧
      r.2.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0) :=
  readN_sound (kindsCfg dom (isExpr dom) ks)
    (kindsCfg_sound dom (isExpr dom) (isExpr_sound dom) ks) k e r h

end Tools.ShippingReaderApp
