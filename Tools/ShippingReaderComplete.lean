import Tools.ShippingReaderInputs

/-! # Reader completeness on the quotations of the core node kinds (G3)

`readTerm_sound` says a term the reader returns quotes back to the
expression. This file is the converse on the image of `quote`: for every
well-formed term `t` built from the eleven node kinds `readTerm` reads
(`core t`),

  `readTerm cfg (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩`

(`readTerm_quote`). With it the strict reader accepts every body that is the
quotation of such a term, and returns THAT term: on these kinds `quote` is
injective on well-formed terms (`quote_injective`).

The condition on the configuration is `Complete` — stated exactly:
* `domOk`: the domain test accepts the domain expression;
* `boolOut`: Bool input `j` (in range) is written as a loose bound variable
  the Bool table maps back to `j`;
* `bitsOut`: BitVec input `j` (in range, at its positive declared width) is
  written as a loose bound variable that the Bool table does NOT claim and
  the BitVec table maps back to `(width, j)`.
Inputs are bound variables, so no input is a node (a node is an
application); nothing else is asked. `kindsCfg_complete` proves `Complete`
for the configuration of the machine endpoints from facts about the binder
list (`KindsOK`).

What is proved, per node kind: each of `boolInput`, `bitsInput`, `boolLit`,
`bitsLit`, `boolNot`, `mux` (both sorts), `binary`, `boolBinary`, `compare`
(five kinds), `boolEq`, `concat` is read back as itself; no kind's quotation
is read as another kind (the earlier alternatives of the node reader return
`none` on it — by a differing head constant, or, where the head is shared
(`mux`, `Signal.beq`, `Signal.pure`, and `&&& ||| ^^^` between `binary` and
`boolBinary`), by a differing type argument). No pair of distinct terms with
one quotation was met among these kinds.

What is NOT proved here
* The ten kinds `readTerm` does not read (`core` is `False` on them).
* Nothing about bodies that are not quotations.
* `KindsOK` (the binder list's positions and widths are consistent with the
  kinds) is a premise of `kindsCfg_complete`; it is a fact about `posB` /
  `posV` / `widV` of every binder list with positive widths, not proved yet.

Uses of evaluation the integrator should watch: `ne_compl_pure`,
`ne_beq_mux` (`decide` on two `Name` literals), `cmpOf?_compareName`,
`binOf?_binMethod`, `boolBinOf?_name`, `binOf?_append` (`rfl` through `Name`
comparisons). -/
namespace Tools.ShippingReaderComplete
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingReaderTerm Tools.ShippingReaderInputs
open Tools.ShippingMixedSourceBridge (inputExpr)

/-! ## Small tools -/

theorem false_ne {Q : Prop} (h : false = true) : Q := by
  cases h

theorem alt_none_left {α : Type} {a b : Option α} (h : a = none) : alt a b = b := by
  subst h
  rfl

theorem alt_some_left {α : Type} {a b : Option α} {r : α} (h : a = some r) :
    alt a b = some r := by
  subst h
  rfl

theorem bind_none_of {α β : Type} {o : Option α} (h : o = none) (f : α → Option β) :
    o.bind f = none := by
  subst h
  rfl

theorem bind_bind_none {α β γ : Type} (o : Option α) (x : Option β)
    (g : α → β → Option γ) (hx : x = none) : (o.bind fun a => x.bind (g a)) = none := by
  subst hx
  cases o <;> rfl

theorem asBits_self (w : Nat) (a : Term (.bits w)) : asBits w ⟨.bits w, a⟩ = some a := by
  show (if h : w = w then some (castBits h a) else none) = some a
  exact (dif_pos rfl).trans rfl

/-! ## The destructors on the forms `quote` writes -/

theorem natE?_natE (n : Nat) : natE? (natE n) = some n := by
  show (if n = n then some n else none) = some n
  exact if_pos rfl

theorem bitVecE?_bitVecE (n : Nat) : bitVecE? (bitVecE n) = some n :=
  natE?_natE n

theorem isConst_self (n : Lean.Name) : isConst n (.const n []) = true := by
  show decide (n = n) = true
  exact decide_eq_true rfl

theorem litOf?_litE (w v : Nat) : litOf? w (litE w v) = some v := by
  show (if natE? (natE w) = some w then natE? (natE v) else none) = some v
  exact (if_pos (natE?_natE w)).trans (natE?_natE v)

theorem bitsBEq?_self (w : Nat) : bitsBEq? (bitsBEqE w) = some w := by
  show ((bitVecE? (bitVecE w)).bind fun w' =>
    if natE? (natE w) = some w' then some w' else none) = some w
  exact Option.bind_eq_some_iff.mpr ⟨w, bitVecE?_bitVecE w, if_pos (natE?_natE w)⟩

theorem cmpOf?_compareName {op : SignalCompareKind} (h : op ≠ .eq) :
    cmpOf? (compareName op) = some op := by
  cases op
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd rfl h

theorem binOf?_binMethod (op : Binary) : binOf? (binMethod op) = some op := by
  cases op <;> rfl

theorem boolBinOf?_name (k : SignalBoolBinKind) :
    boolBinOf? (signalBoolBinName k) = some k := by
  cases k <;> rfl

theorem binOf?_append : binOf? ``HAppend.hAppend = none := rfl

theorem ne_compl_pure : ``Complement.complement ≠ ``Sparkle.Core.Signal.Signal.pure := by
  decide

theorem ne_beq_mux :
    ``Sparkle.Core.Signal.Signal.beq ≠ ``Sparkle.Core.Signal.Signal.mux := by
  decide

section
variable {cfg : Cfg}

theorem isSigBoolT_self (hd : cfg.isDom cfg.dom = true) :
    isSigBoolT cfg (sigBoolT cfg.dom) = true := hd

theorem sigBitsT?_sigT (hd : cfg.isDom cfg.dom = true) (n : Nat) :
    sigBitsT? cfg (sigT cfg.dom n) = some n := by
  show (if cfg.isDom cfg.dom = true then bitVecE? (bitVecE n) else none) = some n
  exact (if_pos hd).trans (bitVecE?_bitVecE n)

theorem sigBitsT?_sigBoolT (d : Lean.Expr) : sigBitsT? cfg (sigBoolT d) = none := by
  show (if cfg.isDom d = true then bitVecE? (.const ``Bool []) else none) = none
  by_cases h : cfg.isDom d = true
  · exact (if_pos h).trans rfl
  · exact if_neg h

theorem isInstDom_self (hd : cfg.isDom cfg.dom = true) (n : Lean.Name) :
    isInstDom cfg n (.app (.const n []) cfg.dom) = true := by
  show decide (n = n ∧ cfg.isDom cfg.dom = true) = true
  exact decide_eq_true ⟨rfl, hd⟩

theorem instDomNat?_self (hd : cfg.isDom cfg.dom = true) (n : Lean.Name) (w : Nat) :
    instDomNat? cfg n (.app (.app (.const n []) cfg.dom) (natE w)) = some w := by
  show (if n = n ∧ cfg.isDom cfg.dom = true then natE? (natE w) else none) = some w
  exact (if_pos ⟨rfl, hd⟩).trans (natE?_natE w)

theorem isConcatInst_self (hd : cfg.isDom cfg.dom = true) (m n : Nat) :
    isConcatInst cfg m n
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat [])
        cfg.dom) (natE m)) (natE n)) = true := by
  show decide (cfg.isDom cfg.dom = true ∧ natE? (natE m) = some m ∧
    natE? (natE n) = some n) = true
  exact decide_eq_true ⟨hd, natE?_natE m, natE?_natE n⟩

/-! ## A node of the reader on its own quotation, and the other kinds' readers
on it -/

/-! ### Three arguments -/

theorem readBoolLit_true (hd : cfg.isDom cfg.dom = true) :
    readBoolLit cfg ``Sparkle.Core.Signal.Signal.pure [.zero] cfg.dom (.const ``Bool [])
      (.const ``Bool.true []) = some ⟨.bool, .boolLit true⟩ := by
  unfold readBoolLit
  exact (if_pos ⟨rfl, rfl, hd, isConst_self _⟩).trans (if_pos (isConst_self _))

theorem readBoolLit_false (hd : cfg.isDom cfg.dom = true) :
    readBoolLit cfg ``Sparkle.Core.Signal.Signal.pure [.zero] cfg.dom (.const ``Bool [])
      (.const ``Bool.false []) = some ⟨.bool, .boolLit false⟩ := by
  unfold readBoolLit
  exact (if_pos ⟨rfl, rfl, hd, isConst_self _⟩).trans
    ((if_neg (by decide : ¬ (isConst ``Bool.true (.const ``Bool.false []) = true))).trans
      (if_pos (isConst_self _)))

/-- The Bool literal reader refuses a BitVec type argument. -/
theorem readBoolLit_bits {c : Lean.Name} {ls : List Lean.Level} {x0 x2 : Lean.Expr}
    (w : Nat) : readBoolLit cfg c ls x0 (bitVecE w) x2 = none := by
  unfold readBoolLit
  exact if_neg (fun g => false_ne g.2.2.2)

theorem readBoolLit_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr}
    (hn : c ≠ ``Sparkle.Core.Signal.Signal.pure) : readBoolLit cfg c ls x0 x1 x2 = none := by
  unfold readBoolLit
  exact if_neg (fun g => hn g.1)

theorem readBitsLit_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr}
    (hn : c ≠ ``Sparkle.Core.Signal.Signal.pure) : readBitsLit cfg c ls x0 x1 x2 = none := by
  unfold readBitsLit
  exact if_neg (fun g => hn g.1)

theorem readBitsLit_eval (hd : cfg.isDom cfg.dom = true) {w v : Nat}
    (hv : v < 2 ^ w ∧ 0 < w) :
    readBitsLit cfg ``Sparkle.Core.Signal.Signal.pure [.zero] cfg.dom (bitVecE w)
      (litE w v) = some ⟨.bits w, .bitsLit w v⟩ := by
  unfold readBitsLit
  refine (if_pos ⟨rfl, rfl, hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨w, bitVecE?_bitVecE w, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨v, litOf?_litE w v, ?_⟩
  exact if_pos hv

theorem readBoolNot_eval (hd : cfg.isDom cfg.dom = true) {r2 : Option AnyTerm}
    {a : Term .bool} (h2 : r2 = some ⟨.bool, a⟩) :
    readBoolNot cfg ``Complement.complement [.zero] (sigBoolT cfg.dom)
      (.app (.const ``Sparkle.Core.Signal.instComplementSignalBool []) cfg.dom) r2 =
      some ⟨.bool, .boolNot a⟩ := by
  unfold readBoolNot
  refine (if_pos ⟨rfl, rfl, isSigBoolT_self hd, isInstDom_self hd _⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h2, rfl⟩, ?_⟩
  rfl

theorem read3_boolLit_true (hd : cfg.isDom cfg.dom = true) {r2 : Option AnyTerm} :
    read3 cfg ``Sparkle.Core.Signal.Signal.pure [.zero] cfg.dom (.const ``Bool [])
      (.const ``Bool.true []) r2 = some ⟨.bool, .boolLit true⟩ := by
  unfold read3
  exact alt_some_left (readBoolLit_true hd)

theorem read3_boolLit_false (hd : cfg.isDom cfg.dom = true) {r2 : Option AnyTerm} :
    read3 cfg ``Sparkle.Core.Signal.Signal.pure [.zero] cfg.dom (.const ``Bool [])
      (.const ``Bool.false []) r2 = some ⟨.bool, .boolLit false⟩ := by
  unfold read3
  exact alt_some_left (readBoolLit_false hd)

theorem read3_bitsLit (hd : cfg.isDom cfg.dom = true) {w v : Nat} (hv : v < 2 ^ w ∧ 0 < w)
    {r2 : Option AnyTerm} :
    read3 cfg ``Sparkle.Core.Signal.Signal.pure [.zero] cfg.dom (bitVecE w) (litE w v) r2 =
      some ⟨.bits w, .bitsLit w v⟩ := by
  unfold read3
  exact (alt_none_left (readBoolLit_bits w)).trans (alt_some_left (readBitsLit_eval hd hv))

theorem read3_boolNot (hd : cfg.isDom cfg.dom = true) {x2 : Lean.Expr}
    {r2 : Option AnyTerm} {a : Term .bool} (h2 : r2 = some ⟨.bool, a⟩) :
    read3 cfg ``Complement.complement [.zero] (sigBoolT cfg.dom)
      (.app (.const ``Sparkle.Core.Signal.instComplementSignalBool []) cfg.dom) x2 r2 =
      some ⟨.bool, .boolNot a⟩ := by
  unfold read3
  exact (alt_none_left (readBoolLit_head ne_compl_pure)).trans
    ((alt_none_left (readBitsLit_head ne_compl_pure)).trans (readBoolNot_eval hd h2))

/-! ### Four arguments -/

theorem readCompare_eval (hd : cfg.isDom cfg.dom = true) {op : SignalCompareKind}
    (hop : op ≠ .eq) {w : Nat} {r2 r3 : Option AnyTerm} {a b : Term (.bits w)}
    (h2 : r2 = some ⟨.bits w, a⟩) (h3 : r3 = some ⟨.bits w, b⟩) :
    readCompare cfg (compareName op) [] cfg.dom (natE w) r2 r3 =
      some ⟨.bool, .compare op a b⟩ := by
  unfold readCompare
  refine (if_pos ⟨rfl, hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨op, cmpOf?_compareName hop, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨w, natE?_natE w, ?_⟩
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h2, asBits_self w a⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr
    ⟨b, Option.bind_eq_some_iff.mpr ⟨_, h3, asBits_self w b⟩, ?_⟩
  rfl

/-! ### Five arguments -/

theorem readMuxBool_eval (hd : cfg.isDom cfg.dom = true) {r2 r3 r4 : Option AnyTerm}
    {c a b : Term .bool} (h2 : r2 = some ⟨.bool, c⟩) (h3 : r3 = some ⟨.bool, a⟩)
    (h4 : r4 = some ⟨.bool, b⟩) :
    readMuxBool cfg ``Sparkle.Core.Signal.Signal.mux [.zero] cfg.dom (.const ``Bool [])
      r2 r3 r4 = some ⟨.bool, .mux c a b⟩ := by
  unfold readMuxBool
  refine (if_pos ⟨rfl, rfl, hd, isConst_self _⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨c, Option.bind_eq_some_iff.mpr ⟨_, h2, rfl⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h3, rfl⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨b, Option.bind_eq_some_iff.mpr ⟨_, h4, rfl⟩, ?_⟩
  rfl

/-- The Bool mux reader refuses a BitVec type argument. -/
theorem readMuxBool_bits {c : Lean.Name} {ls : List Lean.Level} {x0 : Lean.Expr}
    {r2 r3 r4 : Option AnyTerm} (w : Nat) :
    readMuxBool cfg c ls x0 (bitVecE w) r2 r3 r4 = none := by
  unfold readMuxBool
  exact if_neg (fun g => false_ne g.2.2.2)

theorem readMuxBool_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 : Lean.Expr}
    {r2 r3 r4 : Option AnyTerm} (hn : c ≠ ``Sparkle.Core.Signal.Signal.mux) :
    readMuxBool cfg c ls x0 x1 r2 r3 r4 = none := by
  unfold readMuxBool
  exact if_neg (fun g => hn g.1)

theorem readMuxBits_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 : Lean.Expr}
    {r2 r3 r4 : Option AnyTerm} (hn : c ≠ ``Sparkle.Core.Signal.Signal.mux) :
    readMuxBits cfg c ls x0 x1 r2 r3 r4 = none := by
  unfold readMuxBits
  exact if_neg (fun g => hn g.1)

theorem readMuxBits_eval (hd : cfg.isDom cfg.dom = true) {w : Nat}
    {r2 r3 r4 : Option AnyTerm} {c : Term .bool} {a b : Term (.bits w)}
    (h2 : r2 = some ⟨.bool, c⟩) (h3 : r3 = some ⟨.bits w, a⟩)
    (h4 : r4 = some ⟨.bits w, b⟩) :
    readMuxBits cfg ``Sparkle.Core.Signal.Signal.mux [.zero] cfg.dom (bitVecE w)
      r2 r3 r4 = some ⟨.bits w, .mux c a b⟩ := by
  unfold readMuxBits
  refine (if_pos ⟨rfl, rfl, hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨w, bitVecE?_bitVecE w, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨c, Option.bind_eq_some_iff.mpr ⟨_, h2, rfl⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h3, asBits_self w a⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr
    ⟨b, Option.bind_eq_some_iff.mpr ⟨_, h4, asBits_self w b⟩, ?_⟩
  rfl

theorem readBoolEq_eval (hd : cfg.isDom cfg.dom = true) {r3 r4 : Option AnyTerm}
    {a b : Term .bool} (h3 : r3 = some ⟨.bool, a⟩) (h4 : r4 = some ⟨.bool, b⟩) :
    readBoolEq cfg ``Sparkle.Core.Signal.Signal.beq [] (.const ``Bool []) cfg.dom boolBEqE
      r3 r4 = some ⟨.bool, .boolEq a b⟩ := by
  unfold readBoolEq
  refine (if_pos ⟨rfl, rfl, isConst_self _, hd, rfl⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h3, rfl⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨b, Option.bind_eq_some_iff.mpr ⟨_, h4, rfl⟩, ?_⟩
  rfl

/-- The Bool equality reader refuses a BitVec type argument. -/
theorem readBoolEq_bits {c : Lean.Name} {ls : List Lean.Level} {x1 x2 : Lean.Expr}
    {r3 r4 : Option AnyTerm} (w : Nat) :
    readBoolEq cfg c ls (bitVecE w) x1 x2 r3 r4 = none := by
  unfold readBoolEq
  exact if_neg (fun g => false_ne g.2.2.1)

theorem readBitsEq_eval (hd : cfg.isDom cfg.dom = true) {w : Nat}
    {r3 r4 : Option AnyTerm} {a b : Term (.bits w)}
    (h3 : r3 = some ⟨.bits w, a⟩) (h4 : r4 = some ⟨.bits w, b⟩) :
    readBitsEq cfg ``Sparkle.Core.Signal.Signal.beq [] (bitVecE w) cfg.dom (bitsBEqE w)
      r3 r4 = some ⟨.bool, .compare .eq a b⟩ := by
  unfold readBitsEq
  refine (if_pos ⟨rfl, rfl, hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨w, bitVecE?_bitVecE w, ?_⟩
  refine (if_pos (bitsBEq?_self w)).trans ?_
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h3, asBits_self w a⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr
    ⟨b, Option.bind_eq_some_iff.mpr ⟨_, h4, asBits_self w b⟩, ?_⟩
  rfl

theorem read5_muxBool (hd : cfg.isDom cfg.dom = true) {x2 : Lean.Expr}
    {r2 r3 r4 : Option AnyTerm} {c a b : Term .bool} (h2 : r2 = some ⟨.bool, c⟩)
    (h3 : r3 = some ⟨.bool, a⟩) (h4 : r4 = some ⟨.bool, b⟩) :
    read5 cfg ``Sparkle.Core.Signal.Signal.mux [.zero] cfg.dom (.const ``Bool []) x2
      r2 r3 r4 = some ⟨.bool, .mux c a b⟩ := by
  unfold read5
  exact alt_some_left (readMuxBool_eval hd h2 h3 h4)

theorem read5_muxBits (hd : cfg.isDom cfg.dom = true) {w : Nat} {x2 : Lean.Expr}
    {r2 r3 r4 : Option AnyTerm} {c : Term .bool} {a b : Term (.bits w)}
    (h2 : r2 = some ⟨.bool, c⟩) (h3 : r3 = some ⟨.bits w, a⟩)
    (h4 : r4 = some ⟨.bits w, b⟩) :
    read5 cfg ``Sparkle.Core.Signal.Signal.mux [.zero] cfg.dom (bitVecE w) x2
      r2 r3 r4 = some ⟨.bits w, .mux c a b⟩ := by
  unfold read5
  exact (alt_none_left (readMuxBool_bits w)).trans
    (alt_some_left (readMuxBits_eval hd h2 h3 h4))

theorem read5_boolEq (hd : cfg.isDom cfg.dom = true) {r2 r3 r4 : Option AnyTerm}
    {a b : Term .bool} (h3 : r3 = some ⟨.bool, a⟩) (h4 : r4 = some ⟨.bool, b⟩) :
    read5 cfg ``Sparkle.Core.Signal.Signal.beq [] (.const ``Bool []) cfg.dom boolBEqE
      r2 r3 r4 = some ⟨.bool, .boolEq a b⟩ := by
  unfold read5
  exact (alt_none_left (readMuxBool_head ne_beq_mux)).trans
    ((alt_none_left (readMuxBits_head ne_beq_mux)).trans
      (alt_some_left (readBoolEq_eval hd h3 h4)))

theorem read5_bitsEq (hd : cfg.isDom cfg.dom = true) {w : Nat} {r2 r3 r4 : Option AnyTerm}
    {a b : Term (.bits w)} (h3 : r3 = some ⟨.bits w, a⟩) (h4 : r4 = some ⟨.bits w, b⟩) :
    read5 cfg ``Sparkle.Core.Signal.Signal.beq [] (bitVecE w) cfg.dom (bitsBEqE w)
      r2 r3 r4 = some ⟨.bool, .compare .eq a b⟩ := by
  unfold read5
  exact (alt_none_left (readMuxBool_head ne_beq_mux)).trans
    ((alt_none_left (readMuxBits_head ne_beq_mux)).trans
      ((alt_none_left (readBoolEq_bits w)).trans (readBitsEq_eval hd h3 h4)))

/-! ### Six arguments -/

theorem readBinary_eval (hd : cfg.isDom cfg.dom = true) (op : Binary) {w : Nat}
    {r4 r5 : Option AnyTerm} {a b : Term (.bits w)}
    (h4 : r4 = some ⟨.bits w, a⟩) (h5 : r5 = some ⟨.bits w, b⟩) :
    readBinary cfg (binMethod op) [.zero, .zero, .zero] (sigT cfg.dom w) (sigT cfg.dom w)
      (sigT cfg.dom w) (.app (.app (.const (binInst op) []) cfg.dom) (natE w)) r4 r5 =
      some ⟨.bits w, .binary op a b⟩ := by
  unfold readBinary
  refine (if_pos rfl).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨op, binOf?_binMethod op, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨w, sigBitsT?_sigT hd w, ?_⟩
  refine (if_pos ⟨sigBitsT?_sigT hd w, sigBitsT?_sigT hd w,
    instDomNat?_self hd _ w⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h4, asBits_self w a⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr
    ⟨b, Option.bind_eq_some_iff.mpr ⟨_, h5, asBits_self w b⟩, ?_⟩
  rfl

/-- The BitVec operator reader refuses a first type argument that is not a
BitVec Signal type (`&&&`, `|||`, `^^^` are shared with the Bool operators). -/
theorem readBinary_type {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr}
    {r4 r5 : Option AnyTerm} (h0 : sigBitsT? cfg x0 = none) :
    readBinary cfg c ls x0 x1 x2 x3 r4 r5 = none := by
  unfold readBinary
  by_cases hl : lvl3 ls = true
  · exact (if_pos hl).trans (bind_bind_none _ _ _ h0)
  · exact if_neg hl

theorem readBinary_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr}
    {r4 r5 : Option AnyTerm} (hn : binOf? c = none) :
    readBinary cfg c ls x0 x1 x2 x3 r4 r5 = none := by
  unfold readBinary
  by_cases hl : lvl3 ls = true
  · exact (if_pos hl).trans (bind_none_of hn _)
  · exact if_neg hl

theorem readBoolBinary_eval (hd : cfg.isDom cfg.dom = true) (k : SignalBoolBinKind)
    {r4 r5 : Option AnyTerm} {a b : Term .bool}
    (h4 : r4 = some ⟨.bool, a⟩) (h5 : r5 = some ⟨.bool, b⟩) :
    readBoolBinary cfg (signalBoolBinName k) [.zero, .zero, .zero] (sigBoolT cfg.dom)
      (sigBoolT cfg.dom) (sigBoolT cfg.dom)
      (.app (.const (signalBoolBinInst k) []) cfg.dom) r4 r5 =
      some ⟨.bool, .boolBinary k a b⟩ := by
  unfold readBoolBinary
  refine (if_pos ⟨rfl, isSigBoolT_self hd, isSigBoolT_self hd, isSigBoolT_self hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨k, boolBinOf?_name k, ?_⟩
  refine (if_pos (isInstDom_self hd _)).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h4, rfl⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨b, Option.bind_eq_some_iff.mpr ⟨_, h5, rfl⟩, ?_⟩
  rfl

/-- The Bool operator reader refuses a BitVec Signal type argument. -/
theorem readBoolBinary_bits {c : Lean.Name} {ls : List Lean.Level} {x1 x2 x3 : Lean.Expr}
    {r4 r5 : Option AnyTerm} (d : Lean.Expr) (m : Nat) :
    readBoolBinary cfg c ls (sigT d m) x1 x2 x3 r4 r5 = none := by
  unfold readBoolBinary
  exact if_neg (fun g => false_ne g.2.1)

theorem readConcat_eval (hd : cfg.isDom cfg.dom = true) {m n : Nat}
    {r4 r5 : Option AnyTerm} {a : Term (.bits m)} {b : Term (.bits n)}
    (h4 : r4 = some ⟨.bits m, a⟩) (h5 : r5 = some ⟨.bits n, b⟩) :
    readConcat cfg ``HAppend.hAppend [.zero, .zero, .zero] (sigT cfg.dom m) (sigT cfg.dom n)
      (sigT cfg.dom (m + n))
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat [])
        cfg.dom) (natE m)) (natE n)) r4 r5 = some ⟨.bits (m + n), .concat a b⟩ := by
  unfold readConcat
  refine (if_pos ⟨rfl, rfl⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨m, sigBitsT?_sigT hd m, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨n, sigBitsT?_sigT hd n, ?_⟩
  refine (if_pos ⟨sigBitsT?_sigT hd (m + n), isConcatInst_self hd m n⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h4, asBits_self m a⟩, ?_⟩
  refine Option.bind_eq_some_iff.mpr
    ⟨b, Option.bind_eq_some_iff.mpr ⟨_, h5, asBits_self n b⟩, ?_⟩
  rfl

theorem read6_binary (hd : cfg.isDom cfg.dom = true) (op : Binary) {w : Nat}
    {r4 r5 : Option AnyTerm} {a b : Term (.bits w)}
    (h4 : r4 = some ⟨.bits w, a⟩) (h5 : r5 = some ⟨.bits w, b⟩) :
    read6 cfg (binMethod op) [.zero, .zero, .zero] (sigT cfg.dom w) (sigT cfg.dom w)
      (sigT cfg.dom w) (.app (.app (.const (binInst op) []) cfg.dom) (natE w)) r4 r5 =
      some ⟨.bits w, .binary op a b⟩ := by
  unfold read6
  exact alt_some_left (readBinary_eval hd op h4 h5)

theorem read6_boolBinary (hd : cfg.isDom cfg.dom = true) (k : SignalBoolBinKind)
    {r4 r5 : Option AnyTerm} {a b : Term .bool}
    (h4 : r4 = some ⟨.bool, a⟩) (h5 : r5 = some ⟨.bool, b⟩) :
    read6 cfg (signalBoolBinName k) [.zero, .zero, .zero] (sigBoolT cfg.dom)
      (sigBoolT cfg.dom) (sigBoolT cfg.dom)
      (.app (.const (signalBoolBinInst k) []) cfg.dom) r4 r5 =
      some ⟨.bool, .boolBinary k a b⟩ := by
  unfold read6
  exact (alt_none_left (readBinary_type (sigBitsT?_sigBoolT cfg.dom))).trans
    (alt_some_left (readBoolBinary_eval hd k h4 h5))

theorem read6_concat (hd : cfg.isDom cfg.dom = true) {m n : Nat}
    {r4 r5 : Option AnyTerm} {a : Term (.bits m)} {b : Term (.bits n)}
    (h4 : r4 = some ⟨.bits m, a⟩) (h5 : r5 = some ⟨.bits n, b⟩) :
    read6 cfg ``HAppend.hAppend [.zero, .zero, .zero] (sigT cfg.dom m) (sigT cfg.dom n)
      (sigT cfg.dom (m + n))
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat [])
        cfg.dom) (natE m)) (natE n)) r4 r5 = some ⟨.bits (m + n), .concat a b⟩ := by
  unfold read6
  exact (alt_none_left (readBinary_head binOf?_append)).trans
    ((alt_none_left (readBoolBinary_bits cfg.dom m)).trans (readConcat_eval hd h4 h5))

/-! ## The reader on an application, by arity -/

theorem readTerm_app3 {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} :
    readTerm cfg (.app (.app (.app (.const c ls) x0) x1) x2) =
      read3 cfg c ls x0 x1 x2 (readTerm cfg x2) := rfl

theorem readTerm_app4 {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr} :
    readTerm cfg (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) =
      readCompare cfg c ls x0 x1 (readTerm cfg x2) (readTerm cfg x3) := rfl

theorem readTerm_app5 {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr} :
    readTerm cfg (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) =
      read5 cfg c ls x0 x1 x2 (readTerm cfg x2) (readTerm cfg x3) (readTerm cfg x4) := rfl

theorem readTerm_app6 {c : Lean.Name} {ls : List Lean.Level}
    {x0 x1 x2 x3 x4 x5 : Lean.Expr} :
    readTerm cfg (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) =
      read6 cfg c ls x0 x1 x2 x3 (readTerm cfg x4) (readTerm cfg x5) := rfl

end

/-! ## Completeness -/

/-- The terms built from the node kinds `readTerm` reads. -/
def core : {s : SType} → Term s → Prop
  | _, .boolInput _ => True
  | _, .bitsInput _ _ => True
  | _, .boolLit _ => True
  | _, .bitsLit _ _ => True
  | _, .bitsNum _ _ => False
  | _, .binary _ a b => core a ∧ core b
  | _, .compare _ a b => core a ∧ core b
  | _, .boolBinary _ a b => core a ∧ core b
  | _, .boolNot a => core a
  | _, .boolEq a b => core a ∧ core b
  | _, .mux c a b => core c ∧ core a ∧ core b
  | _, .setw _ _ => False
  | _, .slice _ _ _ _ => False
  | _, .concat a b => core a ∧ core b
  | _, .concatLitHi _ _ _ => False
  | _, .concatLitLo _ _ _ => False
  | _, .zextMap _ _ _ => False
  | _, .sliceF _ _ _ _ => False
  | _, .appCompare _ _ _ => False
  | _, .appBool _ _ _ => False
  | _, .appBool2 _ _ _ => False

/-- What completeness asks of the leaf tables (the converse of `Cfg.Sound`). -/
structure Complete (cfg : Cfg) : Prop where
  domOk : cfg.isDom cfg.dom = true
  boolOut : ∀ j, j < cfg.kb → ∃ i, cfg.bools j = .bvar i ∧ cfg.inBool i = some j
  bitsOut : ∀ j w, j < cfg.kv → cfg.vw j = w → 0 < w →
    ∃ i, cfg.bits j = .bvar i ∧ cfg.inBool i = none ∧ cfg.inBits i = some (w, j)

/-- **Reader completeness on core quotations.** The reader returns `t` on the
quotation of every well-formed core term `t`. -/
theorem readTerm_quote {cfg : Cfg} (hc : Complete cfg) :
    ∀ {s : SType} (t : Term s), core t → t.WF cfg.kb cfg.kv cfg.vw →
      readTerm cfg (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩
  | _, .boolInput j, _, hj => by
    obtain ⟨i, hq, hin⟩ := hc.boolOut j hj
    show readTerm cfg (cfg.bools j) = _
    rw [hq]
    show readInput cfg i = _
    unfold readInput
    exact alt_some_left (Option.bind_eq_some_iff.mpr ⟨j, hin, rfl⟩)
  | _, .bitsInput w j, _, hwf => by
    obtain ⟨h1, h2, h3⟩ := hwf
    obtain ⟨i, hq, hnb, hin⟩ := hc.bitsOut j w h1 h2 h3
    show readTerm cfg (cfg.bits j) = _
    rw [hq]
    show readInput cfg i = _
    unfold readInput
    exact (alt_none_left (bind_none_of hnb _)).trans
      (Option.bind_eq_some_iff.mpr ⟨(w, j), hin, rfl⟩)
  | _, .boolLit b, _, _ => by
    cases b
    · exact readTerm_app3.trans (read3_boolLit_false hc.domOk)
    · exact readTerm_app3.trans (read3_boolLit_true hc.domOk)
  | _, .bitsLit w v, _, hwf =>
    readTerm_app3.trans (read3_bitsLit hc.domOk hwf)
  | _, .bitsNum _ _, hcore, _ => False.elim hcore
  | _, .binary op a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    exact readTerm_app6.trans
      (read6_binary hc.domOk op (readTerm_quote hc a ca wa) (readTerm_quote hc b cb wb))
  | _, .compare op a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    have iha := readTerm_quote hc a ca wa
    have ihb := readTerm_quote hc b cb wb
    cases op
    · exact readTerm_app4.trans
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb)
    · exact readTerm_app4.trans
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb)
    · exact readTerm_app4.trans
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb)
    · exact readTerm_app4.trans
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb)
    · exact readTerm_app5.trans (read5_bitsEq hc.domOk iha ihb)
  | _, .boolBinary k a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    exact readTerm_app6.trans
      (read6_boolBinary hc.domOk k (readTerm_quote hc a ca wa) (readTerm_quote hc b cb wb))
  | _, .boolNot a, hcore, hwf =>
    readTerm_app3.trans (read3_boolNot hc.domOk (readTerm_quote hc a hcore hwf))
  | _, .boolEq a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    exact readTerm_app5.trans
      (read5_boolEq hc.domOk (readTerm_quote hc a ca wa) (readTerm_quote hc b cb wb))
  | s, .mux c a b, hcore, hwf => by
    obtain ⟨cc, ca, cb⟩ := hcore
    obtain ⟨wc, wa, wb⟩ := hwf
    have ihc := readTerm_quote hc c cc wc
    have iha := readTerm_quote hc a ca wa
    have ihb := readTerm_quote hc b cb wb
    cases s
    · exact readTerm_app5.trans (read5_muxBool hc.domOk ihc iha ihb)
    · exact readTerm_app5.trans (read5_muxBits hc.domOk ihc iha ihb)
  | _, .setw _ _, hcore, _ => False.elim hcore
  | _, .slice _ _ _ _, hcore, _ => False.elim hcore
  | _, .concat a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    exact readTerm_app6.trans
      (read6_concat hc.domOk (readTerm_quote hc a ca wa) (readTerm_quote hc b cb wb))
  | _, .concatLitHi _ _ _, hcore, _ => False.elim hcore
  | _, .concatLitLo _ _ _, hcore, _ => False.elim hcore
  | _, .zextMap _ _ _, hcore, _ => False.elim hcore
  | _, .sliceF _ _ _ _, hcore, _ => False.elim hcore
  | _, .appCompare _ _ _, hcore, _ => False.elim hcore
  | _, .appBool _ _ _, hcore, _ => False.elim hcore
  | _, .appBool2 _ _ _, hcore, _ => False.elim hcore

/-- **`quote` is injective on well-formed core terms**: two such terms with
one quotation are one term (the reader returns both). -/
theorem quote_injective {cfg : Cfg} (hc : Complete cfg) {s s' : SType} (t : Term s)
    (t' : Term s') (ht : core t) (ht' : core t') (hw : t.WF cfg.kb cfg.kv cfg.vw)
    (hw' : t'.WF cfg.kb cfg.kv cfg.vw)
    (h : quote cfg.dom cfg.bools cfg.bits t = quote cfg.dom cfg.bools cfg.bits t') :
    (⟨s, t⟩ : AnyTerm) = ⟨s', t'⟩ := by
  have h1 := readTerm_quote hc t ht hw
  have h2 := readTerm_quote hc t' ht' hw'
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- A reading and completeness: on a core quotation the reader's answer is
the term quoted, so soundness and completeness describe ONE function. -/
theorem readTerm_quote_iff {cfg : Cfg} (hc : Complete cfg) {s : SType} (t : Term s)
    (ht : core t) (hw : t.WF cfg.kb cfg.kv cfg.vw) (r : AnyTerm) :
    readTerm cfg (quote cfg.dom cfg.bools cfg.bits t) = some r ↔ r = ⟨s, t⟩ := by
  constructor
  · intro h
    exact Option.some.inj (h.symm.trans (readTerm_quote hc t ht hw))
  · intro h
    rw [h]
    exact readTerm_quote hc t ht hw

/-! ## The configuration of the machine endpoints -/

/-- What the binder list has to satisfy: the listed positions carry the
listed kinds. (True of every binder list whose BitVec binders are positive;
stated as a condition here.) -/
structure KindsOK (ks : List MixedGateBinder) : Prop where
  boolAt : ∀ j, j < (posB 0 ks).length →
    (posB 0 ks).getD j 0 < ks.length ∧
    ks[(posB 0 ks).getD j 0]? = some MixedGateBinder.bool ∧
    rankB ks ((posB 0 ks).getD j 0) = j
  bitsAt : ∀ j, j < (posV 0 ks).length → 0 < (widV ks).getD j 0 →
    (posV 0 ks).getD j 0 < ks.length ∧
    ks[(posV 0 ks).getD j 0]? = some (MixedGateBinder.bits ((widV ks).getD j 0)) ∧
    rankV ks ((posV 0 ks).getD j 0) = j

theorem inBoolOf_at (ks : List MixedGateBinder) (p : Nat) (hp : p < ks.length)
    (hk : ks[p]? = some MixedGateBinder.bool) :
    inBoolOf ks (ks.length - 1 - p) = some (rankB ks p) := by
  have e : ks.length - 1 - (ks.length - 1 - p) = p := by omega
  unfold inBoolOf
  rw [e]
  exact (if_pos (by omega)).trans (if_pos hk)

theorem inBoolOf_bits (ks : List MixedGateBinder) (p w : Nat) (hp : p < ks.length)
    (hk : ks[p]? = some (MixedGateBinder.bits w)) :
    inBoolOf ks (ks.length - 1 - p) = none := by
  have e : ks.length - 1 - (ks.length - 1 - p) = p := by omega
  unfold inBoolOf
  rw [e]
  refine (if_pos (by omega)).trans (if_neg ?_)
  intro hb
  rw [hk] at hb
  cases hb

theorem inBitsOf_at (ks : List MixedGateBinder) (p w : Nat) (hp : p < ks.length)
    (hk : ks[p]? = some (MixedGateBinder.bits w)) (hw : 0 < w) :
    inBitsOf ks (ks.length - 1 - p) = some (w, rankV ks p) := by
  have e : ks.length - 1 - (ks.length - 1 - p) = p := by omega
  unfold inBitsOf
  rw [e]
  refine (if_pos (by omega)).trans ?_
  exact Option.bind_eq_some_iff.mpr ⟨w, (congrArg kindWidth? hk).trans rfl, if_pos hw⟩

theorem kindsCfg_complete (dom : Lean.Expr) (isDom : Lean.Expr → Bool)
    (hdom : isDom dom = true) (ks : List MixedGateBinder) (hk : KindsOK ks) :
    Complete (kindsCfg dom isDom ks) where
  domOk := hdom
  boolOut := fun j hj => by
    obtain ⟨hp, hkind, hr⟩ := hk.boolAt j hj
    refine ⟨ks.length - 1 - (posB 0 ks).getD j 0, rfl, ?_⟩
    have h := inBoolOf_at ks _ hp hkind
    rw [hr] at h
    exact h
  bitsOut := fun j w hj hw hpos => by
    have hw' : (widV ks).getD j 0 = w := hw
    subst hw'
    obtain ⟨hp, hkind, hr⟩ := hk.bitsAt j hj hpos
    refine ⟨ks.length - 1 - (posV 0 ks).getD j 0, rfl, inBoolOf_bits ks _ _ hp hkind, ?_⟩
    have h := inBitsOf_at ks _ _ hp hkind hpos
    rw [hr] at h
    exact h

/-- The structural domain test accepts its own expression. -/
theorem isExpr_self (dom : Lean.Expr) : isExpr dom dom = true :=
  @decide_eq_true (dom = dom) (Sparkle.Compiler.ExprDecEq.exprDecEq dom dom) rfl

/-- **Completeness under binders**, with the structural domain test. -/
theorem readTerm_expr_quote (dom : Lean.Expr) (ks : List MixedGateBinder) (hk : KindsOK ks)
    {s : SType} (t : Term s) (ht : core t)
    (hw : t.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0)) :
    readTerm (kindsCfg dom (isExpr dom) ks)
      (quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) t) = some ⟨s, t⟩ :=
  readTerm_quote (kindsCfg_complete dom (isExpr dom) (isExpr_self dom) ks hk) t ht hw

end Tools.ShippingReaderComplete
