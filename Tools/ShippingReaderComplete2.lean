import Tools.ShippingReaderComplete
import Tools.ShippingReaderNodes2

/-! # Completeness of the extended reader on eighteen node kinds (G3)

`readTerm2_quote`: for every well-formed term `t` built from the eighteen
kinds `readTerm2` reads (`core2 t`: everything but the three applicative
lifts),

  `readTerm2 cfg (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩`

under the same condition `Complete cfg` as the core reader. Consequences:
`quote2_injective` (on these kinds two well-formed terms with one quotation
are one term) and `readTerm2_extends_on_quotes` (on the quotation of a core
term the extended reader returns what the core reader returns).

How a kind is told from the others (no tie-break is used; no pair of
distinct terms with one quotation was met):
* `bitsNum` vs `bitsLit` / `boolLit` (`Signal.pure`): the payload —
  `OfNat.ofNat …` is not `BitVec.ofNat …`, the type argument is not `Bool`;
* `setw` / `slice` / `zextMap` (`Signal.map`): the function argument — a
  partial application of `BitVec.setWidth`, a lambda over `extractLsb'`, a
  lambda over `BitVec.append`; and `Signal.map` is neither `mux` nor `beq`;
* `sliceF` (`Functor.map`): its own head;
* `concat` / `concatLitHi` / `concatLitLo` (`HAppend.hAppend`): which of the
  first two type arguments is a Signal type.

What is NOT proved here
* The three lifts `appCompare`, `appBool`, `appBool2` (not read at all).
* That `readTerm2` extends `readTerm` on EVERY expression: only on
  quotations of core terms. The general statement needs "a term `readTerm`
  returns is a core term" (one more instance of `readTerm_induct`), not
  done.

Evaluations to watch (same kind as in `ShippingReaderComplete`): the `Name`
inequalities by `decide`, `binOf?_fmap` / `boolBinOf?_fmap` by `rfl`, and
`sliceLam?` on a `BitVec.append` lambda by `rfl`. -/
namespace Tools.ShippingReaderComplete2
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingEntrySoundness Tools.ShippingScalarSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingReaderTerm Tools.ShippingReaderInputs Tools.ShippingReaderComplete
open Tools.ShippingReaderNodes2

/-! ## Head constants -/

theorem ne_pure_compl : ``Sparkle.Core.Signal.Signal.pure ≠ ``Complement.complement := by
  decide

theorem ne_map_mux :
    ``Sparkle.Core.Signal.Signal.map ≠ ``Sparkle.Core.Signal.Signal.mux := by
  decide

theorem ne_map_beq :
    ``Sparkle.Core.Signal.Signal.map ≠ ``Sparkle.Core.Signal.Signal.beq := by
  decide

theorem ne_fmap_append : ``Functor.map ≠ ``HAppend.hAppend := by
  decide

theorem ne_append_fmap : ``HAppend.hAppend ≠ ``Functor.map := by
  decide

theorem binOf?_fmap : binOf? ``Functor.map = none := rfl

theorem boolBinOf?_fmap : boolBinOf? ``Functor.map = none := rfl

/-! ## The added destructors on the forms `quote` writes -/

theorem numLitOf?_self (w v : Nat) : numLitOf? w (numLitE w v) = some v := by
  show (if bitVecE? (bitVecE w) = some w ∧ natE? (natE w) = some w ∧ v = v then some v
    else none) = some v
  exact if_pos ⟨bitVecE?_bitVecE w, natE?_natE w, rfl⟩

theorem isSetwFn_self (w w' : Nat) : isSetwFn w w' (setwFn w w') = true := by
  show decide (natE? (natE w) = some w ∧ natE? (natE w') = some w') = true
  exact decide_eq_true ⟨natE?_natE w, natE?_natE w'⟩

theorem sliceLam?_self (nm : Lean.Name) (w st len : Nat) :
    sliceLam? w len (sliceFn nm w st len) = some (nm, st) := by
  show (if bitVecE? (bitVecE w) = some w ∧ natE? (natE w) = some w ∧
      natE? (natE len) = some len then (natE? (natE st)).bind fun s => some (nm, s)
    else none) = some (nm, st)
  exact (if_pos ⟨bitVecE?_bitVecE w, natE?_natE w, natE?_natE len⟩).trans
    (Option.bind_eq_some_iff.mpr ⟨st, natE?_natE st, rfl⟩)

theorem zextLam?_self (nm : Lean.Name) (k n : Nat) :
    zextLam? n (zextFn nm k n) = some (nm, k) := by
  show (if bitVecE? (bitVecE n) = some n ∧ natE? (natE n) = some n then
      (natE? (natE k)).bind fun k' =>
        if litOf? k' (litE k 0) = some 0 then some (nm, k') else none
    else none) = some (nm, k)
  exact (if_pos ⟨bitVecE?_bitVecE n, natE?_natE n⟩).trans
    (Option.bind_eq_some_iff.mpr ⟨k, natE?_natE k, if_pos (litOf?_litE k 0)⟩)

section
variable {cfg : Cfg}

theorem isSigHead_self (hd : cfg.isDom cfg.dom = true) :
    isSigHead cfg (.app (.const ``Sparkle.Core.Signal.Signal [.zero]) cfg.dom) = true := hd

theorem isFunctorInst_self (hd : cfg.isDom cfg.dom = true) :
    isFunctorInst cfg
      (.app (.const ``Sparkle.Core.Signal.instFunctorSignal [.zero]) cfg.dom) = true := hd

theorem isHiInst_self (hd : cfg.isDom cfg.dom = true) (k n : Nat) :
    isHiInst cfg k n
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat [])
        (natE k)) cfg.dom) (natE n)) = true := by
  show decide (natE? (natE k) = some k ∧ cfg.isDom cfg.dom = true ∧
    natE? (natE n) = some n) = true
  exact decide_eq_true ⟨natE?_natE k, hd, natE?_natE n⟩

theorem isLoInst_self (hd : cfg.isDom cfg.dom = true) (m k : Nat) :
    isLoInst cfg m k
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat_1 [])
        cfg.dom) (natE m)) (natE k)) = true := by
  show decide (cfg.isDom cfg.dom = true ∧ natE? (natE m) = some m ∧
    natE? (natE k) = some k) = true
  exact decide_eq_true ⟨hd, natE?_natE m, natE?_natE k⟩

/-! ## The added readers on their own quotations -/

theorem readBitsNum_eval (hd : cfg.isDom cfg.dom = true) {w v : Nat}
    (hv : v < 2 ^ w ∧ 0 < w) :
    readBitsNum cfg ``Sparkle.Core.Signal.Signal.pure [.zero] cfg.dom (bitVecE w)
      (numLitE w v) = some ⟨.bits w, .bitsNum w v⟩ := by
  unfold readBitsNum
  refine (if_pos ⟨rfl, rfl, hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨w, bitVecE?_bitVecE w, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨v, numLitOf?_self w v, ?_⟩
  exact if_pos hv

theorem readSetw_eval (hd : cfg.isDom cfg.dom = true) {w w' : Nat} (hpos : 0 < w')
    {r4 : Option AnyTerm} {a : Term (.bits w)} (h4 : r4 = some ⟨.bits w, a⟩) :
    readSetw cfg ``Sparkle.Core.Signal.Signal.map [.zero] cfg.dom (bitVecE w) (bitVecE w')
      (setwFn w w') r4 = some ⟨.bits w', .setw w' a⟩ := by
  unfold readSetw
  refine (if_pos ⟨rfl, rfl, hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨w, bitVecE?_bitVecE w, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨w', bitVecE?_bitVecE w', ?_⟩
  refine (if_pos ⟨isSetwFn_self w w', hpos⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h4, asBits_self w a⟩, ?_⟩
  rfl

theorem readSlice_eval (hd : cfg.isDom cfg.dom = true) {nm : Lean.Name} {w st len : Nat}
    (hok : 0 < len ∧ st + len ≤ w) {r4 : Option AnyTerm} {a : Term (.bits w)}
    (h4 : r4 = some ⟨.bits w, a⟩) :
    readSlice cfg ``Sparkle.Core.Signal.Signal.map [.zero] cfg.dom (bitVecE w) (bitVecE len)
      (sliceFn nm w st len) r4 = some ⟨.bits len, .slice nm st len a⟩ := by
  unfold readSlice
  refine (if_pos ⟨rfl, rfl, hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨w, bitVecE?_bitVecE w, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨len, bitVecE?_bitVecE len, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨(nm, st), sliceLam?_self nm w st len, ?_⟩
  refine (if_pos hok).trans ?_
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h4, asBits_self w a⟩, ?_⟩
  rfl

theorem readZext_eval (hd : cfg.isDom cfg.dom = true) {nm : Lean.Name} {k n : Nat}
    (hpos : 0 < k) {r4 : Option AnyTerm} {a : Term (.bits n)}
    (h4 : r4 = some ⟨.bits n, a⟩) :
    readZext cfg ``Sparkle.Core.Signal.Signal.map [.zero] cfg.dom (bitVecE n)
      (bitVecE (k + n)) (zextFn nm k n) r4 = some ⟨.bits (k + n), .zextMap nm k a⟩ := by
  unfold readZext
  refine (if_pos ⟨rfl, rfl, hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨n, bitVecE?_bitVecE n, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨(nm, k), zextLam?_self nm k n, ?_⟩
  refine (if_pos ⟨bitVecE?_bitVecE (k + n), hpos⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h4, asBits_self n a⟩, ?_⟩
  rfl

theorem readSliceF_eval (hd : cfg.isDom cfg.dom = true) {nm : Lean.Name} {w st len : Nat}
    (hok : 0 < len ∧ st + len ≤ w) {r5 : Option AnyTerm} {a : Term (.bits w)}
    (h5 : r5 = some ⟨.bits w, a⟩) :
    readSliceF cfg ``Functor.map [.zero, .zero]
      (.app (.const ``Sparkle.Core.Signal.Signal [.zero]) cfg.dom)
      (.app (.const ``Sparkle.Core.Signal.instFunctorSignal [.zero]) cfg.dom)
      (bitVecE w) (bitVecE len) (sliceFn nm w st len) r5 =
      some ⟨.bits len, .sliceF nm st len a⟩ := by
  unfold readSliceF
  refine (if_pos ⟨rfl, rfl, isSigHead_self hd, isFunctorInst_self hd⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨w, bitVecE?_bitVecE w, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨len, bitVecE?_bitVecE len, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨(nm, st), sliceLam?_self nm w st len, ?_⟩
  refine (if_pos hok).trans ?_
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h5, asBits_self w a⟩, ?_⟩
  rfl

theorem readConcatHi_eval (hd : cfg.isDom cfg.dom = true) {k v n : Nat} (hk : 0 < k)
    (hv : v < 2 ^ k) {r5 : Option AnyTerm} {b : Term (.bits n)}
    (h5 : r5 = some ⟨.bits n, b⟩) :
    readConcatHi cfg ``HAppend.hAppend [.zero, .zero, .zero] (bitVecE k) (sigT cfg.dom n)
      (sigT cfg.dom (k + n))
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat [])
        (natE k)) cfg.dom) (natE n)) (litE k v) r5 =
      some ⟨.bits (k + n), .concatLitHi k v b⟩ := by
  unfold readConcatHi
  refine (if_pos ⟨rfl, rfl⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨k, bitVecE?_bitVecE k, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨n, sigBitsT?_sigT hd n, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨v, litOf?_litE k v, ?_⟩
  refine (if_pos ⟨sigBitsT?_sigT hd (k + n), isHiInst_self hd k n, hk, hv⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr
    ⟨b, Option.bind_eq_some_iff.mpr ⟨_, h5, asBits_self n b⟩, ?_⟩
  rfl

theorem readConcatLo_eval (hd : cfg.isDom cfg.dom = true) {m k v : Nat} (hk : 0 < k)
    (hv : v < 2 ^ k) {r4 : Option AnyTerm} {a : Term (.bits m)}
    (h4 : r4 = some ⟨.bits m, a⟩) :
    readConcatLo cfg ``HAppend.hAppend [.zero, .zero, .zero] (sigT cfg.dom m) (bitVecE k)
      (sigT cfg.dom (m + k))
      (.app (.app (.app (.const ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat_1 [])
        cfg.dom) (natE m)) (natE k)) (litE k v) r4 =
      some ⟨.bits (m + k), .concatLitLo a k v⟩ := by
  unfold readConcatLo
  refine (if_pos ⟨rfl, rfl⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr ⟨m, sigBitsT?_sigT hd m, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨k, bitVecE?_bitVecE k, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨v, litOf?_litE k v, ?_⟩
  refine (if_pos ⟨sigBitsT?_sigT hd (m + k), isLoInst_self hd m k, hk, hv⟩).trans ?_
  refine Option.bind_eq_some_iff.mpr
    ⟨a, Option.bind_eq_some_iff.mpr ⟨_, h4, asBits_self m a⟩, ?_⟩
  rfl

/-! ## The other readers refuse -/

/-- The BitVec literal reader refuses a payload that is no `BitVec.ofNat`. -/
theorem readBitsLit_none {c : Lean.Name} {ls : List Lean.Level} {x0 x1 : Lean.Expr}
    (x2 : Lean.Expr) (h : ∀ w, litOf? w x2 = none) : readBitsLit cfg c ls x0 x1 x2 = none := by
  unfold readBitsLit
  by_cases hg : c = ``Sparkle.Core.Signal.Signal.pure ∧ lvl1 ls = true ∧ cfg.isDom x0 = true
  · refine (if_pos hg).trans ?_
    cases bitVecE? x1 with
    | none => rfl
    | some w => exact bind_none_of (h w) _
  · exact if_neg hg

theorem readBoolNot_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 : Lean.Expr}
    {r2 : Option AnyTerm} (hn : c ≠ ``Complement.complement) :
    readBoolNot cfg c ls x0 x1 r2 = none := by
  unfold readBoolNot
  exact if_neg (fun g => hn g.1)

theorem read3_num {ls : List Lean.Level} {x0 : Lean.Expr} {r2 : Option AnyTerm}
    (w v : Nat) :
    read3 cfg ``Sparkle.Core.Signal.Signal.pure ls x0 (bitVecE w) (numLitE w v) r2 = none := by
  unfold read3
  exact (alt_none_left (readBoolLit_bits w)).trans
    ((alt_none_left (readBitsLit_none (numLitE w v) (fun _ => rfl))).trans
      (readBoolNot_head ne_pure_compl))

theorem readBoolEq_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr}
    {r3 r4 : Option AnyTerm} (hn : c ≠ ``Sparkle.Core.Signal.Signal.beq) :
    readBoolEq cfg c ls x0 x1 x2 r3 r4 = none := by
  unfold readBoolEq
  exact if_neg (fun g => hn g.1)

theorem readBitsEq_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr}
    {r3 r4 : Option AnyTerm} (hn : c ≠ ``Sparkle.Core.Signal.Signal.beq) :
    readBitsEq cfg c ls x0 x1 x2 r3 r4 = none := by
  unfold readBitsEq
  exact if_neg (fun g => hn g.1)

/-- The five-argument core readers refuse a head that is neither `mux` nor
`beq`. -/
theorem read5_none {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr}
    {r2 r3 r4 : Option AnyTerm} (h1 : c ≠ ``Sparkle.Core.Signal.Signal.mux)
    (h2 : c ≠ ``Sparkle.Core.Signal.Signal.beq) :
    read5 cfg c ls x0 x1 x2 r2 r3 r4 = none := by
  unfold read5
  exact (alt_none_left (readMuxBool_head h1)).trans
    ((alt_none_left (readMuxBits_head h1)).trans
      ((alt_none_left (readBoolEq_head h2)).trans (readBitsEq_head h2)))

/-- The `setWidth` reader refuses a function argument that is no
`BitVec.setWidth` application. -/
theorem readSetw_none {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr}
    {r4 : Option AnyTerm} (x3 : Lean.Expr) (h : ∀ w w', isSetwFn w w' x3 = false) :
    readSetw cfg c ls x0 x1 x2 x3 r4 = none := by
  unfold readSetw
  by_cases hg : c = ``Sparkle.Core.Signal.Signal.map ∧ lvl1 ls = true ∧ cfg.isDom x0 = true
  · refine (if_pos hg).trans ?_
    cases bitVecE? x1 with
    | none => rfl
    | some w =>
      cases bitVecE? x2 with
      | none => rfl
      | some w' => exact if_neg (fun g => false_ne ((h w w').symm.trans g.1))
  · exact if_neg hg

/-- The slice reader refuses a function argument that is no slice lambda. -/
theorem readSlice_none {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr}
    {r4 : Option AnyTerm} (x3 : Lean.Expr) (h : ∀ w len, sliceLam? w len x3 = none) :
    readSlice cfg c ls x0 x1 x2 x3 r4 = none := by
  unfold readSlice
  by_cases hg : c = ``Sparkle.Core.Signal.Signal.map ∧ lvl1 ls = true ∧ cfg.isDom x0 = true
  · refine (if_pos hg).trans ?_
    cases bitVecE? x1 with
    | none => rfl
    | some w =>
      cases bitVecE? x2 with
      | none => rfl
      | some len => exact bind_none_of (h w len) _
  · exact if_neg hg

theorem readBoolBinary_head {c : Lean.Name} {ls : List Lean.Level}
    {x0 x1 x2 x3 : Lean.Expr} {r4 r5 : Option AnyTerm} (hn : boolBinOf? c = none) :
    readBoolBinary cfg c ls x0 x1 x2 x3 r4 r5 = none := by
  unfold readBoolBinary
  by_cases hg : lvl3 ls = true ∧ isSigBoolT cfg x0 = true ∧ isSigBoolT cfg x1 = true ∧
      isSigBoolT cfg x2 = true
  · exact (if_pos hg).trans (bind_none_of hn _)
  · exact if_neg hg

/-- The Bool operator reader refuses a first type argument that is no Bool
Signal type. -/
theorem readBoolBinary_sig {c : Lean.Name} {ls : List Lean.Level} {x1 x2 x3 : Lean.Expr}
    {r4 r5 : Option AnyTerm} (x0 : Lean.Expr) (h0 : isSigBoolT cfg x0 = false) :
    readBoolBinary cfg c ls x0 x1 x2 x3 r4 r5 = none := by
  unfold readBoolBinary
  exact if_neg (fun g => false_ne (h0.symm.trans g.2.1))

theorem readConcat_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr}
    {r4 r5 : Option AnyTerm} (hn : c ≠ ``HAppend.hAppend) :
    readConcat cfg c ls x0 x1 x2 x3 r4 r5 = none := by
  unfold readConcat
  exact if_neg (fun g => hn g.1)

/-- The Signal concatenation reader refuses a first operand type that is no
BitVec Signal type. -/
theorem readConcat_x0 {c : Lean.Name} {ls : List Lean.Level} {x1 x2 x3 : Lean.Expr}
    {r4 r5 : Option AnyTerm} (x0 : Lean.Expr) (h0 : sigBitsT? cfg x0 = none) :
    readConcat cfg c ls x0 x1 x2 x3 r4 r5 = none := by
  unfold readConcat
  by_cases hg : c = ``HAppend.hAppend ∧ lvl3 ls = true
  · exact (if_pos hg).trans (bind_none_of h0 _)
  · exact if_neg hg

/-- … and a second operand type that is no BitVec Signal type. -/
theorem readConcat_x1 {c : Lean.Name} {ls : List Lean.Level} {x0 x2 x3 : Lean.Expr}
    {r4 r5 : Option AnyTerm} (x1 : Lean.Expr) (h1 : sigBitsT? cfg x1 = none) :
    readConcat cfg c ls x0 x1 x2 x3 r4 r5 = none := by
  unfold readConcat
  by_cases hg : c = ``HAppend.hAppend ∧ lvl3 ls = true
  · exact (if_pos hg).trans (bind_bind_none _ _ _ h1)
  · exact if_neg hg

theorem read6_fmap {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr}
    {r4 r5 : Option AnyTerm} : read6 cfg ``Functor.map ls x0 x1 x2 x3 r4 r5 = none := by
  unfold read6
  exact (alt_none_left (readBinary_head binOf?_fmap)).trans
    ((alt_none_left (readBoolBinary_head boolBinOf?_fmap)).trans
      (readConcat_head ne_fmap_append))

theorem read6_hi {ls : List Lean.Level} {x1 x2 x3 : Lean.Expr} {r4 r5 : Option AnyTerm}
    (k : Nat) : read6 cfg ``HAppend.hAppend ls (bitVecE k) x1 x2 x3 r4 r5 = none := by
  unfold read6
  exact (alt_none_left (readBinary_head binOf?_append)).trans
    ((alt_none_left (readBoolBinary_sig (bitVecE k) rfl)).trans
      (readConcat_x0 (bitVecE k) rfl))

theorem read6_lo {ls : List Lean.Level} {x2 x3 : Lean.Expr} {r4 r5 : Option AnyTerm}
    (d : Lean.Expr) (m k : Nat) :
    read6 cfg ``HAppend.hAppend ls (sigT d m) (bitVecE k) x2 x3 r4 r5 = none := by
  unfold read6
  exact (alt_none_left (readBinary_head binOf?_append)).trans
    ((alt_none_left (readBoolBinary_bits d m)).trans (readConcat_x1 (bitVecE k) rfl))

theorem readSliceF_head {c : Lean.Name} {ls : List Lean.Level}
    {x0 x1 x2 x3 x4 : Lean.Expr} {r5 : Option AnyTerm} (hn : c ≠ ``Functor.map) :
    readSliceF cfg c ls x0 x1 x2 x3 x4 r5 = none := by
  unfold readSliceF
  exact if_neg (fun g => hn g.1)

/-- The literal-high reader refuses a first type argument that is no BitVec
type. -/
theorem readConcatHi_x0 {c : Lean.Name} {ls : List Lean.Level} {x1 x2 x3 x4 : Lean.Expr}
    {r5 : Option AnyTerm} (x0 : Lean.Expr) (h0 : bitVecE? x0 = none) :
    readConcatHi cfg c ls x0 x1 x2 x3 x4 r5 = none := by
  unfold readConcatHi
  by_cases hg : c = ``HAppend.hAppend ∧ lvl3 ls = true
  · exact (if_pos hg).trans (bind_none_of h0 _)
  · exact if_neg hg

/-! ## The extended reader on an application, by arity -/

theorem readTerm2_app3 {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} :
    readTerm2 cfg (.app (.app (.app (.const c ls) x0) x1) x2) =
      alt (read3 cfg c ls x0 x1 x2 (readTerm2 cfg x2)) (readBitsNum cfg c ls x0 x1 x2) := rfl

theorem readTerm2_app4 {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr} :
    readTerm2 cfg (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) =
      alt (readCompare cfg c ls x0 x1 (readTerm2 cfg x2) (readTerm2 cfg x3)) none := rfl

theorem readTerm2_app5 {c : Lean.Name} {ls : List Lean.Level}
    {x0 x1 x2 x3 x4 : Lean.Expr} :
    readTerm2 cfg (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) =
      alt (read5 cfg c ls x0 x1 x2 (readTerm2 cfg x2) (readTerm2 cfg x3) (readTerm2 cfg x4))
        (alt (readSetw cfg c ls x0 x1 x2 x3 (readTerm2 cfg x4))
          (alt (readSlice cfg c ls x0 x1 x2 x3 (readTerm2 cfg x4))
            (readZext cfg c ls x0 x1 x2 x3 (readTerm2 cfg x4)))) := rfl

theorem readTerm2_app6 {c : Lean.Name} {ls : List Lean.Level}
    {x0 x1 x2 x3 x4 x5 : Lean.Expr} :
    readTerm2 cfg
        (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) =
      alt (read6 cfg c ls x0 x1 x2 x3 (readTerm2 cfg x4) (readTerm2 cfg x5))
        (alt (readSliceF cfg c ls x0 x1 x2 x3 x4 (readTerm2 cfg x5))
          (alt (readConcatHi cfg c ls x0 x1 x2 x3 x4 (readTerm2 cfg x5))
            (readConcatLo cfg c ls x0 x1 x2 x3 x5 (readTerm2 cfg x4)))) := rfl

end

/-! ## Completeness -/

/-- The terms built from the eighteen node kinds `readTerm2` reads. -/
def core2 : {s : SType} → Term s → Prop
  | _, .boolInput _ => True
  | _, .bitsInput _ _ => True
  | _, .boolLit _ => True
  | _, .bitsLit _ _ => True
  | _, .bitsNum _ _ => True
  | _, .binary _ a b => core2 a ∧ core2 b
  | _, .compare _ a b => core2 a ∧ core2 b
  | _, .boolBinary _ a b => core2 a ∧ core2 b
  | _, .boolNot a => core2 a
  | _, .boolEq a b => core2 a ∧ core2 b
  | _, .mux c a b => core2 c ∧ core2 a ∧ core2 b
  | _, .setw _ a => core2 a
  | _, .slice _ _ _ a => core2 a
  | _, .concat a b => core2 a ∧ core2 b
  | _, .concatLitHi _ _ b => core2 b
  | _, .concatLitLo a _ _ => core2 a
  | _, .zextMap _ _ a => core2 a
  | _, .sliceF _ _ _ a => core2 a
  | _, .appCompare _ _ _ => False
  | _, .appBool _ _ _ => False
  | _, .appBool2 _ _ _ => False

/-- A core term is a term of the extended kinds. -/
theorem core2_of_core : ∀ {s : SType} (t : Term s), core t → core2 t
  | _, .boolInput _, _ => trivial
  | _, .bitsInput _ _, _ => trivial
  | _, .boolLit _, _ => trivial
  | _, .bitsLit _ _, _ => trivial
  | _, .bitsNum _ _, h => False.elim h
  | _, .binary _ a b, h => by
    obtain ⟨ha, hb⟩ := h
    exact And.intro (core2_of_core a ha) (core2_of_core b hb)
  | _, .compare _ a b, h => by
    obtain ⟨ha, hb⟩ := h
    exact And.intro (core2_of_core a ha) (core2_of_core b hb)
  | _, .boolBinary _ a b, h => by
    obtain ⟨ha, hb⟩ := h
    exact And.intro (core2_of_core a ha) (core2_of_core b hb)
  | _, .boolNot a, h => core2_of_core a h
  | _, .boolEq a b, h => by
    obtain ⟨ha, hb⟩ := h
    exact And.intro (core2_of_core a ha) (core2_of_core b hb)
  | _, .mux c a b, h => by
    obtain ⟨hc, ha, hb⟩ := h
    exact And.intro (core2_of_core c hc) (And.intro (core2_of_core a ha) (core2_of_core b hb))
  | _, .setw _ _, h => False.elim h
  | _, .slice _ _ _ _, h => False.elim h
  | _, .concat a b, h => by
    obtain ⟨ha, hb⟩ := h
    exact And.intro (core2_of_core a ha) (core2_of_core b hb)
  | _, .concatLitHi _ _ _, h => False.elim h
  | _, .concatLitLo _ _ _, h => False.elim h
  | _, .zextMap _ _ _, h => False.elim h
  | _, .sliceF _ _ _ _, h => False.elim h
  | _, .appCompare _ _ _, h => False.elim h
  | _, .appBool _ _ _, h => False.elim h
  | _, .appBool2 _ _ _, h => False.elim h

/-- **Completeness of the extended reader.** It returns `t` on the quotation
of every well-formed term `t` of the eighteen kinds. -/
theorem readTerm2_quote {cfg : Cfg} (hc : Complete cfg) :
    ∀ {s : SType} (t : Term s), core2 t → t.WF cfg.kb cfg.kv cfg.vw →
      readTerm2 cfg (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩
  | _, .boolInput j, _, hj => by
    obtain ⟨i, hq, hin⟩ := hc.boolOut j hj
    show readTerm2 cfg (cfg.bools j) = _
    rw [hq]
    show readInput cfg i = _
    unfold readInput
    exact alt_some_left (Option.bind_eq_some_iff.mpr ⟨j, hin, rfl⟩)
  | _, .bitsInput w j, _, hwf => by
    obtain ⟨h1, h2, h3⟩ := hwf
    obtain ⟨i, hq, hnb, hin⟩ := hc.bitsOut j w h1 h2 h3
    show readTerm2 cfg (cfg.bits j) = _
    rw [hq]
    show readInput cfg i = _
    unfold readInput
    exact (alt_none_left (bind_none_of hnb _)).trans
      (Option.bind_eq_some_iff.mpr ⟨(w, j), hin, rfl⟩)
  | _, .boolLit b, _, _ => by
    cases b
    · exact readTerm2_app3.trans (alt_some_left (read3_boolLit_false hc.domOk))
    · exact readTerm2_app3.trans (alt_some_left (read3_boolLit_true hc.domOk))
  | _, .bitsLit w v, _, hwf =>
    readTerm2_app3.trans (alt_some_left (read3_bitsLit hc.domOk hwf))
  | _, .bitsNum w v, _, hwf =>
    readTerm2_app3.trans ((alt_none_left (read3_num w v)).trans (readBitsNum_eval hc.domOk hwf))
  | _, .binary op a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    exact readTerm2_app6.trans (alt_some_left
      (read6_binary hc.domOk op (readTerm2_quote hc a ca wa) (readTerm2_quote hc b cb wb)))
  | _, .compare op a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    have iha := readTerm2_quote hc a ca wa
    have ihb := readTerm2_quote hc b cb wb
    cases op
    · exact readTerm2_app4.trans (alt_some_left
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb))
    · exact readTerm2_app4.trans (alt_some_left
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb))
    · exact readTerm2_app4.trans (alt_some_left
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb))
    · exact readTerm2_app4.trans (alt_some_left
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb))
    · exact readTerm2_app5.trans (alt_some_left (read5_bitsEq hc.domOk iha ihb))
  | _, .boolBinary k a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    exact readTerm2_app6.trans (alt_some_left
      (read6_boolBinary hc.domOk k (readTerm2_quote hc a ca wa) (readTerm2_quote hc b cb wb)))
  | _, .boolNot a, hcore, hwf =>
    readTerm2_app3.trans
      (alt_some_left (read3_boolNot hc.domOk (readTerm2_quote hc a hcore hwf)))
  | _, .boolEq a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    exact readTerm2_app5.trans (alt_some_left
      (read5_boolEq hc.domOk (readTerm2_quote hc a ca wa) (readTerm2_quote hc b cb wb)))
  | s, .mux c a b, hcore, hwf => by
    obtain ⟨cc, ca, cb⟩ := hcore
    obtain ⟨wc, wa, wb⟩ := hwf
    have ihc := readTerm2_quote hc c cc wc
    have iha := readTerm2_quote hc a ca wa
    have ihb := readTerm2_quote hc b cb wb
    cases s
    · exact readTerm2_app5.trans (alt_some_left (read5_muxBool hc.domOk ihc iha ihb))
    · exact readTerm2_app5.trans (alt_some_left (read5_muxBits hc.domOk ihc iha ihb))
  | _, .setw w' a, hcore, hwf => by
    obtain ⟨wa, hpos⟩ := hwf
    exact readTerm2_app5.trans ((alt_none_left (read5_none ne_map_mux ne_map_beq)).trans
      (alt_some_left (readSetw_eval hc.domOk hpos (readTerm2_quote hc a hcore wa))))
  | _, .slice nm st len (w := w) a, hcore, hwf => by
    obtain ⟨wa, hok⟩ := hwf
    exact readTerm2_app5.trans ((alt_none_left (read5_none ne_map_mux ne_map_beq)).trans
      ((alt_none_left (readSetw_none (sliceFn nm w st len) (fun _ _ => rfl))).trans
        (alt_some_left (readSlice_eval hc.domOk hok (readTerm2_quote hc a hcore wa)))))
  | _, .concat a b, hcore, hwf => by
    obtain ⟨ca, cb⟩ := hcore
    obtain ⟨wa, wb⟩ := hwf
    exact readTerm2_app6.trans (alt_some_left
      (read6_concat hc.domOk (readTerm2_quote hc a ca wa) (readTerm2_quote hc b cb wb)))
  | _, .concatLitHi k v b, hcore, hwf => by
    obtain ⟨wb, hk, hv⟩ := hwf
    exact readTerm2_app6.trans ((alt_none_left (read6_hi k)).trans
      ((alt_none_left (readSliceF_head ne_append_fmap)).trans
        (alt_some_left (readConcatHi_eval hc.domOk hk hv (readTerm2_quote hc b hcore wb)))))
  | _, .concatLitLo (m := m) a k v, hcore, hwf => by
    obtain ⟨wa, hk, hv⟩ := hwf
    exact readTerm2_app6.trans ((alt_none_left (read6_lo cfg.dom m k)).trans
      ((alt_none_left (readSliceF_head ne_append_fmap)).trans
        ((alt_none_left (readConcatHi_x0 (sigT cfg.dom m) rfl)).trans
          (readConcatLo_eval hc.domOk hk hv (readTerm2_quote hc a hcore wa)))))
  | _, .zextMap nm k (n := n) a, hcore, hwf => by
    obtain ⟨wa, hpos⟩ := hwf
    exact readTerm2_app5.trans ((alt_none_left (read5_none ne_map_mux ne_map_beq)).trans
      ((alt_none_left (readSetw_none (zextFn nm k n) (fun _ _ => rfl))).trans
        ((alt_none_left (readSlice_none (zextFn nm k n) (fun _ _ => rfl))).trans
          (readZext_eval hc.domOk hpos (readTerm2_quote hc a hcore wa)))))
  | _, .sliceF nm st len a, hcore, hwf => by
    obtain ⟨wa, hok⟩ := hwf
    exact readTerm2_app6.trans ((alt_none_left read6_fmap).trans
      (alt_some_left (readSliceF_eval hc.domOk hok (readTerm2_quote hc a hcore wa))))
  | _, .appCompare _ _ _, hcore, _ => False.elim hcore
  | _, .appBool _ _ _, hcore, _ => False.elim hcore
  | _, .appBool2 _ _ _, hcore, _ => False.elim hcore

/-- **`quote` is injective on well-formed terms of the eighteen kinds.** -/
theorem quote2_injective {cfg : Cfg} (hc : Complete cfg) {s s' : SType} (t : Term s)
    (t' : Term s') (ht : core2 t) (ht' : core2 t') (hw : t.WF cfg.kb cfg.kv cfg.vw)
    (hw' : t'.WF cfg.kb cfg.kv cfg.vw)
    (h : quote cfg.dom cfg.bools cfg.bits t = quote cfg.dom cfg.bools cfg.bits t') :
    (⟨s, t⟩ : AnyTerm) = ⟨s', t'⟩ := by
  have h1 := readTerm2_quote hc t ht hw
  have h2 := readTerm2_quote hc t' ht' hw'
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-- On the quotation of a well-formed core term the extended reader returns
what the core reader returns. -/
theorem readTerm2_extends_on_quotes {cfg : Cfg} (hc : Complete cfg) {s : SType}
    (t : Term s) (ht : core t) (hw : t.WF cfg.kb cfg.kv cfg.vw) :
    readTerm2 cfg (quote cfg.dom cfg.bools cfg.bits t) =
      readTerm cfg (quote cfg.dom cfg.bools cfg.bits t) :=
  (readTerm2_quote hc t (core2_of_core t ht) hw).trans (readTerm_quote hc t ht hw).symm

end Tools.ShippingReaderComplete2
