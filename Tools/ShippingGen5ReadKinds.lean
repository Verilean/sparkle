import Tools.ShippingReaderApp
import Tools.ShippingReaderComplete2
import Tools.ShippingReaderKinds
import Tools.ShippingReaderMachine
import Sparkle.Compiler.MachTupleIn
import Sparkle.Compiler.MachRawSurface

set_option autoImplicit false

/-! # DG-READKINDS: completeness of `readN` on all 21 kinds, and the `readN` machine lemmas (G5)

Statements are those of `scripts/gen5/DG_READKINDS_FREEZE.md` rev2 (3f79600f), §2 U1-U4.

Proved here (against the existing, built readers; no definition of `ShippingReaderApp` is changed)
* `readN_quote`: `readN cfg k` returns `t` on the quotation of a well-formed `t` with `liftDepth t ≤ k`
  (all 21 kinds); `readN_expr_quote`, `quote_injective` (all 21 kinds), `readTot_quote`,
  `readN_mono_on_quotes` (monotonicity on quotations only).
* `machine_body_of_readN`, `machine_wf_of_readN`: the `readN` forms of the `readTerm` machine lemmas.
* `kindsCfg_quote_args`, `packed_wf_cfg`, `readTot_of_quote_body`: a body that IS the quotation of
  `d.packed` is read.

NOT proved here (kept OPEN by the freeze)
* `hq` (body-is-quotation) for a body produced by a run: it is a premise of `readTot_of_quote_body`.
* `RootFacts` / `rootFloat` / `packTupleInputs`: no supply. A definition of `RootFacts` below is a type only
  and does not count as a producer.
* Normalization / production coverage, the general `readN k e = some r → readN (k+1) e = some r`. -/
namespace Tools.ShippingGen5ReadKinds
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingReaderTerm Tools.ShippingReaderInputs
open Tools.ShippingReaderNodes2 Tools.ShippingReaderApp
open Tools.ShippingReaderComplete Tools.ShippingReaderComplete2
open Tools.ShippingReaderKinds Tools.ShippingReaderMachine
open Tools.ShippingMachineAuto Tools.ShippingEntrySoundness Tools.ShippingMuxTypeSoundness
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedSourceBridge (inputExpr)

/-! ## 2.0 Definitions -/

/-- Nesting depth of applicative lifts through FIRST operands (what `readN` levels pay for). -/
def liftDepth : {s : SType} → Term s → Nat
  | _, .boolInput _ => 0
  | _, .bitsInput _ _ => 0
  | _, .boolLit _ => 0
  | _, .bitsLit _ _ => 0
  | _, .bitsNum _ _ => 0
  | _, .binary _ a b => max (liftDepth a) (liftDepth b)
  | _, .compare _ a b => max (liftDepth a) (liftDepth b)
  | _, .boolBinary _ a b => max (liftDepth a) (liftDepth b)
  | _, .boolNot a => liftDepth a
  | _, .boolEq a b => max (liftDepth a) (liftDepth b)
  | _, .mux c a b => max (liftDepth c) (max (liftDepth a) (liftDepth b))
  | _, .setw _ a => liftDepth a
  | _, .slice _ _ _ a => liftDepth a
  | _, .concat a b => max (liftDepth a) (liftDepth b)
  | _, .concatLitHi _ _ b => liftDepth b
  | _, .concatLitLo a _ _ => liftDepth a
  | _, .zextMap _ _ a => liftDepth a
  | _, .sliceF _ _ _ a => liftDepth a
  | _, .appCompare _ a b => max (liftDepth a + 1) (liftDepth b)
  | _, .appBool _ a b => max (liftDepth a + 1) (liftDepth b)
  | _, .appBool2 _ a b => max (liftDepth a + 1) (liftDepth b)

/-- Structural size of an expression (own definition, so its equations are plain). -/
def exprSize : Lean.Expr → Nat
  | .app f a => exprSize f + exprSize a + 1
  | .lam _ t b _ => exprSize t + exprSize b + 1
  | .forallE _ t b _ => exprSize t + exprSize b + 1
  | .letE _ t v b _ => exprSize t + exprSize v + exprSize b + 1
  | .mdata _ e => exprSize e + 1
  | .proj _ _ e => exprSize e + 1
  | _ => 1

/-- The total reader with its level taken from the expression. -/
def readTot (cfg : Cfg) (e : Lean.Expr) : Option AnyTerm := readN cfg (exprSize e) e

/-! ## Small tools -/

theorem eqE_self (a : Lean.Expr) : eqE a a = true :=
  @decide_eq_true (a = a) (Sparkle.Compiler.ExprDecEq.exprDecEq a a) rfl

theorem eqE_true_iff {a b : Lean.Expr} : eqE a b = true ↔ a = b :=
  ⟨eqE_sound, fun h => h ▸ eqE_self a⟩

theorem core2_of_liftDepth_zero : ∀ {s : SType} (t : Term s), liftDepth t = 0 → core2 t
  | _, .boolInput _, _ => trivial
  | _, .bitsInput _ _, _ => trivial
  | _, .boolLit _, _ => trivial
  | _, .bitsLit _ _, _ => trivial
  | _, .bitsNum _ _, _ => trivial
  | _, .binary _ a b, h => by
    simp only [liftDepth] at h
    exact And.intro (core2_of_liftDepth_zero a (by omega)) (core2_of_liftDepth_zero b (by omega))
  | _, .compare _ a b, h => by
    simp only [liftDepth] at h
    exact And.intro (core2_of_liftDepth_zero a (by omega)) (core2_of_liftDepth_zero b (by omega))
  | _, .boolBinary _ a b, h => by
    simp only [liftDepth] at h
    exact And.intro (core2_of_liftDepth_zero a (by omega)) (core2_of_liftDepth_zero b (by omega))
  | _, .boolNot a, h => core2_of_liftDepth_zero a h
  | _, .boolEq a b, h => by
    simp only [liftDepth] at h
    exact And.intro (core2_of_liftDepth_zero a (by omega)) (core2_of_liftDepth_zero b (by omega))
  | _, .mux c a b, h => by
    simp only [liftDepth] at h
    exact And.intro (core2_of_liftDepth_zero c (by omega))
      (And.intro (core2_of_liftDepth_zero a (by omega)) (core2_of_liftDepth_zero b (by omega)))
  | _, .setw _ a, h => core2_of_liftDepth_zero a h
  | _, .slice _ _ _ a, h => core2_of_liftDepth_zero a h
  | _, .concat a b, h => by
    simp only [liftDepth] at h
    exact And.intro (core2_of_liftDepth_zero a (by omega)) (core2_of_liftDepth_zero b (by omega))
  | _, .concatLitHi _ _ b, h => core2_of_liftDepth_zero b h
  | _, .concatLitLo a _ _, h => core2_of_liftDepth_zero a h
  | _, .zextMap _ _ a, h => core2_of_liftDepth_zero a h
  | _, .sliceF _ _ _ a, h => core2_of_liftDepth_zero a h
  | _, .appCompare _ a b, h => by simp only [liftDepth] at h; omega
  | _, .appBool _ a b, h => by simp only [liftDepth] at h; omega
  | _, .appBool2 _ a b, h => by simp only [liftDepth] at h; omega

/-! ## U1a — operator tables on the quoted heads -/

theorem boolOp?_self (dom : Lean.Expr) (op : SignalBoolBinKind) :
    boolOp? dom (mapHeadE dom (.const ``Bool []) (appBoolBodyE op)) = some op := by
  cases op <;>
  simp [boolOp?, pickBy, eqE_true_iff, mapHeadE, appLamE, appBoolBodyE, Lean.mkAppB, Lean.mkApp4, Lean.mkApp2, Lean.mkApp]

theorem bool2Op?_self (dom : Lean.Expr) (f : AppBool2) :
    bool2Op? dom (mapHeadE dom (.const ``Bool []) (appBool2BodyE f)) = some f := by
  cases f <;>
  simp [bool2Op?, pickBy, eqE_true_iff, mapHeadE, appLamE, appBool2BodyE, Lean.mkAppB, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3, Lean.mkApp2, Lean.mkApp]

theorem cmpOp?_self (dom : Lean.Expr) (w : Nat) (op : SignalCompareKind) :
    cmpOp? dom w (mapHeadE dom (bitVecE w) (appCompareBodyE op w)) = some op := by
  cases op <;>
  simp [cmpOp?, pickBy, eqE_true_iff, mapHeadE, appLamE, appCompareBodyE, Lean.mkAppB, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3, Lean.mkApp2, Lean.mkApp]

/-! ## U1d — the three lifts on their own quotations -/

section
variable {cfg : Cfg}

theorem readAp_appBool_eval (hd : cfg.isDom cfg.dom = true) (op : SignalBoolBinKind)
    {a b : Term .bool} {ra rb : Option AnyTerm}
    (ha : ra = some ⟨.bool, a⟩) (hb : rb = some ⟨.bool, b⟩) :
    readAp cfg ``Sparkle.Core.Signal.Signal.ap [.zero] cfg.dom (.const ``Bool []) (.const ``Bool [])
      (mapHeadE cfg.dom (.const ``Bool []) (appBoolBodyE op)) ra rb = some ⟨.bool, .appBool op a b⟩ := by
  subst ha hb
  unfold readAp
  refine (if_pos ⟨rfl, rfl, hd, isConst_self _⟩).trans ?_
  refine alt_some_left ?_
  unfold readApBool
  refine (if_pos (isConst_self _)).trans ?_
  rw [boolOp?_self]
  rfl

theorem readAp_appBool2_eval (hd : cfg.isDom cfg.dom = true) (f : AppBool2)
    {a b : Term .bool} {ra rb : Option AnyTerm}
    (ha : ra = some ⟨.bool, a⟩) (hb : rb = some ⟨.bool, b⟩) :
    readAp cfg ``Sparkle.Core.Signal.Signal.ap [.zero] cfg.dom (.const ``Bool []) (.const ``Bool [])
      (mapHeadE cfg.dom (.const ``Bool []) (appBool2BodyE f)) ra rb = some ⟨.bool, .appBool2 f a b⟩ := by
  subst ha hb
  have hn : readApBool cfg (.const ``Bool []) (mapHeadE cfg.dom (.const ``Bool []) (appBool2BodyE f))
      (some ⟨.bool, a⟩) (some ⟨.bool, b⟩) = none := by
    unfold readApBool
    refine (if_pos (isConst_self _)).trans ?_
    have h : boolOp? cfg.dom (mapHeadE cfg.dom (.const ``Bool []) (appBool2BodyE f)) = none := by
      cases f <;>
      simp [boolOp?, pickBy, eqE_true_iff, mapHeadE, appLamE, appBoolBodyE, appBool2BodyE, Lean.mkAppB, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3, Lean.mkApp2, Lean.mkApp]
    rw [h]
    rfl
  unfold readAp
  refine (if_pos ⟨rfl, rfl, hd, isConst_self _⟩).trans ?_
  refine (alt_none_left hn).trans ?_
  refine alt_some_left ?_
  unfold readApBool2
  refine (if_pos (isConst_self _)).trans ?_
  rw [bool2Op?_self]
  rfl

theorem readAp_appCompare_eval (hd : cfg.isDom cfg.dom = true) (op : SignalCompareKind) {w : Nat}
    {a b : Term (.bits w)} {ra rb : Option AnyTerm}
    (ha : ra = some ⟨.bits w, a⟩) (hb : rb = some ⟨.bits w, b⟩) :
    readAp cfg ``Sparkle.Core.Signal.Signal.ap [.zero] cfg.dom (bitVecE w) (.const ``Bool [])
      (mapHeadE cfg.dom (bitVecE w) (appCompareBodyE op w)) ra rb = some ⟨.bool, .appCompare op a b⟩ := by
  subst ha hb
  have hn1 : readApBool cfg (bitVecE w) (mapHeadE cfg.dom (bitVecE w) (appCompareBodyE op w))
      (some ⟨.bits w, a⟩) (some ⟨.bits w, b⟩) = none := by
    unfold readApBool
    exact if_neg (by intro h; revert h; simp [isConst, bitVecE])
  have hn2 : readApBool2 cfg (bitVecE w) (mapHeadE cfg.dom (bitVecE w) (appCompareBodyE op w))
      (some ⟨.bits w, a⟩) (some ⟨.bits w, b⟩) = none := by
    unfold readApBool2
    exact if_neg (by intro h; revert h; simp [isConst, bitVecE])
  unfold readAp
  refine (if_pos ⟨rfl, rfl, hd, isConst_self _⟩).trans ?_
  refine (alt_none_left hn1).trans ?_
  refine (alt_none_left hn2).trans ?_
  unfold readApCmp
  refine Option.bind_eq_some_iff.mpr ⟨w, bitVecE?_bitVecE w, ?_⟩
  rw [cmpOp?_self]
  refine Option.bind_eq_some_iff.mpr ⟨op, rfl, ?_⟩
  show (Option.bind (Option.bind (some ⟨SType.bits w, a⟩ : Option AnyTerm) (asBits w)) _) = _
  rw [show (some ⟨SType.bits w, a⟩ : Option AnyTerm).bind (asBits w) = some a from asBits_self w a]
  show (Option.bind ((some ⟨SType.bits w, b⟩ : Option AnyTerm).bind (asBits w)) _) = _
  rw [show (some ⟨SType.bits w, b⟩ : Option AnyTerm).bind (asBits w) = some b from asBits_self w b]
  rfl

end

/-! ## U1b — the eighteen-kind node reader refuses `Signal.ap` -/

section
variable {cfg : Cfg}

theorem ne_ap_pure : ``Sparkle.Core.Signal.Signal.ap ≠ ``Sparkle.Core.Signal.Signal.pure := by decide
theorem ne_ap_compl : ``Sparkle.Core.Signal.Signal.ap ≠ ``Complement.complement := by decide
theorem ne_ap_mux : ``Sparkle.Core.Signal.Signal.ap ≠ ``Sparkle.Core.Signal.Signal.mux := by decide
theorem ne_ap_beq : ``Sparkle.Core.Signal.Signal.ap ≠ ``Sparkle.Core.Signal.Signal.beq := by decide
theorem ne_ap_map : ``Sparkle.Core.Signal.Signal.ap ≠ ``Sparkle.Core.Signal.Signal.map := by decide
theorem ne_ap_fmap : ``Sparkle.Core.Signal.Signal.ap ≠ ``Functor.map := by decide
theorem ne_ap_append : ``Sparkle.Core.Signal.Signal.ap ≠ ``HAppend.hAppend := by decide

theorem readBitsNum_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr}
    (hn : c ≠ ``Sparkle.Core.Signal.Signal.pure) : readBitsNum cfg c ls x0 x1 x2 = none := by
  unfold readBitsNum
  exact if_neg (fun g => hn g.1)

theorem readCompare_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 : Lean.Expr}
    {r2 r3 : Option AnyTerm} (hn : cmpOf? c = none) : readCompare cfg c ls x0 x1 r2 r3 = none := by
  unfold readCompare
  by_cases hg : lvl0 ls = true ∧ cfg.isDom x0 = true
  · exact (if_pos hg).trans (bind_none_of hn _)
  · exact if_neg hg

theorem readSetw_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr}
    {r4 : Option AnyTerm} (hn : c ≠ ``Sparkle.Core.Signal.Signal.map) :
    readSetw cfg c ls x0 x1 x2 x3 r4 = none := by
  unfold readSetw
  exact if_neg (fun g => hn g.1)

theorem readSlice_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr}
    {r4 : Option AnyTerm} (hn : c ≠ ``Sparkle.Core.Signal.Signal.map) :
    readSlice cfg c ls x0 x1 x2 x3 r4 = none := by
  unfold readSlice
  exact if_neg (fun g => hn g.1)

theorem readZext_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr}
    {r4 : Option AnyTerm} (hn : c ≠ ``Sparkle.Core.Signal.Signal.map) :
    readZext cfg c ls x0 x1 x2 x3 r4 = none := by
  unfold readZext
  exact if_neg (fun g => hn g.1)

theorem readConcatHi_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr}
    {r5 : Option AnyTerm} (hn : c ≠ ``HAppend.hAppend) :
    readConcatHi cfg c ls x0 x1 x2 x3 x4 r5 = none := by
  unfold readConcatHi
  exact if_neg (fun g => hn g.1)

theorem readConcatLo_head {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr}
    {r4 : Option AnyTerm} (hn : c ≠ ``HAppend.hAppend) :
    readConcatLo cfg c ls x0 x1 x2 x3 x4 r4 = none := by
  unfold readConcatLo
  exact if_neg (fun g => hn g.1)

/-- `readNode2` by arity, on arbitrary readings (`readTerm2_app3..6` with the sub-readings abstracted). -/
theorem readNode2_app3 {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr}
    {r0 r1 r2 : Option AnyTerm} :
    readNode2 cfg c ls [(x0, r0), (x1, r1), (x2, r2)] =
      alt (read3 cfg c ls x0 x1 x2 r2) (readBitsNum cfg c ls x0 x1 x2) := rfl

theorem readNode2_app4 {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr}
    {r0 r1 r2 r3 : Option AnyTerm} :
    readNode2 cfg c ls [(x0, r0), (x1, r1), (x2, r2), (x3, r3)] =
      alt (readCompare cfg c ls x0 x1 r2 r3) none := rfl

theorem readNode2_app5 {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr}
    {r0 r1 r2 r3 r4 : Option AnyTerm} :
    readNode2 cfg c ls [(x0, r0), (x1, r1), (x2, r2), (x3, r3), (x4, r4)] =
      alt (read5 cfg c ls x0 x1 x2 r2 r3 r4)
        (alt (readSetw cfg c ls x0 x1 x2 x3 r4)
          (alt (readSlice cfg c ls x0 x1 x2 x3 r4) (readZext cfg c ls x0 x1 x2 x3 r4))) := rfl

theorem readNode2_app6 {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 x4 x5 : Lean.Expr}
    {r0 r1 r2 r3 r4 r5 : Option AnyTerm} :
    readNode2 cfg c ls [(x0, r0), (x1, r1), (x2, r2), (x3, r3), (x4, r4), (x5, r5)] =
      alt (read6 cfg c ls x0 x1 x2 x3 r4 r5)
        (alt (readSliceF cfg c ls x0 x1 x2 x3 x4 r5)
          (alt (readConcatHi cfg c ls x0 x1 x2 x3 x4 r5)
            (readConcatLo cfg c ls x0 x1 x2 x3 x5 r4))) := rfl

/-- U1b: on a `Signal.ap` head the eighteen-kind node reader gives none (any arguments). -/
theorem readNode2_ap_none {cfg : Cfg} (c : Lean.Name) (hc : c = ``Sparkle.Core.Signal.Signal.ap)
    (ls : List Lean.Level) (args : List Arg) : readNode2 cfg c ls args = none := by
  subst hc
  match args with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [(e0, _), (e1, _), (e2, r2)] =>
    show alt (read3 cfg _ ls e0 e1 e2 r2) (readBitsNum cfg _ ls e0 e1 e2) = none
    exact (alt_none_left (by
      unfold read3
      exact (alt_none_left (readBoolLit_head ne_ap_pure)).trans
        ((alt_none_left (readBitsLit_head ne_ap_pure)).trans (readBoolNot_head ne_ap_compl)))).trans
      (readBitsNum_head ne_ap_pure)
  | [(e0, _), (e1, _), (_, r2), (_, r3)] =>
    show alt (readCompare cfg _ ls e0 e1 r2 r3) none = none
    exact (alt_none_left (readCompare_head rfl)).trans rfl
  | [(e0, _), (e1, _), (e2, r2), (e3, r3), (_, r4)] =>
    rw [readNode2_app5]
    exact (alt_none_left (read5_none ne_ap_mux ne_ap_beq)).trans
      ((alt_none_left (readSetw_head ne_ap_map)).trans
        ((alt_none_left (readSlice_head ne_ap_map)).trans (readZext_head ne_ap_map)))
  | [(e0, _), (e1, _), (e2, _), (e3, _), (e4, r4), (e5, r5)] =>
    rw [readNode2_app6]
    exact (alt_none_left (by
      unfold read6
      exact (alt_none_left (readBinary_head rfl)).trans
        ((alt_none_left (readBoolBinary_head rfl)).trans (readConcat_head ne_ap_append)))).trans
      ((alt_none_left (readSliceF_head ne_ap_fmap)).trans
        ((alt_none_left (readConcatHi_head ne_ap_append)).trans (readConcatLo_head ne_ap_append)))
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

end

/-! ## U1a' — `readN (k+1)` on applications, by arity -/

section
variable {cfg : Cfg}

theorem readN_succ_app3 {k : Nat} {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} :
    readN cfg (k+1) (.app (.app (.app (.const c ls) x0) x1) x2) =
      readNode3 (readN cfg k) cfg c ls
        [(x0, readN cfg (k+1) x0), (x1, readN cfg (k+1) x1), (x2, readN cfg (k+1) x2)] := rfl

theorem readN_succ_app4 {k : Nat} {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr} :
    readN cfg (k+1) (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) =
      readNode3 (readN cfg k) cfg c ls
        [(x0, readN cfg (k+1) x0), (x1, readN cfg (k+1) x1), (x2, readN cfg (k+1) x2),
          (x3, readN cfg (k+1) x3)] := rfl

theorem readN_succ_app5 {k : Nat} {c : Lean.Name} {ls : List Lean.Level}
    {x0 x1 x2 x3 x4 : Lean.Expr} :
    readN cfg (k+1) (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) =
      readNode3 (readN cfg k) cfg c ls
        [(x0, readN cfg (k+1) x0), (x1, readN cfg (k+1) x1), (x2, readN cfg (k+1) x2),
          (x3, readN cfg (k+1) x3), (x4, readN cfg (k+1) x4)] := rfl

theorem readN_succ_app6 {k : Nat} {c : Lean.Name} {ls : List Lean.Level}
    {x0 x1 x2 x3 x4 x5 : Lean.Expr} :
    readN cfg (k+1) (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5) =
      readNode3 (readN cfg k) cfg c ls
        [(x0, readN cfg (k+1) x0), (x1, readN cfg (k+1) x1), (x2, readN cfg (k+1) x2),
          (x3, readN cfg (k+1) x3), (x4, readN cfg (k+1) x4), (x5, readN cfg (k+1) x5)] := rfl

/-- A level-`k+1` reading through the eighteen-kind node reader. -/
theorem rn3 {k : Nat} {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 : Lean.Expr} {r : AnyTerm}
    (h : readNode2 cfg c ls
      [(x0, readN cfg (k+1) x0), (x1, readN cfg (k+1) x1), (x2, readN cfg (k+1) x2)] = some r) :
    readN cfg (k+1) (.app (.app (.app (.const c ls) x0) x1) x2) = some r :=
  readN_succ_app3.trans (alt_some_left h)

theorem rn4 {k : Nat} {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 : Lean.Expr}
    {r : AnyTerm}
    (h : readNode2 cfg c ls
      [(x0, readN cfg (k+1) x0), (x1, readN cfg (k+1) x1), (x2, readN cfg (k+1) x2),
        (x3, readN cfg (k+1) x3)] = some r) :
    readN cfg (k+1) (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) = some r :=
  readN_succ_app4.trans (alt_some_left h)

theorem rn5 {k : Nat} {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 x4 : Lean.Expr}
    {r : AnyTerm}
    (h : readNode2 cfg c ls
      [(x0, readN cfg (k+1) x0), (x1, readN cfg (k+1) x1), (x2, readN cfg (k+1) x2),
        (x3, readN cfg (k+1) x3), (x4, readN cfg (k+1) x4)] = some r) :
    readN cfg (k+1) (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) = some r :=
  readN_succ_app5.trans (alt_some_left h)

theorem rn6 {k : Nat} {c : Lean.Name} {ls : List Lean.Level} {x0 x1 x2 x3 x4 x5 : Lean.Expr}
    {r : AnyTerm}
    (h : readNode2 cfg c ls
      [(x0, readN cfg (k+1) x0), (x1, readN cfg (k+1) x1), (x2, readN cfg (k+1) x2),
        (x3, readN cfg (k+1) x3), (x4, readN cfg (k+1) x4), (x5, readN cfg (k+1) x5)] = some r) :
    readN cfg (k+1) (.app (.app (.app (.app (.app (.app (.const c ls) x0) x1) x2) x3) x4) x5)
      = some r :=
  readN_succ_app6.trans (alt_some_left h)

/-- A level-`k+1` reading of an applicative lift: the node reader refuses, `readAp` decides. -/
theorem rnAp {k : Nat} {ls : List Lean.Level} {x0 x1 x2 f a b : Lean.Expr} {r : AnyTerm}
    (h : readAp cfg ``Sparkle.Core.Signal.Signal.ap ls x0 x1 x2 f (readN cfg k a)
      (readN cfg (k+1) b) = some r) :
    readN cfg (k+1) (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap ls) x0) x1) x2)
      (.app f a)) b) = some r :=
  readN_succ_app5.trans ((alt_none_left (readNode2_ap_none _ rfl _ _)).trans h)

end

/-! ## U1 — completeness of `readN` (all 21 kinds) -/

/-- **Completeness of `readN`** on all 21 kinds, at any level `k ≥ liftDepth t`. -/
theorem readN_quote {cfg : Cfg} (hc : Complete cfg) :
    ∀ {s : SType} (t : Term s) (k : Nat), liftDepth t ≤ k → t.WF cfg.kb cfg.kv cfg.vw →
      readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩
  | _, t, 0, hk, hwf =>
    readTerm2_quote hc t (core2_of_liftDepth_zero t (Nat.le_zero.mp hk)) hwf
  | _, .boolInput j, k+1, _, hj => by
    obtain ⟨i, hq, hin⟩ := hc.boolOut j hj
    show readN cfg (k+1) (cfg.bools j) = _
    rw [hq]
    show readInput cfg i = _
    unfold readInput
    exact alt_some_left (Option.bind_eq_some_iff.mpr ⟨j, hin, rfl⟩)
  | _, .bitsInput w j, k+1, _, hwf => by
    obtain ⟨h1, h2, h3⟩ := hwf
    obtain ⟨i, hq, hnb, hin⟩ := hc.bitsOut j w h1 h2 h3
    show readN cfg (k+1) (cfg.bits j) = _
    rw [hq]
    show readInput cfg i = _
    unfold readInput
    exact (alt_none_left (bind_none_of hnb _)).trans
      (Option.bind_eq_some_iff.mpr ⟨(w, j), hin, rfl⟩)
  | _, .boolLit b, k+1, _, _ => by
    cases b
    · exact rn3 (readNode2_app3.trans (alt_some_left (read3_boolLit_false hc.domOk)))
    · exact rn3 (readNode2_app3.trans (alt_some_left (read3_boolLit_true hc.domOk)))
  | _, .bitsLit w v, k+1, _, hwf =>
    rn3 (readNode2_app3.trans (alt_some_left (read3_bitsLit hc.domOk hwf)))
  | _, .bitsNum w v, k+1, _, hwf =>
    rn3 (readNode2_app3.trans ((alt_none_left (read3_num w v)).trans (readBitsNum_eval hc.domOk hwf)))
  | _, .binary op a b, k+1, hk, hwf => by
    obtain ⟨wa, wb⟩ := hwf
    simp only [liftDepth] at hk
    exact rn6 (readNode2_app6.trans (alt_some_left
      (read6_binary hc.domOk op (readN_quote hc a (k+1) (by omega) wa)
        (readN_quote hc b (k+1) (by omega) wb))))
  | _, .compare op a b, k+1, hk, hwf => by
    obtain ⟨wa, wb⟩ := hwf
    simp only [liftDepth] at hk
    have iha := readN_quote hc a (k+1) (by omega) wa
    have ihb := readN_quote hc b (k+1) (by omega) wb
    cases op
    · exact rn4 (readNode2_app4.trans (alt_some_left
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb)))
    · exact rn4 (readNode2_app4.trans (alt_some_left
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb)))
    · exact rn4 (readNode2_app4.trans (alt_some_left
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb)))
    · exact rn4 (readNode2_app4.trans (alt_some_left
        (readCompare_eval hc.domOk (fun e => by cases e) iha ihb)))
    · exact rn5 (readNode2_app5.trans (alt_some_left (read5_bitsEq hc.domOk iha ihb)))
  | _, .boolBinary kd a b, k+1, hk, hwf => by
    obtain ⟨wa, wb⟩ := hwf
    simp only [liftDepth] at hk
    exact rn6 (readNode2_app6.trans (alt_some_left
      (read6_boolBinary hc.domOk kd (readN_quote hc a (k+1) (by omega) wa)
        (readN_quote hc b (k+1) (by omega) wb))))
  | _, .boolNot a, k+1, hk, hwf =>
    rn3 (readNode2_app3.trans
      (alt_some_left (read3_boolNot hc.domOk (readN_quote hc a (k+1) hk hwf))))
  | _, .boolEq a b, k+1, hk, hwf => by
    obtain ⟨wa, wb⟩ := hwf
    simp only [liftDepth] at hk
    exact rn5 (readNode2_app5.trans (alt_some_left
      (read5_boolEq hc.domOk (readN_quote hc a (k+1) (by omega) wa)
        (readN_quote hc b (k+1) (by omega) wb))))
  | s, .mux c a b, k+1, hk, hwf => by
    obtain ⟨wc, wa, wb⟩ := hwf
    simp only [liftDepth] at hk
    have ihc := readN_quote hc c (k+1) (by omega) wc
    have iha := readN_quote hc a (k+1) (by omega) wa
    have ihb := readN_quote hc b (k+1) (by omega) wb
    cases s
    · exact rn5 (readNode2_app5.trans (alt_some_left (read5_muxBool hc.domOk ihc iha ihb)))
    · exact rn5 (readNode2_app5.trans (alt_some_left (read5_muxBits hc.domOk ihc iha ihb)))
  | _, .setw w' a, k+1, hk, hwf => by
    obtain ⟨wa, hpos⟩ := hwf
    exact rn5 (readNode2_app5.trans ((alt_none_left (read5_none ne_map_mux ne_map_beq)).trans
      (alt_some_left (readSetw_eval hc.domOk hpos (readN_quote hc a (k+1) hk wa)))))
  | _, .slice nm st len (w := w) a, k+1, hk, hwf => by
    obtain ⟨wa, hok⟩ := hwf
    exact rn5 (readNode2_app5.trans ((alt_none_left (read5_none ne_map_mux ne_map_beq)).trans
      ((alt_none_left (readSetw_none (sliceFn nm w st len) (fun _ _ => rfl))).trans
        (alt_some_left (readSlice_eval hc.domOk hok (readN_quote hc a (k+1) hk wa))))))
  | _, .concat a b, k+1, hk, hwf => by
    obtain ⟨wa, wb⟩ := hwf
    simp only [liftDepth] at hk
    exact rn6 (readNode2_app6.trans (alt_some_left
      (read6_concat hc.domOk (readN_quote hc a (k+1) (by omega) wa)
        (readN_quote hc b (k+1) (by omega) wb))))
  | _, .concatLitHi kk v b, k+1, hk, hwf => by
    obtain ⟨wb, hk0, hv⟩ := hwf
    exact rn6 (readNode2_app6.trans ((alt_none_left (read6_hi kk)).trans
      ((alt_none_left (readSliceF_head ne_append_fmap)).trans
        (alt_some_left (readConcatHi_eval hc.domOk hk0 hv (readN_quote hc b (k+1) hk wb))))))
  | _, .concatLitLo (m := m) a kk v, k+1, hk, hwf => by
    obtain ⟨wa, hk0, hv⟩ := hwf
    exact rn6 (readNode2_app6.trans ((alt_none_left (read6_lo cfg.dom m kk)).trans
      ((alt_none_left (readSliceF_head ne_append_fmap)).trans
        ((alt_none_left (readConcatHi_x0 (sigT cfg.dom m) rfl)).trans
          (readConcatLo_eval hc.domOk hk0 hv (readN_quote hc a (k+1) hk wa))))))
  | _, .zextMap nm kk (n := n) a, k+1, hk, hwf => by
    obtain ⟨wa, hpos⟩ := hwf
    exact rn5 (readNode2_app5.trans ((alt_none_left (read5_none ne_map_mux ne_map_beq)).trans
      ((alt_none_left (readSetw_none (zextFn nm kk n) (fun _ _ => rfl))).trans
        ((alt_none_left (readSlice_none (zextFn nm kk n) (fun _ _ => rfl))).trans
          (readZext_eval hc.domOk hpos (readN_quote hc a (k+1) hk wa))))))
  | _, .sliceF nm st len a, k+1, hk, hwf => by
    obtain ⟨wa, hok⟩ := hwf
    exact rn6 (readNode2_app6.trans ((alt_none_left read6_fmap).trans
      (alt_some_left (readSliceF_eval hc.domOk hok (readN_quote hc a (k+1) hk wa)))))
  | _, .appCompare op a b, k+1, hk, hwf => by
    obtain ⟨wa, wb⟩ := hwf
    simp only [liftDepth] at hk
    exact rnAp (readAp_appCompare_eval hc.domOk op (readN_quote hc a k (by omega) wa)
      (readN_quote hc b (k+1) (by omega) wb))
  | _, .appBool op a b, k+1, hk, hwf => by
    obtain ⟨wa, wb⟩ := hwf
    simp only [liftDepth] at hk
    exact rnAp (readAp_appBool_eval hc.domOk op (readN_quote hc a k (by omega) wa)
      (readN_quote hc b (k+1) (by omega) wb))
  | _, .appBool2 f a b, k+1, hk, hwf => by
    obtain ⟨wa, wb⟩ := hwf
    simp only [liftDepth] at hk
    exact rnAp (readAp_appBool2_eval hc.domOk f (readN_quote hc a k (by omega) wa)
      (readN_quote hc b (k+1) (by omega) wb))

/-- U1e: with the endpoint configuration, no condition on the binders. -/
theorem readN_expr_quote (dom : Lean.Expr) (ks : List MixedGateBinder) {s : SType} (t : Term s)
    (k : Nat) (hk : liftDepth t ≤ k)
    (hw : t.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0)) :
    readN (kindsCfg dom (isExpr dom) ks) k
      (quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) t) = some ⟨s, t⟩ :=
  readN_quote (kindsCfg_complete' dom (isExpr dom) (isExpr_self dom) ks) t k hk hw

/-- U1f: `quote` is injective on all 21 kinds. -/
theorem quote_injective {cfg : Cfg} (hc : Complete cfg) {s s' : SType} (t : Term s) (t' : Term s')
    (hw : t.WF cfg.kb cfg.kv cfg.vw) (hw' : t'.WF cfg.kb cfg.kv cfg.vw)
    (h : quote cfg.dom cfg.bools cfg.bits t = quote cfg.dom cfg.bools cfg.bits t') :
    (⟨s, t⟩ : AnyTerm) = ⟨s', t'⟩ := by
  have h1 := readN_quote hc t (max (liftDepth t) (liftDepth t')) (Nat.le_max_left _ _) hw
  have h2 := readN_quote hc t' (max (liftDepth t) (liftDepth t')) (Nat.le_max_right _ _) hw'
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-! ## U2 — level bound and monotonicity on quotations -/

theorem exprSize_app_left (f a : Lean.Expr) : exprSize f ≤ exprSize (.app f a) := by
  show exprSize f ≤ exprSize f + exprSize a + 1
  omega

theorem exprSize_app_right (f a : Lean.Expr) : exprSize a ≤ exprSize (.app f a) := by
  show exprSize a ≤ exprSize f + exprSize a + 1
  omega

theorem liftDepth_le_exprSize {cfg : Cfg} {s : SType} (t : Term s) :
    liftDepth t ≤ exprSize (quote cfg.dom cfg.bools cfg.bits t) := by
  induction t with
  | boolInput j => exact Nat.zero_le _
  | bitsInput w j => exact Nat.zero_le _
  | boolLit b => exact Nat.zero_le _
  | bitsLit w v => exact Nat.zero_le _
  | bitsNum w v => exact Nat.zero_le _
  | binary op a b iha ihb =>
    simp only [liftDepth, quote, binE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | compare op a b iha ihb =>
    cases op <;>
    simp only [liftDepth, quote, compareE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at * <;>
    omega
  | boolBinary op a b iha ihb =>
    simp only [liftDepth, quote, boolBinE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | boolNot a iha =>
    simp only [liftDepth, quote, boolNotE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | boolEq a b iha ihb =>
    simp only [liftDepth, quote, boolEqE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | mux c a b ihc iha ihb =>
    simp only [liftDepth, quote, muxE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | setw w' a iha =>
    simp only [liftDepth, quote, setwE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | slice nm st len a iha =>
    simp only [liftDepth, quote, sliceE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | concat a b iha ihb =>
    simp only [liftDepth, quote, concatE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | concatLitHi k v b ihb =>
    simp only [liftDepth, quote, concatLitHiE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | concatLitLo a k v iha =>
    simp only [liftDepth, quote, concatLitLoE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | zextMap nm k a iha =>
    simp only [liftDepth, quote, zextMapE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | sliceF nm st len a iha =>
    simp only [liftDepth, quote, sliceFE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4, Lean.mkApp3,
      Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | appCompare op a b iha ihb =>
    simp only [liftDepth, quote, appCompareE, appE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4,
      Lean.mkApp3, Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | appBool op a b iha ihb =>
    simp only [liftDepth, quote, appBoolE, appE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4,
      Lean.mkApp3, Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega
  | appBool2 f a b iha ihb =>
    simp only [liftDepth, quote, appBool2E, appE, Lean.mkApp6, Lean.mkApp5, Lean.mkApp4,
      Lean.mkApp3, Lean.mkApp2, Lean.mkApp, exprSize] at *
    omega

theorem readTot_quote {cfg : Cfg} (hc : Complete cfg) {s : SType} (t : Term s)
    (hw : t.WF cfg.kb cfg.kv cfg.vw) :
    readTot cfg (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩ :=
  readN_quote hc t _ (liftDepth_le_exprSize t) hw

/-- U2a: monotonicity ON QUOTATIONS (a corollary of U1 + soundness). -/
theorem readN_mono_on_quotes {cfg : Cfg} (hs : cfg.Sound) (hc : Complete cfg) {s : SType}
    (t : Term s) (hw : t.WF cfg.kb cfg.kv cfg.vw) {k : Nat} (r : AnyTerm)
    (hr : readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some r)
    {k' : Nat} (hk' : liftDepth t ≤ k') :
    readN cfg k' (quote cfg.dom cfg.bools cfg.bits t) = some r := by
  obtain ⟨hq, hwr⟩ := readN_sound cfg hs k _ r hr
  have hinj := quote_injective hc t r.2 hw hwr hq.symm
  have hr' : r = ⟨s, t⟩ := hinj.symm
  rw [hr']
  exact readN_quote hc t k' hk' hw

/-! ## U3 — `readN` forms of the machine body lemmas -/

theorem machine_body_of_readN (d : MachineData) (isDom : Lean.Expr → Bool)
    (hdom : ∀ x, isDom x = true → x = d.dom) (k : Nat)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hread : readN (kindsCfg d.dom isDom (kindsOf d)) k d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)) :
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed := by
  have h := (readN_sound (kindsCfg d.dom isDom (kindsOf d))
    (kindsCfg_sound d.dom isDom hdom (kindsOf d)) k d.shape.body _ hread).1
  change quote d.dom (fun j => inputExpr (kindsOf d).length ((posB 0 (kindsOf d)).getD j 0))
    (fun j => inputExpr (kindsOf d).length ((posV 0 (kindsOf d)).getD j 0)) d.packed = d.shape.body at h
  rw [kindsOf_length, ← hb, ← hv] at h
  exact h.symm

theorem machine_wf_of_readN (d : MachineData) (isDom : Lean.Expr → Bool)
    (hdom : ∀ x, isDom x = true → x = d.dom) (k : Nat)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hread : readN (kindsCfg d.dom isDom (kindsOf d)) k d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)) :
    d.packed.WF d.kb d.kv d.vw := by
  have h := (readN_sound (kindsCfg d.dom isDom (kindsOf d))
    (kindsCfg_sound d.dom isDom hdom (kindsOf d)) k d.shape.body _ hread).2
  change d.packed.WF (posB 0 (kindsOf d)).length (posV 0 (kindsOf d)).length
    (fun j => (widV (kindsOf d)).getD j 0) at h
  rw [← hb, ← hv, ← hw] at h
  exact h

/-! ## U4 — a body that IS the quotation is read -/

theorem kindsCfg_quote_args (d : MachineData) (isDom : Lean.Expr → Bool)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) :
    (kindsCfg d.dom isDom (kindsOf d)).bools = (fun j => inputExpr d.shape.binders.length (d.bpos j)) ∧
    (kindsCfg d.dom isDom (kindsOf d)).bits  = (fun j => inputExpr d.shape.binders.length (d.vpos j)) := by
  constructor
  · funext j
    show inputExpr (kindsOf d).length ((posB 0 (kindsOf d)).getD j 0) =
      inputExpr d.shape.binders.length (d.bposL.getD j 0)
    rw [kindsOf_length, hb]
  · funext j
    show inputExpr (kindsOf d).length ((posV 0 (kindsOf d)).getD j 0) =
      inputExpr d.shape.binders.length (d.vposL.getD j 0)
    rw [kindsOf_length, hv]

theorem packed_wf_cfg (d : MachineData) (isDom : Lean.Expr → Bool)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hwf : d.packed.WF d.kb d.kv d.vw) :
    d.packed.WF (kindsCfg d.dom isDom (kindsOf d)).kb (kindsCfg d.dom isDom (kindsOf d)).kv
      (kindsCfg d.dom isDom (kindsOf d)).vw := by
  have h : d.packed.WF d.bposL.length d.vposL.length (fun j => d.vwL.getD j 0) := hwf
  rw [hb, hv, hw] at h
  exact h

theorem readTot_of_quote_body (d : MachineData) (isDom : Lean.Expr → Bool)
    (hdom : isDom d.dom = true)
    (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hwf : d.packed.WF d.kb d.kv d.vw) :
    readTot (kindsCfg d.dom isDom (kindsOf d)) d.shape.body = some (⟨_, d.packed⟩ : AnyTerm) := by
  have hc := kindsCfg_complete' d.dom isDom hdom (kindsOf d)
  obtain ⟨h1, h2⟩ := kindsCfg_quote_args d isDom hb hv
  have hq' : d.shape.body = quote (kindsCfg d.dom isDom (kindsOf d)).dom
      (kindsCfg d.dom isDom (kindsOf d)).bools (kindsCfg d.dom isDom (kindsOf d)).bits d.packed := by
    rw [h1, h2]
    exact hq
  rw [hq']
  exact readTot_quote hc d.packed (packed_wf_cfg d isDom hb hv hw hwf)

/-! ## U5 — type only (NOT a supply)

`RootFacts` is stated for the audit (type check against an independent statement). Defining it is not a producer:
nothing here, in `RunReadsAt`, or in the compiler path supplies it (freeze rev2 §2.5). -/

structure RootFacts (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder))
    (entryBody₀ entryBody : Lean.Expr) : Prop where
  pack  : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)
  float : entryBody = Sparkle.Compiler.MachRawSurface.rootFloat entryBody₀

end Tools.ShippingGen5ReadKinds
