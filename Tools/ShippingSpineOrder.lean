import Tools.ShippingUnifiedSpine
import Tools.ShippingMachineEntry

/-! # Where the readers of a `let` port are: the packed spine, link by link

The let-closed body puts the alias of `let` port `i` right after the driver of
its operand wire. For that to be in dependency order every statement that
READS the port must come later. This file proves the positional fact behind
it, for the translation of a packed body `packLets fs core`:

for field `i` there is a point of the emission — the builder's body when the
field's translation returned, a SUFFIX of every later body (`pre`) — such
that the operand wire is driven in `pre` (or is an input), and every statement
of `pre` reads, among the protected names, only those in `Vk i`: the wires
bound to the variables the fields before `i` may use (`LP`).

It is an induction over the fields along the real concat arm — the result
wire first, the field, the rest, the assign — through the validated cache
(a hit: `pre` is the whole body at the hit; the links are the record
invariant's). The fields' own translations are `fuel_spine` at the variable
set of their position. -/
namespace Tools.ShippingSpineOrder
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Reorder
open Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTranslationOrder
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingScalarSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires binary_returns core_binary_returns)
open Tools.ShippingMixedRecursion (emit_bool_frame compare_step boolBin_step boolEq_step
  boolNot_step translateBoolUncachedWith_boolBin translateBoolBinary_returns)
open Tools.ShippingMixedInvariant (translateStep_fvar_returns)
open Tools.ShippingVectorMuxRecursion (emit_vector_frame vector_step vectorMuxUncached_muxE emit_vector_order)
open Tools.ShippingMixedOrderSoundness (emit_bool_order)
open Tools.ShippingUnifiedProtection
open Tools.ShippingUnifiedSpine
open Tools.ShippingMachineEntry (packLets)

variable {ctx : CompilerState} {inputs : FVarId → Option Value} {P : String → Prop}
  {dom : Lean.Expr} {bi vi : Nat → FVarId}

local notation "Q(" e ")" =>
  quote dom (fun j => Lean.Expr.fvar (bi j)) (fun j => Lean.Expr.fvar (vi j)) e

/-- The variables position `k` may use: the Bool variables in `ubk k`, the
BitVec variables in `uvk k`. -/
def Bk (bi vi : Nat → FVarId) (ubk uvk : Nat → Nat → Prop) (k : Nat) (id : FVarId) : Prop :=
  (∃ j, ubk k j ∧ id = bi j) ∨ (∃ j, uvk k j ∧ id = vi j)

/-- Field `i + j` is well-formed and uses only the variables of its position. -/
def FieldsOK (ubk uvk : Nat → Nat → Prop) (kb kv : Nat) (vw : Nat → Nat) :
    Nat → List (Σ w : Nat, Term (.bits w)) → Prop
  | _, [] => True
  | i, f :: rest => f.2.WF kb kv vw ∧ Uses (ubk i) (uvk i) f.2 ∧ FieldsOK ubk uvk kb kv vw (i + 1) rest

/-- From `w`, `n` links starting at position `i`: link `{x, y}` of `w`, with a
suffix `pre` of the builder's body in which `x` is driven (or `x` is an input)
and whose statements read only `Vk i` among the protected names. -/
def LP (P : String → Prop) (Vk : Nat → String → Prop) (body : List Stmt) :
    Nat → Nat → String → Prop
  | _, 0, _ => True
  | i, n + 1, w => ∃ x y pre, link w x y ∈ body ∧ pre <:+ body ∧ Drv P pre x ∧
      (∀ l r, Stmt.assign l r ∈ pre → ReadsOK P (Vk i) r) ∧ LP P Vk body (i + 1) n y

theorem LP.mono {Vk : Nat → String → Prop} {body : List Stmt} (more : List Stmt) :
    ∀ {i n : Nat} {w : String}, LP P Vk body i n w → LP P Vk (more ++ body) i n w
  | _, 0, _, _ => trivial
  | _, _ + 1, _, ⟨x, y, pre, hm, hs, hd, hr, hl⟩ =>
    ⟨x, y, pre, List.mem_append_right _ hm, hs.trans (List.suffix_append _ _), hd, hr, hl.mono more⟩

theorem ReadsOK.mono {V V' : String → Prop} (h : ∀ x, V x → V' x) {rhs : Sparkle.IR.AST.Expr}
    (hr : ReadsOK P V rhs) : ReadsOK P V' rhs := fun x hx hp => h x (hr x hx hp)

/-- The invariant at a larger variable set: the new variables' wires are in
the new `V`. -/
theorem St.weaken {B B' : FVarId → Prop} {V V' : String → Prop} {s : CircuitState}
    (h : St ctx inputs B P V s) (hV : ∀ x, V x → V' x)
    (hB : ∀ id z, B' id → visible ctx s.sourceBindings id = some z → V' z) :
    St ctx inputs B' P V' s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hB, fun l r hm => ReadsOK.mono hV (h.2.2.2.2.2 l r hm)⟩

section Run
variable {ubk uvk : Nat → Nat → Prop} {Vk : Nat → String → Prop} {kb kv : Nat} {vw : Nat → Nat}
  {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}

/-- A cache hit on a packed term: the links are the record invariant's; the
point of emission is the whole body now. -/
theorem lp_of_spineQ {wires : List Port} {body : List Stmt}
    (hmonoV : ∀ k x, Vk k x → Vk (k + 1) x) :
    ∀ (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)) (i : Nat)
      (w : String), FieldsOK ubk uvk kb kv vw i fs → core.WF kb kv vw →
      (∀ l r, Stmt.assign l r ∈ body → ReadsOK P (Vk i) r) →
      SpineQ P wires body fs.length Q((packLets fs core).2) w → LP P Vk body i fs.length w
  | [], _, _, _, _, _, _, _, _ => trivial
  | f :: rest, c, core, i, w, hf, hc, hread, hs => by
    obtain ⟨hwf, -, hrest⟩ := hf
    have hrestWF : (packLets rest core).2.WF kb kv vw := by
      clear hs hread
      induction rest generalizing i with
      | nil => exact hc
      | cons g gs ih => exact ⟨hrest.1, ih (i + 1) hrest.2.2⟩
    have hcc : canonicalConcat? Q((packLets (f :: rest) core).2) =
        some (f.1, (packLets rest core).1, Q(f.2), Q((packLets rest core).2)) :=
      canonicalConcat?_concatE dom _ _ (f.2.wf_pos hwf) ((packLets rest core).2.wf_pos hrestWF)
    obtain ⟨x, y, hm, -, hd, hr⟩ := hs _ _ _ _ hcc
    exact ⟨x, y, body, hm, List.suffix_refl _, hd, hread,
      lp_of_spineQ hmonoV rest core (i + 1) y hrest hc
        (fun l r hl => ReadsOK.mono (hmonoV i) (hread l r hl)) hr⟩

/-- **The packed spine, link by link.** Translating `packLets fs core` from a
state satisfying the invariant at position `i` leaves, for each field, the
point of emission of `LP`: the body when the field returned, in which its
wire is driven and which reads only what the fields so far may read. -/
theorem spine_links
    (hb : ∀ j, j < kb → inputs (bi j) = some (.bool (bools j)))
    (hv : ∀ j, j < kv → inputs (vi j) = some (.bits (vw j) (bits j (vw j))))
    (hmonoV : ∀ k x, Vk k x → Vk (k + 1) x) (σ : _)
    (hbind : ∀ k id z, Bk bi vi ubk uvk k id → visible ctx σ id = some z → Vk k z) :
    ∀ (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)) (i fuel : Nat)
      (s t : CircuitState) (w hint : String) (named : Bool),
      FieldsOK ubk uvk kb kv vw i fs → core.WF kb kv vw →
      Uses (ubk (i + fs.length)) (uvk (i + fs.length)) core →
      s.sourceBindings = σ →
      St ctx inputs (Bk bi vi ubk uvk i) P (Vk i) s →
      Returns (translateFuelFix translateStep fuel Q((packLets fs core).2) hint false named)
        ctx s w t →
      LP P Vk t.module.body i fs.length w ∧ Ext s t
  | [], _, core, i, fuel, s, t, w, hint, named, _, hc, hu, _, hq, hr => by
    obtain ⟨-, hx, -⟩ := fuel_spine (ctx := ctx) (P := P) (V := Vk i) (dom := dom) fuel hb hv
      (fun j h => Or.inl ⟨j, h, rfl⟩) (fun j h => Or.inr ⟨j, h, rfl⟩) core hc
      (by simpa using hu) hint named s t w hr hq
    exact ⟨trivial, hx⟩
  | f :: rest, c, core, i, 0, s, t, w, hint, named, _, _, _, _, _, hr => (Returns.throw hr).elim
  | f :: rest, c, core, i, fuel + 1, s, t, w, hint, named, hf, hc, hu, hσ, hq, hr => by
    obtain ⟨hwf, huf, hrest⟩ := hf
    have hrestWF : ∀ (j : Nat) (gs : List (Σ w : Nat, Term (.bits w))),
        FieldsOK ubk uvk kb kv vw j gs → (packLets gs core).2.WF kb kv vw := by
      intro j gs
      induction gs generalizing j with
      | nil => exact fun _ => hc
      | cons g gs ih => exact fun h => ⟨h.1, ih (j + 1) h.2.2⟩
    have pos1 := f.2.wf_pos hwf
    have pos2 := (packLets rest core).2.wf_pos (hrestWF _ rest hrest)
    change Returns (translateStepWith translateFallback (translateFuelFix translateStep fuel)
      (concatE dom f.1 (packLets rest core).1 Q(f.2) Q((packLets rest core).2)) hint false named)
      ctx s w t at hr
    rw [concat_step _ _ _ _ _ _ _ _ _ pos1 pos2] at hr
    rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
    · obtain ⟨hs, hrec⟩ := cacheLookupValidated_returns hit
      subst hs
      refine ⟨lp_of_spineQ (wires := t.module.wires) (dom := dom) (bi := bi) (vi := vi) hmonoV
        (f :: rest) core i w
        ⟨hwf, huf, hrest⟩ hc hq.2.2.2.2.2 ?_, Ext.refl _⟩
      exact (hq.1 w _ (hrec w rfl)).1 _
    · rw [concatUncached_concatE] at miss
      unfold translateConcatWith translateConcatActs at miss
      obtain ⟨res, sA, hmk, rest1⟩ := Returns.bind miss
      obtain ⟨wa, sB, ha, rest2⟩ := Returns.bind rest1
      obtain ⟨wb, sC, hb', rest3⟩ := Returns.bind rest2
      obtain ⟨u, sD, hem, ret⟩ := Returns.bind rest3
      obtain ⟨hwv, ht⟩ := Returns.pure ret
      subst ht
      subst hwv
      obtain ⟨qA, xA, -, -⟩ := makeWire_facts hmk hq
      obtain ⟨qB, xAB, -, -, -, hdrv⟩ := fuel_spine (ctx := ctx) (P := P) (V := Vk i) (dom := dom)
        fuel hb hv (fun j h => Or.inl ⟨j, h, rfl⟩) (fun j h => Or.inr ⟨j, h, rfl⟩) f.2 hwf huf
        "concat_hi" false sA sB wa ha qA
      have hσB : sB.sourceBindings = σ := by rw [xAB.2.1, xA.2.1, hσ]
      have qB' : St ctx inputs (Bk bi vi ubk uvk (i + 1)) P (Vk (i + 1)) sB :=
        St.weaken qB (hmonoV i) (fun id z hB hz => hbind (i + 1) id z hB (hσB ▸ hz))
      obtain ⟨lp, xBC⟩ := spine_links hb hv hmonoV σ hbind rest core (i + 1) fuel sB sC wb
        "concat_lo" false hrest hc
        (by rw [show i + 1 + rest.length = i + (rest.length + 1) by omega]; exact hu) hσB qB' hb'
      have hD := emitAssign_returns hem
      subst hD
      have xCD := emitAssign_ext w (.concat [.ref wa, .ref wb]) sC
      have ht := recordTranslation_returns record
      subst ht
      have hbody : (CircuitM.emitAssign w (.concat [.ref wa, .ref wb]) sC).2.module.body =
          [.assign w (.concat [.ref wa, .ref wb])] ++ sC.module.body := by
        rw [emitAssign_body_cons]; rfl
      refine ⟨⟨wa, wb, sB.module.body, ?_, ?_, hdrv, qB.2.2.2.2.2, ?_⟩,
        (xA.trans (xAB.trans (xBC.trans xCD))).trans ⟨Kept.refl _, rfl, fun _ h => h⟩⟩
      · show link w wa wb ∈ (CircuitM.emitAssign w (.concat [.ref wa, .ref wb]) sC).2.module.body
        rw [emitAssign_body_cons]; exact List.mem_cons_self ..
      · show sB.module.body <:+ (CircuitM.emitAssign w (.concat [.ref wa, .ref wb]) sC).2.module.body
        obtain ⟨more, hm⟩ := xBC.1.1
        rw [hbody, hm, ← List.append_assoc]
        exact List.suffix_append _ _
      · show LP P Vk (CircuitM.emitAssign w (.concat [.ref wa, .ref wb]) sC).2.module.body _ _ _
        rw [hbody]
        exact lp.mono _

end Run

end Tools.ShippingSpineOrder
