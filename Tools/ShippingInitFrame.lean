import Tools.ShippingStartAtLoad
-- BUILT (unit RT2): rt2a (lib) exit 0. No sorry/axiom/native_decide.

/-! # Unit RT2: interleaved module load vs `loadW` (ledger L9d)

**Verdict (read this first).** `loadW wS` (L9c) ran the three `mkRef`s and the `set` back to back. This file
states the real load as an INTERLEAVED run and PROVES, by a frame argument, that the conclusion of
`startAtLoad_of_corr` carries over to it. It is a replacement of the isolation premise by NAMED premises, NOT a
discharge of the initialisation correspondence; runtime fit NOT PROVEN; logical inconsistency NOT PROVEN.

**(a) What the toolchain does (read from `Lean/Compiler/InitAttr.lean`, v4.32.1).** `initialize x : T ← e` elaborates
to an `[init]` declaration; `runInitAttrForMod` first tries the natively compiled module initialiser
(`runModInit`, the generated C `initialize_<Module>`), and only if that is absent interprets the module's
`regularInitAttr` entries in the order of `getModuleEntries`, each at most once per module
(`interpretedModInits`). The generated C initialiser's body order (declaration order) is NOT in the locally
available sources (`EmitC` is not shipped), and for the interpreted path the order of `getModuleEntries` (an
exported `ParametricAttribute` array) is not related here to the source order. So `InitOrder` below is a PREMISE
about what the load does, not something derived from those sources.

* `InitOrder Other wS w` — the load from `wS` to `w` is: `Other`-steps, `sparkleSynthDepth`'s `mkRef`,
  `Other`-steps, `sparkleChildCache`'s `mkRef`, `Other`-steps, `sparkleChildSynth`'s `mkRef`, `Other`-steps, the
  `set (some synthesizeChild)`, `Other`-steps. (Source order in `Elab.lean`: :963, :1032, :1040, :8934.) `Other` is
  an arbitrary relation: the class of all remaining initialiser steps (same module and later modules).
* `OthersFrameRefs R Other` — an `Other` step keeps every model relatedness: `Other w w' → R w h → R w' h`.
  Source evidence (a syntactic check, test `InitFrameTest`): no `[init]` body other than the `set` mentions the
  three ref constants directly; this is NOT a proof (indirect writes via called functions are not excluded) and
  `R` is a parameter.
* `InitHeapRelXfer R Other wS h0` — the L9c `InitHeapRel` at the isolated `mkRefsW wS` transfers to the
  `mkRef`-interleaved world. This is the part the frame argument does NOT cover (the model has no `mkRef`/
  allocation): it is a PREMISE.

**(b) PROVED** (`startAtLoad_of_initOrder`, all conditional on the premises above plus the L9c ones
`InitHeapRel GetSpec SetSynthSpec QuietSpec Q h0.reg`): `StartAtLoad quiet w` for the END world `w` of the
interleaved run. The proved content is the induction `frame_chain` (`Other`-chains preserve `R`) plus the L9c
reasoning. `initOrder_false_iff` shows the specialisation `Other := ⊥`: the run is exactly `loadW wS`.

NOT claimed: that `InitOrder` holds for the real load; that `OthersFrameRefs`/`InitHeapRelXfer` hold; that
the premises are jointly satisfiable with `O`; any discharge of L9c's premises. -/

namespace Tools.ShippingInitFrame
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingStartWorldA Tools.ShippingStartWorldA2 Tools.ShippingStartAtLoad

variable {Ob Pr Er : Type}

/-- The three `mkRef` actions of `Elab.lean`, as world transformers (same match shape as `mkRefsW`). -/
def mkDepthW (w : Void IO.RealWorld) : Void IO.RealWorld :=
  match (IO.mkRef (0 : Nat) : BaseIO (IO.Ref Nat)) w with | .mk _ w' => w'

def mkCacheW (w : Void IO.RealWorld) : Void IO.RealWorld :=
  match (IO.mkRef ({} : Std.HashMap Name Res) : BaseIO (IO.Ref (Std.HashMap Name Res))) w with | .mk _ w' => w'

def mkSynthW (w : Void IO.RealWorld) : Void IO.RealWorld :=
  match (IO.mkRef (none : Option (Name → MetaM Res)) : BaseIO (IO.Ref (Option (Name → MetaM Res)))) w with
  | .mk _ w' => w'

/-- The `initialize sparkleChildSynth.set (some synthesizeChild)` action as a world transformer. -/
def setSynthW (w : Void IO.RealWorld) : Void IO.RealWorld :=
  setW sparkleChildSynth (some synthesizeChild) w

theorem mkRefsW_eq (wS : Void IO.RealWorld) : mkRefsW wS = mkSynthW (mkCacheW (mkDepthW wS)) := rfl
theorem loadW_eq (wS : Void IO.RealWorld) : loadW wS = setSynthW (mkRefsW wS) := rfl

/-- **PREMISE (load order).** The load from `wS` to `w` is the interleaved run described in the header;
`Other` is the relation of all remaining initialiser steps. -/
def InitOrder (Other : Void IO.RealWorld → Void IO.RealWorld → Prop) (wS w : Void IO.RealWorld) : Prop :=
  ∃ a0 a2 a4 a6, Chain Other wS a0 ∧ Chain Other (mkDepthW a0) a2 ∧ Chain Other (mkCacheW a2) a4 ∧
    Chain Other (mkSynthW a4) a6 ∧ Chain Other (setSynthW a6) w

/-- **PREMISE (frame).** Other initialisers do not change what the model relation sees. -/
def OthersFrameRefs (R : Corr Ob Pr Er) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop) : Prop :=
  ∀ w w' h, Other w w' → R w h → R w' h

/-- **PREMISE (transfer through the interleaved `mkRef`s).** -/
def InitHeapRelXfer (R : Corr Ob Pr Er) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (wS : Void IO.RealWorld) (h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)) : Prop :=
  ∀ a0 a2 a4, Chain Other wS a0 → Chain Other (mkDepthW a0) a2 → Chain Other (mkCacheW a2) a4 →
    InitHeapRel R (mkRefsW wS) h0 → InitHeapRel R (mkSynthW a4) h0

/-- PROVED: `Other`-chains preserve relatedness under the frame premise. -/
theorem frame_chain {R : Corr Ob Pr Er} {Other : Void IO.RealWorld → Void IO.RealWorld → Prop}
    (hf : OthersFrameRefs R Other) {a b : Void IO.RealWorld} (c : Chain Other a b)
    {h : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)} (hr : R a h) : R b h := by
  induction c with
  | refl => exact hr
  | tail _ hs ih => exact hf _ _ _ hs ih

/-- **PROVED relative to the premises:** `StartAtLoad` for the end world of the interleaved load. The
premises `hxfer hf hmk hget hset hq hQ0` are named; none is derived here. -/
theorem startAtLoad_of_initOrder (R : Corr Ob Pr Er) (Q : Pr → Prop) (quiet : Void IO.RealWorld → Prop)
    (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    {wS a0 a2 a4 a6 w : Void IO.RealWorld} {h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)}
    (c0 : Chain Other wS a0) (c1 : Chain Other (mkDepthW a0) a2) (c2 : Chain Other (mkCacheW a2) a4)
    (c3 : Chain Other (mkSynthW a4) a6) (c4 : Chain Other (setSynthW a6) w)
    (hxfer : InitHeapRelXfer R Other wS h0) (hf : OthersFrameRefs R Other)
    (hmk : InitHeapRel R (mkRefsW wS) h0) (hget : GetSpec R) (hset : SetSynthSpec R)
    (hq : QuietSpec R Q quiet) (hQ0 : Q h0.reg) :
    StartAtLoad quiet w := by
  have h3 : InitHeapRel R (mkSynthW a4) h0 := hxfer a0 a2 a4 c0 c1 c2 hmk
  have h4 : R a6 h0 := frame_chain hf c3 h3.1
  have h5 := hset a6 h0 (some synthesizeChild) h4
  have h6 := frame_chain hf c4 h5
  obtain ⟨-, hs, hd⟩ := hget _ _ h6
  obtain ⟨-, -, -, hd0⟩ := h3
  refine ⟨hq _ _ h6 ?_, ?_, ?_⟩
  · rw [Tools.ShippingHeapModel.set_reg]; exact hQ0
  · rw [hs]; exact Tools.ShippingHeapModel.get_set_same (σ := sig Ob Pr Er) .synth (some synthesizeChild) h0
  · rw [hd]; exact hd0

/-- Chains of the empty relation are trivial. -/
theorem chain_false {a b : Void IO.RealWorld} (c : Chain (fun _ _ => False) a b) : a = b := by
  induction c with
  | refl => rfl
  | tail _ hs => exact hs.elim

/-- Specialisation `Other := ⊥`: the interleaved run is exactly the isolated `loadW wS`. -/
theorem initOrder_false_iff (wS w : Void IO.RealWorld) :
    InitOrder (fun _ _ => False) wS w ↔ w = loadW wS := by
  constructor
  · rintro ⟨a0, a2, a4, a6, c0, c1, c2, c3, c4⟩
    obtain rfl := chain_false c0
    obtain rfl := chain_false c1
    obtain rfl := chain_false c2
    obtain rfl := chain_false c3
    obtain rfl := chain_false c4
    rfl
  · rintro rfl
    exact ⟨wS, mkDepthW wS, mkCacheW (mkDepthW wS), mkSynthW (mkCacheW (mkDepthW wS)),
      .refl, .refl, .refl, .refl, .refl⟩

end Tools.ShippingInitFrame
