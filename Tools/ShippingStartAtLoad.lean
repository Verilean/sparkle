import Tools.ShippingStartWorldA2
import Tools.ShippingHeapModel
-- BUILT (unit RT1, par/u-rt1): rt1a exit 1 (▸ misuse; BodyStepC namespace), rt1b exit 0 (pre-review); post-review rt1d exit 1 (ST.Out ctor, rw), rt1e exit 0. No sorry/axiom/native_decide.

/-! # Unit RT1: `StartAtLoad` from per-primitive correspondence statements (ledger L9c)

**Verdict (read this first).** `StartAtLoad O.quiet w0` is NOT discharged. It is REDUCED to explicitly
named correspondence PREMISES between the opaque runtime operations and the pure heap model
(`Tools/ShippingHeapModel.lean`), one per primitive, plus one quiet-transfer premise and one
model-side premise. Those premises are exactly the "runtime fit" for the two `initialize`d refs;
they are PREMISES, not proved, and not derived from `O` in this change (non-implication is NOT proved):

* `MkRefTrace wS` — `IO.mkRef` (`@[extern] opaque`), the concrete execution: from the world `wS` the three
  `IO.mkRef` initializers run IN THE SOURCE ORDER (depth `0`, cache `{}`, synth `none`), each returns a ref,
  and the returned ref IS the ref the `initialize` registered (`sparkleSynthDepth`, `sparkleChildCache`,
  `sparkleChildSynth`); the resulting world is `mkRefsW wS`. This is an OPEN Prop (identity of a returned
  ref with a registered constant is the Lean init machinery, outside the logic); NOT proved.
* `InitHeapRel R w h0` — NOT a per-primitive statement: an initial-heap relation premise (`R w h0` plus the
  initial cell values). It is applied to `mkRefsW wS`, the world of the trace, so it cannot refer to another world.
* `GetSpec R` — `ST.Ref.get` (`@[extern] opaque`): the read of each tracked ref in a related world is the
  model cell. not derived from `O` in this change: `O`'s fields (`frame`, `cacheSet`, `depthSet`, …) are about `cv/sv/dv` BEFORE vs AFTER
  an action, never relate a read to a model; `readOf` is *defined* as the value of `ST.Ref.get`.
* `SetSynthSpec R` — `ST.Ref.set` on `sparkleChildSynth`: a write corresponds to `hset .synth`. PARTLY in `O`:
  `O.cacheSet` / `O.depthSet` (under `AdmCtx` + `quiet`, and for `MetaM`, not for the `IO` of `initialize`)
  give `cv w' = v ∧ sv w' = sv w ∧ dv w' = dv w` resp. the depth analogue; there is NO field for a write of
  `sparkleChildSynth` (its only write is the `initialize`, outside `MetaM`) and none relates `R`.
  So the synth write is entirely new.
* `QuietSpec R Q quiet` — related worlds with a `Q`-registry are `quiet`. `quiet` is an arbitrary predicate of
  `O`; this is NOT implied by `O` (and `O` is not shown to have any quiet world: `QuietWitness` stays OPEN,
  and this premise would give a witness only together with the other premises).
* `Q h0.reg` — the model's initial registry is `Q`. (Model side; says nothing about the real printer registry.)

What this file PROVES (`startAtLoad_of_corr`): from those premises, `StartAtLoad O.quiet w1` for `w1` the world
after the three mkRefs and the `initialize`'s `sparkleChildSynth.set (some synthesizeChild)` (`loadW`; `_htrace`, the identity/order premise, is carried in the statement and not used by the proof). The model reasoning
(`get_set_same`, `get_set_other`, `set_reg`) is the only proved content. Corollary `startContents_session_rt`:
L9b's `startContents_session` with `StartAtLoad` replaced. Old theorems unchanged.

NOT claimed: runtime fit; that `R` exists; that the premises are jointly satisfiable with `O` (logical
inconsistency NOT PROVEN, no proof either way); that the `IO.mkRef` of the Lean runtime allocates fresh refs
distinct from the model's tracked ones (that is inside `MkRefTrace`/`SetSynthSpec` being about related worlds);
`OtherCodeKeeps` and `O.quiet` (both stay listed premises, nothing here supplies them implicitly); that initializers of OTHER modules between the mkRefs and the set do not write the refs
(`h0` is arbitrary, but `InitHeapRel` asserts the contents AT `mkRefsW wS` — the set directly follows). -/

namespace Tools.ShippingStartAtLoad
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingStartWorldA Tools.ShippingStartWorldA2
open Tools.ShippingChildInvA Tools.ShippingChildDepthC

/-- The model signature of the compiler's tracked refs: the cache's, the synth ref's contents; the other
cells, registry, exception types stay generic. -/
def sig (Ob Pr Er : Type) : Tools.ShippingHeapModel.Sig :=
  ⟨Std.HashMap Name Res, Option (Name → MetaM Res), Ob, Pr, Er⟩

/-- The abstraction relation between a runtime world and a model heap (a parameter, not constructed). -/
abbrev Corr (Ob Pr Er : Type) := Void IO.RealWorld → Tools.ShippingHeapModel.Heap (sig Ob Pr Er) → Prop

/-- The world after `r.set v` (the `initialize` action), as `readOf` reads: the `ST` run's final world. -/
def setW {σ : Type} (r : IO.Ref σ) (v : σ) (w : Void IO.RealWorld) : Void IO.RealWorld :=
  match (ST.Ref.set r v : ST IO.RealWorld Unit) w with
  | .mk _ w' => w'

variable {Ob Pr Er : Type}

/-- The world after the three `IO.mkRef` initializers of `Elab.lean` in source order
(`sparkleSynthDepth` :963, `sparkleChildCache` :1032, `sparkleChildSynth` :1040) run from `wS`. -/
def mkRefsW (wS : Void IO.RealWorld) : Void IO.RealWorld :=
  match (IO.mkRef (0 : Nat) : BaseIO (IO.Ref Nat)) wS with
  | .mk _ w1 =>
    match (IO.mkRef ({} : Std.HashMap Name Res) : BaseIO (IO.Ref (Std.HashMap Name Res))) w1 with
    | .mk _ w2 =>
      match (IO.mkRef (none : Option (Name → MetaM Res)) : BaseIO (IO.Ref (Option (Name → MetaM Res)))) w2 with
      | .mk _ w3 => w3

/-- **OPEN (not proved; carried as a premise): `IO.mkRef` trace.** The three refs returned by the `mkRef`
runs, in that order, are the registered `sparkleSynthDepth`, `sparkleChildCache`, `sparkleChildSynth`.
(The world returned is `mkRefsW wS`.) -/
def MkRefTrace (wS : Void IO.RealWorld) : Prop :=
  match (IO.mkRef (0 : Nat) : BaseIO (IO.Ref Nat)) wS with
  | .mk r1 w1 =>
    match (IO.mkRef ({} : Std.HashMap Name Res) : BaseIO (IO.Ref (Std.HashMap Name Res))) w1 with
    | .mk r2 w2 =>
      match (IO.mkRef (none : Option (Name → MetaM Res)) : BaseIO (IO.Ref (Option (Name → MetaM Res)))) w2 with
      | .mk r3 _ => r1 = sparkleSynthDepth ∧ r2 = sparkleChildCache ∧ r3 = sparkleChildSynth

/-- **PREMISE (initial-heap relation; NOT a `mkRef` statement).** `w` corresponds to a model heap whose
tracked cells hold the `mkRef` arguments. -/
def InitHeapRel (R : Corr Ob Pr Er) (w : Void IO.RealWorld) (h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)) :
    Prop :=
  R w h0 ∧ h0.cache = ({} : Std.HashMap Name Res) ∧ h0.synth = none ∧ h0.depth = 0

/-- The world at the end of module load: the three `mkRef`s, then `sparkleChildSynth.set (some synthesizeChild)`. -/
def loadW (wS : Void IO.RealWorld) : Void IO.RealWorld :=
  setW sparkleChildSynth (some synthesizeChild) (mkRefsW wS)

/-- **PREMISE (`ST.Ref.get`).** In related worlds the three reads are the model cells. -/
def GetSpec (R : Corr Ob Pr Er) : Prop :=
  ∀ w h, R w h →
    readOf sparkleChildCache w = h.cache ∧ readOf sparkleChildSynth w = h.synth ∧
      readOf sparkleSynthDepth w = h.depth

/-- **PREMISE (`ST.Ref.set` on `sparkleChildSynth`).** A write corresponds to the model write. -/
def SetSynthSpec (R : Corr Ob Pr Er) : Prop :=
  ∀ w h v, R w h → R (setW sparkleChildSynth v w) (Tools.ShippingHeapModel.hset .synth v h)

/-- **PREMISE (quiet transfer).** Related worlds whose model registry is `Q` are `quiet`. -/
def QuietSpec (R : Corr Ob Pr Er) (Q : Pr → Prop) (quiet : Void IO.RealWorld → Prop) : Prop :=
  ∀ w h, R w h → Q h.reg → quiet w

/-- **`StartAtLoad` from the correspondence premises.** PROVED relative to the five premises above. -/
theorem startAtLoad_of_corr (R : Corr Ob Pr Er) (Q : Pr → Prop) (quiet : Void IO.RealWorld → Prop)
    {wS : Void IO.RealWorld} {h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)}
    (_htrace : MkRefTrace wS) (hmk : InitHeapRel R (mkRefsW wS) h0) (hget : GetSpec R) (hset : SetSynthSpec R)
    (hq : QuietSpec R Q quiet) (hQ0 : Q h0.reg) :
    StartAtLoad quiet (loadW wS) := by
  obtain ⟨hR, -, -, hd⟩ := hmk
  have h1 := hset (mkRefsW wS) h0 (some synthesizeChild) hR
  obtain ⟨-, hs, hd1⟩ := hget _ _ h1
  refine ⟨hq _ _ h1 ?_, ?_, ?_⟩
  · rw [Tools.ShippingHeapModel.set_reg]; exact hQ0
  · show readOf sparkleChildSynth (setW _ _ _) = _
    rw [hs]; exact Tools.ShippingHeapModel.get_set_same (σ := sig Ob Pr Er) .synth (some synthesizeChild) h0
  · show readOf sparkleSynthDepth (setW _ _ _) = 0
    rw [hd1]; exact hd

/-- L9b's `startContents_session` with `StartAtLoad` replaced by the correspondence premises (new name; old
theorem unchanged). Remaining Prop hypotheses: `htrace hmk hget hset hq hQ0` (this file), `hA`/`hB` (entry premises),
`hO : OtherCodeKeeps` (OPEN), plus `O` itself. -/
theorem startContents_session_rt {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hB : BodyStepC O) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (hO : OtherCodeKeeps O.quiet Other)
    (R : Corr Ob Pr Er) (Q : Pr → Prop) {wS : Void IO.RealWorld}
    {h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)}
    (htrace : MkRefTrace wS) (hmk : InitHeapRel R (mkRefsW wS) h0) (hget : GetSpec R) (hset : SetSynthSpec R)
    (hq : QuietSpec R Q O.quiet) (hQ0 : Q h0.reg) {w : Void IO.RealWorld}
    (hs : Chain (fun a b => EntryStep mctx mref cctx cref a b ∨ Other a b)
      (loadW wS) w) :
    O.quiet w ∧ StartContents w :=
  startContents_session O hA hB Other hO (startAtLoad_of_corr R Q O.quiet htrace hmk hget hset hq hQ0) hs

end Tools.ShippingStartAtLoad
