import Tools.ShippingStartWorldA2
import Tools.ShippingHeapModel
-- BUILT (unit RT1, par/u-rt1): rt1a exit 1 (▸ misuse; BodyStepC namespace), rt1b exit 0. No sorry/axiom/native_decide.

/-! # Unit RT1: `StartAtLoad` from per-primitive correspondence statements (ledger L9c)

**Verdict (read this first).** `StartAtLoad O.quiet w0` is NOT discharged. It is REDUCED to explicitly
named correspondence PREMISES between the opaque runtime operations and the pure heap model
(`Tools/ShippingHeapModel.lean`), one per primitive, plus one quiet-transfer premise and one
model-side premise. Those premises are exactly the "runtime fit" for the two `initialize`d refs;
they are PREMISES, not proved, and not implied by `O`:

* `MkRefSpec R w0 h0` — `IO.mkRef` (`@[extern] opaque`): the world after the `IO.mkRef` initializers of
  `sparkleChildCache` (`{}`), `sparkleChildSynth` (`none`), `sparkleSynthDepth` (`0`), related by the
  abstraction `R` to a model heap holding exactly those contents. NOT in `O` (no field mentions allocation).
* `GetSpec R` — `ST.Ref.get` (`@[extern] opaque`): the read of each tracked ref in a related world is the
  model cell. NOT in `O`: `O`'s fields (`frame`, `cacheSet`, `depthSet`, …) are about `cv/sv/dv` BEFORE vs AFTER
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
after the module `initialize`'s `sparkleChildSynth.set (some synthesizeChild)` (`setW`). The model reasoning
(`get_set_same`, `get_set_other`, `set_reg`) is the only proved content. Corollary `startContents_session_rt`:
L9b's `startContents_session` with `StartAtLoad` replaced. Old theorems unchanged.

NOT claimed: runtime fit; that `R` exists; that the premises are jointly satisfiable with `O` (logical
inconsistency NOT PROVEN, no proof either way); that the `IO.mkRef` of the Lean runtime allocates fresh refs
distinct from the model's tracked ones (that is inside `MkRefSpec`/`SetSynthSpec` being about related worlds);
`OtherCodeKeeps`; that initializers of OTHER modules between the mkRefs and the set do not write the refs
(`h0` is arbitrary, but `MkRefSpec` asserts the contents AT `w0` — the set directly follows). -/

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

/-- **PREMISE (`IO.mkRef`).** `w0` — the world after the three `IO.mkRef` initializers — corresponds to a model
heap whose tracked cells hold the `mkRef` arguments. -/
def MkRefSpec (R : Corr Ob Pr Er) (w0 : Void IO.RealWorld) (h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)) :
    Prop :=
  R w0 h0 ∧ h0.cache = ({} : Std.HashMap Name Res) ∧ h0.synth = none ∧ h0.depth = 0

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
    {w0 : Void IO.RealWorld} {h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)}
    (hmk : MkRefSpec R w0 h0) (hget : GetSpec R) (hset : SetSynthSpec R)
    (hq : QuietSpec R Q quiet) (hQ0 : Q h0.reg) :
    StartAtLoad quiet (setW sparkleChildSynth (some synthesizeChild) w0) := by
  obtain ⟨hR, -, -, hd⟩ := hmk
  have h1 := hset w0 h0 (some synthesizeChild) hR
  obtain ⟨-, hs, hd1⟩ := hget _ _ h1
  refine ⟨hq _ _ h1 ?_, ?_, ?_⟩
  · rw [Tools.ShippingHeapModel.set_reg]; exact hQ0
  · show readOf sparkleChildSynth _ = _
    rw [hs]; exact Tools.ShippingHeapModel.get_set_same (σ := sig Ob Pr Er) .synth (some synthesizeChild) h0
  · show readOf sparkleSynthDepth _ = 0
    rw [hd1]; exact hd

/-- L9b's `startContents_session` with `StartAtLoad` replaced by the correspondence premises (new name; old
theorem unchanged). Remaining Prop hypotheses: `hmk hget hset hq hQ0` (this file), `hA`/`hB` (entry premises),
`hO : OtherCodeKeeps` (OPEN), plus `O` itself. -/
theorem startContents_session_rt {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hB : BodyStepC O) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (hO : OtherCodeKeeps O.quiet Other)
    (R : Corr Ob Pr Er) (Q : Pr → Prop) {w0 : Void IO.RealWorld}
    {h0 : Tools.ShippingHeapModel.Heap (sig Ob Pr Er)}
    (hmk : MkRefSpec R w0 h0) (hget : GetSpec R) (hset : SetSynthSpec R)
    (hq : QuietSpec R Q O.quiet) (hQ0 : Q h0.reg) {w : Void IO.RealWorld}
    (hs : Chain (fun a b => EntryStep mctx mref cctx cref a b ∨ Other a b)
      (setW sparkleChildSynth (some synthesizeChild) w0) w) :
    O.quiet w ∧ StartContents w :=
  startContents_session O hA hB Other hO (startAtLoad_of_corr R Q O.quiet hmk hget hset hq hQ0) hs

end Tools.ShippingStartAtLoad
