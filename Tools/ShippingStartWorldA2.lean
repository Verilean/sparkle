import Tools.ShippingStartWorldA
import Tools.ShippingChildDepthC
-- BUILT (unit ST2, par/u-st2): st2d exit 0 (this file); st2e exit 0 (Tests.Compiler.StartWorldATest with the in-file audit).

/-! # Unit ST2: the start contents survive one entry run (ledger L9a, R13/R14)

`StartContents w` (`sv w = some synthesizeChild`, `dv w = 0`) is what the entry needs at its start. Unit ST
left it OPEN; the reviewer's point: the values right after `initialize` are not the start values of an
arbitrary command (writes, earlier commands, failed commands lie in between).

**Writes of the two refs, by grep** (`Sparkle/`, whole repo outside `Tools/`):
* `sparkleChildSynth`: ONE write, `Elab.lean:8934` `initialize sparkleChildSynth.set (some synthesizeChild)`
  (module load). No other `.set`/`.modify` anywhere in `Sparkle/`.
* `sparkleSynthDepth`: writes only in `synthesizeCombinationalCoreWith` (`Elab.lean:5561` `set (depth+1)`,
  `:5577` `modify (· - 1)` in the `finally`); the initial `IO.mkRef 0` (`:963`). Outside `Sparkle/`, only
  test/probe files write it (`Tests/Compiler/{SingleOutHit,SubInstanceKey,OptPrintGuardFires}Test.lean`,
  `scripts/shipping-coverage/*`: `sparkleSynthDepth.set 0/1`) — see `OtherCodeKeeps` below.

What this file PROVES (no new axiom/law; premises `O`, `hA`, `BodyStepC O`, named in the statements):
`startContents_entry`: from `O.quiet w ∧ StartContents w`, a run of the FULL entry `synthesizeCombinational`
— returning OR throwing (the `finally` is inside the existing `Triple`: `full_tripleAC_of_bodies` covers every
outcome, exceptions in `EQ`) — ends in `O.quiet w' ∧ StartContents w'` (and a thrown exception has an `OkExc`
message). So `quiet` is ALSO carried along (it is part of `JQ`), not only the two contents. The depth
decrement is not re-proved here: it is inside `BodyStepC`'s `JQC O D` bookkeeping via the existing
`core0_tripleAC_aux` (`tripleC_depthSet`, the `finally` modify).
What it does NOT prove: that the start world is a `StartContents` world (`StartAtLoad`), that code between
commands keeps it (`OtherCodeKeeps`), that a fresh `liftTermElabM` creates refs for which the same `O` is a
witness (`O` is indexed by `mref cref`; a real command makes new ones), `O.quiet` itself, `BodyStepC O`. -/

namespace Tools.ShippingStartWorldA2
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingStartWorldA
open Tools.ShippingChildFresh

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`StartContents` (with `quiet`) is preserved by one run of the full entry, on every outcome.**
PROVED from `full_tripleAC_of_bodies`; premises `O`, `hA`, `hB : BodyStepC O`. -/
theorem startContents_entry (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (declName : Name) (hB : BodyStepC O) {w : Void IO.RealWorld}
    (hq : O.quiet w) (hc : StartContents w) :
    match synthesizeCombinational declName mctx mref cctx cref w with
    | .ok _ w' => O.quiet w' ∧ StartContents w'
    | .error e w' => O.quiet w' ∧ StartContents w' ∧ OkExc e := by
  have h := full_tripleAC_of_bodies O hA declName hB w (jq_zero_of O.quiet hq hc)
  split
  · rename_i heq
    rw [heq] at h
    exact ⟨h.1.1, h.1.2.1, h.1.2.2⟩
  · rename_i heq
    rw [heq] at h
    exact ⟨h.1.1, And.intro ⟨h.1.2.1, h.1.2.2⟩ h.2⟩

/-- Returning runs, in `RunsTo` form (as the endpoint theorems state their run). -/
theorem startContents_of_runs (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (declName : Name) (hB : BodyStepC O) {w w' : Void IO.RealWorld} {r}
    (hq : O.quiet w) (hc : StartContents w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (synthesizeCombinational declName) mctx mref cctx cref w r w') :
    O.quiet w' ∧ StartContents w' := by
  have h := startContents_entry O hA declName hB hq hc
  unfold Tools.ShippingEntrySoundness.RunsTo at hr
  rw [hr] at h
  exact h

/-- The world a failed or successful entry run ends in (`endW` of the existing calculus). -/
theorem startContents_endW (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (declName : Name) (hB : BodyStepC O) {w : Void IO.RealWorld}
    (hq : O.quiet w) (hc : StartContents w) :
    O.quiet (endW mctx mref cctx cref (synthesizeCombinational declName) w) ∧
      StartContents (endW mctx mref cctx cref (synthesizeCombinational declName) w) := by
  have h := startContents_entry O hA declName hB hq hc
  unfold endW
  split <;> rename_i heq <;> rw [heq] at h
  · exact h
  · exact ⟨h.1, h.2.1⟩

/-! ## A session of commands, and the two named gaps -/

/-- One `#synthesizeVerilog`-style step: the full entry on `declName` from `w` ends (returning or
throwing) in `w'`. Same `mctx mref cctx cref` throughout (the fixed-`O` fragment, see the header). -/
def EntryStep (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) : Prop :=
  ∃ declName, w' = endW mctx mref cctx cref (synthesizeCombinational declName) w

/-- **GAP 1 (OPEN): the world at module load → the first command.** The initial world satisfies the
invariant: `quiet` and `StartContents`. `initialize` (`IO.mkRef 0`, `IO.mkRef none`, then
`sparkleChildSynth.set (some synthesizeChild)`) runs outside the logic; `ST.Ref.get/set` and `IO.mkRef`
are `@[extern] opaque`. Not derivable. -/
def StartAtLoad (quiet : Void IO.RealWorld → Prop) (w0 : Void IO.RealWorld) : Prop :=
  quiet w0 ∧ StartContents w0

/-- **GAP 2 (OPEN): non-entry code between commands.** `Other` stands for whatever else runs between two
entries (other commands/elaborators, a failed command's cleanup, test-file `sparkleSynthDepth.set`
probes); it cannot be defined (command monad not modelled). The Prop says it keeps the invariant.
By grep no code in `Sparkle/` writes either ref besides the entry and the `initialize`; the test/probe
files that write the depth are the known exceptions. -/
def OtherCodeKeeps (quiet : Void IO.RealWorld → Prop) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop) :
    Prop :=
  ∀ w w', Other w w' → quiet w → StartContents w → quiet w' ∧ StartContents w'

/-- Reflexive-transitive closure (local: core Lean has no `Relation.ReflTransGen`). -/
inductive Chain (R : Void IO.RealWorld → Void IO.RealWorld → Prop) (a : Void IO.RealWorld) :
    Void IO.RealWorld → Prop
  | refl : Chain R a a
  | tail {b c} : Chain R a b → R b c → Chain R a c

/-- **Session theorem (PROVED, relative to GAP 1 and GAP 2 and the entry premises).** Along any chain of
entry steps and `Other` steps from a `StartAtLoad` world, every world keeps `quiet ∧ StartContents` — so every
entry of the chain starts in a `JQ O.quiet 0` world. -/
theorem startContents_session (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hB : BodyStepC O) (Other : Void IO.RealWorld → Void IO.RealWorld → Prop)
    (hO : OtherCodeKeeps O.quiet Other) {w0 w : Void IO.RealWorld}
    (h0 : StartAtLoad O.quiet w0)
    (hs : Chain (fun a b => EntryStep mctx mref cctx cref a b ∨ Other a b) w0 w) :
    O.quiet w ∧ StartContents w := by
  induction hs with
  | refl => exact h0
  | tail _ hstep ih =>
    rcases hstep with ⟨declName, rfl⟩ | ho
    · exact startContents_endW O hA declName hB ih.1 ih.2
    · exact hO _ _ ho ih.1 ih.2

/-- **ITEM 3 (OPEN, separate): `O.quiet` and a non-empty witness.** `quiet` is an arbitrary predicate
of `O`; preservation above does not make `∃ w, O.quiet w ∧ StartContents w` true. Stated as the Prop
a witness must supply (not proved, no witness for the real refs given). -/
def QuietWitness (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∃ w, O.quiet w ∧ StartContents w

end Tools.ShippingStartWorldA2
