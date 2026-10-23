import Tools.ShippingSrm11Bounds
import Tools.ShippingMachineShipsDepth
import Tools.ShippingOptimizePorts
import Tools.ShippingSeqOptSoundness
import Tools.ShippingKidsResetSat
set_option autoImplicit false
-- BUILT (unit SRM13): dev runs a2 (Supply), a4 (ParentTest), b4 (AuditTest) all exit 0; the final-SHA rebuild is in REPORT-SRM13.md.
-- SCOPE: the three machine-side premises of SRM11 (`hseedB`, `hst`, `hkids`), generic part.
-- hseedB: PROVED from the machine's own seeding `seedIn` and the INPUT-RANGE fact (`ins t x < 2 ^ weS o x` on the inputs), which is a premise already stated by the machine bridge (Tools.ShippingSrm8Bridge);
--   a concrete out-of-range stream falsifies `hseedB` (`seedIn_not_bounded`), so the input range is a genuine source fact, not removable.
-- hst, hkids: NOT supplied.  The machine's `Reset` fixes registers only (values `init.toNat`); `Bounded`/`InvN` constrain EVERY name.  The exact residual facts are `RegsFit` (initial values fit the emitted
--   widths) and `NonRegBounded` (non-register names of the start state fit); `bounded_of_regsAtInit` / `invN_of_resetN_fitTree` / `kidInvN_of_resetNk` prove them SUFFICIENT together with the Reset clause.
--   `bounded_not_forced` / `invN0_not_forced` give concrete falsifying states for the bare binders.
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm13Supply
open Sparkle.IR.AST Sparkle.IR.Semantics Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tools.ShippingHierStateG Tools.ShippingHierState
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineDepth (ResetN)
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.IR.OptCheck (checkedOptimize)

/-! ## hseedB -/

/-- **The machine's seeding keeps widths**, from the input range of the stream. -/
theorem seedB_of_seedIn (o : Module) (ins : Nat → String → Nat)
    (hin : ∀ t x, x ∈ o.inputs.map (·.name) → ins t x < 2 ^ weS o x) :
    ∀ k st, Bounded (weS o) st → Bounded (weS o) (seedIn o ins k st) := by
  intro k st hst n
  unfold seedIn
  by_cases h : (o.inputs.map (·.name)).contains n = true
  · rw [if_pos h]
    exact hin k n (List.contains_iff_mem.mp h)
  · rw [if_neg h]
    exact hst n

/-- the same for the shipped module, with the stream's range stated on the source module's inputs (`checkedOptimize` keeps the ports) -/
theorem seedB_checkedOptimize (b : Module) (ins : Nat → String → Nat)
    (hin : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) :
    ∀ k st, Bounded (weS (checkedOptimize b)) st → Bounded (weS (checkedOptimize b)) (seedIn b ins k st) := by
  have hp := (Tools.ShippingOptimizePorts.checkedOptimize_ports b).1
  have e : seedIn b ins = seedIn (checkedOptimize b) ins := by
    funext t st n
    simp only [seedIn, hp]
  rw [e]
  exact seedB_of_seedIn (checkedOptimize b) ins (by rw [hp]; exact hin)

/-- the bare binder `hseedB` is not forced: an input stream out of range falsifies it -/
theorem seedIn_not_bounded (o : Module) (ins : Nat → String → Nat) (t : Nat) (x : String)
    (hx : x ∈ o.inputs.map (·.name)) (hbig : 2 ^ weS o x ≤ ins t x) :
    ¬ ∀ k st, Bounded (weS o) st → Bounded (weS o) (seedIn o ins k st) := by
  intro h
  have hb : Bounded (weS o) (fun _ => 0) := fun n => Nat.two_pow_pos _
  have := h t _ hb x
  have hc : (o.inputs.map (·.name)).contains x = true := List.contains_iff_mem.mpr hx
  simp only [seedIn, hc, if_true] at this
  omega

/-- the bare binder `hseedB` is not a consequence of the module alone: a seeding writing `2 ^ width` falsifies it -/
theorem hseedB_not_forced (o : Module) :
    ∃ seed : Nat → (String → Nat) → Env, ¬ ∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st) := by
  refine ⟨fun _ _ n => 2 ^ weS o n, fun h => ?_⟩
  have hb : Bounded (weS o) (fun _ => 0) := fun n => Nat.two_pow_pos _
  have := h 0 _ hb ""
  exact Nat.lt_irrefl _ this

/-! ## hst, hkids: the residual facts and their sufficiency -/

/-- the registers of the start state hold their reset values -/
def RegsAtInit (o : Module) (st : String → Nat) : Prop :=
  ∀ r c rs inp (init : Int), Stmt.register r c rs inp init ∈ o.body → st r = init.toNat

/-- the reset values of the registers fit the emitted widths (a fact about the module's `init`s; the emitter encodes `init` modulo the width, so the check does not give it) -/
def RegsFit (o : Module) : Prop :=
  ∀ r c rs inp (init : Int), Stmt.register r c rs inp init ∈ o.body → init.toNat < 2 ^ weS o r

/-- the start state's non-register names fit the emitted widths -/
def NonRegBounded (o : Module) (st : String → Nat) : Prop :=
  ∀ x, (¬ ∃ c rs inp init, Stmt.register x c rs inp init ∈ o.body) → st x < 2 ^ weS o x

/-- **Sufficient for `hst`**: registers at their reset values that fit, the other names within their widths. -/
theorem bounded_of_regsAtInit {o : Module} {st : String → Nat} (h1 : RegsAtInit o st) (h2 : RegsFit o)
    (h3 : NonRegBounded o st) : Bounded (weS o) st := by
  intro x
  by_cases hx : ∃ c rs inp init, Stmt.register x c rs inp init ∈ o.body
  · obtain ⟨c, rs, inp, init, hm⟩ := hx
    rw [h1 x c rs inp init hm]
    exact h2 x c rs inp init hm
  · exact h3 x hx

/-- the bare binder `hst` is not forced by the module: some state is out of range -/
theorem bounded_not_forced (o : Module) : ∃ st : String → Nat, ¬ Bounded (weS o) st :=
  ⟨fun n => 2 ^ weS o n, fun h => Nat.lt_irrefl _ (h "")⟩

/-- the bare binder `hkids` (depth 0) is not forced by the module -/
theorem invN0_not_forced (C : String → Option (Module × WEnv)) (gc : Module) :
    ∃ ks : KT 0, ¬ InvN C 0 gc ks :=
  ⟨(⟨fun n => 2 ^ weS gc n, fun _ _ => 0⟩ : KidState), fun h => Nat.lt_irrefl _ (h "")⟩

/-- the width fits of a whole instance tree, at depth `n` -/
def FitTree (C : String → Option (Module × WEnv)) : (n : Nat) → Module → KT n → Prop
  | 0, o, ks => RegsFit o ∧ NonRegBounded o (KidState.st ks)
  | m + 1, o, s => RegsFit o ∧ NonRegBounded o s.st ∧
      ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (gc, gcwe) →
        FitTree C m gc (s.kids iname)

/-- **Sufficient for `InvN`**: the depth-`n` reset of the tree plus the width fits of the tree. -/
theorem invN_of_resetN_fitTree (D : Design) :
    ∀ (n : Nat) (o : Module) (ks : KT n), ResetN D n o ks → FitTree (childMap D.modules) n o ks →
      InvN (childMap D.modules) n o ks
  | 0, o, ks, hr, hf => by
    exact bounded_of_regsAtInit hr.1 hf.1 hf.2
  | m + 1, o, s, hr, hf => by
    refine ⟨bounded_of_regsAtInit hr.1 hf.1 hf.2.1, ?_⟩
    intro mn iname conns gc gcwe hm hc
    exact invN_of_resetN_fitTree D m gc (s.kids iname)
      (hr.2.2.2 mn iname conns gc hm (Tools.ShippingKidsResetSat.moduleByName_of_childMap hc))
      (hf.2.2 mn iname conns gc gcwe hm hc)

/-- the module found by `moduleByName` carries the name looked up -/
theorem moduleByName_name {ms : List Module} {mn : String} {gc : Module}
    (h : Sparkle.IR.Machine.moduleByName ms mn = some gc) : gc.name = mn := by
  unfold Sparkle.IR.Machine.moduleByName at h
  have := List.find?_some h
  simpa using this

/-- **The machine's children reset gives the instance reset of the shipped module's instances**: `ResetNk` is stated on the source module's instance statements, so the shipped module's
instances must be among them (`hO`). -/
theorem kidReset_of_resetNk {n : Nat} {raw o : Module} {D : Design} {kids : String → KT n}
    (hr : Tools.ShippingMachineShipsDepth.ResetNk n raw D kids)
    (hO : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → Stmt.inst mn iname conns ∈ raw.body) :
    ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body → childMap D.modules mn = some (gc, gcwe) →
      ResetN D n gc (kids iname) := by
  intro mn iname conns gc gcwe hm hc
  have hmb := Tools.ShippingKidsResetSat.moduleByName_of_childMap hc
  have hnm := moduleByName_name hmb
  refine hr iname gc ⟨conns, ?_⟩ (by rw [hnm]; exact hmb)
  rw [hnm]
  exact hO mn iname conns hm

/-- **Sufficient for `hkids`**: the machine's children reset (`ResetNk`) plus the width fits of each instance's tree. -/
theorem kidInvN_of_resetNk {n : Nat} {raw o : Module} {D : Design} {kids : String → KT n}
    (hr : Tools.ShippingMachineShipsDepth.ResetNk n raw D kids)
    (hO : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → Stmt.inst mn iname conns ∈ raw.body)
    (hf : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body → childMap D.modules mn = some (gc, gcwe) →
      FitTree (childMap D.modules) n gc (kids iname)) :
    ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body → childMap D.modules mn = some (gc, gcwe) →
      InvN (childMap D.modules) n gc (kids iname) :=
  fun mn iname conns gc gcwe hm hc =>
    invN_of_resetN_fitTree D n gc (kids iname) (kidReset_of_resetNk hr hO mn iname conns gc gcwe hm hc)
      (hf mn iname conns gc gcwe hm hc)

end Tools.ShippingSrm13Supply
