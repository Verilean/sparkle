import Tools.ShippingCacheCoherentRun
import Tools.ShippingCallsRunFinal
import Tools.ShippingDesignWithG
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

variable {tenv : Lean.Environment}

/-! # Provenance through the machine route's own code (the closings)

The machine route joins its children's designs with `designWith`
(`closeInsts`, `closeInstsG`), the children coming from the memoised child
entry (`closeInstsM`, `closeInstsGM`). This file follows
`Tools.ShippingCacheCoherentRun.Prov` through that code, which is ordinary
(not the translator):

* pure — `mem_designWith`: a module of the joined design is a module of the
  parent design or a visited one (a child's module, or a module of a child's
  design); `closeInsts_design` / `closeInstsG_design`: the closing's design
  IS `designWith children d₀`;
* run level, from the existing laws — `closeInstsGM_design_prov`: for the
  general closing WITHOUT memory children, every module of the closing's
  design is a memory module or the module of an entry of the END cache,
  provided the parent design's modules are (the children are entries of the
  end cache: `Tools.ShippingCallsRunFinal.closeInstsGM_run_allF`);
* run level, relative to the residual `CoreFresh` — `closeInstsM_prov`,
  `closeInstsGM_prov`: a run of a closing keeps `Prov`;
  `machine_prov`: a run of the machine synthesis keeps `Prov`, relative to
  `CoreFresh` and to `HarnessProv` (the harness — the TRANSLATOR — keeps
  `Prov`; a statement, NOT derived: the translator's instance arms call the
  memoised entry, and following `Prov` through them is the same work as
  `translateRel` / `legacyRel` did for the invariant `J`);
* consumption — `machine_closes_of_prov`: the built relative closing
  `MachineClosesAtS` fires from a `Prov` start world.

Not here: the one-output closing's and the memory-children closing's design
provenance (their run lemmas give `ChildrenReal`, not "an entry of the end
cache"); anything about the translator.

WRITTEN, NOT BUILT (par/a-33). ORIGIN DISPATCH: `closeInstsGM_design_prov`
asks the tag condition `hnotag` (no memory ORIGIN) in place of the name
condition; `closeInstsGM_prov` follows the tagged `mapM` — WRITTEN, NOT BUILT
against patched compiler (par/o-close). -/
namespace Tools.ShippingCacheCoherentClose
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingCallsKidsS Tools.ShippingCacheCoherent
open Tools.ShippingCacheCoherentRun Tools.ShippingCallsSame
open Tools.ShippingDesignWith (addM)
open Tools.ShippingDesignWithG (visited designWith_flatG mem_visited)

/-! ## Pure: the joined design -/

theorem mem_foldl_addM : ∀ (l acc : List Sparkle.IR.AST.Module) (x : Sparkle.IR.AST.Module),
    x ∈ l.foldl addM acc → x ∈ acc ∨ x ∈ l
  | [], _, _, h => Or.inl h
  | c :: l, acc, x, h => by
    have h' : x ∈ l.foldl addM (addM acc c) := h
    rcases mem_foldl_addM l (addM acc c) x h' with h1 | h1
    · unfold addM at h1
      split at h1
      · exact Or.inl h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inl h2
        · have hxc : x = c := by simpa using h2
          rw [hxc]
          exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- A module of the joined design: of the parent design, or visited. -/
theorem mem_designWith {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {d : Sparkle.IR.AST.Design} {g : Sparkle.IR.AST.Module}
    (h : g ∈ (Sparkle.IR.Machine.designWith children d).modules) :
    g ∈ d.modules ∨ g ∈ visited children := by
  rw [designWith_flatG children d] at h
  exact mem_foldl_addM _ _ g h

/-- The one-output closing's design is the joined design. -/
theorem closeInsts_design {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    d = Sparkle.IR.Machine.designWith children d₀ := by
  unfold Sparkle.IR.Machine.closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
    rfl
  · cases h

/-- The general closing's design is the joined design. -/
theorem closeInstsG_design {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String}
    {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) =
      some (m, d)) :
    d = Sparkle.IR.Machine.designWith children d₀ := by
  unfold Sparkle.IR.Machine.closeInstsG at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
    rfl
  · cases h

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## Run level, from the existing laws: the general closing's design -/

/-- **The general closing without memory children: its design's modules have
a provenance in the END cache**, when the parent design's modules have and
the end cache satisfies `Prov`. Each child is the end cache's entry under
its declaration (`closeInstsGM_run_allF`); the design is the join. -/
theorem closeInstsGM_design_prov (L : RefLaws mref cref)
    (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ m d} {w w' : Void IO.RealWorld} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hnotag : ∀ o ∈ shape.instTagged, o.2.child?.isNone = true)
    (hp' : Prov (L.val w'))
    (h0 : ∀ a ∈ d₀.modules, IsMem a ∨ IsTop (L.val w') a)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∀ a ∈ d.modules, IsMem a ∨ IsTop (L.val w') a := by
  obtain ⟨children, heq, ⟨hlen, -⟩, -, hcache, -⟩ :=
    Tools.ShippingCallsRunFinal.closeInstsGM_run_allF L hB hw hd hnotag hr
  have hdes : d = Sparkle.IR.Machine.designWith children d₀ := closeInstsG_design heq.symm
  intro a ha
  rw [hdes] at ha
  rcases mem_designWith ha with h1 | h1
  · exact h0 a h1
  · obtain ⟨c, hc, hac⟩ := mem_visited.mp h1
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
    have hkl : k < shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      rw [hlen] at this
      exact this
    obtain ⟨y, hy, hget⟩ := hcache k hkl
    have e : c = y := Option.some.inj (hk.symm.trans hy)
    rw [← e] at hget
    rcases hac with hac | hac
    · exact Or.inr ⟨_, c, hget, hac⟩
    · exact (hp' _ c hget).2 a hac

/-! ## Run level, relative to the residual: the closings keep `Prov` -/

/-- The invariant the closings' `mapM` carries. -/
def PInv (L : RefLaws mref cref) (w : Void IO.RealWorld) : Prop :=
  InvV L w ∧ L.dval w ≠ 0 ∧ Prov (L.val w)

/-- One call of the memoised entry keeps `PInv`, relative to `CoreFresh`. -/
theorem child_pinv (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hR : ∀ c, CoreFresh L c) {c : Name} {w w' : Void IO.RealWorld} {y : Res}
    (hp : PInv L w) (hy : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    PInv L w' := by
  obtain ⟨hw, hd, hpv⟩ := hp
  refine ⟨(synthesizeChild_inv L hB hw hy).2, ?_, synthesizeChild_prov L hw hd hpv (hR c) hy⟩
  rw [synthesizeChild_depth L hB hw hy]
  exact hd

/-- **The one-output closing keeps `Prov`**, relative to `CoreFresh`. -/
theorem closeInstsM_prov (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hR : ∀ c, CoreFresh L c) {shape t m₀ d₀ r} {w w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    Prov (L.val w') := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  have hs1 := L.same .synthGet hget
  have hp1 : PInv L w1 := ⟨hw1, by rw [hs1.2.2]; exact hd, by rw [hs1.1]; exact hp⟩
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨-, hww⟩ := RunsTo.pure_world hr
  obtain ⟨-, -, hp2⟩ := mapM_hoare _ (PInv L)
    (fun (_ : Name × List Nat × MixedGateBinder) (_ : Res) => True)
    (fun x w y w' hp hy => by
      -- a tactic block: elaborated after `hch` has fixed the mapped function
      exact ⟨trivial, child_pinv L hB hR hp hy⟩)
    shape.insts children hp1 hch
  rw [hww]
  exact hp2.2.2

/-- **The general closing keeps `Prov`**, relative to `CoreFresh` (a memory
child is built: its step leaves the world). -/
theorem closeInstsGM_prov (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hR : ∀ c, CoreFresh L c) {shape t m₀ d₀ r} {w w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    Prov (L.val w') := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  have hs1 := L.same .synthGet hget
  have hp1 : PInv L w1 := ⟨hw1, by rw [hs1.2.2]; exact hd, by rw [hs1.1]; exact hp⟩
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨-, hww⟩ := RunsTo.pure_world hr
  obtain ⟨-, -, hp2⟩ := mapM_hoare _ (PInv L)
    (fun (_ : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) (_ : Res) => True)
    (fun x w y w' hp hy => by
      -- the patched closing maps the tagged entries, dispatching on the ORIGIN
      obtain ⟨c, o⟩ := x
      dsimp only at hy
      cases hmc : Sparkle.Compiler.MachInstOrigin.InstOrigin.child? o with
      | some md =>
        rw [hmc] at hy
        obtain ⟨-, hwy⟩ := RunsTo.pure_world hy
        rw [hwy]
        exact ⟨trivial, hp⟩
      | none =>
        rw [hmc] at hy
        exact ⟨trivial, child_pinv L hB hR hp hy⟩)
    shape.instTagged children hp1 hch
  rw [hww]
  exact hp2.2.2

/-! ## The machine synthesis, relative to the residual and to the harness -/

/-- **A STATEMENT, not derived**: the machine route's harness — a run of the
translator on the transition — keeps `Prov`, from an invariant world of
positive depth. -/
def HarnessProv (L : RefLaws mref cref) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (mctx : Meta.Context) (cctx : Core.Context) (b : Bool) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (w : Void IO.RealWorld) (r : Res) (w' : Void IO.RealWorld),
    InvV L w → L.dval w ≠ 0 → Prov (L.val w) →
    RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
      bs body) mctx mref cctx cref w r w' → Prov (L.val w')

/-- **A run of the machine synthesis keeps `Prov`** — whatever it returns —
relative to `HarnessProv` and `CoreFresh`: the harness, then nothing
(`closeLets` failed, or no call), or one of the two closings. -/
theorem machine_prov (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L') (hHP : HarnessProv L)
    (hR : ∀ c, CoreFresh L c) {b : Bool} {declName : Name} {shape : MachineShape}
    {r : Option Res} {w w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w') : Prov (L.val w') := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 : InvV L w1 := harness_inv L hB hH hw run
  have hd1 : L.dval w1 ≠ 0 := by
    rw [harness_depth L hB hH hw run]
    exact hd
  have hp1 : Prov (L.val w1) :=
    hHP mctx cctx b declName shape.binders shape.body w (t, d') w1 hw hd hp run
  dsimp only at hr
  split at hr
  · split at hr
    · obtain ⟨-, hww⟩ := RunsTo.pure_world hr
      rw [hww]
      exact hp1
    · split at hr
      · exact closeInstsM_prov L hB hR hw1 hd1 hp1 hr
      · exact closeInstsGM_prov L hB hR hw1 hd1 hp1 hr
  · obtain ⟨-, hww⟩ := RunsTo.pure_world hr
    rw [hww]
    exact hp1

/-! ## Consumption -/

/-- **The closing from a `Prov` start world**: the built relative closing
`MachineClosesAtS` (for ANY declaration list) fires, because the world the
machine synthesis ends in is coherent — relative to `HarnessProv` and
`CoreFresh`. -/
theorem machine_closes_of_prov {declName : Name} {shape : MachineShape} (decls : List Name)
    (hS : MachineClosesAtS mctx mref cctx cref declName shape decls)
    (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L') (hHP : HarnessProv L)
    (hR : ∀ c, CoreFresh L c) {b : Bool} {r : Option Res} {w w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w') : r ≠ none :=
  hS b w r w' (invW_of_invV L hw) (depthPos_of L hd) hr
    (cacheAgrees_of_coherentAt decls
      (coherentAt_of_val L (coherent_of_prov (machine_prov L hB hH hHP hR hw hd hp hr))))

end Tools.ShippingCacheCoherentClose
