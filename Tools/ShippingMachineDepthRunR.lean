import Tools.ShippingMachineDepthRun
import Tools.ShippingChildServe
import Tools.ShippingChildRun

/-! # Children with calls: the depth conditions from the served child's run witness

`MachineRunN` asks, of the module an instance resolves to, a core run of the
child entry with the child's run boundary, `ExtendsAway` and `NoInstOf`.
`MachineRunNC` takes the child's boundary in the run's contexts and start
world (`CtxBnd`), and `machineRunNC_of_real` DERIVES it from the run witness
`ServedReal` gives for the served instance (`RealChild`: SOME run of the
child's entry in the parent's contexts returning that module, starting in a
world where the cache invariant holds — not a proof about the specific call,
or cache hit, inside the parent's run): the core run under that
run (`synthesizeCombinational_design`: the full entry changes only the
module named after the top), the child's own closing (`closeInsts_acyclic` /
`closeInstsG_acyclic`: the child's module and design do not instantiate it),
and the parent's closing (every module of the child's design resolves in the
parent's design to itself) give `ExtendsAway` and `NoInstOf`; the child's
boundary is supplied for every start world where `ChildBnd` holds, and the
child's run starts in one (`RealChild.bnd`). -/
namespace Tools.ShippingMachineDepthRun
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierMono
open Tools.ShippingMachineDepth Tools.ShippingMachineDepthChild
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCompose (argPorts machPorts_length)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingEntrySoundness (RunsTo)
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)

/-- `MachineRunN` with the child's run boundary in the run's contexts. -/
def MachineRunNC (c : Name) (shape : MachineShape) (Bnd : Tools.ShippingMachineShipsHier.CtxBnd)
    (mc : Module) (dsn : Design) : Prop :=
  ∃ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (raw : Module) (D : Design),
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w' ∧
    MachineDefines mctx mref cctx cref c shape ∧ MachineCloses mctx mref cctx cref c shape ∧
    Bnd mctx mref cctx cref w raw D ∧
    (mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
    ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules) ∧
    NoInstOf raw.name raw.body

theorem mergeChecked_name (m : Module) : (mergeChecked m).name = m.name := by
  rcases Sparkle.IR.RefineCheck.mergeChecked_cases m with h | h <;> rw [h]
  unfold Sparkle.IR.RegDedup.mergeDuplicates Sparkle.IR.RegDedup.mergeDuplicatesRaw
  dsimp only
  repeat' split
  all_goals rfl

/-- Mapping the modules of one name by a name-preserving `f` changes no lookup
of another name. -/
theorem moduleByName_map_other (N : String) (f : Module → Module) (hf : ∀ x, (f x).name = x.name) :
    ∀ (l : List Module) (y : String), y ≠ N →
      moduleByName (l.map fun x => if x.name == N then f x else x) y = moduleByName l y := by
  intro l y hy
  unfold moduleByName
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases hx : x.name = N
    · have h1 : (x.name == N) = true := by simp [hx]
      simp only [h1, if_true, hf]
      have h2 : (x.name == y) = false := by
        simp only [beq_eq_false_iff_ne]; intro h; exact hy (h ▸ hx)
      simp only [h2]
      exact ih
    · have h1 : (x.name == N) = false := by simp [hx]
      simp only [h1, Bool.false_eq_true, if_false]
      split <;> simp_all

/-- **The full entry's design, against the core run's.** Outside the top
module's name the two designs agree. -/
theorem synthesizeCombinational_design {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Module} {D' : Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        M' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      ∀ y, y ≠ M.name → moduleByName D'.modules y = moduleByName D.modules y := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  have hd := moduleByName_map_other M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule dropZW_name
  have hm := moduleByName_map_other M.name mergeChecked mergeChecked_name
  rcases RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    exact ⟨Or.inl rfl, fun y hy => hd D.modules y hy⟩
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    subst h1 h2
    refine ⟨Or.inr rfl, fun y hy => ?_⟩
    show moduleByName ((D.modules.map _).map _) y = _
    rw [hm _ y hy, hd _ y hy]

open Tools.ShippingMachineChild (boolsOf bitsOf sourceInputs_of_vals) in
/-- **A child with children of its own, at depth `n + 1`, from its composed
theorem at depth `n` and the hierarchical run boundary.** -/
theorem seqChildRunN_of_composedC (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (Bnd : Tools.ShippingMachineShipsHier.CtxBnd)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Module} {design : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref c d.shape → MachineCloses mctx mref cctx cref c d.shape →
      Bnd mctx mref cctx cref w m design → ComposedNW n c d kD m design dom src ext extB)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl : d.shape.layout.slots ≠ [])
    (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hextB : ∀ i bools bits j, j < kD → extB i bools bits j = bools j)
    (hext : ∀ i bools bits j n', j < kD → ext i bools bits j n' = bits j n')
    (i : ι) {mc : Module} {dsn : Design} (hrunN : MachineRunNC c d.shape Bnd mc dsn) :
    SeqChildRunN (childMap dsn.modules) dsn (n + 1) mc (d.bsIn.take kD) d.shape.layout.outs
      (fun vals => src i (boolsOf (d.bsIn.take kD) vals) (bitsOf (d.bsIn.take kD) vals)) := by
  obtain ⟨mctx, mref, cctx, cref, w, w', raw, D, hcore, entry, closes, hB, hpost, hEA, hNI⟩ := hrunN
  obtain ⟨ids, nd, len, cache, regs, _, _, lets, _, wired, H⟩ := composed hcore entry closes hB
  obtain ⟨hnd_in, hclk, hrst, hdisj, hargs, hslotNI⟩ :=
    calls_ports wired len hsl houtOk kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, -, regsIn, -, calls1, -, -, houts, -, -, -, -, gCalls, -, -, hcleanG, -, hW1⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hcleanG houtTy
  -- the core module has an instance, so the full entry kept it
  have hInst : Tools.ShippingMachineShipsHier.hasInst (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) := by
    by_cases hfe : d.shape.instFields = []
    · -- one-output combinational calls (`closeInsts`)
      obtain ⟨args, mc', st, _, hst, _, hcall⟩ := calls1 hfe 0 hI0
      obtain ⟨_, _, _, iname, _, _, _, _, _, _, _, _, _, heq⟩ := hcall
      subst heq
      exact ⟨_, _, _, by rw [hb]; exact hst⟩
    · obtain ⟨st, hst, args, outs, mc', hcall, _⟩ := gCalls hfe 0 hI0
      obtain ⟨_, _, iname, _, _, _, _, _, _, _, _, _, _, _, heq⟩ := hcall
      subst heq
      exact ⟨_, _, _, by rw [hb]; exact hst⟩
  have hmc : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · rw [h, mergeChecked_of_hasInst hInst]
  subst hmc
  have hargsMc : argPorts (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) = argPorts raw := by
    unfold argPorts; rw [hi]
  have hlenIn : (d.bsIn.take kD).length ≤ ids.length := by
    rw [len, d.binders_split]; simp; omega
  refine ⟨by rw [ho, houts], by rw [hi]; exact hnd_in, by rw [hi]; exact hclk,
    by rw [hi]; exact hrst, by rw [hi, ho]; exact hdisj, ?_, ?_⟩
  · rw [hargsMc, hargs, machPorts_length _ hlenIn]
  intro T ins s vals hrange hports hrstZ hclkZ hreset
  have hseed : seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ins = seedIn raw ins := by
    unfold seedIn; rw [hi]
  unfold ResetN at hreset
  obtain ⟨hregR, _, _, hkidR⟩ := hreset
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i (boolsOf (d.bsIn.take kD) vals)
    (bitsOf (d.bsIn.take kD) vals) T (seedIn raw ins) s.st s.mems s.kids
    (fun t st ht => by
      have hS := sourceInputs_of_vals nd hlenIn hargs (seedIn raw ins t st) (vals (T - 1 - t))
        (by
          rw [← hports t ht, hargsMc]
          apply List.map_congr_left
          intro p hp
          have hpi : p ∈ raw.inputs := (List.mem_filter.mp hp).1
          simp [seedIn, List.contains_eq_mem, List.mem_map_of_mem hpi])
        (hrange _ (by omega))
      refine Tools.ShippingMachineEntry.sourceInputs_congr nd ?_ ?_ hS
      · intro j hj
        have hjk : j < kD := by simp at hj; omega
        rw [hextB _ _ _ j hjk]; rfl
      · intro j hj n'
        have hjk : j < kD := by simp at hj; omega
        rw [hext _ _ _ j n' hjk]; rfl)
    (fun t st r hr => by
      have hnot := hslotNI r (regsIn r hr)
      simp [seedIn, List.contains_eq_mem, hnot])
    (fun t st => by simp [seedIn, List.contains_eq_mem, hrst, hrstZ])
    (fun t st => by simp [seedIn, List.contains_eq_mem, hclk, hclkZ])
    (fun k r f hr hf => by
      obtain ⟨rk, inp, hmem⟩ := hW1 k r f hr hf
      have := hregR r "clk" ("rst", rk) inp (Int.ofNat f.init) (by rw [hb]; exact hmem)
      simpa [stOf] using this)
    (fun iname mc' ⟨conns, hm⟩ hf => by
      have hc1 : childMap D.modules mc'.name = some (mc', Sparkle.IR.RegDedup.declWidth mc') :=
        childMap_some.mpr ⟨mc', hf, rfl⟩
      have hc2 := hEA.1 _ _ (hNI _ _ _ hm) hc1
      obtain ⟨x, hx, hxe⟩ := childMap_some.mp hc2
      have : x = mc' := by injection hxe with h; exact h.symm
      subst this
      exact resetN_away hEA n x (s.kids iname) (hEA.2 _ _ hc1)
        (hkidR x.name iname conns x (by rw [hb]; exact hm) hx))
  have hrun' := runModuleTG_mono_away (KSn_mono_away hEA n) hEA _ raw.body hNI _ T _ envs hrun
  refine ⟨envs, ?_, hlen, hobs⟩
  show runModuleTG (KSn (childMap dsn.modules) n)
    (Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (childMap dsn.modules)
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body
    (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ins) T s = some envs
  rw [hseed, hb]
  have hwe : Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) =
      Tools.ShippingEntrySoundness.weOf raw := hw
  rw [hwe]
  exact hrun'

theorem moduleByName_mem {ms : List Module} {nm : String} {mc : Module}
    (h : moduleByName ms nm = some mc) : mc ∈ ms := by
  unfold moduleByName at h
  exact List.mem_of_find?_eq_some h

/-- **The depth conditions from a run witness.** The module of a run of
`c`'s entry in the parent's contexts — one the parent's closing found, so
every module of its design resolves in the parent's design to itself — with
`c`'s reflection facts, `ChildBnd` and `c`'s boundary (a fact of the
contexts) satisfies `MachineRunNC`: the core run under it, its boundary, the
post-processing, `ExtendsAway` (from the parent's closing and the full
entry's changing only the top module) and `NoInstOf` (from `c`'s own
closing). -/
theorem machineRunNC_of_real {c : Name} {shape : MachineShape}
    {Bnd : Tools.ShippingMachineShipsHier.CtxBnd} {mc : Module} {Dc dsn : Design}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hreal : Tools.ShippingChildInv.RealChild mctx mref cctx cref c (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g)
    (entry : MachineDefines mctx mref cctx cref c shape)
    (closes : MachineCloses mctx mref cctx cref c shape)
    (hL : Tools.ShippingChildInv.ChildLaws mctx mref cctx cref) (hi : shape.insts ≠ [])
    (hB : ∀ w raw D, Tools.ShippingChildInv.ChildBnd mctx mref cctx cref w →
      Bnd mctx mref cctx cref w raw D) :
    MachineRunNC c shape Bnd mc dsn := by
  obtain ⟨w, w', hb, hrun⟩ := hreal.bnd hL
  obtain ⟨raw, D, w1, hcore, hpost, hagree⟩ := synthesizeCombinational_design hrun
  obtain ⟨t, t', d₀, children, _, hcc, _⟩ :=
    Tools.ShippingChildInv.machine_children_real hcore entry closes hb hi
  have acyc : NoInstOf raw.name raw.body ∧ ∀ g ∈ D.modules, NoInstOf raw.name g.body := by
    rcases hcc with ⟨_, h⟩ | ⟨_, h, _⟩
    · obtain ⟨_, h1, h2, _⟩ := Tools.ShippingChildServe.closeInsts_acyclic h
      exact ⟨h1, h2⟩
    · obtain ⟨_, h1, h2⟩ := Tools.ShippingChildServe.closeInstsG_acyclic h
      exact ⟨h1, h2⟩
  refine ⟨mctx, mref, cctx, cref, w, w1, raw, D, hcore, entry, closes, hB w raw D hb, hpost, ⟨?_, ?_⟩,
    acyc.1⟩
  · intro x r hx hD
    obtain ⟨g, hg, rfl⟩ := childMap_some.mp hD
    have hDc : moduleByName Dc.modules x = some g := by rw [hagree x hx]; exact hg
    have hn : g.name = x := Tools.ShippingMachineInst.moduleByName_name hg
    exact childMap_some.mpr ⟨g, by rw [← hn]; exact hcons g (moduleByName_mem hDc), rfl⟩
  · intro x r hD
    obtain ⟨g, hg, rfl⟩ := childMap_some.mp hD
    exact acyc.2 g (moduleByName_mem hg)

end Tools.ShippingMachineDepthRun
