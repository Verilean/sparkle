import Tools.ShippingMachineDepthChild
import Tools.ShippingMachineCallsLinkedTN
import Tools.ShippingHierMono
import Tools.ShippingMachineShipsHier

/-! # A child with children of its own, from its composed theorem

`SeqChildRunN (n + 1)` says that a child module, run at depth `n + 1` (its
own instances one level down) from reset, shows its source. For a child that
itself calls sequential children, it follows from the child's own composed
theorem at depth `n` (`machine_linkedT_callsN`, carrying the child's wiring
for the same ports): the module the parent instantiates is the child's core
module after the full entry's post-processing (the identity on an
instance-bearing body), its ports are the declaration's (`calls_ports`),
and its run carries from the child's own design to the parent's
(`KSn_mono_away`: the designs agree away from the child's own name, which
no module instantiates). That correspondence is the hierarchical run
boundary `MachineRunN`. -/
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

/-- The composed theorem at depth `n`, with the module's wiring. -/
def ComposedNW (n : Nat) (declName : Name) (d : MachineData) (kD : Nat) (m : Module) (dsn : Design)
    {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
    ∃ lets : List String, lets.length = d.letBs.length ∧
    MachineWired declName d.shape ids cache m dsn regs lets ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
      (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t))
        (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      (∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
        moduleByName dsn.modules mc.name = some mc → ResetN dsn n mc (kids iname)) →
      ∃ envs, runModuleTG (KSn (childMap dsn.modules) n) (Tools.ShippingEntrySoundness.weOf m)
          (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j

/-- **The hierarchical run boundary.** The module an instance of a call of
`c` resolves to in the parent's design `dsn` is the full entry's
post-processing of a core run of `c` whose design `dsn` extends away from
`c`'s own name, which neither that design nor the module instantiates. -/
def MachineRunN (c : Name) (shape : MachineShape) (Bnd : Module → Design → Prop) (mc : Module)
    (dsn : Design) : Prop :=
  ∃ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (raw : Module) (D : Design),
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w' ∧
    MachineDefines mctx mref cctx cref c shape ∧ MachineCloses mctx mref cctx cref c shape ∧
    Bnd raw D ∧
    (mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
    ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules) ∧
    NoInstOf raw.name raw.body

/-- The checked merge keeps a module with an instance. -/
theorem mergeChecked_of_hasInst {r : Module} (h : Tools.ShippingMachineShipsHier.hasInst r) :
    mergeChecked r = r := by
  unfold mergeChecked
  dsimp only
  rw [if_neg (by rw [Tools.ShippingMachineShipsHier.not_all_assign h]; simp)]
  split
  · rename_i hrc
    have := Tools.ShippingMachineShipping.refineCheck_stmtOk_m hrc
    rw [Tools.ShippingMachineShipsHier.not_all_seqOk h] at this
    cases this
  · rfl

theorem dropZW_name (m : Module) : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).name = m.name := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule; split <;> rfl

theorem childMap_some {ms : List Module} {mn : String} {r : Module × WEnv} :
    childMap ms mn = some r ↔ ∃ x, moduleByName ms mn = some x ∧ r = (x, Sparkle.IR.RegDedup.declWidth x) := by
  unfold childMap
  cases h : moduleByName ms mn with
  | none => simp
  | some x => simp [eq_comm]

/-- **The reset state carries to a design agreeing away from `t`.** -/
theorem resetN_away {t : String} {D₁ D₂ : Design}
    (hEA : ExtendsAway t (childMap D₁.modules) (childMap D₂.modules)) :
    ∀ (n : Nat) (mc : Module) (s : KT n), NoInstOf t mc.body → ResetN D₂ n mc s → ResetN D₁ n mc s
  | 0, mc, s, _, h => by
    unfold ResetN at h ⊢
    exact h
  | k + 1, mc, s, hn, h => by
    unfold ResetN at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, h3, ?_⟩
    intro mn iname conns mc' hm hf
    have hmn : mn ≠ t := hn mn iname conns hm
    have hc1 : childMap D₁.modules mn = some (mc', Sparkle.IR.RegDedup.declWidth mc') :=
      childMap_some.mpr ⟨mc', hf, rfl⟩
    have hc2 := hEA.1 mn _ hmn hc1
    obtain ⟨x, hx, hxe⟩ := childMap_some.mp hc2
    have : x = mc' := by injection hxe with h; exact h.symm
    subst this
    exact resetN_away hEA k x (KState.kids s iname) (hEA.2 mn _ hc1) (h4 mn iname conns x hm hx)

open Tools.ShippingMachineChild (boolsOf bitsOf sourceInputs_of_vals) in
/-- **A child with children of its own, at depth `n + 1`, from its composed
theorem at depth `n` and the hierarchical run boundary.** -/
theorem seqChildRunN_of_composed (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (Bnd : Module → Design → Prop)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Module} {design : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref c d.shape → MachineCloses mctx mref cctx cref c d.shape →
      Bnd m design → ComposedNW n c d kD m design dom src ext extB)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hfe : d.shape.instFields ≠ []) (hsl : d.shape.layout.slots ≠ [])
    (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hextB : ∀ i bools bits j, j < kD → extB i bools bits j = bools j)
    (hext : ∀ i bools bits j n', j < kD → ext i bools bits j n' = bits j n')
    (i : ι) {mc : Module} {dsn : Design} (hrunN : MachineRunN c d.shape Bnd mc dsn) :
    SeqChildRunN (childMap dsn.modules) dsn (n + 1) mc (d.bsIn.take kD) d.shape.layout.outs
      (fun vals => src i (boolsOf (d.bsIn.take kD) vals) (bitsOf (d.bsIn.take kD) vals)) := by
  obtain ⟨mctx, mref, cctx, cref, w, w', raw, D, hcore, entry, closes, hB, hpost, hEA, hNI⟩ := hrunN
  obtain ⟨ids, nd, len, cache, regs, _, _, lets, _, wired, H⟩ := composed hcore entry closes hB
  obtain ⟨hnd_in, hclk, hrst, hdisj, hargs, hslotNI⟩ :=
    calls_ports wired len hfe hsl houtOk kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, -, regsIn, -, -, -, -, houts, -, -, -, -, gCalls, -, -, hcleanG, -, hW1⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hcleanG houtTy
  -- the core module has an instance, so the full entry kept it
  have hInst : Tools.ShippingMachineShipsHier.hasInst (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) := by
    obtain ⟨st, hst, args, outs, mc', hcall, _⟩ := gCalls hfe 0 hI0
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

end Tools.ShippingMachineDepthRun
