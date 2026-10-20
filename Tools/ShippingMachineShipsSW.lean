import Tools.ShippingMachineShipsS

/-! # `MachineShipsSW`: the two-state leaf statement exporting its registers' wiring

BUILT by the integrator: sw1 exit 0 (325 jobs) (round par/leafsat, base ef5a26e3).

`Tools.ShippingMachineShipsS.MachineShipsS` exports of its existential `regs` only
`regs.Nodup ∧ regs.length = d.ss.length`. A user must discharge
`∀ t st r, r ∈ regs → seedIn raw ins t st r = st r` (no register is an input port) and
the slot registers' widths: impossible with `regs` opaque. The producer has the facts:
`machine_ships_wiredS` destructures `MachineTraceL` into `ids, cache, regs, lets,
wired : MachineWired …` and drops `wired`.

Here (the same move as Tools/ShippingComposedGW.lean on the instance route):

* `ShipsSBody`: the `∀`-part of `MachineShipsS` for FIXED `ids`, `cache`, `regs`;
* `MachineShipsSW declName d m0 dsn b o wof dom src`: `MachineShipsS` for
  `raw := dropZeroWidthModule m0`, whose existential ALSO exports
  `∃ lets, MachineWired declName d.shape ids cache m0 dsn regs lets` (the core module
  `m0` the entry's core run returned, and its design `dsn`); `MachineShipsSW.toS`
  forgets it;
* `shipsSBody_of_trace`: the proof of `machine_shipsS`, copied, for fixed
  `ids`/`cache`/`regs` (the trace's inner statement in, `ShipsSBody` out);
* `machine_ships_wiredSW`: `machine_ships_wiredS` with the strengthened conclusion,
  which also exports the core run `RunsTo (synthesizeCombinationalCore …) … (m0, dsn)`
  and the post step `b = drop m0 ∨ b = mergeChecked (drop m0)`. Same hypotheses;
  no hypothesis added.

No new fact about the compiler; nothing added to `RefLaws` or a trusted list.

Writing-time guesses (integrator: check these first):
* `MachineShipsSW.toS`: `exact ⟨…, H⟩` relies on `ShipsSBody` unfolding by defeq
  to the `∀`-part of `MachineShipsS`.
* `machine_ships_wiredSW`: the inner trace `H` of `MachineTraceL` is applied with
  `ext := fun _ _ bits => bits`, `extB := fun _ bools _ => bools`; its `SourceInputs`
  arguments are beta-redexes of the ones in `ShipsSBody` (accepted by `exact`?).
  The `rw [hw, hb]` on the run of `drop m0` (as in `machineTrace_congr`).
* the `wired` destructuring patterns copied from `machine_ships_wiredS`
  (12 components; `hclean` 11th; 9 components of `hclean hnoI houtTy`).
-/
namespace Tools.ShippingMachineShipsSW
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Tools.ShippingMachineShipsW Tools.ShippingMachineShipsS
open Sparkle.IR.RegDedup (declWidth)

/-- The `∀`-part of `MachineShipsS`, for fixed `ids`, `cache`, `regs`. -/
def ShipsSBody (declName : Name) (d : MachineData) (raw b o : Sparkle.IR.AST.Module)
    (wof : String → Option Nat) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String) : Prop :=
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
        (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
        (seedIn raw ins t st)) →
      (∀ t st r, r ∈ regs → seedIn raw ins t st r = st r) →
      (∀ t x, x ∈ raw.inputs.map (·.name) → ins t x < 2 ^ declWidth raw x) →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ t x, x ∈ raw.inputs.map (·.name) → ins t x < 2 ^ Tools.SVParser.EmitSem.weOf wof x) →
      (∀ t, ins t "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      (∀ r ∈ seqRegs raw, st0 r.1 < 2 ^ declWidth raw r.1) →
      (∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1) →
      (refineCheck b o = false → Bounded (Tools.SVParser.EmitSem.weOf wof) st0) →
      ∃ envsO,
        runModule (declWidth o) o.body (seedIn raw ins) T (tgtSt b o st0) mems = some envsO ∧
        (∃ pairs regs' mprog,
          Tools.SVParser.EmitSem.emitAssigns wof o.body = some pairs ∧
          Tools.SVParser.EmitSem.emitRegs wof o.body = some regs' ∧
          Tools.SVParser.EmitSem.emitMemWrites wof o.body = some mprog ∧
          Tools.SVParser.EmitSem.runModuleSV wof pairs regs' mprog
            (seedIn raw ins) T (tgtSt b o st0) mems = some envsO) ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
          (envsO[j]'hj) q.name = f j

/-- `MachineShipsS` for `raw := dropZeroWidthModule m0`, ALSO exporting the wiring of
the same `ids`, `cache`, `regs` (`MachineWired` of the core module `m0` in `dsn`). -/
def MachineShipsSW (declName : Name) (d : MachineData) (m0 : Sparkle.IR.AST.Module)
    (dsn : Sparkle.IR.AST.Design) (b o : Sparkle.IR.AST.Module)
    (wof : String → Option Nat) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
    (∃ lets : List String, MachineWired declName d.shape ids cache m0 dsn regs lets) ∧
    ShipsSBody declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule m0) b o wof dom src
      ids cache regs

/-- Forgetting the wiring. -/
theorem MachineShipsSW.toS {declName : Name} {d : MachineData} {m0 : Sparkle.IR.AST.Module}
    {dsn : Sparkle.IR.AST.Design} {b o : Sparkle.IR.AST.Module} {wof : String → Option Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (h : MachineShipsSW declName d m0 dsn b o wof dom src) :
    MachineShipsS declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule m0) b o wof dom src := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, -, H⟩ := h
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩

/-- The proof of `machine_shipsS`, copied, for FIXED `ids`, `cache`, `regs`: the trace's
inner statement (over `raw`) to `ShipsSBody`. -/
theorem shipsSBody_of_trace {declName : Name} {d : MachineData}
    {raw b o : Sparkle.IR.AST.Module} {wof : String → Option Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {regs : List String}
    (h : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
        (fun j => (bools j).val (T - 1 - t))
        (fun j n => (bits j n).val (T - 1 - t))
        (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ∃ envs, runModule (weOf raw) raw.body seed T st0 mems = some envs ∧ envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (q : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
          (envs[j]'hj) q.name = f j)
    (hmerge : refineCheck raw b = true ∨ b = raw) (hopt : refineCheck b o = true ∨ o = b)
    (hrstIn : "rst" ∈ raw.inputs.map (·.name))
    (houtP : ∀ q ∈ d.shape.layout.outs, ∃ p ∈ raw.outputs, p.name = q.name)
    (hrawOk : raw.body.all seqStmtOk = true)
    (hsv : Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwag : ((seqNames o.body).all fun n =>
      declWidth o n == Tools.SVParser.EmitSem.weOf wof n) = true) :
    ShipsSBody declName d raw b o wof dom src ids cache regs := by
  intro i bools bits T ins st0 mems inputs pass hinsRaw hinsB hinsW hrstZ init hfitRaw hfitB hstB
  have hrst : ∀ t st, seedIn raw ins t st "rst" = 0 := by
    intro t st
    simp only [seedIn]
    rw [if_pos (by simpa [List.contains_eq_mem] using hrstIn)]
    exact hrstZ t
  obtain ⟨envs, hrun, hlen, hobs⟩ := h i bools bits T (seedIn raw ins) st0 mems inputs pass hrst
    init
  have hrun' : runModule (declWidth raw) raw.body (seedIn raw ins) T st0 mems = some envs :=
    hrun
  have stepB : b.inputs = raw.inputs ∧ b.outputs = raw.outputs ∧ ∃ envsB,
      runModule (declWidth b) b.body (seedIn raw ins) T st0 mems = some envsB ∧
      envsB.length = envs.length ∧
      ∀ p ∈ raw.outputs, ∀ j (hj : j < envsB.length) (hj' : j < envs.length),
        (envsB[j]'hj) p.name = (envs[j]'hj') p.name := by
    rcases hmerge with hmerge | rfl
    · obtain ⟨hinB, houtB⟩ := refineCheck_ports hmerge
      exact ⟨hinB, houtB, refineCheck_transfer hmerge ins hinsRaw hrstIn hrstZ (stO := st0)
        (fun _ _ => rfl) hfitRaw hrun'⟩
    · exact ⟨rfl, rfl, envs, hrun', rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨hinB, houtB, envsB, hrunB, hlenB, hcorrB⟩ := stepB
  have hseed : seedIn b ins = seedIn raw ins := seedIn_of_inputs hinB ins
  have hrstInB : "rst" ∈ b.inputs.map (·.name) := by rw [hinB]; exact hrstIn
  have hok : o.body.all seqStmtOk = true := by
    rcases hopt with hopt | rfl
    · exact refineCheck_stmtOk_o hopt
    · rcases hmerge with hmerge | rfl
      · exact refineCheck_stmtOk_o hmerge
      · exact hrawOk
  have hwag' : ∀ n ∈ seqNames o.body,
      declWidth o n = Tools.SVParser.EmitSem.weOf wof n := by
    intro n hn
    have := List.all_eq_true.mp hwag n hn
    simpa using this
  have stepO : ∃ envsO,
      runModule (declWidth o) o.body (seedIn raw ins) T (tgtSt b o st0) mems = some envsO ∧
      envsO.length = envsB.length ∧
      ∀ p ∈ b.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envsB.length),
        (envsO[j]'hj) p.name = (envsB[j]'hj') p.name := by
    cases hc : refineCheck b o with
    | true =>
      rw [← hseed] at hrunB
      obtain ⟨envsO, hrunO, hlenO, hcorrO⟩ :=
        refineCheck_transfer hc ins hinsB hrstInB hrstZ (stO := tgtSt b o st0)
          (tgtSt_agree b o st0) hfitB hrunB
      rw [hseed] at hrunO
      exact ⟨envsO, hrunO, hlenO, hcorrO⟩
    | false =>
      have hob : o = b := by
        rcases hopt with h' | h'
        · rw [hc] at h'; cases h'
        · exact h'
      rw [tgtSt_of_false st0 hc, hob]
      exact ⟨envsB, hrunB, rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨envsO, hrunO, hlenO, hcorrO⟩ := stepO
  have hstO : Bounded (Tools.SVParser.EmitSem.weOf wof) (tgtSt b o st0) := by
    cases hc : refineCheck b o with
    | true => exact tgtSt_bounded hc hfitB hwag'
    | false => rw [tgtSt_of_false st0 hc]; exact hstB hc
  have hSV := seq_run_to_sv hok hsv hwag' (seedIn raw ins) (seedIn_bounded hinsW) hstO hrunO
  refine ⟨envsO, hrunO, hSV, by omega, ?_⟩
  intro j hj k q f hq hf
  obtain ⟨p, hp, hpname⟩ := houtP q (List.mem_of_getElem? hq)
  have h1 := hcorrO p (by rw [houtB]; exact hp) j hj (by omega)
  have h2 := hcorrB p hp j (by omega) (by omega)
  rw [hpname] at h1 h2
  rw [h1, h2]
  exact hobs j (by omega) k q f hq hf

/-- **`machine_ships_wiredS` exporting the wiring and the core run.** Same hypotheses as
`Tools.ShippingMachineShipsS.machine_ships_wiredS`; the conclusion also names the core
module `m0` and design `dsn` of the entry's core run, and `MachineShipsSW` exports
`MachineWired` of `m0` for the same `ids`, `cache`, `regs`. -/
theorem machine_ships_wiredSW {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ (raw : Sparkle.IR.AST.Module) (dsn : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (raw, dsn) w1 ∧
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        simpleBody b = false →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShipsSW declName d raw dsn b (checkedOptimize b) wof dom src := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  have hL := soundL hcore entry closes
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, _, wired, H⟩ := hL
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := id wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, _, _, _, _, _, hok⟩ := hclean hnoI houtTy
  refine ⟨raw, D, w1, hcore, hpost, ?_⟩
  intro wof hsB hsv hwag
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ⟨lets, wired⟩, ?_⟩
  have Hr0 : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
        (fun j => (bools j).val (T - 1 - t))
        (fun j n => (bits j n).val (T - 1 - t))
        (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ∃ envs, runModule (weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
          (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body seed T st0 mems = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (q : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
          (envs[j]'hj) q.name = f j := by
    intro i bools bits T seed st0 mems a b' c e
    rw [hb, hw]
    obtain ⟨envs, hrun, hlen, hobs, _⟩ := H i bools bits T seed st0 mems a b' c e
    exact ⟨envs, hrun, hlen, hobs⟩
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost Hr0 ⊢
  obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons f _ => exact ⟨f, rfl⟩
  obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
    cases hrs : regs with
    | nil =>
      have : d.shape.layout.slots.length = 0 := by
        rw [← hSS, ← rlen, hrs]; rfl
      rw [List.length_eq_zero_iff] at this; exact absurd this hsl
    | cons r _ => exact ⟨r, rfl⟩
  obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
  have hnA : r0.body.all Sparkle.IR.RegDedup.isAssign = false := by
    apply List.all_eq_false.mpr
    exact ⟨_, hb ▸ hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
  have hr0ok : r0.body.all seqStmtOk = true := by rw [hb]; exact hok
  have hmerge : refineCheck r0 b = true ∨ b = r0 := by
    rcases hpost with rfl | rfl
    · exact Or.inr rfl
    · exact mergeChecked_nonAssign hnA
  have hbok : b.body.all seqStmtOk = true := by
    rcases hmerge with h | rfl
    · exact refineCheck_stmtOk_o h
    · exact hr0ok
  exact shipsSBody_of_trace Hr0 hmerge (checkedOptimize_seqOk hsB hbok)
    (by rw [hi]; exact hrstIn hsl)
    (fun q hq => ⟨⟨q.name, q.ty⟩, by rw [ho, houts]; exact List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩)
    hr0ok hsv hwag

end Tools.ShippingMachineShipsSW
