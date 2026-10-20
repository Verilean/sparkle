import Tools.ShippingMachineShipsW

/-! # A leaf state machine to its emitted Verilog, with a SEPARATE target start state

BUILT by the integrator: lf1 exit 1 (ambiguous `Expr` at :78, :90 -> `Sparkle.IR.AST.Expr`), lf2 exit 0 for this file; axioms standard (ax5) (round par/leafnz, base aa35e8a6).

`MachineShips` (Tools/ShippingMachineShipping.lean:63) runs the source modules
(`raw`, `b`) AND the optimized module `o` with its emitted Verilog from ONE start
state `st0`, and asks `Bounded (weOf wof) st0` over every name. When the optimizer
removes a register `r` with a nonzero reset value, the emitter's width map gives
`weOf wof r = 0`, so that bound contradicts `st0 r = f.init ≠ 0`: the statement is
vacuous for such a machine (docs/parallel/leaf-nonzero-init.md §2).

Here the optimized module runs from the TARGET state `tgtSt b o st0`: the source
state cleared on every name that the accepted optimized module does not keep as a
register. The optimizer step already allows two states (`refineCheck_transfer`,
Tools/ShippingRefineSoundness.lean:1039, agreement on `seqRegs o` only); the bound
on the target state now follows from the source register fits and the emitted width
agreement (`tgtSt_bounded`), and `Bounded (weOf wof) st0` is asked only when the
optimizer's output was rejected (`o = b`, nothing removed).

Writing-time guesses (integrator: check these first):
* `seqRegs_mem_seqNames`: `cases st with | register .. | _` catch-all and the
  `first` alternatives reducing the `filterMap` match.
* `refineCheck_regWidth`: the 12-tuple destructuring copied from
  `refineCheck_step_sound` (:709-725); `hf.1.2` is the width conjunct there.
* `tgtSt_of_false` / `tgtSt_agree`: `if_neg` with the `∧` condition (`decide`
  instance of `refineCheck b o = true ∧ n ∉ _`).
* `machine_shipsS`: `subst hob` direction in the rejected branch.
-/
namespace Tools.ShippingMachineShipsS
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Tools.ShippingMachineShipsW
open Sparkle.IR.RegDedup (declWidth)

/-- The target start state: the source state `st0`, cleared (to `0`) on every name
that is not a register of the ACCEPTED optimized module `o`. When the optimizer's
output was rejected (`refineCheck b o = false`) it is `st0`. -/
def tgtSt (b o : Sparkle.IR.AST.Module) (st0 : String → Nat) (n : String) : Nat :=
  if refineCheck b o = true ∧ n ∉ (seqRegs o).map (·.1) then 0 else st0 n

/-- **The source/target correspondence**: on every register the optimized module
keeps, the target state is the source state. -/
theorem tgtSt_agree (b o : Sparkle.IR.AST.Module) (st0 : String → Nat) :
    ∀ r ∈ seqRegs o, tgtSt b o st0 r.1 = st0 r.1 := by
  intro r hr
  unfold tgtSt
  rw [if_neg]
  intro h
  exact h.2 (List.mem_map_of_mem (f := (·.1)) hr)

/-- Off the kept registers, after an accepted optimization, the target state is `0`. -/
theorem tgtSt_removed {b o : Sparkle.IR.AST.Module} (st0 : String → Nat)
    (hc : refineCheck b o = true) {n : String} (hn : n ∉ (seqRegs o).map (·.1)) :
    tgtSt b o st0 n = 0 := by
  unfold tgtSt
  rw [if_pos ⟨hc, hn⟩]

/-- A rejected optimization keeps the source state. -/
theorem tgtSt_of_false {b o : Sparkle.IR.AST.Module} (st0 : String → Nat)
    (hc : refineCheck b o = false) : tgtSt b o st0 = st0 := by
  funext n
  unfold tgtSt
  rw [if_neg]
  intro h
  have h1 := h.1
  rw [hc] at h1
  exact Bool.false_ne_true h1

/-- A register statement's target is in `seqNames`. -/
theorem mem_seqNames_of_reg : ∀ {body : List Stmt} {o c : String}
    {rk : String × Sparkle.IR.Type.ResetKind} {i : Sparkle.IR.AST.Expr} {iv : Int},
    Stmt.register o c rk i iv ∈ body → o ∈ seqNames body
  | [], _, _, _, _, _, h => by cases h
  | st :: rest, o, c, rk, i, iv, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h
      simp [seqNames]
    · have ih : o ∈ seqNames rest := mem_seqNames_of_reg h
      cases st <;> simp [seqNames, ih]

/-- Registers of a module are in its `seqNames`. -/
theorem seqRegs_mem_seqNames {o : Sparkle.IR.AST.Module}
    {r : String × String × (String × Sparkle.IR.Type.ResetKind) × Sparkle.IR.AST.Expr × Int}
    (hr : r ∈ seqRegs o) : r.1 ∈ seqNames o.body := by
  unfold seqRegs at hr
  obtain ⟨st, hst, hf⟩ := List.mem_filterMap.mp hr
  cases st with
  | register o' c rk i iv =>
    have he : (o', c, rk, i, iv) = r := by
      first
        | exact Option.some.inj hf
        | (simp only [Option.some.injEq] at hf; exact hf)
        | (injection hf)
    subst he
    exact mem_seqNames_of_reg hst
  | _ => first | cases hf | simp at hf | exact absurd hf (by simp)

/-- `refineCheck` keeps the width of every register it keeps. -/
theorem refineCheck_regWidth {m o : Sparkle.IR.AST.Module} (h : refineCheck m o = true) :
    ∀ ro ∈ seqRegs o, ∃ rm ∈ seqRegs m, rm.1 = ro.1 ∧ declWidth m rm.1 = declWidth o ro.1 := by
  simp only [refineCheck] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hpairs⟩, _⟩ := h1
  intro ro hro
  have hf := List.all_eq_true.mp hpairs ro hro
  cases hrm : regOf (seqRegs m) ro.1 with
  | none => rw [hrm] at hf; cases hf
  | some rm =>
    rw [hrm] at hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
    obtain ⟨hmem, hname⟩ := regOf_some hrm
    exact ⟨rm, hmem, hname, hf.1.2⟩

/-- **The target state is bounded by the emitted widths** — from the source fits on
the registers of `b` and the width agreement of the emitted module on its own names;
no bound on `st0` outside the kept registers is needed. -/
theorem tgtSt_bounded {b o : Sparkle.IR.AST.Module} {wof : String → Option Nat}
    {st0 : String → Nat} (hc : refineCheck b o = true)
    (hfitB : ∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1)
    (hwag : ∀ n ∈ seqNames o.body, declWidth o n = Tools.SVParser.EmitSem.weOf wof n) :
    Bounded (Tools.SVParser.EmitSem.weOf wof) (tgtSt b o st0) := by
  intro n
  by_cases hn : n ∈ (seqRegs o).map (·.1)
  · obtain ⟨ro, hro, hro1⟩ := List.mem_map.mp hn
    subst hro1
    rw [tgtSt_agree b o st0 ro hro]
    obtain ⟨rm, hrm, hname, hw⟩ := refineCheck_regWidth hc ro hro
    rw [← hwag ro.1 (seqRegs_mem_seqNames hro), ← hw, ← hname]
    exact hfitB rm hrm
  · rw [tgtSt_removed st0 hc hn]
    exact Nat.two_pow_pos _

/-- **What the shipped leaf module shows, from a target start state.** As
`MachineShips`, except: the optimized module `o` and its emitted Verilog run from
`tgtSt b o st0` (the source state on the registers `o` keeps), and the all-names
bound on `st0` is asked only when the optimizer's output was rejected. -/
def MachineShipsS (declName : Name) (d : MachineData) (raw b o : Sparkle.IR.AST.Module)
    (wof : String → Option Nat) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
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

/-- **A machine trace, to the optimized module and its emitted Verilog, from the
target start state.** Proof of `machine_ships` with the optimizer step taken from
`tgtSt b o st0` (`refineCheck_transfer`'s two-state form). -/
theorem machine_shipsS {declName : Name} {d : MachineData}
    {raw b o : Sparkle.IR.AST.Module} {wof : String → Option Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (htrace : MachineTrace declName d raw dom src)
    (hmerge : refineCheck raw b = true ∨ b = raw) (hopt : refineCheck b o = true ∨ o = b)
    (hrstIn : "rst" ∈ raw.inputs.map (·.name))
    (houtP : ∀ q ∈ d.shape.layout.outs, ∃ p ∈ raw.outputs, p.name = q.name)
    (hrawOk : raw.body.all seqStmtOk = true)
    (hsv : Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwag : ((seqNames o.body).all fun n =>
      declWidth o n == Tools.SVParser.EmitSem.weOf wof n) = true) :
    MachineShipsS declName d raw b o wof dom src := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, h⟩ := htrace
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
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

/-- **A leaf state machine at the full entry, to the emitted Verilog, from its
wiring — the optimized module from the target start state.** Proof of
`machine_ships_wired`, ending in `machine_shipsS`. -/
theorem machine_ships_wiredS {declName : Name} (d : MachineData)
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
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        simpleBody b = false →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShipsS declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
          (checkedOptimize b) wof dom src := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  have hL := soundL hcore entry closes
  obtain ⟨_, _, _, _, regs, _, rlen, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, _, _, _, _, _, hok⟩ := hclean hnoI houtTy
  refine ⟨raw, hpost, ?_⟩
  intro wof hsB hsv hwag
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost ⊢
  have htrace : MachineTrace declName d r0 dom src :=
    machineTrace_congr hb hw (MachineTraceL.toWith hL)
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
  exact machine_shipsS htrace hmerge (checkedOptimize_seqOk hsB hbok)
    (by rw [hi]; exact hrstIn hsl)
    (fun q hq => ⟨⟨q.name, q.ty⟩, by rw [ho, houts]; exact List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩)
    hr0ok hsv hwag

end Tools.ShippingMachineShipsS
