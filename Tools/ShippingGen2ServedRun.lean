import Tools.ShippingGen2KeepChild
import Tools.ShippingChildRunAKids
set_option autoImplicit false
-- NOT BUILT (written by reading at 96cbd548; scripts/gen2/SERVED_FREEZE.md rev1 §1.3, §1.5). Every proof is a
-- substitution copy of a BUILT source, named at each declaration. No `sorry`, no `axiom`, no `native_decide`.

/-! # G-SERVED F1: the run level at `InvAt` (canonical, D3; imported by G-POST)

The `JQC`-chain of the served-real producer (Tools/ShippingChildRunA.lean, Tools/ShippingChildRunAKids.lean,
Tools/ShippingChildCacheA.lean) re-stated at `InvAt L P Reach` (`JQC ∧ CacheShips`), with each child's value from
`synthesizeChild_shipsRes` (Tools/ShippingGen2KeepChild.lean:331) and its end world from `ChildKeepsInv`. No
`BodyStepC`, no `hrow`: nothing here is conditional on the G-ONEOUT-REACH row.

* `cacheShips_empty`, `tripleInv_clear`: the depth-0 clear gives `InvAt` from `JQ`.
* `core_reads_invAt0` (G-START form: `JQC D ∧ (D = 0 ∨ CacheShips)`), `synthesizeFromConst_machine_invAt`,
  `machineRunInv_of_core0`, `machineRunInv_of_coreA` (GPOST P1), `MachineRunInv`, `machineRunInv_of_closes0`.
* `synthesizeChild_ships`, `ChildrenShipsI` (GPOST P2 text), `closeInstsM_ships`, `closeInstsGM_ships`,
  `synthesizeMachineCertified_runsS` (GPOST P2 `…_runsInv`).

`RealChildA` is a history of past synthesis results; `InvAt` is not freshness. Not runtime fit. -/

namespace Tools.ShippingGen2
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFrontCP
open Tools.ShippingChildFresh
open Tools.ShippingChildCacheA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildDepthC
open Tools.ShippingChildCoreC
open Tools.ShippingChildComposeC
open Tools.ShippingChildVertA
open Tools.ShippingChildRunA
open Tools.ShippingChildRunAKids

/-! ## 1. The depth-0 clear -/

/-- The empty cache ships (every lookup misses). -/
theorem cacheShips_empty {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) :
    CacheShips L P Reach ({} : Std.HashMap Name Res) := by
  intro c r _ h
  first
    | simp at h
    | (rw [Std.HashMap.get?_empty] at h; cases h)

/-- The depth-0 clear establishes `InvAt` from `JQ` (copy of `tripleC_clear`, ChildCacheA.lean:218; both cache
halves of the cleared value hold). -/
theorem tripleInv_clear {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ L.O.quiet D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => InvAt L P Reach D) R :=
  Triple.of_runs (refSet_runs _ _) fun w u w' hw h => by
    have hk := L.O.cacheSet hA _ _ _ _ h hw.1
    refine ⟨⟨⟨L.O.cacheSetQ hA _ _ _ _ h hw.1, hk.2.1.trans hw.2.1, hk.2.2.trans hw.2.2⟩, ?_⟩, ?_⟩
    · rw [hk.1]; exact cacheInvA_empty L.O
    · rw [hk.1]
      first
        | exact cacheShips_empty L P Reach
        | (intro c r _ h'; simp at h')

/-! ## 2. The core entry's prefix at `InvAt` (G-START) -/

/-- **The entry's prefix establishes `InvAt` at the body's start** (copy of `core_reads_invA`,
ChildRunA.lean:89-198). Start: `JQC D` and the cache disjunct `D = 0 ∨ CacheShips` (G-START: the outermost start
gives only `JQC 0`). At `D = 0` the clear establishes both cache halves (`tripleInv_clear`); nested, `InvAt D` is the
stable invariant of the whole walk. -/
theorem core_reads_invAt0 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {D : Nat} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module}
    {Dg : Sparkle.IR.AST.Design}
    (hw : JQC L.O D w) (hc : D = 0 ∨ CacheShips L P Reach (cv w))
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, Dg) w') :
    ∃ (b : Bool) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO b)
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, Dg) w4 ∧ InvAt L P Reach (D + 1) w3 := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases h0 : D = 0
  · -- outermost: the clear establishes both cache halves
    subst h0
    replace hw := hw.1
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_JQ _ 0) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag L.O hA (stableA_JQ _ 0)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet L.O hA (stableA_JQ _ 0)) hw s3
    have hdD : d = 0 := hd.2.trans hd.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    simp only [↓reduceIte, beq_self_eq_true] at h
    peelP h; peelP h; peelP h; peelP h; peelP h; peelP h; peelP h
    peelF L.O hA (stableA_JQ _ 0) h hw; peelF L.O hA (stableA_JQ _ 0) h hw
    peelF L.O hA (stableA_JQ _ 0) h hw; peelF L.O hA (stableA_JQ _ 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleInv_clear L P Reach hA 0 (R := fun _ _ => False)) hw step
    clear step
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw; peelF L.O hA (stableA_invAt L P Reach 0) h hw
    peelF L.O hA (stableA_invAt L P Reach 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleInv_depthSet L P Reach hA 0 (0 + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (0 + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (0 + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, hw⟩
  · -- nested: `InvAt D` throughout
    replace hw : InvAt L P Reach D w := ⟨hw, hc.resolve_left h0⟩
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach D)
      (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag L.O hA (stableA_invAt L P Reach D)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet L.O hA (stableA_invAt L P Reach D)) hw s3
    have hdD : d = D := hd.2.trans hd.1.1.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    have h0' : ¬ ((d == 0) = true) := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw; peelF L.O hA (stableA_invAt L P Reach d) h hw
    peelF L.O hA (stableA_invAt L P Reach d) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleInv_depthSet L P Reach hA d (d + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (d + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach (d + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, hw⟩

/-- `synthesizeFromConst_machine_invA` (ChildRunA.lean:200-235) at `InvAt` (`getEnv` is framed). -/
theorem synthesizeFromConst_machine_invAt {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {tenv : Lean.Environment}
    {logProf : String → IO Unit} {declName : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : InvAt L P Reach n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) logProf
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w7 w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
            shape) mctx mref cctx cref w7 r w8 ∧ InvAt L P Reach n w7 ∧
          ∀ res, r = some res → res = (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (keepsA_framed L.O hA (stableA_invAt L P Reach n)
    FramedA.env)) hw henv
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  refine ⟨envR, _, _, henv, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  refine ⟨r, _, _, hmach, hw1, ?_⟩
  intro res hres
  subst hres
  dsimp only at hr
  have hr := hr.mreturns
  peel_bind hr
  peel_bind hr
  exact (MReturns.pure hr).symm

/-- **The machine synthesis inside a real core run, at `InvAt`** (copy of `machine_run_of_coreA`, ChildRunA.lean:241;
G-START premise). -/
theorem machineRunInv_of_core0 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (hw : JQC L.O D w) (hc : D = 0 ∨ CacheShips L P Reach (cv w)) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
        mctx mref cctx cref w9 r w10 ∧ InvAt L P Reach (D + 1) w9 ∧
      ∀ res, r = some res → res = (m, d) := by
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run, hw3⟩ :=
    core_reads_invAt0 L P Reach hA hw hc hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine_invAt L P Reach hA old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hw9, hres⟩ := hmach shape hshape
  exact ⟨_, b, r, w9, w10, hrun, hw9, hres⟩

/-- **GPOST P1** (scripts/gen2/GPOST_FREEZE.md §5 P1 text): the `InvAt` form, by `Or.inr hw.2`. -/
theorem machineRunInv_of_coreA {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {c : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref c shape)
    (hw : InvAt L P Reach D w) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
        mctx mref cctx cref w9 r w10 ∧ InvAt L P Reach (D + 1) w9 ∧
      ∀ res, r = some res → res = (m, d) :=
  machineRunInv_of_core0 L P Reach hA hr entry hw.1 (Or.inr hw.2)

/-! ## 3. Route evidence at `InvAt` -/

/-- `MachineRunJQC` (ServedRealA.lean:90) with `JQC O n` replaced by `InvAt L P Reach n` (frozen text, rev1 §1.5). -/
def MachineRunInv {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (mctx : Meta.Context)
    (cctx : Core.Context) (n : Nat) (c : Name) (shape : MachineShape) (M : Sparkle.IR.AST.Module)
    (D : Sparkle.IR.AST.Design) : Prop :=
  ∃ (tenv : Lean.Environment), ∃ (b : Bool) (w9 w10 : Void IO.RealWorld),
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
      mctx mref cctx cref w9 (some (M, D)) w10 ∧ InvAt L P Reach n w9

/-- `MachineRunInv` projects to `MachineRunJQC` (the `JQC` half of `InvAt`). -/
theorem machineRunJQC_of_runInv {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {mctx : Meta.Context}
    {cctx : Core.Context} {n : Nat} {c : Name} {shape : MachineShape} {M : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design} (h : MachineRunInv L P Reach mctx cctx n c shape M D) :
    Tools.ShippingServedRealA.MachineRunJQC L.O mctx cctx n c shape M D := by
  obtain ⟨tenv, b, w9, w10, hrun, hw9⟩ := h
  exact ⟨tenv, b, w9, w10, hrun, hw9.1⟩

/-- **`MachineRunInv` from a returning core run** (copy of `machineRunJQC_of_closesA`, ServedRealA.lean:97). -/
theorem machineRunInv_of_closes0 {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineClosesAtA L.O mctx cctx declName shape)
    (hw : JQC L.O D w) (hc : D = 0 ∨ CacheShips L P Reach (cv w)) :
    MachineRunInv L P Reach mctx cctx (D + 1) declName shape m d := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machineRunInv_of_core0 L P Reach hA hr entry hw hc
  have hne := closes b (D + 1) w9 r w10 hw9.1 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact ⟨tenv, b, w9, w10, hrun, hw9⟩

/-! ## 4. The children at `InvAt` -/

/-- **One child, returning run** (freeze (d)): the value is a `RealChildA` (hit: the read world's `JQC` cache half;
miss: `RealChildA.of_jqc` at the pre-entry world) that ships if the name is reached (`synthesizeChild_shipsRes`,
KeepChild.lean:331), and the end world is `InvAt D` (`ChildKeepsInv D`). No `BodyStepC`. -/
theorem synthesizeChild_ships {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res}
    (hw : InvAt L P Reach D w) (hIH : IHAt L P Reach D) (hKI : ChildKeepsInv L P Reach D)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') :
    RealChildA L.O n r ∧ (Reach n → ShipsRes L P n r) ∧ InvAt L P Reach D w' := by
  refine ⟨?_, synthesizeChild_shipsRes L P Reach hA hw hIH h, ?_⟩
  · have h' := h
    unfold synthesizeChild at h'
    obtain ⟨m, w1, hget, h'⟩ := RunsTo.bind h'
    have hw1 : InvAt L P Reach D w1 ∧ m = cv w1 :=
      runs_of_triple (tripleInv_cacheGet L P Reach hA D) hw hget
    cases hc : m.get? n with
    | some y =>
      simp only [hc] at h'
      obtain ⟨hy, -⟩ := RunsTo.pure_world h'
      rw [hy]
      exact hw1.1.1.2 n y (by rw [← hw1.2]; exact hc)
    | none =>
      simp only [hc] at h'
      obtain ⟨r1, w2, hrun, h'⟩ := RunsTo.bind h'
      obtain ⟨u, w3, -, h'⟩ := RunsTo.bind h'
      obtain ⟨hy, -⟩ := RunsTo.pure_world h'
      rw [hy]
      exact RealChildA.of_jqc L.O hA hw1.1.1 hrun
  · have hK : Tools.ShippingChildFrontCP.ChildSynthA L.O (InvAt L P Reach D) := hKI
    have hk := (hK mctx cctx hA n w hw).1
    rw [endW_of_runs h] at hk
    exact hk

/-- **GPOST P2's children predicate** (GPOST_FREEZE.md §5 P2 text, verbatim; frozen rev1 §1.5). -/
def ChildrenShipsI {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (shape : MachineShape)
    (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → ShipsRes L P (shape.insts[k]).1 y)))

/-- **The one-output closing's children at `InvAt`** (copy of `closeInstsM_realA`, ChildCacheA.lean:420, with
`synthesizeChild_ships`). The synthesis-ref read is framed. -/
theorem closeInstsM_ships {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {D : Nat} (hIH : IHAt L P Reach D) (hKI : ChildKeepsInv L P Reach D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : InvAt L P Reach D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → ShipsRes L P (shape.insts[k]).1 y))) ∧
      InvAt L P Reach D w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  have hw1 : InvAt L P Reach D w1 :=
    framed_runs L.O hA (stableA_invAt L P Reach D) hw hget FramedA.synthGet
  obtain ⟨rfl, -⟩ := jqc_synthGet L.O hA hw.1 hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoareA _ (InvAt L P Reach D)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      RealChildA L.O x.1 y ∧ (Reach x.1 → ShipsRes L P x.1 y))
    (fun x w y w' hp hy => by
      obtain ⟨h1, h2, h3⟩ := synthesizeChild_ships L P Reach hA (n := x.1) hp hIH hKI hy
      exact ⟨⟨h1, h2⟩, h3⟩)
    shape.insts children hw1 hch
  exact ⟨children, heq.symm, hlen, hk, hw2⟩

/-- **The general closing's children at `InvAt`** (copy of `closeInstsGM_realC`, ChildRunAKids.lean:59, with
`synthesizeChild_ships`; the origin-built arm unchanged). -/
theorem closeInstsGM_ships {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {D : Nat} (hIH : IHAt L P Reach D) (hKI : ChildKeepsInv L P Reach D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : InvAt L P Reach D w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧ MemChildren shape children ∧
      ChildrenShipsI L P Reach shape children ∧ InvAt L P Reach D w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  have hw1 : InvAt L P Reach D w1 :=
    framed_runs L.O hA (stableA_invAt L P Reach D) hw hget FramedA.synthGet
  obtain ⟨rfl, -⟩ := jqc_synthGet L.O hA hw.1 hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := Tools.ShippingChildInv.mapM_hoare _ (InvAt L P Reach D)
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) y =>
      (∀ md, x.2.child? = some md → y = md) ∧
      (x.2.child? = some y ∨ (RealChildA L.O x.1 y ∧ (Reach x.1 → ShipsRes L P x.1 y))))
    (fun x w y w' hp hy => by
      obtain ⟨c, o⟩ := x
      dsimp only at hy ⊢
      cases hmc : Sparkle.Compiler.MachInstOrigin.InstOrigin.child? o with
      | some md =>
        rw [hmc] at hy
        obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
        exact ⟨⟨fun md' h => by cases h; rfl, Or.inl rfl⟩, hp⟩
      | none =>
        rw [hmc] at hy
        obtain ⟨hrc, hsr, hp'⟩ := synthesizeChild_ships L P Reach hA (n := c) hp hIH hKI hy
        exact ⟨⟨fun md' h => (by cases h), Or.inr ⟨hrc, hsr⟩⟩, hp'⟩)
    shape.instTagged children hw1 hch
  have hlenI : children.length = shape.insts.length := by
    rw [hlen]; exact instTagged_length' shape
  refine ⟨children, heq.symm, ?_, ⟨hlenI, fun k hkl => ?_⟩, hw2⟩
  · intro k hkl md hmd
    obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    obtain ⟨y, hky, hm, _⟩ := hk k hkT
    rw [he] at hm
    rw [hm md hmd] at hky
    exact hky
  · obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    obtain ⟨y, hky, _, hor⟩ := hk k hkT
    rw [he] at hor
    exact ⟨y, hky, hor⟩

/-! ## 5. The machine synthesis at `InvAt` (GPOST P2) -/

/-- **The machine synthesis, with its children, from an `InvAt n` world** (copy of
`synthesizeMachineCertified_runsA`, ChildRunAKids.lean:109). Harness: `mixed_keepsAP` with the restricted translator
kept by `translate_keepsInv_of_tele n hKI` (Keep.lean:176). Children: `closeInstsM_ships` / `closeInstsGM_ships`. -/
theorem synthesizeMachineCertified_runsS {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {n : Nat} {tenv : Lean.Environment}
    (hIH : IHAt L P Reach n) (hKI : ChildKeepsInv L P Reach n)
    {b : Bool} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : InvAt L P Reach n w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
          ChildrenShipsI L P Reach shape children)) := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (mixed_keepsAP L.O hA (stableA_invAt L P Reach n)
    (fun e hint top named => translateExprToWire tenv e hint top named) b declName
    shape.binders shape.body
    (fun e hint top named =>
      (translate_keepsInv_of_tele L P Reach n hKI tenv) mctx cctx hA e hint top named))) hw run
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    split at hr
    · rename_i hi
      have eq := RunsTo.pure_eq hr
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨hm, hd⟩ := eq
      exact ⟨t, t', d', run.mreturns, hcl, Or.inl ⟨hi, hm, hd⟩⟩
    · rename_i hi
      have hne : shape.insts ≠ [] := by rw [hi]; exact List.cons_ne_nil _ _
      split at hr
      · rename_i hf
        obtain ⟨children, hc, hlen, hreal, _⟩ := closeInstsM_ships L P Reach hA hIH hKI hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inl ⟨List.isEmpty_iff.mp hf, hc⟩,
          ⟨hlen, fun k hk => by
            obtain ⟨y, hy, hre⟩ := hreal k hk
            exact ⟨y, hy, Or.inr hre⟩⟩⟩⟩
      · rename_i hf
        obtain ⟨children, hc, hmc, hreal, _⟩ := closeInstsGM_ships L P Reach hA hIH hKI hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inr ⟨fun h => hf (List.isEmpty_iff.mpr h), hc, hmc⟩, hreal⟩⟩
  · have eq := RunsTo.pure_eq hr
    cases eq

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.cacheShips_empty
#print axioms Tools.ShippingGen2.tripleInv_clear
#print axioms Tools.ShippingGen2.core_reads_invAt0
#print axioms Tools.ShippingGen2.synthesizeFromConst_machine_invAt
#print axioms Tools.ShippingGen2.machineRunInv_of_core0
#print axioms Tools.ShippingGen2.machineRunInv_of_coreA
#print axioms Tools.ShippingGen2.machineRunJQC_of_runInv
#print axioms Tools.ShippingGen2.machineRunInv_of_closes0
#print axioms Tools.ShippingGen2.synthesizeChild_ships
#print axioms Tools.ShippingGen2.closeInstsM_ships
#print axioms Tools.ShippingGen2.closeInstsGM_ships
#print axioms Tools.ShippingGen2.synthesizeMachineCertified_runsS
