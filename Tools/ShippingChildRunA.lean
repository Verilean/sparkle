import Tools.ShippingChildCoreC
-- BUILT (unit G, par/u-g): g9 exit 0 (build of Tools.ShippingChildRunA); axioms of core_reads_invA, machine_run_of_coreA, synthesizeFromConst_machine_invA: propext, Classical.choice, Quot.sound (g10 exit 0, #print axioms, since removed).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Law witness: `O : RefLawsAOps MkRefd
-- mref cref` at `hA : AdmCtx O.quiet mctx cctx` only (no `RefLaws`, no `ChildBnd`, no old `InvV`).
-- Writing-time guesses (marked `-- guess: Gn`):
--  G1 `triple_runs` : `rw [h] at this` turns the `match` of `Triple` into the `.ok` arm by iota;
--  G2 the `peelF`/`peelP` macros: `by first | exact FramedA.sideSet _ (by constructor) | …` is
--     elaborated after `step` fixed the program (tactic blocks are postponed);
--  G3 `simp only [Bool.false_eq_true, ↓reduceIte]` leaves the same do-block as in `core_reads_inv`
--     (ShippingChildRun.lean:134-190) and `core0_tripleAC_aux` (ShippingChildDepthC.lean:139).

/-! # Run unpacking under the NEW boundary (row L5 of docs/parallel/main-theorem-connection.md)

The analogue of `core_reads_inv` / `machine_run_of_core` (ShippingChildRun.lean) with
`O : RefLawsAOps MkRefd mref cref` and the invariants `JQ O.quiet D` / `JQC O D` in place of the old
`RefLaws`, `StartV`, `InvV`.

PROVED here (relative to `O`, `hA` only; the start world is a hypothesis):
* `core_reads_invA`: a returning run of `synthesizeCombinationalCore declName [] false` from a world
  with `JQ O.quiet D` (and, when `D ≠ 0`, `CacheInvA O (cv w)`) contains a run of the body
  `synthesizeFromConst …` from a `JQC O (D + 1)` world (the depth-0 clear establishes the cache
  half; nested runs inherit it);
* `synthesizeFromConst_machine_invA`, `machine_run_of_coreA`: on the machine route the body contains
  a run of `synthesizeMachineCertified` starting in a `JQC O (D + 1)` world (depth ≥ 1).

This is a CONDITIONAL connection to the old endpoints' decomposition. It is not RTL semantic
preservation, not a runtime-fit proof of `O`, and `RealChildA` / `JQC` is a history of past
synthesis results, not freshness. -/

namespace Tools.ShippingChildRunA
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA
open Tools.ShippingChildVertA
open Tools.ShippingChildCoreC

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A `Triple` on a RETURNING run: the postcondition at the end world. -/
theorem triple_runs {α : Type} {P : Void IO.RealWorld → Prop} {p : MetaM α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (ht : Triple mctx mref cctx cref P p Q R) {w a w'} (hw : P w)
    (h : RunsTo p mctx mref cctx cref w a w') : Q a w' := by
  have := ht w hw
  unfold RunsTo at h
  rw [h] at this  -- guess: G1
  exact this

/-- A framed step carries a stable invariant (the run `h` is taken BEFORE the framing proof `hp`,
so the proof's tactic block sees the program). -/
theorem framed_runs (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) {α : Type} {p : MetaM α}
    {w a w'} (hw : I w) (h : RunsTo p mctx mref cctx cref w a w') (hp : FramedA MkRefd p) : I w' :=
  triple_runs (keeps_iff.mp (keepsA_framed O hA hS hp)) hw h

/-- One framed step of the walk: the stable invariant is carried, the program read off the step. -/
macro "peelF " O:term:max hA:term:max hS:term:max h:ident hw:ident : tactic => `(tactic|
  (obtain ⟨_, _, step, $h:ident⟩ := RunsTo.bind $h:ident
   have $hw:ident := framed_runs $O $hA $hS $hw step
     (by first | exact FramedA.sideSet _ (by constructor) | exact FramedA.sideGet (by constructor)
               | exact FramedA.env | exact FramedA.constInfo _)  -- guess: G2
   clear step))

/-- A `pure` bind is skipped (syntactic match on the head, no defeq search). -/
theorem pure_bind_runs {α β : Type} {a : α} {f : α → MetaM β} {w b w'}
    (h : RunsTo ((Pure.pure a : MetaM α) >>= f) mctx mref cctx cref w b w') :
    RunsTo (f a) mctx mref cctx cref w b w' := by
  obtain ⟨_, w1, hp, h⟩ := RunsTo.bind h
  obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hp
  exact h

/-- One `pure` step of the walk. -/
macro "peelP " h:ident : tactic => `(tactic| replace $h:ident := pure_bind_runs $h:ident)

/-- **The entry's prefix ESTABLISHES `JQC` at the body's start** (new boundary). From a world with
`JQ O.quiet D` — and the cache half `CacheInvA O (cv w)` when `D ≠ 0` — a returning run of the core
entry contains: `getConstInfo`, `getEnv`, and the body `synthesizeFromConst …` run from a world `w3`
in `JQC O (D + 1)`. At `D = 0` the cache clear establishes the cache half from ANY cache; nested, it
is inherited. -/
theorem core_reads_invA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {D : Nat} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module}
    {Dg : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
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
        mctx mref cctx cref w3 (M, Dg) w4 ∧ JQC O (D + 1) w3 := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h  -- guess: G3
  by_cases h0 : D = 0
  · -- outermost: the clear establishes the cache half
    subst h0
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQ _ 0) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag O hA (stableA_JQ _ 0)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet O hA (stableA_JQ _ 0)) hw s3
    have hdD : d = 0 := hd.2.trans hd.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    simp only [↓reduceIte, beq_self_eq_true] at h
    peelP h; peelP h; peelP h; peelP h; peelP h; peelP h; peelP h
    peelF O hA (stableA_JQ _ 0) h hw; peelF O hA (stableA_JQ _ 0) h hw
    peelF O hA (stableA_JQ _ 0) h hw; peelF O hA (stableA_JQ _ 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleC_clear O hA 0 (R := fun _ _ => False)) hw step
    clear step
    peelF O hA (stableA_JQC O 0) h hw; peelF O hA (stableA_JQC O 0) h hw
    peelF O hA (stableA_JQC O 0) h hw; peelF O hA (stableA_JQC O 0) h hw
    peelF O hA (stableA_JQC O 0) h hw; peelF O hA (stableA_JQC O 0) h hw
    peelF O hA (stableA_JQC O 0) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleC_depthSet O hA 0 (0 + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (0 + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (0 + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, hw⟩
  · -- nested: the cache half is inherited
    replace hw : JQC O D w := ⟨hw, hc.resolve_left h0⟩
    obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O D) (FramedA.ioEnv _))) hw s1
    obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_diag O hA (stableA_JQC O D)
      (Diag.profLog prof.isSome _))) hw s2
    obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
    have hd := triple_runs (tripleA_depthGet O hA (stableA_JQC O D)) hw s3
    have hdD : d = D := hd.2.trans hd.1.1.2.2
    have hw := hd.1
    subst hdD
    rcases RunsTo.ite h with h | h
    · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ ht).elim
    have h0' : ¬ ((d == 0) = true) := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw; peelF O hA (stableA_JQC O d) h hw
    peelF O hA (stableA_JQC O d) h hw
    obtain ⟨_, _, step, h⟩ := RunsTo.bind h
    have hw := triple_runs (tripleC_depthSet O hA d (d + 1) (R := fun _ _ => False)) hw step
    clear step
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
      (FramedA.constInfo _))) hw hget
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O (d + 1))
      FramedA.env)) hw henv
    exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, hw⟩

/-- `synthesizeFromConst_machine_inv` under `JQC`: on the machine route (both gates miss), the
body's run contains a `getEnv` and a run of `synthesizeMachineCertified` of every machine shape the
second environment defines, starting in a `JQC O n` world (the same `n`: `getEnv` is framed). -/
theorem synthesizeFromConst_machine_invA (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {tenv : Lean.Environment}
    {logProf : String → IO Unit} {declName : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : JQC O n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) logProf
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w7 w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
            shape) mctx mref cctx cref w7 r w8 ∧ JQC O n w7 ∧
          ∀ res, r = some res → res = (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (keepsA_framed O hA (stableA_JQC O n) FramedA.env)) hw henv
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

/-- **The machine synthesis inside a real core run** (new boundary): from a world with `JQ O.quiet D`
(and the cache half when `D ≠ 0`), the machine synthesis the entry performed starts in a world in
`JQC O (D + 1)` — in particular at depth `D + 1 ≥ 1`, with the cache half. Analogue of
`machine_run_of_core`; `InvW`/`DepthPos` are replaced by `JQC O (D + 1)`. -/
theorem machine_run_of_coreA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
        mctx mref cctx cref w9 r w10 ∧ JQC O (D + 1) w9 ∧
      ∀ res, r = some res → res = (m, d) := by
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run, hw3⟩ :=
    core_reads_invA O hA hw hc hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine_invA O hA old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hw9, hres⟩ := hmach shape hshape
  exact ⟨_, b, r, w9, w10, hrun, hw9, hres⟩

/-- At the machine synthesis's start the depth is at least one: `dv w9 = D + 1`. -/
theorem jqc_depth_pos {O : RefLawsAOps MkRefd mref cref} {D : Nat} {w : Void IO.RealWorld}
    (h : JQC O D w) : dv w = D ∧ O.quiet w ∧ sv w = some synthesizeChild :=
  ⟨h.1.2.2, h.1.1, h.1.2.1⟩

end Tools.ShippingChildRunA
