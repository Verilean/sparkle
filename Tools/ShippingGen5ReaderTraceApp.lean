import Tools.ShippingGen5ReaderTraceChain
set_option autoImplicit false
-- NOT BUILT: written against freeze rev5 `scripts/gen5/DG_READERTRACE_FREEZE_REV5.md` §4 (U-R4a); clean issue-linked build pending (coder). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R4a: the three leaf arms of `convStep` `app` (bare register found, `machLoopRead?`, `machReadV`)

Statements are those of `DG_READERTRACE_FREEZE_REV5.md` §4. Conditional (intermediate) result: each arm lemma assumes the discriminants that select the arm and a
successful run `hv`; it takes no `hT`, no `hstep`, no `PureFacts` and no extern fact.
Not supplied: the other `app` arms, `convStep` `letE`, the other bodies, the dispatch, `TraceGood senv nDecl (readF senv n)` as a whole, U-R2, `PhFacts`,
`ShapeInputs`, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

theorem exprPh_slot {senv : StructEnv} {nDecl : Nat} {st : MachRead} {d i : Nat}
    (hTr : TrInv senv nDecl st) (hi : i < st.kinds.size) :
    FReachC nDecl st st ∧ ExprPh senv nDecl d (machSlot i, st) :=
  ⟨FReachC.refl st, hTr, inRange_machSlot hi, noLoose_fvar⟩

theorem conv_app_bareFound_trace (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (dom α init x : Lean.Expr)
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x))
    (hgate : (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false)
    (e0 : Lean.Expr) (k : Nat)
    (hfind : st.bareRegs.find? (·.1 == Lean.Expr.app f a) = some (e0, k))
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  obtain ⟨_, ⟨hTr, _, _, _⟩⟩ := hpre
  have hk : k < st.kinds.size := by
    have hmem : (e0, k) ∈ st.bareRegs.toList := by
      have := Array.mem_of_find?_eq_some hfind
      simpa using this
    exact hTr.2.2.1 (e0, k) hmem
  have hg : (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false := hgate
  simp only [convStep, hreg, hg, hfind, okO, Bool.false_eq_true, ↓reduceIte, run_pure,
    Option.some.injEq] at hv
  subst hv
  exact exprPh_slot hTr hk

theorem conv_app_loopRead_trace (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (i : Nat) (hl : machLoopRead? env d (.app f a) = some i)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  obtain ⟨_, ⟨hTr, _, _, _⟩⟩ := hpre
  simp only [convStep, hreg, hl, run_pure] at hv
  split at hv
  · rename_i hi
    simp only [Option.some.injEq] at hv
    subst hv
    exact exprPh_slot hTr hi
  · simp at hv

theorem conv_app_readV_trace (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (hl : machLoopRead? env d (.app f a) = none)
    (hrun : machRunApp? (.app f a) = none)
    (hic : machInstCall? senv (.app f a) = none)
    (hics : machInstCallS? senv (.app f a) = none)
    (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none)
    (i : Nat) (hr : machReadV env d (.app f a) = some i)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  obtain ⟨_, ⟨hTr, _, _, _⟩⟩ := hpre
  simp only [convStep, hreg, hl, hrun, hic, hics, hmem, hr, run_pure] at hv
  split at hv
  · rename_i hi
    simp only [Option.some.injEq] at hv
    subst hv
    exact exprPh_slot hTr hi
  · simp at hv

end Tools.ShippingGen5ReaderTrace
