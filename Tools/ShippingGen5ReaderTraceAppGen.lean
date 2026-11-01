import Tools.ShippingGen5ReaderTraceReg
import Tools.ShippingGen5ReaderTraceIota
set_option autoImplicit false
-- NOT BUILT: written against freeze rev7 `scripts/gen5/DG_READERTRACE_FREEZE_REV7.md` §3 (U-R4d); build result and clean issue-linked build pending. No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R4d: the general `app` arm of `convStep`

Statement is that of `DG_READERTRACE_FREEZE_REV7.md` §3. Conditional (intermediate) result: the lemma assumes the discriminants that select the arm, the fuel-`n` table
`hT : TraceGood senv nDecl (readF senv n)` and a successful run `hv`; it takes no `hstep`, no `PureFacts` and no extern fact (the structural `bundleProj_ph` is a lemma, not a hypothesis).
Not supplied: the instance / nested / memory `app` arms (U-R4e onward), `convStep` `letE`, the other bodies, the dispatch, `TraceGood senv nDecl (readF senv n)` as a whole,
`ShapeInputs`, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

theorem conv_app_general_trace (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (hl : machLoopRead? env d (.app f a) = none)
    (hrun : machRunApp? (.app f a) = none)
    (hic : machInstCall? senv (.app f a) = none)
    (hics : machInstCallS? senv (.app f a) = none)
    (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none)
    (hr : machReadV env d (.app f a) = none)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  obtain ⟨⟨hst, hE, hlo⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have hnp' : NoPh f = true ∧ NoPh a = true := by simpa [NoPh] using hnp
  have hbl' : BvarLt (d + env.length + nDecl) f = true ∧ BvarLt (d + env.length + nDecl) a = true := by
    simpa [BvarLt] using hbl
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl d p)
      (convStep senv env d (.app f a) st) := by
    simp only [convStep, hreg, hl, hrun, hic, hics, hmem, hr]
    refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env d f st) p)
      (fun p hp => hT (Call.conv env d f st)
        ⟨⟨hst, hE, noPh_letOk 0 f hnp'.1⟩, ⟨hTr, hEp, hnp'.1, hbl'.1⟩⟩ p hp) ?_
    rintro ⟨f', s1⟩ hQ1
    obtain ⟨hP1, hR1, hX1⟩ := hQ1
    have hAdv : Adv st s1 := hP1.1
    refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env d a s1) p)
      (fun p hp => hT (Call.conv env d a s1)
        ⟨⟨hAdv.1, envOk_mono hAdv.2 hE, noPh_letOk 0 a hnp'.2⟩,
         ⟨hX1.1, envPh_mono hEp hR1, hnp'.2, hbl'.2⟩⟩ p hp) ?_
    rintro ⟨a', s2⟩ hQ2
    obtain ⟨_, hR2, hX2⟩ := hQ2
    obtain ⟨hl2, hI2, hK2⟩ := reachC_sizes_mono hR2
    obtain ⟨hIR, hNL⟩ := bundleProj_ph (k := s2.lets.size) (d := d) senv.proj
      ⟨inRange_mono hX1.2.1 hI2 hK2 hl2, hX1.2.2⟩ hX2.2
    exact satp_okO ⟨reachC_trans hR1 hR2, hX2.1, hIR, hNL⟩
  exact key v hv

end Tools.ShippingGen5ReaderTrace
