import Tools.ShippingGen5ReaderTraceApp
import Tools.ShippingGen3ArgSupply4
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceReg, exit 0) on the tree of 252ea167e441cc345829d4fd35c41c8c473da47f (this header is comment-only). Written against freeze rev6 `scripts/gen5/DG_READERTRACE_FREEZE_REV6.md` (U-R4b); clean issue-linked build pending (coder). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R4b: the new bare-register arm of `convStep` `app`

Statements are those of `DG_READERTRACE_FREEZE_REV6.md` §1. Conditional (intermediate) result: `conv_app_bareNew_trace` assumes the discriminants that select the arm, the fuel-`n` table
`hT : TraceGood senv nDecl (readF senv n)` and a successful run `hv`; it takes no `hstep`, no `PureFacts` and no extern fact.
Not supplied: the other `app` arms, `convStep` `letE`, the other bodies, the dispatch, `TraceGood senv nDecl (readF senv n)` as a whole, U-R2, `PhFacts`,
`ShapeInputs`, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

theorem ph_argsAcc {L : Nat} : ∀ (e : Lean.Expr) (acc : List Lean.Expr), NoPh e = true → BvarLt L e = true →
    (∀ a ∈ acc, NoPh a = true ∧ BvarLt L a = true) →
    ∀ a ∈ Tools.ShippingReaderMatcherArity.argsAcc e acc, NoPh a = true ∧ BvarLt L a = true
  | .app f a, acc, hn, hb, hacc => by
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    refine ph_argsAcc f (a :: acc) hn.1 hb.1 ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hn.2, hb.2⟩
    · exact hacc x hx
  | .bvar _, _, _, _, hacc => hacc
  | .fvar _, _, _, _, hacc => hacc
  | .mvar _, _, _, _, hacc => hacc
  | .sort _, _, _, _, hacc => hacc
  | .const _ _, _, _, _, hacc => hacc
  | .lit _, _, _, _, hacc => hacc
  | .lam _ _ _ _, _, _, _, hacc => hacc
  | .forallE _ _ _ _, _, _, _, hacc => hacc
  | .letE _ _ _ _ _, _, _, _, hacc => hacc
  | .mdata _ _, _, _, _, hacc => hacc
  | .proj _ _ _, _, _, _, hacc => hacc

theorem phArgs_getAppArgs {L : Nat} {e : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true) :
    ∀ a ∈ e.getAppArgs, NoPh a = true ∧ BvarLt L a = true := by
  intro a ha
  rw [Tools.ShippingReaderMatcherArityArray.getAppArgs_eq] at ha
  exact ph_argsAcc e [] hn hb (by simp) a (List.mem_toArray.mp ha)

theorem regView_ph {L : Nat} {e dom α init x : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : regView? e.getAppFn e.getAppArgs = some (dom, α, init, x)) :
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh x = true ∧ BvarLt L x = true) :=
  Tools.ShippingGen3ArgSupply4.regView?_all (fun a => NoPh a = true ∧ BvarLt L a = true) _ _ dom α init x
    (phArgs_getAppArgs hn hb) h

/-- helper (not one of the frozen statements): the state after pushing a bare register keeps `TrInv` and is `FReachC`-reachable. -/
theorem trInv_pushReg {senv : StructEnv} {nDecl : Nat} {s1 : MachRead} (hTr : TrInv senv nDecl s1)
    {dom' : Lean.Expr} (hdr : InRange nDecl s1 s1.lets.size dom') (hdn : NoLoose 0 dom')
    (kind : MixedGateBinder) (initN : Nat) (nm : Name) (e : Lean.Expr) :
    FReachC nDecl s1 { s1 with
        kinds := s1.kinds.push kind, inits := s1.inits.push initN, names := s1.names.push nm,
        dom := some dom', bareRegs := s1.bareRegs.push (e, s1.kinds.size) } ∧
    TrInv senv nDecl { s1 with
        kinds := s1.kinds.push kind, inits := s1.inits.push initN, names := s1.names.push nm,
        dom := some dom', bareRegs := s1.bareRegs.push (e, s1.kinds.size) } := by
  have hreach : FReachC nDecl s1 { s1 with
        kinds := s1.kinds.push kind, inits := s1.inits.push initN, names := s1.names.push nm,
        dom := some dom', bareRegs := s1.bareRegs.push (e, s1.kinds.size) } :=
    .ctrl (.tail (.refl s1) (FStep.slot s1 kind initN nm)) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hreach, fullInv_reachC hTr.1 hreach, ?_⟩
  obtain ⟨hlw, hbr, hne, hdm, hln, hgr⟩ := hTr.2
  obtain ⟨hl, hi, hk⟩ := reachC_sizes_mono hreach
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Nat.le_trans (hlw x hx) hk
  · intro x hx
    have hx' : x ∈ s1.bareRegs.toList ++ [(e, s1.kinds.size)] := by
      simpa [Array.toList_push] using hx
    rcases List.mem_append.mp hx' with hx' | hx'
    · exact Nat.lt_of_lt_of_le (hbr x hx') hk
    · rw [List.mem_singleton.mp hx']
      show s1.kinds.size < (s1.kinds.push kind).size
      rw [Array.size_push]
      exact Nat.lt_succ_self _
  · intro x hx
    obtain ⟨h1, h2⟩ := hne x hx
    exact ⟨inRange_mono h1 hi hk hl, h2⟩
  · intro d hd
    have hd' : some dom' = some d := hd
    cases hd'
    exact ⟨inRange_mono hdr hi hk hl, hdn⟩
  · exact hln
  · exact fun k c js r h1 h2 => hgr k c js r h1 h2

theorem conv_app_bareNew_trace (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (dom α init x : Lean.Expr)
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x))
    (hgate : (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false)
    (hfind : st.bareRegs.find? (·.1 == Lean.Expr.app f a) = none)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  obtain ⟨⟨hst, hE, hl⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have hd0 : d = 0 := by
    by_cases hz : d = 0
    · exact hz
    · simp [hz] at hgate
  have hbl0 : BvarLt (0 + env.length + nDecl) (Lean.Expr.app f a) = true := by
    rw [← hd0]; exact hbl
  obtain ⟨hdomP, hxP⟩ := regView_ph hnp hbl0 hreg
  have hlx : LetOk 0 x = true := noPh_letOk 0 x hxP.1
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl d p)
      (convStep senv env d (.app f a) st) := by
    simp only [convStep, hreg, hgate, hfind, Bool.false_eq_true, ↓reduceIte]
    refine satp_optK ?_
    intro kind _
    refine satp_optK ?_
    intro initN _
    refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 dom st) p)
      (fun p hp => hT (Call.conv env 0 dom st)
        ⟨⟨hst, hE, noPh_letOk 0 dom hdomP.1⟩, ⟨hTr, hEp, hdomP.1, hdomP.2⟩⟩ p hp) ?_
    rintro ⟨dom', s1⟩ hQ1
    obtain ⟨hP1, hR1, hX1⟩ := hQ1
    have h1' : Adv st s1 := hP1.1
    have hd'' : LetOk s1.lets.size dom' = true := hP1.2
    refine satp_domGuard ?_
    obtain ⟨hreach2, hTr2⟩ := trInv_pushReg hX1.1 hX1.2.1 hX1.2.2 kind initN
      (Name.mkSimple s!"reg{s1.kinds.size}") (Lean.Expr.app f a)
    let st2 : MachRead :=
      { s1 with
        kinds := s1.kinds.push kind, inits := s1.inits.push initN
        names := s1.names.push (Name.mkSimple s!"reg{s1.kinds.size}"), dom := some dom'
        bareRegs := s1.bareRegs.push (Lean.Expr.app f a, s1.kinds.size) }
    have hRd2 : RdOk st2 := rdOk_dom h1'.1 rfl rfl rfl hd''
    refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 x st2) p)
      (fun p hp => hT (Call.conv env 0 x st2)
        ⟨⟨hRd2, envOk_mono h1'.2 hE, hlx⟩,
         ⟨hTr2, envPh_mono hEp (reachC_trans hR1 hreach2), hxP.1, hxP.2⟩⟩ p hp) ?_
    rintro ⟨x', s3⟩ hQ2
    obtain ⟨_, hR2, hX2⟩ := hQ2
    have hR2' : FReachC nDecl st2 s3 := hR2
    obtain ⟨_, _, hk⟩ := reachC_sizes_mono hR2'
    have hbase : s1.kinds.size < s3.kinds.size := by
      have : (s1.kinds.push kind).size ≤ s3.kinds.size := hk
      rw [Array.size_push] at this
      omega
    have hws : ∀ w ∈ s3.ws.push (s1.kinds.size, x'),
        w.1 < s3.kinds.size ∧ InRange nDecl s3 s3.lets.size w.2 := by
      intro w hw
      rcases Array.mem_push.mp hw with hw | hw
      · exact hX2.1.1.2.1.2 w hw
      · rw [hw]; exact ⟨hbase, hX2.2.1⟩
    have hreach : FReachC nDecl st { s3 with ws := s3.ws.push (s1.kinds.size, x') } :=
      reachC_trans hR1 (reachC_trans hreach2 (reachC_trans hR2' (reachC_ws s3 _ hws)))
    refine satp_okO ⟨hreach, ⟨fullInv_reachC hTr.1 hreach, hX2.1.2⟩, inRange_machSlot hbase, noLoose_fvar⟩
  exact key v hv

end Tools.ShippingGen5ReaderTrace
