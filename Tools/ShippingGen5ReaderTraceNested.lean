import Tools.ShippingGen5ReaderTraceLet
import Tools.ShippingReaderLenOkReserve
set_option autoImplicit false
-- NOT BUILT: written against freeze rev10 addendum §3 `scripts/gen5/DG_READERTRACE_FREEZE_REV10.md` (U-R6: `nestedStep`; no premise). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R6: `nestedStep`

Conditional (intermediate) result: `nested_trace` holds under the fuel-`n` table `hT : TraceGood senv nDecl (readF senv n)` and a successful run `hv`. No `hstep`, no `PureFacts`, no extern fact, no named hypothesis.
Not supplied: the other bodies, `TraceGood senv nDecl (readF senv n)` as a whole, the dispatch, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingReaderLenOk

theorem trInv_reserved {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    {dom' : Lean.Expr} (hdr : InRange nDecl s s.lets.size dom') (hdn : NoLoose 0 dom')
    (body : Lean.Expr) (kinds : List MixedGateBinder) (inits : List Nat) :
    FReachC nDecl s (reserved s dom' body kinds inits) ∧ TrInv senv nDecl (reserved s dom' body kinds inits) := by
  have hreach : FReachC nDecl s (reserved s dom' body kinds inits) := reserved_reachC
  refine ⟨hreach, fullInv_reachC hTr.1 hreach, ?_⟩
  obtain ⟨hlw, hbr, hne, hdm, hln, hgr⟩ := hTr.2
  obtain ⟨hl, hi, hk⟩ := reachC_sizes_mono hreach
  refine ⟨?_, ?_, ?_, ?_, hln, fun k c js r h1 h2 => hgr k c js r h1 h2⟩
  · intro x hx
    exact Nat.le_trans (hlw x hx) hk
  · intro x hx
    exact Nat.lt_of_lt_of_le (hbr x hx) hk
  · intro x hx
    obtain ⟨h1, h2⟩ := hne x hx
    exact ⟨inRange_mono h1 hi hk hl, h2⟩
  · intro d hd
    have hd' : some dom' = some d := hd
    cases hd'
    exact ⟨inRange_mono hdr hi hk hl, hdn⟩

theorem trInv_pushNested {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    (ob : Bool) (e : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr)
    (hv : InRange nDecl s s.lets.size e.2.2.2.2.2) (hn : NoLoose 0 e.2.2.2.2.2) :
    FReachC nDecl s { s with inInner := ob, nested := s.nested.push e } ∧
    TrInv senv nDecl { s with inInner := ob, nested := s.nested.push e } := by
  have hreach : FReachC nDecl s { s with inInner := ob, nested := s.nested.push e } :=
    .ctrl (.refl s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hreach, fullInv_reachC hTr.1 hreach, ?_⟩
  obtain ⟨hlw, hbr, hne, hdm, hln, hgr⟩ := hTr.2
  refine ⟨hlw, hbr, ?_, hdm, hln, fun k c js r h1 h2 => hgr k c js r h1 h2⟩
  intro x hx
  have hx' : x ∈ s.nested.toList ++ [e] := by simpa [Array.toList_push] using hx
  rcases List.mem_append.mp hx' with hx' | hx'
  · exact hne x hx'
  · rw [List.mem_singleton.mp hx']
    exact ⟨hv, hn⟩

theorem nested_trace (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.nested env dom αs initsE body st))
    (r : (Call.nested env dom αs initsE body st).Res)
    (hv : (nestedStep senv env dom αs initsE body st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.nested env dom αs initsE body st) r) ∧
    PhPost senv nDecl (Call.nested env dom αs initsE body st) r := by
  obtain ⟨⟨hst, hE, hld, hlb⟩, ⟨hTr, hEp, hnd, hbd, hnb, hbb⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl 0 p)
      (nestedStep senv env dom αs initsE body st) := by
    unfold nestedStep
    by_cases hin : st.inInner = true
    · simp only [hin, if_true]
      exact satp_failO
    · simp only [hin]
      have hbd0 : BvarLt (0 + env.length + nDecl) dom = true := by rw [Nat.zero_add]; exact hbd
      refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 dom st) p)
        (fun p hp => hT (Call.conv env 0 dom st)
          ⟨⟨hst, hE, noPh_letOk 0 dom hnd⟩, ⟨hTr, hEp, hnd, hbd0⟩⟩ p hp) ?_
      rintro ⟨dom', s1⟩ ⟨hP1, hR1, hX1⟩
      have h1' : Adv st s1 := hP1.1
      have hd'' : LetOk s1.lets.size dom' = true := hP1.2
      have hbc : BvarLt (((MachVal.regs 0) :: env).length + nDecl) body = true := by
        have hh : ((MachVal.regs 0) :: env).length + nDecl = env.length + 1 + nDecl := by simp [List.length_cons]
        rw [hh]; exact hbb
      refine satp_bind ?_
      intro shared hsh
      cases shared with
      | none =>
        refine satp_optK ?_
        rintro ⟨base, s2⟩ hres
        obtain ⟨kinds, inits, _, _, hbase, hs2⟩ := machReserve_some hres
        subst hs2
        obtain ⟨hRes, hTrRes⟩ := trInv_reserved hX1.1 hX1.2.1 hX1.2.2 body kinds inits
        have h2 : Adv s1 (reserved s1 dom' body kinds inits) :=
          adv_dom (adv_refl h1'.1) (by rfl) (by rfl) (by rfl) hd''
        have hRes' : FReachC nDecl s1 { reserved s1 dom' body kinds inits with inInner := true } :=
          .ctrl hRes ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hTr' : TrInv senv nDecl { reserved s1 dom' body kinds inits with inInner := true } := hTrRes
        have hRd' : RdOk { reserved s1 dom' body kinds inits with inInner := true } :=
          rdOk_congr h2.1 (by rfl) (by rfl) (by rfl)
        refine satp_bindO (Q := fun p : List (Nat × Lean.Expr) × Lean.Expr × MachRead =>
            TracePost senv nDecl (Call.chain (MachVal.regs base :: env) body
              { reserved s1 dom' body kinds inits with inInner := true }) p)
          (fun p hp => hT (Call.chain (MachVal.regs base :: env) body
              { reserved s1 dom' body kinds inits with inInner := true })
            ⟨⟨hRd', envOk_cons (envOk_mono h1'.2 hE) (fun w hw => by cases hw), hlb⟩,
             ⟨hTr', envPh_cons_regs (envPh_mono hEp (reachC_trans hR1 hRes')) base, hnb, hbc⟩⟩ p hp) ?_
        rintro ⟨ws, v, s3⟩ ⟨hP3, hR3, hX3⟩
        have hR3' : FReachC nDecl s1 s3 := reachC_trans hRes' hR3
        obtain ⟨hl3, hi3, hk3⟩ := reachC_sizes_mono hR3'
        have hws : ∀ w ∈ s3.ws ++ ws.toArray, w.1 < s3.kinds.size ∧ InRange nDecl s3 s3.lets.size w.2 := by
          intro w hw
          rcases Array.mem_append.mp hw with hw | hw
          · exact hX3.1.1.2.1.2 w hw
          · exact hX3.2.1 w (List.mem_toArray.mp hw)
        have hwsR : FReachC nDecl s3 { s3 with ws := s3.ws ++ ws.toArray } := reachC_ws s3 _ hws
        have hTrW : TrInv senv nDecl { s3 with ws := s3.ws ++ ws.toArray } :=
          ⟨fullInv_reachC hX3.1.1 hwsR, hX3.1.2⟩
        obtain ⟨hRn, hTrN⟩ := trInv_pushNested hTrW s1.inInner (base, dom', αs, initsE, ws, v)
          hX3.2.2.1 hX3.2.2.2
        refine satp_okO ⟨reachC_trans hR1 (reachC_trans hR3' (reachC_trans hwsR hRn)), hTrN, ?_, hX3.2.2.2⟩
        exact hX3.2.2.1
      | some r1 =>
        have hprobe : ∀ a, a ∈ s1.nested.toList →
            SatP (readF senv n) (fun p : Lean.Expr × MachRead => FReachC nDecl s1 p.2 ∧ ExprPh senv nDecl 0 p)
              (nestedProbe env dom' αs initsE body s1 a) := by
          rintro ⟨base, d, a, ini, ws, v⟩ hmem
          refine satp_ite ?_ satp_failO
          refine satp_bind ?_
          intro r2 hr2
          rcases r2 with _ | ⟨ws', v', st'⟩
          · exact satp_failO
          · have hh := hT (Call.chain (MachVal.regs base :: env) body s1)
              ⟨⟨h1'.1, envOk_cons (envOk_mono h1'.2 hE) (fun w hw => by cases hw), hlb⟩,
               ⟨hX1.1, envPh_cons_regs (envPh_mono hEp hR1) base, hnb, hbc⟩⟩ (ws', v', st') hr2
            obtain ⟨hl3, hi3, hk3⟩ := reachC_sizes_mono hh.2.1
            obtain ⟨hI, hN⟩ := hX1.1.2.2.2.1 _ hmem
            refine satp_pure_ite ?_
            exact ⟨hh.2.1, hh.2.2.1, inRange_mono hI hi3 hk3 hl3, hN⟩
        have hh := satp_findSomeO (P := fun p : Lean.Expr × MachRead => FReachC nDecl s1 p.2 ∧ ExprPh senv nDecl 0 p)
          s1.nested.toList hprobe r1 hsh
        exact satp_okO ⟨reachC_trans hR1 hh.1, hh.2⟩
  exact key r hv

end Tools.ShippingGen5ReaderTrace
