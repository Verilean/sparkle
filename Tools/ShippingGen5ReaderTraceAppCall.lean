import Tools.ShippingGen5ReaderTraceApp
import Tools.ShippingGen5ReaderTraceAppGen
import Tools.ShippingGen5ReaderTraceSigTy
import Tools.ShippingGen5ReaderTraceInst
import Tools.ShippingGen5ReaderTraceNested
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceAppCall, exit 0, 762 jobs) on the tree of this file's commit. No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R11a: the call-forwarding `app` arms of `convStep` (nested / instance / structure instance / memory)

Conditional (intermediate) results. Each arm lemma assumes the discriminants that select the arm, the fuel-`n` table `hT : TraceGood senv nDecl (readF senv n)` and a successful run `hv`.
The only named hypothesis is `SigTyPh senv` in the structure-instance arm (as `machInstCallS?_ty_ph`). No new premise.
Not supplied: the dispatch over all `convStep` shapes (U-R11b), the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

theorem memCall?_len {natOf : Lean.Expr → Option Nat} {e : Lean.Expr} {combo : Bool} {aw dw : Nat}
    {dom : Lean.Expr} {ops : List Lean.Expr}
    (h : Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops)) : ops.length = 4 := by
  unfold Sparkle.Compiler.MachMemory.memCall? at h
  simp only [] at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, _, rfl, rfl⟩ := h
        rfl
    · simp at h

theorem conv_app_nested_trace (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (hl : machLoopRead? env d (.app f a) = none)
    (dom αs initsE body : Lean.Expr) (hrun : machRunApp? (.app f a) = some (dom, αs, initsE, body))
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  obtain ⟨⟨hst, hE, hlo⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl d p)
      (convStep senv env d (.app f a) st) := by
    simp only [convStep, hreg, hl, hrun]
    by_cases hd0 : d = 0
    · subst hd0
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      have hbl0 : BvarLt (env.length + nDecl) (Lean.Expr.app f a) = true := by simpa using hbl
      obtain ⟨hD, hA, hI, hB⟩ := machRunApp?_ph hnp hbl0 hrun
      have hB' : BvarLt (env.length + 1 + nDecl) body = true := by
        have : env.length + 1 + nDecl = env.length + nDecl + 1 := by omega
        rw [this]; exact hB.2
      intro r' hr'
      have hh := hT (Call.nested env dom αs initsE body st)
        ⟨⟨hst, hE, noPh_letOk 0 dom hD.1, noPh_letOk 0 body hB.1⟩, ⟨hTr, hEp, hD.1, hD.2, hB.1, hB'⟩⟩ r' hr'
      exact ⟨hh.2.1, hh.2.2⟩
    · have hne : (d != 0) = true := by simp [hd0]
      simp only [hne, if_true]
      exact satp_failO
  exact key v hv

theorem conv_app_inst_trace (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (hl : machLoopRead? env d (.app f a) = none)
    (hrun : machRunApp? (.app f a) = none)
    (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr)
    (hic : machInstCall? senv (.app f a) = some (c, kinds, res, args))
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  obtain ⟨⟨hst, hE, hlo⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl d p)
      (convStep senv env d (.app f a) st) := by
    simp only [convStep, hreg, hl, hrun, hic]
    by_cases hd0 : d = 0
    · subst hd0
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      have hbl0 : BvarLt (env.length + nDecl) (Lean.Expr.app f a) = true := by simpa using hbl
      have hargs := machInstCall?_ph hnp hbl0 hic
      intro r' hr'
      have hh := hT (Call.inst env c Sparkle.Compiler.MachInstOrigin.InstOrigin.ord kinds res args st)
        ⟨⟨hst, hE, fun x hx => noPh_letOk 0 x (hargs x hx).1⟩, ⟨hTr, hEp, hargs, Or.inl rfl⟩⟩ r' hr'
      exact ⟨hh.2.1, hh.2.2⟩
    · have hne : (d != 0) = true := by simp [hd0]
      simp only [hne, if_true]
      exact satp_failO
  exact key v hv

theorem conv_app_instS_trace (senv : StructEnv) (nDecl n : Nat) (hS : SigTyPh senv)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (hl : machLoopRead? env d (.app f a) = none)
    (hrun : machRunApp? (.app f a) = none)
    (hic : machInstCall? senv (.app f a) = none)
    (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr)
    (hics : machInstCallS? senv (.app f a) = some (c, kinds, ty, args))
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  obtain ⟨⟨hst, hE, hlo⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl d p)
      (convStep senv env d (.app f a) st) := by
    simp only [convStep, hreg, hl, hrun, hic, hics]
    by_cases hd0 : d = 0
    · subst hd0
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      have hbl0 : BvarLt (env.length + nDecl) (Lean.Expr.app f a) = true := by simpa using hbl
      have hargs := machInstCallS?_args_ph hnp hbl0 hics
      obtain ⟨hsig, hlen⟩ := machInstCallS?_spec hics
      obtain ⟨hty1, hty2⟩ := machInstCallS?_ty_ph hS hics
      have hty3 : BvarLt (env.length + nDecl) ty = true := bvarLt_mono (Nat.zero_le _) hty2
      intro r' hr'
      have hh := hT (Call.instS env c kinds ty args st)
        ⟨⟨hst, hE, fun x hx => noPh_letOk 0 x (hargs x hx).1, noPh_letOk 0 ty hty1⟩,
         ⟨hTr, hEp, hsig, hlen, hargs, hty1, hty3⟩⟩ r' hr'
      exact ⟨hh.2.1, hh.2.2⟩
    · have hne : (d != 0) = true := by simp [hd0]
      simp only [hne, if_true]
      exact satp_failO
  exact key v hv

theorem conv_app_mem_trace (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (hl : machLoopRead? env d (.app f a) = none)
    (hrun : machRunApp? (.app f a) = none)
    (hic : machInstCall? senv (.app f a) = none)
    (hics : machInstCallS? senv (.app f a) = none)
    (combo : Bool) (aw dw : Nat) (dom : Lean.Expr) (ops : List Lean.Expr)
    (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) =
      some (combo, aw, dw, dom, ops))
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  obtain ⟨⟨hst, hE, hlo⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have key : SatP (readF senv n)
      (fun p : Lean.Expr × MachRead => FReachC nDecl st p.2 ∧ ExprPh senv nDecl d p)
      (convStep senv env d (.app f a) st) := by
    simp only [convStep, hreg, hl, hrun, hic, hics, hmem]
    by_cases hd0 : d = 0
    · subst hd0
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      have hbl0 : BvarLt (env.length + nDecl) (Lean.Expr.app f a) = true := by simpa using hbl
      obtain ⟨hdom, hops⟩ := memCall?_ph hnp hbl0 hmem
      have hlen := memCall?_len hmem
      have hargs : ∀ x ∈ dom :: ops, NoPh x = true ∧ BvarLt (env.length + nDecl) x = true := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdom
        · exact hops x hx
      refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl
          (Call.inst env (Sparkle.Compiler.MachMemory.memChildName combo aw dw)
            (Sparkle.Compiler.MachInstOrigin.InstOrigin.mem combo aw dw)
            [.domain, .bits aw, .bits dw, .bool, .bits aw] (.bits dw) (dom :: ops) st) p)
        (fun p hp => hT (Call.inst env (Sparkle.Compiler.MachMemory.memChildName combo aw dw)
            (Sparkle.Compiler.MachInstOrigin.InstOrigin.mem combo aw dw)
            [.domain, .bits aw, .bits dw, .bool, .bits aw] (.bits dw) (dom :: ops) st)
          ⟨⟨hst, hE, fun x hx => noPh_letOk 0 x (hargs x hx).1⟩,
           ⟨hTr, hEp, hargs, Or.inr ⟨combo, aw, dw, rfl, rfl, rfl, by simp [hlen]⟩⟩⟩ p hp) ?_
      rintro ⟨v1, s1⟩ ⟨hP1, hR1, hX1⟩
      have hreach : FReachC nDecl s1 { s1 with instStruct := true } :=
        .ctrl (.refl s1) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact satp_okO ⟨reachC_trans hR1 hreach, ⟨fullInv_reachC hX1.1.1 hreach, hX1.1.2⟩, hX1.2.1, hX1.2.2⟩
    · have hne : (d != 0) = true := by simp [hd0]
      simp only [hne, if_true]
      exact satp_failO
  exact key v hv

end Tools.ShippingGen5ReaderTrace
