import Tools.ShippingGen5ReaderTraceLoop
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceLoopRoot, exit 0, 756 jobs) on the tree of 97de8a8e8a8ada2267a12a6d50738201a64e9ec5 (Lean content identical; this header is comment-only). Written against freeze rev13 `scripts/gen5/DG_READERTRACE_FREEZE_REV13.md` §2 (U-R10: `loopRootStep`; no premise). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R10: `loopRootStep`

Conditional (intermediate) result: `loopRoot_trace` holds under the fuel-`n` table `hT : TraceGood senv nDecl (readF senv n)` and a successful run `hv`. No `hstep`, no `PureFacts`, no extern fact, no named hypothesis.
Not supplied: `instSStep`, the dispatch, `TraceGood senv nDecl (readF senv n)` as a whole, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv

theorem inlSpine_ph {L : Nat} : ∀ (e : Lean.Expr) (acc : List Lean.Expr), NoPh e = true → BvarLt L e = true →
    (∀ a ∈ acc, NoPh a = true ∧ BvarLt L a = true) →
    ∀ (fn : Lean.Expr) (args : List Lean.Expr), inlSpine e acc = (fn, args) →
    ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true
  | .app f a, acc, hn, hb, hacc, fn, args, h => by
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    refine inlSpine_ph f (a :: acc) hn.1 hb.1 ?_ fn args h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hn.2, hb.2⟩
    · exact hacc x hx
  | .bvar _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .fvar _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .mvar _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .sort _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .const _ _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .lit _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .lam _ _ _ _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .forallE _ _ _ _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .letE _ _ _ _ _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .mdata _ _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc
  | .proj _ _ _, acc, _, _, hacc, fn, args, h => by
    simp only [inlSpine, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact hacc

theorem loopView_ph {L : Nat} {e dom body : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : loopView? e = some (dom, body)) :
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh body = true ∧ BvarLt (L + 1) body = true) := by
  have hs := inlSpine_ph e [] hn hb (by simp)
  unfold loopView? at h
  generalize hsp : inlSpine e [] = sp at h
  obtain ⟨fn, args⟩ := sp
  have hs' := hs fn args hsp
  split at h
  · rename_i t1 t2 t3 nm t body' bi hsh
    injection h with h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at hsh
    obtain ⟨_, rfl⟩ := hsh
    have hd := hs' t1 (by simp)
    have hl := hs' (Lean.Expr.lam nm t body' bi) (by simp)
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hl
    exact ⟨hd, hl.1.2, hl.2.2⟩
  · cases h

theorem mapM_len_some {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil] at h
    injection h with h
    subst h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    injection h with h
    subst h
    simp [mapM_len_some f l bs hbs]

theorem trInv_pushLoop {senv : StructEnv} {nDecl : Nat} {s1 : MachRead} (hTr : TrInv senv nDecl s1)
    {dom' : Lean.Expr} (hdr : InRange nDecl s1 s1.lets.size dom') (hdn : NoLoose 0 dom')
    (ks : List MixedGateBinder) (iv : List Nat) (ns : List Name)
    (lp : Array (Nat × Nat)) (nl ld : Nat) :
    FReachC nDecl s1 { s1 with
        kinds := s1.kinds ++ ks.toArray, inits := s1.inits ++ iv.toArray,
        names := s1.names ++ ns.toArray, dom := some dom', loops := lp, nestedLoops := nl, loopDepth := ld } ∧
    TrInv senv nDecl { s1 with
        kinds := s1.kinds ++ ks.toArray, inits := s1.inits ++ iv.toArray,
        names := s1.names ++ ns.toArray, dom := some dom', loops := lp, nestedLoops := nl, loopDepth := ld } := by
  have hreach : FReachC nDecl s1 { s1 with
        kinds := s1.kinds ++ ks.toArray, inits := s1.inits ++ iv.toArray,
        names := s1.names ++ ns.toArray, dom := some dom', loops := lp, nestedLoops := nl, loopDepth := ld } :=
    .ctrl (.tail (.refl s1) (FStep.slots s1 ks iv ns)) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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

def loopNewSt (s1 : MachRead) (kinds : List MixedGateBinder) (inits : List Nat) (dom' : Lean.Expr) : MachRead :=
  { s1 with
    kinds := s1.kinds ++ kinds.toArray
    inits := s1.inits ++ inits.toArray
    names := s1.names ++ ((List.range kinds.length).map fun i => Name.mkSimple s!"loop{s1.loops.size}_r{i}").toArray
    dom := some dom'
    loops := s1.loops.push (s1.kinds.size, kinds.length)
    nestedLoops := if s1.loopDepth ≥ 1 then s1.nestedLoops + 1 else s1.nestedLoops
    loopDepth := s1.loopDepth + 1 }

theorem envPh_cons_state {nDecl : Nat} {st : MachRead} {env : List MachVal} (h : EnvPh nDecl st env) {b n : Nat}
    (hb : b + n ≤ st.kinds.size) : EnvPh nDecl st (MachVal.state b n :: env) := by
  refine ⟨fun v hv => ?_, fun b' n' hbn => ?_⟩
  · rcases List.mem_cons.mp hv with hv | hv
    · cases hv
    · exact h.1 v hv
  · rcases List.mem_cons.mp hbn with hv | hv
    · injection hv with e1 e2
      subst e1 e2
      exact hb
    · exact h.2 b' n' hv

theorem trInv_loopWs {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    (lw : Array (Nat × Nat × List (Nat × Lean.Expr))) (ld : Nat)
    (hlw : ∀ x ∈ lw.toList, x.1 + x.2.1 ≤ s.kinds.size) :
    FReachC nDecl s { s with loopWs := lw, loopDepth := ld } ∧
    TrInv senv nDecl { s with loopWs := lw, loopDepth := ld } := by
  have hreach : FReachC nDecl s { s with loopWs := lw, loopDepth := ld } :=
    .ctrl (.refl s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hreach, fullInv_reachC hTr.1 hreach, ?_⟩
  obtain ⟨_, hbr, hne, hdm, hln, hgr⟩ := hTr.2
  exact ⟨hlw, hbr, hne, hdm, hln, fun k c js r h1 h2 => hgr k c js r h1 h2⟩

/-- the sharing probe of `loopRootStep`. -/
theorem loopProbe_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (body : Lean.Expr) (m : Nat) (hnb : NoPh body = true)
    (hbb : BvarLt (env.length + 1 + nDecl) body = true)
    (hreglen : ∀ regs, machLoopRegs (machLetTail body) = some regs → regs.length = m)
    (s1 : MachRead) (hst : RdOk s1) (hE : EnvOk s1.lets.size env) (hTr : TrInv senv nDecl s1)
    (hEp : EnvPh nDecl s1 env) :
    ∀ a, a ∈ s1.loopWs.toList →
      SatP (readF senv n) (fun p : Nat × MachRead => FReachC nDecl s1 p.2 ∧ TrInv senv nDecl p.2 ∧
          p.1 + m ≤ p.2.kinds.size) (loopProbe env body m s1 a) := by
  rintro ⟨b0, n0, ws0⟩ hmem
  unfold loopProbe
  dsimp only
  by_cases hc : (n0 != m) = true
  · rw [if_pos hc]
    exact satp_pure (fun a h => by cases h)
  · rw [if_neg hc]
    have hn0 : n0 = m := by simpa using hc
    have hbd : b0 + m ≤ s1.kinds.size := hn0 ▸ hTr.2.1 (b0, n0, ws0) hmem
    have hEp2 : EnvPh nDecl { s1 with ws := #[] } (MachVal.state b0 m :: env) := by
      refine ⟨fun v hv => ?_, fun b n hbn => ?_⟩
      · rcases List.mem_cons.mp hv with hv | hv
        · cases hv
        · exact hEp.1 v hv
      · rcases List.mem_cons.mp hbn with hv | hv
        · injection hv with e1 e2
          subst e1 e2
          exact hbd
        · exact hEp.2 b n hv
    have hreach0 : FReachC nDecl s1 { s1 with ws := #[] } :=
      reachC_ws s1 _ (fun w hw => by simp at hw)
    have hTr0 : TrInv senv nDecl { s1 with ws := #[] } := ⟨fullInv_reachC hTr.1 hreach0, hTr.2⟩
    refine satp_bind ?_
    intro r hr
    rcases r with _ | st'
    · exact satp_pure (fun a h => by cases h)
    · have hpre : TracePre senv nDecl (Call.loopBody b0 (MachVal.state b0 m :: env) body { s1 with ws := #[] }) :=
        ⟨⟨(adv_refl hst).1, envOk_cons hE (fun w hw => by cases hw), noPh_letOk 0 body hnb⟩,
         ⟨hTr0, hEp2, hnb, hbb, fun regs hreg => by rw [hreglen regs hreg]; exact hbd⟩⟩
      obtain ⟨_, hR', hX'⟩ := hT _ hpre st' hr
      obtain ⟨_, hi', hk'⟩ := reachC_sizes_mono (reachC_trans hreach0 hR')
      refine satp_pure ?_
      intro a ha
      dsimp only at ha
      split at ha
      · injection ha with ha
        subst ha
        have hws : ∀ w ∈ s1.ws, w.1 < st'.kinds.size ∧ InRange nDecl st' st'.lets.size w.2 := by
          intro w hw
          obtain ⟨h1, h2⟩ := hTr.1.2.1.2 w hw
          obtain ⟨hl', hi'', hk''⟩ := reachC_sizes_mono (reachC_trans hreach0 hR')
          exact ⟨Nat.lt_of_lt_of_le h1 hk'', inRange_mono h2 hi'' hk'' hl'⟩
        have hreach := reachC_trans hreach0 (reachC_trans hR' (reachC_ws st' _ hws))
        refine ⟨hreach, ⟨fullInv_reachC hTr.1 hreach, hX'.2⟩, ?_⟩
        have hk2 : s1.kinds.size ≤ st'.kinds.size := hk'
        show b0 + m ≤ st'.kinds.size
        omega
      · cases ha

theorem loopRoot_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopRoot env e st))
    (r : (Call.loopRoot env e st).Res)
    (hv : (loopRootStep senv env e st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.loopRoot env e st) r) ∧
    PhPost senv nDecl (Call.loopRoot env e st) r := by
  obtain ⟨⟨hst, hE, hl⟩, ⟨hTr, hEp, hnp, hbl⟩⟩ := hpre
  have key : SatP (readF senv n) (fun p : MachVal × MachRead => FReachC nDecl st p.2 ∧ RootPh senv nDecl p)
      (loopRootStep senv env e st) := by
    unfold loopRootStep
    split
    · rename_i dom body hview
      obtain ⟨⟨hnd, hbd⟩, ⟨hnb, hbb⟩⟩ := loopView_ph hnp hbl hview
      refine satp_ite satp_failO ?_
      refine satp_optK ?_
      intro regs hregs
      refine satp_ite satp_failO ?_
      refine satp_optK ?_
      intro kinds hkinds
      refine satp_optK ?_
      intro inits hinits
      have hlenK : kinds.length = regs.length := (mapM_len_some _ regs kinds hkinds).symm ▸ rfl
      have hbd0 : BvarLt (0 + env.length + nDecl) dom = true := by rw [Nat.zero_add]; exact hbd
      refine satp_bindO (Q := fun p : Lean.Expr × MachRead => TracePost senv nDecl (Call.conv env 0 dom st) p)
        (fun p hp => hT (Call.conv env 0 dom st) ⟨⟨hst, hE, noPh_letOk 0 dom hnd⟩, ⟨hTr, hEp, hnd, hbd0⟩⟩ p hp) ?_
      rintro ⟨dom', s1⟩ ⟨hP1, hR1, hX1⟩
      have h1' : Adv st s1 := hP1.1
      have hd'' : LetOk s1.lets.size dom' = true := hP1.2
      refine satp_domGuard ?_
      dsimp only
      have hbb' : BvarLt (env.length + 1 + nDecl) body = true := by rw [Nat.add_right_comm]; exact hbb
      have hreglen : ∀ regs', machLoopRegs (machLetTail body) = some regs' → regs'.length = kinds.length := by
        intro regs' hr'
        rw [hregs] at hr'
        injection hr' with hr'
        subst hr'
        exact hlenK.symm
      refine satp_bind ?_
      intro shared hsh
      rcases shared with _ | ⟨b0, st2⟩
      · dsimp only
        have hpl : FReachC nDecl s1 (loopNewSt s1 kinds inits dom') ∧ TrInv senv nDecl (loopNewSt s1 kinds inits dom') :=
          trInv_pushLoop hX1.1 hX1.2.1 hX1.2.2 kinds inits _ _ _ _
        have hbase : s1.kinds.size + kinds.length ≤ (loopNewSt s1 kinds inits dom').kinds.size := by
          show _ ≤ (s1.kinds ++ kinds.toArray).size
          simp [Array.size_append]
        have hpre2 : TracePre senv nDecl (Call.loopBody s1.kinds.size (MachVal.state s1.kinds.size kinds.length :: env) body
            (loopNewSt s1 kinds inits dom')) :=
          ⟨⟨rdOk_dom h1'.1 rfl rfl rfl hd'', envOk_cons (envOk_mono h1'.2 hE) (fun w hw => by cases hw),
            noPh_letOk 0 body hnb⟩,
           ⟨hpl.2, envPh_cons_state (envPh_mono hEp (reachC_trans hR1 hpl.1)) hbase, hnb, hbb',
            fun regs' hreg => by rw [hreglen regs' hreg]; exact hbase⟩⟩
        refine satp_bindO (Q := fun st3 : MachRead => TracePost senv nDecl
            (Call.loopBody s1.kinds.size (MachVal.state s1.kinds.size kinds.length :: env) body
              (loopNewSt s1 kinds inits dom')) st3)
          (fun p hp => hT _ hpre2 p hp) ?_
        rintro st3 ⟨hP3, hR3, hX3⟩
        obtain ⟨_, _, hk3⟩ := reachC_sizes_mono hR3
        have hb3 : s1.kinds.size + kinds.length ≤ st3.kinds.size := Nat.le_trans hbase hk3
        have hlw : ∀ x ∈ (st3.loopWs.push (s1.kinds.size, kinds.length,
            st3.ws.toList.drop (loopNewSt s1 kinds inits dom').ws.size)).toList, x.1 + x.2.1 ≤ st3.kinds.size := by
          intro x hx
          rw [Array.toList_push] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hX3.2.1 x hx
          · rw [List.mem_singleton.mp hx]
            exact hb3
        obtain ⟨hrW, hTW⟩ := trInv_loopWs hX3 _ s1.loopDepth hlw
        refine satp_okO ⟨reachC_trans hR1 (reachC_trans hpl.1 (reachC_trans hR3 hrW)), hTW,
          fun b n' hbn => ?_, fun v hv' => by cases hv'⟩
        injection hbn with e1 e2
        subst e1 e2
        exact hb3
      · have hP := satp_findSomeO (P := fun p : Nat × MachRead => FReachC nDecl s1 p.2 ∧ TrInv senv nDecl p.2 ∧
            p.1 + kinds.length ≤ p.2.kinds.size) s1.loopWs.toList
          (loopProbe_trace senv nDecl n hT env body kinds.length hnb hbb' hreglen s1 h1'.1
            (envOk_mono h1'.2 hE) hX1.1 (envPh_mono hEp hR1)) (b0, st2) hsh
        refine satp_okO ?_
        refine ⟨reachC_trans hR1 hP.1, hP.2.1, fun b n' hbn => ?_, fun v hv' => by cases hv'⟩
        injection hbn with e1 e2
        subst e1 e2
        exact hP.2.2
    · exact satp_failO
  exact ⟨(key r hv).1, (key r hv).2⟩

end Tools.ShippingGen5ReaderTrace
