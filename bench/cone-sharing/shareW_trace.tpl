set_option maxHeartbeats 4000000 in
theorem trace (i : Signal defaultDomain (BitVec 8)) (t : Nat) :
    ((shareX{n} i).val t).toNat =
      (Sparkle.IR.Semantics.evalExpr (weOfC nm (fun k => (([8] ++ [8]) ++ GW : List Nat).get k))
          (envOfC nm (natJoin
            (natJoin (CdoW.irState deep nm (fun t j => (inp i j).val t) t)
              (fun j => ((inp i j).val t).toNat))
            (CdoW.irWires deep nm (natJoin (CdoW.irState deep nm (fun t j => (inp i j).val t) t)
              (fun j => ((inp i j).val t).toNat)))))
          (CExpr.compile nm (CdoW.out deep))).getD 0 := by
  rw [← CdoW.elab_general deep nm (by decide) (inp i) t]
  refine congrArg BitVec.toNat ?_
  simp -zeta only [shareX{n}]
  rw [runCircuitH_eq]
  simp -zeta only [outFOf, mkHolds, Signal.map, sigval_add, sigval_xor]
  generalize hL : Signal.loop (loopFOf (dom := Sparkle.Core.Domain.defaultDomain) (αs := [BitVec 8]) (ρ := Signal defaultDomain (BitVec 8)) _ _) = L
  have hLt : ∀ (u : Nat), L.val u = (rd0 i u, ()) := by
    intro u
    rw [← hL]
    refine loop_trace_at _ (fun s => (rd0 i s, ())) ?_ u
    intro u pre hpre
    cases u with
    | zero =>
      simp -zeta [loopFOf, packRegister, Signal.register, Signal.memStep, Circuit.next, Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux, bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq, inp_at_0, inp_at_mk_0]
      all_goals (try simp only [rd0_zero])
      all_goals first | rfl | bv_decide | (simp; done) | (trace_state; sorry)
    | succ m =>
      simp [loopFOf, packRegister, Signal.register, Signal.memStep, Circuit.next, Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux, bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq, sigval_add, sigval_xor, inp_at_0, inp_at_mk_0, hpre m (Nat.lt_succ_self m)]
      all_goals (try simp only [rd0_succ])
      -- IR-side wire equations as HYPOTHESES (never rewritten in):
      -- bv_decide sees rw_k i m and rd0 i m as atoms and bitblasts the
      -- conjunction linearly
      WIREHYPS_M
      all_goals first | bv_decide | (trace_state; sorry)
  rw [outS]
  simp only [Signal.map, sigval_add, sigval_xor, hLt]
  WIREHYPS_T
  all_goals first | bv_decide | (trace_state; sorry)

#print axioms trace
