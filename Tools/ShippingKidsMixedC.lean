import Tools.ShippingMemKidFacts
import Tools.ConeFoldMem
-- WRITTEN, NOT BUILT (round par/o-gchk, unit "comb disjunct").

/-! # The depth-0 children bound with a COMBINATIONAL disjunct (round par/o-gchk)

The depth-0 route's children bound `kidsMixed` (`Tools.ShippingMachineShipsHier`) asks of
every instance's child: masked outputs and no memory (`kidsMasked`), or the built memory module
(`kidsMem`). A GATE child (the unified mixed gate's module) is neither: its output is driven by
`assign "out" (.ref w)` (`Sparkle.Compiler.Elab.emitLeaves`), not by a constant or a slice. So
`kidsMixed` is false at a parent that instantiates one, and every endpoint stated under it is
vacuous.

Here the bound gets a THIRD disjunct, `combAt`: the child has no memory and each output port
`p` is reached by a CHAIN — some statement `w := e` with `e` SELF-BOUNDED (`selfBounded`: a
constant, a slice, or a two-operand masked operator `and/or/xor/add/sub/mul/shl`, whose every
value is below `2 ^ widthOf`), `widthOf e ≤ p`'s width, followed (in the statements after it)
by exactly one write of `p.name`, namely `p.name := w`, and no write of `w`. The gate route
emits exactly that for a binary operator at the top of the term (`Elab.lean`, the binary
operator arm: `emitAssign resWire (.op op [.ref a, .ref b])`, then `out := ref resWire`).

* `selfBounded_lt` — a self-bounded expression's value is below `2 ^ widthOf` in EVERY
  environment (the per-operator lemmas of `Tools.ConeFoldMem`);
* `evalAssigns_ref_final` — after a fold in which `o` is written once, by `o := w`, and `w` is
  not written, `o` holds `w`'s value at the START of the fold;
* `combChain_bound` — the chain bounds the output in every environment;
* `kidsMixedC`, `mixCKS_boundedIn` — the three-way bound and its `KSBoundedIn` under `flatKS`
  with the SAME invariant `mixInv` (a combinational child has no memory, so `mixInv` is
  vacuous for it), i.e. a drop-in `Bd` / `hBd` for the depth-0 heads;
* `kidsMixedC_of`, `combAt_one`, `core_kidsMixedCMT` — the run-level derivation, from one fact
  per kid (`FlatOk` or `combOk`), as `core_kidsMixedMT`.

No new fact about the compiler is assumed; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingKidsMixedC
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto
open Tools.ShippingChildInv
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingHierOptRun (KSBoundedIn)
open Tools.ShippingMachineShipsHier (kidsMasked kidsMem mixInv noMem)

/-! ## Self-bounded expressions -/

/-- The masked two-operand operators. -/
def maskedOp : Operator → Bool
  | .and | .or | .xor | .add | .sub | .mul | .shl => true
  | _ => false

/-- An expression whose every value is below `2 ^ widthOf`, whatever the environment. -/
def selfBounded : Sparkle.IR.AST.Expr → Bool
  | .const .. => true
  | .slice .. => true
  | .op o [_, _] => maskedOp o
  | _ => false

theorem selfBounded_lt (we : WEnv) (env : Env) :
    ∀ (e : Sparkle.IR.AST.Expr) (v : Nat), selfBounded e = true → evalExpr we env e = some v →
      v < 2 ^ widthOf we e
  | .const c w, v, _, hv => Tools.ConeFold.evalExpr_bounded_const we env c w v hv
  | .slice x hi lo, v, _, hv => Tools.ConeFold.evalExpr_bounded_slice we env x hi lo v hv
  | .op o [a, b], v, h, hv => by
    have hm : maskedOp o = true := h
    simp only [evalExpr, Option.bind_eq_bind] at hv
    cases hl : evalList we env [a, b] with
    | none => rw [hl] at hv; simp at hv
    | some vals =>
      rw [hl] at hv
      simp only [Option.bind_some] at hv
      have hlen := Tools.ConeFold.evalList_len hl
      rcases vals with _ | ⟨va, _ | ⟨vb, _ | ⟨vc, rest⟩⟩⟩
      · simp at hlen
      · simp at hlen
      · cases o <;> simp only [maskedOp, Bool.false_eq_true] at hm <;> first
          | exact Tools.ConeFold.evalOp_bounded_and we a b va vb v hv
          | exact Tools.ConeFold.evalOp_bounded_or we a b va vb v hv
          | exact Tools.ConeFold.evalOp_bounded_xor we a b va vb v hv
          | exact Tools.ConeFold.evalOp_bounded_add we a b va vb v hv
          | exact Tools.ConeFold.evalOp_bounded_sub we a b va vb v hv
          | exact Tools.ConeFold.evalOp_bounded_mul we a b va vb v hv
          | exact Tools.ConeFold.evalOp_bounded_shl we a b va vb v hv
      · simp at hlen
  | .ref _, _, h, _ => by simp [selfBounded] at h
  | .op _ [], _, h, _ => by simp [selfBounded] at h
  | .op _ [_], _, h, _ => by simp [selfBounded] at h
  | .op _ (_ :: _ :: _ :: _), _, h, _ => by simp [selfBounded] at h
  | .concat _, _, h, _ => by simp [selfBounded] at h
  | .sliceDim _ _ _, _, h, _ => by simp [selfBounded] at h
  | .index _ _, _, h, _ => by simp [selfBounded] at h

/-! ## The chain -/

/-- The wire an expression reads when it is a bare reference. -/
def refOf? : Sparkle.IR.AST.Expr → Option String
  | .ref w => some w
  | _ => none

/-- `s` is `o := w` (a bare reference). -/
def isRefAssign (o w : String) (s : Stmt) : Bool :=
  match s with
  | .assign o' e => o' == o && refOf? e == some w
  | _ => false

theorem isRefAssign_eq {o w : String} {s : Stmt} (h : isRefAssign o w s = true) :
    s = .assign o (.ref w) := by
  cases s with
  | assign o' e =>
    simp only [isRefAssign, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    cases e <;> simp_all [refOf?]
  | _ => simp [isRefAssign] at h

theorem mem_of_refAny {o w : String} {rest : List Stmt} (h : rest.any (isRefAssign o w) = true) :
    Stmt.assign o (.ref w) ∈ rest := by
  obtain ⟨s, hs, hk⟩ := List.any_eq_true.mp h
  rw [← isRefAssign_eq hk]
  exact hs

/-- `p.name` (`o`, of width `k`) is reached by a chain: some `w := e`, `e` self-bounded within
`k`, followed by exactly one write of `o`, namely `o := w`, and no write of `w`. -/
def combChain (we : WEnv) (k : Nat) (o : String) : List Stmt → Bool
  | [] => false
  | st :: rest =>
    (match st with
      | .assign w e => selfBounded e && decide (widthOf we e ≤ k) &&
          decide (w ∉ Sparkle.IR.Reorder.writesOf rest) &&
          (Sparkle.IR.Reorder.writesOf rest).count o == 1 &&
          rest.any (isRefAssign o w)
      | _ => false) || combChain we k o rest

theorem writes_cons_mem {st : Stmt} {rest : List Stmt} {x : String}
    (h : x ∈ Sparkle.IR.Reorder.writesOf rest) : x ∈ Sparkle.IR.Reorder.writesOf (st :: rest) := by
  unfold Sparkle.IR.Reorder.writesOf at h ⊢
  obtain ⟨s, hs, hx⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨s, List.mem_cons_of_mem _ hs, hx⟩

theorem writes_head_assign {l : String} {r : Sparkle.IR.AST.Expr} {rest : List Stmt} :
    l ∈ Sparkle.IR.Reorder.writesOf (Stmt.assign l r :: rest) := by
  unfold Sparkle.IR.Reorder.writesOf
  exact List.mem_flatMap.mpr ⟨_, List.mem_cons_self, by simp [Sparkle.IR.Reorder.stmtWrites]⟩

/-- **After a fold writing `o` once, by `o := w`, and not writing `w`, `o` holds `w`'s start
value.** -/
theorem evalAssigns_ref_final (we : WEnv) (mems : MEnv) {o w : String} :
    ∀ (body : List Stmt) (env0 env1 : Env), evalAssigns we mems body env0 = some env1 →
      Tools.ConeFold.memFree body → Stmt.assign o (.ref w) ∈ body →
      (Sparkle.IR.Reorder.writesOf body).count o = 1 →
      w ∉ Sparkle.IR.Reorder.writesOf body → env1 o = env0 w
  | [], _, _, _, _, hm, _, _ => by cases hm
  | st :: rest, env0, env1, h, hmf, hm, hc, hw => by
    have hmf' : Tools.ConeFold.memFree rest := by
      cases st <;> simp_all [Tools.ConeFold.memFree]
    have hw' : w ∉ Sparkle.IR.Reorder.writesOf rest := fun hx => hw (writes_cons_mem hx)
    cases st with
    | assign l r =>
      simp only [evalAssigns] at h
      cases hv : evalExpr we env0 r with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        have hcount : (Sparkle.IR.Reorder.writesOf (Stmt.assign l r :: rest)).count o =
            (if l = o then 1 else 0) + (Sparkle.IR.Reorder.writesOf rest).count o := by
          simp only [Sparkle.IR.Reorder.writesOf, List.flatMap_cons, Sparkle.IR.Reorder.stmtWrites,
            List.count_append, List.count_singleton]
          by_cases he : l = o <;> simp [he, beq_iff_eq]
        rw [hcount] at hc
        have hwl : w ≠ l := fun e => hw (by rw [e]; exact writes_head_assign)
        by_cases he : l = o
        · subst he
          have h0 : (Sparkle.IR.Reorder.writesOf rest).count l = 0 := by simp at hc; omega
          have hnot : l ∉ Sparkle.IR.Reorder.writesOf rest := List.count_eq_zero.mp h0
          rcases List.mem_cons.mp hm with heq | hin
          · cases heq
            rw [Tools.ConeFold.evalAssigns_frame we mems rest _ env1 h hmf' l hnot]
            simp only [evalExpr, Option.some.injEq] at hv
            simp [hv]
          · exfalso
            apply hnot
            unfold Sparkle.IR.Reorder.writesOf
            exact List.mem_flatMap.mpr ⟨_, hin, by simp [Sparkle.IR.Reorder.stmtWrites]⟩
        · simp only [he, if_false, Nat.zero_add] at hc
          rcases List.mem_cons.mp hm with heq | hin
          · cases heq; exact absurd rfl he
          · rw [evalAssigns_ref_final we mems rest _ env1 h hmf' hin hc hw']
            simp [hwl]
    | register o' c rk i iv =>
      simp only [evalAssigns] at h
      rcases List.mem_cons.mp hm with heq | hin
      · cases heq
      · exact evalAssigns_ref_final we mems rest env0 env1 h hmf'
          hin (by simpa [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites] using hc) hw'
    | inst mn iname conns =>
      simp only [evalAssigns] at h
      rcases List.mem_cons.mp hm with heq | hin
      · cases heq
      · exact evalAssigns_ref_final we mems rest env0 env1 h hmf'
          hin (by simpa [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites] using hc) hw'
    | memory nm aw dw c wa wd wen ra rd cr ew er => simp [Tools.ConeFold.memFree] at hmf

/-- **The chain bounds the output, in every start environment.** -/
theorem combChain_bound (we : WEnv) (mems : MEnv) {k : Nat} {o : String} :
    ∀ (body : List Stmt) (env0 envF : Env), evalAssigns we mems body env0 = some envF →
      Tools.ConeFold.memFree body → combChain we k o body = true → envF o < 2 ^ k
  | [], _, _, _, _, hc => by simp [combChain] at hc
  | st :: rest, env0, envF, h, hmf, hc => by
    have hmf' : Tools.ConeFold.memFree rest := by
      cases st <;> simp_all [Tools.ConeFold.memFree]
    cases st with
    | assign l r =>
      simp only [evalAssigns] at h
      cases hv : evalExpr we env0 r with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        simp only [combChain, Bool.or_eq_true] at hc
        rcases hc with hh | hr
        · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hh
          obtain ⟨⟨⟨⟨hsb, hwk⟩, hnw⟩, hco⟩, hmem⟩ := hh
          rw [evalAssigns_ref_final we mems rest _ envF h hmf' (mem_of_refAny hmem) hco hnw]
          show (if l = l then v else env0 l) < 2 ^ k
          rw [if_pos rfl]
          exact Nat.lt_of_lt_of_le (selfBounded_lt we env0 r v hsb hv)
            (Nat.pow_le_pow_right (by omega) hwk)
        · exact combChain_bound we mems rest _ envF h hmf' hr
    | register o' c rk i iv =>
      simp only [evalAssigns] at h
      simp only [combChain, Bool.or_eq_true, Bool.false_eq_true, false_or] at hc
      exact combChain_bound we mems rest env0 envF h hmf' hc
    | inst mn iname conns =>
      simp only [evalAssigns] at h
      simp only [combChain, Bool.or_eq_true, Bool.false_eq_true, false_or] at hc
      exact combChain_bound we mems rest env0 envF h hmf' hc
    | memory nm aw dw c wa wd wen ra rd cr ew er => simp [Tools.ConeFold.memFree] at hmf

/-! ## The three-way children bound -/

/-- A combinational child: no memory, every output reached by a chain. -/
def combOk (c : Sparkle.IR.AST.Module) (cwe : WEnv) : Bool :=
  noMem c.body && c.outputs.all fun p => combChain cwe p.ty.bitWidth p.name c.body

/-- The comb disjunct at one statement. -/
def combAt (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (st : Stmt) : Bool :=
  match st with
  | .inst mn _ _ => match children mn with
    | some (c, cwe) => combOk c cwe
    | none => false
  | _ => true

/-- **The depth-0 children bound with three disjuncts**: masked, memory, combinational. -/
def kidsMixedC (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (body : List Stmt) : Bool :=
  body.all fun st => kidsMasked children [st] || kidsMem children [st] || combAt children st

/-- **Masked, memory and combinational children keep their outputs within their ports' widths**
(`mixKS_boundedIn` with the third case), under `flatKS` and the same invariant `mixInv`. -/
theorem mixCKS_boundedIn (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (body : List Stmt) (hok : kidsMixedC children body = true) :
    KSBoundedIn children Tools.ShippingHierStateG.flatKS body mixInv := by
  intro mn iname conns hmem child cwe hc env s cres s' hinv hk
  have h1 := List.all_eq_true.mp hok _ hmem
  simp only [Bool.or_eq_true] at h1
  rcases h1 with (hs | hm) | hcomb
  · obtain ⟨hb, -⟩ := Tools.ShippingMachineShipsHier.flatKS_boundedIn children _ hs mn iname conns
      List.mem_cons_self child cwe hc env s cres s' trivial hk
    refine ⟨hb, fun hp => ?_⟩
    have h2 := List.all_eq_true.mp hs _ List.mem_cons_self
    simp only [hc, Bool.and_eq_true] at h2
    rw [Tools.ShippingMachineShipsHier.memParams_noMem h2.1] at hp
    cases hp
  · have hmp : (Sparkle.Compiler.MachMemory.memParams? child).isSome = true := by
      have h2 := List.all_eq_true.mp hm _ List.mem_cons_self
      simp only [Bool.and_eq_true] at h2
      rw [hc] at h2
      simp only at h2
      cases hp : Sparkle.Compiler.MachMemory.memParams? child with
      | none => rw [hp] at h2; simp at h2
      | some _ => rfl
    obtain ⟨hb, hi⟩ := Tools.ShippingMachineShipsHier.memKS_boundedIn children _ hm mn iname conns
      List.mem_cons_self child cwe hc env s cres s' (hinv hmp) hk
    exact ⟨hb, fun _ => hi⟩
  · have hco : combOk child cwe = true := by
      simp only [combAt, hc] at hcomb
      exact hcomb
    unfold combOk at hco
    rw [Bool.and_eq_true] at hco
    obtain ⟨hnm, hch⟩ := hco
    refine ⟨fun p hp => ?_, fun hp => ?_⟩
    · simp only [Tools.ShippingHierStateG.flatKS] at hk
      cases hst : stepModule cwe child.body
          (Tools.ShippingHierarchySoundness.connEnvS (Tools.ShippingHierState.inConns child.outputs conns)
            env s.st) s.mems with
      | none => simp [hst] at hk
      | some r =>
        simp only [hst, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨envF, nexts, mems', hF, -, -, rfl⟩ := Tools.ShippingHierState.stepModule_some hst
        obtain ⟨rfl, -⟩ := hk
        exact combChain_bound cwe s.mems child.body _ envF hF
          (Tools.ShippingMachineShipsHier.memFree_of_noMem hnm) (List.all_eq_true.mp hch p hp)
    · rw [Tools.ShippingMachineShipsHier.memParams_noMem hnm] at hp
      cases hp

/-! ## The run-level derivation -/

/-- One instance whose child is combinational. -/
theorem combAt_one {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)}
    {child : Sparkle.IR.AST.Module} {cwe : WEnv}
    (hc : C mn = some (child, cwe)) (h : combOk child cwe = true) :
    combAt C (Stmt.inst mn iname conns) = true := by
  simp [combAt, hc, h]

/-- **`kidsMixedC` from one fact per instance statement.** -/
theorem kidsMixedC_of {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {body : List Stmt}
    (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
      (kidsMasked C [Stmt.inst mn iname conns] = true ∨
        kidsMem C [Stmt.inst mn iname conns] = true) ∨
      combAt C (Stmt.inst mn iname conns) = true) :
    kidsMixedC C body = true := by
  unfold kidsMixedC
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    rw [Bool.or_eq_true, Bool.or_eq_true]
    exact h mn iname conns hst
  | _ => simp [kidsMasked]

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

set_option maxHeartbeats 4000000 in
/-- **`kidsMixedC` of a machine tied by the general closing, on the core run's design**
(`core_kidsMixedMT` with the third disjunct), from one fact per kid: `FlatOk` (masked or the
built memory module) or `combOk` at the module's own width table. -/
theorem core_kidsMixedCMT {c : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidF : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ combOk y.1 (Sparkle.IR.RegDedup.declWidth y.1) = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    kidsMixedC (childMap D.modules) b.body = true := by
  have hst := Tools.ShippingMemKid.core_callStmtMT d ok hbody hC hslots hdomB hins hfne outTy hB
    hcore hpost entry closes
  refine kidsMixedC_of fun mn iname conns hm => ?_
  obtain ⟨mc, hmc, ⟨k, hk, y, hre, hmcy⟩, nIn, kI, n, names, args, outs, hcs⟩ :=
    hst mn iname conns hm
  have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
    congrArg (fun o : Option Sparkle.IR.AST.Module =>
      o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
  rcases hkidF k hk y hre with (⟨h1, h2⟩ | ⟨cb, aw, dw, hmem⟩) | hcomb
  · left; left
    rw [← hmcy] at h1 h2
    exact Tools.ShippingMemKid.kidsMasked_one hCm h1 h2
  · left; right
    rw [← hmcy] at hmem
    rw [hmem] at hcs hCm
    exact Tools.ShippingMemKid.kidsMem_one hCm (Tools.ShippingMemKid.mem_conns_noRdata hcs)
  · right
    rw [← hmcy] at hcomb
    exact combAt_one hCm hcomb

end Tools.ShippingKidsMixedC
