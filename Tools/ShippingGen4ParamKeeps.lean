import Tools.ShippingChildBalance
import Tools.ShippingChildBody
import Tools.ShippingGen4ParamEntry
set_option autoImplicit false
-- BUILT: clean issue-linked build par6v-41ad0be7 (Tests.Gen4.ParamIfaceCheck) exit 0, 705 jobs, at 41ad0be7. Comment-only update.

/-! # M4 parametric entry, rev4 §11.2: I3c for the OUTERMOST symbolic run (scripts/gen4/PARAMETRIC_FREEZE.md)

The symbolic analogue of `body_keeps` / `core_keeps` / `core_triple0` / `core_balance` (Tools/ShippingChildBody,
ShippingChildKeeps, ShippingChildBalance), under the same `RefLaws` witness `L` (no new law, no new RefLaws field).
SCOPE (as proposed in the freeze): the run is OUTERMOST (depth 0) for the world/balance statements; the keeps
statements are for general depth `D`. NOT claimed: equality of the seven side-map CONTENTS between `w` and `w'` for a
nested symbolic run; a symbolic run at depth >= 1; `LimitStmt` for symbolic flags. -/

namespace Tools.ShippingGen4ParamKeeps
open Lean Meta Tools.ShippingEntrySoundness Tools.ShippingChildInv Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBalance
open Tools.ShippingGen4ParamEntry (Tsyn entryConst_off)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}


/-! ## The symbolic body -/

theorem bindInputsLegacy_sym_keepsC (L : RefLaws mref cref) (D : Nat)
    (parameters : List (String × Nat)) (symbolicMode : Bool)
    (xs : Array Lean.Expr) (k : CompilerM String)
    (hk : KeepsC mctx mref cctx cref (J L D) k) :
    ∀ (n i : Nat), xs.size - i < n →
      KeepsC mctx mref cctx cref (J L D) (bindInputsLegacy parameters symbolicMode xs i k)
  | 0, _, h => by omega
  | n + 1, i, h => by
    have ih := fun (h' : xs.size - (i + 1) < n) =>
      bindInputsLegacy_sym_keepsC L D parameters symbolicMode xs k hk n (i + 1) h'
    unfold bindInputsLegacy
    vc

theorem body_symbolic_keeps (L : RefLaws mref cref) (D : Nat) (hC : ChildKeeps L D)
    (b : Bool) (declName : Name) (parameters : List (String × Nat))
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {tenv : Lean.Environment} :
    Keeps mctx mref cctx cref (J L D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName parameters true true ci isInst) := by
  have hb := fun (mctx : Meta.Context) (cctx : Core.Context) (xs : Array Lean.Expr) i (k : CompilerM String)
      (hk : KeepsC mctx mref cctx cref (J L D) k) =>
    bindInputsLegacy_sym_keepsC L D parameters true xs k hk (xs.size - i + 1) i (Nat.lt_succ_self _)
  vc

/-! ## The prologue (duplicate / zero parameter checks) keeps any invariant that survives `throwError` -/

theorem Triple.forIn_list {α β : Type} {P : Void IO.RealWorld → Prop}
    {R : Exception → Void IO.RealWorld → Prop}
    (f : α → β → MetaM (ForInStep β))
    (hf : ∀ a b, Triple mctx mref cctx cref P (f a b) (fun _ => P) R) :
    ∀ (l : List α) (b : β), Triple mctx mref cctx cref P (forIn l b f) (fun _ => P) R
  | [], b => by
    rw [List.forIn_nil]
    exact Triple.pure fun w hw => hw
  | a :: l, b => by
    rw [List.forIn_cons]
    refine Triple.bind (hf a b) (fun r => ?_)
    cases r with
    | done b' => exact Triple.pure fun w hw => hw
    | yield b' => exact Triple.forIn_list f hf l b'

/-- The prologue of the symbolic core, from the invariant `J L D`: the duplicate check throws (the rest of the
run is then not reached: its postcondition is `False`), the per-parameter zero check throws, otherwise the run
continues unchanged.  The `then` branch of the source `if` repeats the rest of the run after the throw; it is
discharged by `False.elim`, so the rest is proved once, in the `else` branch. -/
macro "pro_split_J " L:term:max D:term:max : tactic => `(tactic|
  (refine Triple.ite (fun _ => ?_) (fun _ => ?_)
   · refine Triple.bind (Q := fun _ _ => False)
       (Triple.throwErr $L _ (by first | exact .str _ | exact .fmt _) $D) ?_
     intro _ w hf
     exact hf.elim
   refine Triple.bind (Triple.forIn_list _ (fun a b => ?_) _ _) (fun _ => ?rest)
   · rcases a with ⟨nm, dv⟩
     dsimp only
     refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
     refine Triple.bind (Q := fun _ _ => False)
       (Triple.throwErr $L _ (by first | exact .str _ | exact .fmt _) $D) ?_
     intro _ w hf
     exact hf.elim))

macro "pro_split_O " L:term:max : tactic => `(tactic|
  (refine Triple.ite (fun _ => ?_) (fun _ => ?_)
   · refine Triple.bind (Q := fun _ _ => False)
       (tripleO_throwErr $L _ (by first | exact .str _ | exact .fmt _)) ?_
     intro _ w hf
     exact hf.elim
   refine Triple.bind (Triple.forIn_list _ (fun a b => ?_) _ _) (fun _ => ?rest)
   · rcases a with ⟨nm, dv⟩
     dsimp only
     refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
     refine Triple.bind (Q := fun _ _ => False)
       (tripleO_throwErr $L _ (by first | exact .str _ | exact .fmt _)) ?_
     intro _ w hf
     exact hf.elim))

/-! ## The symbolic core, keeps at depth `D` -/

theorem core_symbolic_keeps (L : RefLaws mref cref) (D : Nat) (declName : Name)
    (parameters : List (String × Nat)) (hA0 : D = 0 → L.aux {})
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (J L (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName parameters true true ci isInst)) :
    Keeps mctx mref cctx cref (J L D)
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true) := by
  rw [keeps_iff]
  unfold synthesizeCombinationalCoreWith
  simp only [↓reduceIte, eq_self_iff_true, if_true]
  pro_split_J L D
  refine Triple.bind (Triple.frame L (Framed.ioEnv _) D) ?_
  intro prof
  refine Triple.bind (Triple.diag L (Diag.profLog prof.isSome _) D) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = D)
    (Triple.frameQ L Framed.depthGet D fun w d w' hw h => by rw [L.depthGet _ _ _ h]; exact hw.2.1) ?_
  intro d hd
  subst hd
  refine Triple.ite (fun _ => ?_) (fun hlt => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (Triple.throwErr L _ (by first | exact .str _ | exact .fmt _) d) ?_
    intro _ w hf
    exact hf.elim
  · have hlt : d < sparkleSynthDepthLimit := Nat.lt_of_not_ge hlt
    have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
        (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
        (m7 : Std.HashMap String String),
        Triple mctx mref cctx cref (J L (d + 1))
          (_root_.tryFinally
            (do
              let constInfo ← getConstInfo declName
              let env ← getEnv
              synthesizeFromConst (fun e h t n => translateExprToWire env e h t n)
                (profLogIO prof.isSome) declName parameters true true
                (entryConst true true parameters constInfo (instancePredicate env) (userInliner env)
                  (structEnv env))
                (instancePredicate env))
            (do
              ST.Ref.modify sparkleSynthDepth fun x => x - 1
              if (d != 0) = true then do
                  ST.Ref.set sparkleFvarValueMap m1
                  ST.Ref.set sparkleWireWidthCache m2
                  ST.Ref.set sparkleLetWireCache m3
                  ST.Ref.set sparkleLoopWireCache m4
                  ST.Ref.set sparkleWireCanon m5
                  ST.Ref.set sparkleSubInstanceOutputs m6
                  ST.Ref.set sparkleSingleOutInstanceCache m7
                else pure () : MetaM Unit))
          (fun _ => J L d) (JE L d) := by
      intro m1 m2 m3 m4 m5 m6 m7
      refine Triple.tryFinally (M := J L (d + 1)) (E := OkExc) ?_
        (fin_triple L d d m1 m2 m3 m4 m5 m6 m7)
      refine Triple.bind (Triple.frame L (Framed.constInfo _) (d + 1)) ?_
      intro ci
      refine Triple.bind (Triple.frame L Framed.env (d + 1)) ?_
      intro env
      exact keeps_iff.mp (hbody hlt prof.isSome _ _)
    by_cases h0 : (d == 0) = true
    · simp only [h0, ↓reduceIte]
      tpure L d; tpure L d; tpure L d; tpure L d; tpure L d; tpure L d; tpure L d
      tset L d; tset L d; tset L d; tset L d
      refine Triple.bind (Triple.clear L d (hA0 (by simpa using h0))) ?_
      intro _
      tset L d; tset L d; tset L d; tset L d; tset L d; tset L d; tset L d
      refine Triple.bind (Triple.depthSet L d (d + 1)) ?_
      intro _
      exact body _ _ _ _ _ _ _
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      tget L d; tget L d; tget L d; tget L d; tget L d; tget L d; tget L d
      tset L d; tset L d; tset L d; tset L d; tset L d; tset L d; tset L d
      refine Triple.bind (Triple.depthSet L d (d + 1)) ?_
      intro _
      exact body _ _ _ _ _ _ _

/-! ## The symbolic core from an outermost world -/

theorem core_symbolic_triple0 (L : RefLaws mref cref) (hA : L.aux {}) (declName : Name)
    (parameters : List (String × Nat)) :
    Triple mctx mref cctx cref (Out0 L)
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
      (fun _ => Out0 L) (E0 L) := by
  unfold synthesizeCombinationalCoreWith
  simp only [↓reduceIte]
  pro_split_O L
  refine Triple.bind (tripleO_op L (.framed (Framed.ioEnv _))) ?_
  intro prof
  refine Triple.bind (tripleO_op L (.diag (Diag.profLog prof.isSome _))) ?_
  intro _
  refine Triple.bindQ (φ := fun d => d = 0)
    (tripleO_frameQ L Framed.depthGet fun w d w' hw h => by
      rw [L.depthGet _ _ _ h]; exact hw.2.2) ?_
  intro d hd
  have body : ∀ (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
      (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
      (m7 : Std.HashMap String String),
      Triple mctx mref cctx cref (J L (d + 1))
        (_root_.tryFinally
          (do
            let constInfo ← getConstInfo declName
            let env ← getEnv
            synthesizeFromConst (fun e h t n => translateExprToWire env e h t n)
              (profLogIO prof.isSome) declName parameters true true
              (entryConst true true parameters constInfo (instancePredicate env) (userInliner env)
                (structEnv env))
              (instancePredicate env))
          (do
            ST.Ref.modify sparkleSynthDepth fun x => x - 1
            if (d != 0) = true then do
                ST.Ref.set sparkleFvarValueMap m1
                ST.Ref.set sparkleWireWidthCache m2
                ST.Ref.set sparkleLetWireCache m3
                ST.Ref.set sparkleLoopWireCache m4
                ST.Ref.set sparkleWireCanon m5
                ST.Ref.set sparkleSubInstanceOutputs m6
                ST.Ref.set sparkleSingleOutInstanceCache m7
              else pure () : MetaM Unit))
        (fun _ => J L d) (JE L d) := by
    intro m1 m2 m3 m4 m5 m6 m7
    refine Triple.tryFinally (M := J L (d + 1)) (E := OkExc) ?_
      (fin_triple L d d m1 m2 m3 m4 m5 m6 m7)
    refine Triple.bind (Triple.frame L (Framed.constInfo _) (d + 1)) ?_
    intro ci
    refine Triple.bind (Triple.frame L Framed.env (d + 1)) ?_
    intro env
    have hC : ChildKeeps L (d + 1) := childKeeps L (d + 1) (fun h => absurd h (Nat.succ_ne_zero _))
    exact keeps_iff.mp (body_symbolic_keeps L (d + 1) hC prof.isSome declName parameters _ _)
  refine Triple.ite (fun _ => ?_) (fun _ => ?_)
  · refine Triple.bind (Q := fun _ _ => False)
      (tripleO_throwErr L _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  · have h0 : (d == 0) = true := by subst hd; first | rfl | decide | simp
    simp only [h0, ↓reduceIte]
    bpure0 L; bpure0 L; bpure0 L; bpure0 L; bpure0 L; bpure0 L; bpure0 L
    bset0 L; bset0 L; bset0 L; bset0 L
    refine Triple.bind (tripleO_clear L hA d hd) ?_
    intro _
    refine Triple.conseq (P := J L d) (Q := fun _ => J L d) (R := JE L d) ?_
      (fun _ h => h) (fun _ _ h => out0_of_J L hd h) (fun _ _ h => ⟨out0_of_J L hd h.1, h.2⟩)
    tset L d; tset L d; tset L d; tset L d; tset L d; tset L d; tset L d
    refine Triple.bind (Triple.depthSet L d (d + 1)) ?_
    intro _
    exact body _ _ _ _ _ _ _

theorem core_symbolic_balance (L : RefLaws mref cref) (declName : Name)
    (parameters : List (String × Nat)) {w : Void IO.RealWorld}
    (hs : StartV L w) (hq : L.quiet w) (hd : L.dval w = 0) :
    Out0 L (endW mctx mref cctx cref
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true) w) ∧
    ErrOk mctx mref cctx cref
      (synthesizeCombinationalCoreWith Tsyn declName parameters true true) w := by
  have h := out0_endW_of_triple L.plain (core_symbolic_triple0 (mctx := mctx) (cctx := cctx)
    L.plain trivial declName parameters) (w := w) ⟨hs.1, hq, hd⟩
  exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, h.2⟩

/-! ## The worlds of an outermost symbolic run -/

theorem RunsTo_triple {α : Type} {P : Void IO.RealWorld → Prop} {Q : α → Void IO.RealWorld → Prop}
    {R : Exception → Void IO.RealWorld → Prop} {m : MetaM α}
    (hT : Triple mctx mref cctx cref P m Q R) {w : Void IO.RealWorld} {a : α} {w' : Void IO.RealWorld}
    (hP : P w) (hr : RunsTo m mctx mref cctx cref w a w') : Q a w' := by
  have := hT w hP
  unfold RunsTo at hr
  rw [hr] at this
  exact this

theorem RunsTo_bind_inv {α β : Type} {P : Void IO.RealWorld → Prop}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    {m : MetaM α} {f : α → MetaM β}
    (hT : Triple mctx mref cctx cref P m Q R) {w : Void IO.RealWorld} {b : β} {w'' : Void IO.RealWorld}
    (hP : P w) (h : RunsTo (m >>= f) mctx mref cctx cref w b w'') :
    ∃ (a : α) (w1 : Void IO.RealWorld), Q a w1 ∧ RunsTo (f a) mctx mref cctx cref w1 b w'' := by
  obtain ⟨a, w1, hm, hf⟩ := RunsTo.bind h
  exact ⟨a, w1, RunsTo_triple hT hP hm, hf⟩

/-- The `try … finally` of the entry from `J L (d+1)` back to `J L d` (the `body` of the Triple proofs). -/
theorem tf_triple (L : RefLaws mref cref) (d : Nat) (declName : Name)
    (parameters : List (String × Nat)) (b : Bool)
    (hb : ∀ {tenv : Lean.Environment} (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Keeps mctx mref cctx cref (J L (d + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName parameters true true ci isInst))
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (J L (d + 1))
      (_root_.tryFinally
        (do
          let constInfo ← getConstInfo declName
          let env ← getEnv
          synthesizeFromConst (fun e h t n => translateExprToWire env e h t n)
            (profLogIO b) declName parameters true true
            (entryConst true true parameters constInfo (instancePredicate env) (userInliner env)
              (structEnv env))
            (instancePredicate env))
        (do
          ST.Ref.modify sparkleSynthDepth fun x => x - 1
          if (d != 0) = true then do
              ST.Ref.set sparkleFvarValueMap m1
              ST.Ref.set sparkleWireWidthCache m2
              ST.Ref.set sparkleLetWireCache m3
              ST.Ref.set sparkleLoopWireCache m4
              ST.Ref.set sparkleWireCanon m5
              ST.Ref.set sparkleSubInstanceOutputs m6
              ST.Ref.set sparkleSingleOutInstanceCache m7
            else pure () : MetaM Unit))
      (fun _ => J L d) (JE L d) := by
  refine Triple.tryFinally (M := J L (d + 1)) (E := OkExc) ?_
    (fin_triple L d d m1 m2 m3 m4 m5 m6 m7)
  refine Triple.bind (Triple.frame L (Framed.constInfo _) (d + 1)) ?_
  intro ci
  refine Triple.bind (Triple.frame L Framed.env (d + 1)) ?_
  intro env
  exact keeps_iff.mp (hb _ _)

set_option hygiene false in
macro "rbind " T:term:max : tactic => `(tactic|
  (obtain ⟨_, _, hI, h⟩ := RunsTo_bind_inv $T hI h))

set_option maxHeartbeats 1600000 in
theorem core_symbolic_worlds (L : RefLaws mref cref) (hA : L.aux {}) {declName : Name}
    {parameters : List (String × Nat)} {w w' : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hw : Out0 L w)
    (hbody : ∀ {tenv : Lean.Environment} (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (J L 1)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName parameters true true ci isInst))
    (h : RunsTo (synthesizeCombinationalCoreWith Tsyn declName parameters true true)
      mctx mref cctx cref w (M, D) w') :
    ∃ (logProf : String → IO Unit) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (Tsyn envR) logProf declName parameters true true ci
        (instancePredicate envR)) mctx mref cctx cref w3 (M, D) w4 ∧
      J L 1 w3 ∧ J L 1 w4 ∧ J L 0 w' := by
  unfold synthesizeCombinationalCoreWith at h
  simp only [↓reduceIte] at h
  rcases RunsTo.ite h with h | h
  · obtain ⟨_, _, h1, -⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  obtain ⟨_, w1, hf, h⟩ := RunsTo.bind h
  have hI : Out0 L w1 := by
    refine RunsTo_triple (Q := fun _ => Out0 L) (R := E0 L) ?_ hw hf
    refine Triple.forIn_list _ (fun a b => ?_) _ _
    rcases a with ⟨nm, dv⟩
    dsimp only
    refine Triple.ite (fun _ => ?_) (fun _ => Triple.pure fun w hw => hw)
    refine Triple.bind (Q := fun _ _ => False)
      (tripleO_throwErr L _ (by first | exact .str _ | exact .fmt _)) ?_
    intro _ w hf
    exact hf.elim
  obtain ⟨prof, _, hI, h⟩ := RunsTo_bind_inv (tripleO_op L (.framed (Framed.ioEnv _))) hI h
  rbind (tripleO_op L (.diag (Diag.profLog prof.isSome _)))
  obtain ⟨d, _, hI, h⟩ := RunsTo_bind_inv (tripleO_frameQ L Framed.depthGet (φ := fun d => d = 0)
    (fun w d w' hw h => by rw [L.depthGet _ _ _ h]; exact hw.2.2)) hI h
  obtain ⟨hI, hd⟩ := hI
  rcases RunsTo.ite h with h | h
  · obtain ⟨_, _, h1, -⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  have h0 : (d == 0) = true := by subst hd; rfl
  simp only [h0, ↓reduceIte] at h
  rbind (Triple.pure (Q := fun _ => Out0 L) (R := E0 L) (fun w hw => hw))
  rbind (Triple.pure (Q := fun _ => Out0 L) (R := E0 L) (fun w hw => hw))
  rbind (Triple.pure (Q := fun _ => Out0 L) (R := E0 L) (fun w hw => hw))
  rbind (Triple.pure (Q := fun _ => Out0 L) (R := E0 L) (fun w hw => hw))
  rbind (Triple.pure (Q := fun _ => Out0 L) (R := E0 L) (fun w hw => hw))
  rbind (Triple.pure (Q := fun _ => Out0 L) (R := E0 L) (fun w hw => hw))
  rbind (Triple.pure (Q := fun _ => Out0 L) (R := E0 L) (fun w hw => hw))
  rbind (tripleO_op L (Op.framed (Framed.sideSet _ (by constructor))))
  rbind (tripleO_op L (Op.framed (Framed.sideSet _ (by constructor))))
  rbind (tripleO_op L (Op.framed (Framed.sideSet _ (by constructor))))
  rbind (tripleO_op L (Op.framed (Framed.sideSet _ (by constructor))))
  rbind (tripleO_clear L hA d hd (R := E0 L))
  rbind (Triple.frame L (Framed.sideSet _ (by constructor)) d)
  rbind (Triple.frame L (Framed.sideSet _ (by constructor)) d)
  rbind (Triple.frame L (Framed.sideSet _ (by constructor)) d)
  rbind (Triple.frame L (Framed.sideSet _ (by constructor)) d)
  rbind (Triple.frame L (Framed.sideSet _ (by constructor)) d)
  rbind (Triple.frame L (Framed.sideSet _ (by constructor)) d)
  rbind (Triple.frame L (Framed.sideSet _ (by constructor)) d)
  rbind (Triple.depthSet L d (d + 1) (R := fun _ _ => True))
  subst hd
  have htf := tf_triple L 0 declName parameters prof.isSome (fun {tenv} ci isInst => hbody _ ci isInst) 
  have hJ0 := RunsTo_triple (htf _ _ _ _ _ _ _) hI h
  obtain ⟨_, h⟩ := RunsTo.try_finally h
  obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
  obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
  rw [entryConst_off _ _ _ _ _ _ _ (by simp)] at h
  have hJ2 := RunsTo_triple (Triple.frame L (Framed.constInfo _) (0 + 1)) hI hget
  have hJ3 := RunsTo_triple (Triple.frame L Framed.env (0 + 1)) hJ2 henv
  have hJ4 := RunsTo_triple (keeps_iff.mp (hbody prof.isSome _ _)) hJ3 h
  exact ⟨_, env, ci, _, w2, _, _, _, _, hget, henv, h, hJ3, hJ4, hJ0⟩

end Tools.ShippingGen4ParamKeeps
