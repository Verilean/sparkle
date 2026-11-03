import Tools.ShippingGen5DCEntryS
set_option autoImplicit false
-- NOT BUILT: U-RUNT, scripts/gen5/DC_CONNECT_RUNT_FREEZE.md §3 (freeze 64cbaa20 approved as a design). Not yet built in a clean issue-linked build.

/-! # DC-CONNECT U-RUNT: conditional run transport `childMap D'` → `childMap D`

CONDITIONAL on `NoRawBelow` and on the lookup agreement `hlk`. Does NOT link a given core run's `(raw, D)` to a closing equation,
does not supply `EntryWitness`/`ReflectsAll`, does not give `TopShips` on `D'`, does not adopt `Post`, is not FG. -/

namespace Tools.ShippingGen5DCEntryT

theorem childMap_transport {D D' : Sparkle.IR.AST.Design} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn)
    (mn : String) (hne : mn ≠ rn) :
    Tools.ShippingMachineLinked.childMap D'.modules mn = Tools.ShippingMachineLinked.childMap D.modules mn := by
  unfold Tools.ShippingMachineLinked.childMap
  rw [hlk mn hne]

private theorem evalAssignsKG_congr {σ : Type}
    {KS KS' : Tools.ShippingHierStateG.KStep σ} {we : Sparkle.IR.Semantics.WEnv}
    {ch ch' : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    (kids : String → σ) (mems : Sparkle.IR.Semantics.MEnv) :
    ∀ (l : List Sparkle.IR.AST.Stmt),
      (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ l → ch' mn = ch mn) →
      (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ l →
        ∀ (c : Sparkle.IR.AST.Module) (cwe : Sparkle.IR.Semantics.WEnv), ch mn = some (c, cwe) →
          ∀ (cin : List (String × Sparkle.IR.AST.Expr)) (env : Sparkle.IR.Semantics.Env) (s : σ),
            KS' c cwe cin env s = KS c cwe cin env s) →
      ∀ (env : Sparkle.IR.Semantics.Env) (acc : String → σ),
        Tools.ShippingHierStateG.evalAssignsKG KS' we ch' kids mems l env acc =
          Tools.ShippingHierStateG.evalAssignsKG KS we ch kids mems l env acc := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons s rest ih =>
    intro hch hks env acc
    have ih' := fun env acc => ih
      (fun mn iname conns h => hch mn iname conns (List.mem_cons_of_mem _ h))
      (fun mn iname conns h => hks mn iname conns (List.mem_cons_of_mem _ h)) env acc
    cases s with
    | assign l r =>
      simp only [Tools.ShippingHierStateG.evalAssignsKG]
      cases evalExpr_eq : Sparkle.IR.Semantics.evalExpr we env r with
      | none => rfl
      | some v => simp only [Option.bind_eq_bind, Option.bind_some]; exact ih' _ _
    | register => simp only [Tools.ShippingHierStateG.evalAssignsKG]; exact ih' _ _
    | memory name aw dw a b c d ra rd cr e er =>
      simp only [Tools.ShippingHierStateG.evalAssignsKG]
      cases cr
      · exact ih' _ _
      · simp only [if_true]
        cases Sparkle.IR.Semantics.comboReads we mems name aw dw ((ra, rd) :: er) env with
        | none => rfl
        | some env' => simp only [Option.bind_eq_bind, Option.bind_some]; exact ih' _ _
    | inst mn iname conns =>
      have hmem : Sparkle.IR.AST.Stmt.inst mn iname conns ∈ Sparkle.IR.AST.Stmt.inst mn iname conns :: rest :=
        List.mem_cons_self
      simp only [Tools.ShippingHierStateG.evalAssignsKG]
      rw [hch mn iname conns hmem]
      cases hc : ch mn with
      | none => rfl
      | some p =>
        obtain ⟨child, cwe⟩ := p
        simp only [Option.bind_eq_bind, Option.bind_some]
        rw [hks mn iname conns hmem child cwe hc _ _ _]
        cases KS child cwe (Tools.ShippingHierState.inConns child.outputs conns) env (kids iname) with
        | none => rfl
        | some r => simp only [Option.bind_eq_bind, Option.bind_some]; exact ih' _ _

theorem stepModuleTG_congr {σ : Type}
    {KS KS' : Tools.ShippingHierStateG.KStep σ} {we : Sparkle.IR.Semantics.WEnv}
    {ch ch' : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {body : List Sparkle.IR.AST.Stmt}
    (hch : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Sparkle.IR.AST.Module) (cwe : Sparkle.IR.Semantics.WEnv), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Sparkle.IR.AST.Expr)) (env : Sparkle.IR.Semantics.Env) (s : σ),
          KS' c cwe cin env s = KS c cwe cin env s)
    (env0 : Sparkle.IR.Semantics.Env) (s : Tools.ShippingHierStateG.KState σ) :
    Tools.ShippingHierStateG.stepModuleTG KS' we ch' body env0 s =
      Tools.ShippingHierStateG.stepModuleTG KS we ch body env0 s := by
  unfold Tools.ShippingHierStateG.stepModuleTG
  rw [evalAssignsKG_congr (KS := KS) (KS' := KS') (ch := ch) (ch' := ch') s.kids s.mems body
    hch hKS env0 s.kids]

theorem runModuleTG_congr {σ : Type}
    {KS KS' : Tools.ShippingHierStateG.KStep σ} {we : Sparkle.IR.Semantics.WEnv}
    {ch ch' : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {body : List Sparkle.IR.AST.Stmt}
    (hch : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body → ch' mn = ch mn)
    (hKS : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Sparkle.IR.AST.Stmt.inst mn iname conns ∈ body →
      ∀ (c : Sparkle.IR.AST.Module) (cwe : Sparkle.IR.Semantics.WEnv), ch mn = some (c, cwe) →
        ∀ (cin : List (String × Sparkle.IR.AST.Expr)) (env : Sparkle.IR.Semantics.Env) (s : σ),
          KS' c cwe cin env s = KS c cwe cin env s)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) :
    ∀ (T : Nat) (s : Tools.ShippingHierStateG.KState σ),
      Tools.ShippingHierStateG.runModuleTG KS' we ch' body seed T s =
        Tools.ShippingHierStateG.runModuleTG KS we ch body seed T s := by
  intro T
  induction T with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    simp only [Tools.ShippingHierStateG.runModuleTG]
    rw [stepModuleTG_congr (KS := KS) (KS' := KS') hch hKS]
    cases Tools.ShippingHierStateG.stepModuleTG KS we ch body (seed k s.st) s with
    | none => rfl
    | some r =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ih r.2]

theorem KSn_transport {D D' : Sparkle.IR.AST.Design} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn) :
    ∀ (n : Nat) (child : Sparkle.IR.AST.Module),
      Tools.ShippingGen5DCEntryR.NoRawBelow D rn n child →
      ∀ (cwe : Sparkle.IR.Semantics.WEnv) (cin : List (String × Sparkle.IR.AST.Expr))
        (env : Sparkle.IR.Semantics.Env) (s : Tools.ShippingHierStateG.KT n),
        Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) n child cwe cin env s =
          Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) n child cwe cin env s := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ k ih =>
    intro child hno cwe cin env s
    obtain ⟨hnm, hrec⟩ := hno
    show Tools.ShippingHierStateG.stepModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) k) cwe
        (Tools.ShippingMachineLinked.childMap D'.modules) child.body
        (Tools.ShippingHierarchySoundness.connEnvS cin env s.st) s =
      Tools.ShippingHierStateG.stepModuleTG
        (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) k) cwe
        (Tools.ShippingMachineLinked.childMap D.modules) child.body
        (Tools.ShippingHierarchySoundness.connEnvS cin env s.st) s
    apply stepModuleTG_congr
    · intro mn iname conns hmem
      exact childMap_transport hlk mn (hnm mn iname conns hmem)
    · intro mn iname conns hmem c cwe' hc cin' env' s'
      unfold Tools.ShippingMachineLinked.childMap at hc
      cases hl : Sparkle.IR.Machine.moduleByName D.modules mn with
      | none => rw [hl] at hc; simp at hc
      | some c' =>
        rw [hl] at hc
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨hcc, -⟩ := hc
        subst hcc
        exact ih _ (hrec mn iname conns _ hmem hl) cwe' cin' env' s'

theorem runModuleTG_transport {D D' : Sparkle.IR.AST.Design} {rn : String}
    (hlk : ∀ mn : String, mn ≠ rn →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn) :
    ∀ (n : Nat) (mc : Sparkle.IR.AST.Module) (we : Sparkle.IR.Semantics.WEnv)
      (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T : Nat)
      (s : Tools.ShippingHierStateG.KState (Tools.ShippingHierStateG.KT n)),
      Tools.ShippingGen5DCEntryR.NoRawBelow D rn (n + 1) mc →
      Tools.ShippingHierStateG.runModuleTG
          (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D'.modules) n) we
          (Tools.ShippingMachineLinked.childMap D'.modules) mc.body seed T s =
        Tools.ShippingHierStateG.runModuleTG
          (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) n) we
          (Tools.ShippingMachineLinked.childMap D.modules) mc.body seed T s := by
  intro n mc we seed T s hno
  obtain ⟨hnm, hrec⟩ := hno
  apply runModuleTG_congr
  · intro mn iname conns hmem
    exact childMap_transport hlk mn (hnm mn iname conns hmem)
  · intro mn iname conns hmem c cwe' hc cin' env' s'
    unfold Tools.ShippingMachineLinked.childMap at hc
    cases hl : Sparkle.IR.Machine.moduleByName D.modules mn with
    | none => rw [hl] at hc; simp at hc
    | some c' =>
      rw [hl] at hc
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨hcc, -⟩ := hc
      subst hcc
      exact KSn_transport hlk n _ (hrec mn iname conns _ hmem hl) cwe' cin' env' s'

end Tools.ShippingGen5DCEntryT
