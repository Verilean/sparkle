import Tools.ShippingSrm16Reset
set_option autoImplicit false
-- BUILT (unit SRM18): dev run a4 (exit 0; edit after a4 removed two unused simp arguments, rebuilt in a5); the final-SHA rebuild is in REPORT-SRM18.md.
-- SCOPE: the start-state premise `hsk : s.kids = resetKids D n raw` of the SRM16/17 corollaries is an EQUALITY of functions over ALL names.  The actual start-state proposition of the shipping chain
-- (`ComposedG`'s `Reset m dsn kids`, instantiated `ResetNk n`) is a Prop on the instance names of `raw` only, and the consumers (`kidReset_of_resetNk`, SRM13 `hrk`) need only that Prop.
-- PROVED here (no premise about the design): for ANY state `s` admitted by `hrun : runModuleTG … = some envs` there is an explicit state `bumpedStart …` with the same registers/memories, the SAME run result, a
-- `ResetNk` kids function whenever `s.kids` has one, and `kids ≠ resetKids D n raw`.  So `hsk` is not implied by `hrun`, nor by `hrun ∧ ResetNk`.
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm18Start
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierStateG Tools.ShippingHierState Tools.ShippingMachineLinked
open Tools.ShippingSrm16Reset
open Tools.ShippingMachineShipsDepth (ResetNk)

/-- Two evaluation results agree on the environment and, off the name `z`, on the instance-state function. -/
def RelZ {σ : Type} (z : String) : Option (Env × (String → σ)) → Option (Env × (String → σ)) → Prop
  | none, none => True
  | some a, some b => a.1 = b.1 ∧ ∀ i, i ≠ z → a.2 i = b.2 i
  | _, _ => False

/-- One cycle's elaboration never reads the state of an instance name `z` that no instance statement of the body uses. -/
theorem evalAssignsKG_relZ {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (mems : MEnv) (z : String) (kids kids' : String → σ)
    (hk : ∀ i, i ≠ z → kids i = kids' i) :
    ∀ (body : List Stmt), (∀ mn conns, Stmt.inst mn z conns ∉ body) →
      ∀ (env : Env) (acc acc' : String → σ), (∀ i, i ≠ z → acc i = acc' i) →
        RelZ z (evalAssignsKG KS we children kids mems body env acc)
               (evalAssignsKG KS we children kids' mems body env acc')
  | [], _, _, _, _, hacc => by
    simp only [evalAssignsKG]
    exact ⟨rfl, hacc⟩
  | .assign l r :: rest, hz, env, acc, acc', hacc => by
    simp only [evalAssignsKG]
    cases hv : evalExpr we env r with
    | none => first | exact True.intro | simp [RelZ]
    | some v =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      exact evalAssignsKG_relZ KS we children mems z kids kids' hk rest
        (fun mn c h => hz mn c (List.mem_cons_of_mem _ h)) _ acc acc' hacc
  | .register .. :: rest, hz, env, acc, acc', hacc => by
    simp only [evalAssignsKG]
    exact evalAssignsKG_relZ KS we children mems z kids kids' hk rest
      (fun mn c h => hz mn c (List.mem_cons_of_mem _ h)) _ acc acc' hacc
  | .memory name aw dw c wa wd we' ra rd cr ew er :: rest, hz, env, acc, acc', hacc => by
    simp only [evalAssignsKG]
    split
    · cases hc : comboReads we mems name aw dw ((ra, rd) :: er) env with
      | none => first | exact True.intro | simp [RelZ]
      | some env' =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        exact evalAssignsKG_relZ KS we children mems z kids kids' hk rest
          (fun mn c h => hz mn c (List.mem_cons_of_mem _ h)) _ acc acc' hacc
    · exact evalAssignsKG_relZ KS we children mems z kids kids' hk rest
        (fun mn c h => hz mn c (List.mem_cons_of_mem _ h)) _ acc acc' hacc
  | .inst mn iname conns :: rest, hz, env, acc, acc', hacc => by
    have hne : iname ≠ z := fun h => hz mn conns (h ▸ List.mem_cons_self)
    simp only [evalAssignsKG]
    cases hch : children mn with
    | none => first | exact True.intro | simp [RelZ]
    | some p =>
      obtain ⟨child, cwe⟩ := p
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [← hk iname hne]
      cases hs : KS child cwe (inConns child.outputs conns) env (kids iname) with
      | none => first | exact True.intro | simp [RelZ]
      | some q =>
        simp only [Option.bind_some]
        exact evalAssignsKG_relZ KS we children mems z kids kids' hk rest
          (fun mn' c h => hz mn' c (List.mem_cons_of_mem _ h)) _ _ _
          (fun i hi => by
            by_cases h : i = iname
            · subst h; simp
            · simp [h, hacc i hi])

/-- **The run never reads the state of an instance name that the body does not use.**  Two start states with the same registers and memories and kids functions agreeing off `z` have the same run. -/
theorem runModuleTG_kids_congr {σ : Type} (KS : KStep σ) (we : WEnv)
    (children : String → Option (Module × WEnv)) (body : List Stmt) (z : String)
    (hz : ∀ mn conns, Stmt.inst mn z conns ∉ body) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (s s' : KState σ), s.st = s'.st → s.mems = s'.mems → (∀ i, i ≠ z → s.kids i = s'.kids i) →
      runModuleTG KS we children body seed k s = runModuleTG KS we children body seed k s'
  | 0, _, _, _, _, _ => rfl
  | k + 1, ⟨st, mems, kids⟩, ⟨st', mems', kids'⟩, hst, hm, hk => by
    subst hst
    subst hm
    have hrel := evalAssignsKG_relZ KS we children mems z kids kids' hk body hz (seed k st) kids kids' hk
    simp only [runModuleTG, stepModuleTG]
    cases h1 : evalAssignsKG KS we children kids mems body (seed k st) kids with
    | none =>
      cases h2 : evalAssignsKG KS we children kids' mems body (seed k st) kids' with
      | none => first | rfl | simp
      | some r2 => rw [h1, h2] at hrel; exact hrel.elim
    | some r1 =>
      cases h2 : evalAssignsKG KS we children kids' mems body (seed k st) kids' with
      | none => rw [h1, h2] at hrel; exact hrel.elim
      | some r2 =>
        rw [h1, h2] at hrel
        obtain ⟨e1, a1⟩ := r1
        obtain ⟨e2, a2⟩ := r2
        obtain ⟨he, hk2⟩ := hrel
        try simp only at he hk2
        subst he
        simp only [Option.bind_some]
        cases hN : regNexts we mems body e1 with
        | none => rfl
        | some nexts =>
          simp only [Option.bind_some]
          cases hM : memNexts we body mems e1 with
          | none => rfl
          | some mems2 =>
            simp only [Option.bind_some]
            rw [runModuleTG_kids_congr KS we children body z hz seed k
              ⟨applyNexts st nexts, mems2, a1⟩ ⟨applyNexts st nexts, mems2, a2⟩ rfl rfl hk2]

/-- A different state of the same depth: every register bumped by one. -/
def bumpKT : (n : Nat) → KT n → KT n
  | 0, x => (⟨fun r => KidState.st x r + 1, KidState.mems x⟩ : KidState)
  | _ + 1, x => (⟨fun r => KState.st x r + 1, KState.mems x, KState.kids x⟩ : KState _)

theorem bumpKT_ne (n : Nat) (x : KT n) : bumpKT n x ≠ x := by
  intro h
  have h2 : stOf n (bumpKT n x) "" = stOf n x "" := by rw [h]
  cases n <;> simp only [bumpKT, stOf] at h2 <;> omega

/-- A name that is the instance name of no `inst` statement of `L`: longer than the sum of all the instance-name lengths. -/
def instNames : List Stmt → List String
  | [] => []
  | .inst _ i _ :: rest => i :: instNames rest
  | _ :: rest => instNames rest

def freshName (L : List Stmt) : String := String.ofList (List.replicate (((instNames L).map String.length).sum + 1) 'a')

theorem mem_instNames {L : List Stmt} {mn i : String} {conns : List (String × Expr)}
    (h : Stmt.inst mn i conns ∈ L) : i ∈ instNames L := by
  induction L with
  | nil => cases h
  | cons st rest ih =>
    cases h with
    | head => simp [instNames]
    | tail _ h' =>
      have := ih h'
      cases st <;> simp [instNames, this]

theorem length_le_sum (ns : List String) (i : String) (h : i ∈ ns) : i.length ≤ (ns.map String.length).sum := by
  induction ns with
  | nil => cases h
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    cases List.mem_cons.mp h with
    | inl e => subst e; omega
    | inr h' => have := ih h'; omega

theorem freshName_fresh (L : List Stmt) : ∀ mn conns, Stmt.inst mn (freshName L) conns ∉ L := by
  intro mn conns h
  have h1 := length_le_sum _ _ (mem_instNames h)
  have h2 : (freshName L).length = ((instNames L).map String.length).sum + 1 := by
    first | simp [freshName] | (unfold freshName; simp) | rfl
  omega

/-- **The explicit non-reset start state**: `s` with the instance state at the fresh name `z = freshName (raw.body ++ body)` replaced by a bumped copy of `resetKids D n raw z`.  It has the same registers
and memories as `s`. -/
def bumpedStart (n : Nat) (raw : Module) (D : Design) (body : List Stmt) (s : KState (KT n)) : KState (KT n) :=
  ⟨s.st, s.mems, fun i => if i = freshName (raw.body ++ body) then bumpKT n (resetKids D n raw i) else s.kids i⟩

/-- **`hsk` is not implied by the run proposition (nor by the run proposition together with `ResetNk`).**  For EVERY state `s` with `runModuleTG … body … T s = some envs`, the explicit state
`bumpedStart n raw D body s`: has the same registers and memories, has the SAME run result, has kids function `≠ resetKids D n raw`, and has `ResetNk n raw D` kids whenever `s` has. -/
theorem bumpedStart_spec {n : Nat} (raw : Module) (D : Design) (KS : KStep (KT n)) (we : WEnv)
    (children : String → Option (Module × WEnv)) (body : List Stmt) (seed : Nat → (String → Nat) → Env) (T : Nat)
    (s : KState (KT n)) (envs : List Env)
    (hrun : runModuleTG KS we children body seed T s = some envs) :
    runModuleTG KS we children body seed T (bumpedStart n raw D body s) = some envs ∧
    (bumpedStart n raw D body s).st = s.st ∧ (bumpedStart n raw D body s).mems = s.mems ∧
    (bumpedStart n raw D body s).kids ≠ resetKids D n raw ∧
    (ResetNk n raw D s.kids → ResetNk n raw D (bumpedStart n raw D body s).kids) := by
  have hzb : ∀ mn conns, Stmt.inst mn (freshName (raw.body ++ body)) conns ∉ body := fun mn conns h =>
    freshName_fresh (raw.body ++ body) mn conns (List.mem_append_right _ h)
  have hzr : ∀ mn conns, Stmt.inst mn (freshName (raw.body ++ body)) conns ∉ raw.body := fun mn conns h =>
    freshName_fresh (raw.body ++ body) mn conns (List.mem_append_left _ h)
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · rw [← runModuleTG_kids_congr KS we children body _ hzb seed T s (bumpedStart n raw D body s) rfl rfl
      (fun i hi => by simp [bumpedStart, hi])]
    exact hrun
  · intro h
    have h2 := congrFun h (freshName (raw.body ++ body))
    simp only [bumpedStart, if_true] at h2
    exact bumpKT_ne n _ h2
  · intro hr iname mc ⟨conns, hi⟩ hmb
    have hne : iname ≠ freshName (raw.body ++ body) := fun h => hzr mc.name conns (h ▸ hi)
    have := hr iname mc ⟨conns, hi⟩ hmb
    simpa [bumpedStart, hne] using this

end Tools.ShippingSrm18Start
