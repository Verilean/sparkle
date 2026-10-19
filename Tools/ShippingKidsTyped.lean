import Tools.ShippingGateKidFactsT
import Tools.ShippingKidsMixedC
import Tools.ShippingTypedWidthOk
import Tools.ShippingDesignSVBounds
-- WRITTEN, NOT BUILT (round par/o-typed).

/-! # A TYPED children bound for the depth-0 route (round par/o-typed, Option A)

The general-closing ships head (`Tools.ShippingShipsFree.machine_ships_hierC_at_free`) consumes
its children bound `hBd : Bd b D → KSBoundedIn children KS b.body Inv`
(`Tools/ShippingHierOptRun.lean`, `KSBoundedIn`) in ONE place: `fitX_of_run` (same file), to
show that along the linked run of the full entry's module `b` every EXTRACTED input (an
instance-driven wire, `openIns b`) fits its declared width — the `hfitX` premise of
`hierRefineCheck_linked`, in the branch where the optimizer's candidate is accepted.
`KSBoundedIn` bounds each child's outputs in EVERY parent environment. A GATE child (the
unified mixed gate's module) drives `out := ref w`; its outputs are bounded only because its
inputs are (width typing), so `KSBoundedIn` holds for it only by a syntactic chain fact
(`combOk`, the `hchain` binder of `collMixSame_designClosed`).

The minimal weaker hypothesis: bound the children only in the environments REACHED by the run.
Along the run of `b`, from inputs that fit and a state that fits off the output ports, every
environment fits off the output ports (`BoundOff`, `Tools.ShippingHierTyped`) when

* every assignment is width-typed (`assignTyped`, as in `hierTyped`);
* every instance's child is either FREE-bounded (`FreeKid`: the `KSBoundedIn` clause for that
  one instance — masked children and the built memory module, under `mixInv`) or TYPED
  (`TypedKid`: `childTyped`, its input connections read parent wires off the outputs no wider
  than the ports, the invariant trivial, and its emitted width table no wider than its IR table
  off its outputs — the last to read the instance's start state off `InvN`);
* each typed child's own state fits off its outputs (`KidsOk`), which a step preserves
  (register updates are masked).

* `TypedRun` — the per-module record (assignments, extracted inputs off the outputs,
  `KSBoundedTypedIn`);
* `evalAssignsKG_boundOff`, `runModuleTG_typed`, `fitX_of_runTyped` — the run argument
  (`flatKS`, depth 0), `fitX_of_runTyped` the drop-in for `fitX_of_run`;
* `KidTyped`, `gate_weS_le`, `kidTyped_of_gate` — what a gate child gives (from
  `GateChildPorts`: `childTyped_ok`, `notSeq`, the width tables);
* `core_typedRunMT` — `TypedRun` of the full entry's module of a machine with calls
  (memory / instance fields), from the core run and ONE fact per kid (`FlatOk ∨ KidTyped`),
  the kids' `KidFactsTC` (input widths `inW`, `outsIn`) and the data condition `callArgsOk`;
  the parent side (typed assignments, wires not outputs, argument connections at the `let`
  binders' widths) DERIVED (`core_closed_typedInMT`, `core_callConnsMT`, `core_callStmtMT`).

No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingKidsTyped
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingHierarchySoundness (connEnvS bindOuts)
open Tools.ShippingHierTyped (BoundOff assignTyped childTyped childStmtTyped)
open Tools.ShippingSeqOptSoundness (seedIn)

/-! ## The bound -/

/-- An instance's INPUT connections are typed: a reference connection of a non-output port
reads a parent wire off `Xp`, no wider (parent widths `W`) than the port (child widths `cwe`). -/
abbrev inTyped (W : WEnv) (Xp : List String) (child : Module) (cwe : WEnv)
    (conns : List (String × Expr)) : Prop :=
  ∀ c ∈ conns, c.1 ∉ child.outputs.map (·.name) → ∀ w, c.2 = .ref w → w ∉ Xp ∧ W w ≤ cwe c.1

/-- The `KSBoundedIn` clause of ONE instance under `flatKS`: outputs within the ports' widths in
every environment, the invariant kept. -/
abbrev FreeKid (Inv : Module → KidState → Prop) (child : Module) (cwe : WEnv)
    (conns : List (String × Expr)) : Prop :=
  ∀ env s cres s', Inv child s →
    flatKS child cwe (inConns child.outputs conns) env s = some (cres, s') →
    (∀ p ∈ child.outputs, cres p.name < 2 ^ p.ty.bitWidth) ∧ Inv child s'

/-- A width-typed instance: a typed child, typed input connections, a trivial invariant, the
child's emitted widths no wider than its declared ones off its outputs. -/
abbrev TypedKid (W : WEnv) (Xp : List String) (Inv : Module → KidState → Prop) (child : Module)
    (cwe : WEnv) (conns : List (String × Expr)) : Prop :=
  childTyped cwe child = true ∧ inTyped W Xp child cwe conns ∧ (∀ s, Inv child s) ∧
    ∀ x, x ∉ child.outputs.map (·.name) → Tools.ShippingDesignSV.weS child x ≤ cwe x

/-- **The typed children bound**: every instance free-bounded or typed. -/
abbrev KSBoundedTypedIn (children : String → Option (Module × WEnv)) (W : WEnv)
    (Xp : List String) (body : List Stmt) (Inv : Module → KidState → Prop) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
    children mn = some (child, cwe) → FreeKid Inv child cwe conns ∨ TypedKid W Xp Inv child cwe conns

/-- The instances' states: the invariant, and a typed instance's registers within its declared
widths off its outputs. -/
abbrev KidsOk (children : String → Option (Module × WEnv)) (W : WEnv) (Xp : List String)
    (body : List Stmt) (Inv : Module → KidState → Prop) (kids : String → KidState) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
    children mn = some (child, cwe) →
    Inv child (kids iname) ∧
      (TypedKid W Xp Inv child cwe conns → BoundOff cwe (child.outputs.map (·.name)) (kids iname).st)

/-- **What the typed run argument takes of a module** (in place of `KSBoundedIn`). -/
structure TypedRun (children : String → Option (Module × WEnv)) (b : Module)
    (Inv : Module → KidState → Prop) : Prop where
  asg : ∀ l r, Stmt.assign l r ∈ b.body →
    assignTyped (declWidth b) (b.outputs.map (·.name)) l r = true
  openX : ∀ p ∈ Sparkle.IR.HierCheck.openIns b, p.name ∉ b.outputs.map (·.name)
  kids : KSBoundedTypedIn children (declWidth b) (b.outputs.map (·.name)) b.body Inv

/-! ## Small facts -/

theorem memFree_tail {st : Stmt} {rest : List Stmt} (h : Tools.ConeFold.memFree (st :: rest)) :
    Tools.ConeFold.memFree rest := by
  cases st <;> simp_all [Tools.ConeFold.memFree]

theorem noMemB_of_memFree : ∀ {body : List Stmt}, Tools.ConeFold.memFree body →
    body.all (fun st => match st with | .memory .. => false | _ => true) = true
  | [], _ => rfl
  | st :: rest, h => by
    have ih : rest.all (fun st => match st with | .memory .. => false | _ => true) = true :=
      noMemB_of_memFree (memFree_tail h)
    cases st <;> simp_all [Tools.ConeFold.memFree]

theorem noMemB_of_childTyped {cwe : WEnv} {child : Module} (h : childTyped cwe child = true) :
    child.body.all (fun st => match st with | .memory .. => false | _ => true) = true := by
  simp only [childTyped, Bool.and_eq_true] at h
  rw [List.all_eq_true]
  intro st hst
  have h1 := List.all_eq_true.mp h.1 st hst
  cases st with
  | memory => simp [childStmtTyped] at h1
  | _ => rfl

theorem noMem_of_childTyped {cwe : WEnv} {child : Module} (h : childTyped cwe child = true) :
    Tools.ShippingMachineShipsHier.noMem child.body = true := by
  simp only [childTyped, Bool.and_eq_true] at h
  unfold Tools.ShippingMachineShipsHier.noMem
  rw [List.all_eq_true]
  intro st hst
  have h1 := List.all_eq_true.mp h.1 st hst
  cases st with
  | memory => simp [childStmtTyped] at h1
  | _ => rfl

/-- Masked register updates keep a state within its widths off `X`. -/
theorem boundOff_applyNexts {we : WEnv} {X : List String} {st : String → Nat}
    {nexts : List (String × Nat)} (hst : BoundOff we X st)
    (hn : ∀ pr ∈ nexts, pr.2 < 2 ^ we pr.1) : BoundOff we X (applyNexts st nexts) := by
  intro n hnX
  simp only [applyNexts]
  cases hf : nexts.find? (fun p => p.1 == n) with
  | none => exact hst n hnX
  | some pr =>
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    simp only [beq_iff_eq] at hpred
    have hb := hn pr hmem
    rw [hpred] at hb
    exact hb

/-- A typed instance's connection-fed environment fits the child's widths off its outputs. -/
theorem connEnvS_boundOffT {W : WEnv} {Xp : List String} {child : Module} {cwe : WEnv}
    {conns : List (String × Expr)} {env : Env} {st : String → Nat}
    (hb : BoundOff W Xp env) (ht : inTyped W Xp child cwe conns)
    (hst : BoundOff cwe (child.outputs.map (·.name)) st) :
    BoundOff cwe (child.outputs.map (·.name)) (connEnvS (inConns child.outputs conns) env st) := by
  intro n hn
  unfold connEnvS
  cases hl : (inConns child.outputs conns).lookup n with
  | none => exact hst n hn
  | some e =>
    cases e with
    | ref w =>
      have hm := Tools.ShippingHierSVRun.lookup_mem hl
      have hm' : (n, Expr.ref w) ∈ conns := (List.mem_filter.mp hm).1
      obtain ⟨hwX, hle⟩ := ht (n, Expr.ref w) hm' hn w rfl
      exact Nat.lt_of_lt_of_le (hb w hwX) (Nat.pow_le_pow_right (by omega) hle)
    | _ => exact hst n hn

/-- **A typed child's step**: from a connection-fed environment within its widths off its
outputs, its outputs fit the ports. -/
theorem typed_step_out {child : Module} {cwe : WEnv} {cin : List (String × Expr)} {env : Env}
    {s : KidState} {cres : Env} {s' : KidState}
    (hct : childTyped cwe child = true)
    (hin : BoundOff cwe (child.outputs.map (·.name)) (connEnvS cin env s.st))
    (hk : flatKS child cwe cin env s = some (cres, s')) :
    ∀ p ∈ child.outputs, cres p.name < 2 ^ p.ty.bitWidth := by
  simp only [flatKS] at hk
  cases hst : stepModule cwe child.body (connEnvS cin env s.st) s.mems with
  | none => simp [hst] at hk
  | some r =>
    simp only [hst, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨envF, nexts, mems', hF, -, -, rfl⟩ := stepModule_some hst
    obtain ⟨rfl, -⟩ := hk
    simp only [childTyped, Bool.and_eq_true] at hct
    obtain ⟨hcb, hco⟩ := hct
    obtain ⟨-, hO⟩ := Tools.ShippingHierTyped.evalAssigns_typed cwe s.mems _ child.body _ envF hF
      hcb hin
    intro p hp
    have h1 := List.all_eq_true.mp hco p hp
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h1
    obtain ⟨hcount, st', hst', hm⟩ := h1
    cases st' with
    | assign l r =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
      obtain ⟨hl, hwd⟩ := hm
      subst hl
      obtain ⟨env1, hbe, hev⟩ := hO _ r hst' hcount
      have ht := List.all_eq_true.mp hcb _ hst'
      simp only [childStmtTyped, assignTyped, Bool.and_eq_true] at ht
      exact Nat.lt_of_lt_of_le (Tools.ShippingHierTyped.evalExpr_boundOff hbe ht.1.1 ht.1.2 hev)
        (Nat.pow_le_pow_right (by omega) hwd)
    | _ => simp at hm

/-- **A typed child's step keeps its registers within its widths** (whatever the parent's
environment). -/
theorem typed_step_state {child : Module} {cwe : WEnv} {cin : List (String × Expr)} {env : Env}
    {s : KidState} {cres : Env} {s' : KidState} {X : List String}
    (hct : childTyped cwe child = true) (hst0 : BoundOff cwe X s.st)
    (hk : flatKS child cwe cin env s = some (cres, s')) : BoundOff cwe X s'.st := by
  simp only [flatKS] at hk
  cases hst : stepModule cwe child.body (connEnvS cin env s.st) s.mems with
  | none => simp [hst] at hk
  | some r =>
    simp only [hst, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨envF, nexts, mems', -, hN, -, rfl⟩ := stepModule_some hst
    obtain ⟨-, rfl⟩ := hk
    exact boundOff_applyNexts hst0
      (Tools.ShippingHierTyped.regNexts_bounded' (noMemB_of_childTyped hct) hN)

/-! ## The run -/

/-- **One cycle's linked fold stays within the declared widths off the outputs**, given
typed assignments and instances whose outputs fit the wires they drive whenever the
environment they step on does (`evalAssignsKG_envBound` with `BoundOff` / `assignTyped`). -/
theorem evalAssignsKG_boundOff {σ : Type} (KS : KStep σ) (W : WEnv) (Xp : List String)
    (C : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv) :
    ∀ (body : List Stmt) (env envF : Env) (acc acc' : String → σ),
      Tools.ConeFold.memFree body →
      (∀ l r, Stmt.assign l r ∈ body → assignTyped W Xp l r = true) →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe, C mn = some (child, cwe) →
        ∀ e cres s', BoundOff W Xp e →
          KS child cwe (inConns child.outputs conns) e (kids iname) = some (cres, s') →
          ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) → w ∉ Xp →
            cres p.name < 2 ^ W w) →
      BoundOff W Xp env →
      evalAssignsKG KS W C kids mems body env acc = some (envF, acc') →
      BoundOff W Xp envF
  | [], env, envF, acc, acc', _, _, _, hb, h => by
    simp only [evalAssignsKG, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hb
  | st :: rest, env, envF, acc, acc', hmf, hA, hI, hb, h => by
    have hmf' : Tools.ConeFold.memFree rest := memFree_tail hmf
    have hA' := fun l r hm => hA l r (List.mem_cons_of_mem _ hm)
    have hI' := fun mn iname conns hm => hI mn iname conns (List.mem_cons_of_mem _ hm)
    cases st with
    | assign l r =>
      simp only [evalAssignsKG] at h
      cases hv : evalExpr W env r with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        exact evalAssignsKG_boundOff KS W Xp C kids mems rest _ envF acc acc' hmf' hA' hI'
          (Tools.ShippingHierTyped.boundOff_write hb (hA l r List.mem_cons_self) hv) h
    | register o c rk i iv =>
      exact evalAssignsKG_boundOff KS W Xp C kids mems rest env envF acc acc' hmf' hA' hI' hb h
    | memory nm aw dw c wa wd wen ra rd cr ew er => simp [Tools.ConeFold.memFree] at hmf
    | inst mn iname conns =>
      simp only [evalAssignsKG] at h
      cases hc : C mn with
      | none => simp [hc] at h
      | some cp =>
        obtain ⟨child, cwe⟩ := cp
        simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
        cases hk : KS child cwe (inConns child.outputs conns) env (kids iname) with
        | none => simp [hk] at h
        | some r =>
          obtain ⟨cres, s'⟩ := r
          simp only [hk, Option.bind_some] at h
          refine evalAssignsKG_boundOff KS W Xp C kids mems rest _ envF _ acc' hmf' hA' hI' ?_ h
          exact Tools.ShippingHierTyped.bindOuts_pres (fun n v => n ∉ Xp → v < 2 ^ W n) conns cres
            child.outputs env hb
            (fun p hp w hl hw => hI mn iname conns List.mem_cons_self child cwe hc env cres s' hb hk
              p hp w hl hw)

/-- **A typed linked run (`flatKS`) keeps every cycle's environment within the declared widths
off the output ports**, from seeds and a state that do and instances' states that are `KidsOk`. -/
theorem runModuleTG_typed (C : String → Option (Module × WEnv)) (m : Module)
    (Inv : Module → KidState → Prop) (ht : TypedRun C m Inv)
    (hwf : linkedWF C m.body = true) (hnd : (instNames m.body).Nodup)
    (hIW : instOutWidthsOk C (declWidth m) m.body = true)
    (seed : Nat → (String → Nat) → Env)
    (hseed : ∀ t st, BoundOff (declWidth m) (m.outputs.map (·.name)) st →
      BoundOff (declWidth m) (m.outputs.map (·.name)) (seed t st)) :
    ∀ (T : Nat) (s : KState KidState) (envs : List Env),
      runModuleTG flatKS (declWidth m) C m.body seed T s = some envs →
      BoundOff (declWidth m) (m.outputs.map (·.name)) s.st →
      KidsOk C (declWidth m) (m.outputs.map (·.name)) m.body Inv s.kids →
      ∀ j (hj : j < envs.length), BoundOff (declWidth m) (m.outputs.map (·.name)) (envs[j]'hj)
  | 0, _, envs, h, _, _, j, hj => by
    simp only [runModuleTG, Option.some.injEq] at h; subst h; cases hj
  | k + 1, s, envs, h, hst, hkids, j, hj => by
    have hmf := memFree_of_linkedWF _ hwf
    simp only [runModuleTG] at h
    cases hS : stepModuleTG flatKS (declWidth m) C m.body (seed k s.st) s with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, s'⟩ := r
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG flatKS (declWidth m) C m.body seed k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    unfold stepModuleTG at hS
    cases hK : evalAssignsKG flatKS (declWidth m) C s.kids s.mems m.body (seed k s.st) s.kids with
    | none => simp [hK] at hS
    | some ek =>
    obtain ⟨envF', kids'⟩ := ek
    cases hN : regNexts (declWidth m) s.mems m.body envF' with
    | none => simp [hK, hN] at hS
    | some nexts =>
    have hM : memNexts (declWidth m) m.body s.mems envF' = some s.mems :=
      Tools.ConeFold.memNexts_memFree _ m.body hmf s.mems envF'
    simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    -- an instance's outputs fit the wires they drive, on a bounded environment
    have hI : ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body → ∀ child cwe,
        C mn = some (child, cwe) → ∀ e cres s1, BoundOff (declWidth m) (m.outputs.map (·.name)) e →
        flatKS child cwe (inConns child.outputs conns) e (s.kids iname) = some (cres, s1) →
        ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
          w ∉ m.outputs.map (·.name) → cres p.name < 2 ^ declWidth m w := by
      intro mn iname conns hm child cwe hc e cres s1 hbe hk p hp w hl _
      rw [instOutWidthsOk_at hIW hm hc p hp w hl]
      obtain ⟨hinv, hbst⟩ := hkids mn iname conns hm child cwe hc
      rcases ht.kids mn iname conns hm child cwe hc with hfree | htk
      · exact (hfree e (s.kids iname) cres s1 hinv hk).1 p hp
      · exact typed_step_out htk.1 (connEnvS_boundOffT hbe htk.2.1 (hbst htk)) hk p hp
    have hbF : BoundOff (declWidth m) (m.outputs.map (·.name)) envF' :=
      evalAssignsKG_boundOff flatKS (declWidth m) (m.outputs.map (·.name)) C s.kids s.mems m.body
        _ envF' s.kids kids' hmf ht.asg hI (hseed k s.st hst) hK
    cases j with
    | zero => exact hbF
    | succ j =>
      refine runModuleTG_typed C m Inv ht hwf hnd hIW seed hseed k _ rest hR ?_ ?_ j
        (by simpa using hj)
      · exact boundOff_applyNexts hst
          (Tools.ShippingHierTyped.regNexts_bounded' (noMemB_of_memFree hmf) hN)
      · intro mn iname conns hm child cwe hc
        obtain ⟨child', cwe', envAt, cres, hc', hk, -, -⟩ :=
          Tools.ShippingHierOptLinked.linked_consistentKG flatKS (declWidth m) C s.kids s.mems
            m.body _ envF' s.kids kids' hwf hnd hK mn iname conns hm
        rw [hc] at hc'
        cases hc'
        obtain ⟨hinv, hbst⟩ := hkids mn iname conns hm child cwe hc
        rcases ht.kids mn iname conns hm child cwe hc with hfree | htk
        · exact ⟨(hfree envAt (s.kids iname) cres (kids' iname) hinv hk).2,
            fun htk' => typed_step_state htk'.1 (hbst htk') hk⟩
        · exact ⟨htk.2.2.1 _, fun htk' => typed_step_state htk.1 (hbst htk') hk⟩

/-- **The extracted inputs fit along a typed linked run** — the drop-in for
`Tools.ShippingHierOptRun.fitX_of_run` (`hfitX` of `hierRefineCheck_linked`), with the children
bounded only on the environments the run reaches. -/
theorem fitX_of_runTyped (C : String → Option (Module × WEnv)) (m : Module)
    (Inv : Module → KidState → Prop) (ht : TypedRun C m Inv)
    (hwf : linkedWF C m.body = true) (hnd : (instNames m.body).Nodup)
    (hIW : instOutWidthsOk C (declWidth m) m.body = true) (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    (T : Nat) (s : KState KidState) (envs : List Env)
    (hrun : runModuleTG flatKS (declWidth m) C m.body (seedIn m ins) T s = some envs)
    (hst : BoundOff (declWidth m) (m.outputs.map (·.name)) s.st)
    (hkids : KidsOk C (declWidth m) (m.outputs.map (·.name)) m.body Inv s.kids) :
    ∀ j (hj : j < envs.length), ∀ x ∈ (Sparkle.IR.HierCheck.openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x := by
  have hB := runModuleTG_typed C m Inv ht hwf hnd hIW (seedIn m ins)
    (fun t st hb n hn => by
      simp only [seedIn]
      split
      · rename_i hi
        exact hinsFit t n (by simpa [List.contains_eq_mem] using hi)
      · exact hb n hn) T s envs hrun hst hkids
  intro j hj x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact hB j hj p.name (ht.openX p hp)

/-! ## A gate child -/

/-- The per-child typing a gate child gives: a typed child, no clock / reset input, its emitted
widths no wider than its declared ones off its outputs. -/
abbrev KidTyped (m : Module) : Prop :=
  childTyped (declWidth m) m = true ∧ Tools.ShippingInstStmtG.isSeqChild m = false ∧
    ∀ x, x ∉ m.outputs.map (·.name) → Tools.ShippingDesignSV.weS m x ≤ declWidth m x

/-- **A gate child's emitted width of a name other than `out` is at most its declared one**:
a wire's is equal (sanitize-stable wires), any other name's is `0` (inputs are wires, the
output is `out`). -/
theorem gate_weS_le {c bs w} {m : Module} (h : Tools.ShippingGatePorts.GateChildPorts c bs w m)
    {x : String} (hx : x ≠ "out") : Tools.ShippingDesignSV.weS m x ≤ declWidth m x := by
  by_cases hw : x ∈ m.wires.map (·.name)
  · exact Nat.le_of_eq (Tools.ShippingWidthTables.declWidth_eq_weS h.wn hw).symm
  · have hnone : (m.wires ++ m.inputs ++ m.outputs).find?
        (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) = none := by
      rw [List.find?_eq_none]
      intro p hp hb
      have hs : Sparkle.Backend.Verilog.sanitizeName p.name = x := beq_iff_eq.mp hb
      rcases List.mem_append.mp hp with hp' | hp'
      · rcases List.mem_append.mp hp' with hpw | hpi
        · rw [h.wn p hpw] at hs
          exact hw (List.mem_map.mpr ⟨p, hpw, hs⟩)
        · have hpw := h.inWire p hpi
          rw [h.wn p hpw] at hs
          exact hw (List.mem_map.mpr ⟨p, hpw, hs⟩)
      · have hpo : p.name = "out" := (h.outWidth p hp').1
        rw [hpo] at hs
        have hso : Sparkle.Backend.Verilog.sanitizeName "out" = "out" := by
          simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
        rw [hso] at hs
        exact hx hs.symm
    have h0 : Tools.ShippingDesignSV.weS m x = 0 := by
      show (Tools.SVParser.RoundtripProof.moduleWof m x).getD 0 = 0
      -- UNSURE: the unfolding of `moduleWof` at `x`
      first
        | (simp only [Tools.SVParser.RoundtripProof.moduleWof, hnone, Option.bind_none,
            Option.getD_none])
        | (unfold Tools.SVParser.RoundtripProof.moduleWof
           rw [hnone]
           rfl)
        | simp [Tools.SVParser.RoundtripProof.moduleWof, hnone]
    rw [h0]
    exact Nat.zero_le _

/-- **A gate child is `KidTyped`.** -/
theorem kidTyped_of_gate {c bs w} {m : Module}
    (h : Tools.ShippingGatePorts.GateChildPorts c bs w m) : KidTyped m := by
  refine ⟨h.childTyped_ok, h.notSeq, fun x hx => gate_weS_le h ?_⟩
  intro e
  apply hx
  obtain ⟨ty, ho, -, -⟩ := h.out
  rw [ho, e]
  simp

/-! ## From the core run -/

section Core
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Compiler.Elab Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto
open Tools.ShippingChildInv
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

set_option maxHeartbeats 4000000 in
/-- **`TypedRun` of the full entry's module of a machine with calls** (memory / instance fields,
the closing `MachineClosesAt`), from the core run and ONE fact per kid: `FlatOk` (masked or the
built memory module: the free clause, by `mixCKS_boundedIn` on the one instance) or `KidTyped`
(the typed clause). The parent side is derived: typed assignments and no wire named as an output
(`core_closed_typedInMT`), each argument connection a wire at its `let` binder's width
(`core_callConnsMT`), `= ` the child's argument width (`callArgsOk`, `KidFactsTC.inW`). -/
theorem core_typedRunMT {c : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      Tools.ShippingMemKid.KidFactsTC mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    (hkidF : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingInstTagged.KidT mref cref (Tools.ShippingInstTagged.originAt d.shape k)
        (d.shape.insts[k]).1 y →
      Tools.ShippingMemKid.FlatOk y.1 ∨ KidTyped y.1)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    TypedRun (childMap D.modules) b Tools.ShippingMachineShipsHier.mixInv := by
  have hT : Tools.ShippingTextTyped.TypedIn b :=
    Tools.ShippingMemKid.core_closed_typedInMT d ok hbody hC hslots hdomB hins outTy hfne
      hB hcore hpost entry closes hon hoty
  have hconn := Tools.ShippingMemKid.core_callConnsMT d ok hbody hC hslots hdomB hins hfne outTy
    hB hcore hpost entry closes
  have hstm := Tools.ShippingMemKid.core_callStmtMT d ok hbody hC hslots hdomB hins hfne outTy
    hB hcore hpost entry closes
  refine ⟨fun l r hm => Tools.ShippingTypedWidthOk.typedIn_assignTyped hT hm, ?_, ?_⟩
  · -- an extracted input is a wire, and no wire has an output's name
    intro p hp hx
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hx
    have hpw : p ∈ b.wires := (List.mem_filter.mp hp).1
    exact hT.ow q hq p hpw hqn.symm
  · intro mn iname conns hm child cwe hc
    obtain ⟨mc, hmc, ⟨k, hk, y, hre, hmcy⟩, nIn, kI, n', names, args, outs, hcs⟩ :=
      hstm mn iname conns hm
    have hCm : childMap D.modules mn = some (mc, declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, declWidth g)) hmc
    have e : (mc, declWidth mc) = (child, cwe) := Option.some.inj (hCm.symm.trans hc)
    have e1 : mc = child := congrArg Prod.fst e
    have e2 : declWidth mc = cwe := congrArg Prod.snd e
    rcases hkidF k hk y hre with (⟨h1, h2⟩ | ⟨cb, aw, dw, hmem⟩) | hty
    · -- masked: the free clause
      left
      rw [← hmcy] at h1 h2
      have hK1 := Tools.ShippingMemKid.kidsMasked_one (iname := iname) (conns := conns) hCm h1 h2
      have hKM : KSBoundedIn (childMap D.modules) flatKS [Stmt.inst mn iname conns]
          Tools.ShippingMachineShipsHier.mixInv :=
        Tools.ShippingKidsMixedC.mixCKS_boundedIn _ _
          (by simp [Tools.ShippingKidsMixedC.kidsMixedC, hK1])
      exact hKM mn iname conns List.mem_cons_self child cwe hc
    · -- the built memory module: the free clause
      left
      rw [← hmcy] at hmem
      rw [hmem] at hcs hCm
      have hK1 := Tools.ShippingMemKid.kidsMem_one (iname := iname) hCm
        (Tools.ShippingMemKid.mem_conns_noRdata hcs)
      have hKM : KSBoundedIn (childMap D.modules) flatKS [Stmt.inst mn iname conns]
          Tools.ShippingMachineShipsHier.mixInv :=
        Tools.ShippingKidsMixedC.mixCKS_boundedIn _ _
          (by simp [Tools.ShippingKidsMixedC.kidsMixedC, hK1])
      exact hKM mn iname conns List.mem_cons_self child cwe hc
    · -- typed: the typed clause, its input connections from the run
      right
      rw [← hmcy] at hty
      rw [← e1, ← e2]
      refine ⟨hty.1, ?_, fun s => ?_, hty.2.2⟩
      · intro cn hcn hno x hx
        have hcm : (cn.1, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
          rw [← hx]
          exact hcn
        obtain ⟨mc', hmc', -, hall⟩ := hconn mn iname conns hm
        have hmm : mc' = mc := Option.some.inj (hmc'.symm.trans hmc)
        rcases hall cn.1 x hcm with ⟨hseq, -⟩ | ⟨hxw, k', hk', y', hre', hmcy', hside⟩
        · rw [hmm, hty.2.1] at hseq
          cases hseq
        · rcases hside with ⟨-, ⟨p, hp, hpn⟩, -⟩ | ⟨j, q, a, bn, hq, hqn, haj, hbn, hdw⟩
          · -- an output connection: excluded
            rw [hmm] at hp
            exact absurd (List.mem_map.mpr ⟨p, hp, hpn⟩) hno
          · -- an argument connection
            refine ⟨fun hxo => ?_, ?_⟩
            · obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hxw
              obtain ⟨q', hq', hq'n⟩ := List.mem_map.mp hxo
              exact hT.ow q' hq' p hp (hpn.trans hq'n.symm)
            · have hq1 : (Tools.ShippingInstStmtG.inPortsOf y'.1)[j]? = some q := by
                rw [← hmcy']
                exact hq
              obtain ⟨wd, hwd, hws⟩ := (hkid k' hk').inW y' hre' j q hq1
              have h5 := Tools.ShippingPortsMatchRaw.callArgs_width hargs hk' haj hbn hwd
              have hqm : q ∈ Tools.ShippingInstStmtG.inPortsOf mc' := List.mem_of_getElem? hq
              have hqo : q.name ∉ mc.outputs.map (·.name) := by
                intro hqo
                obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hqo
                have hpy : p ∈ y'.1.outputs := by
                  rw [← hmcy', hmm]
                  exact hp
                have hqy : q ∈ Tools.ShippingInstStmtG.inPortsOf y'.1 := by
                  rw [← hmcy']
                  exact hqm
                exact ((hkid k' hk').outsIn y' hre' p hpy).1 q hqy hpn.symm
              have hle := hty.2.2 q.name hqo
              rw [← hqn, hdw, h5, ← hws, ← hmcy', hmm]
              exact hle
      · -- the invariant is vacuous: a typed child has no memory
        intro hp
        rw [Tools.ShippingMachineShipsHier.memParams_noMem (noMem_of_childTyped hty.1)] at hp
        cases hp

end Core

end Tools.ShippingKidsTyped
