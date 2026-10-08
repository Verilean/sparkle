import Tools.ShippingDesignSV
import Tools.ShippingHierTyped

/-! # The width premises of the design's emitted texts, derived

`design_sv_runN` needs `SVBounds`: at every level, the seeding and the start
state within the emitted widths (`weS`). Here they are DERIVED, for any
finite depth, from
* the decidable `designCheck` (each module's emitted-text check `seqCheck`,
  width agreement, linked well-formedness, distinct instance names, no
  self-read, `PortsMatch`; leaves flat) — no further checker;
* the top seeding mapping bounded states to bounded environments (the top
  inputs within their emitted widths) and the start state bounded;
* every instance's start state bounded (`InvN`: the reset / initial state
  of the instance tree within the emitted widths).

The argument follows the LINKED ORDER inside each cycle — an instance's
inputs are computed before its outputs are written — so no step assumes the
bound it proves:
* `evalAssignsKG_envBound`: along one cycle's fold the environment stays
  bounded, every assignment's value fitting its target (`seqCheck`:
  `widthOf r = weS l`, `sf4_bounded`) and every instance's outputs fitting
  the wires they drive (its inputs being bounded when it steps);
* `KSn_stepBound`: a child's step at any depth, from bounded inputs and a
  bounded state, gives a bounded environment and a bounded next state
  (leaves: `emit_sem_assigns`, masked register updates; deeper: the fold,
  recursively);
* `runModuleTG_envBound`: every cycle's environment of the run is bounded;
* `svBounds_of_checks`: `SVBounds`. -/
namespace Tools.ShippingDesignSVBounds
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Tools.ShippingHierarchySoundness (connEnvS bindOuts)
open Tools.ShippingHierSVRun (oracle)
open Tools.ShippingDesignSV
open Tools.ShippingSeqSVSoundness (seqNames)
open Tools.ShippingHierSVSoundness (seqStmtOkI)

/-! ## Per-statement facts of the emitted-text check -/

theorem seqCheck_assign {wof : String → Option Nat} {we : WEnv} :
    ∀ {body : List Stmt}, Tools.SVParser.EmitSem.seqCheck wof we body = true →
      ∀ {l : String} {r : Expr}, Stmt.assign l r ∈ body →
        widthOf we r = we l ∧ Tools.SVParser.EmitSem.sf4Check wof we r = true
  | [], _, _, _, h => by cases h
  | st :: rest, hc, l, r, hm => by
    cases st with
    | assign l' r' =>
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true, beq_iff_eq] at hc
      rcases List.mem_cons.mp hm with he | hin
      · cases he; exact ⟨hc.1.1.2, hc.1.2⟩
      · exact seqCheck_assign hc.2 hin
    | register =>
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true] at hc
      rcases List.mem_cons.mp hm with he | hin
      · cases he
      · exact seqCheck_assign hc.2 hin
    | memory =>
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true] at hc
      rcases List.mem_cons.mp hm with he | hin
      · cases he
      · exact seqCheck_assign hc.2 hin
    | inst =>
      simp only [Tools.SVParser.EmitSem.seqCheck] at hc
      rcases List.mem_cons.mp hm with he | hin
      · cases he
      · exact seqCheck_assign hc hin

theorem refs_seqNames : ∀ {body : List Stmt} {l : String} {r : Expr}, Stmt.assign l r ∈ body →
    ∀ n ∈ Sparkle.IR.Reorder.refsOf r, n ∈ seqNames body
  | [], _, _, h => by cases h
  | st :: rest, l, r, hm => by
    intro n hn
    rcases List.mem_cons.mp hm with he | hin
    · subst he; simp only [seqNames]; exact List.mem_append_left _ hn
    · have := refs_seqNames hin n hn
      cases st with
      | assign => simp only [seqNames]; exact List.mem_append_right _ this
      | register => simp only [seqNames]; exact List.mem_cons_of_mem _ (List.mem_append_right _ this)
      | _ => simpa [seqNames] using this

/-- An assignment of a checked module writes a value within its target's
emitted width, from an environment within the emitted widths. -/
theorem assign_bound {o : Module} (hsv : Tools.SVParser.EmitSem.seqCheck (wofOf o) (weS o) o.body = true)
    (hwg : ∀ n ∈ seqNames o.body, declWidth o n = weS o n)
    {l : String} {r : Expr} (hm : Stmt.assign l r ∈ o.body)
    {env : Env} (hb : Bounded (weS o) env) {v : Nat}
    (hv : evalExpr (declWidth o) env r = some v) : v < 2 ^ weS o l := by
  obtain ⟨hw, hsf⟩ := seqCheck_assign hsv hm
  have hcongr : evalExpr (declWidth o) env r = evalExpr (weS o) env r :=
    Tools.ConeFold.evalExpr_we_congr _ _ env r (fun n hn => hwg n (refs_seqNames hm n hn))
  rw [hcongr] at hv
  have := Tools.SVParser.EmitSem.sf4_bounded (Tools.SVParser.EmitSem.sf4Check_sound hsf) hb v hv
  rwa [hw] at this

/-! ## One cycle's fold -/

/-- **One cycle's linked fold stays within the emitted widths**, given
that each assignment and each instance step does. -/
theorem evalAssignsKG_envBound {σ : Type} (KS : KStep σ) (W wS : WEnv)
    (C : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv) :
    ∀ (body : List Stmt) (env envF : Env) (acc acc' : String → σ),
      body.all seqStmtOkI = true →
      (∀ l r, Stmt.assign l r ∈ body → ∀ e v, Bounded wS e → evalExpr W e r = some v → v < 2 ^ wS l) →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe, C mn = some (child, cwe) →
        ∀ e cres s', Bounded wS e →
          KS child cwe (inConns child.outputs conns) e (kids iname) = some (cres, s') →
          ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) → cres p.name < 2 ^ wS w) →
      Bounded wS env →
      evalAssignsKG KS W C kids mems body env acc = some (envF, acc') →
      Bounded wS envF
  | [], env, envF, acc, acc', _, _, _, hb, h => by
    simp only [evalAssignsKG, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hb
  | st :: rest, env, envF, acc, acc', hok, hA, hI, hb, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have hA' := fun l r hm => hA l r (List.mem_cons_of_mem _ hm)
    have hI' := fun mn iname conns hm => hI mn iname conns (List.mem_cons_of_mem _ hm)
    cases st with
    | assign l r =>
      simp only [evalAssignsKG] at h
      cases hv : evalExpr W env r with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        refine evalAssignsKG_envBound KS W wS C kids mems rest _ envF acc acc' hok.2 hA' hI' ?_ h
        intro n
        by_cases he : n = l
        · subst he; simp only [if_true]; exact hA n r List.mem_cons_self env v hb hv
        · simp only [he, if_false]; exact hb n
    | register => exact evalAssignsKG_envBound KS W wS C kids mems rest env envF acc acc' hok.2 hA' hI' hb h
    | memory => simp [seqStmtOkI] at hok
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
          refine evalAssignsKG_envBound KS W wS C kids mems rest _ envF _ acc' hok.2 hA' hI' ?_ h
          exact fun n => Tools.ShippingHierTyped.bindOuts_pres (fun n v => v < 2 ^ wS n) conns cres
            child.outputs env (fun n => hb n)
            (fun p hp w hl => hI mn iname conns List.mem_cons_self child cwe hc env cres s' hb hk p hp w hl) n

/-! ## A child's step at any depth -/

/-- The instance tree's states within the emitted widths, at depth `n`. -/
def InvN (C : String → Option (Module × WEnv)) : (n : Nat) → Module → KT n → Prop
  | 0, child, ks => Bounded (weS child) (KidState.st ks)
  | m + 1, child, s => Bounded (weS child) s.st ∧
      ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ child.body → C mn = some (gc, gcwe) →
        InvN C m gc (s.kids iname)

/-- What a child stepping at depth `n` must pass. -/
def levelCheck (C : String → Option (Module × WEnv)) : Nat → Module → Bool
  | 0, child => leafCheck child
  | m + 1, child => designCheck C m child

/-- The connection-fed environment of a child is bounded when its inputs read
bounded values. -/
theorem connEnvS_bound {wS : WEnv} {cin : List (String × Expr)} {env : Env} {st : String → Nat}
    (hin : ∀ c ∈ cin, ∀ w, c.2 = .ref w → env w < 2 ^ wS c.1) (hst : Bounded wS st) :
    Bounded wS (connEnvS cin env st) := by
  intro n
  unfold connEnvS
  cases hl : cin.lookup n with
  | none => exact hst n
  | some e =>
    cases e with
    | ref w =>
      have := hin _ (Tools.ShippingHierSVRun.lookup_mem hl) w rfl
      simpa using this
    | _ => exact hst n

/-- A checked module's body is in the instance fragment and its regs/mems
step within its emitted widths. -/
theorem regs_bound {m : Module} (hok : m.body.all seqStmtOkI = true)
    (hwg : ∀ n ∈ seqNames m.body, declWidth m n = weS m n) {mems : MEnv} {envF : Env}
    {nexts : List (String × Nat)}
    (h : regNexts (declWidth m) mems m.body envF = some nexts) :
    ∀ pr ∈ nexts, pr.2 < 2 ^ weS m pr.1 := by
  rw [Tools.ShippingHierSVSoundness.regNexts_we_congrI hok hwg envF] at h
  exact Tools.ShippingHierSVSoundness.regNexts_boundedI hok h

theorem applyNexts_bound {wS : WEnv} {st : String → Nat} {nexts : List (String × Nat)}
    (hst : Bounded wS st) (hn : ∀ pr ∈ nexts, pr.2 < 2 ^ wS pr.1) : Bounded wS (applyNexts st nexts) :=
  Tools.ShippingSeqSVSoundness.applyNexts_bounded hst hn

/-- The step bound at depth `n`: a child stepping by `KSn C n`, from bounded
inputs and a bounded state, gives a bounded environment and state. -/
def StepBoundAt (ms : List Module) (n : Nat) : Prop :=
  ∀ (child : Module), levelCheck (Tools.ShippingMachineLinked.childMap ms) n child = true →
    ∀ (cin : List (String × Expr)) (env : Env) (s : KT n) (cres : Env) (s' : KT n),
      (∀ c ∈ cin, ∀ w, c.2 = .ref w → env w < 2 ^ weS child c.1) →
      InvN (Tools.ShippingMachineLinked.childMap ms) n child s →
      KSn (Tools.ShippingMachineLinked.childMap ms) n child (declWidth child) cin env s =
        some (cres, s') →
      Bounded (weS child) cres ∧ InvN (Tools.ShippingMachineLinked.childMap ms) n child s'

/-- **One cycle of a checked module whose children step at depth `m`**, from
a bounded environment, a bounded state and bounded children's states: a
bounded environment, state and children's states. -/
theorem moduleStepBound (ms : List Module) (m : Nat) (ih : StepBoundAt ms m) {o : Module}
    (hchk : designCheck (Tools.ShippingMachineLinked.childMap ms) m o = true)
    {env0 : Env} (hb0 : Bounded (weS o) env0) {s : KState (KT m)} (hst : Bounded (weS o) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
      Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
      InvN (Tools.ShippingMachineLinked.childMap ms) m gc (s.kids iname))
    {envF : Env} {s' : KState (KT m)}
    (h : stepModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) m) (declWidth o)
      (Tools.ShippingMachineLinked.childMap ms) o.body env0 s = some (envF, s')) :
    Bounded (weS o) envF ∧ Bounded (weS o) s'.st ∧
      ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
        Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
        InvN (Tools.ShippingMachineLinked.childMap ms) m gc (s'.kids iname) := by
  have hlc : designCheck (Tools.ShippingMachineLinked.childMap ms) m o = true := hchk
  obtain ⟨hok, hsv, hwg, hwf, hnd, hns, hpm, hres⟩ := textCheckI_sound (by
    cases m <;> simp only [designCheck, Bool.and_eq_true] at hlc <;> exact hlc.1)
  have hkp : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
      Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
      levelCheck (Tools.ShippingMachineLinked.childMap ms) m gc = true := by
    intro mn iname conns gc gcwe hm hc
    cases m with
    | zero => simp only [designCheck, Bool.and_eq_true] at hlc; exact kidsPass_at hlc.2 hm hc
    | succ m' => simp only [designCheck, Bool.and_eq_true] at hlc; exact kidsPass_at hlc.2 hm hc
  unfold stepModuleTG at h
  cases hK : evalAssignsKG (KSn (Tools.ShippingMachineLinked.childMap ms) m) (declWidth o)
      (Tools.ShippingMachineLinked.childMap ms) s.kids s.mems o.body env0 s.kids with
  | none => simp [hK] at h
  | some ek =>
  obtain ⟨envF', kids'⟩ := ek
  cases hN : regNexts (declWidth o) s.mems o.body envF' with
  | none => simp [hK, hN] at h
  | some nexts =>
  cases hM : memNexts (declWidth o) o.body s.mems envF' with
  | none => simp [hK, hN, hM] at h
  | some mems' =>
  simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hgc : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ gc gcwe,
      Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) → ∀ e cr ks', Bounded (weS o) e →
      KSn (Tools.ShippingMachineLinked.childMap ms) m gc gcwe (inConns gc.outputs conns) e (s.kids iname) =
        some (cr, ks') →
      Bounded (weS gc) cr ∧ InvN (Tools.ShippingMachineLinked.childMap ms) m gc ks' := by
    intro mn iname conns hm gc gcwe hc e cr ks' hbe hk
    obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
    cases hxe
    refine ih gc (hkp mn iname conns gc _ hm hc) _ e (s.kids iname) cr ks' ?_
      (hkids mn iname conns gc _ hm hc) hk
    intro c hcin w hw
    have := hbe w
    rwa [hpm mn iname conns gc _ hm hc c (List.mem_filter.mp hcin).1 w hw] at this
  have hbF : Bounded (weS o) envF' :=
    evalAssignsKG_envBound (KSn (Tools.ShippingMachineLinked.childMap ms) m) (declWidth o) (weS o)
      (Tools.ShippingMachineLinked.childMap ms) s.kids s.mems o.body _ envF' s.kids kids' hok
      (fun l r hm e v hbe hv => assign_bound hsv hwg hm hbe hv)
      (fun mn iname conns hm gc gcwe hc e cr ks' hbe hk p hp w hl => by
        have h1 := (hgc mn iname conns hm gc gcwe hc e cr ks' hbe hk).1 p.name
        rwa [← hpm mn iname conns gc gcwe hm hc (p.name, .ref w)
          (Tools.ShippingHierSVRun.lookup_mem hl) w rfl] at h1)
      hb0 hK
  refine ⟨hbF, applyNexts_bound hst (regs_bound hok hwg hN), ?_⟩
  intro mn iname conns gc gcwe hm hc
  obtain ⟨gc', gcwe', envAt, cr, hc', hk, hag, -⟩ :=
    Tools.ShippingHierOptLinked.linked_consistentKG (KSn (Tools.ShippingMachineLinked.childMap ms) m)
      (declWidth o) (Tools.ShippingMachineLinked.childMap ms) s.kids s.mems
      o.body _ envF' s.kids kids' hwf hnd hK mn iname conns hm
  rw [hc] at hc'
  cases hc'
  have hloc := KSn_local (Tools.ShippingMachineLinked.childMap ms) m gc gcwe (inConns gc.outputs conns)
    envAt envF' (s.kids iname)
    (fun c hcin w hw => hag c (List.mem_filter.mp hcin).1 w hw
      (Tools.ShippingHierPremisesBase.noSelfRead_sound hns mn iname conns hm gc gcwe hc c hcin w hw))
  rw [hloc] at hk
  exact (hgc mn iname conns hm gc gcwe hc envF' cr (kids' iname) hbF hk).2

/-- **A child's step at any depth stays within the emitted widths.** -/
theorem KSn_stepBound (ms : List Module) : ∀ n, StepBoundAt ms n
  | 0 => by
    intro child hlc cin env s cres s' hin hinv hstep
    obtain ⟨hlok, hlsv, hlwg⟩ := leafCheck_sound hlc
    have hokI := Tools.ShippingHierSVSoundness.seqStmtOkI_of_ok hlok
    have hseed := connEnvS_bound hin hinv
    change (stepModule (declWidth child) child.body (connEnvS cin env (KidState.st s))
      (KidState.mems s)).map (fun r => (r.1, (⟨applyNexts (KidState.st s) r.2.1, r.2.2⟩ : KidState))) =
      some (cres, s') at hstep
    cases hsm : stepModule (declWidth child) child.body (connEnvS cin env (KidState.st s)) (KidState.mems s) with
    | none => rw [hsm] at hstep; cases hstep
    | some r =>
      obtain ⟨envF, nexts, mems'⟩ := r
      rw [hsm] at hstep
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      rw [Tools.ShippingHierSVSoundness.stepModule_we_congrI hokI hlwg] at hsm
      unfold stepModule at hsm
      obtain ⟨pairs, env', _, hev, _, hbe, _⟩ := Tools.SVParser.EmitSem.emit_sem_assigns (KidState.mems s)
        child.body (connEnvS cin env (KidState.st s)) (Tools.SVParser.EmitSem.seqCheck_assigns hlsv)
        hseed (Tools.SVParser.EmitSem.bounded_iff_wof hseed)
      rw [hev] at hsm
      simp only [Option.bind_eq_bind, Option.bind_some] at hsm
      cases hn : regNexts (weS child) (KidState.mems s) child.body env' with
      | none => rw [hn] at hsm; simp at hsm
      | some nx =>
        rw [hn] at hsm
        simp only [Option.bind_some, Tools.ShippingHierSVSoundness.memNexts_okI hokI,
          Option.some.injEq, Prod.mk.injEq] at hsm
        obtain ⟨rfl, rfl, rfl⟩ := hsm
        exact ⟨hbe, applyNexts_bound hinv (Tools.ShippingHierSVSoundness.regNexts_boundedI hokI hn)⟩
  | m + 1 => by
    intro child hlc cin env s cres s' hin hinv hstep
    obtain ⟨hst, hkids⟩ := hinv
    obtain ⟨hbF, hst', hkids'⟩ := moduleStepBound ms m (KSn_stepBound ms m) hlc
      (connEnvS_bound hin hst) hst hkids hstep
    exact ⟨hbF, hst', hkids'⟩

/-- **Every cycle's environment of the run stays within the emitted widths**,
and so do the state and the children's states. -/
theorem runModuleTG_envBound (ms : List Module) (n : Nat) {o : Module}
    (hchk : designCheck (Tools.ShippingMachineLinked.childMap ms) n o = true)
    {seed : Nat → (String → Nat) → Env}
    (hseedB : ∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st)) :
    ∀ (T : Nat) (s : KState (KT n)) (envs : List Env),
      Bounded (weS o) s.st →
      (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
        Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
        InvN (Tools.ShippingMachineLinked.childMap ms) n gc (s.kids iname)) →
      runModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) n) (declWidth o)
        (Tools.ShippingMachineLinked.childMap ms) o.body seed T s = some envs →
      ∀ j (hj : j < envs.length), Bounded (weS o) (envs[j]'hj)
  | 0, s, envs, _, _, h, j, hj => by
    simp only [runModuleTG, Option.some.injEq] at h
    subst h; cases hj
  | k + 1, s, envs, hst, hkids, h, j, hj => by
    simp only [runModuleTG] at h
    cases hS : stepModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) n) (declWidth o)
        (Tools.ShippingMachineLinked.childMap ms) o.body (seed k s.st) s with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, s'⟩ := r
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) n) (declWidth o)
        (Tools.ShippingMachineLinked.childMap ms) o.body seed k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    obtain ⟨hbF, hst', hkids'⟩ := moduleStepBound ms n (KSn_stepBound ms n) hchk (hseedB k s.st hst)
      hst hkids hS
    cases j with
    | zero => exact hbF
    | succ j => exact runModuleTG_envBound ms n hchk hseedB k s' rest hst' hkids' hR j (by simpa using hj)

/-- The values of a cycle, read off the run (`envAt`), are bounded. -/
theorem envAt_bound {wS : WEnv} {envs : List Env} {T : Nat}
    (h : ∀ j (hj : j < envs.length), Bounded wS (envs[j]'hj)) : ∀ k, Bounded wS (envAt envs T k) := by
  intro k n
  simp only [envAt]
  cases hj : envs[T - 1 - k]? with
  | none => simp [Nat.two_pow_pos]
  | some e =>
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
    exact h _ hlt n

theorem oracle_bound {C : String → Option (Module × WEnv)} {body : List Stmt} {wS : WEnv}
    {E : Nat → Env} {seed : Nat → (String → Nat) → Env} (hE : ∀ k, Bounded wS (E k))
    (hseedB : ∀ k st, Bounded wS st → Bounded wS (seed k st)) :
    ∀ k st, Bounded wS st → Bounded wS (oracle C body E seed k st) := by
  intro k st hst n
  simp only [oracle, seedOuts]
  split
  · exact hE k n
  · exact hseedB k st hst n

/-- **The width premises of the design's emitted texts, derived**: from the
decidable `designCheck`, a top seeding within the emitted widths, and the
start states of the instance tree within their emitted widths. -/
theorem svBounds_of_checks (ms : List Module) :
    ∀ (n : Nat) (o : Module) (seed : Nat → (String → Nat) → Env) (T : Nat) (s : KState (KT n))
      (envs : List Env),
      designCheck (Tools.ShippingMachineLinked.childMap ms) n o = true →
      (∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st)) →
      Bounded (weS o) s.st →
      (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
        Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
        InvN (Tools.ShippingMachineLinked.childMap ms) n gc (s.kids iname)) →
      runModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) n) (declWidth o)
        (Tools.ShippingMachineLinked.childMap ms) o.body seed T s = some envs →
      SVBounds (Tools.ShippingMachineLinked.childMap ms) n o seed T s envs := by
  intro n
  induction n with
  | zero =>
    intro o seed T s envs hchk hseedB hst hkids hrun
    have hE := envAt_bound (T := T) (runModuleTG_envBound ms 0 hchk hseedB T s envs hst hkids hrun)
    simp only [designCheck, Bool.and_eq_true] at hchk
    obtain ⟨-, -, -, -, -, -, hpm, -⟩ := textCheckI_sound hchk.1
    refine ⟨⟨oracle_bound hE hseedB, hst⟩, ?_⟩
    intro mn iname conns child cwe hm hc
    refine ⟨fun k st' hst' => connEnvS_bound (fun c hcin w hw => ?_) hst', hkids mn iname conns child cwe hm hc⟩
    have := hE k w
    rwa [hpm mn iname conns child cwe hm hc c (List.mem_filter.mp hcin).1 w hw] at this
  | succ m ih =>
    intro o seed T s envs hchk hseedB hst hkids hrun
    have hE := envAt_bound (T := T) (runModuleTG_envBound ms (m + 1) hchk hseedB T s envs hst hkids hrun)
    have hchk' := hchk
    simp only [designCheck, Bool.and_eq_true] at hchk'
    obtain ⟨-, -, -, -, -, -, hpm, -⟩ := textCheckI_sound hchk'.1
    refine ⟨⟨oracle_bound hE hseedB, hst⟩, ?_⟩
    intro mn iname conns child cwe hm hc cenvs hcr
    obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
    cases hxe
    obtain ⟨hcst, hgk⟩ := hkids mn iname conns child _ hm hc
    exact ih child _ T (s.kids iname) cenvs (kidsPass_at hchk'.2 hm hc)
      (fun k st' hst' => connEnvS_bound (fun c hcin w hw => by
        have := hE k w
        rwa [hpm mn iname conns child _ hm hc c (List.mem_filter.mp hcin).1 w hw] at this) hst')
      hcst hgk hcr

end Tools.ShippingDesignSVBounds
