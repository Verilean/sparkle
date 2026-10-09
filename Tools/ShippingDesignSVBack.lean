import Tools.ShippingDesignSVBounds
import Tools.ShippingMachineCompose
import Tools.ShippingDesignSVLeaf

/-! # The closed emitted texts determine the run (backward simulation)

`design_sv_runN` is a forward simulation: the IR linked run IS a closed run
of the design's emitted texts (`DesignSV`). Here the converse:
`design_sv_backN` — EVERY closed run of the emitted texts, from a seeding and
states within the emitted widths, is the IR linked run. Hence the closed
relation has AT MOST ONE solution (`design_sv_unique`), and any solution is
the IR run. That a solution EXISTS is a separate fact: the forward theorem
(`design_sv_runN`) gives one when the IR run succeeds and its premises hold
— in the shipping endpoints, from the source shipping theorem's run.

No bound is assumed of the solution. The emitted texts' semantics masks
every assignment at its target's declared width (`evalAssignsSV`) and every
memory read at the data width, so a child's output port — assigned in its
body, or a leaf's combinational read target (`outsCheck`) — carries a value
within its width WHATEVER its inputs (`runModuleSV_assigned`); the parent's
instance-output wires carry exactly those values (`Supplies`), within the
same widths (`PortsMatch`); with the seeding and states within their widths,
every environment of the parent's text is then within its widths
(`runModuleSV_bounded`), its text runs as the IR open run
(`forward_trace_invI`), each child's text as the child's IR run (by
induction on the depth), and the open run with the children supplying the
instance outputs is the linked run (`runModuleTG_of_childRuns`). -/
namespace Tools.ShippingDesignSVBack
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Tools.ShippingHierarchySoundness (connEnvS)
open Tools.ShippingHierSVRun (oracle)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tools.ShippingSeqSVSoundness (seqNames)
open Tools.ShippingHierSVSoundness (seqStmtOkI)
open Tools.SVParser.EmitSem (CombStep emitAssigns evalAssignsSV regNextsSV runModuleSV weOf)

/-! ## The decidable fact the backward direction adds -/

/-- Every child of the design, at every level below `o`, assigns its outputs. -/
def outsCheck (C : String → Option (Module × WEnv)) : Nat → Module → Bool
  | 0, o => kidsPass C outsLeaf o.body
  | n + 1, o => kidsPass C (fun c => outsAssigned c && outsCheck C n c) o.body

/-! ## Transfer lemmas -/

/-- A module's emitted text, run from anywhere, carries its assigned outputs
within their widths. -/
theorem textRun_outs {m : Module} (hok : m.body.all seqStmtOkI = true) (hoa : outsAssigned m = true)
    {seed : Nat → (String → Nat) → Env} {T : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env}
    (h : TextRun m seed T st mems envs) :
    ∀ j (hj : j < envs.length), ∀ p ∈ m.outputs, (envs[j]'hj) p.name < 2 ^ weS m p.name := by
  obtain ⟨pairs, regs, mprog, hA, _, _, hrun⟩ := h
  intro j hj p hp
  obtain ⟨r, hr⟩ := outsAssigned_sound hoa p hp
  obtain ⟨sv, hsv⟩ := emitAssigns_mem hA hr
  exact runModuleSV_assigned (emitAssigns_assigns hok hA) hsv T st mems envs hrun j hj

/-- A checked module's emitted text, from a seeding and state within its
widths, runs as its IR open run, every environment within its widths. -/
theorem textRun_open {m : Module} (hok : m.body.all seqStmtOkI = true)
    (hsv : Tools.SVParser.EmitSem.seqCheck (wofOf m) (weS m) m.body = true)
    (hwg : ∀ n ∈ seqNames m.body, declWidth m n = weS m n)
    {seed : Nat → (String → Nat) → Env}
    (hseedB : ∀ k st, Bounded (weS m) st → Bounded (weS m) (seed k st))
    {T : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env} (hst : Bounded (weS m) st)
    (h : TextRun m seed T st mems envs) :
    runModule (declWidth m) m.body seed T st mems = some envs ∧
      ∀ j (hj : j < envs.length), Bounded (weS m) (envs[j]'hj) := by
  obtain ⟨pairs, regs, mprog, hA, hR, hM, hrun⟩ := h
  obtain ⟨pairs', regs', mprog', hA', hR', hM', heq⟩ :=
    Tools.ShippingHierSVSoundness.forward_trace_invI hsv hok seed hseedB
  rw [hA] at hA'; rw [hR] at hR'; rw [hM] at hM'
  simp only [Option.some.injEq] at hA' hR' hM'
  subst hA' hR' hM'
  refine ⟨?_, runModuleSV_bounded (emitAssigns_assigns hok hA) hseedB T st mems envs hst hrun⟩
  rw [Tools.ShippingHierSVSoundness.runModule_we_congrI m.body hok hwg seed T st mems, heq T st mems hst]
  exact hrun

/-- The instance-output wires of a closed run are within the parent's widths. -/
theorem instOuts_bound {C : String → Option (Module × WEnv)} {o : Module} {envs : List Env} {T : Nat}
    (hpm : PortsMatch C o)
    (hkids : ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
      ∃ cenvs : List Env, Supplies child conns envs cenvs ∧
        ∀ j (hj : j < cenvs.length), ∀ p ∈ child.outputs, (cenvs[j]'hj) p.name < 2 ^ weS child p.name) :
    ∀ k, ∀ x ∈ bodyInstOuts C o.body, envAt envs T k x < 2 ^ weS o x := by
  intro k x hx
  obtain ⟨mn, iname, conns, child, cwe, p, hm, hc, hp, hl⟩ := mem_bodyInstOuts hx
  obtain ⟨cenvs, ⟨hlen, hsup⟩, hb⟩ := hkids mn iname conns child cwe hm hc
  simp only [envAt]
  cases hj : envs[T - 1 - k]? with
  | none => simp [Nat.two_pow_pos]
  | some e =>
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [Option.getD_some]
    rw [hsup _ hlt (by omega) p hp x hl,
      hpm mn iname conns child cwe hm hc (p.name, .ref x) (Tools.ShippingHierSVRun.lookup_mem hl) x rfl]
    exact hb _ (by omega) p hp

theorem oracle_bound' {C : String → Option (Module × WEnv)} {body : List Stmt} {wS : WEnv}
    {E : Nat → Env} {seed : Nat → (String → Nat) → Env}
    (hE : ∀ k, ∀ x ∈ bodyInstOuts C body, E k x < 2 ^ wS x)
    (hseedB : ∀ k st, Bounded wS st → Bounded wS (seed k st)) :
    ∀ k st, Bounded wS st → Bounded wS (oracle C body E seed k st) := by
  intro k st hst x
  simp only [oracle, seedOuts]
  split
  · rename_i h; exact hE k x (by simpa using h)
  · exact hseedB k st hst x

/-- The open run from the oracle seeding, the children's own runs supplying
the instance outputs, is the linked run. -/
theorem open_linked {σ : Type} (KS : KStep σ) (hloc : KSLocal KS)
    {C : String → Option (Module × WEnv)} {o : Module} (hwf : linkedWF C o.body = true)
    (hnd : (instNames o.body).Nodup)
    (hns : Tools.ShippingHierPremisesBase.noSelfRead C o.body = true)
    {seed : Nat → (String → Nat) → Env} {T : Nat} {s : KState σ} {envs : List Env}
    (hopen : runModule (declWidth o) o.body (oracle C o.body (envAt envs T) seed) T s.st s.mems = some envs)
    (hkids : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∃ child cwe cenvs,
      C mn = some (child, cwe) ∧
      runKS KS child cwe (inConns child.outputs conns) (envAt envs T) T (s.kids iname) = some cenvs ∧
      Supplies child conns envs cenvs) :
    runModuleTG KS (declWidth o) C o.body seed T s = some envs := by
  have hlen := (Tools.ShippingMachineCompose.runModule_envs _ _ _ T s.st s.mems envs hopen).1
  refine runModuleTG_of_childRuns KS hloc (declWidth o) C o.body seed (oracle C o.body (envAt envs T) seed)
    hwf hnd (Tools.ShippingHierPremisesBase.noSelfRead_sound hns) ?_ (envAt envs T) T s envs hopen ?_ ?_
  · intro t st mems envF hF
    funext x
    simp only [oracle, seedOuts]
    split
    · rename_i hc
      have hx : x ∈ bodyInstOuts C o.body := by simpa using hc
      have := Tools.ShippingMachineLinked.evalAssigns_frame (declWidth o) mems C o.body _ envF x hwf hF
        (Tools.ShippingMachineCompose.instOuts_not_written o.body x hwf hx)
      simp only [oracle, seedOuts, hc, if_true] at this
      exact this.symm
    · rfl
  · intro j hj
    have hj' : j < envs.length := by omega
    rw [List.getElem?_eq_getElem hj', envAt_spec hlen j hj']
  · intro mn iname conns hm
    obtain ⟨child, cwe, cenvs, hc, hr, hlen', hsup⟩ := hkids mn iname conns hm
    refine ⟨child, cwe, cenvs, hc, hr, fun j hj p hp w hl => ?_⟩
    have hj1 : j < envs.length := by omega
    have hj2 : j < cenvs.length := by omega
    rw [List.getElem?_eq_getElem hj2, Option.map_some, ← hsup j hj1 hj2 p hp w hl, envAt_spec hlen j hj1]

/-! ## The backward simulation and uniqueness -/

/-- **Every closed run of the design's emitted texts is the IR linked run**
(backward simulation), for any finite depth: from a seeding and states
within the emitted widths, under `designCheck` and `outsCheck`. -/
theorem design_sv_backN (ms : List Module) :
    let C := Tools.ShippingMachineLinked.childMap ms
    ∀ (n : Nat) (o : Module) (seed : Nat → (String → Nat) → Env) (T : Nat) (s : KState (KT n))
      (envs : List Env),
      designCheck C n o = true → outsCheck C n o = true →
      (∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st)) →
      Bounded (weS o) s.st →
      (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (gc, gcwe) →
        InvN C n gc (s.kids iname)) →
      DesignSV C n o seed T s envs →
      runModuleTG (KSn C n) (declWidth o) C o.body seed T s = some envs := by
  intro C n
  induction n with
  | zero =>
    intro o seed T s envs hchk hoc hseedB hst hkids hD
    simp only [designCheck, Bool.and_eq_true] at hchk
    obtain ⟨hok, hsv, hwg, hwf, hnd, hns, -, -⟩ := textCheckI_sound hchk.1
    obtain ⟨htext, hres, hpm, hch⟩ := hD
    -- the children's outputs, from their texts alone
    have hout : ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
        ∃ cenvs : List Env, Supplies child conns envs cenvs ∧
          ∀ j (hj : j < cenvs.length), ∀ p ∈ child.outputs, (cenvs[j]'hj) p.name < 2 ^ weS child p.name := by
      intro mn iname conns child cwe hm hc
      obtain ⟨cenvs, ht, hsup⟩ := hch mn iname conns child cwe hm hc
      exact ⟨cenvs, hsup, leaf_outs (kidsPass_at hchk.2 hm hc) (kidsPass_at hoc hm hc) ht⟩
    have hseed' := oracle_bound' (instOuts_bound (T := T) hpm hout) hseedB
    obtain ⟨hopen, hbE⟩ := textRun_open hok hsv hwg hseed' hst htext
    have hE := envAt_bound (T := T) hbE
    refine open_linked (KSn C 0) (KSn_local C 0) hwf hnd hns hopen ?_
    intro mn iname conns hm
    obtain ⟨child, cwe, hc⟩ := hres mn iname conns hm
    obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
    cases hxe
    obtain ⟨cenvs, ht, hsup⟩ := hch mn iname conns child _ hm hc
    refine ⟨child, _, cenvs, hc, ?_, hsup⟩
    have hrun := leaf_backward (kidsPass_at hchk.2 hm hc)
      (fun k st' hst' => connEnvS_bound (fun c hcin w hw => by
        have := hE k w
        rwa [hpm mn iname conns child _ hm hc c (List.mem_filter.mp hcin).1 w hw] at this) hst')
      (hkids mn iname conns child _ hm hc) ht
    exact (runKS_flat child _ _ _ T (s.kids iname)).trans hrun
  | succ m ih =>
    intro o seed T s envs hchk hoc hseedB hst hkids hD
    simp only [designCheck, Bool.and_eq_true] at hchk
    obtain ⟨hok, hsv, hwg, hwf, hnd, hns, -, -⟩ := textCheckI_sound hchk.1
    obtain ⟨htext, hres, hpm, hch⟩ := hD
    have hout : ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
        ∃ cenvs : List Env, Supplies child conns envs cenvs ∧
          ∀ j (hj : j < cenvs.length), ∀ p ∈ child.outputs, (cenvs[j]'hj) p.name < 2 ^ weS child p.name := by
      intro mn iname conns child cwe hm hc
      obtain ⟨cenvs, hcd, hsup⟩ := hch mn iname conns child cwe hm hc
      have hcc := kidsPass_at hchk.2 hm hc
      have hco := kidsPass_at hoc hm hc
      simp only [Bool.and_eq_true] at hco
      have hcok : child.body.all seqStmtOkI = true := by
        cases m <;> simp only [designCheck, Bool.and_eq_true] at hcc <;>
          exact (textCheckI_sound hcc.1).1
      cases m with
      | zero => exact ⟨cenvs, hsup, textRun_outs hcok hco.1 hcd.1⟩
      | succ m' => exact ⟨cenvs, hsup, textRun_outs hcok hco.1 hcd.1⟩
    have hseed' := oracle_bound' (instOuts_bound (T := T) hpm hout) hseedB
    obtain ⟨hopen, hbE⟩ := textRun_open hok hsv hwg hseed' hst htext
    have hE := envAt_bound (T := T) hbE
    refine open_linked (KSn C (m + 1)) (KSn_local C (m + 1)) hwf hnd hns hopen ?_
    intro mn iname conns hm
    obtain ⟨child, cwe, hc⟩ := hres mn iname conns hm
    obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
    cases hxe
    obtain ⟨cenvs, hcd, hsup⟩ := hch mn iname conns child _ hm hc
    obtain ⟨hcst, hgk⟩ := hkids mn iname conns child _ hm hc
    have hco := kidsPass_at hoc hm hc
    simp only [Bool.and_eq_true] at hco
    have hrun := ih child _ T (s.kids iname) cenvs (kidsPass_at hchk.2 hm hc) hco.2
      (fun k st' hst' => connEnvS_bound (fun c hcin w hw => by
        have := hE k w
        rwa [hpm mn iname conns child _ hm hc c (List.mem_filter.mp hcin).1 w hw] at this) hst')
      hcst hgk hcd
    exact ⟨child, _, cenvs, hc, (runKS_succ (KSn C m) C child _ _ _ T (s.kids iname)).trans hrun, hsup⟩

/-- **The closed run of the design's emitted texts is unique**: two closed
runs from the same seeding and states (within the emitted widths) are the
same run. -/
theorem design_sv_unique (ms : List Module) (n : Nat) (o : Module)
    (seed : Nat → (String → Nat) → Env) (T : Nat) (s : KState (KT n)) (envs envs' : List Env)
    (hchk : designCheck (Tools.ShippingMachineLinked.childMap ms) n o = true)
    (hoc : outsCheck (Tools.ShippingMachineLinked.childMap ms) n o = true)
    (hseedB : ∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st))
    (hst : Bounded (weS o) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
      Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
      InvN (Tools.ShippingMachineLinked.childMap ms) n gc (s.kids iname))
    (h1 : DesignSV (Tools.ShippingMachineLinked.childMap ms) n o seed T s envs)
    (h2 : DesignSV (Tools.ShippingMachineLinked.childMap ms) n o seed T s envs') :
    envs = envs' := by
  have r1 := design_sv_backN ms n o seed T s envs hchk hoc hseedB hst hkids h1
  have r2 := design_sv_backN ms n o seed T s envs' hchk hoc hseedB hst hkids h2
  rw [r1] at r2
  exact Option.some.inj r2

/-- **Every closed run shows what one does**: given one closed run with a
property (e.g. the source's values on the output ports, from
`ships_design_svN`), every closed run from the same seeding and states has
it — there is only one. -/
theorem design_sv_all (ms : List Module) (n : Nat) (o : Module)
    (seed : Nat → (String → Nat) → Env) (T : Nat) (s : KState (KT n)) (envs : List Env)
    (P : List Env → Prop)
    (hchk : designCheck (Tools.ShippingMachineLinked.childMap ms) n o = true)
    (hoc : outsCheck (Tools.ShippingMachineLinked.childMap ms) n o = true)
    (hseedB : ∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st))
    (hst : Bounded (weS o) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
      Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
      InvN (Tools.ShippingMachineLinked.childMap ms) n gc (s.kids iname))
    (h : DesignSV (Tools.ShippingMachineLinked.childMap ms) n o seed T s envs) (hP : P envs) :
    ∀ envs', DesignSV (Tools.ShippingMachineLinked.childMap ms) n o seed T s envs' → P envs' := by
  intro envs' h'
  rw [← design_sv_unique ms n o seed T s envs envs' hchk hoc hseedB hst hkids h h']
  exact hP

end Tools.ShippingDesignSVBack
