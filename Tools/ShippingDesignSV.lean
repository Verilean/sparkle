import Tools.ShippingHierSVRun
import Tools.ShippingHierPremisesBase
import Tools.ShippingSeqSVSoundness
import Tools.ShippingDesignSVLeaf

/-! # The emitted Verilog of a whole design, at any depth

`linked_sv_run` / `shipped_sv` run the PARENT's emitted text against an
ORACLE: the values of the instance-output wires are taken from the linked
run. Here the oracle is REALIZED by the children's own emitted texts,
recursively, at any finite depth.

`DesignSV C n o seed T s envs` (a relation; it embeds no IR run) says:
* the emitted text of `o` runs from the oracle seeding built from `envs` to
  `envs` (`TextRun`);
* every instance of `o` resolves in the design `C` (`Resolved`) — no
  instance output is left to the oracle unexplained;
* for every instance, its child — looked up in `C`, starting from the
  instance's OWN state `s.kids iname`, fed at each cycle with that cycle's
  values on its input connections (`connSeed`) — runs to environments whose
  output ports carry the values of the wires the instance drives, at the same
  cycle (`Supplies`): at depth 0 the child's own emitted text, and the child
  must be flat (`seqStmtOk`: no instance, nothing left free); at depth
  `n + 1`, recursively `DesignSV C n` of the child.

`design_sv_runN` is a FORWARD SIMULATION: a run of the IR linked semantics
at depth `n` (`runModuleTG (KSn C n)`), under the decidable `designCheck`
and the width premises along the run (`SVBounds`), gives a closed run of the
emitted texts with the SAME environments. It does not say the closed
relation is unique (that the connected texts admit no other run); see the
note at the end. -/
namespace Tools.ShippingDesignSV
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Tools.ShippingHierarchySoundness (connEnvS)
open Tools.ShippingHierSVRun (oracle)
open Tools.ShippingHierOptLinked (linked_consistentKG)

/-- The environment of cycle `k` (the seed index counts down). -/
def envAt (envs : List Env) (T : Nat) : Nat → Env := fun k => (envs[T - 1 - k]?).getD (fun _ => 0)

/-- A child's seeding: its input connections read the parent's values of the cycle. -/
def connSeed (cin : List (String × Expr)) (E : Nat → Env) : Nat → (String → Nat) → Env :=
  fun k st => connEnvS cin (E k) st

/-- Every instance resolves in the design. -/
def Resolved (C : String → Option (Module × WEnv)) (body : List Stmt) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∃ child cwe, C mn = some (child, cwe)

/-- The child's run supplies, cycle by cycle, the wires the instance drives. -/
def Supplies (child : Module) (conns : List (String × Expr)) (envs cenvs : List Env) : Prop :=
  cenvs.length = envs.length ∧
    ∀ j (hj : j < envs.length) (hj' : j < cenvs.length), ∀ p ∈ child.outputs, ∀ w,
      conns.lookup p.name = some (.ref w) → (envs[j]'hj) w = (cenvs[j]'hj') p.name

/-- Every connection of every instance joins a parent wire and a child port
of the SAME emitted width (so connecting the texts neither truncates nor
extends a value). -/
def PortsMatch (C : String → Option (Module × WEnv)) (o : Module) : Prop :=
  ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
    ∀ c ∈ conns, ∀ w, c.2 = .ref w → weS o w = weS child c.1

def portsMatchB (C : String → Option (Module × WEnv)) (o : Module) : Bool :=
  o.body.all fun st => match st with
    | .inst mn _ conns => match C mn with
      | some (child, _) => conns.all fun c => match c.2 with
        | .ref w => weS o w == weS child c.1
        | _ => true
      | none => false
    | _ => true

theorem portsMatchB_sound {C : String → Option (Module × WEnv)} {o : Module}
    (h : portsMatchB C o = true) : PortsMatch C o := by
  intro mn iname conns child cwe hm hc c hcm w hw
  have h1 := List.all_eq_true.mp h _ hm
  simp only [hc] at h1
  have h2 := List.all_eq_true.mp h1 c hcm
  rw [hw] at h2
  simpa using h2

/-- **The closed run of a design's emitted texts, at depth `n`.** -/
def DesignSV (C : String → Option (Module × WEnv)) :
    (n : Nat) → Module → (Nat → (String → Nat) → Env) → Nat → KState (KT n) → List Env → Prop
  | 0, o, seed, T, s, envs =>
    TextRun o (oracle C o.body (envAt envs T) seed) T s.st s.mems envs ∧ Resolved C o.body ∧
    PortsMatch C o ∧
    ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
      ∃ cenvs, LeafRun child (connSeed (inConns child.outputs conns) (envAt envs T)) T
          (KidState.st (s.kids iname)) (KidState.mems (s.kids iname)) cenvs ∧
        Supplies child conns envs cenvs
  | n + 1, o, seed, T, s, envs =>
    TextRun o (oracle C o.body (envAt envs T) seed) T s.st s.mems envs ∧ Resolved C o.body ∧
    PortsMatch C o ∧
    ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
      ∃ cenvs, DesignSV C n child (connSeed (inConns child.outputs conns) (envAt envs T)) T
          (s.kids iname) cenvs ∧
        Supplies child conns envs cenvs

/-! ## The decidable checks and the width premises -/

/-- A module's own emitted-text checks (`seq_run_to_svI`'s, `linked_sv_run`'s). -/
def textCheckI (C : String → Option (Module × WEnv)) (o : Module) : Bool :=
  o.body.all Tools.ShippingHierSVSoundness.seqStmtOkI &&
    Tools.SVParser.EmitSem.seqCheck (wofOf o) (weS o) o.body &&
    (Tools.ShippingSeqSVSoundness.seqNames o.body).all (fun x => declWidth o x == weS o x) &&
    linkedWF C o.body && decide (instNames o.body).Nodup &&
    Tools.ShippingHierPremisesBase.noSelfRead C o.body && portsMatchB C o &&
    o.body.all (fun st => match st with
      | .inst mn _ _ => (C mn).isSome
      | _ => true)

/-- Each instance's child passes `f`. -/
def kidsPass (C : String → Option (Module × WEnv)) (f : Module → Bool) (body : List Stmt) : Bool :=
  body.all fun st => match st with
    | .inst mn _ _ => match C mn with
      | some (child, _) => f child
      | none => false
    | _ => true

/-- **The decidable checks of a design at depth `n`.** -/
def designCheck (C : String → Option (Module × WEnv)) : Nat → Module → Bool
  | 0, o => textCheckI C o && kidsPass C leafCheck o.body
  | n + 1, o => textCheckI C o && kidsPass C (designCheck C n) o.body

/-- The width premises of the parent's oracle seeding and start state. -/
def ParentBounds (C : String → Option (Module × WEnv)) (o : Module)
    (seed : Nat → (String → Nat) → Env) (T : Nat) (st : String → Nat) (envs : List Env) : Prop :=
  (∀ k st', Bounded (weS o) st' → Bounded (weS o) (oracle C o.body (envAt envs T) seed k st')) ∧
    Bounded (weS o) st

/-- **The width premises along the IR run**, at every level: each module's
seeding and start state within its emitted widths. (Run-level premises; a
later unit derives them from width checks and the inputs.) -/
def SVBounds (C : String → Option (Module × WEnv)) :
    (n : Nat) → Module → (Nat → (String → Nat) → Env) → Nat → KState (KT n) → List Env → Prop
  | 0, o, seed, T, s, envs =>
    ParentBounds C o seed T s.st envs ∧
    ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
      (∀ k st', Bounded (weS child) st' →
        Bounded (weS child) (connSeed (inConns child.outputs conns) (envAt envs T) k st')) ∧
      Bounded (weS child) (KidState.st (s.kids iname))
  | n + 1, o, seed, T, s, envs =>
    ParentBounds C o seed T s.st envs ∧
    ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
      ∀ cenvs, runModuleTG (KSn C n) (declWidth child) C child.body
          (connSeed (inConns child.outputs conns) (envAt envs T)) T (s.kids iname) = some cenvs →
        SVBounds C n child (connSeed (inConns child.outputs conns) (envAt envs T)) T (s.kids iname) cenvs

/-! ## Each instance's child runs on its connections -/

/-- **Each instance's child runs on its connections**, for any local child
step: along a linked run, the child of an instance runs (`runKS`) fed at
each cycle with the cycle's values on its input connections, from the
instance's own state, and its outputs are the values of the wires they
drive. (`child_run_of_linked` is the `flatKS` case.) -/
theorem child_runKS_of_linked {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) (W : WEnv)
    (children : String → Option (Module × WEnv))
    (body : List Stmt) (seed : Nat → (String → Nat) → Env) (E : Nat → Env)
    (hwf : linkedWF children body = true) (hnd : (instNames body).Nodup)
    {mn iname : String} {conns : List (String × Expr)} {child : Module} {cwe : WEnv}
    (hmem : Stmt.inst mn iname conns ∈ body) (hc : children mn = some (child, cwe))
    (hnofb : ∀ c ∈ inConns child.outputs conns, ∀ w, c.2 = .ref w →
      w ∉ instOutWires child.outputs conns) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS W children body seed T s = some envs →
      (∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j)) →
      ∃ cenvs, runKS KS child cwe (inConns child.outputs conns) E T (s.kids iname) = some cenvs ∧
        Supplies child conns envs cenvs
  | 0, s, envs, h, _ => by
    simp only [runModuleTG, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl, fun j hj => by cases hj⟩
  | k + 1, s, envs, h, hE => by
    simp only [runModuleTG] at h
    cases hS : stepModuleTG KS W children body (seed k s.st) s with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, s'⟩ := r
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG KS W children body seed k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    unfold stepModuleTG at hS
    cases hK : evalAssignsKG KS W children s.kids s.mems body (seed k s.st) s.kids with
    | none => simp [hK] at hS
    | some ek =>
    obtain ⟨envF', kids'⟩ := ek
    cases hN : regNexts W s.mems body envF' with
    | none => simp [hK, hN] at hS
    | some nexts =>
    cases hM : memNexts W body s.mems envF' with
    | none => simp [hK, hN, hM] at hS
    | some mems' =>
    simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    have hE0 : envF' = E k := by
      have := hE 0 (by simp)
      simpa using this
    obtain ⟨child', cwe', envAt', cres, hc', hk, hin, hout⟩ :=
      linked_consistentKG KS W children s.kids s.mems body _ envF' s.kids kids' hwf hnd hK
        mn iname conns hmem
    rw [hc] at hc'
    cases hc'
    -- the child's step reads only its input connections: the cycle's final values
    have hk' : KS child cwe (inConns child.outputs conns) (E k) (s.kids iname) =
        some (cres, kids' iname) := by
      rw [← hk]
      apply hloc
      intro c hcin w hw
      rw [← hE0]
      exact (hin c (List.mem_filter.mp hcin).1 w hw (hnofb c hcin w hw)).symm
    have ih := child_runKS_of_linked KS hloc W children body seed E hwf hnd hmem hc hnofb k
      ⟨applyNexts s.st nexts, mems', kids'⟩ rest hR (fun j hj => by
        have := hE (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [this]
        congr 1
        omega)
    obtain ⟨crest, hcr, hcl, hco⟩ := ih
    refine ⟨cres :: crest, ?_, by simp [hcl], ?_⟩
    · simp only [runKS, hk', Option.bind_eq_bind, Option.bind_some]
      rw [show (⟨applyNexts s.st nexts, mems', kids'⟩ : KState σ).kids iname = kids' iname from rfl] at hcr
      rw [hcr]
      rfl
    · intro j hj hj' p hp w hl
      cases j with
      | zero => exact hout p hp w hl
      | succ j => exact hco j (by simpa using hj) (by simpa using hj') p hp w hl

/-! ## The forward simulation -/

theorem envAt_spec {envs : List Env} {T : Nat} (hlen : envs.length = T) :
    ∀ j (hj : j < envs.length), envs[j] = envAt envs T (T - 1 - j) := by
  intro j hj
  simp only [envAt]
  rw [show T - 1 - (T - 1 - j) = j by omega]
  simp [hj]

theorem textCheckI_sound {C : String → Option (Module × WEnv)} {o : Module}
    (h : textCheckI C o = true) :
    o.body.all Tools.ShippingHierSVSoundness.seqStmtOkI = true ∧
    Tools.SVParser.EmitSem.seqCheck (wofOf o) (weS o) o.body = true ∧
    (∀ n ∈ Tools.ShippingSeqSVSoundness.seqNames o.body, declWidth o n = weS o n) ∧
    linkedWF C o.body = true ∧ (instNames o.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead C o.body = true ∧ PortsMatch C o ∧ Resolved C o.body := by
  simp only [textCheckI, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hok, hsv⟩, hwg⟩, hwf⟩, hnd⟩, hns⟩, hpm⟩, hres⟩ := h
  refine ⟨hok, hsv, fun n hn => ?_, hwf, hnd, hns, portsMatchB_sound hpm, fun mn iname conns hm => ?_⟩
  · have := List.all_eq_true.mp hwg n hn
    simpa using this
  · have := List.all_eq_true.mp hres _ hm
    simp only at this
    obtain ⟨⟨child, cwe⟩, hc⟩ := Option.isSome_iff_exists.mp this
    exact ⟨child, cwe, hc⟩

theorem kidsPass_at {C : String → Option (Module × WEnv)} {f : Module → Bool} {body : List Stmt}
    (h : kidsPass C f body = true) {mn iname : String} {conns : List (String × Expr)}
    {child : Module} {cwe : WEnv} (hm : Stmt.inst mn iname conns ∈ body)
    (hc : C mn = some (child, cwe)) : f child = true := by
  have := List.all_eq_true.mp h _ hm
  simp only [hc] at this
  exact this

/-- **The IR linked run at depth `n` is a closed run of the design's emitted
texts** (forward simulation): along a run of `o`'s module with its children
stepping at depth `n` (`KSn`), under the decidable `designCheck` and the
width premises `SVBounds`, the emitted texts of `o` and of all its
descendants — each child from its instance's own state, fed at each cycle
with its input connections' values — run to the same environments, the
children supplying every instance-output wire. -/
theorem design_sv_runN (ms : List Module) :
    let C := Tools.ShippingMachineLinked.childMap ms
    ∀ (n : Nat) (o : Module) (seed : Nat → (String → Nat) → Env) (T : Nat) (s : KState (KT n))
      (envs : List Env),
      designCheck C n o = true →
      runModuleTG (KSn C n) (declWidth o) C o.body seed T s = some envs →
      SVBounds C n o seed T s envs →
      DesignSV C n o seed T s envs := by
  intro C n
  induction n with
  | zero =>
    intro o seed T s envs hchk hrun hB
    simp only [designCheck, Bool.and_eq_true] at hchk
    obtain ⟨hok, hsv, hwg, hwf, hnd, hns, hpm, hres⟩ := textCheckI_sound hchk.1
    obtain ⟨⟨hsb, hst⟩, hkB⟩ := hB
    have hlen := runModuleTG_length (KSn C 0) _ C o.body seed T s envs hrun
    refine ⟨Tools.ShippingHierSVRun.linked_sv_run (KSn C 0) C hwf hok hsv hwg hrun hsb hst, hres, hpm, ?_⟩
    intro mn iname conns child cwe hm hc
    have hleaf := kidsPass_at hchk.2 hm hc
    obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
    cases hxe
    obtain ⟨cenvs, hcr, hsup⟩ := child_runKS_of_linked (KSn C 0) (KSn_local C 0) _ C o.body seed
      (envAt envs T) hwf hnd hm hc (Tools.ShippingHierPremisesBase.noSelfRead_sound hns mn iname conns hm child _ hc)
      T s envs hrun (envAt_spec hlen)
    have hcr' : runModule (declWidth child) child.body
        (connSeed (inConns child.outputs conns) (envAt envs T)) T
        (KidState.st (s.kids iname)) (KidState.mems (s.kids iname)) = some cenvs := by
      have := runKS_flat child (declWidth child) (inConns child.outputs conns) (envAt envs T) T (s.kids iname)
      exact this.symm.trans hcr
    obtain ⟨hcs, hcst⟩ := hkB mn iname conns child _ hm hc
    exact ⟨cenvs, leaf_forward hleaf hcs hcst hcr', hsup⟩
  | succ m ih =>
    intro o seed T s envs hchk hrun hB
    simp only [designCheck, Bool.and_eq_true] at hchk
    obtain ⟨hok, hsv, hwg, hwf, hnd, hns, hpm, hres⟩ := textCheckI_sound hchk.1
    obtain ⟨⟨hsb, hst⟩, hkB⟩ := hB
    have hlen := runModuleTG_length (KSn C (m + 1)) _ C o.body seed T s envs hrun
    refine ⟨Tools.ShippingHierSVRun.linked_sv_run (KSn C (m + 1)) C hwf hok hsv hwg hrun hsb hst, hres, hpm, ?_⟩
    intro mn iname conns child cwe hm hc
    have hsub := kidsPass_at hchk.2 hm hc
    obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
    cases hxe
    obtain ⟨cenvs, hcr, hsup⟩ := child_runKS_of_linked (KSn C (m + 1)) (KSn_local C (m + 1)) _ C
      o.body seed (envAt envs T) hwf hnd hm hc
      (Tools.ShippingHierPremisesBase.noSelfRead_sound hns mn iname conns hm child _ hc)
      T s envs hrun (envAt_spec hlen)
    have hcr' : runModuleTG (KSn C m) (declWidth child) C child.body
        (connSeed (inConns child.outputs conns) (envAt envs T)) T (s.kids iname) = some cenvs := by
      have := runKS_succ (KSn C m) C child (declWidth child) (inConns child.outputs conns)
        (envAt envs T) T (s.kids iname)
      exact this.symm.trans hcr
    exact ⟨cenvs, ih child _ T (s.kids iname) cenvs hsub hcr' (hkB mn iname conns child _ hm hc cenvs hcr'), hsup⟩

end Tools.ShippingDesignSV
