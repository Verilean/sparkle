import Tools.ShippingFGCircuitS3tSpec
set_option autoImplicit false
-- FG circuit pilot S3t, step 1 (example): the four seed premises of `RootShowsAt` — `(a)` the input ports carry the source's inputs (`SourceInputs`), `(b)` a register reads the state, `(c)` reset is 0, `(d)` the initial value of register k is its slot's init — are SIMULTANEOUSLY SATISFIABLE, for every inputs, run length, and every compiler ids/cache/regs that satisfy the naming facts of `MachineWired` (names distinct and allocated, the registers among the slot/`let` ports).  A statement about the premises, not about any IR.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §69.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3tSat
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Compiler.Elab
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedInputSoundness
open Tools.ShippingMuxLoweringSoundness (encodeBool)

/-- the names the allocator gives the ports of a binder list from a circuit state (domain binders have none) -/
def portNamesOf : List ((Name × MixedGateBinder) × FVarId) → Sparkle.IR.Builder.CircuitState → List String
  | [], _ => []
  | ((_, .domain), _) :: rest, st => portNamesOf rest st
  | ((name, .bool), _) :: rest, st =>
    inputWire st name.toString .bit :: portNamesOf rest (inputState st name.toString .bit)
  | ((name, .bits n), _) :: rest, st =>
    inputWire st name.toString (.bitVector n) :: portNamesOf rest (inputState st name.toString (.bitVector n))

theorem inputPorts_names (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup) :
    (inputPorts bools bits L a).map (·.name) = portNamesOf L a.state := by
  induction L generalizing a with
  | nil => rfl
  | cons binder rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact ih _
    | bool => simp only [inputPorts, portNamesOf, List.map_cons, ih (extend a ((name, .bool), id) bools bits)]; rfl
    | bits n => simp only [inputPorts, portNamesOf, List.map_cons, ih (extend a ((name, .bits n), id) bools bits)]; rfl

/-- the source value at a port: the bool's code or the bit-vector's number -/
def valOf (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    (Name × MixedGateBinder) × FVarId → Nat
  | ((_, .domain), _) => 0
  | ((_, .bool), id) => encodeBool (bools id)
  | ((_, .bits n), id) => (bits id n).toNat

/-- `Admissible` follows from the port values: when the ports are `portNamesOf` and `initial` carries the value at each -/
theorem admissible_of_ports (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) (initial : Env) :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup), (∀ x ∈ L, x.1.2 ≠ .domain) →
      (∀ p ∈ (portNamesOf L a.state).zip (L.map (valOf bools bits)), initial p.1 = p.2) →
      Admissible bools bits initial L a := by
  intro L
  induction L with
  | nil => intro a _ _; trivial
  | cons binder rest ih =>
    intro a hnd hval
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact absurd rfl (hnd _ (List.mem_cons_self ..))
    | bool =>
      refine ⟨?_, ih _ (fun x hx => hnd x (List.mem_cons_of_mem _ hx)) ?_⟩
      · exact hval (inputWire a.state name.toString .bit, encodeBool (bools id)) (List.mem_cons_self ..)
      · intro p hp
        have h2 : p ∈ ((inputWire a.state name.toString .bit) :: portNamesOf rest (inputState a.state name.toString .bit)).zip
            (encodeBool (bools id) :: List.map (valOf bools bits) rest) := List.mem_cons_of_mem _ hp
        exact hval p h2
    | bits n =>
      refine ⟨?_, ih _ (fun x hx => hnd x (List.mem_cons_of_mem _ hx)) ?_⟩
      · exact hval (inputWire a.state name.toString (.bitVector n), (bits id n).toNat) (List.mem_cons_self ..)
      · intro p hp
        have h2 : p ∈ ((inputWire a.state name.toString (.bitVector n)) :: portNamesOf rest (inputState a.state name.toString (.bitVector n))).zip
            ((bits id n).toNat :: List.map (valOf bools bits) rest) := List.mem_cons_of_mem _ hp
        exact hval p h2

/-! ### the seed: an association list over the first `kD` port names -/

/-- the value an association list gives a name, or the default -/
def lk (P : List (String × Nat)) (n : String) (d : Nat) : Nat :=
  match P.find? (fun p => p.1 == n) with
  | some p => p.2
  | none => d

theorem lk_mem : ∀ (P : List (String × Nat)), (P.map Prod.fst).Nodup → ∀ p ∈ P, ∀ d, lk P p.1 d = p.2
  | [], _, p, hp, _ => by simp at hp
  | q :: rest, hnd, p, hp, d => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [lk]
    · have hne : q.1 ≠ p.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hp)
      have := lk_mem rest hnd.2 p hp d
      simp only [lk, List.find?_cons] at this ⊢
      have hb : (q.1 == p.1) = false := by simpa using hne
      simp [hb, this]

theorem lk_not_mem : ∀ (P : List (String × Nat)) (n : String), n ∉ P.map Prod.fst → ∀ d, lk P n d = d
  | [], n, _, d => by simp [lk]
  | q :: rest, n, h, d => by
    rw [List.map_cons, List.mem_cons, not_or] at h
    have := lk_not_mem rest n h.2 d
    simp only [lk, List.find?_cons] at this ⊢
    have hb : (q.1 == n) = false := by simpa using (Ne.symm h.1)
    simp [hb, this]

/-- the names of the first `k` binders are the first `k` names, when none of them is a domain binder -/
theorem portNamesOf_take : ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (st : Sparkle.IR.Builder.CircuitState) (k : Nat),
    (∀ x ∈ L.take k, x.1.2 ≠ .domain) → portNamesOf (L.take k) st = (portNamesOf L st).take k
  | [], st, k, _ => by simp [portNamesOf]
  | binder :: rest, st, 0, _ => by simp [portNamesOf]
  | ((name, kind), id) :: rest, st, k + 1, h => by
    cases kind with
    | domain => exact absurd rfl (h ((name, .domain), id) (by simp))
    | bool =>
      have := portNamesOf_take rest (inputState st name.toString .bit) k (fun x hx => h x (by simp [hx]))
      simp [portNamesOf, this]
    | bits n =>
      have := portNamesOf_take rest (inputState st name.toString (.bitVector n)) k (fun x hx => h x (by simp [hx]))
      simp [portNamesOf, this]

theorem portNamesOf_length : ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (st : Sparkle.IR.Builder.CircuitState),
    (∀ x ∈ L, x.1.2 ≠ .domain) → (portNamesOf L st).length = L.length
  | [], st, _ => by simp [portNamesOf]
  | ((name, kind), id) :: rest, st, h => by
    cases kind with
    | domain => exact absurd rfl (h ((name, .domain), id) (by simp))
    | bool =>
      have := portNamesOf_length rest (inputState st name.toString .bit) (fun x hx => h x (by simp [hx]))
      simp [portNamesOf, this]
    | bits n =>
      have := portNamesOf_length rest (inputState st name.toString (.bitVector n)) (fun x hx => h x (by simp [hx]))
      simp [portNamesOf, this]

theorem zip_take_eq {α β : Type} : ∀ (bs : List α) (ids : List β) (k : Nat), (bs.take k).zip ids = (bs.zip ids).take k
  | [], ids, k => by simp
  | b :: bs, [], k => by cases k <;> simp
  | b :: bs, i :: ids, 0 => by simp
  | b :: bs, i :: ids, k + 1 => by simp [zip_take_eq bs ids k]

theorem not_allocated_rst : ¬ Sparkle.IR.NameHints.Allocated "rst" := by
  intro h
  have h2 := h.2
  have : "rst".toList.head? = some 'r' := by decide
  rw [this] at h2
  simp at h2

/-- the seed over the first `kD` ports: the value at a port name, `0` at `rst`, the state elsewhere -/
theorem seed_core (a0 : Setup) (LL : List ((Name × MixedGateBinder) × FVarId)) (kD : Nat)
    (hnd : (portNamesOf LL a0.state).Nodup) (hlen : (portNamesOf (LL.take kD) a0.state).length = (LL.take kD).length)
    (hal : ∀ x ∈ portNamesOf LL a0.state, Sparkle.IR.NameHints.Allocated x)
    (hn5 : portNamesOf (LL.take kD) a0.state = (portNamesOf LL a0.state).take kD)
    (regs : List String) (hreg : ∀ r ∈ regs, r ∈ (portNamesOf LL a0.state).drop kD)
    (val : Nat → ((Name × MixedGateBinder) × FVarId) → Nat) :
    ∃ seed : Nat → (String → Nat) → Env,
      (∀ (t : Nat) (st : String → Nat), ∀ p ∈ (portNamesOf (LL.take kD) a0.state).zip ((LL.take kD).map (val t)),
        seed t st p.1 = p.2) ∧
      (∀ (t : Nat) (st : String → Nat) (r : String), r ∈ regs → seed t st r = st r) ∧
      (∀ (t : Nat) (st : String → Nat), seed t st "rst" = 0) := by
  have hsplit : portNamesOf LL a0.state = (portNamesOf LL a0.state).take kD ++ (portNamesOf LL a0.state).drop kD :=
    (List.take_append_drop _ _).symm
  have hdisj := (List.nodup_append.mp (hsplit ▸ hnd)).2.2
  have hnd5 := (List.nodup_append.mp (hsplit ▸ hnd)).1
  refine ⟨fun t st n => if n = "rst" then 0 else
      lk ((portNamesOf (LL.take kD) a0.state).zip ((LL.take kD).map (val t))) n (st n), ?_, ?_, ?_⟩
  · intro t st p hp
    have hp1 : p.1 ∈ portNamesOf (LL.take kD) a0.state := (List.of_mem_zip hp).1
    have hne : p.1 ≠ "rst" := by
      intro h
      have := hal p.1 (List.mem_of_mem_take (hn5 ▸ hp1))
      rw [h] at this
      exact not_allocated_rst this
    have hfst : (((portNamesOf (LL.take kD) a0.state).zip ((LL.take kD).map (val t))).map Prod.fst) =
        portNamesOf (LL.take kD) a0.state := by
      apply List.map_fst_zip
      simp [hlen]
    have hnd' : ((((portNamesOf (LL.take kD) a0.state).zip ((LL.take kD).map (val t))).map Prod.fst)).Nodup := by
      rw [hfst, hn5]; exact hnd5
    simp only [hne, if_false]
    exact lk_mem _ hnd' p hp _
  · intro t st r hr
    have hr5 : r ∉ portNamesOf (LL.take kD) a0.state := by
      rw [hn5]; exact fun h => hdisj r h r (hreg r hr) rfl
    have hrne : r ≠ "rst" := by
      intro h
      have := hal r (List.mem_of_mem_drop (hreg r hr))
      rw [h] at this
      exact not_allocated_rst this
    have hfst : (((portNamesOf (LL.take kD) a0.state).zip ((LL.take kD).map (val t))).map Prod.fst) =
        portNamesOf (LL.take kD) a0.state := by
      apply List.map_fst_zip
      simp [hlen]
    simp only [hrne, if_false]
    exact lk_not_mem _ _ (by rw [hfst]; exact hr5) _
  · intro t st
    simp

theorem idxOf_getElem_nodup : ∀ (l : List String), l.Nodup → ∀ (k : Nat) (hk : k < l.length), l.idxOf l[k] = k
  | [], _, k, hk => by simp at hk
  | a :: rest, hnd, 0, _ => by simp
  | a :: rest, hnd, k + 1, hk => by
    rw [List.nodup_cons] at hnd
    have hk' : k < rest.length := by simpa using hk
    have ih := idxOf_getElem_nodup rest hnd.2 k hk'
    have hne : a ≠ rest[k] := fun h => hnd.1 (h ▸ List.getElem_mem hk')
    have hb : (a == rest[k]) = false := by simpa using hne
    simp [List.idxOf_cons, hb, ih]

/-- the initial state: register `k` holds the `k`-th initial value -/
theorem st0_exists (regs : List String) (hrn : regs.Nodup) (inits : List Nat) :
    ∃ st0 : String → Nat, ∀ (k : Nat) (r : String) (n : Nat), regs[k]? = some r → inits[k]? = some n → st0 r = n := by
  refine ⟨fun r => (inits[regs.idxOf r]?).getD 0, ?_⟩
  intro k r n hr hn
  have hk : k < regs.length := (List.getElem?_eq_some_iff.mp hr).1
  have hr' : regs[k] = r := (List.getElem?_eq_some_iff.mp hr).2
  have : regs.idxOf r = k := by
    rw [← hr']
    exact idxOf_getElem_nodup regs hrn k hk
  simp [this, hn]

/-- **the seed premises are simultaneously satisfiable.**  For every ids, cache, `regs`, `lets`, module and design that satisfy `MachineWired`'s naming facts (and `regs` distinct), every per-cycle source valuation `bv`/`wv` of the first `kD` input binders, and every run length `T`: there are `seed` and `st0` with `(a)` `SourceInputs` at every cycle `t < T` and every state, `(b)` a register reads the state, `(c)` reset is 0, `(d)` register `k`'s initial value is slot `k`'s init.  Hypotheses beyond `MachineWired`: the ids are one per binder; no binder is a domain binder; the first `kD` ports lie before the registers' range (`kD + lets + slots ≤ binders`). -/
theorem premises_satisfiable (S : Tools.ShippingFGCircuitS3tSpec.SourceData) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (regs lets : List String) (b : Sparkle.IR.AST.Module) (D : Design)
    (hW : MachineWired S.declName S.d.shape ids cache b D regs lets) (hrn : regs.Nodup)
    (hids : ids.length = S.d.shape.binders.length) (hkD : S.kD ≤ S.d.nIn)
    (hall : ∀ x ∈ S.d.shape.binders, x.2 ≠ .domain)
    (hpos : S.kD + S.d.shape.layout.lets + S.d.shape.layout.slots.length ≤ S.d.shape.binders.length)
    (bv : Nat → Nat → Bool) (wv : Nat → (j n : Nat) → BitVec n) (T : Nat) :
    ∃ (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ (t : Nat) (st : String → Nat), t < T →
        SourceInputs S.declName (S.d.bsIn.take S.kD) ids cache (bv t) (wv t) (seed t st)) ∧
      (∀ (t : Nat) (st : String → Nat) (r : String), r ∈ regs → seed t st r = st r) ∧
      (∀ (t : Nat) (st : String → Nat), seed t st "rst" = 0) ∧
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → S.d.shape.layout.slots[k]? = some f →
        st0 r = f.init) := by
  obtain ⟨hnd, hal, hreg, -⟩ := hW
  have hnames : (machPorts S.declName ids cache S.d.shape.binders).map (·.name) =
      portNamesOf (S.d.shape.binders.zip ids) (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl S.declName)).state :=
    inputPorts_names _ _ _ _
  rw [hnames] at hnd hal hreg
  have hLLdom : ∀ x ∈ S.d.shape.binders.zip ids, x.1.2 ≠ .domain := fun x hx => hall x.1 (List.of_mem_zip hx).1
  have hlen : (portNamesOf (S.d.shape.binders.zip ids) (Tools.ShippingMixedEntrySoundness.start
      (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl S.declName)).state).length =
      S.d.shape.binders.length := by
    rw [portNamesOf_length _ _ hLLdom, List.length_zip]; omega
  rw [hlen] at hreg
  have hreg' : ∀ r ∈ regs, r ∈ (portNamesOf (S.d.shape.binders.zip ids) (Tools.ShippingMixedEntrySoundness.start
      (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl S.declName)).state).drop S.kD := by
    intro r hr
    have h := hreg r hr
    have hm : S.kD ≤ S.d.shape.binders.length - S.d.shape.layout.lets - S.d.shape.layout.slots.length := by omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hm
    rw [hj, ← List.drop_drop] at h
    exact List.mem_of_mem_drop h
  have hbsIn : S.d.bsIn.take S.kD = S.d.shape.binders.take S.kD := by
    unfold MachineData.bsIn
    rw [List.take_take, Nat.min_eq_left hkD]
  have hL5 := zip_take_eq S.d.shape.binders ids S.kD
  have hdom5 : ∀ x ∈ (S.d.shape.binders.zip ids).take S.kD, x.1.2 ≠ .domain :=
    fun x hx => hLLdom x (List.mem_of_mem_take hx)
  have hn5 := portNamesOf_take (S.d.shape.binders.zip ids) (Tools.ShippingMixedEntrySoundness.start
      (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl S.declName)).state S.kD hdom5
  have hlen5 := portNamesOf_length ((S.d.shape.binders.zip ids).take S.kD) (Tools.ShippingMixedEntrySoundness.start
      (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl S.declName)).state hdom5
  obtain ⟨seed, hs1, hs2, hs3⟩ := seed_core (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
    (Sparkle.IR.ModuleName.ofDecl S.declName)) (S.d.shape.binders.zip ids) S.kD hnd hlen5 hal hn5 regs hreg'
    (fun t => valOf (boolValues ids (bv t)) (bitValues ids (wv t)))
  obtain ⟨st0, hst0⟩ := st0_exists regs hrn (S.d.shape.layout.slots.map (·.init))
  refine ⟨seed, st0, ?_, hs2, hs3, ?_⟩
  · intro t st _
    unfold SourceInputs
    rw [hbsIn, hL5]
    apply admissible_of_ports _ _ _ _ _ hdom5
    intro p hp
    exact hs1 t st p hp
  · intro k r f hr hf
    exact hst0 k r f.init hr (by simp [List.getElem?_map, hf])

open Tools.ShippingFGCircuitS3tSpec Tools.ShippingFGCircuitS1kRoot in
/-- the three numeric/structural side conditions, for the concrete root (kernel): `kD = 5 ≤ nIn = 7`, no binder is a domain binder, `5 + 45 lets + 17 slots ≤ 69 binders` -/
theorem rootS_hyps : rootS.kD ≤ rootS.d.nIn ∧ (∀ x ∈ rootS.d.shape.binders, x.2 ≠ .domain) ∧
    rootS.kD + rootS.d.shape.layout.lets + rootS.d.shape.layout.slots.length ≤ rootS.d.shape.binders.length := by
  decide +kernel

open Tools.ShippingFGCircuitS3tSpec in
/-- **simultaneous satisfaction for the concrete root**: for every ids/cache/regs/lets/module/design with `MachineWired`'s naming facts and every per-cycle input valuation, the four seed premises of `RootShowsAt` hold together for some `seed`, `st0`.  (The compiler's ids/cache/regs are not constructed here: the allocator's names are not kernel-evaluable, docs §69 gap G1; the satisfiability is for ALL witnesses with these facts.) -/
theorem rootS_premises (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs lets : List String)
    (b : Sparkle.IR.AST.Module) (D : Design)
    (hW : MachineWired rootS.declName rootS.d.shape ids cache b D regs lets) (hrn : regs.Nodup)
    (hids : ids.length = rootS.d.shape.binders.length)
    (bv : Nat → Nat → Bool) (wv : Nat → (j n : Nat) → BitVec n) (T : Nat) :
    ∃ (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ (t : Nat) (st : String → Nat), t < T →
        SourceInputs rootS.declName (rootS.d.bsIn.take rootS.kD) ids cache (bv t) (wv t) (seed t st)) ∧
      (∀ (t : Nat) (st : String → Nat) (r : String), r ∈ regs → seed t st r = st r) ∧
      (∀ (t : Nat) (st : String → Nat), seed t st "rst" = 0) ∧
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → rootS.d.shape.layout.slots[k]? = some f →
        st0 r = f.init) :=
  premises_satisfiable rootS ids cache regs lets b D hW hrn hids rootS_hyps.1 rootS_hyps.2.1 rootS_hyps.2.2 bv wv T

end Tools.ShippingFGCircuitS3tSat
