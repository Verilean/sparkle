import Tools.ShippingNoPortsTypedI
import Tools.ShippingPortWidthsPure
import Tools.ShippingTransitionPortTys
-- Round par/sat. BUILT: sa1 (ComposedGW, NoPortsTypedBW exit ok; SatInputs failed: 7 tactic/term errors, fixed by the worker), sa2 (all, exit 0, 669 jobs).

/-! # Pure facts for satisfying the head's run hypotheses (round par/sat)

No run. Everything here is about lists, the binder walk (`inputPorts` / `machPorts`) and the
wiring clause of `MachineWired`.

## The source stream as an environment (task (c))

The port a binder gets is `inputWire a.state name ty`; the allocator state `a.state` moves by
`inputState`, which reads the binder's NAME and KIND only (`extend_state`, `inputPorts_congr`).
So the port names depend on the declaration name and the binder list, NOT on the fresh ids or on
the wire cache. The VALUES of `SourceInputs declName bs ids cache bools bits` are
`boolValues ids bools`, `bitValues ids bits` — the binder's position in `ids`.

* `portVals bools bits L a`: the walk's ports, each paired with the value `Admissible` asks there;
  `portVals_fst`: its ports are `inputPorts bools bits L a`.
* `admissible_of_portVals`: an environment carrying every pair's value at its port name is
  admissible.
* `envOf l`: the environment of a pair list (first match; `0` off the names);
  `envOf_mem` (distinct names), `envOf_cases`, `envOf_none`, `envOf_lt`.
* `streamEnv declName bs ids cache bools bits`: `envOf` of the pairs of `SourceInputs`' walk.
  `sourceInputs_of_env`: every environment agreeing with it on the ports of
  `machPorts declName ids cache bs` (distinct names) satisfies `SourceInputs`.

## The wiring (task (d), the parts not about widths)

From `MachineWired`'s port-name clauses (`wired_parts`):

* `regs_not_input`: no register is an input (registers lie in the DROP part of the port names, the
  inputs in the TAKE part — distinct names — or are `clk` / `rst`, which are not allocated);
* `clk_input`: with a slot, `clk` is an input;
* `port_input`: a port of the first `kD` binders is an input (it lies in the take part and is not
  a call port: the call ports sit at positions `machNIn + k`, after it);
* `input_mem_ports`: an input other than `clk` / `rst` is a port of the walk;
* `lengths`: the counting, under the data conditions `hlen`, `hdom`.

## Widths

* `declWidth_of_wire`: a port that is a wire of `b` (distinct wire names) has its type's width;
* `weS_input`: in the shipped module's emitted width map, an input that is also a wire of `b`, the
  only input of its name, has its type's width (via `checkedOptimize_ports_wires`). -/
namespace Tools.ShippingSatInputs
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedInputSoundness
open Tools.ShippingMachineEntry Tools.ShippingMixedSourceBridge
open Tools.ShippingMuxLoweringSoundness (encodeBool encodeBool_lt)
open Sparkle.IR.NameHints (Allocated)

/-! ## The walk's ports with their values -/

/-- The ports of the binder walk, each with the value `Admissible` asks at it. Same recursion as
`inputPorts`. -/
def portVals (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    List ((Name × MixedGateBinder) × FVarId) → Setup → List (Port × Nat)
  | [], _ => []
  | ((name, .domain), id) :: rest, a =>
    portVals bools bits rest (extend a ((name, .domain), id) bools bits)
  | ((name, .bool), id) :: rest, a =>
    ({ name := inputWire a.state name.toString .bit, ty := .bit }, encodeBool (bools id)) ::
      portVals bools bits rest (extend a ((name, .bool), id) bools bits)
  | ((name, .bits n), id) :: rest, a =>
    ({ name := inputWire a.state name.toString (.bitVector n), ty := .bitVector n },
        (bits id n).toNat) ::
      portVals bools bits rest (extend a ((name, .bits n), id) bools bits)

theorem portVals_fst {bools : FVarId → Bool} {bits : (id : FVarId) → (n : Nat) → BitVec n} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      (portVals bools bits L a).map (·.1) = inputPorts bools bits L a
  | [], _ => rfl
  | ((name, .domain), id) :: rest, a => by
    simp only [portVals, inputPorts]
    exact portVals_fst rest _
  | ((name, .bool), id) :: rest, a => by
    simp only [portVals, inputPorts, List.map_cons]
    rw [portVals_fst rest _]
  | ((name, .bits n), id) :: rest, a => by
    simp only [portVals, inputPorts, List.map_cons]
    rw [portVals_fst rest _]

theorem admissible_of_portVals {bools : FVarId → Bool}
    {bits : (id : FVarId) → (n : Nat) → BitVec n} {env : Sparkle.IR.Semantics.Env} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      (∀ q ∈ portVals bools bits L a, env q.1.name = q.2) → Admissible bools bits env L a
  | [], _, _ => trivial
  | ((name, .domain), id) :: rest, a, h =>
    ⟨trivial, admissible_of_portVals rest _ (fun q hq => h q (by simp only [portVals]; exact hq))⟩
  | ((name, .bool), id) :: rest, a, h =>
    -- (sa1: the pair is given explicitly and `InputValue` unfolded first)
    ⟨by
      simp only [InputValue]
      exact h ({ name := inputWire a.state name.toString .bit, ty := .bit }, encodeBool (bools id))
        (by simp only [portVals]; exact List.mem_cons_self),
      admissible_of_portVals rest _
        (fun q hq => h q (by simp only [portVals]; exact List.mem_cons_of_mem _ hq))⟩
  | ((name, .bits n), id) :: rest, a, h =>
    ⟨by
      simp only [InputValue]
      exact h ({ name := inputWire a.state name.toString (.bitVector n), ty := .bitVector n },
          (bits id n).toNat)
        (by simp only [portVals]; exact List.mem_cons_self),
      admissible_of_portVals rest _
        (fun q hq => h q (by simp only [portVals]; exact List.mem_cons_of_mem _ hq))⟩

/-- A pair's value fits its port's type. -/
theorem portVals_lt {bools : FVarId → Bool} {bits : (id : FVarId) → (n : Nat) → BitVec n} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      ∀ q ∈ portVals bools bits L a, q.2 < 2 ^ q.1.ty.bitWidth
  | [], _, q, hq => by cases hq
  | ((name, .domain), id) :: rest, a, q, hq => by
    simp only [portVals] at hq
    exact portVals_lt rest _ q hq
  | ((name, .bool), id) :: rest, a, q, hq => by
    simp only [portVals, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact encodeBool_lt _
    · exact portVals_lt rest _ q hq
  | ((name, .bits n), id) :: rest, a, q, hq => by
    simp only [portVals, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact (bits id n).isLt
    · exact portVals_lt rest _ q hq

/-- The walk's ports are one bit or bit vectors. -/
theorem inputPorts_ty {bools : FVarId → Bool} {bits : (id : FVarId) → (n : Nat) → BitVec n} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      ∀ p ∈ inputPorts bools bits L a, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n
  | [], _, p, hp => by cases hp
  | ((name, .domain), id) :: rest, a, p, hp => by
    simp only [inputPorts] at hp
    exact inputPorts_ty rest _ p hp
  | ((name, .bool), id) :: rest, a, p, hp => by
    simp only [inputPorts, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inl rfl
    · exact inputPorts_ty rest _ p hp
  | ((name, .bits n), id) :: rest, a, p, hp => by
    simp only [inputPorts, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inr ⟨n, rfl⟩
    · exact inputPorts_ty rest _ p hp

/-! ## The environment of a pair list -/

/-- The value of the first pair of name `x`, `0` off the names. -/
def envOf (l : List (Port × Nat)) : Sparkle.IR.Semantics.Env := fun x =>
  ((l.find? (fun q => q.1.name == x)).map (·.2)).getD 0

theorem envOf_cases (l : List (Port × Nat)) (x : String) :
    envOf l x = 0 ∨ ∃ q ∈ l, q.1.name = x ∧ envOf l x = q.2 := by
  simp only [envOf]
  cases h : l.find? (fun q => q.1.name == x) with
  | none => exact Or.inl rfl
  | some q =>
    refine Or.inr ⟨q, List.mem_of_find?_eq_some h, ?_, rfl⟩
    have := List.find?_some h
    simpa using this

theorem envOf_none {l : List (Port × Nat)} {x : String} (h : ∀ q ∈ l, q.1.name ≠ x) :
    envOf l x = 0 := by
  rcases envOf_cases l x with h0 | ⟨q, hq, hn, -⟩
  · exact h0
  · exact absurd hn (h q hq)

theorem find_name {l : List (Port × Nat)} (hnd : (l.map (·.1.name)).Nodup) {q : Port × Nat}
    (hq : q ∈ l) : l.find? (fun r => r.1.name == q.1.name) = some q := by
  induction l with
  | nil => cases hq
  | cons a rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hq with rfl | hq'
    · simp
    · have hne : a.1.name ≠ q.1.name := fun e =>
        hnd.1 (e ▸ List.mem_map.mpr ⟨q, hq', rfl⟩)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hnd.2 hq'

theorem envOf_mem {l : List (Port × Nat)} (hnd : (l.map (·.1.name)).Nodup) {q : Port × Nat}
    (hq : q ∈ l) : envOf l q.1.name = q.2 := by
  simp only [envOf, find_name hnd hq]
  rfl

/-- **The environment's values fit `W`** where `W` is the pairs' type width (or the type has
width `0`, where the value is `0`). -/
theorem envOf_lt {l : List (Port × Nat)} (hlt : ∀ q ∈ l, q.2 < 2 ^ q.1.ty.bitWidth)
    (W : String → Nat) (hW : ∀ q ∈ l, q.1.ty.bitWidth ≠ 0 → W q.1.name = q.1.ty.bitWidth) :
    ∀ x, envOf l x < 2 ^ W x := by
  intro x
  rcases envOf_cases l x with h0 | ⟨q, hq, hn, he⟩
  · rw [h0]; exact Nat.two_pow_pos _
  · rw [he]
    by_cases hz : q.1.ty.bitWidth = 0
    · have h1 := hlt q hq
      rw [hz, Nat.pow_zero] at h1
      rw [show q.2 = 0 by omega]
      exact Nat.two_pow_pos _
    · rw [← hn, hW q hq hz]
      exact hlt q hq

/-! ## The source stream's environment -/

/-- **The source stream at one cycle, as an environment**: the pairs of `SourceInputs`' walk. -/
def streamEnv (declName : Name) (bs : List (Name × MixedGateBinder)) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (bools : Nat → Bool)
    (bits : (j : Nat) → (n : Nat) → BitVec n) : Sparkle.IR.Semantics.Env :=
  envOf (portVals (boolValues ids bools) (bitValues ids bits) (bs.zip ids)
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)))

/-- The pairs' ports are `machPorts`. -/
theorem streamPorts (declName : Name) (bs : List (Name × MixedGateBinder)) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (bools : Nat → Bool)
    (bits : (j : Nat) → (n : Nat) → BitVec n) :
    (portVals (boolValues ids bools) (bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))).map (·.1) =
      machPorts declName ids cache bs := by
  rw [portVals_fst]
  unfold machPorts
  exact inputPorts_congr _ _ _ rfl

/-- **`SourceInputs` from the stream's environment** (task (c)): every environment that agrees
with `streamEnv` on the ports of the walk satisfies `SourceInputs`, when the ports' names are
distinct. -/
theorem sourceInputs_of_env {declName : Name} {bs : List (Name × MixedGateBinder)}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {bools : Nat → Bool}
    {bits : (j : Nat) → (n : Nat) → BitVec n} {env : Sparkle.IR.Semantics.Env}
    (hnd : ((machPorts declName ids cache bs).map (·.name)).Nodup)
    (hag : ∀ p ∈ machPorts declName ids cache bs,
      env p.name = streamEnv declName bs ids cache bools bits p.name) :
    SourceInputs declName bs ids cache bools bits env := by
  unfold SourceInputs
  have hP := streamPorts declName bs ids cache bools bits
  have hnd' : ((portVals (boolValues ids bools) (bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))).map
        (·.1.name)).Nodup := by
    -- (sa1) the names of the pairs are the names of their ports
    have e : (portVals (boolValues ids bools) (bitValues ids bits) (bs.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))).map
          (·.1.name) = (machPorts declName ids cache bs).map (·.name) := by
      rw [← hP, List.map_map]
      rfl
    rw [e]
    exact hnd
  apply admissible_of_portVals
  intro q hq
  have hq1 : q.1 ∈ machPorts declName ids cache bs := by
    rw [← hP]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [hag q.1 hq1]
  exact envOf_mem hnd' hq

/-- Off the walk's port names, the stream's environment is `0`. -/
theorem streamEnv_off {declName : Name} {bs : List (Name × MixedGateBinder)}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {bools : Nat → Bool}
    {bits : (j : Nat) → (n : Nat) → BitVec n} {x : String}
    (hx : ∀ p ∈ machPorts declName ids cache bs, p.name ≠ x) :
    streamEnv declName bs ids cache bools bits x = 0 := by
  unfold streamEnv
  refine envOf_none (fun q hq => hx q.1 ?_)
  rw [← streamPorts declName bs ids cache bools bits]
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- The stream's values fit `W`, where `W` gives each port of positive width its type's width. -/
theorem streamEnv_lt {declName : Name} {bs : List (Name × MixedGateBinder)}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} {bools : Nat → Bool}
    {bits : (j : Nat) → (n : Nat) → BitVec n} (W : String → Nat)
    (hW : ∀ p ∈ machPorts declName ids cache bs, p.ty.bitWidth ≠ 0 → W p.name = p.ty.bitWidth) :
    ∀ x, streamEnv declName bs ids cache bools bits x < 2 ^ W x := by
  unfold streamEnv
  refine envOf_lt (portVals_lt _ _) W (fun q hq hz => hW q.1 ?_ hz)
  rw [← streamPorts declName bs ids cache bools bits]
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

theorem machPorts_ty {declName : Name} {bs : List (Name × MixedGateBinder)}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)} :
    ∀ p ∈ machPorts declName ids cache bs, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n := by
  unfold machPorts
  exact inputPorts_ty _ _

/-! ## Prefixes of the walk -/

theorem zip_take_left {α β : Type} : ∀ (l : List α) (r : List β) (k : Nat),
    (l.take k).zip r = (l.zip r).take k
  | [], r, k => by simp
  | a :: l, [], k => by cases k <;> simp
  | a :: l, b :: r, 0 => by simp
  | a :: l, b :: r, k + 1 => by
    simp only [List.take_succ_cons, List.zip_cons_cons]
    rw [zip_take_left l r k]

theorem inputPorts_take_prefix {bools : FVarId → Bool}
    {bits : (id : FVarId) → (n : Nat) → BitVec n} :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (k : Nat) (a : Setup),
      ∃ R, inputPorts bools bits L a = inputPorts bools bits (L.take k) a ++ R
  | [], k, a => ⟨[], by simp [inputPorts]⟩
  | b :: rest, 0, a => ⟨inputPorts bools bits (b :: rest) a, by rw [List.take_zero]; rfl⟩
  | ((name, .domain), id) :: rest, k + 1, a => by
    obtain ⟨R, hR⟩ := inputPorts_take_prefix rest k (extend a ((name, .domain), id) bools bits)
    exact ⟨R, by simp only [List.take_succ_cons, inputPorts]; exact hR⟩
  | ((name, .bool), id) :: rest, k + 1, a => by
    obtain ⟨R, hR⟩ := inputPorts_take_prefix rest k (extend a ((name, .bool), id) bools bits)
    exact ⟨R, by simp only [List.take_succ_cons, inputPorts, List.cons_append]; rw [hR]⟩
  | ((name, .bits n), id) :: rest, k + 1, a => by
    obtain ⟨R, hR⟩ := inputPorts_take_prefix rest k (extend a ((name, .bits n), id) bools bits)
    exact ⟨R, by simp only [List.take_succ_cons, inputPorts, List.cons_append]; rw [hR]⟩

/-- The ports of the first `k` binders are a prefix of the ports of all of them. -/
theorem machPorts_take_prefix (declName : Name) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (bs : List (Name × MixedGateBinder)) (k : Nat) :
    ∃ R, machPorts declName ids cache bs = machPorts declName ids cache (bs.take k) ++ R := by
  unfold machPorts
  rw [zip_take_left]
  exact inputPorts_take_prefix _ _ _

/-! ## The wiring clause -/

theorem not_clk_of_alloc {x : String} (h : Allocated x) : x ≠ "clk" :=
  fun e => Tools.ShippingMachineCleanup.not_allocated_clk (e ▸ h)

theorem not_rst_of_alloc {x : String} (h : Allocated x) : x ≠ "rst" :=
  fun e => Tools.ShippingRegisterSoundness.not_allocated_rst (e ▸ h)

/-- The parts of `MachineWired` read here. -/
theorem wired_parts {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (h : MachineWired declName shape ids cache m dsn regs lets) :
    ((machPorts declName ids cache shape.binders).map (·.name)).Nodup ∧
    (∀ x ∈ (machPorts declName ids cache shape.binders).map (·.name), Allocated x) ∧
    (∀ r ∈ regs, r ∈ ((machPorts declName ids cache shape.binders).map (·.name)).drop
      (((machPorts declName ids cache shape.binders).map (·.name)).length - shape.layout.lets -
        shape.layout.slots.length)) ∧
    ∃ (outWs : List String) (extra : List Port),
      (∀ w ∈ outWs, ∃ k, k < shape.insts.length ∧
        ((machPorts declName ids cache shape.binders).map (·.name))[machNIn shape + k]? = some w) ∧
      (extra = [] ∨ (extra = [({ name := "clk", ty := .bit } : Port), { name := "rst", ty := .bit }] ∧
        shape.layout.slots = [])) ∧
      m.inputs =
        ((machPorts declName ids cache shape.binders).take
            (((machPorts declName ids cache shape.binders).map (·.name)).length -
              shape.layout.lets - shape.layout.slots.length) ++
          (if shape.layout.slots.isEmpty then [] else
            [({ name := "clk", ty := .bit } : Port), { name := "rst", ty := .bit }]) ++ extra).filter
          fun p => !outWs.contains p.name := by
  -- (writing-time guess, accepted by build sa1/sa2: the 18 conjuncts of `MachineWired`, as `wireNames_runMT` destructures
  -- them; the `let names := …` of the definition zeta-reduced by `obtain`)
  obtain ⟨hnd, hal, hregs, -, -, -, -, -, -, -, -, -, -, -, -, -, hinM, -⟩ := h
  obtain ⟨outWs, extra, hw, -, hx, hi⟩ := hinM
  exact ⟨hnd, hal, hregs, outWs, extra, hw, hx, hi⟩

theorem clkrst_of_mem_if {s : Bool} {p : Port}
    (h : p ∈ (if s then [] else
      [({ name := "clk", ty := .bit } : Port), { name := "rst", ty := .bit }])) :
    p.name = "clk" ∨ p.name = "rst" := by
  split at h
  · cases h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem clkrst_of_extra {extra : List Port} {c : Prop}
    (hx : extra = [] ∨ (extra = [({ name := "clk", ty := .bit } : Port), { name := "rst", ty := .bit }] ∧ c)) :
    ∀ p ∈ extra, p.name = "clk" ∨ p.name = "rst" := by
  intro p hp
  rcases hx with he | ⟨he, -⟩
  · rw [he] at hp; cases hp
  · rw [he] at hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **No register is an input.** -/
theorem regs_not_input {P : List Port} {K : Nat} {regs : List String} {outWs : List String}
    {extra : List Port} {s : Bool} {I : List Port}
    (hnd : (P.map (·.name)).Nodup) (hal : ∀ x ∈ P.map (·.name), Allocated x)
    (hregs : ∀ r ∈ regs, r ∈ (P.map (·.name)).drop K)
    (hext : ∀ p ∈ extra, p.name = "clk" ∨ p.name = "rst")
    (hi : I = (P.take K ++ (if s then [] else
      [({ name := "clk", ty := .bit } : Port), { name := "rst", ty := .bit }]) ++ extra).filter
        fun p => !outWs.contains p.name) :
    ∀ r ∈ regs, r ∉ I.map (·.name) := by
  intro r hr hin
  obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hin
  rw [hi] at hp
  have hp' := (List.mem_filter.mp hp).1
  have hrN := hregs r hr
  have hrA : Allocated r := hal r (List.mem_of_mem_drop hrN)
  have hcr : ∀ x : String, x = "clk" ∨ x = "rst" → x = r → False := by
    intro x hx e
    rcases hx with h | h
    · exact not_clk_of_alloc hrA (e.symm.trans h)
    · exact not_rst_of_alloc hrA (e.symm.trans h)
  rcases List.mem_append.mp hp' with h1 | h3
  · rcases List.mem_append.mp h1 with h1 | h2
    · have hpn' : p.name ∈ (P.map (·.name)).take K := by
        rw [← List.map_take]
        exact List.mem_map.mpr ⟨p, h1, rfl⟩
      have hnd' := hnd
      rw [← List.take_append_drop K (P.map (·.name))] at hnd'
      exact (List.nodup_append.mp hnd').2.2 _ hpn' _ hrN hpn
    · exact hcr _ (clkrst_of_mem_if h2) hpn
  · exact hcr _ (hext p h3) hpn

/-- **With a slot, `clk` is an input** (it is not a call port: those are allocated names). -/
theorem clk_input {P : List Port} {K : Nat} {outWs : List String} {extra : List Port}
    {s : Bool} {I : List Port}
    (hal : ∀ x ∈ P.map (·.name), Allocated x) (hw : ∀ w ∈ outWs, w ∈ P.map (·.name))
    (hs : s = false)
    (hi : I = (P.take K ++ (if s then [] else
      [({ name := "clk", ty := .bit } : Port), { name := "rst", ty := .bit }]) ++ extra).filter
        fun p => !outWs.contains p.name) :
    "clk" ∈ I.map (·.name) := by
  rw [hi]
  have hc : outWs.contains "clk" = false :=
    Bool.eq_false_iff.mpr (fun hc =>
      Tools.ShippingMachineCleanup.not_allocated_clk (hal _ (hw _ (List.contains_iff_mem.mp hc))))
  refine List.mem_map.mpr ⟨({ name := "clk", ty := .bit } : Port), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · subst hs
    exact List.mem_append_left _ (List.mem_append_right _ (by simp))
  · -- (sa1) `simp` turns both `hc` and the goal into `"clk" ∉ outWs`
    simpa using hc

/-- An index of a list with distinct elements is its element's. -/
theorem nodup_getElem?_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} {x : α}
    (hi : l[i]? = some x) (hj : l[j]? = some x) : i = j := by
  have hi' : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  exact (List.getElem?_inj hi' h).mp (hi.trans hj.symm)

/-- **A port of the first binders is an input**: it lies in the take part and is not a call port
(the call ports sit at the positions `nIn + k`, at or after the prefix's length). -/
theorem port_input {P PL R : List Port} {K nIn kI : Nat} {outWs : List String}
    {extra : List Port} {s : Bool} {I : List Port}
    (hP : P = PL ++ R) (hcK : PL.length ≤ K) (hcN : PL.length ≤ nIn)
    (hw : ∀ w ∈ outWs, ∃ k, k < kI ∧ (P.map (·.name))[nIn + k]? = some w)
    (hnd : (P.map (·.name)).Nodup)
    (hi : I = (P.take K ++ (if s then [] else
      [({ name := "clk", ty := .bit } : Port), { name := "rst", ty := .bit }]) ++ extra).filter
        fun p => !outWs.contains p.name)
    {p : Port} (hp : p ∈ PL) : p ∈ I := by
  obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp
  have hPj : P[j]? = some p := by
    rw [hP, List.getElem?_append_left hj, List.getElem?_eq_getElem hj, hpj]
  have hmem : p ∈ P.take K :=
    List.mem_of_getElem? (show (P.take K)[j]? = some p by
      rw [List.getElem?_take_of_lt (by omega)]; exact hPj)
  have hc : outWs.contains p.name = false := Bool.eq_false_iff.mpr fun hc => by
    obtain ⟨k, -, hk⟩ := hw _ (List.contains_iff_mem.mp hc)
    have hNj : (P.map (·.name))[j]? = some p.name := by
      rw [List.getElem?_map, hPj]; rfl
    have := nodup_getElem?_inj hnd hNj hk
    omega
  rw [hi]
  refine List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hmem), ?_⟩
  -- (sa1) `simp` turns both `hc` and the goal into `p.name ∉ outWs`
  simpa using hc

/-- **An input other than `clk` / `rst` is a port of the walk.** -/
theorem input_mem_ports {P : List Port} {K : Nat} {outWs : List String} {extra : List Port}
    {s : Bool} {I : List Port}
    (hext : ∀ p ∈ extra, p.name = "clk" ∨ p.name = "rst")
    (hi : I = (P.take K ++ (if s then [] else
      [({ name := "clk", ty := .bit } : Port), { name := "rst", ty := .bit }]) ++ extra).filter
        fun p => !outWs.contains p.name)
    {q : Port} (hq : q ∈ I) (h1 : q.name ≠ "clk") (h2 : q.name ≠ "rst") : q ∈ P := by
  rw [hi] at hq
  have hq' := (List.mem_filter.mp hq).1
  rcases List.mem_append.mp hq' with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_of_mem_take h
    · rcases clkrst_of_mem_if h with e | e
      · exact absurd e h1
      · exact absurd e h2
  · rcases hext q h with e | e
    · exact absurd e h1
    · exact absurd e h2

/-- **The counting**, under the data conditions: the binders from `kD` on are the calls', the
slots' and the `let`s', none a domain. -/
theorem lengths (declName : Name) (ids : List FVarId) (cache : IO.Ref (ExprStructMap String))
    (shape : MachineShape) (kD : Nat) (hids : shape.binders.length ≤ ids.length)
    (hlen : kD + shape.insts.length + shape.layout.slots.length + shape.layout.lets =
      shape.binders.length)
    (hdom : ∀ b ∈ shape.binders.drop kD, b.2 ≠ .domain) :
    (machPorts declName ids cache shape.binders).length =
      (machPorts declName ids cache (shape.binders.take kD)).length + shape.insts.length +
        shape.layout.slots.length + shape.layout.lets ∧
    machNIn shape = (machPorts declName ids cache (shape.binders.take kD)).length := by
  have hl : ∀ bs : List (Name × MixedGateBinder), bs.length ≤ ids.length →
      (machPorts declName ids cache bs).length =
        (bs.filter Tools.ShippingPortWidthsPure.nonDom).length := by
    intro bs h
    have := congrArg List.length (Tools.ShippingPortWidthsPure.machPorts_tys declName ids cache bs h)
    simpa using this
  have hk : (shape.binders.take kD).length ≤ ids.length :=
    Nat.le_trans (List.length_take_le' _ _) hids
  have hsplit : (shape.binders.filter Tools.ShippingPortWidthsPure.nonDom).length =
      ((shape.binders.take kD).filter Tools.ShippingPortWidthsPure.nonDom).length +
        (shape.binders.drop kD).length := by
    -- (sa1: no `conv_lhs` in core) the drop part passes the filter whole
    have h2 : (shape.binders.drop kD).filter Tools.ShippingPortWidthsPure.nonDom =
        shape.binders.drop kD :=
      List.filter_eq_self.mpr (fun b hb => by
        -- (writing-time guess, accepted by build sa1/sa2: `nonDom b = (b.2 != .domain)` closes by `simpa`)
        simpa [Tools.ShippingPortWidthsPure.nonDom] using hdom b hb)
    rw [← h2, ← List.length_append, ← List.filter_append, List.take_append_drop]
  have hdl : (shape.binders.drop kD).length =
      shape.insts.length + shape.layout.slots.length + shape.layout.lets := by
    rw [List.length_drop]; omega
  refine ⟨by rw [hl _ hids, hl _ hk, hsplit, hdl]; omega, ?_⟩
  unfold machNIn
  rw [hl _ hk, show shape.binders.length - shape.insts.length - shape.layout.slots.length -
    shape.layout.lets = kD by omega]
  -- (writing-time guess, accepted by build sa1/sa2: `fun b => b.2 != .domain` and `nonDom` are the same function by `rfl`)
  rfl

/-! ## Widths -/

/-- A wire of `b` (distinct wire names) of type `bit` / `bitVector` has its type's declared
width. -/
theorem declWidth_of_wire {b : Module} {p : Port} (hnd : (b.wires.map (·.name)).Nodup)
    (hp : p ∈ b.wires) (hty : p.ty = .bit ∨ ∃ n, p.ty = .bitVector n) :
    Sparkle.IR.RegDedup.declWidth b p.name = p.ty.bitWidth := by
  have hfd := Tools.ShippingEntrySoundness.find?_of_nodup hnd hp
  simp only [Sparkle.IR.RegDedup.declWidth, hfd]
  obtain ⟨pn, pty⟩ := p
  rcases hty with h | ⟨n, h⟩
  · simp only at h; subst h; rfl
  · simp only at h; subst h; rfl

/-- **An input of `b` that is also a wire of `b`, the only input of its name, has its type's
width in the shipped module's emitted width map.** -/
theorem weS_input {b : Module} {p : Port}
    (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hs : ∀ q ∈ b.wires ++ b.inputs ++ b.outputs,
      Sparkle.Backend.Verilog.sanitizeName q.name = q.name)
    (hoi : ∀ q ∈ b.outputs, ∀ r ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName r.name ≠ q.name)
    (hp : p ∈ b.inputs) (hpw : p ∈ b.wires)
    (huniq : ∀ q ∈ b.inputs, q.name = p.name → q = p)
    (hty : p.ty = .bit ∨ ∃ n, p.ty = .bitVector n) :
    Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) p.name = p.ty.bitWidth := by
  obtain ⟨hi, ho, hsub⟩ := Tools.ShippingNoPortsTypedI.checkedOptimize_ports_wires hgate
  have hsp : Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
    hs p (List.mem_append_left _ (List.mem_append_right _ hp))
  simp only [Tools.ShippingDesignSV.weS, Tools.ShippingDesignSV.wofOf, Tools.SVParser.EmitSem.weOf,
    Tools.SVParser.RoundtripProof.moduleWof]
  cases hf : ((Sparkle.IR.OptCheck.checkedOptimize b).wires ++
      (Sparkle.IR.OptCheck.checkedOptimize b).inputs ++
      (Sparkle.IR.OptCheck.checkedOptimize b).outputs).find?
      (fun q => Sparkle.Backend.Verilog.sanitizeName q.name == p.name) with
  | none =>
    exfalso
    have hmem : p ∈ (Sparkle.IR.OptCheck.checkedOptimize b).wires ++
        (Sparkle.IR.OptCheck.checkedOptimize b).inputs ++
        (Sparkle.IR.OptCheck.checkedOptimize b).outputs := by
      rw [hi]; exact List.mem_append_left _ (List.mem_append_right _ hp)
    have := List.find?_eq_none.mp hf p hmem
    simp [hsp] at this
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have hqx : Sparkle.Backend.Verilog.sanitizeName q.name = p.name := by
      have := List.find?_some hf
      simpa using this
    have hqp : q = p := by
      rw [hi, ho] at hq
      rcases List.mem_append.mp hq with hq' | hqo
      · rcases List.mem_append.mp hq' with hqw | hqi
        · have hqb := hsub q hqw
          have hst := hs q (List.mem_append_left _ (List.mem_append_left _ hqb))
          exact Tools.ShippingTransitionPortTys.port_of_name hnd hqb hpw (hst.symm.trans hqx)
        · have hst := hs q (List.mem_append_left _ (List.mem_append_right _ hqi))
          exact huniq q hqi (hst.symm.trans hqx)
      · exfalso
        have hst := hs q (List.mem_append_right _ hqo)
        exact hoi q hqo p hp (by rw [hsp, ← hqx, hst])
    subst hqp
    -- (writing-time guess, accepted by build sa1/sa2: the `bind`/`match`/`getD` reduce by `simp` once the type is a
    -- constructor, as in `weS_le_of_sub`)
    obtain ⟨qn, qty⟩ := q
    rcases hty with h | ⟨n, h⟩
    · simp only at h; subst h; simp [Sparkle.IR.Type.HWType.bitWidth]
    · simp only at h; subst h; simp [Sparkle.IR.Type.HWType.bitWidth]

/-! ## The seeding -/

theorem seedIn_in {b : Module} {ins : Nat → String → Nat} {t : Nat} {st : String → Nat}
    {x : String} (h : x ∈ b.inputs.map (·.name)) :
    Tools.ShippingSeqOptSoundness.seedIn b ins t st x = ins t x := by
  simp only [Tools.ShippingSeqOptSoundness.seedIn, List.contains_eq_mem, decide_eq_true h, if_true]

theorem seedIn_out {b : Module} {ins : Nat → String → Nat} {t : Nat} {st : String → Nat}
    {x : String} (h : x ∉ b.inputs.map (·.name)) :
    Tools.ShippingSeqOptSoundness.seedIn b ins t st x = st x := by
  unfold Tools.ShippingSeqOptSoundness.seedIn
  split
  · rename_i hc
    exact absurd (by simpa [List.contains_eq_mem] using hc) h
  · rfl

end Tools.ShippingSatInputs
