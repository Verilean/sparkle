import Tools.ShippingGuardsLeaf

/-! # A leaf register machine AS AN ENTRY, at the design level (round par/b-27)

`f.machine_ships_leafC` (`#machine_leaf_entry`,
`Tools/ShippingLeafEntryCommand.lean`) ends in `MachineShips` at the
emitter's own width map: ONE module. The parents' endpoints
(`f.machine_design_noPortsR0_closed`, `…NR{n}_closed`,
`machine_design_svH_full_closed`) end in `DesignSV (childMap D.modules) n
(checkedOptimize b) …`: the closed run of the design's emitted texts. This
file is the GENERAL BRIDGE between the two for an entry WITHOUT calls, and
the statement of its design-level endpoint in the parents' shape.

## The route, and why not the parents' head

The parents' head (`Tools.ShippingNoPorts.machine_design_noPorts`,
`Tools.ShippingOneOutHead.machine_design_svH_free`) CANNOT be instantiated
at "no children". It is not a matter of vacuous clauses:

* its hypothesis `hFacts` asks `Tools.ShippingGuardsSound.RunFacts
  (childMap D.modules) b`, whose first field is `gate : hierGate b = true`,
  and `hierGate m = m.body.any isInst && …` (`Sparkle/IR/RefineCheck.lean`
  196–200) is FALSE on a body without an instance;
* its proof goes through `machine_ships_hierC_at_free`: the branch of
  `checkedOptimize` for instance-bearing modules (`hierBinds` /
  `hierRefineCheck` / the `hierGate` fallback). An instance-free
  assign + register module takes ANOTHER branch (`refineCheck m o &&
  printOk o`, `RefineCheck.lean` 391–392);
* the data theorems its generators feed it ask `d.shape.insts ≠ []` and
  `d.shape.instFields ≠ []` (`hins`, `hfne` of
  `core_portsMatch_raw_leaf`), and `composed` asks `ComposedG`, the
  composition with the children.

So the route is `MachineShips` (`leaf_entry_ships_closed` — the branch a leaf
takes) + `Tools.ShippingLeafEntry.designSV0_of_leaf`.

## The precise relation between `MachineShips` and `DesignSV` for a leaf

`MachineShips f d raw b o (wofOf o) dom src` gives, for the use conditions,
ONE list of environments `envsO` with: (a) `runModule (declWidth o) o.body
(seedIn raw ins) T st0 mems = some envsO` (the IR run of the shipped
module); (b) the run of its emitted text — literally
`TextRun o (seedIn raw ins) T st0 mems envsO` (`TextRun` unfolded at
`wofOf o`); (c) `envsO.length = T`; (d) the source on the output ports.

`DesignSV C 0 o seed T ⟨st0, mems, kids⟩ envs` of a module without
instances is `TextRun o seed T st0 mems envs` and three vacuous clauses, in
BOTH directions, for every `C` and every `kids`:

* `designSV0_of_leaf` (built): `TextRun → DesignSV C 0`;
* `designSV0_leaf_text` (here): `DesignSV C 0 → TextRun` (the oracle
  seeding is the seeding, `oracle_seq`).

And `TextRun` is a FUNCTION of the seeding and the start state
(`textRun_unique`: `emitAssigns`, `emitRegs`, `emitMemWrites`, `runModuleSV`
are functions). Hence:

* what `DesignSV` adds to `MachineShips` for a leaf: NOTHING about the
  values (clause (b) is the closed run). It adds the FORM — the object the
  parents' endpoints and the writer theorem speak about — and the second
  half of the parents' conclusion, "EVERY closed run from the same seeding
  and states shows the source", which for a leaf is uniqueness of the text
  run and needs NO width premise and no check (`designSV0_leaf_unique`);
  the parents get it from `design_sv_backN` under `designCheck`, `outsCheck`
  and the width conditions.
* what `MachineShips` says that the parents' conclusion form does not:
  clause (a), the IR run of the shipped module with the same environments.
  `leaf_design_of_ships` / `leaf_entry_design_all` KEEP it;
  the parents'-shape statements (`leaf_design0_of_checks`,
  `leaf_entry_design0_of_wired`, `leaf_entry_design`) do not state it.

## The design-level endpoint of an entry without calls (item 1)

    ∀ {mctx mref cctx cref w w' b design}
      (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
      (entry : MachineDefines mctx mref cctx cref f d.shape),
      ∃ raw,
        (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
        (ChildBnd mref cref w →
          ∃ ids, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
          ∃ cache regs, regs.Nodup ∧ regs.length = d.ss.length ∧
            ∀ i bools bits T ins st0 mems (kids : String → KT 0),
              (use conditions) →
              (∃ envsO,
                DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
                  ⟨st0, mems, kids⟩ envsO ∧
                envsO.length = T ∧ (the source on the output ports))
              ∧ ∀ envs', DesignSV (childMap design.modules) 0 (checkedOptimize b)
                    (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                  envs'.length = T ∧ (the source on the output ports))

Premises: the run, `MachineDefines f` (binders), `ChildBnd` (the one
antecedent under the existential — where the parents' closed endpoints have
it). Differences from a parent's depth-0 endpoint, ALL of them:

1. `∃ raw`, not `∃ raw D`. A parent's `D` is the design of the CORE run
   (hidden in `synthesizeCombinational_checked`), which holds its children.
   Here the child map is that of the RETURNED design `design` (a binder,
   not a witness). It does not matter which: the statement holds for EVERY
   child map (`leaf_design0_of_checks C`, `leaf_design_of_ships`), because
   an instance-free module looks nothing up. READ, not proved here: for a
   machine without calls the returned design has NO module
   (`Tools.ShippingChecksDerived.leaf_run_seqOk`, `design.modules = []`,
   BUILT but under `InvW`, which is not an allowed premise; there is no
   `ChildBnd` form), so `childMap design.modules` is `fun _ => none`.
2. use conditions. Common with a parent's: the source inputs on the seeding
   (`SourceInputs f d.bsIn …` on `bools` / `bits` themselves — a parent has
   `d.bsIn.take kD` on the inputs EXTENDED by its calls' outputs), the
   registers pass through the seeding, `rst` low, the start registers at the
   reset values, the inputs within `declWidth b`, the start registers of `b`
   within `declWidth b` (a parent: of `openFlat b …`), the inputs within the
   emitted widths, `Bounded (weS (checkedOptimize b)) st0`.
   ABSENT here (not needed): `seedIn b ins t st "clk" = 0`, `Reset raw D
   kids`, the bound on `openIns b`, `InvN` of the instances' states.
   EXTRA here: `∀ r ∈ seqRegs (dropZeroWidthModule raw), st0 r.1 < 2 ^
   declWidth (dropZeroWidthModule raw) r.1` — the start registers of the
   module BEFORE the checked merge. A parent has no such condition because
   an instance-bearing module is never merged (`mergeChecked_inst`:
   `b = raw`); a leaf can be, and `refineCheck_transfer` across the merge
   needs the merged-away registers' start values within their widths. It is
   `MachineShips`' own condition, kept as it is.
3. `MachineShips`' seeding `seedIn (dropZeroWidthModule raw) ins` is
   rewritten to the parents' `seedIn b ins` (the checked merge keeps the
   input ports, `mergeChecked_ports`). Of its two input conditions over
   `raw.inputs`, the one at `declWidth raw` is DISCHARGED from the one at
   `declWidth b` (same inputs; `declWidth` reads `Module.wires`, kept by
   the merge: `declWidth_of_wires`), and the one at the emitted widths is
   restated over `b.inputs` (the same list). Nine use conditions, against
   `MachineShips`' ten.
4. `kids` is quantified as in the parents and is free: nothing reads it.

SCOPE: one declaration as an entry, depth 0, no call; the module LIST
(`DesignSV` over the returned design's child map) — not the SV string, not
`#sim`; a compiler with the two guards of `Sparkle/IR/RefineCheck.lean`;
the run, the reflection and `ChildBnd` stay premises (`LeafKid` carries the
decided data conditions, the reflection and the closing).

WRITTEN, NOT BUILT. -/
namespace Tools.ShippingLeafDesign
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Sparkle.IR.RegDedup (declWidth)

/-! ## Pure -/

/-- The module the full entry returns has the cleaned module's input ports
and wire declarations: it is that module or its checked merge
(`mergeChecked_ports`). -/
theorem post_ports {b r : Sparkle.IR.AST.Module}
    (h : b = r ∨ b = Sparkle.IR.RefineCheck.mergeChecked r) :
    b.inputs = r.inputs ∧ b.wires = r.wires := by
  rcases h with e | e
  · rw [e]
    exact ⟨rfl, rfl⟩
  · rw [e]
    exact ⟨(Sparkle.IR.RefineCheck.mergeChecked_ports r).1,
      (Sparkle.IR.RefineCheck.mergeChecked_ports r).2.2⟩

/-- The declared width reads the wire declarations only. -/
theorem declWidth_of_wires {m o : Sparkle.IR.AST.Module} (h : o.wires = m.wires) :
    Sparkle.IR.RegDedup.declWidth o = Sparkle.IR.RegDedup.declWidth m := by
  funext x
  unfold Sparkle.IR.RegDedup.declWidth
  rw [h]

/-- **The run of a module's emitted text is a function** of the seeding and
the start state: the emitter's three programs and `runModuleSV` are. -/
theorem textRun_unique {m : Sparkle.IR.AST.Module}
    {seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env} {T : Nat}
    {st : String → Nat} {mems : Sparkle.IR.Semantics.MEnv}
    {envs envs' : List Sparkle.IR.Semantics.Env}
    (h1 : Tools.ShippingDesignSV.TextRun m seed T st mems envs)
    (h2 : Tools.ShippingDesignSV.TextRun m seed T st mems envs') : envs = envs' := by
  obtain ⟨p1, r1, g1, ha1, hr1, hm1, hrun1⟩ := h1
  obtain ⟨p2, r2, g2, ha2, hr2, hm2, hrun2⟩ := h2
  have ep : p1 = p2 := Option.some.inj (ha1.symm.trans ha2)
  have er : r1 = r2 := Option.some.inj (hr1.symm.trans hr2)
  have eg : g1 = g2 := Option.some.inj (hm1.symm.trans hm2)
  subst ep
  subst er
  subst eg
  exact Option.some.inj (hrun1.symm.trans hrun2)

/-- **The converse of `Tools.ShippingLeafEntry.designSV0_of_leaf`**: a closed
run at depth 0 of a module without instances is a run of its own emitted
text from the seeding itself (the oracle seeding is the seeding,
`oracle_seq`), for every child map and every children's state. -/
theorem designSV0_leaf_text
    (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    {o : Sparkle.IR.AST.Module} (hs : o.body.all Sparkle.IR.OptCheck.seqStmtOk = true)
    {seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env} {T : Nat}
    {s : Tools.ShippingHierStateG.KState (Tools.ShippingHierStateG.KT 0)}
    {envs : List Sparkle.IR.Semantics.Env}
    (h : Tools.ShippingDesignSV.DesignSV C 0 o seed T s envs) :
    Tools.ShippingDesignSV.TextRun o seed T s.st s.mems envs := by
  have e := Tools.ShippingLeafEntry.oracle_seq C hs (Tools.ShippingDesignSV.envAt envs T) seed
  have h1 : Tools.ShippingDesignSV.TextRun o
      (Tools.ShippingHierSVRun.oracle C o.body (Tools.ShippingDesignSV.envAt envs T) seed)
      T s.st s.mems envs := by
    obtain ⟨h1, -⟩ := h
    exact h1
  rw [e] at h1
  exact h1

/-- **At depth 0 a module without instances has ONE closed run**: every
closed run from a seeding and a start state is the run of its emitted text
from them — over any child map, with any children's state. No width
premise, no check. -/
theorem designSV0_leaf_unique
    (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    {o : Sparkle.IR.AST.Module} (hs : o.body.all Sparkle.IR.OptCheck.seqStmtOk = true)
    {seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env} {T : Nat}
    {st : String → Nat} {mems : Sparkle.IR.Semantics.MEnv}
    {kids : String → Tools.ShippingHierStateG.KT 0}
    {envs envs' : List Sparkle.IR.Semantics.Env}
    (h1 : Tools.ShippingDesignSV.TextRun o seed T st mems envs)
    (h2 : Tools.ShippingDesignSV.DesignSV C 0 o seed T ⟨st, mems, kids⟩ envs') :
    envs' = envs := by
  have h2' : Tools.ShippingDesignSV.TextRun o seed T st mems envs' :=
    designSV0_leaf_text C hs h2
  exact textRun_unique h2' h1

/-! ## `MachineShips` at the emitter's own width map, to `DesignSV` at depth 0 -/

/-- **The general bridge, pure**: `MachineShips` of an assignments-and-registers
shipped module `o`, at the emitter's own width map `wofOf o`, where `b` is the
cleaned module `raw` or its checked merge — is, for the SAME environments:
the IR run of `o`; a closed run `DesignSV C 0 o` over EVERY child map `C`
and every children's state; the source on the output ports; and the only
closed run. Seeded by `seedIn b` (`= seedIn raw`: the ports are kept); of
the two input conditions of `MachineShips` over `raw.inputs`, the one at
`declWidth raw` follows from the one at `declWidth b` (`declWidth` reads the
wires, which are kept) and the one at the emitted widths is stated over
`b.inputs` (the same list). -/
theorem leaf_design_of_ships {declName : Name} {d : MachineData}
    {raw b o : Sparkle.IR.AST.Module}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (hs : o.body.all Sparkle.IR.OptCheck.seqStmtOk = true)
    (hpost : b = raw ∨ b = mergeChecked raw)
    (h : MachineShips declName d raw b o (Tools.ShippingDesignSV.wofOf o) dom src) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
        (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv),
        -- the source's inputs are the seeding's, the registers pass through, reset is low
        (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
          (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
          (seedIn b ins t st)) →
        (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
        (∀ t, ins t "rst" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        -- the declared widths' use conditions: inputs, start registers
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
        (∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1) →
        -- ... and the start registers of the module BEFORE the checked merge
        (∀ r ∈ seqRegs raw, st0 r.1 < 2 ^ declWidth raw r.1) →
        -- the emitted widths' use conditions: inputs, start registers
        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS o x) →
        Bounded (Tools.ShippingDesignSV.weS o) st0 →
        ∃ envsO,
          -- the shipped module's IR run
          runModule (declWidth o) o.body (seedIn b ins) T st0 mems = some envsO ∧
          -- the SAME environments are a closed run at depth 0, over EVERY child map
          -- and every children's state
          (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
              (kids : String → Tools.ShippingHierStateG.KT 0),
            Tools.ShippingDesignSV.DesignSV C 0 o (seedIn b ins) T ⟨st0, mems, kids⟩ envsO) ∧
          envsO.length = T ∧
          (∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
            (envsO[j]'hj) q.name = f j) ∧
          -- ... and it is the ONLY closed run from that seeding and those states
          ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
            (kids : String → Tools.ShippingHierStateG.KT 0)
            (envs' : List Sparkle.IR.Semantics.Env),
            Tools.ShippingDesignSV.DesignSV C 0 o (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
            envs' = envsO := by
  obtain ⟨hin, hwires⟩ := post_ports hpost
  have hdw : declWidth b = declWidth raw := declWidth_of_wires hwires
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems hsrc hpass hrst hinit hinsB hfitB hfitRaw hinsW hstB
  have e : seedIn b ins = seedIn raw ins := seedIn_of_inputs hin ins
  rw [e] at hsrc hpass
  rw [e]
  obtain ⟨envsO, hrun, hsv, hlen, hobs⟩ := H i bools bits T ins st0 mems hsrc hpass
    (fun t x hx => by
      have h1 := hinsB t x (by rw [hin]; exact hx)
      rw [hdw] at h1
      exact h1)
    hinsB
    (fun t x hx => hinsW t x (by rw [hin]; exact hx))
    hrst hinit hfitRaw hfitB hstB
  have htext : Tools.ShippingDesignSV.TextRun o (seedIn raw ins) T st0 mems envsO := hsv
  refine ⟨envsO, hrun, ?_, hlen, hobs, ?_⟩
  · intro C kids
    exact Tools.ShippingLeafEntry.designSV0_of_leaf C hs (s := ⟨st0, mems, kids⟩) htext
  · intro C kids envs' hD
    exact designSV0_leaf_unique C hs htext hD

/-- **The design-level endpoint of an entry WITHOUT calls, in the parents'
shape, pure**: from the conclusion of `machine_ships_wired` (`hships`), its
three check antecedents at the emitter's own width map (`hchk`) and the
statement kinds of the shipped module (`hs`) — the last two under a boundary
`A` (the runtime boundary `ChildBnd`, in the uses) — for ANY child map `C`:
under `∃ raw, (b = … ∨ b = …) ∧ (A → …)`, a closed run `DesignSV C 0
(checkedOptimize b)` showing the source exists, and every closed run from
the same seeding and states shows it. -/
theorem leaf_design0_of_checks
    (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) {A : Prop}
    {declName : Name} {d : MachineData}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {b : Sparkle.IR.AST.Module}
    (hships : ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        simpleBody b = false →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShips declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
          (checkedOptimize b) wof dom src)
    (hchk : A →
      Sparkle.IR.OptCheck.simpleBody b = false ∧
        Tools.SVParser.EmitSem.seqCheck
          (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b))
          (Tools.SVParser.EmitSem.weOf
            (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)))
          (Sparkle.IR.OptCheck.checkedOptimize b).body = true ∧
        ((Tools.ShippingSeqSVSoundness.seqNames (Sparkle.IR.OptCheck.checkedOptimize b).body).all
          fun n => Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b) n ==
            Tools.SVParser.EmitSem.weOf
              (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)) n) = true)
    (hs : A → (checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk = true) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (A →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → Tools.ShippingHierStateG.KT 0),
            -- the source's inputs are the seeding's, the registers pass through, reset is low
            (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
              (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
              (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            -- the declared widths' use conditions: inputs, start registers
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1) →
            -- ... and the start registers of the module BEFORE the checked merge
            (∀ r ∈ seqRegs (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw), st0 r.1 < 2 ^ declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) r.1) →
            -- the emitted widths' use conditions: inputs, start registers
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
            Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st0 →
            -- a closed run of the emitted text showing the source exists ...
            (∃ envsO,
              Tools.ShippingDesignSV.DesignSV C 0 (checkedOptimize b) (seedIn b ins) T
                ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) q.name = f j)
            -- ... and EVERY closed run from the same seeding and states shows it
            ∧ ∀ envs', Tools.ShippingDesignSV.DesignSV C 0 (checkedOptimize b) (seedIn b ins) T
                  ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                  (envs'[j]'hj) q.name = f j) := by
  obtain ⟨raw, hpost, H⟩ := hships
  refine ⟨raw, hpost, ?_⟩
  intro hA
  obtain ⟨c1, c2, c3⟩ := hchk hA
  have hS := H (Tools.ShippingDesignSV.wofOf (checkedOptimize b)) c1 c2 c3
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, G⟩ := leaf_design_of_ships (hs hA) hpost hS
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrst hinit hinsB hfitB hfitRaw hinsW hstB
  obtain ⟨envsO, -, hD, hlen, hobs, huniq⟩ :=
    G i bools bits T ins st0 mems hsrc hpass hrst hinit hinsB hfitB hfitRaw hinsW hstB
  refine ⟨⟨envsO, hD C kids, hlen, hobs⟩, ?_⟩
  intro envs' hD'
  have e := huniq C kids envs' hD'
  subst e
  exact ⟨hlen, hobs⟩

/-! ## From the run of the full entry -/

/-- **The design-level endpoint of a leaf register machine as an entry, from
its wired ship-level endpoint**: `hships` is what `f.machine_ships_wired`
gives for the run (its `MachineCloses` binder discharged); the three check
antecedents and the statement kinds are
`Tools.ShippingGuardsLeaf.leaf_entry_textChecks_closed` /
`leaf_entry_shipped_seq_closed` (from `LeafKid`, the run and `ChildBnd`).
The child map is that of the RETURNED design of the run. This is the term
`#machine_leaf_design` instantiates. -/
theorem leaf_entry_design0_of_wired {declName : Name} {d : MachineData}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {c : Name} {dk : MachineData}
    (hships : ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        simpleBody b = false →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShips declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
          (checkedOptimize b) wof dom src)
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w') :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Tools.ShippingChildInv.ChildBnd mref cref w →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → Tools.ShippingHierStateG.KT 0),
            -- the source's inputs are the seeding's, the registers pass through, reset is low
            (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
              (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
              (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            -- the declared widths' use conditions: inputs, start registers
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1) →
            -- ... and the start registers of the module BEFORE the checked merge
            (∀ r ∈ seqRegs (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw), st0 r.1 < 2 ^ declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) r.1) →
            -- the emitted widths' use conditions: inputs, start registers
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
            Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st0 →
            -- a closed run of the emitted text showing the source exists ...
            (∃ envsO,
              Tools.ShippingDesignSV.DesignSV (Tools.ShippingMachineLinked.childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
                ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) q.name = f j)
            -- ... and EVERY closed run from the same seeding and states shows it
            ∧ ∀ envs', Tools.ShippingDesignSV.DesignSV (Tools.ShippingMachineLinked.childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
                  ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                  (envs'[j]'hj) q.name = f j) :=
  leaf_design0_of_checks (Tools.ShippingMachineLinked.childMap design.modules)
    (A := Tools.ShippingChildInv.ChildBnd mref cref w) hships
    (fun hbnd => Tools.ShippingGuardsLeaf.leaf_entry_textChecks_closed K hbnd hr)
    (fun hbnd => Tools.ShippingGuardsLeaf.leaf_entry_shipped_seq_closed K hbnd hr)

/-- **The general bridge: a leaf register machine at the full entry, to the
closed run of its emitted text at depth 0, in the parents' shape.** Premises:
the wired trace theorem of the declaration, the premises about the
declaration (`LeafKid`: decided data, the reflection, the closing), the run;
`ChildBnd` at its start is the one antecedent under `∃ raw`. -/
theorem leaf_entry_design {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref declName d)
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w') :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Tools.ShippingChildInv.ChildBnd mref cref w →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → Tools.ShippingHierStateG.KT 0),
            -- the source's inputs are the seeding's, the registers pass through, reset is low
            (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
              (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
              (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            -- the declared widths' use conditions: inputs, start registers
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1) →
            -- ... and the start registers of the module BEFORE the checked merge
            (∀ r ∈ seqRegs (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw), st0 r.1 < 2 ^ declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) r.1) →
            -- the emitted widths' use conditions: inputs, start registers
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
            Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st0 →
            -- a closed run of the emitted text showing the source exists ...
            (∃ envsO,
              Tools.ShippingDesignSV.DesignSV (Tools.ShippingMachineLinked.childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
                ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) q.name = f j)
            -- ... and EVERY closed run from the same seeding and states shows it
            ∧ ∀ envs', Tools.ShippingDesignSV.DesignSV (Tools.ShippingMachineLinked.childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
                  ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (q : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
                  (envs'[j]'hj) q.name = f j) :=
  leaf_entry_design0_of_wired
    (Tools.ShippingMachineShipsW.machine_ships_wired d @soundL K.leaf K.slots K.ss K.outTy hr
      K.entry (K.closes mctx cctx))
    K hr

/-- **The same bridge in its strongest form**: with `ChildBnd` a hypothesis,
the environments of the shipped module's IR run are a closed run over EVERY
child map and every children's state, they show the source, and they are
the only closed run. (`leaf_entry_design` is this at the returned design's
child map, without the IR-run clause and with the uniqueness read as "every
closed run shows the source".) -/
theorem leaf_entry_design_all {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref declName d)
    (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w') :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
      ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        regs.Nodup ∧ regs.length = d.ss.length ∧
        ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
          (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
          (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv),
          -- the source's inputs are the seeding's, the registers pass through, reset is low
          (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
            (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
            (seedIn b ins t st)) →
          (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
          (∀ t, ins t "rst" = 0) →
          (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
            d.shape.layout.slots[k]? = some f → st0 r = f.init) →
          -- the declared widths' use conditions: inputs, start registers
          (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
          (∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1) →
          -- ... and the start registers of the module BEFORE the checked merge
          (∀ r ∈ seqRegs (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw), st0 r.1 < 2 ^ declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) r.1) →
          -- the emitted widths' use conditions: inputs, start registers
          (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) →
          Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st0 →
          ∃ envsO,
            -- the shipped module's IR run
            runModule (declWidth (checkedOptimize b)) (checkedOptimize b).body (seedIn b ins) T st0 mems = some envsO ∧
            -- the SAME environments are a closed run at depth 0, over EVERY child map
            -- and every children's state
            (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
                (kids : String → Tools.ShippingHierStateG.KT 0),
              Tools.ShippingDesignSV.DesignSV C 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO) ∧
            envsO.length = T ∧
            (∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
              d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
              (envsO[j]'hj) q.name = f j) ∧
            -- ... and it is the ONLY closed run from that seeding and those states
            ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
              (kids : String → Tools.ShippingHierStateG.KT 0)
              (envs' : List Sparkle.IR.Semantics.Env),
              Tools.ShippingDesignSV.DesignSV C 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
              envs' = envsO := by
  obtain ⟨raw, hpost, hS⟩ :=
    Tools.ShippingGuardsLeaf.leaf_entry_ships_closed d @soundL K hbnd hr
  exact ⟨raw, hpost,
    leaf_design_of_ships (Tools.ShippingGuardsLeaf.leaf_entry_shipped_seq_closed K hbnd hr)
      hpost hS⟩

end Tools.ShippingLeafDesign
