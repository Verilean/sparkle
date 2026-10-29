import Tools.ShippingGen2SlotlessParentRun
import Tools.ShippingGen2TopVacuity
import Tools.ShippingSlotlessClk
import Tools.ShippingSlotlessKidFacts
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- WRITTEN, NOT BUILT (2026-10-29). To be confirmed by `kjob lake build Tests.Gen2.S5Check`.
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # S5 stage A/B checks and the D1 vacuity lemma (scripts/gen2/S5_SLOTLESS_FREEZE.md rev0 §7, §8)

1. **Expected types** (`Tests.Gen3.ExpectedType.checkExpected`: binder by binder, names, binder infos, types,
   conclusion; `==` else logged `isDefEq`) against independent `Exp…` statements written from the freeze §3/§4 text
   (A1, A2 + `NoTouchZ`, A3 + `slSeedZ`, B1, B2, B3) and from the vacuity task (V0-V2). Meaning-changing MUTANTS
   must be REJECTED (`checkMutant`).
2. **Pair check against the originals** (`s5CheckPair`): every binder of the original (`calls_ports`, C6,
   `oneOut_childShips`, `group_childShips`) is present in the copy, in order, with the same binder info and the SAME
   type, except the listed renamed/changed one (`hsl` ↦ `hsl0`); the copy's extra binders are exactly the listed ones
   (A3: `hZ`); B2/B3 also have the original's conclusion.
3. **Audit, full reachable closure** (`s5Reach`, as `s3Reach`, S3GroupCheck:238-262: type and explicit body of every
   reached constant, every namespace): no new declaration reaches a constant of `Tools.ShippingSlotlessClk.*`
   (incl. `SeqKid`) or `Tools.ShippingSlotlessKidFacts.*`. Detector controls with the SAME search: a direct use of
   `SeqKid`, a use through two helpers in other namespaces, a direct use of `core_runFactsS` are found; an unrelated
   theorem is not.
4. **Controls.** P1: a toy body (`o := a`, an instance reading `x`) is `NoTouchZ ["rst","clk"]` (proved) and A2
   applies to two seeds that differ only at `"rst"`. N1: `¬ NoTouchZ ["rst","clk"] [o := rst]` (proved); the
   comb-only mutant of A1 is rejected (MutA1comb).
5. **D1 vacuity, used.** For a module without a `"clk"` input the clock binder of `TopShips` is refuted, so
   `TopShips`'s INNER guarantee holds for every `ids`/`cache`/`regs` and `TopShips` is exactly its OUTER existence.
   This is NOT non-vacuity evidence for anything (no syntactic `False.elim` scan is used as such evidence).
6. Axioms: `checkAxioms` (standard axioms only) and `#print axioms` of every new declaration. -/

namespace Tests.Gen2.S5ReachHelperA
/-- helper 1 (uses `SeqKid`) -/
theorem helperA : True := (fun _ => trivial) @Tools.ShippingSlotlessClk.SeqKid
end Tests.Gen2.S5ReachHelperA

namespace Tests.Gen2.S5ReachHelperB
/-- helper 2 (uses helper 1) -/
theorem helperB : True := Tests.Gen2.S5ReachHelperA.helperA
end Tests.Gen2.S5ReachHelperB

namespace Tests.Gen2.S5ReachFixture
/-- closure-detector control: direct use of `SeqKid` -/
theorem badDirect : True := (fun _ => trivial) @Tools.ShippingSlotlessClk.SeqKid
/-- closure-detector control: use through two helpers in other namespaces -/
theorem badIndirect : True := Tests.Gen2.S5ReachHelperB.helperB
/-- closure-detector control: direct use of a `SlotlessKidFacts` theorem -/
theorem badKidFacts : True := (fun _ => trivial) @Tools.ShippingSlotlessKidFacts.core_runFactsS
/-- closure-detector control: unrelated (must NOT be flagged) -/
theorem goodUnrelated : True := trivial
end Tests.Gen2.S5ReachFixture

namespace Tests.Gen2.S5Check

/-! ## 1. Expected statements -/

section ExpectedA
-- the opens of Tools/ShippingGen2SlotlessParent.lean
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierMono
open Tools.ShippingMachineDepth Tools.ShippingMachineDepthChild Tools.ShippingMachineDepthRun
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCompose (argPorts machPorts_length)
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineChild (boolsOf bitsOf)
open Tools.ShippingGen2SlotlessParent (NoTouchZ)

/-- A1, freeze §3. -/
def ExpA1 : Prop :=
  ∀ {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (len : ids.length = d.shape.binders.length)
    (hsl0 : d.shape.layout.slots = [])
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length),
    (m.inputs.map (·.name)).Nodup ∧
    (("clk" ∈ m.inputs.map (·.name) ∧ "rst" ∈ m.inputs.map (·.name)) ∨
      ("clk" ∉ m.inputs.map (·.name) ∧ "rst" ∉ m.inputs.map (·.name))) ∧
    (∀ x ∈ m.outputs.map (·.name), x ∉ m.inputs.map (·.name)) ∧
    argPorts m = machPorts declName ids cache (d.bsIn.take kD) ∧
    (∀ x ∈ ((machPorts declName ids cache d.shape.binders).map (·.name)).drop
        (((machPorts declName ids cache d.shape.binders).map (·.name)).length -
          d.shape.layout.lets - d.shape.layout.slots.length), x ∉ m.inputs.map (·.name))

/-- MUTANT of A1: the comb case only (false for a module with clk/rst inputs, case S). -/
def MutA1comb : Prop :=
  ∀ {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (len : ids.length = d.shape.binders.length)
    (hsl0 : d.shape.layout.slots = [])
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length),
    (m.inputs.map (·.name)).Nodup ∧
    ("clk" ∉ m.inputs.map (·.name) ∧ "rst" ∉ m.inputs.map (·.name)) ∧
    (∀ x ∈ m.outputs.map (·.name), x ∉ m.inputs.map (·.name)) ∧
    argPorts m = machPorts declName ids cache (d.bsIn.take kD) ∧
    (∀ x ∈ ((machPorts declName ids cache d.shape.binders).map (·.name)).drop
        (((machPorts declName ids cache d.shape.binders).map (·.name)).length -
          d.shape.layout.lets - d.shape.layout.slots.length), x ∉ m.inputs.map (·.name))

/-- `NoTouchZ`, freeze §3 A2 (definition value). -/
def ExpNoTouchZ (Z : List String) (body : List Stmt) : Prop :=
  ∀ st ∈ body,
    (∃ l r, st = Stmt.assign l r ∧ l ∉ Z ∧ ∀ z ∈ Z, z ∉ Sparkle.IR.Reorder.refsOf r) ∨
    (∃ mn iname conns, st = Stmt.inst mn iname conns ∧ ∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ Z)

/-- MUTANT of `NoTouchZ`: the read clause of assignments dropped. -/
def MutNoTouchZ (Z : List String) (body : List Stmt) : Prop :=
  ∀ st ∈ body,
    (∃ l r, st = Stmt.assign l r ∧ l ∉ Z) ∨
    (∃ mn iname conns, st = Stmt.inst mn iname conns ∧ ∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ Z)

/-- A2, freeze §3. -/
def ExpA2 : Prop :=
  ∀ {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) (we : WEnv)
    (children : String → Option (Module × WEnv)) {body : List Stmt} {Z : List String}
    (hZ : NoTouchZ Z body) {seed₁ seed₂ : Nat → (String → Nat) → Env}
    (hagree : ∀ t st y, y ∉ Z → seed₁ t st y = seed₂ t st y),
    ∀ (T : Nat) (s : KState σ) (envs₁ : List Env),
      runModuleTG KS we children body seed₁ T s = some envs₁ →
      ∃ envs₂, runModuleTG KS we children body seed₂ T s = some envs₂ ∧ envs₂.length = envs₁.length ∧
        ∀ j (h₁ : j < envs₁.length) (h₂ : j < envs₂.length) (y : String), y ∉ Z →
          (envs₂[j]'h₂) y = (envs₁[j]'h₁) y

/-- MUTANT of A2: agreement everywhere (not only off `Z`). -/
def MutA2all : Prop :=
  ∀ {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) (we : WEnv)
    (children : String → Option (Module × WEnv)) {body : List Stmt} {Z : List String}
    (hZ : NoTouchZ Z body) {seed₁ seed₂ : Nat → (String → Nat) → Env}
    (hagree : ∀ t st y, y ∉ Z → seed₁ t st y = seed₂ t st y),
    ∀ (T : Nat) (s : KState σ) (envs₁ : List Env),
      runModuleTG KS we children body seed₁ T s = some envs₁ →
      ∃ envs₂, runModuleTG KS we children body seed₂ T s = some envs₂ ∧ envs₂.length = envs₁.length ∧
        ∀ j (h₁ : j < envs₁.length) (h₂ : j < envs₂.length) (y : String),
          (envs₂[j]'h₂) y = (envs₁[j]'h₁) y

/-- `slSeedZ`, freeze §3 A3 (definition value). -/
def ExpSlSeedZ (m : Module) (ins : Nat → String → Nat) : Nat → (String → Nat) → Env :=
  fun t st => seedIn m ins t (fun x => if x = "rst" ∨ x = "clk" then 0 else st x)

/-- A3, freeze §3. -/
def ExpA3 : Prop :=
  ∀ (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl0 : d.shape.layout.slots = [])
    (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length) (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hextB : ∀ i bools bits j, j < kD → extB i bools bits j = bools j)
    (hext : ∀ i bools bits j n', j < kD → ext i bools bits j n' = bits j n')
    (i : ι) {mc raw : Module} {D dsn : Design}
    (hcomp : ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hEA : ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules))
    (hNI : NoInstOf raw.name raw.body)
    (hZ : "rst" ∉ raw.inputs.map (·.name) → NoTouchZ ["rst", "clk"] raw.body),
    Tools.ShippingGen2.ChildRunN (childMap dsn.modules) dsn (n + 1) mc (d.bsIn.take kD)
      d.shape.layout.outs (fun vals => src i (boolsOf (d.bsIn.take kD) vals) (bitsOf (d.bsIn.take kD) vals))

/-- MUTANT of A3: the sequential conclusion kept (`SeqChildRunN`, as C6). -/
def MutA3seq : Prop :=
  ∀ (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl0 : d.shape.layout.slots = [])
    (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length) (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hextB : ∀ i bools bits j, j < kD → extB i bools bits j = bools j)
    (hext : ∀ i bools bits j n', j < kD → ext i bools bits j n' = bits j n')
    (i : ι) {mc raw : Module} {D dsn : Design}
    (hcomp : ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hEA : ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules))
    (hNI : NoInstOf raw.name raw.body)
    (hZ : "rst" ∉ raw.inputs.map (·.name) → NoTouchZ ["rst", "clk"] raw.body),
    SeqChildRunN (childMap dsn.modules) dsn (n + 1) mc (d.bsIn.take kD)
      d.shape.layout.outs (fun vals => src i (boolsOf (d.bsIn.take kD) vals) (bitsOf (d.bsIn.take kD) vals))

/-- MUTANT of A3: `hZ` unconditional (a premise not tied to the module's inputs). -/
def MutA3hZ : Prop :=
  ∀ (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl0 : d.shape.layout.slots = [])
    (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length) (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hextB : ∀ i bools bits j, j < kD → extB i bools bits j = bools j)
    (hext : ∀ i bools bits j n', j < kD → ext i bools bits j n' = bits j n')
    (i : ι) {mc raw : Module} {D dsn : Design}
    (hcomp : ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hEA : ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules))
    (hNI : NoInstOf raw.name raw.body)
    (hZ : NoTouchZ ["rst", "clk"] raw.body),
    Tools.ShippingGen2.ChildRunN (childMap dsn.modules) dsn (n + 1) mc (d.bsIn.take kD)
      d.shape.layout.outs (fun vals => src i (boolsOf (d.bsIn.take kD) vals) (bitsOf (d.bsIn.take kD) vals))

end ExpectedA

section ExpectedB
-- the opens of Tools/ShippingGen2SlotlessParentRun.lean (GroupServed:247-266)
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingGen2
open Tools.ShippingGen2SlotlessParent (NoTouchZ)

/-- B1, freeze §4. -/
def ExpB1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hins : p.d.shape.insts ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hrst : "rst" ∉ raw.inputs.map (·.name)),
    NoTouchZ ["rst", "clk"] raw.body

/-- MUTANT of B1: the reset absence dropped (the claim would hold for case-S parents too). -/
def MutB1noRst : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hins : p.d.shape.insts ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D),
    NoTouchZ ["rst", "clk"] raw.body

/-- B2, freeze §4. -/
def ExpB2 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat),
    ChildShips p (n + 1) b D

/-- B3, freeze §4. -/
def ExpB3 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc),
    ChildShips p (n + 1) b D

/-- MUTANT of B3: the height of the trace's `ShipsAt` decoupled from the conclusion's (`n + 1` at `ShipsAt … (n + 1)`). -/
def MutB3height : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P (n + 1)) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc),
    ChildShips p (n + 1) b D

/-- V0: the clock binder is refutable without a clock input. -/
def ExpV0 : Prop :=
  ∀ {b : Sparkle.IR.AST.Module} (ins : Nat → String → Nat)
    (h : "clk" ∉ b.inputs.map (·.name)), ¬ (∀ t st, seedIn b ins t st "clk" = 0)

/-- V1: the INNER guarantee holds for every `ids`/`cache`/`regs` without a clock input. -/
def ExpV1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) (h : "clk" ∉ b.inputs.map (·.name))
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    TopShipsInner p n declName b raw D ids cache regs

/-- V2: `TopShips` is exactly its OUTER existence without a clock input. -/
def ExpV2 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) (h : "clk" ∉ b.inputs.map (·.name)),
    TopShips p n declName b raw D ↔
      ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
      ∃ (_cache : IO.Ref (ExprStructMap String)) (regs : List String),
        regs.Nodup ∧ regs.length = p.d.ss.length

/-- MUTANT of V2: the OUTER existence claimed vacuous as well (`TopShips ↔ True`). -/
def MutV2 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) (h : "clk" ∉ b.inputs.map (·.name)),
    TopShips p n declName b raw D ↔ True

end ExpectedB

/-! ## 2. Pair check against the originals -/
open Lean Meta Elab Command
open Tests.Gen3.ExpectedType

/-- Every binder of `orig` is in `copy` in order, same binder info, SAME type, except: names renamed per `ren`
(their types not compared: they are the changed binders); the copy's remaining binders are exactly `added`;
the conclusion compared iff `concl`. -/
def s5CheckPair (orig copy : Name) (ren : List (Name × Name)) (added : List Name) (concl : Bool) : MetaM Unit := do
  let ciO ← getConstInfo orig
  let ciC ← getConstInfo copy
  forallTelescope ciO.type fun xs bodyO => do
    let decls ← xs.mapM (·.fvarId!.getDecl)
    let mut t := ciC.type
    for i in [0:xs.size] do
      let dO := decls[i]!
      let nO := dO.userName.eraseMacroScopes
      let expName := (ren.lookup nO).getD nO
      let .forallE n ty b bi := t
        | throwError "S5 PAIR FAILED {copy}: fewer binders than {orig} (at {nO})"
      unless n.eraseMacroScopes == expName do
        throwError "S5 PAIR FAILED {copy}: binder {i} is {n}, expected {expName} (original {nO})"
      unless bi == dO.binderInfo do
        throwError "S5 PAIR FAILED {copy}: binder {n} has a different binder info"
      if (ren.lookup nO).isNone then
        cmpEq s!"{copy} vs {orig} binder {n}" ty dO.type
      t := b.instantiate1 xs[i]!
    let mut extra : List Name := []
    let mut t' := t
    repeat
      match t' with
      | .forallE n _ b _ =>
        extra := extra ++ [n.eraseMacroScopes]
        t' := b
      | _ => break
    if concl then
      unless extra.isEmpty do throwError "S5 PAIR FAILED {copy}: extra binders {extra}"
      cmpEq s!"{copy} vs {orig} conclusion" t bodyO
    else
      unless extra.take added.length == added do
        throwError "S5 PAIR FAILED {copy}: extra binders {extra}, expected to start with {added}"
  logInfo m!"S5 PAIR OK {copy} against {orig}: renamed {toString ren}, added {added}, conclusion compared {concl}"

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  -- 1. expected types and mutants
  checkExpected ``Tools.ShippingGen2SlotlessParent.calls_ports_sl ``ExpA1
  checkExpected ``Tools.ShippingGen2SlotlessParent.NoTouchZ ``ExpNoTouchZ
  checkExpected ``Tools.ShippingGen2SlotlessParent.runModuleTG_seed_offZ ``ExpA2
  checkExpected ``Tools.ShippingGen2SlotlessParent.slSeedZ ``ExpSlSeedZ
  checkExpected ``Tools.ShippingGen2SlotlessParent.childRunN_of_composedNW_runSl ``ExpA3
  checkExpected ``Tools.ShippingGen2.slotlessParent_noTouch_ofRun ``ExpB1
  checkExpected ``Tools.ShippingGen2.oneOutSl_childShips ``ExpB2
  checkExpected ``Tools.ShippingGen2.groupSl_childShips ``ExpB3
  checkExpected ``Tools.ShippingGen2.not_seedIn_clk_zero ``ExpV0
  checkExpected ``Tools.ShippingGen2.topShipsInner_of_noClk ``ExpV1
  checkExpected ``Tools.ShippingGen2.topShips_iff_outer_of_noClk ``ExpV2
  checkMutant ``Tools.ShippingGen2SlotlessParent.calls_ports_sl ``MutA1comb
  checkMutant ``Tools.ShippingGen2SlotlessParent.NoTouchZ ``MutNoTouchZ
  checkMutant ``Tools.ShippingGen2SlotlessParent.runModuleTG_seed_offZ ``MutA2all
  checkMutant ``Tools.ShippingGen2SlotlessParent.childRunN_of_composedNW_runSl ``MutA3seq
  checkMutant ``Tools.ShippingGen2SlotlessParent.childRunN_of_composedNW_runSl ``MutA3hZ
  checkMutant ``Tools.ShippingGen2.slotlessParent_noTouch_ofRun ``MutB1noRst
  checkMutant ``Tools.ShippingGen2.groupSl_childShips ``MutB3height
  checkMutant ``Tools.ShippingGen2.topShips_iff_outer_of_noClk ``MutV2
  -- 2. pairs against the originals (only `hsl` ↦ `hsl0` changes; A3 adds `hZ`)
  s5CheckPair ``Tools.ShippingMachineDepthChild.calls_ports ``Tools.ShippingGen2SlotlessParent.calls_ports_sl
    [(`hsl, `hsl0)] [] false
  s5CheckPair ``Tools.ShippingGen2C6.seqChildRunN_of_composedNW_run
    ``Tools.ShippingGen2SlotlessParent.childRunN_of_composedNW_runSl [(`hsl, `hsl0)] [`hZ] false
  s5CheckPair ``Tools.ShippingGen2.oneOut_childShips ``Tools.ShippingGen2.oneOutSl_childShips
    [(`hsl, `hsl0)] [] true
  s5CheckPair ``Tools.ShippingGen2.group_childShips ``Tools.ShippingGen2.groupSl_childShips
    [(`hsl, `hsl0)] [] true

/-! ## 3. Audit: full reachable closure -/

/-- Every new declaration of this unit (stage A, stage B, D1 vacuity). -/
def s5New : List Name :=
  [``Tools.ShippingGen2SlotlessParent.allocated_notZ, ``Tools.ShippingGen2SlotlessParent.outName_notZ,
   ``Tools.ShippingGen2SlotlessParent.calls_ports_sl, ``Tools.ShippingGen2SlotlessParent.NoTouchZ,
   ``Tools.ShippingGen2SlotlessParent.noTouchZ_tail, ``Tools.ShippingGen2SlotlessParent.bindOuts_agreeZ,
   ``Tools.ShippingGen2SlotlessParent.evalAssignsKG_offZ, ``Tools.ShippingGen2SlotlessParent.regNexts_noTouch,
   ``Tools.ShippingGen2SlotlessParent.memNexts_noTouch, ``Tools.ShippingGen2SlotlessParent.stepModuleTG_offZ,
   ``Tools.ShippingGen2SlotlessParent.runModuleTG_seed_offZ, ``Tools.ShippingGen2SlotlessParent.slSeedZ,
   ``Tools.ShippingGen2SlotlessParent.slSeedZ_agree,
   ``Tools.ShippingGen2SlotlessParent.childRunN_of_composedNW_runSl,
   ``Tools.ShippingGen2.slp_readsClosedB_mem, ``Tools.ShippingGen2.slp_mapM_mem', ``Tools.ShippingGen2.slp_mapM_mem,
   ``Tools.ShippingGen2.slotlessParent_noTouch_ofRun, ``Tools.ShippingGen2.oneOutSl_childShips,
   ``Tools.ShippingGen2.groupSl_childShips,
   ``Tools.ShippingGen2.not_seedIn_clk_zero, ``Tools.ShippingGen2.TopShipsInner, ``Tools.ShippingGen2.topShips_iff_inner,
   ``Tools.ShippingGen2.topShipsInner_of_noClk, ``Tools.ShippingGen2.topShips_iff_outer_of_noClk]

/-- The forbidden constants: the old-boundary slotless facts (freeze §8.2). -/
def s5Forbidden (n : Name) : Bool :=
  (`Tools.ShippingSlotlessClk).isPrefixOf n || (`Tools.ShippingSlotlessKidFacts).isPrefixOf n

/-- The body of a constant, read EXPLICITLY per kind (as `s3Body?`). -/
def s5Body? : ConstantInfo → Option Lean.Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure S5Reach where
  hit : Option (List Name) := none
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Array Name := #[]
  deriving Inhabited

/-- Breadth-first search of the FULL dependency closure of `root` (as `s3Reach`) for a forbidden constant. -/
def s5Reach (root : Name) (cap : Nat := 3000000) : MetaM S5Reach := do
  let env ← getEnv
  let mut out : S5Reach := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then
      throwError "S5 AUDIT INCOMPLETE at {root}: more than {cap} constants; non-reference NOT established"
    let some ci := env.find? c | continue
    let body := s5Body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques.push c }
    let used := ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[]
    for u in used do
      if s5Forbidden u then
        return { out with hit := some (path ++ [u]) }
      unless seen.contains u do
        seen := seen.insert u
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  -- detector controls with the SAME search
  for (c, bad) in [(``Tests.Gen2.S5ReachFixture.badDirect, true), (``Tests.Gen2.S5ReachFixture.badIndirect, true),
      (``Tests.Gen2.S5ReachFixture.badKidFacts, true), (``Tests.Gen2.S5ReachFixture.goodUnrelated, false)] do
    let r ← s5Reach c
    if bad && r.hit.isNone then throwError "S5 AUDIT FAILED: the closure detector misses {c}"
    if !bad && r.hit.isSome then throwError "S5 AUDIT FAILED: the closure detector flags {c}"
    logInfo m!"S5 REACH CONTROL {c}: {toString r.hit}"
  for c in s5New do
    let r ← s5Reach c
    if let some p := r.hit then
      throwError "S5 AUDIT FAILED {c}: reaches an old-boundary slotless constant via {p}"
    logInfo m!"S5 REACH {c}: no Tools.ShippingSlotlessClk.* / Tools.ShippingSlotlessKidFacts.* in the closure (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques.size}: implementations of opaque/partial constants are not kernel terms and are not followed)"
  -- axioms
  for c in s5New do
    checkAxioms c

end Tests.Gen2.S5Check

/-! ## 4. Controls P1, N1 -/
namespace Tests.Gen2.S5CheckControls
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingGen2SlotlessParent

/-- The toy body: `o := a`, and an instance `i` of `k` reading `x`. -/
def p1Body : List Stmt := [.assign "o" (.ref "a"), .inst "k" "i" [("a", .ref "x")]]

/-- **P1** the toy body touches neither the reset nor the clock. -/
theorem p1_noTouch : NoTouchZ ["rst", "clk"] p1Body := by
  intro st hst
  rcases List.mem_cons.mp hst with rfl | hst
  · refine Or.inl ⟨"o", .ref "a", rfl, by simp, fun z hz hzr => ?_⟩
    simp only [Sparkle.IR.Reorder.refsOf, List.mem_singleton] at hzr
    subst hzr
    simp at hz
  · rw [List.mem_singleton] at hst
    subst hst
    refine Or.inr ⟨"k", "i", [("a", .ref "x")], rfl, fun c hc w hw => ?_⟩
    rw [List.mem_singleton] at hc
    subst hc
    have hwx : w = "x" := by simpa using hw.symm
    subst hwx
    simp

/-- **P1** A2 applied to two seeds that differ only at `"rst"` (flat children). -/
theorem p1_A2 (we : WEnv) (children : String → Option (Module × WEnv)) :
    ∀ (T : Nat) (s : KState KidState) (envs₁ : List Env),
      runModuleTG flatKS we children p1Body (fun _ _ n => if n = "rst" then 1 else 0) T s = some envs₁ →
      ∃ envs₂, runModuleTG flatKS we children p1Body (fun _ _ _ => 0) T s = some envs₂ ∧
        envs₂.length = envs₁.length ∧
        ∀ j (h₁ : j < envs₁.length) (h₂ : j < envs₂.length) (y : String), y ∉ ["rst", "clk"] →
          (envs₂[j]'h₂) y = (envs₁[j]'h₁) y :=
  runModuleTG_seed_offZ flatKS flatKS_local we children p1_noTouch (fun t st y hy => by
    have hy1 : y ≠ "rst" := fun h => hy (by subst h; simp)
    simp [hy1])

/-- **N1** an assignment reading the reset is not `NoTouchZ`. -/
theorem n1_reads_rst : ¬ NoTouchZ ["rst", "clk"] [Stmt.assign "o" (.ref "rst")] := by
  intro h
  rcases h _ List.mem_cons_self with ⟨l, r, heq, _, hr⟩ | ⟨mn, iname, conns, heq, _⟩
  · cases heq
    exact hr "rst" (by simp) (by simp [Sparkle.IR.Reorder.refsOf])
  · cases heq

/-! ## 5. D1 vacuity, used -/

/-- A module without inputs (in particular without `"clk"`). -/
def vacM : Module := { name := "s5vac", inputs := [], outputs := [], wires := [], body := [] }

theorem vacM_noClk : "clk" ∉ vacM.inputs.map (·.name) := by simp [vacM]

/-- The clock binder of `TopShips` is refuted for `vacM`. -/
theorem vacM_clk_refuted : ¬ (∀ t st, seedIn vacM (fun _ _ => 0) t st "clk" = 0) :=
  Tools.ShippingGen2.not_seedIn_clk_zero _ vacM_noClk

/-- For `vacM` the INNER guarantee of `TopShips` holds for every `ids`/`cache`/`regs` and any package (it carries no
information about any run); only the OUTER existence remains. -/
example {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} (p : Tools.ShippingGen2.Pkg ι dom) (n : Nat)
    (declName : Lean.Name) (raw : Module) (D : Design) (ids : List Lean.FVarId)
    (cache : IO.Ref (Lean.ExprStructMap String)) (regs : List String) :
    Tools.ShippingGen2.TopShipsInner p n declName vacM raw D ids cache regs :=
  Tools.ShippingGen2.topShipsInner_of_noClk p n declName vacM raw D vacM_noClk ids cache regs

end Tests.Gen2.S5CheckControls

#print axioms Tools.ShippingGen2SlotlessParent.calls_ports_sl
#print axioms Tools.ShippingGen2SlotlessParent.runModuleTG_seed_offZ
#print axioms Tools.ShippingGen2SlotlessParent.stepModuleTG_offZ
#print axioms Tools.ShippingGen2SlotlessParent.childRunN_of_composedNW_runSl
#print axioms Tools.ShippingGen2.slotlessParent_noTouch_ofRun
#print axioms Tools.ShippingGen2.oneOutSl_childShips
#print axioms Tools.ShippingGen2.groupSl_childShips
#print axioms Tools.ShippingGen2.not_seedIn_clk_zero
#print axioms Tools.ShippingGen2.topShipsInner_of_noClk
#print axioms Tools.ShippingGen2.topShips_iff_outer_of_noClk
#print axioms Tests.Gen2.S5CheckControls.p1_noTouch
#print axioms Tests.Gen2.S5CheckControls.p1_A2
#print axioms Tests.Gen2.S5CheckControls.n1_reads_rst
#print axioms Tests.Gen2.S5CheckControls.vacM_clk_refuted

run_cmd Lean.Elab.Command.liftTermElabM do
  for c in [``Tests.Gen2.S5CheckControls.p1_noTouch, ``Tests.Gen2.S5CheckControls.p1_A2,
      ``Tests.Gen2.S5CheckControls.n1_reads_rst, ``Tests.Gen2.S5CheckControls.vacM_clk_refuted] do
    Tests.Gen3.ExpectedType.checkAxioms c
