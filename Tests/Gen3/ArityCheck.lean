import Tools.ShippingGen3Arity
import Tests.Gen3.ExpectedType
import Tests.Compiler.ShippingMachineLinkedTest
import Tests.Compiler.ShippingMachineSeqTest
set_option autoImplicit false
-- NOT BUILT (written without running Lean; the integrator builds it on the cluster).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # U-ARITY checks (scripts/gen3/UARITY_FREEZE.md §5, §6)

1. **Expected types.** Each of A0-A7 is compared MECHANICALLY (`Tests.Gen3.ExpectedType.checkExpected`: binder by binder,
   names, binder infos, types, conclusion; `==` else logged `isDefEq`) against an independent `Expected…` statement
   written below from the freeze §2 text. Meaning-changing MUTANTS (lengths swapped/replaced, the served witness dropped,
   `hnone` dropped, the group membership dropped, clk/rst filter dropped) must FAIL (`checkMutant`). A `#check` display is
   not used as a substitute.
2. **Data controls** (data only; they say nothing about the run premises):
   * P1 one-output `callerL` → `pickByteH`: the arity row decided (2 = 2), and the data premises `hk`, `hnone`, `hP`
     (through the concrete `PL`), `instFields = []` decided (V: the data part of A5/A7's premises is satisfiable).
   * P2 the application path of A7 for every package with `callerL`'s data: this unit exhibits no package/run witness.
   * P3 group `parent` → `cnt`: `instFields ≠ []`, `hnone`, the row (expected 1 = 1) decided.
3. **Negative controls.** N1: a 2-port module with a 1-argument list has no `CallStmt`/`CallStmtG` (A2/A3). N2: under
   any `P'` sending `pickByteH` to a package whose port count is not 2, no `MachineTraceLBX (ServedP (ShipsRes L P') …)`
   exists for a package with `callerL`'s data; instantiated with the concrete `pbh1Pkg` (`pickByteH` with `kD := 1`,
   one port).
4. Axioms: `checkAxioms` (standard axioms only) and `#print axioms` of every root and control. -/

namespace Tests.Gen3.ArityCheck
open Tools.ShippingGen2
open Tools.ShippingGen3Arity
open Tests.Gen3.ExpectedType
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Sparkle.Core.Domain

/-! ## 1. Expected statements (freeze §2 text; the §2 header opens) -/

section Expected
open Lean hiding Module
open Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingMachineEntry Tools.ShippingMachineLinked
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingChildInv (Res)

def ExpectedA0 : Prop :=
  ∀ {shape : MachineShape} {k : Nat} (hk : k < shape.insts.length) {args : List Nat}
    (hargs : (shape.insts.map (·.2.1))[k]? = some args),
    args = (shape.insts[k]).2.1

def ExpectedA1 : Prop :=
  ∀ {children : String → Option (Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Design} {n : Nat} {mc : Module} {bsC : List (Name × MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : ChildRunN children dsn n mc bsC outsC S),
    (argPorts mc).length = (bsC.filter fun b => b.2 != .domain).length

def ExpectedA2 : Prop :=
  ∀ {nIn kI n k : Nat} {names : List String} {args : List Nat} {mc : Module} {st : Stmt}
    (h : Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc st),
    args.length = (argPorts mc).length

def ExpectedA3 : Prop :=
  ∀ {nIn kI n : Nat} {names : List String} {args : List Nat}
    {outs : List (Nat × String)} {mc : Module} {st : Stmt}
    (h : Tools.ShippingMachineInstG.CallStmtG nIn kI n names args outs mc st),
    args.length = (argPorts mc).length

def ExpectedA4 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) {c : Name} {q : Pkg ι dom} {mc : Module} {Dc D : Design}
    (i : ι)
    (hship : ShipsRes L P c (mc, Dc)) (hP : P c = some q)
    (hDc : ∀ g ∈ Dc.modules, moduleByName D.modules g.name = some g)
    (hmod : moduleByName D.modules mc.name = some mc),
    (argPorts mc).length = q.ports.length

def ExpectedA5 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : Served1P (ShipsRes L P) p.decl p.d.shape raw D ids cache)
    (hf0 : p.d.shape.instFields = []) (i : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q)
    {args : List Nat} {mc : Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInst.CallStmt (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) k args mc st)
    (hmod : moduleByName D.modules mc.name = some mc),
    (p.d.shape.insts[k]).2.1.length = q.ports.length ∧
    ∀ (argWs : List String),
      args.mapM (fun j => ((machPorts p.decl ids cache p.d.shape.binders).map (·.name))[machNIn p.d.shape +
        p.d.shape.insts.length + p.d.shape.layout.slots.length + j]?) = some argWs →
      argWs.length = q.ports.length

def ExpectedA6 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : ServedGP (ShipsRes L P) p.decl p.d.shape raw D ids cache)
    (hfne : p.d.shape.instFields ≠ []) (i : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q)
    {args : List Nat} {outs : List (Nat × String)} {mc : Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInstG.CallStmtG (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) args outs mc st)
    (hkout : (k, p.d.shape.instFields.getD k "") ∈ outs)
    (hmod : moduleByName D.modules mc.name = some mc),
    (p.d.shape.insts[k]).2.1.length = q.ports.length ∧
    ∀ (argWs : List String),
      args.mapM (fun j => ((machPorts p.decl ids cache p.d.shape.binders).map (·.name))[machNIn p.d.shape +
        p.d.shape.insts.length + p.d.shape.layout.slots.length + j]?) = some argWs →
      argWs.length = q.ports.length

def ExpectedA7 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (i : ι) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q),
    (p.d.shape.insts[k]).2.1.length = q.ports.length

/-! ### Mutants (meaning-changing; each must be REJECTED) -/

/-- A0 weakened to lengths. -/
def MutA0 : Prop :=
  ∀ {shape : MachineShape} {k : Nat} (hk : k < shape.insts.length) {args : List Nat}
    (hargs : (shape.insts.map (·.2.1))[k]? = some args),
    args.length = (shape.insts[k]).2.1.length

/-- A1 without the clk/rst filter (all inputs). -/
def MutA1 : Prop :=
  ∀ {children : String → Option (Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Design} {n : Nat} {mc : Module} {bsC : List (Name × MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : ChildRunN children dsn n mc bsC outsC S),
    mc.inputs.length = (bsC.filter fun b => b.2 != .domain).length

/-- A2 against all inputs. -/
def MutA2 : Prop :=
  ∀ {nIn kI n k : Nat} {names : List String} {args : List Nat} {mc : Module} {st : Stmt}
    (h : Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc st),
    args.length = mc.inputs.length

/-- A4 against the package's full binder list (domain binders and calls counted). -/
def MutA4 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) {c : Name} {q : Pkg ι dom} {mc : Module} {Dc D : Design}
    (i : ι)
    (hship : ShipsRes L P c (mc, Dc)) (hP : P c = some q)
    (hDc : ∀ g ∈ Dc.modules, moduleByName D.modules g.name = some g)
    (hmod : moduleByName D.modules mc.name = some mc),
    (argPorts mc).length = q.d.bsIn.length

/-- A5 with the SHIPPING witness dropped (`Served1P` of the trivial predicate). -/
def MutA5served : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : Served1P (fun _ _ => True) p.decl p.d.shape raw D ids cache)
    (hf0 : p.d.shape.instFields = []) (i : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q)
    {args : List Nat} {mc : Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInst.CallStmt (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) k args mc st)
    (hmod : moduleByName D.modules mc.name = some mc),
    (p.d.shape.insts[k]).2.1.length = q.ports.length ∧
    ∀ (argWs : List String),
      args.mapM (fun j => ((machPorts p.decl ids cache p.d.shape.binders).map (·.name))[machNIn p.d.shape +
        p.d.shape.insts.length + p.d.shape.layout.slots.length + j]?) = some argWs →
      argWs.length = q.ports.length

/-- A6 without the call's membership in the group (`hkout` dropped). -/
def MutA6kout : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : ServedGP (ShipsRes L P) p.decl p.d.shape raw D ids cache)
    (hfne : p.d.shape.instFields ≠ []) (i : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q)
    {args : List Nat} {outs : List (Nat × String)} {mc : Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInstG.CallStmtG (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) args outs mc st)
    (hmod : moduleByName D.modules mc.name = some mc),
    (p.d.shape.insts[k]).2.1.length = q.ports.length ∧
    ∀ (argWs : List String),
      args.mapM (fun j => ((machPorts p.decl ids cache p.d.shape.binders).map (·.name))[machNIn p.d.shape +
        p.d.shape.insts.length + p.d.shape.layout.slots.length + j]?) = some argWs →
      argWs.length = q.ports.length

/-- A7 with the served witness dropped (trace of the trivial `X`). -/
def MutA7served : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (fun _ _ => True)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (i : ι) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q),
    (p.d.shape.insts[k]).2.1.length = q.ports.length

/-- A7 with `hnone` dropped (memory-origin calls not excluded). -/
def MutA7hnone : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (i : ι) {k : Nat} (hk : k < p.d.shape.insts.length)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q),
    (p.d.shape.insts[k]).2.1.length = q.ports.length

/-- A7 with the sides swapped AND the package's ports replaced by its full input list. -/
def MutA7ports : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (i : ι) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q),
    q.d.bsIn.length = (p.d.shape.insts[k]).2.1.length

/-- A7 with only the sides swapped (rejected too: the comparison is of the frozen statement, not up to symmetry). -/
def MutA7swap : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (i : ι) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q),
    q.ports.length = (p.d.shape.insts[k]).2.1.length

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``insts_args_eq ``ExpectedA0
  checkExpected ``childRunN_argLen ``ExpectedA1
  checkExpected ``callStmt_argLen ``ExpectedA2
  checkExpected ``callStmtG_argLen ``ExpectedA3
  checkExpected ``argLen_of_shipsRes ``ExpectedA4
  checkExpected ``callArity_one ``ExpectedA5
  checkExpected ``callArity_group ``ExpectedA6
  checkExpected ``callArity_of_trace ``ExpectedA7
  checkMutant ``insts_args_eq ``MutA0
  checkMutant ``childRunN_argLen ``MutA1
  checkMutant ``callStmt_argLen ``MutA2
  checkMutant ``argLen_of_shipsRes ``MutA4
  checkMutant ``callArity_one ``MutA5served
  checkMutant ``callArity_group ``MutA6kout
  checkMutant ``callArity_of_trace ``MutA7served
  checkMutant ``callArity_of_trace ``MutA7hnone
  checkMutant ``callArity_of_trace ``MutA7ports
  checkMutant ``callArity_of_trace ``MutA7swap
  -- the mutants are also mutually distinct from the expected statements (sanity of the harness)
  checkMutant ``ExpectedA7 ``MutA7served

/-! ## 2. Data fixtures (as Tests/Gen2/DataBridgeCheck.lean:37-50; copied, not imported) -/

abbrev U := fun _ : Unit => defaultDomain

/-- `pickByteH`'s comb package. -/
noncomputable def pbhC : CombPkg Unit U :=
  { decl := ``pickByteH, d := pickByteH.machineData, kD := pickByteH.machineData.bsIn.length,
    inits := pickByteH.machineInits, src := pickByteH.machineSource,
    facts := ⟨pickByteH.machine_ok, pickByteH.machine_body, pickByteH.machine_inits, pickByteH.machine_next,
      pickByteH.machine_result⟩ }

noncomputable abbrev pbhPkg : Pkg Unit U := .comb pbhC

/-- A concrete assignment: `pickByteH` ↦ its comb package, everything else ↦ none. -/
noncomputable def PL : Pkgs Unit U := fun c => if c == ``pickByteH then some pbhPkg else none

/-- A MISMATCHED package for N2: `pickByteH` with `kD := 1` (one declared port). -/
noncomputable def pbh1C : CombPkg Unit U := { pbhC with kD := 1 }

noncomputable abbrev pbh1Pkg : Pkg Unit U := .comb pbh1C

noncomputable def PL1 : Pkgs Unit U := fun c => if c == ``pickByteH then some pbh1Pkg else none

theorem pickByteH_beq : ((``pickByteH : Lean.Name) == ``pickByteH) = true := by
  first | decide | rfl

theorem PL_pbh : PL ``pickByteH = some pbhPkg := by
  show (if ((``pickByteH : Lean.Name) == ``pickByteH) = true then some pbhPkg else none) = some pbhPkg
  rw [if_pos pickByteH_beq]

theorem PL1_pbh1 : PL1 ``pickByteH = some pbh1Pkg := by
  show (if ((``pickByteH : Lean.Name) == ``pickByteH) = true then some pbh1Pkg else none) = some pbh1Pkg
  rw [if_pos pickByteH_beq]

/-! ## 3. P1: one-output `callerL` → `pickByteH` (real data, decided) -/

set_option maxRecDepth 100000

theorem callerL_hk : 0 < callerL.machineData.shape.insts.length := by
  first | decide | decide +kernel

theorem callerL_noFields : callerL.machineData.shape.instFields = [] := by
  first | rfl | decide | decide +kernel

theorem callerL_hnone :
    (callerL.machineData.shape.instOrigins.getD 0 Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none :=
  Option.isNone_iff_eq_none.mp (by first | rfl | decide | decide +kernel)

theorem callerL_inst0 : (callerL.machineData.shape.insts[0]'callerL_hk).1 = ``pickByteH := by
  first | decide | decide +kernel

theorem callerL_hP : PL (callerL.machineData.shape.insts[0]'callerL_hk).1 = some pbhPkg := by
  rw [callerL_inst0]; exact PL_pbh

theorem callerL_args_len : (callerL.machineData.shape.insts[0]'callerL_hk).2.1.length = 2 := by
  first | decide | decide +kernel

theorem pbh_ports_len : pbhPkg.ports.length = 2 := by
  first | decide | decide +kernel

theorem pbh1_ports_len : pbh1Pkg.ports.length = 1 := by
  first | decide | decide +kernel

/-- **P1** the arity row on real data (2 = 2). -/
theorem callerL_arity_row : (callerL.machineData.shape.insts[0]'callerL_hk).2.1.length = pbhPkg.ports.length :=
  callerL_args_len.trans pbh_ports_len.symm

/-! ## 4. P2: the application path of A7 (conditional; no package/run witness is exhibited) -/

theorem hk0 (p : Pkg Unit U) (hp : p.d = callerL.machineData) : 0 < p.d.shape.insts.length := by
  rw [hp]; exact callerL_hk

theorem hnone0 (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    (p.d.shape.instOrigins.getD 0 Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none := by
  rw [hp]; exact callerL_hnone

theorem insts0_name (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    (p.d.shape.insts[0]'(hk0 p hp)).1 = ``pickByteH := by
  have key : ∀ (d : Tools.ShippingMachineAuto.MachineData) (hd : d = callerL.machineData)
      (h : 0 < d.shape.insts.length), (d.shape.insts[0]'h).1 = ``pickByteH := by
    intro d hd h
    subst hd
    exact callerL_inst0
  exact key p.d hp (hk0 p hp)

theorem insts0_len (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    (p.d.shape.insts[0]'(hk0 p hp)).2.1.length = 2 := by
  have key : ∀ (d : Tools.ShippingMachineAuto.MachineData) (hd : d = callerL.machineData)
      (h : 0 < d.shape.insts.length), (d.shape.insts[0]'h).2.1.length = 2 := by
    intro d hd h
    subst hd
    exact callerL_args_len
  exact key p.d hp (hk0 p hp)

/-- **P2** every package with `callerL`'s data, under a served trace through `PL`, gets the arity row. -/
theorem callerL_arity {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (p : Pkg Unit U) (hp : p.d = callerL.machineData)
    {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L PL) p.decl p.d.shape raw D)
      p.decl p.d raw D U p.src p.extS p.extBS p.lsrc) :
    (p.d.shape.insts[0]'(hk0 p hp)).2.1.length = pbhPkg.ports.length :=
  callArity_of_trace L PL p h () (hk0 p hp) (hnone0 p hp) (q := pbhPkg)
    (by rw [insts0_name p hp]; exact PL_pbh)

/-! ## 5. P3: group `parent` → `cnt` (real data, decided; data only, no `cnt` package) -/

section P3
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

theorem parent_hk : 0 < parent.machineData.shape.insts.length := by
  first | decide | decide +kernel

theorem parent_fields : parent.machineData.shape.instFields ≠ [] := by
  first | decide | decide +kernel

theorem parent_hnone :
    (parent.machineData.shape.instOrigins.getD 0 Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none :=
  Option.isNone_iff_eq_none.mp (by first | rfl | decide | decide +kernel)

/-- **P3** the group row on real data (expected 1 = 1; `{dom}` is a domain binder and is filtered). -/
theorem parent_arity_row : (parent.machineData.shape.insts[0]'parent_hk).2.1.length =
    ((cnt.machineData.bsIn.take cnt.machineData.bsIn.length).filter fun b => b.2 != .domain).length := by
  first | decide | decide +kernel

end P3

/-! ## 6. Negative controls -/

/-- A module with two argument ports (no clk/rst). -/
def mc2 : Sparkle.IR.AST.Module :=
  { name := "two", inputs := [{ name := "a", ty := .bitVector 8 }, { name := "b", ty := .bitVector 8 }],
    outputs := [], wires := [], body := [] }

theorem mc2_args : (Tools.ShippingMachineCompose.argPorts mc2).length = 2 := by
  first | rfl | decide

/-- **N1** a one-argument call of a two-port module has no `CallStmt` (A2 reads the compiler's count check). -/
theorem n1_callStmt (nIn kI n k : Nat) (names : List String) (st : Sparkle.IR.AST.Stmt) :
    ¬ Tools.ShippingMachineInst.CallStmt nIn kI n names k [0] mc2 st := by
  intro h
  have h1 := callStmt_argLen h
  rw [mc2_args] at h1
  exact absurd h1 (by decide)

/-- **N1** the same for `CallStmtG` (A3). -/
theorem n1_callStmtG (nIn kI n : Nat) (names : List String) (outs : List (Nat × String))
    (st : Sparkle.IR.AST.Stmt) :
    ¬ Tools.ShippingMachineInstG.CallStmtG nIn kI n names [0] outs mc2 st := by
  intro h
  have h1 := callStmtG_argLen h
  rw [mc2_args] at h1
  exact absurd h1 (by decide)

/-- **N2** a package with a different port count is excluded: no served trace exists for `callerL`'s data. -/
theorem n2_excluded {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (P' : Pkgs Unit U) (q2 : Pkg Unit U)
    (hP' : P' ``pickByteH = some q2) (hq2 : q2.ports.length ≠ 2)
    (p : Pkg Unit U) (hp : p.d = callerL.machineData)
    {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} :
    ¬ Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P') p.decl p.d.shape raw D)
      p.decl p.d raw D U p.src p.extS p.extBS p.lsrc := by
  intro h
  have ha := callArity_of_trace L P' p h () (hk0 p hp) (hnone0 p hp) (q := q2)
    (by rw [insts0_name p hp]; exact hP')
  exact hq2 (ha.symm.trans (insts0_len p hp))

/-- **N2** instantiated with the concrete mismatched package `pbh1Pkg` (one port). -/
theorem n2_concrete {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (p : Pkg Unit U) (hp : p.d = callerL.machineData)
    {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} :
    ¬ Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L PL1) p.decl p.d.shape raw D)
      p.decl p.d raw D U p.src p.extS p.extBS p.lsrc :=
  n2_excluded L PL1 pbh1Pkg PL1_pbh1 (by rw [pbh1_ports_len]; decide) p hp

/-! ## 7. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``insts_args_eq, ``childRunN_argLen, ``callStmt_argLen, ``callStmtG_argLen, ``argLen_of_shipsRes,
      ``callArity_one, ``callArity_group, ``callArity_of_trace, ``PL_pbh, ``PL1_pbh1, ``callerL_hk,
      ``callerL_noFields, ``callerL_hnone, ``callerL_inst0, ``callerL_hP, ``callerL_args_len, ``pbh_ports_len,
      ``pbh1_ports_len, ``callerL_arity_row, ``callerL_arity, ``parent_hk, ``parent_fields, ``parent_hnone,
      ``parent_arity_row, ``n1_callStmt, ``n1_callStmtG, ``n2_excluded, ``n2_concrete] do
    checkAxioms n

#print axioms insts_args_eq
#print axioms childRunN_argLen
#print axioms callStmt_argLen
#print axioms callStmtG_argLen
#print axioms argLen_of_shipsRes
#print axioms callArity_one
#print axioms callArity_group
#print axioms callArity_of_trace
#print axioms callerL_arity_row
#print axioms callerL_arity
#print axioms parent_arity_row
#print axioms n1_callStmt
#print axioms n1_callStmtG
#print axioms n2_excluded
#print axioms n2_concrete

end Tests.Gen3.ArityCheck
