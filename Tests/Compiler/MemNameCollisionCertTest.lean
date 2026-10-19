import Sparkle
import Tools.ShippingMachineCommand
import Tools.ShippingMemClosesKidsT
import Tools.ShippingModuleName

/-! # Certificate: the closing of a memory parent beside a COLLIDING declaration call (round par/o-kidt)

TARGET-ONLY (not in `Tests.AllTests`): it declares (or imports) its own `SparkleMem.sync.4.8`
(the leaf register `fakeReg`), a different function from `MemNameCollisionTest`'s declaration under
the same GLOBAL placeholder name; the two cannot be imported together (`environment already
contains`). See `MemNameCollisionGenTest` for the build command.

`Tests/Compiler/MemNameCollisionTest.lean` checks that the patched compiler
compiles a parent with a memory AND a call of a `@[hardware_module]`
declared (by metaprogramming) under the memory's placeholder name
`MachMemory.memChildName false 4 8`: two call entries (one of origin
`.mem false 4 8`, one of origin `.ord`), two instances. The name-based
memory-parent closing `Tools.ShippingMemCloses.machineClosesAt_of_kidsDM`
cannot state that: it asks `TagsAgree` (FALSE here, `collSame_not_agree`,
`collArgs_not_agree`), and its name separation identifies the two entries.

This file states, kernel-checked, `MachineClosesAt` of two such parents by the
ORIGIN-based closing `Tools.ShippingMemCloses.machineClosesAt_of_kidsDMT`
(`Tools/ShippingMemClosesKidsT.lean`): no `TagsAgree`, no name half of
`hnomem`. The only premise is the reflection (`MachineDefines`) of the
colliding declaration.

## The declarations (why not `fakeSrc`)

`MemNameCollisionTest` collides a COMBINATIONAL declaration (`fakeSrc`,
`wd + 1`). A combinational (gate-route) child directly under the general
closing has no derived interface in the repository
(`Tools/ShippingChildIfaceGen.lean` 147: "a gate child … directly under the
general closing (not derived)"; `#machine_no_ports_memseq` refuses a slotless
or gate child). The colliding declaration here is therefore a LEAF REGISTER
machine with the memory's interface, `fakeReg` (a `circuit do`, as `cnt`;
interface from `seqChild_of_real`), copied under `memChildName false 4 8`
exactly as `MemNameCollisionTest` copies `fakeSrc` (`copyAs`, `renameIn`):

* `collSameR` — synchronous memory 4/8 at `(wa, wd, we, ra)` and the colliding
  call at the SAME arguments (the case the unpatched reader merged);
* `collArgsR` — the same memory and the colliding call at `(wa, wd, we, wa)`.

## Data

`collSameD`, `collArgsD`, `fakeD`: the reader's data
(`Tools.ShippingMachineCommand.readMachine` / `dataE`, as `#machine_endpoint`
adds `f.machineData`), under ordinary names (the declaration's own name has
numeric components, which identifiers cannot spell). `…_ok`, `…_body`: the
endpoint's two data checks, by `Eq.refl` checked by the kernel only (as
`#machine_endpoint` adds `f.machine_ok` / `f.machine_body`). `#machine_endpoint`
itself (the trace theorem) is NOT run: the closing does not need it.

BUILT and RUN (par/o-kidt; integrator fixes: missing import Tools.ShippingModuleName, addRefl via mkTheoremValEx, `(nomatch hx)` parenthesised, `intro tenv`; run kt4 exit 0, peak 0.29 GB; axioms of collSame_closes / collArgs_closes / closes_of_collision / collSame_not_agree: [propext, Classical.choice, Quot.sound]). Data READ: the sources below. NOT READ
(logged by the first `run_cmd`, asserted where the proofs depend on it): the
entry order, `nDecl` (asserted 4), the entries' names and origins (asserted:
two entries, both named `memChildName false 4 8`, one `.mem false 4 8`, one
`.ord`), `instFields`, the output names. -/
namespace Sparkle.Tests.Compiler.MemNameCollisionCertTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- A leaf register machine with the memory's interface. -/
@[hardware_module] def fakeReg {dom : DomainConfig} (wa : Signal dom (BitVec 4))
    (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) (ra : Signal dom (BitVec 4)) :
    Signal dom (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux we (Signal.mux (wa === ra) (cs ^^^ wd) (cs + wd)) cs
    return cs

/-- A synchronous memory and `fakeReg` on the SAME arguments. -/
def mixSameR (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (ra : Signal defaultDomain (BitVec 4)) (wd : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let r1 := Signal.memory wa wd we ra
    let r2 := fakeReg wa wd we ra
    r <~ (r1 ^^^ r2) + rs
    return rs

/-- A synchronous memory and `fakeReg` on other arguments. -/
def mixArgsR (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (ra : Signal defaultDomain (BitVec 4)) (wd : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let r1 := Signal.memory wa wd we ra
    let r2 := fakeReg wa wd we wa
    r <~ (r1 ^^^ r2) + rs
    return rs

/-- `src` copied under `nm`, tagged `@[hardware_module]` (as `MemNameCollisionTest.copyAs`). -/
def copyAs (src nm : Name) : CoreM Unit := do
  let ci ← getConstInfo src
  addDecl (Declaration.defnDecl (mkDefinitionValEx nm [] ci.type ci.value! .abbrev .safe [nm]))
  Sparkle.Compiler.hardwareModuleAttr.setTag nm

/-- `par` with `src` replaced by `nm`, declared as `out` (as `MemNameCollisionTest.renameIn`). -/
def renameIn (par src nm out : Name) : CoreM Unit := do
  let ci ← getConstInfo par
  let v := ci.value!.replace fun e => if e.isConstOf src then some (.const nm []) else none
  addDecl (Declaration.defnDecl (mkDefinitionValEx out [] ci.type v .abbrev .safe [out]))

/-- The synchronous 4/8 memory's placeholder name. -/
def syncName : Name := Sparkle.Compiler.MachMemory.memChildName false 4 8

def ns : Name := `Sparkle.Tests.Compiler.MemNameCollisionCertTest

run_cmd liftCoreM do
  copyAs ``fakeReg syncName
  renameIn ``mixSameR ``fakeReg syncName (ns ++ `collSameR)
  renameIn ``mixArgsR ``fakeReg syncName (ns ++ `collArgsR)

/-- `name : stmt` with the proof `Eq.refl lhs`, checked by the kernel only. -/
def addRefl (name : Name) (stx : Lean.Term) : TermElabM Unit := do
  let stmt ← Term.elabTerm stx (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let stmt ← instantiateMVars stmt
  if stmt.hasMVar then throwError "{name}: the statement has metavariables"
  let some (α, lhs, _) := stmt.eq? | throwError "{name}: not an equation: {stmt}"
  let u ← getLevel α
  withOptions (fun o => Lean.Elab.async.set o false) do
    addDecl (.thmDecl (mkTheoremValEx name [] stmt (mkApp2 (mkConst ``Eq.refl [u]) α lhs) [name]))

/-- The reader's data of `src`, as `base`. -/
def addData (src base : Name) : TermElabM Unit := do
  let r ← Tools.ShippingMachineCommand.readMachine src
  Tools.ShippingMachineCommand.addDef base (mkConst ``Tools.ShippingMachineAuto.MachineData)
    (← Tools.ShippingMachineCommand.dataE r)

/-! ## The data: LOGGED, then asserted -/

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let fake ← Tools.ShippingMachineCommand.readMachine syncName
  Lean.logInfo m!"COLLCERT DATA {syncName} (fakeReg): nDecl={fake.nDecl}, binders={fake.shape.binders.length}, slots={fake.shape.layout.slots.length}, lets={fake.shape.layout.lets}, call entries {fake.shape.insts.map (·.1)}, outputs {fake.shape.layout.outs.map (·.name)}"
  unless fake.shape.insts.isEmpty do throwError "{syncName}: not a leaf (entries {fake.shape.insts.map (·.1)})"
  for p in [ns ++ `collSameR, ns ++ `collArgsR] do
    let rf ← Tools.ShippingMachineCommand.readMachine p
    let tagged := rf.shape.instTagged
    Lean.logInfo m!"COLLCERT DATA {p}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, call entries {rf.shape.insts.map (·.1)}, origins {repr rf.shape.instOrigins}, argument lets {rf.shape.insts.map (·.2.1)}, instFields={rf.shape.instFields}, slots={rf.shape.layout.slots.length}, lets={rf.shape.layout.lets}, outputs {rf.shape.layout.outs.map (·.name)}"
    unless rf.nDecl == 4 do throwError "{p}: nDecl = {rf.nDecl}, the theorems below are written for 4"
    unless tagged.length == 2 do throwError "{p}: {tagged.length} call entries, expected 2 (the memory and the colliding call)"
    unless tagged.all (fun x => x.1 == syncName) do
      throwError "{p}: an entry not named {syncName}: {tagged.map (·.1)}"
    unless tagged.any (fun x => x.2 == .mem false 4 8) && tagged.any (fun x => x.2 == .ord) do
      throwError "{p}: the origins are {repr (tagged.map (·.2))}, expected one .mem false 4 8 and one .ord"
    unless tagged.any (fun x => !Tools.ShippingInstTagged.tagAgrees x.1 x.2) do
      throwError "{p}: TagsAgree holds — not a collision shape"
  let rs ← Tools.ShippingMachineCommand.readMachine (ns ++ `collSameR)
  let ra ← Tools.ShippingMachineCommand.readMachine (ns ++ `collArgsR)
  unless (rs.shape.insts.map (·.2.1)).eraseDups.length == 1 do
    throwError "collSameR: the two entries' argument lets differ: {rs.shape.insts.map (·.2.1)}"
  unless (ra.shape.insts.map (·.2.1)).eraseDups.length == 2 do
    throwError "collArgsR: the two entries' argument lets agree: {ra.shape.insts.map (·.2.1)}"
  addData syncName (ns ++ `fakeD)
  addData (ns ++ `collSameR) (ns ++ `collSameD)
  addData (ns ++ `collArgsR) (ns ++ `collArgsD)

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  addRefl (ns ++ `fake_ok) (← `(Tools.ShippingMachineAuto.MachineData.ok fakeD = true))
  addRefl (ns ++ `fake_body) (← `(fakeD.shape.body = Tools.ShippingUnifiedSource.quote fakeD.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr fakeD.shape.binders.length (fakeD.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr fakeD.shape.binders.length (fakeD.vpos j))
      fakeD.packed))
  addRefl (ns ++ `collSame_ok) (← `(Tools.ShippingMachineAuto.MachineData.ok collSameD = true))
  addRefl (ns ++ `collSame_body) (← `(collSameD.shape.body = Tools.ShippingUnifiedSource.quote collSameD.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collSameD.shape.binders.length (collSameD.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collSameD.shape.binders.length (collSameD.vpos j))
      collSameD.packed))
  addRefl (ns ++ `collArgs_ok) (← `(Tools.ShippingMachineAuto.MachineData.ok collArgsD = true))
  addRefl (ns ++ `collArgs_body) (← `(collArgsD.shape.body = Tools.ShippingUnifiedSource.quote collArgsD.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collArgsD.shape.binders.length (collArgsD.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr collArgsD.shape.binders.length (collArgsD.vpos j))
      collArgsD.packed))

/-! ## The old (name-based) closing does not apply: `TagsAgree` is false -/

theorem collSame_not_agree : ¬ Tools.ShippingInstTagged.TagsAgree collSameD.shape := by
  first | decide | decide +kernel

theorem collArgs_not_agree : ¬ Tools.ShippingInstTagged.TagsAgree collArgsD.shape := by
  first | decide | decide +kernel

/-! ## The colliding declaration's child: a leaf register machine -/

open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Compiler.MachMemory (memModule)
open Tools.ShippingInstTagged (KidT originAt)
open Tools.ShippingMemCloses (ChildIfaceP)

theorem fake_leaf : fakeD.shape.insts = [] := rfl

theorem fake_outTy : ∀ o ∈ fakeD.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

/-- `fakeReg` (under the placeholder name) closes in every world: no call, and
the data's `let` check (`closes_of_data`) or no `let` (`machineCloses_of_noLets`). -/
theorem fake_closes (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State)
    (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State) :
    Tools.ShippingMachineEntry.MachineCloses mctx mref cctx cref syncName fakeD.shape := by
  first
    | exact Tools.ShippingMachineClosesData.closes_of_data fakeD fake_ok fake_body
        (by first | decide | decide +kernel) mctx mref cctx cref
    | exact Tools.ShippingMachineEntry.machineCloses_of_noLets
        (by first | rfl | decide) (by first | rfl | decide)

/-- `fakeReg`'s number of argument ports (`seqChild_of_real`'s form). -/
noncomputable def fakeNk : Nat :=
  ((fakeD.shape.binders.take (fakeD.shape.binders.length - fakeD.shape.layout.slots.length -
    fakeD.shape.layout.lets)).filter fun x => x.2 != .domain).length

/-- **A real child of the colliding declaration has the interface** (from its
reflection; its closing is `fake_closes`). -/
theorem fake_iface {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape)
    {y : Tools.ShippingChildInv.Res} (hy : Tools.ShippingChildInv.RealChild mref cref syncName y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl syncName) fakeNk
      (fakeD.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
  have hG := Tools.ShippingSeqChildIface.seqChild_of_real fakeD fake_ok fake_body fake_leaf
    fake_outTy hRc (fun mc cc => fake_closes mc _ cc _) hy
  exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG)
    (fun hx => nomatch hx)

/-! ## The per-entry tables, keyed by the entry's ORIGIN (both entries carry one name) -/

/-- The child module's name. -/
def nameO : InstOrigin → String
  | .mem cb aw dw => (memModule cb aw dw).1.name
  | .ord => Sparkle.IR.ModuleName.ofDecl syncName
  | .field _ => Sparkle.IR.ModuleName.ofDecl syncName

/-- The child's number of argument ports. -/
noncomputable def nkO : InstOrigin → Nat
  | .mem _ _ _ => 4
  | .ord => fakeNk
  | .field _ => fakeNk

/-- The child's output names. -/
noncomputable def outsO : InstOrigin → List String
  | .mem _ _ _ => ["out"]
  | .ord => fakeD.shape.layout.outs.map (·.name)
  | .field _ => fakeD.shape.layout.outs.map (·.name)

/-- The module names of the child's design. -/
def namesO : InstOrigin → List String
  | .mem cb aw dw => [(memModule cb aw dw).1.name]
  | .ord => []
  | .field _ => []

theorem memName_eq : (memModule false 4 8).1.name = Sparkle.IR.ModuleName.ofMem false 4 8 := rfl

/-- No declaration's module is named as the built memory module. -/
theorem decl_ne_mem (c : Name) : Sparkle.IR.ModuleName.ofDecl c ≠ (memModule false 4 8).1.name :=
  fun e => Tools.ShippingModuleName.ofDecl_ne_ofMem c false 4 8 (e.trans memName_eq)

theorem decl_notin_mem (c : Name) :
    Sparkle.IR.ModuleName.ofDecl c ∉ [(memModule false 4 8).1.name] :=
  fun h => decl_ne_mem c (List.mem_singleton.mp h)

/-! ## The closing of a collision parent, from decided data and the colliding declaration's reflection -/

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt` of a parent whose call entries are a synchronous 4/8
memory and calls of the declaration carrying that memory's placeholder name**
— by the origin-based closing, from the reflection of that declaration only.
The data conditions are premises here, decided per parent below. -/
theorem closes_of_collision {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {declName : Name}
    (d : Tools.ShippingMachineAuto.MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j))
      d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (hent : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).1 = syncName ∧
        (originAt d.shape k = .mem false 4 8 ∨ originAt d.shape k = .ord))
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nkO (originAt d.shape k) = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsO (originAt d.shape k))
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      Tools.ShippingMemCloses.memKey (originAt d.shape k) =
        Tools.ShippingMemCloses.memKey (originAt d.shape k') →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (houtHead : ∀ o ∈ d.shape.layout.outs, o.name.toList.head? ≠ some 'i')
    (hpar : Sparkle.IR.ModuleName.ofDecl syncName ≠ Sparkle.IR.ModuleName.ofDecl declName)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref declName d.shape := by
  have hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      KidT mref cref (originAt d.shape k) (d.shape.insts[k]).1 y →
      ChildIfaceP (nameO (originAt d.shape k)) (nkO (originAt d.shape k))
        (outsO (originAt d.shape k)) (namesO (originAt d.shape k)) y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    rcases ho with ho | ho
    · rw [ho] at hy ⊢
      exact Tools.ShippingMemCloses.memKidT_iface (Tools.ShippingInstTagged.child?_mem false 4 8) hy
    · rw [ho] at hy ⊢
      have hre := Tools.ShippingInstTagged.KidT.real hy rfl
      rw [hn] at hre
      exact fake_iface hRc hre
  have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), nameO (originAt d.shape k) = nameO (originAt d.shape k') →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        Tools.ShippingMemCloses.memKey (originAt d.shape k) =
          Tools.ShippingMemCloses.memKey (originAt d.shape k') := by
    intro k hk k' hk' he
    obtain ⟨hn, ho⟩ := hent k hk
    obtain ⟨hn', ho'⟩ := hent k' hk'
    refine ⟨hn.trans hn'.symm, ?_⟩
    rcases ho with ho | ho <;> rcases ho' with ho' | ho'
    · rw [ho, ho']
    · rw [ho, ho'] at he
      exact absurd he.symm (decl_ne_mem syncName)
    · rw [ho, ho'] at he
      exact absurd he (decl_ne_mem syncName)
    · rw [ho, ho']
  have hparent : ∀ (k : Nat), k < d.shape.insts.length →
      nameO (originAt d.shape k) ≠ Sparkle.IR.ModuleName.ofDecl declName := by
    intro k hk
    rcases (hent k hk).2 with ho | ho
    · rw [ho]
      exact fun e => decl_ne_mem declName e.symm
    · rw [ho]
      exact hpar
  have hparentD : ∀ (k : Nat), k < d.shape.insts.length →
      Sparkle.IR.ModuleName.ofDecl declName ∉ namesO (originAt d.shape k) := by
    intro k hk
    rcases (hent k hk).2 with ho | ho
    · rw [ho]
      exact decl_notin_mem declName
    · rw [ho]
      show Sparkle.IR.ModuleName.ofDecl declName ∉ ([] : List String)
      exact fun hx => nomatch hx
  have hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length),
      ¬ ((d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        Tools.ShippingMemCloses.memKey (originAt d.shape k) =
          Tools.ShippingMemCloses.memKey (originAt d.shape k')) →
      nameO (originAt d.shape k) ∉ namesO (originAt d.shape k') ∧
        ∀ x ∈ namesO (originAt d.shape k), x ∉ namesO (originAt d.shape k') := by
    intro k hk k' hk' hne
    obtain ⟨hn, ho⟩ := hent k hk
    obtain ⟨hn', ho'⟩ := hent k' hk'
    rcases ho with ho | ho <;> rcases ho' with ho' | ho'
    · exact (hne ⟨hn.trans hn'.symm, by rw [ho, ho']⟩).elim
    · rw [ho, ho']
      show (memModule false 4 8).1.name ∉ ([] : List String) ∧
        ∀ x ∈ [(memModule false 4 8).1.name], x ∉ ([] : List String)
      exact ⟨fun hx => (nomatch hx), fun _ _ hx => nomatch hx⟩
    · rw [ho, ho']
      show Sparkle.IR.ModuleName.ofDecl syncName ∉ [(memModule false 4 8).1.name] ∧
        ∀ x ∈ ([] : List String), x ∉ [(memModule false 4 8).1.name]
      exact ⟨decl_notin_mem syncName, fun _ hx => nomatch hx⟩
    · exact (hne ⟨hn.trans hn'.symm, by rw [ho, ho']⟩).elim
  intro tenv
  exact Tools.ShippingMemCloses.machineClosesAt_of_kidsDMT d ok hbody halias hC hslots hdomB hfne
    (fun k => nameO (originAt d.shape k)) (fun k => nkO (originAt d.shape k))
    (fun k => outsO (originAt d.shape k)) (fun k => namesO (originAt d.shape k))
    hkid hargsN hfieldOut hfieldsNd hsep hparent
    (fun gi _ _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (houtHead o ho) gi _)
    hparentD hdisjD

/-! ## The two collision parents -/

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt collSameR`**: a synchronous 4/8 memory and the call of
the declaration named `SparkleMem.sync.4.8` on the SAME argument `let`s —
two calls (origins `.mem false 4 8` / `.ord`), closed from the declaration's
reflection only; no `TagsAgree` (false: `collSame_not_agree`). -/
theorem collSame_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collSameR collSameD.shape :=
  closes_of_collision (declName := ``collSameR) (nDecl := 4) collSameD collSame_ok collSame_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel)) hRc

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt collArgsR`**: the same memory and the colliding call on
OTHER argument `let`s; no `TagsAgree` (false: `collArgs_not_agree`). -/
theorem collArgs_closes {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref syncName fakeD.shape) :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``collArgsR collArgsD.shape :=
  closes_of_collision (declName := ``collArgsR) (nDecl := 4) collArgsD collArgs_ok collArgs_body
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (Tools.ShippingModuleName.ofDecl_ne (by first | decide | decide +kernel)) hRc

#print axioms Tools.ShippingMemCloses.machineClosesAt_of_kidsDMT
#print axioms Tools.ShippingMemCloses.machineClosesAt_of_kidsDM_fromT
#print axioms closes_of_collision
#print axioms collSame_closes
#print axioms collArgs_closes
#print axioms collSame_not_agree

end Sparkle.Tests.Compiler.MemNameCollisionCertTest
