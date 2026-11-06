import Tools.ShippingFGCircuitS2lDec
set_option autoImplicit false
-- FG circuit pilot S2l check (light). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §38.

/-! # FGCircuitPilotCheck32 (light)

1. SIGNATURES: `hftCallDec_of_readers`, `hftCallDec_of_checked`, `callDec_of_oneOutCall` against independently written complete statements; mutants: swapped callee readers, wrong call index, another root, a dropped reader, a fixed callee.
2. CONTROLS (kernel): the static data checks for the swapped callee and the wrong call index are `false`.
3. HYPS: the premises of `hftCallDec_of_readers` are the three readers only; nothing run-related is reachable from the statement.
4. REMAINING, AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck32
open Lean Meta Elab Command Term
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain
open Tools.ShippingGen2 Tools.ShippingFGCircuit Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitS1kStmt
open Tools.ShippingFGCircuitS2jTop Tools.ShippingFGCircuitS2lDec Tools.ShippingFGCircuitS1kRoot
open Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitRoots Tools.ShippingGen5Sem Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntryReadsLinked (envAt)
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

/-! ## 1. complete expected statements -/

def ExpDec {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment) : Prop :=
  ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftRoot = some p →
    ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, GPt (ι := ι) lvl env (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k

def ExpReaders : Prop :=
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    RootReader lvl env hftRoot synth_hftPcieOutByte.machineData →
    RootReader lvl env hftHttp httpGetByte.machineData →
    RootReader lvl env hftTlp tlpCplByte.machineData → ExpDec (ι := ι) lvl env
/-- mutant: the two callees' readers swapped (the data of the other child) -/
def MuSwap : Prop :=
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    RootReader lvl env hftRoot synth_hftPcieOutByte.machineData →
    RootReader lvl env hftHttp tlpCplByte.machineData →
    RootReader lvl env hftTlp httpGetByte.machineData → ExpDec (ι := ι) lvl env
/-- mutant: another root (the second child asked for as the root) -/
def MuOtherRoot : Prop :=
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    RootReader lvl env hftTlp tlpCplByte.machineData →
    RootReader lvl env hftHttp httpGetByte.machineData →
    RootReader lvl env hftTlp tlpCplByte.machineData →
    (∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftTlp = some p →
      ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, GPt (ι := ι) lvl env (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
/-- mutant: a reader dropped -/
def MuNoT : Prop :=
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    RootReader lvl env hftRoot synth_hftPcieOutByte.machineData →
    RootReader lvl env hftHttp httpGetByte.machineData → ExpDec (ι := ι) lvl env
/-- mutant: the decoding of call 0 for every call -/
def MuIdx0 : Prop :=
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    RootReader lvl env hftRoot synth_hftPcieOutByte.machineData →
    RootReader lvl env hftHttp httpGetByte.machineData →
    RootReader lvl env hftTlp tlpCplByte.machineData →
    (∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftRoot = some p →
      ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, GPt (ι := ι) lvl env (p.d.shape.insts[k]).1 = some q ∧ CallDec p q 0)
/-- mutant: one fixed callee for every call -/
def MuFixed : Prop :=
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    RootReader lvl env hftRoot synth_hftPcieOutByte.machineData →
    RootReader lvl env hftHttp httpGetByte.machineData →
    RootReader lvl env hftTlp tlpCplByte.machineData →
    (∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl env hftRoot = some p →
      ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ q, GPt (ι := ι) lvl env hftHttp = some q ∧ CallDec p q k)

def ExpChecked : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (lvl : Lean.Expr → Nat) (env₀ : Environment) {w : Void IO.RealWorld},
    CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData →
    (∃ ci : ConstantInfo, (envAt cref w).find? hftRoot = some ci) →
    RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData → ExpDec (ι := ι) lvl (envAt cref w)
/-- mutant: the declaration found is not the root's -/
def MuCheckedFind : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (lvl : Lean.Expr → Nat) (env₀ : Environment) {w : Void IO.RealWorld},
    CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData →
    (∃ ci : ConstantInfo, (envAt cref w).find? hftHttp = some ci) →
    RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData → ExpDec (ι := ι) lvl (envAt cref w)
/-- mutant: the end world's environment for the decoding -/
def MuCheckedEnd : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (lvl : Lean.Expr → Nat) (env₀ : Environment) {w w' : Void IO.RealWorld},
    CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData →
    (∃ ci : ConstantInfo, (envAt cref w).find? hftRoot = some ci) →
    RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData →
    RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData → ExpDec (ι := ι) lvl (envAt cref w')

def ExpOneOutCall : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length),
    P (p.d.shape.insts[k]'hk).1 = some q → (p.d.shape.instOrigins.getD k .ord).child? = none →
    GenExtAtCall p q k hk → p.d.shape.instFields = [] →
    p.d.callsOk p.kD = true → p.d.ss.length = p.d.shape.layout.slots.length →
    callArgsOkAt p.d p.kD k q.portWidths = true → (p.d.shape.insts[k]'hk).2.1.length = q.ports.length →
    (∃ o, q.d.shape.layout.outs = [o]) → (∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width) →
    (∀ o, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some o.ty.bitWidth) →
    CallDec p q k
/-- mutant: the range row dropped (the callee's output widths) -/
def MuOneOutNoTy : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length),
    P (p.d.shape.insts[k]'hk).1 = some q → (p.d.shape.instOrigins.getD k .ord).child? = none →
    GenExtAtCall p q k hk → p.d.shape.instFields = [] →
    p.d.callsOk p.kD = true → p.d.ss.length = p.d.shape.layout.slots.length →
    callArgsOkAt p.d p.kD k q.portWidths = true → (p.d.shape.insts[k]'hk).2.1.length = q.ports.length →
    (∃ o, q.d.shape.layout.outs = [o]) →
    (∀ o, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some o.ty.bitWidth) →
    CallDec p q k
/-- mutant: the callee package is the call's own parent (`p.decl`) -/
def MuOneOutParent : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length),
    P p.decl = some q → (p.d.shape.instOrigins.getD k .ord).child? = none →
    GenExtAtCall p q k hk → p.d.shape.instFields = [] →
    p.d.callsOk p.kD = true → p.d.ss.length = p.d.shape.layout.slots.length →
    callArgsOkAt p.d p.kD k q.portWidths = true → (p.d.shape.insts[k]'hk).2.1.length = q.ports.length →
    (∃ o, q.d.shape.layout.outs = [o]) → (∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width) →
    (∀ o, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some o.ty.bitWidth) →
    CallDec p q k

/-! ## comparison helpers -/

def normOnce (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if c == ``HftCallDec || (`Tests.Gen5.FGCircuitPilotCheck32).isPrefixOf c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:6] do
    e ← normOnce e
  return e
def sameTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  unless ← withDefault (isDefEq a e) do throwError "{what}: type is NOT the expected statement"
def diffTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  if a == e then throwError "{what}: the MUTANT is the same expression"
  if ← withReducible (isDefEq a e) then throwError "{what}: the MUTANT was accepted"
def tyOf (n : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo n
  unless ci.levelParams.isEmpty do throwError "{n}: level parameters"
  pure ci.type

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let Q := `Tests.Gen5.FGCircuitPilotCheck32
  let S := `Tools.ShippingFGCircuitS2lDec
  let C (n : Name) : Lean.Expr := mkConst n
  let mut nm : Nat := 0
  let t1 ← tyOf (S ++ `hftCallDec_of_readers)
  sameTy "hftCallDec_of_readers" t1 (C (Q ++ `ExpReaders))
  for mu in ["MuSwap", "MuOtherRoot", "MuNoT", "MuIdx0", "MuFixed"] do
    diffTy s!"hftCallDec_of_readers vs {mu}" t1 (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  let t2 ← tyOf (S ++ `hftCallDec_of_checked)
  sameTy "hftCallDec_of_checked" t2 (C (Q ++ `ExpChecked))
  for mu in ["MuCheckedFind", "MuCheckedEnd"] do
    diffTy s!"hftCallDec_of_checked vs {mu}" t2 (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  let t3 ← tyOf (S ++ `callDec_of_oneOutCall)
  sameTy "callDec_of_oneOutCall" t3 (C (Q ++ `ExpOneOutCall))
  for mu in ["MuOneOutNoTy", "MuOneOutParent"] do
    diffTy s!"callDec_of_oneOutCall vs {mu}" t3 (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT32 SIGNATURES: hftCallDec_of_readers (premises: the root's, http's and tlp's RootReader at the table's env; conclusion HftCallDec), hftCallDec_of_checked (root reader from CheckedStart + the root found) and callDec_of_oneOutCall (GenExtAtCall + static data + the callee's single output and its widths) match independently written complete statements; {nm} mutants rejected (swapped callee readers, another root, a reader dropped, call index 0, a fixed callee; the found declaration, the end world's environment; range row dropped, the callee package being the parent's)"

/-! ## 2. kernel controls: the static data of the swapped callee and of the wrong call index are false -/

theorem ctl_swap0 : callArgsOkAt synth_hftPcieOutByte.machineData 5 0 (dataPW tlpCplByte.machineData (kDOf tlpCplByte.machineData)) = false := by decide +kernel
theorem ctl_swap1 : callArgsOkAt synth_hftPcieOutByte.machineData 5 1 (dataPW httpGetByte.machineData (kDOf httpGetByte.machineData)) = false := by decide +kernel
theorem ctl_ok0 : callArgsOkAt synth_hftPcieOutByte.machineData 5 0 (dataPW httpGetByte.machineData (kDOf httpGetByte.machineData)) = true := hft_args0
theorem ctl_ok1 : callArgsOkAt synth_hftPcieOutByte.machineData 5 1 (dataPW tlpCplByte.machineData (kDOf tlpCplByte.machineData)) = true := hft_args1

run_cmd liftTermElabM do
  logInfo m!"FGCIRCUIT32 CONTROLS: kernel: callArgsOkAt of the root at call 0 with the tlp callee's ports is false, at call 1 with http's ports is false (swapped callees / wrong call index are rejected by the static check); the right pairs are true"

/-! ## 3. HYPS -/

partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        if (`Tools).isPrefixOf n || (`Sparkle).isPrefixOf n then reach env (d.value.getUsedConstants.toList ++ d.type.getUsedConstants.toList ++ rest) seen
        else reach env rest seen
      | some (.inductInfo i) => if (`Tools).isPrefixOf n then reach env (i.ctors ++ rest) seen else reach env rest seen
      | some (.ctorInfo c) => reach env (c.type.getUsedConstants.toList ++ rest) seen
      | _ => reach env rest seen

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let t ← tyOf ``Tools.ShippingFGCircuitS2lDec.hftCallDec_of_readers
  let hs ← forallTelescope t fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, ← instantiateMVars d.type)]
    return hs
  let expected := ["lvl", "env", "hreadR", "hreadH", "hreadT"]
  unless hs.map (·.1) == expected do throwError "hypotheses are {hs.map (·.1)}, expected {expected}"
  let env ← getEnv
  let mut tot : Nat := 0
  for (_, ty) in hs do
    let r := reach env ty.getUsedConstants.toList {}
    tot := tot + r.size
    for bad in [``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingGen2.Start,
        ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingGen5Env.ReadsAt, ``Tools.ShippingFGCircuitS1iEnv.CheckedStart,
        ``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingGen2.ShipsRes, ``Tools.ShippingGen2.ChildShips, ``Tools.ShippingGen2.TopShips] do
      if r.contains bad then throwError "{bad} is reachable from a premise of hftCallDec_of_readers"
  let r := reach env [``HftCallDec] {}
  for bad in [``Tools.ShippingEntrySoundness.RunsTo, ``Tools.ShippingGen2.ShipsRes, ``Tools.ShippingGen2.TopShips, ``Tools.ShippingGen2.Start] do
    if r.contains bad then throwError "{bad} is reachable from HftCallDec"
  logInfo m!"FGCIRCUIT32 HYPS: hftCallDec_of_readers has exactly the explicit premises {expected} (the three RootReaders at the table's environment); no run / world / Start / MachineDefines / ShipsRes / TopShips is reachable from a premise or from HftCallDec (reach {tot}, {r.size})"

/-! ## 4. REMAINING, AXIOMS -/

run_cmd liftTermElabM do
  logInfo m!"FGCIRCUIT32 REMAINING (S2l): HftCallDec is PROVED from the three RootReaders (FG D.D-4 G-CALLDEC): GenExtAtCall by hDT1_of_genGP at the table GPt (guard hord by kernel), CallOutRange by callOutRange_of_widths (Pkg.src_range + the callee's o.ty.bitWidth = o.width + the binder width, kernel), T2-FIELD by callField_one (the callee has one output, kernel; no run needed), the static data by kernel (callsOk, ss/slots, callArgsOkAt, port count). Hypotheses left for hdec: RootReader of the root (hchk + the root found in the start environment, hftCallDec_of_checked), RootReader of http (hreadH) and tlp (hreadT), nothing else. No FG row is added by S2l"

run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitS2lDec
  let names : List Name := [S ++ `callDec_of_oneOutCall, S ++ `hft_callsOk, S ++ `hft_slotsLen, S ++ `hft_args0, S ++ `hft_args1, S ++ `hft_len0', S ++ `hft_len1',
    S ++ `http_outTy, S ++ `tlp_outTy, S ++ `hftCallDec_of_readers, S ++ `hftCallDec_of_checked, `Tests.Gen5.FGCircuitPilotCheck32.ctl_swap0, `Tests.Gen5.FGCircuitPilotCheck32.ctl_swap1]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT32 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck32
