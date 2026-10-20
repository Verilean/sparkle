import Tools.ShippingSeqChildIface
import Tools.ShippingShipsDesignSVAll
import Tools.ShippingHierPremises
import Tools.ShippingMachineDepthH
import Tools.ShippingMachineShipsDepth
import Tools.ShippingMachineShipsComb

/-! # Output checks derived from a run (G1): a machine without calls

The generated endpoints take decidable checks on the emitted modules as
premises and discharge them by `decide` per declaration (`outsCheck`,
`designCheck`, `shipsHierCheck`, `shipsHierHCheck`, `kidsMixed`, `kidsMem`,
`kidsMaskedN`, `kidsComb`). Inventory: docs/parallel/G1-checks.md.

Here: what a body WITHOUT instances gives, and that the full entry's module
of a machine without calls — and its checked optimization — is such a body,
for EVERY run (not per declaration).

Pure facts (a body of assignments and registers, `body.all seqStmtOk`):
* `kidsPass_of_seqOk`, `outsCheck_of_seqOk` (every depth), `kidsMasked…`,
  `kidsMem…`, `kidsMixed…`, `kidsMaskedN…`, `kidsComb…`, `kidsLocal…`,
  `noSelfRead…`: every check that only inspects instance statements holds;
* `checkedOptimize_seqOk_all`: the checked optimizer keeps such a body such
  (its own `optCheck` / `refineCheck`, or the module unchanged);
* `hierGate_false_of_seqOk`, `shipsHierCheck_false_of_seqOk`,
  `shipsHierHCheck_false_of_seqOk`: the instance routes' bundled checks are
  FALSE on a module without instances (`hierBinds` asks an instance) — a
  machine without calls can never use the heads that ask them.

From a run (`leaf_run_seqOk`, `leaf_run_outsCheck`, `leaf_run_kids`,
`leaf_run_noHier`): a run of the full entry on a machine-route declaration
without calls, at the machine boundary, under the declaration's data — the
premises of `Tools.ShippingSeqChildIface.seqChild_iface`, which is where the
body's kinds come from.

For a module WITH instances: `kidsPass_of_insts` / `outsCheck0_of_insts`
reduce the depth-0 `outsCheck` to one fact per instance statement (it
resolves to a child that passes); where those facts come from in a run is
STATED in the note, not derived here.

What is NOT proved here
* Any conjunct that looks at assignments, registers, widths or the emitted
  text: `textCheckI`'s `seqCheck` and width agreement, `leafCheck`,
  `simpleBody b = false`, `outsAssigned` of a child after the checked merge.
* Anything for a module with instances beyond the two reductions above.
* The top-level leaf endpoint (`machine_ships_wired`) does not ask any of
  the checks proved here: they are the CHILD-side conjuncts of a parent's
  recursive checks, and the instance-free cases of the kids checks. -/
namespace Tools.ShippingChecksDerived
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Sparkle.IR.Semantics (WEnv)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize simpleBody checkedOptimize_seqOk)
open Sparkle.IR.RefineCheck (hierGate hierBinds)

/-! ## Tools -/

theorem ff_absurd {Q : Prop} (h : false = true) : Q := by
  cases h

theorem and_false_left (a b : Bool) (h : a = false) : (a && b) = false := by
  subst h
  rfl

/-- On a body of assignments and registers, a per-statement check that
accepts assignments and registers holds of the body. -/
theorem all_of_seqOk {body : List Stmt} (h : body.all seqStmtOk = true) (g : Stmt → Bool)
    (hg : ∀ st, seqStmtOk st = true → g st = true) : body.all g = true :=
  List.all_eq_true.mpr fun st hst => hg st (List.all_eq_true.mp h st hst)

/-- On such a body, a per-statement test that refuses assignments and
registers finds nothing. -/
theorem any_false_of_seqOk {body : List Stmt} (h : body.all seqStmtOk = true)
    (p : Stmt → Bool) (hp : ∀ st, seqStmtOk st = true → p st = false) : body.any p = false :=
  List.any_eq_false.mpr fun st hst hpt => by
    have := hp st (List.all_eq_true.mp h st hst)
    rw [this] at hpt
    cases hpt

/-! ## Checks that only inspect instance statements -/

theorem kidsPass_of_seqOk {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {f : Sparkle.IR.AST.Module → Bool}
    {body : List Stmt} (h : body.all seqStmtOk = true) :
    Tools.ShippingDesignSV.kidsPass C f body = true :=
  all_of_seqOk h _ fun st hs => by
    cases st <;> first | rfl | exact ff_absurd hs

/-- `outsCheck`, at every depth, on a module without instances. -/
theorem outsCheck_of_seqOk {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {o : Sparkle.IR.AST.Module}
    (h : o.body.all seqStmtOk = true) :
    ∀ n, Tools.ShippingDesignSVBack.outsCheck C n o = true
  | 0 => kidsPass_of_seqOk h
  | _ + 1 => kidsPass_of_seqOk h

theorem kidsMasked_of_seqOk {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {body : List Stmt}
    (h : body.all seqStmtOk = true) : Tools.ShippingMachineShipsHier.kidsMasked C body = true :=
  all_of_seqOk h _ fun st hs => by
    cases st <;> first | rfl | exact ff_absurd hs

theorem kidsMem_of_seqOk {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {body : List Stmt}
    (h : body.all seqStmtOk = true) : Tools.ShippingMachineShipsHier.kidsMem C body = true :=
  all_of_seqOk h _ fun st hs => by
    cases st <;> first | rfl | exact ff_absurd hs

theorem kidsMixed_of_seqOk {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {body : List Stmt}
    (h : body.all seqStmtOk = true) : Tools.ShippingMachineShipsHier.kidsMixed C body = true :=
  all_of_seqOk h _ fun st hs => by
    cases st <;> first | rfl | exact ff_absurd hs

theorem kidsMaskedN_of_seqOk {ms : List Sparkle.IR.AST.Module} {body : List Stmt}
    (h : body.all seqStmtOk = true) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN ms body = true :=
  all_of_seqOk h _ fun st hs => by
    cases st <;> first | rfl | exact ff_absurd hs

theorem kidsComb_of_seqOk {ms : List Sparkle.IR.AST.Module} {body : List Stmt}
    (h : body.all seqStmtOk = true) : Tools.ShippingMachineDepthH.kidsComb ms body = true :=
  all_of_seqOk h _ fun st hs => by
    cases st <;> first | rfl | exact ff_absurd hs

theorem kidsLocal_of_seqOk {ms : List Sparkle.IR.AST.Module} {body : List Stmt}
    (h : body.all seqStmtOk = true) : Tools.ShippingHierOptRunH.kidsLocal ms body = true :=
  all_of_seqOk h _ fun st hs => by
    cases st <;> first | rfl | exact ff_absurd hs

theorem noSelfRead_of_seqOk {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {body : List Stmt}
    (h : body.all seqStmtOk = true) :
    Tools.ShippingHierPremisesBase.noSelfRead C body = true :=
  all_of_seqOk h _ fun st hs => by
    cases st <;> first | rfl | exact ff_absurd hs

/-! ## The checked optimizer keeps the statement kinds -/

/-- **The checked optimization of an assignments-and-registers body is one.**
Whatever the optimizer does: its output is kept only under `optCheck` (a
simple body) or `refineCheck`, else the module is returned unchanged. -/
theorem checkedOptimize_seqOk_all {m : Sparkle.IR.AST.Module} (h : m.body.all seqStmtOk = true) :
    (checkedOptimize m).body.all seqStmtOk = true := by
  cases hs : simpleBody m with
  | true =>
    have ha := Tools.ShippingMachineShipsComb.checkedOptimize_assigns hs
    exact List.all_eq_true.mpr fun st hst => by
      have hst' := List.all_eq_true.mp ha st hst
      cases st <;> first | rfl | exact ff_absurd hst'
  | false =>
    rcases checkedOptimize_seqOk hs h with hrc | heq
    · exact Tools.ShippingMachineShipping.refineCheck_stmtOk_o hrc
    · rw [heq]
      exact h

/-! ## The instance routes' bundled checks are false without an instance -/

theorem hierGate_false_of_seqOk {m : Sparkle.IR.AST.Module} (h : m.body.all seqStmtOk = true) :
    hierGate m = false :=
  and_false_left _ _ (any_false_of_seqOk h _ fun st hs => by
    cases st <;> first | rfl | exact ff_absurd hs)

theorem hierBinds_false_of_seqOk {m : Sparkle.IR.AST.Module} (h : m.body.all seqStmtOk = true) :
    hierBinds m = false :=
  and_false_left _ _ (hierGate_false_of_seqOk h)

theorem hierCheck_false_of_seqOk {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {b : Sparkle.IR.AST.Module}
    (h : b.body.all seqStmtOk = true) : Tools.ShippingHierPremisesBase.hierCheck C b = false :=
  and_false_left _ _ (and_false_left _ _ (and_false_left _ _ (and_false_left _ _
    (and_false_left _ _ (and_false_left _ _ (hierBinds_false_of_seqOk h))))))

/-- `shipsHierCheck` is false on a module without instances. -/
theorem shipsHierCheck_false_of_seqOk {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {b : Sparkle.IR.AST.Module}
    (h : b.body.all seqStmtOk = true) :
    Tools.ShippingHierPremisesBase.shipsHierCheck C b = false :=
  and_false_left _ _ (hierCheck_false_of_seqOk h)

/-- `shipsHierHCheck` is false on a module without instances. -/
theorem shipsHierHCheck_false_of_seqOk {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (h : b.body.all seqStmtOk = true) :
    Tools.ShippingHierPremises.shipsHierHCheck ms b = false :=
  and_false_left _ _ (and_false_left _ _ (hierCheck_false_of_seqOk h))

/-! ## A module with instances: one fact per instance statement -/

/-- `kidsPass` from the instances: each resolves to a child that passes. -/
theorem kidsPass_of_insts {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {f : Sparkle.IR.AST.Module → Bool}
    {body : List Stmt}
    (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
      ∃ child cwe, C mn = some (child, cwe) ∧ f child = true) :
    Tools.ShippingDesignSV.kidsPass C f body = true := by
  unfold Tools.ShippingDesignSV.kidsPass
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    obtain ⟨child, cwe, hc, hf⟩ := h mn iname conns hst
    simp only [hc]
    exact hf
  | _ => rfl

/-- **The depth-0 `outsCheck` of a module with instances**, from: every
instance statement of the module resolves to a child whose outputs are
assigned or read from a combinational memory (`outsLeaf`). -/
theorem outsCheck0_of_insts {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {o : Sparkle.IR.AST.Module}
    (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body →
      ∃ child cwe, C mn = some (child, cwe) ∧ Tools.ShippingDesignSV.outsLeaf child = true) :
    Tools.ShippingDesignSVBack.outsCheck C 0 o = true :=
  kidsPass_of_insts h

/-! ## From a run: a machine without calls -/

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **Every run of the full entry on a machine without calls returns a
module of assignments and registers, and so is its checked optimization;
the design is empty.** -/
theorem leaf_run_seqOk {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    b.body.all seqStmtOk = true ∧ (checkedOptimize b).body.all seqStmtOk = true ∧
      design.modules = [] :=
  have hI := Tools.ShippingSeqChildIface.seqChild_iface d ok hbody hno outTy hw hr entry closesM
  ⟨hI.seqOk, checkedOptimize_seqOk_all hI.seqOk, hI.design⟩

/-- **`outsCheck` of every run's module of a machine without calls**, at
every depth and for every child map: of the entry's module (what a parent's
recursive check asks of this child) and of its checked optimization. -/
theorem leaf_run_outsCheck {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape)
    (C : String → Option (Sparkle.IR.AST.Module × WEnv)) (n : Nat) :
    Tools.ShippingDesignSVBack.outsCheck C n b = true ∧
      Tools.ShippingDesignSVBack.outsCheck C n (checkedOptimize b) = true :=
  have hs := leaf_run_seqOk d ok hbody hno outTy hw hr entry closesM
  ⟨outsCheck_of_seqOk hs.1 n, outsCheck_of_seqOk hs.2.1 n⟩

/-- **The kids checks of every run's module of a machine without calls.** -/
theorem leaf_run_kids {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape)
    (C : String → Option (Sparkle.IR.AST.Module × WEnv)) (ms : List Sparkle.IR.AST.Module) :
    Tools.ShippingMachineShipsHier.kidsMixed C (checkedOptimize b).body = true ∧
      Tools.ShippingMachineShipsHier.kidsMem C (checkedOptimize b).body = true ∧
      Tools.ShippingMachineShipsDepth.kidsMaskedN ms (checkedOptimize b).body = true ∧
      Tools.ShippingMachineDepthH.kidsComb ms (checkedOptimize b).body = true :=
  have hs := (leaf_run_seqOk d ok hbody hno outTy hw hr entry closesM).2.1
  ⟨kidsMixed_of_seqOk hs, kidsMem_of_seqOk hs, kidsMaskedN_of_seqOk hs, kidsComb_of_seqOk hs⟩

/-- **A machine without calls never passes the instance routes' bundled
checks**: on every run's module `shipsHierCheck` and `shipsHierHCheck` are
`false`. -/
theorem leaf_run_noHier {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape)
    (C : String → Option (Sparkle.IR.AST.Module × WEnv)) (ms : List Sparkle.IR.AST.Module) :
    Tools.ShippingHierPremisesBase.shipsHierCheck C b = false ∧
      Tools.ShippingHierPremises.shipsHierHCheck ms b = false :=
  have hs := (leaf_run_seqOk d ok hbody hno outTy hw hr entry closesM).1
  ⟨shipsHierCheck_false_of_seqOk hs, shipsHierHCheck_false_of_seqOk hs⟩

end Tools.ShippingChecksDerived
