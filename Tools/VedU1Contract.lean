import Lean
import Sparkle.IR.Semantics
import Sparkle.IR.ReorderInvariance
import Tools.VedIRDecEq
import Sparkle.Core.Signal

/-!
# U1 contract for the checked `#verify_elab_deep` entry (rev 3)

Reviewer change requests 2026-11-08: P1-4 (rev 2), then P1-A / P1-B (this
revision).  Definitions, the declaration-side table reader, and small lemmas.
The first instance (`toyDelay`, a hand-written module) is proved in
`Tests/Ved/U1ContractCheck.lean`; the minimal end-to-end entry slice (one
`synthesizeCombinational` call, the full statement over the returned module and the
original constant, kernel, strict audit) is `Tools/VedU1Entry.lean`.  Nothing
here imports `Tools.DeepElab`.
Design: docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md §4, §9 and §10.

## P1-A: the declaration side fixes the port correspondence

The contract no longer takes its data inputs and outputs from the returned
module.  It carries a `DeclTable` read from the ORIGINAL declaration's TYPE
(`ved_table% decl`, below):

* `ins`: one entry per explicit binder, in binder order, each
  `Signal defaultDomain Bool` (`.bit`) or `Signal defaultDomain (BitVec w)`
  (`.bv w`); `binders` are the binder names;
* `out`: the result `Signal defaultDomain T` with `T` a tree of `Bool`,
  `BitVec w` and `×`; `OTy.flat` flattens it left-first (`(a × b) × c` gives
  `a, b, c`), which is the FIXED order of the output projections.

`DeclTable.Ty tbl` is the Lean type the table denotes.  The final statement
`U1Stmt c m f` takes the declaration itself as `f : c.table.Ty`, so it only
typechecks when the declaration's type is (definitionally) the table's: the
kernel checks the table against the declaration, and the source
(`srcOf c f`) is built from `f`, not supplied.

`CorrStmt` (arity of names vs table, coverage of every output projection,
injectivity of all port names, separation from clk/rst, positive widths) and
`ShapeCore` (module inputs = the table's ports in order with their widths,
then clk, rst; module outputs = ALL projections in order with their widths)
reject another declaration's table, merged inputs, a missing output and a
width mismatch (kernel-checked controls in the Check).

## P1-B: the clock is free

`InputsOk` bounds the data inputs and holds the RESET at 0 (scope: runs
without reset, stated); it does NOT constrain the clock input: its value at
every cycle is universally quantified.  (The previous revision fixed it to 0
and claimed the IR semantics never reads the clock; that is false in general:
`evalExpr (.ref clk)` reads the environment's clock value, and assignments or
register inputs may reference it.  With the clock free, nothing about clock
reads needs to be assumed.)  The optimiser connection (`seqOptCheck_run_sound`
has `hinsFit`, which bounds `clk` by `2^declWidth clk = 1`) will need its own
bridge at that unit; the IR guarantee is not narrowed to fit it.

## Other parts (unchanged from rev 2)

* `ShapeStmt` = `ShapeCore` ∧ v1 scope (no memories, no instances).
* `WidthStmt`: `declWidth` reads `m.wires` ONLY; a wire declaration is
  required for every data input and every register output, not for clk, rst
  or output ports (the real artifact `pilotB0` has none for them).
* `st0`: each register at `encodeInit` of its init; memories at 0.
* `seedFwd`: `runModule` passes the cycle index counting down; `seedFwd`
  re-indexes so trace position `t` reads stream time `t` (`seedFwd_time`).

## Order-free meaning (rev 4, user decision 2026-11-09)

`OutputsStmt` quantifies over every arrangement of `m.body` that assigns each
wire before reading it (`WO [] b`), and `OrderStmt` requires one to exist and
the body to be a well-formed netlist (no self-read, no undriven read, unique
update names).  `main`'s compiler emits `circuit do` bodies with a read before
the assignment; as continuous assignments (and in the printed Verilog) the
order is irrelevant, but the one-pass `evalAssigns` is not.  The returned
module itself is never reordered.  `outputs_body` recovers the in-order
statement over `m.body` when that order is already well-ordered.

What is NOT here (honest status): the entry is `Tools/VedU1Entry.lean` (a
minimal slice: one output; register-free or one-register-delay bodies; see
§10 of the design doc).  The general proof generator, multi-output naming,
memories, instances and declarations with non-Signal parameters are open.
-/

namespace Tools.VedU1Contract

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- The width of a name's WIRE declaration (`bit` is one bit), `0` when the
name has none or another type.  The width function the statements give the
IR semantics. -/
def declWidth (m : Module) (x : String) : Nat :=
  match m.wires.find? (fun p => p.name == x) with
  | some { ty := .bitVector k, .. } => k
  | some { ty := .bit, .. } => 1
  | _ => 0

/-! ## The declaration-side table -/

/-- A scalar port type as written in the declaration's type. -/
inductive PTy
  | bit
  | bv (w : Nat)
  deriving Repr, DecidableEq, Lean.ToExpr

/-- The Lean value type of a port. -/
def PTy.val : PTy → Type
  | .bit => Bool
  | .bv w => BitVec w

def PTy.hw : PTy → HWType
  | .bit => .bit
  | .bv w => .bitVector w

def PTy.width : PTy → Nat
  | .bit => 1
  | .bv w => w

/-- Observation of a port value as a natural number. -/
def PTy.obs : (p : PTy) → p.val → Nat
  | .bit, b => Bool.toNat (show Bool from b)
  | .bv _, v => v.toNat

/-- The input signal a port's stream denotes. -/
def PTy.sig : (p : PTy) → (Nat → String → Nat) → String → Signal defaultDomain p.val
  | .bit, ins, n => ⟨fun t => ins t n != 0⟩
  | .bv w, ins, n => ⟨fun t => BitVec.ofNat w (ins t n)⟩

/-- The declaration's result value type: a `×`-tree of scalar ports. -/
inductive OTy
  | leaf (p : PTy)
  | pair (a b : OTy)
  deriving Repr, DecidableEq, Lean.ToExpr

def OTy.val : OTy → Type
  | .leaf p => p.val
  | .pair a b => a.val × b.val

/-- The output projections in their fixed order (left-first). -/
def OTy.flat : OTy → List PTy
  | .leaf p => [p]
  | .pair a b => a.flat ++ b.flat

/-- Observations of every projection, in `flat` order. -/
def OTy.obs : (o : OTy) → o.val → List Nat
  | .leaf p, v => [p.obs v]
  | .pair a b, v => a.obs v.1 ++ b.obs v.2

/-- The correspondence table read from the declaration's type. -/
structure DeclTable where
  /-- explicit binder names, in order -/
  binders : List String
  /-- binder port types, in order -/
  ins : List PTy
  out : OTy
  deriving Repr, DecidableEq, Lean.ToExpr

/-- Curried function type over the input ports. -/
def InTy : List PTy → Type → Type
  | [], R => R
  | p :: ps, R => Signal defaultDomain p.val → InTy ps R

/-- The Lean type the table denotes. -/
def DeclTable.Ty (d : DeclTable) : Type := InTy d.ins (Signal defaultDomain d.out.val)

/-- Apply a declaration to one input signal per port (named by `ns`). -/
def applyIns {R : Type} : (ps : List PTy) → List String → (Nat → String → Nat) → InTy ps R → R
  | [], _, _, f => f
  | p :: ps, ns, ins, f => applyIns ps ns.tail ins (f (p.sig ins (ns.headD "")))

section Reader
open Lean Meta Elab Term

/-- Read a scalar value type (`Bool` or `BitVec w` with a numeral width). -/
def readPTy (ty : Lean.Expr) : MetaM PTy := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``Bool, #[]) => pure .bit
  | (``BitVec, #[w]) =>
    match ← evalNat (← instantiateMVars w) with
    | some n => pure (.bv n)
    | none => throwError "ved_table%: non-literal BitVec width {w}"
  | _ => throwError "ved_table%: unsupported port type {ty} (v1: Bool or BitVec w)"

/-- Read the result value type (a `×`-tree of scalars). -/
partial def readOTy (ty : Lean.Expr) : MetaM OTy := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``Prod, #[a, b]) => return .pair (← readOTy a) (← readOTy b)
  | _ => return .leaf (← readPTy ty)

/-- `Signal defaultDomain α` ↦ `α`, otherwise an error. -/
def signalArg (ty : Lean.Expr) : MetaM Lean.Expr := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``Sparkle.Core.Signal.Signal, #[dom, a]) =>
    unless dom.isConstOf ``Sparkle.Core.Domain.defaultDomain do
      throwError "ved_table%: signal domain {dom} is not defaultDomain"
    pure a
  | _ => throwError "ved_table%: {ty} is not a Signal defaultDomain _ (v1: Signal binders only)"

/-- The table of a declaration, read from its type only. -/
def readTable (decl : Name) : MetaM DeclTable := do
  let some ci := (← getEnv).find? decl | throwError "ved_table%: unknown {decl}"
  unless ci.levelParams.isEmpty do throwError "ved_table%: {decl} is universe polymorphic"
  forallTelescopeReducing ci.type fun xs res => do
    let mut bs : List String := []
    let mut ps : List PTy := []
    for x in xs do
      let ld ← x.fvarId!.getDecl
      unless ld.binderInfo.isExplicit do
        throwError "ved_table%: {decl} has a non-explicit binder {ld.userName}"
      bs := bs ++ [ld.userName.toString]
      ps := ps ++ [← readPTy (← signalArg ld.type)]
    return { binders := bs, ins := ps, out := ← readOTy (← signalArg res) }

/-- `ved_table% decl`: the `DeclTable` literal of `decl`, read from its type. -/
elab "ved_table% " id:ident : term => do
  let decl ← realizeGlobalConstNoOverloadWithInfo id
  return toExpr (← readTable decl)

end Reader

/-! ## The contract -/

/-- Fixed by the entry: the table from the declaration, the port names, and
the module fields the meaning reads. -/
structure Contract where
  modName  : String
  /-- `(clock input, reset input)`; `none` for a module without registers -/
  clkRst   : Option (String × String)
  table    : DeclTable
  /-- the i-th input binder ↦ module input port name -/
  inNames  : List String
  /-- the j-th output projection (`table.out.flat` order) ↦ output port name -/
  outNames : List String
  wires    : List Port
  /-- register output ↦ initial value, in body order -/
  inits    : List (String × Int)
  deriving Repr, DecidableEq

/-- Data input ports built from the TABLE (order and widths are the table's). -/
def Contract.dataInputs (c : Contract) : List Port :=
  (c.inNames.zip c.table.ins).map fun (n, p) => ⟨n, p.hw⟩

/-- Output ports built from the TABLE (every projection, in order). -/
def Contract.outputs (c : Contract) : List Port :=
  (c.outNames.zip c.table.out.flat).map fun (n, p) => ⟨n, p.hw⟩

def clkRstNames (c : Contract) : List String :=
  match c.clkRst with
  | some (k, r) => [k, r]
  | none => []

def clkRstPorts (c : Contract) : List Port :=
  match c.clkRst with
  | some (k, r) => [⟨k, .bit⟩, ⟨r, .bit⟩]
  | none => []

/-- The declaration/contract correspondence: arity (names vs table: the
`zip`s above would otherwise truncate silently), coverage of every output
projection, injectivity of all port names (no two inputs share a stream, no
input doubles as an output), separation from clk/rst, positive widths. -/
def CorrStmt (c : Contract) : Prop :=
  c.table.binders.length = c.table.ins.length ∧
  c.inNames.length = c.table.ins.length ∧
  c.outNames.length = c.table.out.flat.length ∧
  (c.inNames ++ c.outNames ++ clkRstNames c).Nodup ∧
  (∀ p ∈ c.table.ins ++ c.table.out.flat, 0 < p.width)

instance (c : Contract) : Decidable (CorrStmt c) := by
  unfold CorrStmt; infer_instance

/-- Registers of a body: (output, clock, reset name, init). -/
def regsOf : List Stmt → List (String × String × String × Int)
  | [] => []
  | .register o c (r, _) _ i :: rest => (o, c, r, i) :: regsOf rest
  | _ :: rest => regsOf rest

/-- v1 scope: no memories, no instances. -/
def memInstFree : List Stmt → Bool
  | [] => true
  | .memory .. :: _ => false
  | .inst .. :: _ => false
  | _ :: rest => memInstFree rest

/-- Every Module field the meaning reads is the contract's; inputs and
outputs are compared with the TABLE's ports (order, widths, all outputs). -/
def ShapeCore (c : Contract) (m : Module) : Prop :=
  m.name = c.modName ∧ m.parameters = [] ∧ m.assertions = [] ∧ m.isPrimitive = false ∧
  m.inputs = c.dataInputs ++ clkRstPorts c ∧
  m.outputs = c.outputs ∧ m.wires = c.wires ∧
  (regsOf m.body).map (fun r => (r.1, r.2.2.2)) = c.inits ∧
  (∀ r ∈ regsOf m.body, c.clkRst = some (r.2.1, r.2.2.1))

instance (c : Contract) (m : Module) : Decidable (ShapeCore c m) := by
  unfold ShapeCore; infer_instance

/-- The v1 shape: the core plus the v1 scope. -/
def ShapeStmt (c : Contract) (m : Module) : Prop :=
  ShapeCore c m ∧ memInstFree m.body = true

instance (c : Contract) (m : Module) : Decidable (ShapeStmt c m) := by
  unfold ShapeStmt; infer_instance

/-- A scalar port type of positive width. -/
def scalar : HWType → Bool
  | .bit => true
  | .bitVector w => 0 < w
  | _ => false

/-- Widths, reading `declWidth` (wires only) where the semantics reads it. -/
def WidthStmt (c : Contract) (m : Module) : Prop :=
  (m.wires.map (·.name)).Nodup ∧
  (∀ p ∈ c.dataInputs, scalar p.ty = true ∧ declWidth m p.name = p.ty.bitWidth) ∧
  (∀ p ∈ c.outputs, scalar p.ty = true) ∧
  (∀ r ∈ regsOf m.body, ∃ p ∈ m.wires, p.name = r.1 ∧ scalar p.ty = true)

instance (c : Contract) (m : Module) : Decidable (WidthStmt c m) := by
  unfold WidthStmt; infer_instance

/-- The FIRST draft's width clause (kept only to show that it over-rejects). -/
def WidthStmtDraft1 (m : Module) : Prop :=
  ∀ p ∈ m.inputs ++ m.outputs ++ m.wires, declWidth m p.name = p.ty.bitWidth

instance (m : Module) : Decidable (WidthStmtDraft1 m) := by
  unfold WidthStmtDraft1; infer_instance

/-- Input streams the contract covers: data inputs fit their declared width,
the reset is held 0 (scope: reset-free runs).  The CLOCK is unconstrained. -/
def InputsOk (c : Contract) (m : Module) (ins : Nat → String → Nat) : Prop :=
  (∀ t, ∀ p ∈ c.dataInputs, ins t p.name < 2 ^ declWidth m p.name) ∧
  (∀ t kr, c.clkRst = some kr → ins t kr.2 = 0)

/-- Initial register state. -/
def st0 (c : Contract) (m : Module) : String → Nat := fun n =>
  match c.inits.lookup n with
  | some i => encodeInit i (declWidth m n)
  | none => 0

/-- `seedIn` of Tools/ShippingSeqOptSoundness.lean (restated to avoid the
import): inputs from the stream at the GIVEN index, the rest from the state. -/
def seedIn (m : Module) (ins : Nat → String → Nat) : Nat → (String → Nat) → Env :=
  fun t st n => if (m.inputs.map (·.name)).contains n then ins t n else st n

/-- Seeding for a `K`-cycle run in wall-clock order. -/
def seedFwd (m : Module) (K : Nat) (ins : Nat → String → Nat) : Nat → (String → Nat) → Env :=
  fun j st n => if (m.inputs.map (·.name)).contains n then ins (K - 1 - j) n else st n

/-- Time direction: in a `K`-cycle run, trace position `t` is seeded with
index `K-1-t`, which `seedFwd` maps back to stream time `t`. -/
theorem seedFwd_time (m : Module) (K : Nat) (ins : Nat → String → Nat) {t : Nat}
    (ht : t < K) (st : String → Nat) :
    seedFwd m K ins (K - 1 - t) st = seedIn m ins t st := by
  funext n
  have h : K - 1 - (K - 1 - t) = t := by omega
  simp only [seedFwd, seedIn, h]

/-- The trace's first (oldest) environment is the one seeded with `K-1`. -/
theorem runModule_first (we : WEnv) (body : List Stmt) (seed : Nat → (String → Nat) → Env)
    (k : Nat) (st : String → Nat) (mems : MEnv) :
    runModule we body seed (k + 1) st mems =
      (do let (envF, nexts, mems') ← stepModule we body (seed k st) mems
          let rest ← runModule we body seed k (applyNexts st nexts) mems'
          some (envF :: rest)) := rfl

/-- The source built from the DECLARATION `f`: apply it to one input signal
per table port, observe every output projection, and read port `o`'s. -/
def srcOf (c : Contract) (f : c.table.Ty) : (Nat → String → Nat) → String → Nat → Nat :=
  fun ins o t =>
    ((c.outNames.zip (c.table.out.obs ((applyIns c.table.ins c.inNames ins f).val t))).lookup o).getD 0

/-- Every output port (all projections), at every cycle of every run of the
statement list `b` from `st0`, equals the declaration's value.  `m` supplies
the widths and the input names; `b` is an arrangement of `m.body`. -/
def OutputsOn (c : Contract) (m : Module) (b : List Stmt) (f : c.table.Ty) : Prop :=
  ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
    runModule (declWidth m) b (seedFwd m K ins) K (st0 c m) (fun _ _ => 0) = some envs ∧
    ∀ t, t < K → ∀ o ∈ c.outputs, ∃ env, envs[t]? = some env ∧ env o.name = srcOf c f ins o.name t

/-! ## Order-free meaning (user decision 2026-11-09, option D)

A module body is a list of continuous assignments, registers and memories:
as a circuit its statement ORDER carries no meaning.  `evalAssigns` folds the
list once, top to bottom, so a wire read before its assignment sees the seed
value.  The statement therefore speaks about every arrangement in which each
wire is assigned before it is read (`WO [] b`, `Sparkle.IR.Reorder`), and
`runModule_perm` makes all of them agree.  The returned module is NOT
reordered; only the meaning is order-free.  `OrderStmt` says such an
arrangement exists (else the statement would be vacuous) and rules out what has
no order-free meaning:

* a combinational cycle (no well-ordered arrangement exists);
* an assignment that reads its own target (`WO` alone allows it: the read
  sees the seed);
* a read of a name that is neither a module input, a register output nor
  assigned in the body (an undriven net);
* two register updates of one name, two memories of one name (the
  `runModule_perm` side conditions);
* an output port with no driver (PR #148 review P1: the seed would show it as
  a constant 0), an assignment to a module input, and a name both assigned
  and a register output.

Netlist well-formedness here means exactly these conditions, for the v1 scope
(no memories, no instances): every output is a register output or assigned,
every read is an input, a register output or assigned, each driven name has
ONE driver (an assignment or a register, never both, never an input), and the
combinational part is acyclic.  It is an IR contract (the seed default never
stands in for a missing driver), not a statement about the printed Verilog. -/

open Sparkle.IR.Reorder in
/-- Names a statement reads, register inputs included (combinational reads
are `stmtReads`). -/
def allReads : Stmt → List String
  | .register _ _ _ e _ => refsOf e
  | s => stmtReads s

open Sparkle.IR.Reorder in
/-- The decidable side of `OrderStmt` for one arrangement `b` of `m.body`. -/
def OrderOk (m : Module) (b : List Stmt) : Bool :=
  isPermOf b m.body && woCheck [] b &&
  decide (nextKeys b).Nodup && decide (b.filterMap stmtMemName).Nodup &&
  b.all (fun s => (stmtReads s).all (fun n => !(stmtWrites s).contains n)) &&
  b.all (fun s => (allReads s).all (fun n =>
    (m.inputs.map (·.name)).contains n || ((regsOf b).map (·.1)).contains n ||
      (writesOf b).contains n)) &&
  m.outputs.all (fun p => ((regsOf b).map (·.1)).contains p.name || (writesOf b).contains p.name) &&
  (writesOf b).all (fun n => !(m.inputs.map (·.name)).contains n && !((regsOf b).map (·.1)).contains n) &&
  ((regsOf b).map (·.1)).all (fun n => !(m.inputs.map (·.name)).contains n)

/-- Some arrangement of the body assigns every wire before reading it, and the
body is a well-formed netlist in the sense above. -/
def OrderStmt (m : Module) : Prop := ∃ b, OrderOk m b = true

/-- The order-free output statement: EVERY well-ordered arrangement of the
module's statements produces the declaration's outputs. -/
def OutputsStmt (c : Contract) (m : Module) (f : c.table.Ty) : Prop :=
  ∀ b, b.Perm m.body → Sparkle.IR.Reorder.WO [] b → OutputsOn c m b f

open Sparkle.IR.Reorder in
/-- One checked arrangement is enough: `runModule_perm` carries its outputs to
every other well-ordered arrangement. -/
theorem outputs_of_order {c : Contract} {m : Module} {f : c.table.Ty} (b0 : List Stmt)
    (h : OrderOk m b0 = true) (hout : OutputsOn c m b0 f) : OutputsStmt c m f := by
  simp only [OrderOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp, hwo⟩, hk⟩, hmem⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  intro b hb hwob ins hok K
  obtain ⟨envs, hrun, hall⟩ := hout ins hok K
  refine ⟨envs, ?_, hall⟩
  rw [← runModule_perm (declWidth m) ((isPermOf_sound hp).trans hb.symm)
    (woCheck_sound _ _ hwo) hwob hmem hk]
  exact hrun

open Sparkle.IR.Reorder in
/-- When the module's own order is already well-ordered, the statement is the
in-order one over `m.body` itself. -/
theorem outputs_body {c : Contract} {m : Module} {f : c.table.Ty}
    (h : OutputsStmt c m f) (hwo : woCheck [] m.body = true) : OutputsOn c m m.body f :=
  h m.body (List.Perm.refl _) (woCheck_sound _ _ hwo)

/-- The statement the U1 entry registers.  `f` is the declaration constant;
it typechecks only at the table's type. -/
def U1Stmt (c : Contract) (m : Module) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeStmt c m ∧ WidthStmt c m ∧ OrderStmt m ∧ OutputsStmt c m f

/-- The data input ports of a module: everything except clk/rst. -/
def dataPortsOf (m : Module) (clkRst : Option (String × String)) : List Port :=
  m.inputs.filter (fun p => match clkRst with
    | some (k, r) => p.name != k && p.name != r
    | none => true)

/-- The contract the entry computes.  The TABLE (arity, order, widths, output
projections) comes from the declaration; input port names follow the
synthesizer's naming rule `_gen_<binder>` (observed on the toy and on
`pilotB0`; a different rule makes `ShapeCore` reject, never accept);
`outNames` are given per output projection.  Name, wires and register
inits are read from `m`: they are not part of the declaration's type.  A
mismatch in them is rejected because `OutputsStmt` cannot be proved WHEN it
affects the output meaning; a mismatch that does not affect the observed
outputs (an unused register, say) need not be rejected (reviewer wording,
2026-11-08).  The module name is likewise read from `m` and is not bound to
the declaration's name. -/
def contractOf (tbl : DeclTable) (outNames : List String)
    (clkRst : Option (String × String)) (m : Module) : Contract :=
  { modName := m.name, clkRst, table := tbl,
    inNames := tbl.binders.map ("_gen_" ++ ·), outNames,
    wires := m.wires,
    inits := (regsOf m.body).map (fun r => (r.1, r.2.2.2)) }

end Tools.VedU1Contract
