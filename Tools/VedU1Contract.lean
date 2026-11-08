import Sparkle.IR.Semantics
import Sparkle.IR.RegDedup
import Sparkle.Core.Signal

/-!
# U1 contract for the checked `#verify_elab_deep` entry (SKETCH, P1-4)

Reviewer change request 2026-11-08, P1-4.  Definitions only: no entry, no
generator, no proof of `OutputsStmt` yet.  Nothing here imports
`Tools.DeepElab`.  Design: docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md §4.

The U1 entry calls `synthesizeEntry declName` ONCE, registers the returned
module `m` as a constant `f_u1_mod` and a contract `c` as `f_u1_contract`
(both by `toExpr`, synchronously), and must prove

  `U1Stmt f_u1_contract f_u1_mod (fun ins o t => SRC)`

where `SRC` is built SYNTACTICALLY from the original declaration: the
constant `declName` applied to the parameter values and to one input signal
per data input port (`sigBV`/`sigB` of the stream), observed with
`obsBV`/`obsB` and projected to the output port `o` (`toySrc` below is the
shape).  The source is therefore NOT a free argument of the final statement:
the entry checks that the registered theorem's type is Expr-equal to the
statement it builds from `declName`, the params and these two constants, and
that `f_u1_mod`'s value is `toExpr m` of the same run (identity of the
verified and the returned module).

What each part pins:
* `ShapeStmt` = `ShapeCore` ∧ v1 scope.  `ShapeCore`: every Module field the
  meaning reads (name, parameters, assertions, primitive flag, inputs in
  order, outputs, wires, the register list with initial values) is the
  contract's; every register's clock and reset NAME is the module's
  clock/reset input (`clkRst`).  v1 scope: memory-free and instance-free
  (memories and child instances are later units; `pilotB0` has two child
  instances and is outside v1, while its `ShapeCore` and `WidthStmt` hold).
* `WidthStmt`: `declWidth` reads `m.wires` ONLY.  So the contract requires a
  wire declaration (with the port's scalar width) for every DATA input and
  every register output, and deliberately NOT for the clock, the reset or the
  output ports: the real artifact `pilotB0`
  (Tools/ShippingFGCircuitS3rArtifact.lean) has no wire for `clk`, `rst` or
  `out`, and the first draft (`WidthStmtDraft1`: every input, output and wire
  through `declWidth`) rejects it (Tests/Ved/U1ContractCheck.lean).
* `InputsOk`: data inputs fit `declWidth`; reset AND clock are held 0.  The
  IR semantics never reads the clock's value (one `stepModule` per cycle), so
  fixing it to 0 loses no behaviour; it matches the `hinsFit` premise of
  `seqOptCheck_run_sound` (which bounds every input by `declWidth`, i.e.
  `clk`/`rst` by `2^0`), the intended next connection (`checkedOptimize`).
* `st0`: the initial register state is each register's `encodeInit` of its
  contract init at its declared width (the Signal side starts registers at
  their init, `Signal.register` at time 0); memories start at 0.
* `seedFwd`: `runModule` passes the cycle index COUNTING DOWN (first cycle
  gets `k-1`, Sparkle/IR/Semantics.lean `runModule`).  `seedFwd m K ins`
  re-indexes, so trace position `t` (oldest first) reads `ins t`
  (`seedFwd_time`); the first draft fed `seedIn m ins` directly and compared
  `envs[t]` with time `t`, i.e. with the stream reversed.
-/

namespace Tools.VedU1Contract

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- `declWidth` (Sparkle/IR/RegDedup.lean): the width of a name's WIRE
declaration, `0` when the name has none. -/
abbrev declWidth : Module → String → Nat := Sparkle.IR.RegDedup.declWidth

/-- Fixed by the entry from the ONE `synthesizeEntry` result. -/
structure Contract where
  modName    : String
  /-- `(clock input, reset input)`; `none` for a module without registers -/
  clkRst     : Option (String × String)
  /-- data inputs in port order; the i-th feeds the declaration's i-th
  explicit Signal parameter in the expected statement -/
  dataInputs : List Port
  outputs    : List Port
  wires      : List Port
  /-- register output ↦ initial value, in body order -/
  inits      : List (String × Int)
  deriving Repr, DecidableEq

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

def clkRstPorts (c : Contract) : List Port :=
  match c.clkRst with
  | some (k, r) => [⟨k, .bit⟩, ⟨r, .bit⟩]
  | none => []

/-- Every Module field the meaning reads is the contract's (scope-free part). -/
def ShapeCore (c : Contract) (m : Module) : Prop :=
  m.name = c.modName ∧ m.parameters = [] ∧ m.assertions = [] ∧ m.isPrimitive = false ∧
  m.inputs = c.dataInputs ++ clkRstPorts c ∧
  m.outputs = c.outputs ∧ m.wires = c.wires ∧
  (regsOf m.body).map (fun r => (r.1, r.2.2.2)) = c.inits ∧
  (∀ r ∈ regsOf m.body, c.clkRst = some (r.2.1, r.2.2.1))

instance (c : Contract) (m : Module) : Decidable (ShapeCore c m) := by
  unfold ShapeCore; infer_instance

/-- The v1 shape: the core plus the v1 scope (no memories, no child
instances; `pilotB0` has two instances, so it is outside v1 — a scope
limit, not a width or naming rejection). -/
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

/-- The FIRST draft's width clause (kept only to show that it over-rejects:
`clk`, `rst` and the output ports have no wire declaration, so `declWidth`
is `0` for them). -/
def WidthStmtDraft1 (m : Module) : Prop :=
  ∀ p ∈ m.inputs ++ m.outputs ++ m.wires, declWidth m p.name = p.ty.bitWidth

instance (m : Module) : Decidable (WidthStmtDraft1 m) := by
  unfold WidthStmtDraft1; infer_instance

/-- Input streams the contract covers. -/
def InputsOk (c : Contract) (m : Module) (ins : Nat → String → Nat) : Prop :=
  (∀ t, ∀ p ∈ c.dataInputs, ins t p.name < 2 ^ declWidth m p.name) ∧
  (∀ t kr, c.clkRst = some kr → ins t kr.1 = 0 ∧ ins t kr.2 = 0)

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

/-- Time direction: `runModule … (k+1)` seeds its first cycle with index `k`;
in a `K`-cycle run, trace position `t` is seeded with index `K-1-t`, which
`seedFwd` maps back to stream time `t`. -/
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

/-- Every output port, at every cycle of every run of `m.body` ITSELF from
`st0`, equals the source's value. -/
def OutputsStmt (c : Contract) (m : Module)
    (src : (Nat → String → Nat) → String → Nat → Nat) : Prop :=
  ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
    runModule (declWidth m) m.body (seedFwd m K ins) K (st0 c m) (fun _ _ => 0) = some envs ∧
    ∀ t, t < K → ∀ o ∈ c.outputs, ∃ env, envs[t]? = some env ∧ env o.name = src ins o.name t

/-- The statement the U1 entry registers (with `src` built from the
declaration, never supplied by the caller). -/
def U1Stmt (c : Contract) (m : Module)
    (src : (Nat → String → Nat) → String → Nat → Nat) : Prop :=
  ShapeStmt c m ∧ WidthStmt c m ∧ OutputsStmt c m src

/-! ## Input signals and observations used to BUILD `src` from a declaration -/

def sigBV (ins : Nat → String → Nat) (p : String) (w : Nat) : Signal defaultDomain (BitVec w) :=
  ⟨fun t => BitVec.ofNat w (ins t p)⟩

def sigB (ins : Nat → String → Nat) (p : String) : Signal defaultDomain Bool :=
  ⟨fun t => ins t p != 0⟩

def obsBV {w : Nat} (s : Signal defaultDomain (BitVec w)) (t : Nat) : Nat := (s.val t).toNat

def obsB (s : Signal defaultDomain Bool) (t : Nat) : Nat := if s.val t then 1 else 0

/-- The contract the entry would compute from a module (the contract
constant is then a closed literal; another module with a different field
fails `ShapeStmt` against it). -/
def contractOf (m : Module) (clkRst : Option (String × String)) : Contract :=
  { modName := m.name, clkRst,
    dataInputs := m.inputs.filter (fun p => match clkRst with
      | some (k, r) => p.name != k && p.name != r
      | none => true),
    outputs := m.outputs, wires := m.wires,
    inits := (regsOf m.body).map (fun r => (r.1, r.2.2.2)) }

end Tools.VedU1Contract
