import Tests.Compiler.ShippingMachineLinkedTest
import Tests.Compiler.ShippingMachineInstTest
import Tools.ShippingMachineShipsDepth
set_option autoImplicit false

/-! # S4-BD risk check: the syntactic masking supplier on served comb children
(scripts/gen2/S4_CONSUMER_FREEZE.md rev2 §6)

The only supplier of `KSBoundedIn … (KSn …) b.body _` (Tools/ShippingHierOptRun.lean:658) is
`KSn_boundedIn` (Tools/ShippingMachineShipsDepth.lean:171), whose premise is
`kidsMaskedN D.modules b.body = true` (ShipsDepth:163): every instance of the parent body names a module of the
design satisfying `outsMaskedN` (ShipsDepth:155) — no memory, each output port assigned exactly once by a
`selfMasked` right-hand side (`.const` / `.slice` ONLY, Tools/ShippingMachineShipsHier.lean:578) no wider than the
port, and no instance connection naming the port.

## Interpretation rules (binding for every result below)
* A `false` mask result does NOT refute `KSBoundedIn`: `kidsMaskedN` / `outsMaskedN` are SUFFICIENT, not
  necessary. `false` only says that the EXISTING syntactic supplier `KSn_boundedIn` does not apply.
* `true` only says that the existing supplier applies (to that module / body); it is not a statement about runs.
* The hand-written module `idH` (§3) is a boundary example of the PREDICATE. It is NOT a module served by a successful
  compilation and is NOT a counterexample of one.
* The skeletons of §1/§2 are closed terms built from the compiler's OWN closing functions on a stub transition; they
  evaluate the closing's contribution only, not the full-entry module. The full-entry modules are not closed terms
  (they are the result of an `IO`/`MetaM` run: translator, `closeLets`, `closeMachine`, `dropZeroWidthModule`,
  `mergeChecked`), so no `decide` theorem about them is possible here; §4 evaluates them by RUNNING the real entry
  (`synthesizeCombinational`, as Tests/Compiler/ShippingMachineInstTest.lean:115-145 does) and LOGS the result —
  a log, not a theorem. No `#eval` on `machineData` (it panics).

BUILT: g2bd-323d0501 at 323d0501 (exit 0); decided theorems kernel-checked ([propext]); real-entry results are logged observations. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.S4BdProbe
open Sparkle.IR.AST
open Sparkle.IR.Machine (closeMachine moduleByName)
open Tools.ShippingMachineShipsDepth (outsMaskedN kidsMaskedN)
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

/-! ## 1. `pickByteH` (machine route, slotless, with lets) — the closing skeleton

The real entry (Sparkle/Compiler/Elab.lean:5252-5264) emits `closeMachine shape.layout (closeLets … t)`. `closeLets`
ends its body with `assign out = ref core` (Machine.lean:189); `closeMachine` DROPS that last statement and drives
every output by `outAssigns w lay.outs` = `.assign o.name (.slice (.ref w) (o.lo + o.width - 1) o.lo)`
(Machine.lean:76-78, :98-115). Evaluated here: `closeMachine pickByteH.machineData.shape.layout pbhStub`, where the
stub transition is only the final `assign out = ref _core` that `closeMachine` reads (the translator's statements of
the real transition write `_`-allocated wires, not `out`, and are not modelled). -/

/-- Shape facts of the real layout (decided on the generated `pickByteH.machineData`). Expected: one output, no
slots, the output's type width equal to its field width (`houtTy` of `child_full_post`). -/
theorem pbh_outs_len : pickByteH.machineData.shape.layout.outs.length = 1 := by
  first | decide | decide +kernel
theorem pbh_slots_nil : pickByteH.machineData.shape.layout.slots = [] := by
  first | decide | decide +kernel
theorem pbh_outs_ty : (pickByteH.machineData.shape.layout.outs.all fun o => o.ty.bitWidth == o.width) = true := by
  first | decide | decide +kernel

/-- The stub transition: just the packed-wire tail `closeMachine` matches (`packedWire?`, Machine.lean:89). -/
def pbhStub : Module :=
  { name := "pickByteH_stub", inputs := [], outputs := [{ name := "out", ty := .bitVector 8 }],
    wires := [{ name := "_core", ty := .bitVector 8 }], body := [.assign "out" (.ref "_core")] }

/-- The closing's contribution on the real layout. -/
noncomputable def pbhSkeleton : Module := closeMachine pickByteH.machineData.shape.layout pbhStub

/-- **Expected `true`.** The only output is driven once by a `.slice` of width `o.width = o.ty.bitWidth`; no memory,
no instance. So the closing ITSELF yields a module the syntactic supplier accepts. What this does NOT cover: the
translator's statements and the post-processing (`dropZeroWidthModule`, `mergeChecked` — the latter keeps a merge
only if the masks are kept, `Sparkle.IR.RefineCheck.masksKept`, cf. Tools/ShippingChecksMaskedLeaf.lean:4-12). -/
theorem pbh_skeleton_masked : outsMaskedN pbhSkeleton = true := by
  first | decide | decide +kernel

/-- `callerL`-shaped parent body over the skeleton: one instance of it (the connection names are illustrative). -/
theorem pbh_skeleton_kidsMasked :
    kidsMaskedN [pbhSkeleton]
      [.inst pbhSkeleton.name "inst0" [("w", .ref "a"), ("sel", .ref "b"), ("out", .ref "_gen_inst0")]] = true := by
  first | decide | decide +kernel

/-! ## 2. `pick` (certified gate leaf) — the gate's finish skeleton

The gate route (`synthesizeMixedCertified`, Elab.lean:2959) finishes each leaf by `emitLeaves`
(Elab.lean:2157-2194): `addOutput "out"` and `emitAssign "out" (.ref leafWire)` — a `.ref`, which `selfMasked`
rejects. If `mergeChecked` substitutes the leaf wire's definition, `pick`'s top operator is a `Signal.mux`, i.e. an
`.op .mux …` right-hand side — also rejected. No `pick.machineData`-style closed term of the gate MODULE exists, so
both forms are evaluated as skeletons. -/

/-- The gate's emission form: `out := ref _w`. -/
def pickGateRef : Module :=
  { name := "pick_skel_ref", inputs := [{ name := "sel", ty := .bitVector 2 }, { name := "x", ty := .bitVector 8 }],
    outputs := [{ name := "out", ty := .bitVector 8 }], wires := [{ name := "_w", ty := .bitVector 8 }],
    body := [.assign "_w" (.op .mux [.ref "_c", .ref "x", .ref "_e"]), .assign "out" (.ref "_w")] }

/-- The merged form: `out := mux …`. -/
def pickGateMux : Module :=
  { name := "pick_skel_mux", inputs := [{ name := "sel", ty := .bitVector 2 }, { name := "x", ty := .bitVector 8 }],
    outputs := [{ name := "out", ty := .bitVector 8 }], wires := [],
    body := [.assign "out" (.op .mux [.ref "_c", .ref "x", .ref "_e"])] }

/-- **Expected `false`** (rhs `.ref`). The supplier does not apply; NOT a refutation of `KSBoundedIn`. -/
theorem pick_skeleton_ref_masked : outsMaskedN pickGateRef = false := by
  first | decide | decide +kernel
/-- **Expected `false`** (rhs `.op .mux`). Same reading. -/
theorem pick_skeleton_mux_masked : outsMaskedN pickGateMux = false := by
  first | decide | decide +kernel

/-! ## 3. Boundary example: the hand-written assign-only `idH` (x : 8 bits ⟶ y, `y := x`)

NOT a compiled module; NOT a counterexample of a successful compilation. It shows that the predicate rejects an
unmasked input read even though such a module plainly keeps `y < 2 ^ 8` on every IN-RANGE input (`KSBoundedIn`
quantifies over EVERY `env`, HierOptRun:658-663, so on an out-of-range `x` the bound could fail — a fact about the
predicate on this module only). `idHSlice` (`y := x[7:0]`) is the same function on in-range inputs and IS accepted:
the supplier is purely syntactic. -/

def idH : Module :=
  { name := "idH", inputs := [{ name := "x", ty := .bitVector 8 }], outputs := [{ name := "y", ty := .bitVector 8 }],
    wires := [], body := [.assign "y" (.ref "x")] }

def idHSlice : Module :=
  { name := "idHSlice", inputs := [{ name := "x", ty := .bitVector 8 }],
    outputs := [{ name := "y", ty := .bitVector 8 }], wires := [], body := [.assign "y" (.slice (.ref "x") 7 0)] }

/-- **Expected `false`** (`y := ref x`). -/
theorem idH_masked : outsMaskedN idH = false := by
  first | decide | decide +kernel
/-- **Expected `false`**: a parent with one `idH` instance. -/
theorem idH_kidsMasked : kidsMaskedN [idH] [.inst "idH" "u0" [("x", .ref "a"), ("y", .ref "b")]] = false := by
  first | decide | decide +kernel
/-- **Expected `true`** (`y := x[7:0]`, width 7 - 0 + 1 = 8 ≤ 8). -/
theorem idHSlice_masked : outsMaskedN idHSlice = true := by
  first | decide | decide +kernel
/-- **Expected `false`**: the `none` branch — an instance whose module is not in the list. -/
theorem missing_kidsMasked : kidsMaskedN [] [.inst "idH" "u0" []] = false := by
  first | decide | decide +kernel

/-! ## 4. The REAL served modules (run of the real entry; LOGGED, not theorems)

`synthesizeCombinational parent` is the full entry (the `hr` of `child_full`, Tools/ShippingMachineChild.lean:386):
`b` = the returned parent module, `D` = its design; `kidsMaskedN D.modules b.body` is EXACTLY the premise of
`KSn_boundedIn` as consumed (`fun b D h => KSn_boundedIn D.modules b.body h n`, Tools/ShippingSeqParentAt.lean:171).
For every instance the served module (`moduleByName D.modules mn`, the lookup `kidsMaskedN` makes) gets its
`outsMaskedN` and each output's right-hand sides logged. Nothing is asserted on the mask values (this draft was not
built; the expected values are stated); the command fails only if the entry itself throws for `callerL` / `caller`.

Expected: `callerL` → `pickByteH` `true` (§1: slice from `closeMachine`, kept by the `mergeChecked` masks guard);
`caller` → `pick` `false` (§2: `.ref` / `.op`); `callerIdH` → `idHSrc` `false` (gate route, `out := ref x` or similar
— recorded, not assumed). -/

/-- The compiled counterpart of §3 (spec §6 item 2): an identity hardware module … -/
@[hardware_module]
def idHSrc (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := x

/-- … called once by a one-output register parent (the shape of ShippingMachineInstTest's `caller`). -/
def callerIdH (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let y := idHSrc (accS + x)
    acc <~ y
    return y

open Lean Meta in
/-- Run the real entry on `parent`; log `kidsMaskedN D.modules b.body` and, per instance, the served module's
`outsMaskedN` and output right-hand sides. -/
def probeParent (parent : Name) : MetaM Unit := do
  let (b, D) ← Sparkle.Compiler.Elab.synthesizeCombinational parent
  logInfo m!"S4-BD REAL [{parent}]: kidsMaskedN D.modules b.body = {toString (kidsMaskedN D.modules b.body)}"
  for st in b.body do
    match st with
    | .inst mn iname _ =>
      match moduleByName D.modules mn with
      | some c =>
        let rhs := c.outputs.map fun p => (p.name, c.body.filterMap fun s => match s with
          | .assign l r => if l == p.name then some r else none
          | _ => none)
        logInfo m!"S4-BD REAL [{parent}] instance {iname} of {mn}: outsMaskedN = {toString (outsMaskedN c)}; inputs = {repr (c.inputs.map (·.name))}; output rhs = {repr rhs}"
      | none =>
        logInfo m!"S4-BD REAL [{parent}] instance {iname} of {mn}: not in the design (kidsMaskedN's `none` branch: false)"
    | _ => pure ()

run_cmd Lean.Elab.Command.liftTermElabM do
  probeParent ``Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL
  probeParent ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
  -- the compiled identity: the route may refuse it; record what happens instead of failing the file
  try probeParent ``callerIdH
  catch e => Lean.logInfo m!"S4-BD REAL [callerIdH]: the entry threw: {e.toMessageData}"

#print axioms pbh_skeleton_masked
#print axioms pick_skeleton_ref_masked
#print axioms idH_masked
#print axioms idHSlice_masked

end Tests.Gen2.S4BdProbe
