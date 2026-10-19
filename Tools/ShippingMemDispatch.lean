import Tools.ShippingReaderFuelR1
import Tools.ShippingReaderFuelShape
import Tools.ShippingChildRun

/-! # Memory placeholder names: the collision, the ORIGIN dispatch, and the withdrawn guard model

## Current (par/o-close): the origin dispatch — BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md)

The compiler change "explicit call-entry origin" (`Sparkle/Compiler/MachInstOrigin.lean`,
`docs/parallel/S-memname-collision.md` §5) records an origin per call entry
(`MachineShape.instOrigins`) and the general closing `closeInstsGM` maps
`shape.instTagged` = (callee, origin) and builds the child FROM THE ORIGIN:
`match o.child? with | some md => pure md | none => synth c`.

* `gmChoice` — that per-entry choice, on the origin;
* `gmChoice_body` — the closing's `mapM` body is `gmChoice` (as written in
  the patched Elab.lean);
* `gmChoice_mem` — a memory-origin entry gets the memory module of ITS OWN
  `combo aw dw`, whatever its name;
* `gmChoice_notMem`, `gmChoice_collision` — every other entry gets
  `synth c`, the declaration's own compile, REGARDLESS OF THE NAME: a
  declaration named `memChildName combo aw dw` with an ordinary origin is
  compiled;
* `closeInstsGM_child_choice`, `closeInstsGM_collision_compiled` — the same
  on a real run of `closeInstsGM` from an invariant world (via
  `Tools.ShippingChildInv.closeInstsGM_inv`): a memory-origin entry's child IS
  `memModule cb aw dw`; any other entry's child is a `RealChild` of its
  declaration (in particular a colliding name with an ordinary origin);
* `not_memR1_all` — kept (`MemR1` is not a property of every signature table).

## WITHDRAWN / HISTORICAL: the guard model (BUILT on poc 3a1938a3, run `md1`)

Before the origin tag, this file modelled a GUARDED reader (`machineShapeG?`:
refuse a general-closing shape whose entry name is a memory placeholder AND has
a signature, `shapeClash` / `memSigClash`) over the NAME-keyed dispatch
(`gmChoiceName`, the pre-patch `closeInstsGM` body). That proposal was NOT
applied; the origin tag replaced it. The theorems are kept (renamed
`gmChoiceName*` where they speak of the old dispatch) so nothing referring to
them breaks; they describe the unpatched compiler and the withdrawn proposal,
not the shipped code.

The finding itself (measured, `Tests/Compiler/MemNameCollisionProbe.lean`, runs
`mc2`, `mc4`): with `fakeSrc` copied under `SparkleMem.sync.4.8` and tagged
`@[hardware_module]`, the unpatched certified route emitted a SYNCHRONOUS
MEMORY for the call of the declaration (`collParent`), a miscompile; `MemR1`
held there, so `MemR1` was not the guarding property. -/
namespace Tools.ShippingMemDispatch
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachMemory (memChild? memChildName memModule)
open Tools.ShippingReaderFuelR1 (MemR1)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)

/-- HISTORICAL: the child choice of the UNPATCHED `closeInstsGM` (keyed on
the entry's NAME) for one entry's callee `c`, given the child synthesiser. -/
def gmChoiceName {m : Type → Type} [Monad m] {α : Type}
    (synth : Name → m α) (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α) (c : Name) : m α :=
  match memChild? c with
  | some md => pure (mem md)
  | none => synth c

/-- A memory placeholder decodes to its own memory module. -/
theorem memChild_memChildName (combo : Bool) (aw dw : Nat) :
    memChild? (memChildName combo aw dw) = some (memModule combo aw dw) := by
  cases combo
  · first
      | rfl
      | simp [memChild?, memChildName]
      | decide
  · first
      | rfl
      | simp [memChild?, memChildName]
      | decide

/-- HISTORICAL (name dispatch): a placeholder-named entry gets its memory module. -/
theorem gmChoiceName_mem {m : Type → Type} [Monad m] {α : Type} (synth : Name → m α)
    (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α) (combo : Bool) (aw dw : Nat) :
    gmChoiceName synth mem (memChildName combo aw dw) = pure (mem (memModule combo aw dw)) := by
  unfold gmChoiceName
  rw [memChild_memChildName]

/-- A callee name that is a memory placeholder AND has a signature in `senv`. -/
def memSigClash (senv : StructEnv) (c : Name) : Bool :=
  (memChild? c).isSome && ((senv.inst c).isSome || (senv.instS c).isSome)

/-- The guard: a shape closed by the general closing with a clashing entry. -/
def shapeClash (senv : StructEnv) (sp : MachineShape) : Bool :=
  !sp.instFields.isEmpty && sp.insts.any (fun i => memSigClash senv i.1)

/-- **The guarded reader (model of the proposed compiler change).** -/
def machineShapeG? (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool := true) : Option MachineShape :=
  (machineShape? symbolicMode parameters ci senv allowInsts).bind fun sp =>
    if shapeClash senv sp then none else some sp

theorem machineShapeG_some {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeG? sym ps ci senv ai = some sp) :
    machineShape? sym ps ci senv ai = some sp ∧ shapeClash senv sp = false := by
  unfold machineShapeG? at h
  cases hm : machineShape? sym ps ci senv ai with
  | none => rw [hm] at h; cases h
  | some sp' =>
    rw [hm] at h
    dsimp only [Option.bind] at h
    cases hc : shapeClash senv sp' with
    | true => rw [hc] at h; cases h
    | false =>
      rw [hc] at h
      cases h
      exact ⟨rfl, hc⟩

/-- No entry of a guarded general-closing shape clashes. -/
theorem machineShapeG_noClash {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeG? sym ps ci senv ai = some sp) (hne : sp.instFields ≠ [])
    {e : Name × List Nat × MixedGateBinder} (he : e ∈ sp.insts) :
    memSigClash senv e.1 = false := by
  have hc := (machineShapeG_some h).2
  unfold shapeClash at hc
  have hne' : sp.instFields.isEmpty = false := by
    cases hf : sp.instFields with
    | nil => exact absurd hf hne
    | cons _ _ => rfl
  rw [hne', Bool.not_false, Bool.true_and] at hc
  cases hx : memSigClash senv e.1 with
  | false => rfl
  | true =>
    have : sp.insts.any (fun i => memSigClash senv i.1) = true :=
      List.any_eq_true.mpr ⟨e, he, hx⟩
    rw [this] at hc
    first | cases hc | simp at hc

/-- HISTORICAL (withdrawn guard): under the guard, a callee with a signature gets its own compile. -/
theorem gmChoiceName_sig {m : Type → Type} [Monad m] {α : Type} (synth : Name → m α)
    (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α) {senv : StructEnv} {c : Name}
    (hsig : (senv.inst c).isSome = true ∨ (senv.instS c).isSome = true)
    (hno : memSigClash senv c = false) :
    gmChoiceName synth mem c = synth c := by
  unfold gmChoiceName
  cases hm : memChild? c with
  | none => rfl
  | some md =>
    exfalso
    unfold memSigClash at hno
    rw [hm] at hno
    rcases hsig with h | h
    · rw [h] at hno
      first | cases hno | simp at hno
    · rw [h, Bool.or_true] at hno
      first | cases hno | simp at hno

/-- **Dispatch of a guarded shape**: every entry of a general-closing shape
whose callee has a signature is given the declaration's own compile. -/
theorem machineShapeG_dispatch {m : Type → Type} [Monad m] {α : Type} (synth : Name → m α)
    (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α)
    {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeG? sym ps ci senv ai = some sp) (hne : sp.instFields ≠ [])
    {e : Name × List Nat × MixedGateBinder} (he : e ∈ sp.insts)
    (hsig : (senv.inst e.1).isSome = true ∨ (senv.instS e.1).isSome = true) :
    gmChoiceName synth mem e.1 = synth e.1 :=
  gmChoiceName_sig synth mem hsig (machineShapeG_noClash h hne he)

/-- Under the guard, a memory placeholder entry of a general-closing shape has
NO signature (so `R1` holds for it without `MemR1`). -/
theorem machineShapeG_mem_noSig {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeG? sym ps ci senv ai = some sp) (hne : sp.instFields ≠ [])
    {combo : Bool} {aw dw : Nat} {js : List Nat} {r : MixedGateBinder}
    (he : (memChildName combo aw dw, js, r) ∈ sp.insts) :
    senv.inst (memChildName combo aw dw) = none ∧ senv.instS (memChildName combo aw dw) = none := by
  have hc := machineShapeG_noClash h hne he
  unfold memSigClash at hc
  rw [memChild_memChildName] at hc
  dsimp only [Option.isSome] at hc
  cases hi : senv.inst (memChildName combo aw dw) with
  | some _ => rw [hi] at hc; cases hc
  | none =>
    cases hs : senv.instS (memChildName combo aw dw) with
    | some _ => rw [hi, hs] at hc; cases hc
    | none => exact ⟨rfl, rfl⟩

/-- **`MemR1` is not a property of every signature table.** -/
theorem not_memR1_all : ¬ ∀ senv : StructEnv, MemR1 senv := by
  intro h
  have := h { proj := fun _ => none, fields := fun _ => none,
              inst := fun _ => some ([], MixedGateBinder.bool) } false 1 1 [] MixedGateBinder.bool rfl
  cases this


/-! ## The origin dispatch (patched compiler) -/

/-- **The child choice of the patched `closeInstsGM`** for one tagged entry
(callee `c`, origin `o`): the origin's built child, else the declaration's
compile. -/
def gmChoice {m : Type → Type} [Monad m] {α : Type}
    (synth : Name → m α) (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α)
    (c : Name) (o : InstOrigin) : m α :=
  match o.child? with
  | some md => pure (mem md)
  | none => synth c

/-- The patched closing's `mapM` body (Elab.lean, `closeInstsGM`) is `gmChoice`. -/
theorem gmChoice_body {m : Type → Type} [Monad m]
    (synth : Name → m (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) :
    (fun (x : Name × InstOrigin) => match x with
      | (c, o) => match o.child? with
        | some md => pure md
        | none => synth c) = fun x => gmChoice synth id x.1 x.2 := by
  funext x
  obtain ⟨c, o⟩ := x
  rfl

/-- **A memory-origin entry gets the memory module of its own widths**,
whatever the entry's name. -/
theorem gmChoice_mem {m : Type → Type} [Monad m] {α : Type} (synth : Name → m α)
    (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α) (c : Name)
    (combo : Bool) (aw dw : Nat) :
    gmChoice synth mem c (.mem combo aw dw) = pure (mem (memModule combo aw dw)) := rfl

/-- **Every other entry gets the declaration's own compile.** -/
theorem gmChoice_notMem {m : Type → Type} [Monad m] {α : Type} (synth : Name → m α)
    (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α) (c : Name) {o : InstOrigin}
    (h : ∀ combo aw dw, o ≠ .mem combo aw dw) :
    gmChoice synth mem c o = synth c := by
  cases o with
  | ord => rfl
  | field i => rfl
  | mem combo aw dw => exact absurd rfl (h combo aw dw)

/-- **The collision case**: a declaration NAMED as a memory placeholder, read
as an ordinary call (or a structure field), gets its own compile. -/
theorem gmChoice_collision {m : Type → Type} [Monad m] {α : Type} (synth : Name → m α)
    (mem : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design → α) (combo : Bool) (aw dw : Nat) :
    gmChoice synth mem (memChildName combo aw dw) .ord = synth (memChildName combo aw dw) ∧
    ∀ i, gmChoice synth mem (memChildName combo aw dw) (.field i) =
      synth (memChildName combo aw dw) :=
  ⟨rfl, fun _ => rfl⟩

section Run
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingMachineEntry

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The per-entry choice of a real run of the patched `closeInstsGM`**, from
an invariant world: a memory-origin entry's child IS `memModule cb aw dw`; an
entry of any other origin has a `RealChild` of its declaration — whatever the
name. -/
theorem closeInstsGM_child_choice (L : RefLaws mref cref)
    (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : InvV L w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧
      children.length = shape.insts.length ∧
      ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        (∀ combo aw dw, shape.instOrigins.getD k .ord = .mem combo aw dw →
          y = memModule combo aw dw) ∧
        ((∀ combo aw dw, shape.instOrigins.getD k .ord ≠ .mem combo aw dw) →
          RealChild mref cref (shape.insts[k]).1 y) := by
  obtain ⟨children, hc, hMC, ⟨hlen, hall⟩, -⟩ := closeInstsGM_inv L hB hw hr
  refine ⟨children, hc, hlen, fun k hk => ?_⟩
  obtain ⟨y, hy, hor⟩ := hall k hk
  refine ⟨y, hy, fun combo aw dw ho => ?_, fun hno => ?_⟩
  · have h1 := hMC k hk (memModule combo aw dw)
      (by rw [ho]; rfl)
    rw [hy] at h1
    exact Option.some.inj h1
  · have hnone : (shape.instOrigins.getD k .ord).child? = none := by
      cases ho' : shape.instOrigins.getD k .ord with
      | ord => rfl
      | field i => rfl
      | mem combo aw dw => exact absurd ho' (hno combo aw dw)
    rcases hor with h | h
    · rw [hnone] at h
      cases h
    · exact h

/-- **A colliding name is compiled**: an entry named `memChildName combo aw dw`
whose origin is ordinary gets a `RealChild` of that declaration. -/
theorem closeInstsGM_collision_compiled (L : RefLaws mref cref)
    (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : InvV L w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w')
    {k : Nat} (hk : k < shape.insts.length) {combo : Bool} {aw dw : Nat}
    (hname : (shape.insts[k]).1 = memChildName combo aw dw)
    (hord : shape.instOrigins.getD k .ord = .ord) :
    ∃ children y, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧
      children[k]? = some y ∧ RealChild mref cref (memChildName combo aw dw) y := by
  obtain ⟨children, hc, -, hall⟩ := closeInstsGM_child_choice L hB hw hr
  obtain ⟨y, hy, -, hre⟩ := hall k hk
  refine ⟨children, y, hc, hy, ?_⟩
  rw [← hname]
  exact hre (fun combo' aw' dw' h => by rw [hord] at h; cases h)

end Run

/-! ## The same guard on the fuel candidate -/

/-- The candidate wrapper followed by the guard (OUT stays OUT). -/
def machineShapeFG (n : Nat) (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (senv : StructEnv) (allowInsts : Bool := true) :
    Option (Option MachineShape) :=
  (Tools.ShippingReaderFuel.machineShapeF n symbolicMode parameters ci senv allowInsts).map
    fun r => r.bind fun sp => if shapeClash senv sp then none else some sp

/-- The guard commutes with any answer of the candidate (so every stability /
adequacy / driver theorem of `machineShapeF` transfers by this equation). -/
theorem machineShapeFG_of {n : Nat} {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {r : Option MachineShape}
    (h : Tools.ShippingReaderFuel.machineShapeF n sym ps ci senv ai = some r) :
    machineShapeFG n sym ps ci senv ai =
      some (r.bind fun sp => if shapeClash senv sp then none else some sp) := by
  unfold machineShapeFG
  rw [h]
  rfl

theorem machineShapeFG_out {n : Nat} {sym : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool}
    (h : Tools.ShippingReaderFuel.machineShapeF n sym ps ci senv ai = none) :
    machineShapeFG n sym ps ci senv ai = none := by
  unfold machineShapeFG
  rw [h]
  rfl

end Tools.ShippingMemDispatch
