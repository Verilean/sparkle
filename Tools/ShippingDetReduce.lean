import Tools.ShippingCacheCoherentVia

/-! # The closing at EVERY invariant world, reduced to determinism of the real compiles

`MachineClosesAt declName shape` (every invariant world of positive depth,
whatever its cache holds) follows from the built relative closing
`MachineClosesAtS … decls` when the cache the machine synthesis ends with
satisfies `Agree decls`. That cache satisfies `CacheInv`: each entry is a
`RealChild` — the result of SOME real compile of its key. This file says
exactly what has to be known of real compiles for `Agree` to follow, and
proves the implication:

* `DetN c`: two real compiles of `c` return the same MODULE
  (`y.1 = y'.1`; nothing is asked of the design component);
* `RealMod S a`: the module `a` is the module of a real compile of a
  declaration of `S`, and is named after it;
* `eq_of_realMod`: two such modules of one name are equal — the names are
  injective in the declaration (`ofDecl_injective`), and `DetN`;
* `agree_of_realMods`: `Agree decls m` when every module an entry of `decls`
  holds is a `RealMod`;
* **`machineClosesAt_of_det`**: `MachineClosesAt` at its full scope, from
  `MachineClosesAtS`, `DetN` on `S`, and `hreal` — every module of every
  real compile of a callee (its own module and the modules of its design)
  is a `RealMod S`.

`DetN` is NOT proved here and `hreal` is not instantiated: see
`docs/parallel/A-determinism.md` for what stands between the present laws
and `DetN` (the run-local translation cache has no value law), and for the
declarations — legacy route, an untagged helper compiled as a module — for
which `DetN` is FALSE of abstract invariant worlds.

WRITTEN, NOT BUILT (par/a-39). -/
namespace Tools.ShippingDetReduce
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.IR.ModuleName (ofDecl)
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingCallsKidsS Tools.ShippingCacheCoherent
open Tools.ShippingCacheCoherentVia (keeps_runs)
open Tools.ShippingModuleName (ofDecl_injective)

section Defs
variable (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)

/-- Two real compiles of `c` return the same module. -/
def DetN (c : Name) : Prop :=
  ∀ y y' : Res, RealChild mref cref c y → RealChild mref cref c y' → y.1 = y'.1

/-- `a` is the module of a real compile of a declaration of `S`, named after
that declaration. -/
def RealMod (S : Name → Prop) (a : Sparkle.IR.AST.Module) : Prop :=
  ∃ (c : Name) (z : Res), S c ∧ RealChild mref cref c z ∧ a = z.1 ∧ z.1.name = ofDecl c

end Defs

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- Two modules of real compiles of `S`, of one name, are equal — given
`DetN` on `S`. -/
theorem eq_of_realMod {S : Name → Prop} (hdet : ∀ c, S c → DetN mref cref c)
    {a b : Sparkle.IR.AST.Module} (ha : RealMod mref cref S a) (hb : RealMod mref cref S b)
    (hn : a.name = b.name) : a = b := by
  obtain ⟨c, z, hc, hz, ea, na⟩ := ha
  obtain ⟨c', z', hc', hz', eb, nb⟩ := hb
  have e : ofDecl c = ofDecl c' := by
    rw [← na, ← nb, ← ea, ← eb]
    exact hn
  have hcc : c = c' := ofDecl_injective e
  rw [← hcc] at hz'
  rw [ea, eb]
  exact hdet c hc z z' hz hz'

/-- `Agree decls m` when every module an entry of `decls` holds is the module
of a real compile of `S`. -/
theorem agree_of_realMods (decls : List Name) {m : Std.HashMap Name Res} {S : Name → Prop}
    (hdet : ∀ c, S c → DetN mref cref c)
    (hmods : ∀ c ∈ decls, ∀ y : Res, m.get? c = some y → ∀ a ∈ mods y, RealMod mref cref S a) :
    Agree decls m :=
  fun c hc c' hc' _ y y' hy hy' a ha b hb hn =>
    eq_of_realMod hdet (hmods c hc y hy a ha) (hmods c' hc' y' hy' b hb) hn

/-- **`MachineClosesAt` at its full scope, from the relative closing and
determinism.** `hreal`: every module of a real compile of a callee is the
module of a real compile of a declaration of `S`. -/
theorem machineClosesAt_of_det {declName : Name} {shape : MachineShape} (decls : List Name)
    (hS : MachineClosesAtS mctx mref cctx cref declName shape decls)
    (hB : ∀ L' : RefLaws mref cref, BodyRel L') (hH : ∀ L' : RefLaws mref cref, HarnessRel L')
    {S : Name → Prop} (hdet : ∀ c, S c → DetN mref cref c)
    (hreal : ∀ c ∈ decls, ∀ y : Res, RealChild mref cref c y →
      ∀ a ∈ mods y, RealMod mref cref S a) :
    MachineClosesAt mctx mref cctx cref declName shape := by
  intro b w r w' hw hd hr
  obtain ⟨L, hv⟩ := invV_of_invW mctx cctx hw
  have hJ := keeps_runs
    (machine_keeps (mctx := mctx) (cctx := cctx) L.plain (hH _) (L.dval w)
      (childKeeps_all L.plain (hB _) _ (fun _ => trivial)) b declName shape)
    (show J L.plain _ _ from ⟨hv, rfl, trivial⟩) hr
  have hci : CacheInv mref cref (L.val w') := hJ.1.1
  refine hS b w r w' hw hd hr (fun mctx' cctx' m w1 hg => ?_)
  rw [L.cacheGet _ _ _ hg]
  exact agree_of_realMods decls hdet (fun c hc y hy a ha => hreal c hc y (hci c y hy) a ha)

end Tools.ShippingDetReduce
