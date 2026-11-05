import Tools.ShippingGen5ReaderTraceShape2
import Tools.ShippingGen5GDCover1
set_option autoImplicit false
-- Built in Pod (kjob lake build, exit 0) on the tree of 103188546c6022566a55a5d45f16cb92681aa8d7 (Lean content identical; this header is comment-only). Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # RT: the W-side state `st` and the `machineShapeF_reach'` state `st` are the same state

`machineShapeF` is a function, so every phase of its run (`shapePre`, `machNormF`, `shapeStart`, `foldO … rootLets`, `shapeBody`) is deterministic.
`stateSide_functional`: two `StateSideWitness` for the same `E senv sp n` agree in every component.
`reach'_of_witness`: the facts that `machineShapeF_reach'` states about its `st` hold for the `st` of any `StateSideWitness` (the one of `stateSide_of_production` / `shapeAgree_witness`).
No new premise: `hE`, `hT`, `hIn` are the hypotheses of `machineShapeF_reach'`, `hn` is the fuel equation `stateSide_of_production` obtains from `hbr`. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.ShippingReaderLenOk
  Tools.Assume.ExprEqv Tools.ShippingGen5GDCover1

theorem stateSide_functional {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat}
    {p p' : ShapePre} {en en' : Lean.Expr} {st0 st0' : MachRead} {env env' : List MachVal}
    {st1 st1' st st' : MachRead} {v v' : Lean.Expr}
    (w : StateSideWitness E senv sp n p en st0 env st1 st v)
    (w' : StateSideWitness E senv sp n p' en' st0' env' st1' st' v') :
    p = p' ∧ en = en' ∧ st0 = st0' ∧ env = env' ∧ st1 = st1' ∧ st = st' ∧ v = v' := by
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := w
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := w'
  have hp : p = p' := Option.some.inj (a1.symm.trans b1)
  subst hp
  have hen : en = en' := Option.some.inj (a2.symm.trans b2)
  subst hen
  have h0 : st0 = st0' := Option.some.inj (Option.some.inj (a3.symm.trans b3))
  subst h0
  have h1 : (env, st1) = (env', st1') := Option.some.inj (Option.some.inj (a4.symm.trans b4))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
  have h2 : (st, v) = (st', v') := Option.some.inj (Option.some.inj (a5.symm.trans b5))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem reach'_of_witness {n : Nat} {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {nDecl : Nat}
    (hE : EqvAtom) (hT : TraceGood senv nDecl (readF senv n))
    (hn : machineShapeF n false [] E senv true = some (some sp))
    (hIn : ShapeInputs' nDecl senv false [] E n)
    {p : ShapePre} {en : Lean.Expr} {st0 : MachRead} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr}
    (w : StateSideWitness E senv sp n p en st0 env st1 st v) :
    FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
    TrInv senv nDecl st ∧
    ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) := by
  obtain ⟨p', en', st0', env', st1', st', v', hp, hen, h0, h1, h2, h3, l2, i1, i2, i3, i4, R0, R1, R2, Tr, hv⟩ :=
    machineShapeF_reach' hE hT hn hIn
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := stateSide_functional w
    ⟨hp, hen, h0, h1, h2, h3, l2, i1, i2, i3, i4⟩
  exact ⟨R0, R1, R2, Tr, hv⟩

end Tools.ShippingGen5ReaderTrace
