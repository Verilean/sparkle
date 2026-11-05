import Tools.ShippingGenFGLedgerPremisesG
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- C.SM-7 audit (Issue sparkle-ledger-sm7). No `sorry`, no `axiom`, no `native_decide`.

/-! # C.SM-7: the ordinary-call guard `hord` comes from the top consumer's own guard

`stepDec_of_ties` (`Tools/ShippingGen5T2Tie.lean`) is the top consumer of `CallTie`; its premise `hT2_TIE` asks for `CallTie`
only UNDER the guard `(p.d.shape.instOrigins.getD k .ord).child? = none`. `hT2Tie_of_genGP` supplies exactly that premise for
the generated table `genGP` (GPFIX): `GenExtAtCall` by `hDT1_of_genGP` (whose `hord` is the guard), the rest by the ND roots
`callTie_of_served_oneOut_t1ND` / `callTie_of_served_kidW_closing_t1ND`. Its binders are existing rows only (T1HypND, the
package of `p`, the ClosingRun row, OneOutWidth / hkidW); none of them is a `child? = none` fact. Conditional on those rows;
not FG. -/

namespace Tools.ShippingGen5SM7
open Lean Tools.ShippingGen2 Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Core Sparkle.Core.Signal

theorem hT2Tie_of_genGP {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (Sparkle.Compiler.Elab.structEnv env)))
    (env : Environment) (L : Laws mref cref) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) Reach DataOk)
    (p : Pkg ι dom) (hRp : Reach p.decl) (hPp : genGP (ι := ι) (dom := dom) lvl hs genData₀ env p.decl = some p)
    (hDG_CLOSINGRUN : ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
      (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl hs genData₀ env (p.d.shape.insts[k]).1 = some q →
      ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
        ShipsRes L (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) (p.d.shape.insts[k]'hk).1 r ∧
        (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
        Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hOW : p.d.shape.instFields = [] → ∀ k, OneOutWidth (genGP (ι := ι) (dom := dom) lvl hs genData₀ env) p k)
    (hkidW : p.d.shape.instFields ≠ [] →
      ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
        Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
        ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
          (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
            some pt.ty.bitWidth) :
    ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, genGP (ι := ι) (dom := dom) lvl hs genData₀ env (p.d.shape.insts[k]).1 = some q → CallTie p q k hk := by
  intro k hk hord q hq
  have hsem := hDT1_of_genGP (ι := ι) (dom := dom) lvl hs genData₀ env p.decl p hPp k hk hord q hq
  by_cases h1 : p.d.shape.instFields = []
  · exact callTie_of_served_oneOut_t1ND L _ p q k hk H hRp hPp hord hq (hDG_CLOSINGRUN k hk hord q hq) hsem h1
      (hOW h1 k)
  · exact callTie_of_served_kidW_closing_t1ND L _ p q k hk H hRp hPp hord hq (hDG_CLOSINGRUN k hk hord q hq) hsem h1
      (hkidW h1)

end Tools.ShippingGen5SM7

#print axioms Tools.ShippingGen5SM7.hT2Tie_of_genGP
