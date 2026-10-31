import Tools.ShippingGen5T2TieCR
import Tests.Gen5.ClosingRun2Check
import Tests.Gen5.T2TieCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: new unit (freeze r1 95671524); clean build is run by the coder.
-- No sorry / axiom / native_decide.

/-! # T2-TIE x DG-CLOSINGRUN checks (Tools/ShippingGen5T2TieCR.lean; scripts/gen5/T2TIE_CR_FREEZE_R1.md)

Expected statements `ExpT1`-`ExpT3` are written from the Lean text of freeze r1 §4' (not from the implementation's signature).
The comparator is the SAME reducible one as `Tests.Gen5.ClosingRun2Check` (`checkExpectedR`/`checkMutantR`/`reachWith`, imported, not
copied). Positive controls run first with it on the built `callTie_of_served` and `closingRun0_of_run`. Mutants are the well-typed
one-point differences of freeze §5' (20 definitions, expanding the 12 ids M1-M12 over the theorems they apply to); each is rejected by
signature/defeq only, NOT a semantic counterexample. Then: closure walker (unknown names fail), forbidden roots, AXIOMS standard.

Not checked / not claimed: `hDG_GENP`, `hDG_SEM`, `hDG_SEM_range`, the group field row, `hord`/`hrow`, `hGen`/`GeneratedAt`,
non-vacuity of `ClosingShared`/`ClosingRun0`, depth-0 `stop`, T1/FG, Issue completion. -/

namespace Tests.Gen5.T2TieCRCheck
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingGen2 Tools.ShippingGen5ClosingRun2 Tools.ShippingGen5T2TieCR
open Tests.Gen3.ExpectedType Tests.Gen5.ClosingRun2Check

def ExpT1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def ExpT2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def ExpT3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingGen5ClosingRun2.ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def MutM1T1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def MutM1T2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def MutM1T3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingGen5ClosingRun2.ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def MutM2T1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? ≠ none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def MutM2T2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? ≠ none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def MutM2T3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingGen5ClosingRun2.ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? ≠ none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def MutM3T1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (dsn : Sparkle.IR.AST.Design) (r : Tools.ShippingChildInv.Res),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def MutM4T1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p (k + 1) r.1

def MutM5T1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P X r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def MutM6T1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ dsn.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def MutM7T1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = none ∧ FieldRowAt p k r.1

def MutM8T2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P p.decl = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def MutM8T3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingGen5ClosingRun2.ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P p.decl = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def MutM9T2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM_range : CallOutRange p q k hk) (hDG_SEM : GenExtAtCall p q k hk),
    CallTie p q k hk

def MutM9T3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingGen5ClosingRun2.ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM_range : CallOutRange p q k hk) (hDG_SEM : GenExtAtCall p q k hk),
    CallTie p q k hk

def MutM10T2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p p k hk

def MutM10T3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingGen5ClosingRun2.ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p p k hk

def MutM11T3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingGen5ClosingRun2.ClosingRun0 L P Reach mctx cctx X p (fun _ _ _ => False) w w' raw D) (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def MutM12T1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h1 : p.d.shape.instFields = []) (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none),
    ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1

def MutM12T2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    (hR : Reach X) (hP : P X = some p)
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h1 : p.d.shape.instFields = []) (hsh : Tools.ShippingGen5ClosingRun2.ClosingShared L P Reach mctx cctx X p Gen w w' raw D) (k : Nat) (hk : k < p.d.shape.insts.length) (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none) (q : Pkg ι dom) (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q) (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

run_cmd Lean.Elab.Command.liftTermElabM do
  -- positive controls: built statements, same comparator
  checkExpectedR ``callTie_of_served ``Tests.Gen5.T2TieCheck.ExpectedCallTieOfServed
  checkExpectedR ``closingRun0_of_run ``ExpRun0OfRun
  -- new statements against the independent Expected
  checkExpectedR ``servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.ExpT1
  checkExpectedR ``callTie_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.ExpT2
  checkExpectedR ``callTie_of_closingRun0_one ``Tests.Gen5.T2TieCRCheck.ExpT3
  -- mutants
  checkMutantR ``servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM1T1
  checkMutantR ``callTie_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM1T2
  checkMutantR ``callTie_of_closingRun0_one ``Tests.Gen5.T2TieCRCheck.MutM1T3
  checkMutantR ``servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM2T1
  checkMutantR ``callTie_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM2T2
  checkMutantR ``callTie_of_closingRun0_one ``Tests.Gen5.T2TieCRCheck.MutM2T3
  checkMutantR ``servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM3T1
  checkMutantR ``servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM4T1
  checkMutantR ``servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM5T1
  checkMutantR ``servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM6T1
  checkMutantR ``servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM7T1
  checkMutantR ``callTie_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM8T2
  checkMutantR ``callTie_of_closingRun0_one ``Tests.Gen5.T2TieCRCheck.MutM8T3
  checkMutantR ``callTie_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM9T2
  checkMutantR ``callTie_of_closingRun0_one ``Tests.Gen5.T2TieCRCheck.MutM9T3
  checkMutantR ``callTie_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM10T2
  checkMutantR ``callTie_of_closingRun0_one ``Tests.Gen5.T2TieCRCheck.MutM10T3
  checkMutantR ``callTie_of_closingRun0_one ``Tests.Gen5.T2TieCRCheck.MutM11T3
  checkMutantR ``servedCall_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM12T1
  checkMutantR ``callTie_of_closingShared_one ``Tests.Gen5.T2TieCRCheck.MutM12T2

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let F := `Tests.Gen5.ClosingRun2Fixture
  -- controls (same walker): bad fixtures hit, clean ones do not, unresolved names counted
  for (c, bad) in [(F ++ `badDec, true), (F ++ `badCoreReads, true), (F ++ `unrelated, false), (F ++ `cleanND, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "CRT AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "CRT AUDIT FAILED: detector flags {c}"
  let envU ← getEnv
  let hideB := fun n => if n == `Tests.Gen5.ClosingRun2Helper.helperA then none else envU.find? n
  let rU ← reachWith hideB (F ++ `badCoreReadsHelper)
  if rU.unknown == 0 then throwError "CRT AUDIT FAILED: unresolved name was skipped, not counted"
  for (c, req) in [(``servedCall_of_closingShared_one,
        [``Tools.ShippingMachineInst.closeInsts_calls, ``Tools.ShippingChildServe.closeInsts_names,
         ``Tools.ShippingChildServe.closeInsts_acyclic, ``Tools.ShippingGen2.fieldRow_one_of_callStmt,
         ``Tools.ShippingGen2.T1HypND.closed]),
      (``callTie_of_closingShared_one, [``Tools.ShippingGen2.callTie_of_served, ``servedCall_of_closingShared_one]),
      (``callTie_of_closingRun0_one, [``callTie_of_closingShared_one])] do
    let r ← reach c
    if let some p := r.hit then throwError "CRT AUDIT FAILED {c}: forbidden use via {p}"
    if r.unknown != 0 then throwError "CRT AUDIT FAILED {c}: {r.unknown} unresolved name(s), first via {toString r.unknownFirst}"
    for t in req do
      unless r.seen.contains t do throwError "CRT AUDIT FAILED {c}: {t} not reached"
    logInfo m!"CRT REACH {c}: no forbidden root (T1Hyp.dec / T1Hyp fields / raw proj / recursor / BodyStepC / core_reads_invAt0 / soundX_ships_ran / servedShips0_proved / TopShips / ofReduceBool); reaches {req} (visited {r.visited}, unknown 0)"

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``servedCall_of_closingShared_one, ``callTie_of_closingShared_one, ``callTie_of_closingRun0_one] do
    checkAxioms n

end Tests.Gen5.T2TieCRCheck
