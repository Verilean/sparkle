import Tools.ShippingGen5AP17
import Tools.ShippingGen5AuditE3B3ND
import Tools.ShippingGen5SM7
import Tools.ShippingGen5FG
import Tools.ShippingGenFGLedgerPremisesG
set_option autoImplicit false
-- C.CR-4 (Issue sparkle-ledger-cr4). No `sorry`, no `axiom`, no `native_decide`.

/-! # C.CR-4: the ND roots with `H : T1HypND` replaced by existing rows

At `Reach := TgtRun P declName` the four fields of `T1HypND` are existing rows: `pkg` = A.P-08 (`hpkg`), `defines` = `h_A_P06`
(`hA6`, the same type as in `FGLedgerPremisesStmtG`), `closes` = A.P-07 (`hcl`), `closed` = `TgtRun.call`.
`t1HypND_of_rows` builds the structure; every `_rows` theorem below passes it to the ND theorem of the same name.
Existing theorems are not edited. In the `_rows` roots the `Reach` binder is replaced by `declName` (`Reach := TgtRun P declName`). -/

namespace Tools.ShippingGen5CR4
open Lean Tools.ShippingGen2 Tools.ShippingGen5FG Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingChildInvA Tools.ShippingChildBndCore (dv cv)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5Sem
open Tools.ShippingGen5ClosingRun2 Tools.ShippingGen5ClosingRun3 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun

theorem t1HypND_of_rows {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (declName : Name) (DataOk : Pkg ι dom → Prop)
    (hpkg : ∀ c, TgtRun P declName c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q)
    (hA6 : ∀ c, TgtRun P declName c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
        Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hcl : ∀ c, TgtRun P declName c → ∀ q : Pkg ι dom, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape) :
    T1HypND L P (TgtRun P declName) DataOk :=
  ⟨hpkg, hA6, hcl, fun _ hc _ hq k hk hord => TgtRun.call hc hq k hk hord⟩

theorem servedShips0_runND_rows {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (declName : Name) (DataOk : Pkg ι dom → Prop)
    (hpkg : ∀ c, TgtRun P declName c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q)
    (hA6 : ∀ c, TgtRun P declName c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
        Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hcl : ∀ c, TgtRun P declName c → ∀ q : Pkg ι dom, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape) :
    ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
      (raw : Sparkle.IR.AST.Module) (D : Design),
      TgtRun P declName p.decl → P p.decl = some p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
      (dv w = 0 ∨ CacheShips L P (TgtRun P declName) (cv w)) →
      IHAt L P (TgtRun P declName) (dv w + 1) → ChildKeepsInv L P (TgtRun P declName) (dv w + 1) →
      RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w' →
      Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
        p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc :=
  servedShips0_runND L P (TgtRun P declName) DataOk (t1HypND_of_rows L P declName DataOk hpkg hA6 hcl)

theorem postFacts_of_runND_rows {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (declName : Lean.Name) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hpkg : ∀ c, TgtRun P declName c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q)
    (hA6 : ∀ c, TgtRun P declName c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
        Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hcl : ∀ c, TgtRun P declName c → ∀ q : Pkg ι dom, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape) :
    ∀ (q : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (u u' w1 : Void IO.RealWorld)
      (M' raw : Sparkle.IR.AST.Module) (Dg' Dg : Design),
      TgtRun P declName q.decl → P q.decl = some q → DataOk q → AdmCtx L.O.quiet mctx cctx →
      InvAt L P (TgtRun P declName) (dv u) u →
      IHAt L P (TgtRun P declName) (dv u + 1) → ChildKeepsInv L P (TgtRun P declName) (dv u + 1) →
      RunsTo (synthesizeCombinational q.decl) mctx mref cctx cref u (M', Dg') u' →
      RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref u (raw, Dg) w1 →
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        M' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Dg'.topModule = Dg.topModule →
      ((∀ x ∈ Dg.modules, x.name ≠ raw.name) → Dg'.modules = Dg.modules) →
      MachineTaken L mctx cctx (dv u + 1) q.decl q.d.shape raw Dg →
      (∀ x ∈ Dg.modules, x.name ≠ raw.name) ∧ InstClosed (M', Dg') :=
  postFacts_of_runND L P (TgtRun P declName) DataOk hrows (t1HypND_of_rows L P declName DataOk hpkg hA6 hcl)

section GPForm
variable {ι : Type} {dom : ι → DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
variable (lvl : Lean.Expr → Nat) {initsOf : (d : Tools.ShippingMachineAuto.MachineData) → HList (tys d.ss)}
  (hs : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) initsOf)
  (genData₀ : (env : Environment) → (E : ConstantInfo) →
    Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (Sparkle.Compiler.Elab.structEnv env)))
  (env : Environment)

local notation "GP" => genGP (ι := ι) (dom := dom) lvl hs genData₀ env

theorem t1_of_stepPF_ND_rows (L : Laws mref cref) {declName : Name} {DataOk : Pkg ι dom → Prop}
    (hpkg : ∀ c, TgtRun GP declName c → ∃ q, GP c = some q ∧ q.decl = c ∧ DataOk q)
    (hA6 : ∀ c, TgtRun GP declName c → ∀ q : Pkg ι dom, GP c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
        Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hcl : ∀ c, TgtRun GP declName c → ∀ q : Pkg ι dom, GP c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape)
    (hStep : StepStmt L GP DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hMEM : HMemRow GP (TgtRun GP declName)) (hARGS : HArgsRow GP (TgtRun GP declName))
    (hOW : HOWRow GP (TgtRun GP declName)) (hkidW : HKidWRow L GP (TgtRun GP declName)) :
    ∀ (c : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
      (raw b : Sparkle.IR.AST.Module) (Dg : Design),
      TgtRun GP declName c → Start L mctx cctx w →
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, Dg) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      ∃ q n, GP c = some q ∧ TopShips q n c b raw Dg :=
  t1_of_stepPF_ND lvl hs genData₀ env L (t1HypND_of_rows L GP declName DataOk hpkg hA6 hcl) hStep hrows hMEM hARGS hOW hkidW

theorem closingRun0_of_runT1_ND_rows (L : Laws mref cref) {declName : Name} {DataOk : Pkg ι dom → Prop}
    (hpkg : ∀ c, TgtRun GP declName c → ∃ q, GP c = some q ∧ q.decl = c ∧ DataOk q)
    (hA6 : ∀ c, TgtRun GP declName c → ∀ q : Pkg ι dom, GP c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
        Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hcl : ∀ c, TgtRun GP declName c → ∀ q : Pkg ι dom, GP c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L GP DataOk)
    (hMEM : HMemRow GP (TgtRun GP declName)) (hARGS : HArgsRow GP (TgtRun GP declName))
    (hOW : HOWRow GP (TgtRun GP declName)) (hkidW : HKidWRow L GP (TgtRun GP declName))
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : TgtRun GP declName X) (hP : GP X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs0 : Start L mctx cctx w) (hd0 : dv w = 0)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun0 L GP (TgtRun GP declName) mctx cctx X p Gen w w' raw D :=
  closingRun0_of_runT1_ND lvl hs genData₀ env L (t1HypND_of_rows L GP declName DataOk hpkg hA6 hcl) hrows hStep
    hMEM hARGS hOW hkidW hR hP hs0 hd0 hrun Gen hGen

theorem closingRun_of_runT1_ND_rows (L : Laws mref cref) {declName : Name} {DataOk : Pkg ι dom → Prop}
    (hpkg : ∀ c, TgtRun GP declName c → ∃ q, GP c = some q ∧ q.decl = c ∧ DataOk q)
    (hA6 : ∀ c, TgtRun GP declName c → ∀ q : Pkg ι dom, GP c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
        Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hcl : ∀ c, TgtRun GP declName c → ∀ q : Pkg ι dom, GP c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L GP DataOk)
    (hMEM : HMemRow GP (TgtRun GP declName)) (hARGS : HArgsRow GP (TgtRun GP declName))
    (hOW : HOWRow GP (TgtRun GP declName)) (hkidW : HKidWRow L GP (TgtRun GP declName))
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : TgtRun GP declName X) (hP : GP X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L GP (TgtRun GP declName) (dv w) w)
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun L GP (TgtRun GP declName) mctx cctx X p Gen w w' raw D :=
  closingRun_of_runT1_ND lvl hs genData₀ env L (t1HypND_of_rows L GP declName DataOk hpkg hA6 hcl) hrows hStep
    hMEM hARGS hOW hkidW hA hR hP hst h1 hrun Gen hGen

theorem hT2Tie_of_genGP_rows (L : Laws mref cref) {declName : Name} {DataOk : Pkg ι dom → Prop}
    (hpkg : ∀ c, TgtRun GP declName c → ∃ q, GP c = some q ∧ q.decl = c ∧ DataOk q)
    (hA6 : ∀ c, TgtRun GP declName c → ∀ q : Pkg ι dom, GP c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
        Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hcl : ∀ c, TgtRun GP declName c → ∀ q : Pkg ι dom, GP c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape)
    (p : Pkg ι dom) (hRp : TgtRun GP declName p.decl) (hPp : GP p.decl = some p)
    (hDG_CLOSINGRUN : ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
      (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q : Pkg ι dom, GP (p.d.shape.insts[k]).1 = some q →
      ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
        ShipsRes L GP (p.d.shape.insts[k]'hk).1 r ∧
        (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
        Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hOW : p.d.shape.instFields = [] → ∀ k, OneOutWidth GP p k)
    (hkidW : p.d.shape.instFields ≠ [] →
      ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
        Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
        ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
          (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
            some pt.ty.bitWidth) :
    ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, GP (p.d.shape.insts[k]).1 = some q → CallTie p q k hk :=
  Tools.ShippingGen5SM7.hT2Tie_of_genGP lvl hs genData₀ env L (t1HypND_of_rows L GP declName DataOk hpkg hA6 hcl)
    p hRp hPp hDG_CLOSINGRUN hOW hkidW

end GPForm

theorem auditE3B3_of_t1hypND_run_rows {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {declName : Name} {DataOk : Pkg ι dom → Prop}
    (hpkg : ∀ c, TgtRun P declName c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q)
    (hA6 : ∀ c, TgtRun P declName c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
        Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hcl : ∀ c, TgtRun P declName c → ∀ q : Pkg ι dom, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape)
    (hMemRow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen5AuditE3B3.MemParentDataOk q ∧ Tools.ShippingGen5AuditE3B3.ExtInS q)
    (hLeafAlias : ∀ q : Pkg ι dom, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {g : Tools.ShippingSrm7Rank.CallGraph} {B : Nat} {top : Name}
    (hin : Tools.ShippingSrm7Rank.InClass g B top = true)
    (hsp : Tools.ShippingGen5NameKids3.ReachSpans g top (TgtRun P declName))
    (hg : Tools.ShippingGen5NameKids3.GraphAgrees g (TgtRun P declName) (Tools.ShippingGen5AuditCarrier.SOf P)) :
    Tools.ShippingGen5AuditE3B3.AuditE3 P (TgtRun P declName) L ∧ Tools.ShippingGen5AuditE3B3.AuditB3 L P (TgtRun P declName) :=
  Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run (t1HypND_of_rows L P declName DataOk hpkg hA6 hcl)
    hMemRow hLeafAlias hA hin hsp hg

end Tools.ShippingGen5CR4

#print axioms Tools.ShippingGen5CR4.t1HypND_of_rows
#print axioms Tools.ShippingGen5CR4.servedShips0_runND_rows
#print axioms Tools.ShippingGen5CR4.postFacts_of_runND_rows
#print axioms Tools.ShippingGen5CR4.t1_of_stepPF_ND_rows
#print axioms Tools.ShippingGen5CR4.closingRun0_of_runT1_ND_rows
#print axioms Tools.ShippingGen5CR4.closingRun_of_runT1_ND_rows
#print axioms Tools.ShippingGen5CR4.hT2Tie_of_genGP_rows
#print axioms Tools.ShippingGen5CR4.auditE3B3_of_t1hypND_run_rows
