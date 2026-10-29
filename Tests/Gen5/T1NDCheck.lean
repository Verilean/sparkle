import Tools.ShippingGen5T1ND
import Tests.Gen3.ExpectedType
import Tests.Gen5.T2OutTyCheck
set_option autoImplicit false
-- Built in g5nd2-b1e4bdbf (clean, exit 0, 743 jobs; field pair 1, root pair 5, TYPE 5, MUTANT 8 signature/defeq
-- rejections, SIG 5 + control, closure controls 12, REACH 6, AXIOMS 6). No sorry / axiom / native_decide.

/-! # T1HypND / dec-free T2-OUTTY checks (Tools/ShippingGen5T1ND.lean; DGEN_FREEZE.md §7.10, par/gen5-t2 5f0b2a69)

Acceptance conditions against circularity (review of 5f0b2a69):
1. **Field pair**: `T1HypND.mk`'s telescope vs `T1Hyp.mk`'s with `dec` removed, on the SAME parameter fvars: field
   names, order, `binderInfo`, types (`isDefEq`), the same number of parameters, and NO extra field; plus the
   structure-field lists (`getStructureFields`) against the declared index tables `t1Fields` / `ndFields`.
2. **Root pair at `H.toND`**: for each §7.9 root `old` and ND root `nd`, on `old`'s telescope `xs` (with `H : T1Hyp …`
   at position `iH`), the PROPOSITION `nd xs[0..iH) (T1Hyp.toND H) xs(iH..]` has type `isDefEq` to `old`'s body, and
   `nd`'s telescope agrees with `old`'s binder by binder (names, `binderInfo`; types `isDefEq`, except at `iH` where it
   is `T1HypND` of the same arguments). Not a proof-term equality.
3. **Expected types** (fully bound) for the five ND roots; mutants: `H : T1Hyp` (the §7.9 statement), without `hord`.
   Rejections are signature / defeq rejections.
4. **Signature audit**: no binder type nor the conclusion of any ND root mentions `T1Hyp`, `T1Hyp.dec` or
   `T1Hyp.toND`; negative control `sigBad` (a `T1Hyp` binder) is flagged, positive control `sigGood` (`T1HypND`) not.
5. **Closure audit (ND roots)**: full reachable closure; forbidden: EVERY `T1Hyp` projection, raw `.proj T1Hyp _`,
   `T1Hyp.rec/casesOn/recOn`, `T1Hyp.toND`, the §7.9 roots; `T1HypND` fields other than the allowed ones (by projection
   constant or raw `.proj T1HypND i`), `T1HypND.rec/casesOn/recOn`. Allowed: H1/H3 `defines`, H2 `closed`, H4 both.
   **Adapter** `T1Hyp.toND`, separately: `T1Hyp` `pkg/defines/closes/closed` allowed, `dec` and the recursors
   forbidden. Controls for each rule.
6. Axioms. -/

/-! ## 0. Fixtures -/
namespace Tests.Gen5.T1NDFixture
open Tools.ShippingGen2
theorem oldProj : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.defines
theorem oldCases : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.casesOn.{0}
theorem adapterUse : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.toND
theorem oldRootUse : True := (fun _ => trivial) @Tools.ShippingGen2.houtTy_of_realChild
theorem ndPkg : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.pkg
theorem ndCases : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.casesOn.{0}
theorem ndDefines : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.defines
theorem decUse : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.dec
theorem unrelated : True := trivial
/-- signature negative control: a `T1Hyp` binder -/
theorem sigBad {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref cref} (L : Laws mref cref)
    (P : Pkgs ι dom) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop} (_H : T1Hyp L P Reach DataOk) : True :=
  trivial
/-- signature positive control: a `T1HypND` binder -/
theorem sigGood {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref cref} (L : Laws mref cref)
    (P : Pkgs ι dom) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop} (_H : T1HypND L P Reach DataOk) : True :=
  trivial
end Tests.Gen5.T1NDFixture

namespace Tests.Gen5.T1NDCheck
open Lean Meta
open Tools.ShippingGen2
open Tests.Gen3.ExpectedType
open Sparkle.Core.Domain
open Sparkle.Core Sparkle.Core.Signal

/-! ## 1. Field pair and index tables -/

def t1Fields : List String := ["pkg", "defines", "closes", "dec", "closed"]
def ndFields : List String := ["pkg", "defines", "closes", "closed"]

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let f1 := (getStructureFields env ``T1Hyp).toList.map (·.toString)
  let f2 := (getStructureFields env ``T1HypND).toList.map (·.toString)
  unless f1 == t1Fields do throwError "T1ND FIELD TABLE FAILED: T1Hyp fields {f1} ≠ table {t1Fields}"
  unless f2 == ndFields do throwError "T1ND FIELD TABLE FAILED: T1HypND fields {f2} ≠ table {ndFields}"
  unless t1Fields.filter (· != "dec") == ndFields do throwError "T1ND FIELD TABLE FAILED: ND ≠ T1Hyp minus dec"
  let some (.inductInfo i1) := env.find? ``T1Hyp | throwError "no T1Hyp"
  let some (.inductInfo i2) := env.find? ``T1HypND | throwError "no T1HypND"
  unless i1.numParams == i2.numParams do throwError "T1ND PAIR FAILED: numParams {i1.numParams} ≠ {i2.numParams}"
  let c1 ← getConstInfo ``T1Hyp.mk
  let c2 ← getConstInfo ``T1HypND.mk
  forallTelescope c1.type fun xs _ => do
    let ps := xs[:i1.numParams].toArray
    let t2 ← instantiateForall c2.type ps
    let mut t2 := t2
    let mut j : Nat := 0
    for x in xs[i1.numParams:].toArray do
      let ld ← x.fvarId!.getDecl
      if ld.userName.toString == "dec" then continue
      match t2 with
      | .forallE n ty b bi =>
        unless n == ld.userName do throwError "T1ND PAIR FAILED: field {j}: {n} ≠ {ld.userName}"
        unless bi == ld.binderInfo do throwError "T1ND PAIR FAILED: binderInfo of {n}"
        unless ← isDefEq ty ld.type do throwError "T1ND PAIR FAILED: type of {n}"
        t2 := b.instantiate1 x
        j := j + 1
      | _ => throwError "T1ND PAIR FAILED: T1HypND.mk has fewer fields than T1Hyp minus dec (at {ld.userName})"
    if t2.isForall then throwError "T1ND PAIR FAILED: T1HypND.mk has an EXTRA field"
    logInfo m!"T1ND FIELD PAIR OK: {j} fields = T1Hyp minus dec (names, order, binderInfo, types), no extra field; tables match getStructureFields"

/-! ## 2. Root pair at `H.toND` -/

def rootPairs : List (Name × Name) :=
  [(``houtTy_of_realChild, ``houtTy_of_realChildND), (``reach_callee_of_t1, ``reach_callee_of_t1ND),
   (``houtTy_of_closing, ``houtTy_of_closingND), (``callTie_of_served_oneOut_t1, ``callTie_of_served_oneOut_t1ND),
   (``callTie_of_served_kidW_closing_t1, ``callTie_of_served_kidW_closing_t1ND)]

def isT1Hyp (ty : Expr) : Bool := ty.getAppFn.isConstOf ``T1Hyp

run_cmd Lean.Elab.Command.liftTermElabM do
  for (old, nd) in rootPairs do
    let co ← getConstInfo old
    let cn ← getConstInfo nd
    forallTelescope co.type fun xs body => do
      let mut iH? : Option Nat := none
      for i in [:xs.size] do
        if isT1Hyp (← inferType xs[i]!) then iH? := some i
      let some iH := iH? | throwError "T1ND ROOT PAIR FAILED {old}: no T1Hyp binder"
      -- (a) proposition at H.toND
      let hnd ← mkAppM ``T1Hyp.toND #[xs[iH]!]
      let args := xs.set! iH hnd
      let e := mkAppN (← mkConstWithLevelParams nd) args
      let ty ← inferType e
      unless ← isDefEq ty body do throwError "T1ND ROOT PAIR FAILED {old}/{nd}: proposition at H.toND differs"
      -- (b) telescope, binder by binder
      let mut t := cn.type
      for i in [:xs.size] do
        let ld ← xs[i]!.fvarId!.getDecl
        match t with
        | .forallE n ty b bi =>
          unless n == ld.userName && bi == ld.binderInfo do
            throwError "T1ND ROOT PAIR FAILED {nd}: binder {i} name/info {n} vs {ld.userName}"
          if i == iH then
            unless ty.getAppFn.isConstOf ``T1HypND && ty.getAppArgs.size == ld.type.getAppArgs.size do
              throwError "T1ND ROOT PAIR FAILED {nd}: binder {i} is not T1HypND"
            for (a1, a2) in ty.getAppArgs.zip ld.type.getAppArgs do
              unless ← isDefEq a1 a2 do throwError "T1ND ROOT PAIR FAILED {nd}: T1HypND arguments differ"
            t := b.instantiate1 hnd
          else
            unless ← isDefEq ty ld.type do throwError "T1ND ROOT PAIR FAILED {nd}: binder {i} ({n}) type"
            t := b.instantiate1 xs[i]!
        | _ => throwError "T1ND ROOT PAIR FAILED {nd}: fewer binders"
      if t.isForall then throwError "T1ND ROOT PAIR FAILED {nd}: extra binder"
      unless ← isDefEq t body do throwError "T1ND ROOT PAIR FAILED {nd}: conclusion"
      logInfo m!"T1ND ROOT PAIR OK {old} / {nd}: proposition at H.toND and telescope agree (H at {iH})"

/-! ## 3. Expected types and mutants -/

/-- (H1) §7.9 -/
def ExpH1ND : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1HypND L P Reach DataOk) {c : Lean.Name} {q : Pkg ι dom}
    {r : Tools.ShippingChildInv.Res} (hR : Reach c) (hq : P c = some q)
    (hy : Tools.ShippingChildCacheA.RealChildA L.O c r),
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width


/-- (H2) §7.9 -/
def ExpH2ND : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1HypND L P Reach DataOk) (p : Pkg ι dom) (hRp : Reach p.decl)
    (hPp : P p.decl = some p) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none),
    Reach (p.d.shape.insts[k]'hk).1


/-- Mutant: without `hord` (memory-origin calls included). -/
def MutH2NoOrdND : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1HypND L P Reach DataOk) (p : Pkg ι dom) (hRp : Reach p.decl)
    (hPp : P p.decl = some p) (k : Nat) (hk : k < p.d.shape.insts.length),
    Reach (p.d.shape.insts[k]'hk).1


/-- (H3) §7.9 -/
def ExpH3ND : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1HypND L P Reach DataOk) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hRc : Reach (p.d.shape.insts[k]'hk).1)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1),
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width


/-- (H4) one-output, §7.7 (c) telescope with `houtTy` replaced (fully bound) -/
def ExpH4OneND : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (h1 : p.d.shape.instFields = []) (hOW : OneOutWidth P p k),
    CallTie p q k hk


/-- Mutant: without `hord`. -/
def MutH4OneNoOrdND : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (h1 : p.d.shape.instFields = []) (hOW : OneOutWidth P p k),
    CallTie p q k hk


/-- (H4) group, §7.8 telescope with `houtTy` replaced (fully bound) -/
def ExpH4KidND : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallTie p q k hk


/-- Mutant: without `hord`. -/
def MutH4KidNoOrdND : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallTie p q k hk


run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``houtTy_of_realChildND ``ExpH1ND
  checkExpected ``reach_callee_of_t1ND ``ExpH2ND
  checkExpected ``houtTy_of_closingND ``ExpH3ND
  checkExpected ``callTie_of_served_oneOut_t1ND ``ExpH4OneND
  checkExpected ``callTie_of_served_kidW_closing_t1ND ``ExpH4KidND
  checkMutant ``houtTy_of_realChildND ``Tests.Gen5.T2OutTyCheck.ExpH1
  checkMutant ``reach_callee_of_t1ND ``Tests.Gen5.T2OutTyCheck.ExpH2
  checkMutant ``houtTy_of_closingND ``Tests.Gen5.T2OutTyCheck.ExpH3
  checkMutant ``callTie_of_served_oneOut_t1ND ``Tests.Gen5.T2OutTyCheck.ExpH4One
  checkMutant ``callTie_of_served_kidW_closing_t1ND ``Tests.Gen5.T2OutTyCheck.ExpH4Kid
  checkMutant ``reach_callee_of_t1ND ``MutH2NoOrdND
  checkMutant ``callTie_of_served_oneOut_t1ND ``MutH4OneNoOrdND
  checkMutant ``callTie_of_served_kidW_closing_t1ND ``MutH4KidNoOrdND

/-! ## 4. Signature audit -/

def sigBadConsts : List Name := [``T1Hyp, ``T1Hyp.dec, ``T1Hyp.toND]

/-- Does the TYPE (every binder and the conclusion) of `n` mention a forbidden constant? -/
def sigHit (n : Name) : MetaM (Option Name) := do
  let ty := (← getConstInfo n).type
  return sigBadConsts.find? fun c => ty.getUsedConstants.contains c

def ndRoots : List Name := rootPairs.map (·.2)

run_cmd Lean.Elab.Command.liftTermElabM do
  if (← sigHit ``Tests.Gen5.T1NDFixture.sigBad).isNone then throwError "T1ND SIG AUDIT FAILED: sigBad not flagged"
  if (← sigHit ``Tests.Gen5.T1NDFixture.sigGood).isSome then throwError "T1ND SIG AUDIT FAILED: sigGood flagged"
  logInfo "T1ND SIG CONTROL: sigBad (T1Hyp binder) flagged, sigGood (T1HypND binder) not flagged"
  for n in ndRoots do
    if let some c ← sigHit n then throwError "T1ND SIG AUDIT FAILED {n}: signature mentions {c}"
    logInfo m!"T1ND SIG OK {n}: no T1Hyp / T1Hyp.dec / T1Hyp.toND in the signature"

/-! ## 5. Closure audit -/

structure Rule where
  allowNDFields : List String
  allowT1Fields : List String
  /-- extra forbidden constants (adapter, old roots) -/
  forbid : List Name

def badConst (r : Rule) (u : Name) : Bool :=
  (t1Fields.any fun f => !r.allowT1Fields.contains f && u == (``T1Hyp).str f) ||
  (ndFields.any fun f => !r.allowNDFields.contains f && u == (``T1HypND).str f) ||
  [``T1Hyp.rec, ``T1Hyp.casesOn, ``T1Hyp.recOn, ``T1HypND.rec, ``T1HypND.casesOn, ``T1HypND.recOn].contains u ||
  r.forbid.contains u

def badProj (r : Rule) (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .proj s i _ =>
      (s == ``T1Hyp && !r.allowT1Fields.contains (t1Fields.getD i "?")) ||
      (s == ``T1HypND && !r.allowNDFields.contains (ndFields.getD i "?"))
    | _ => false).isSome

def body? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure AReach where
  hit : Option (List Name) := none
  seen : NameSet := {}
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Nat := 0

def reach (root : Name) (r : Rule) (cap : Nat := 3000000) : MetaM AReach := do
  let env ← getEnv
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "T1ND AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | continue
    let body := body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques + 1 }
    if badProj r ci.type || (body.map (badProj r)).getD false then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if badConst r u then return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

def oldRoots : List Name := rootPairs.map (·.1)

def ndRule (allowed : List String) : Rule := { allowNDFields := allowed, allowT1Fields := [], forbid := ``T1Hyp.toND :: oldRoots }
def adapterRule : Rule := { allowNDFields := [], allowT1Fields := ["pkg", "defines", "closes", "closed"], forbid := [] }

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- raw-proj unit controls
  unless badProj (ndRule ["defines"]) (.proj ``T1Hyp 1 (.bvar 0)) do throwError "T1ND AUDIT FAILED: old raw proj missed"
  unless badProj (ndRule ["defines"]) (.proj ``T1HypND 0 (.bvar 0)) do throwError "T1ND AUDIT FAILED: ND pkg raw proj missed"
  if badProj (ndRule ["defines"]) (.proj ``T1HypND 1 (.bvar 0)) then throwError "T1ND AUDIT FAILED: ND defines raw proj flagged"
  unless badProj adapterRule (.proj ``T1Hyp 3 (.bvar 0)) do throwError "T1ND AUDIT FAILED: adapter dec raw proj missed"
  if badProj adapterRule (.proj ``T1Hyp 4 (.bvar 0)) then throwError "T1ND AUDIT FAILED: adapter closed raw proj flagged"
  logInfo "T1ND CONTROL rawProj: old T1Hyp idx1 / ND idx0 flagged under ND[defines]; ND idx1 not; adapter: idx3 flagged, idx4 not"
  let F := `Tests.Gen5.T1NDFixture
  for (c, rule, lbl, bad) in [(F ++ `oldProj, ndRule ["defines", "closed"], "ND", true),
      (F ++ `oldCases, ndRule ["defines", "closed"], "ND", true),
      (F ++ `adapterUse, ndRule ["defines", "closed"], "ND", true),
      (F ++ `oldRootUse, ndRule ["defines", "closed"], "ND", true),
      (F ++ `ndPkg, ndRule ["defines", "closed"], "ND", true),
      (F ++ `ndCases, ndRule ["defines", "closed"], "ND", true),
      (F ++ `ndDefines, ndRule ["defines"], "ND[defines]", false),
      (F ++ `ndDefines, ndRule ["closed"], "ND[closed]", true),
      (F ++ `decUse, adapterRule, "adapter", true),
      (F ++ `oldProj, adapterRule, "adapter", false),
      (F ++ `unrelated, ndRule [], "ND[]", false)] do
    let r ← reach c rule
    if bad && r.hit.isNone then throwError "T1ND AUDIT FAILED: detector misses {c} under {lbl}"
    if !bad && r.hit.isSome then throwError "T1ND AUDIT FAILED: detector flags {c} under {lbl}"
    logInfo m!"T1ND CONTROL {c} under {lbl}: {toString r.hit}"
  let req1 := [``Tools.ShippingReaderOutsInv.outTy_of_core,
    ``Tools.ShippingPostSoundness.synthesizeCombinational_reads, ``T1HypND.defines]
  for (c, rule, req) in [(``houtTy_of_realChildND, ndRule ["defines"], req1),
      (``houtTy_of_closingND, ndRule ["defines"], req1),
      (``reach_callee_of_t1ND, ndRule ["closed"], [``T1HypND.closed]),
      (``callTie_of_served_oneOut_t1ND, ndRule ["defines", "closed"], req1 ++ [``T1HypND.closed]),
      (``callTie_of_served_kidW_closing_t1ND, ndRule ["defines", "closed"], req1 ++ [``T1HypND.closed]),
      (``T1Hyp.toND, adapterRule, [``T1Hyp.pkg, ``T1Hyp.defines, ``T1Hyp.closes, ``T1Hyp.closed])] do
    let r ← reach c rule
    if let some p := r.hit then throwError "T1ND AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "T1ND AUDIT FAILED {c}: {t} not reached"
    logInfo m!"T1ND REACH {c}: ND fields ⊆ {rule.allowNDFields}, T1Hyp fields ⊆ {rule.allowT1Fields}, no recursor/forbidden constant; reaches {req} (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques})"

/-! ## 6. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in ``T1Hyp.toND :: ndRoots do
    checkAxioms n

end Tests.Gen5.T1NDCheck
