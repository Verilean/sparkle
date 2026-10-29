import Tools.ShippingGen5T2OutTy
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in g5to2-20d6dfd3 (clean, exit 0, 741 jobs; TYPE 5, MUTANT 8 signature/defeq rejections, closure controls 7 +
-- 5 roots, AXIOMS 5 standard). No sorry / axiom / native_decide.

/-! # T2-OUTTY checks (Tools/ShippingGen5T2OutTy.lean; DGEN_FREEZE.md §7.9 rev2.5, par/gen5-t2 505f3392)

1. Expected types (`checkExpected`) against independent FULLY BOUND telescopes; H4's are the §7.7 (c) / §7.8 binder
   lists with `houtTy` removed and `{Reach} {DataOk} H hRp hPp hord` inserted after `hk`, written out in full.
2. Mutants (`checkMutant`): signature / defeq rejections, NOT semantic counterexamples.
3. **Closure audit (no circularity through `T1Hyp.dec`)**: full reachable closure (type and explicit body of every
   reached constant, every namespace; opaque implementations not followed). A `T1Hyp` field is USED when its
   projection constant `T1Hyp.<field>` occurs or a raw `Expr.proj T1Hyp i` with that field's index occurs; whole
   destructuring (`T1Hyp.rec` / `casesOn` / `recOn`) is forbidden everywhere. Per root:
   H1 `houtTy_of_realChild`, H3 `houtTy_of_closing`: may use `defines` only; H2 `reach_callee_of_t1`: `closed` only;
   H4: `defines` and `closed` only. `dec`, `pkg`, `closes` are forbidden for all. Positive reachability: H1/H3/H4
   reach `outTy_of_core` and `synthesizeCombinational_reads`; H1/H3/H4 reach `T1Hyp.defines`; H2/H4 reach
   `T1Hyp.closed`. Detector controls: `dec` direct, `dec` through two helpers in other namespaces, `casesOn`
   direct, raw `.proj` index 3 (detector unit control on a synthetic term), an unrelated theorem (not flagged), and a
   `defines` user (not flagged under H1's set, flagged under H2's).
4. Axioms. CONDITIONAL: `hDG_CLOSINGRUN`, DG-SEM, `OneOutWidth`/`hkidW` stay inputs. Not M5/FG completion. -/

/-! ## 0. Detector fixtures -/
namespace Tests.Gen5.T2OutTyHelperA
/-- helper 1 (uses `T1Hyp.dec`) -/
theorem helperA : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.dec
end Tests.Gen5.T2OutTyHelperA

namespace Tests.Gen5.T2OutTyHelperB
/-- helper 2 (uses helper 1) -/
theorem helperB : True := Tests.Gen5.T2OutTyHelperA.helperA
end Tests.Gen5.T2OutTyHelperB

namespace Tests.Gen5.T2OutTyFixture
/-- control: direct `T1Hyp.dec` -/
theorem badDecDirect : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.dec
/-- control: `T1Hyp.dec` through two helpers in other namespaces -/
theorem badDecIndirect : True := Tests.Gen5.T2OutTyHelperB.helperB
/-- control: whole destructuring -/
theorem badCases : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.casesOn.{0}
/-- control: uses `T1Hyp.defines` (allowed for H1, forbidden for H2) -/
theorem usesDefines : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.defines
/-- control: unrelated -/
theorem goodUnrelated : True := trivial
end Tests.Gen5.T2OutTyFixture

namespace Tests.Gen5.T2OutTyCheck
open Lean Meta
open Tools.ShippingGen2
open Tests.Gen3.ExpectedType
open Sparkle.Core.Domain
open Sparkle.Core Sparkle.Core.Signal

/-! ## 1-2. Expected types and mutants -/

/-- (H1) §7.9 -/
def ExpH1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) {c : Lean.Name} {q : Pkg ι dom}
    {r : Tools.ShippingChildInv.Res} (hR : Reach c) (hq : P c = some q)
    (hy : Tools.ShippingChildCacheA.RealChildA L.O c r),
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width

/-- Mutant: without `hR` (callee not reached). -/
def MutH1NoReach : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) {c : Lean.Name} {q : Pkg ι dom}
    {r : Tools.ShippingChildInv.Res} (hq : P c = some q)
    (hy : Tools.ShippingChildCacheA.RealChildA L.O c r),
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width

/-- Mutant: `hy` at a different name `c'`. -/
def MutH1OtherName : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) {c c' : Lean.Name} {q : Pkg ι dom}
    {r : Tools.ShippingChildInv.Res} (hR : Reach c) (hq : P c = some q)
    (hy : Tools.ShippingChildCacheA.RealChildA L.O c' r),
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width

/-- (H2) §7.9 -/
def ExpH2 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) (p : Pkg ι dom) (hRp : Reach p.decl)
    (hPp : P p.decl = some p) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none),
    Reach (p.d.shape.insts[k]'hk).1

/-- Mutant: without `hord` (memory-origin calls included). -/
def MutH2NoOrd : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) (p : Pkg ι dom) (hRp : Reach p.decl)
    (hPp : P p.decl = some p) (k : Nat) (hk : k < p.d.shape.insts.length),
    Reach (p.d.shape.insts[k]'hk).1

/-- (H3) §7.9 -/
def ExpH3 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hRc : Reach (p.d.shape.insts[k]'hk).1)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1),
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width

/-- Mutant: without `hRc`. -/
def MutH3NoReach : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1),
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width

/-- (H4) one-output, §7.7 (c) telescope with `houtTy` replaced (fully bound) -/
def ExpH4One : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
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
def MutH4OneNoOrd : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (h1 : p.d.shape.instFields = []) (hOW : OneOutWidth P p k),
    CallTie p q k hk

/-- Mutant: without `hOW`. -/
def MutH4OneNoOW : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (h1 : p.d.shape.instFields = []),
    CallTie p q k hk

/-- (H4) group, §7.8 telescope with `houtTy` replaced (fully bound) -/
def ExpH4Kid : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
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
def MutH4KidNoOrd : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
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

/-- Mutant: without `hkidW`. -/
def MutH4KidNoKidW : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (hG : p.d.shape.instFields ≠ []),
    CallTie p q k hk

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``houtTy_of_realChild ``ExpH1
  checkExpected ``reach_callee_of_t1 ``ExpH2
  checkExpected ``houtTy_of_closing ``ExpH3
  checkExpected ``callTie_of_served_oneOut_t1 ``ExpH4One
  checkExpected ``callTie_of_served_kidW_closing_t1 ``ExpH4Kid
  checkMutant ``houtTy_of_realChild ``MutH1NoReach
  checkMutant ``houtTy_of_realChild ``MutH1OtherName
  checkMutant ``reach_callee_of_t1 ``MutH2NoOrd
  checkMutant ``houtTy_of_closing ``MutH3NoReach
  checkMutant ``callTie_of_served_oneOut_t1 ``MutH4OneNoOrd
  checkMutant ``callTie_of_served_oneOut_t1 ``MutH4OneNoOW
  checkMutant ``callTie_of_served_kidW_closing_t1 ``MutH4KidNoOrd
  checkMutant ``callTie_of_served_kidW_closing_t1 ``MutH4KidNoKidW

/-! ## 3. Closure audit -/

/-- `T1Hyp` field names in declaration order (Tools/ShippingGen2Defs.lean:194-214). -/
def t1Fields : List String := ["pkg", "defines", "closes", "dec", "closed"]

/-- Is `u` a use of a forbidden field (by projection constant) or whole destructuring? -/
def badConst (allowed : List String) (u : Name) : Bool :=
  (t1Fields.any fun f => !allowed.contains f && u == (``Tools.ShippingGen2.T1Hyp).str f) ||
  u == ``Tools.ShippingGen2.T1Hyp.rec || u == ``Tools.ShippingGen2.T1Hyp.casesOn ||
  u == ``Tools.ShippingGen2.T1Hyp.recOn

/-- Does `e` contain a raw `Expr.proj T1Hyp i` of a forbidden field? -/
def badProj (allowed : List String) (e : Lean.Expr) : Bool :=
  (e.find? fun x => match x with
    | .proj s i _ => s == ``Tools.ShippingGen2.T1Hyp && !allowed.contains (t1Fields.getD i "?")
    | _ => false).isSome

def body? : ConstantInfo → Option Lean.Expr
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

/-- Full reachable closure of `root` (types and explicit bodies). Stops at the first forbidden use. The projection
functions of ALLOWED fields are traversed (their bodies are the allowed `.proj`). -/
def reach (root : Name) (allowed : List String) (cap : Nat := 3000000) : MetaM AReach := do
  let env ← getEnv
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then
      throwError "T2OUTTY AUDIT INCOMPLETE at {root}: more than {cap} constants"
    let some ci := env.find? c | continue
    let body := body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques + 1 }
    let isAllowedProjFn := allowed.any fun f => c == (``Tools.ShippingGen2.T1Hyp).str f
    if !isAllowedProjFn && (badProj allowed ci.type || (body.map (badProj allowed)).getD false) then
      return { out with hit := some (path ++ [`rawProj]) }
    let used := ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[]
    for u in used do
      if badConst allowed u then
        return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- detector unit controls on synthetic terms
  unless badProj ["defines"] (.proj ``Tools.ShippingGen2.T1Hyp 3 (.bvar 0)) do
    throwError "T2OUTTY AUDIT FAILED: raw proj of dec not detected"
  if badProj ["defines"] (.proj ``Tools.ShippingGen2.T1Hyp 1 (.bvar 0)) then
    throwError "T2OUTTY AUDIT FAILED: raw proj of defines flagged under defines-only"
  logInfo "T2OUTTY CONTROL rawProj: index 3 flagged, index 1 not flagged under [defines]"
  -- closure-level controls with the SAME search
  for (c, allowed, bad) in [(``Tests.Gen5.T2OutTyFixture.badDecDirect, ["defines", "closed"], true),
      (``Tests.Gen5.T2OutTyFixture.badDecIndirect, ["defines", "closed"], true),
      (``Tests.Gen5.T2OutTyFixture.badCases, ["defines", "closed"], true),
      (``Tests.Gen5.T2OutTyFixture.usesDefines, ["defines"], false),
      (``Tests.Gen5.T2OutTyFixture.usesDefines, ["closed"], true),
      (``Tests.Gen5.T2OutTyFixture.goodUnrelated, ([] : List String), false)] do
    let r ← reach c allowed
    if bad && r.hit.isNone then throwError "T2OUTTY AUDIT FAILED: the detector misses {c} under {allowed}"
    if !bad && r.hit.isSome then throwError "T2OUTTY AUDIT FAILED: the detector flags {c} under {allowed}"
    logInfo m!"T2OUTTY CONTROL {c} under {allowed}: {toString r.hit}"
  -- audited roots
  let req1 := [``Tools.ShippingReaderOutsInv.outTy_of_core,
    ``Tools.ShippingPostSoundness.synthesizeCombinational_reads, ``Tools.ShippingGen2.T1Hyp.defines]
  for (c, allowed, req) in [(``houtTy_of_realChild, ["defines"], req1), (``houtTy_of_closing, ["defines"], req1),
      (``reach_callee_of_t1, ["closed"], [``Tools.ShippingGen2.T1Hyp.closed]),
      (``callTie_of_served_oneOut_t1, ["defines", "closed"], req1 ++ [``Tools.ShippingGen2.T1Hyp.closed]),
      (``callTie_of_served_kidW_closing_t1, ["defines", "closed"], req1 ++ [``Tools.ShippingGen2.T1Hyp.closed])] do
    let r ← reach c allowed
    if let some p := r.hit then
      throwError "T2OUTTY AUDIT FAILED {c}: forbidden T1Hyp use (allowed {allowed}) via {p}"
    for t in req do
      unless r.seen.contains t do
        throwError "T2OUTTY AUDIT FAILED {c}: {t} not reached"
    logInfo m!"T2OUTTY REACH {c}: T1Hyp fields used ⊆ {allowed}; no dec/pkg/closes/rec/casesOn; reaches {req} (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques}: opaque implementations not followed)"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``houtTy_of_realChild, ``reach_callee_of_t1, ``houtTy_of_closing, ``callTie_of_served_oneOut_t1,
      ``callTie_of_served_kidW_closing_t1] do
    checkAxioms n

end Tests.Gen5.T2OutTyCheck
