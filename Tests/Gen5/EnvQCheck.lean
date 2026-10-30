import Tools.ShippingGen5EnvQ
import Tests.Gen5.EnvCheck
set_option autoImplicit false
-- NOT BUILT yet.

/-! # DG-ENV unit (d) checks (Tools/ShippingGen5EnvQ.lean; scripts/gen5/DG_ENV_FREEZE.md rev2.2 §4.5)

1. TYPE: `QuietStrength`, `AdmDown` against independent copies; Q1-Q10 against the freeze statements.
2. MUTANT (signature/defeq rejections, NOT semantic counterexamples): `QuietStrength` with `→` for `↔`; Q4 without
   `hd`; Q8 stated for `T1Hyp` (with `dec`); Q9 concluding `JQC L'.O 0 w₀` (cache half); Q10 without `hA'`.
3. CLOSURE, three rules (named projection, raw `.proj`, recursor):
   - rule A (Q1-Q7, Q9): no `RefLawsAOps` field other than `quiet`, no `RefLawsATele` field, no `Laws.T`, no
     `T1Hyp`/`T1HypND` field;
   - rule B (Q8): as A, but the `T1HypND` fields (and its constructor) are allowed; `T1Hyp` fields stay forbidden;
   - rule C (Q10): `RefLawsAOps` fields allowed (RR1 at the given `L'`); no `RefLawsATele` field, no `Laws.T`, no
     `T1Hyp`/`T1HypND` field;
   - all rules: no `GetEnvFrame`/`ReadKeeps`/`EnvSnapshot`.
   Controls per rule (each forbidden control also hits its intended constant alone; allowed controls are NOT flagged).
4. Axioms. -/

/-! ## 0. Fixtures -/
namespace Tests.Gen5.EnvQFixture
theorem badLawsT : True := (fun _ => trivial) @Tools.ShippingGen2.Laws.T
theorem badT1Dec : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.dec
theorem okQuiet : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.quiet
theorem okLawsO : True := (fun _ => trivial) @Tools.ShippingGen2.Laws.O
end Tests.Gen5.EnvQFixture

namespace Tests.Gen5.EnvQCheck
open Lean Meta
open Sparkle.Core.Domain (DomainConfig)
open Sparkle.Compiler.Elab (MachineShape)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingChildCacheA (RealChildA CacheInvA JQC)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingGen2 (Laws Start Pkgs Pkg T1HypND T1Hyp)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvQ
open Tests.Gen3.ExpectedType

/-! ## 1. Expected types -/
def ExpQuietStrength {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) : Prop :=
  ∀ w, L'.O.quiet w ↔ (L.O.quiet w ∧ ReadsAt env₀ cref w)

def MutQuietStrengthImp {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) : Prop :=
  ∀ w, L'.O.quiet w → (L.O.quiet w ∧ ReadsAt env₀ cref w)

def ExpAdmDown {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L'.O.quiet mctx cctx → AdmCtx L.O.quiet mctx cctx

def ExpQ1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) {w : Void IO.RealWorld} (h : L'.O.quiet w), L.O.quiet w

def ExpQ2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) {w : Void IO.RealWorld} (h : L'.O.quiet w),
    ReadsAt env₀ cref w

def ExpQ3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) {D : Nat} {w : Void IO.RealWorld}
    (h : JQ L'.O.quiet D w), JQ L.O.quiet D w

def ExpQ4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) (hd : AdmDown L L') {c : Name} {r : Res}
    (h : RealChildA L'.O c r), RealChildA L.O c r

def MutQ4NoHd : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) {c : Name} {r : Res}
    (h : RealChildA L'.O c r), RealChildA L.O c r

def ExpQ5 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) (hd : AdmDown L L') {m : Std.HashMap Name Res}
    (h : CacheInvA L'.O m), CacheInvA L.O m

def ExpQ6 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) (hd : AdmDown L L') {D : Nat} {w : Void IO.RealWorld}
    (h : JQC L'.O D w), JQC L.O D w

def ExpQ7 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) (hd : AdmDown L L') {mctx : Meta.Context}
    {cctx : Core.Context} {c : Name} {shape : MachineShape}
    (h : MachineClosesAtA L.O mctx cctx c shape), MachineClosesAtA L'.O mctx cctx c shape

def ExpQ8 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) (hd : AdmDown L L') {P : Pkgs ι dom}
    {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk), T1HypND L' P Reach DataOk

def MutQ8T1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {env₀ : Environment} (hq : QuietStrength L L' env₀) (hd : AdmDown L L') {P : Pkgs ι dom}
    {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk), T1Hyp L' P Reach DataOk

def ExpQ9 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀), JQ L'.O.quiet 0 w₀

def MutQ9JQC : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ : Void IO.RealWorld}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀), JQC L'.O 0 w₀

def ExpQ10 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ w1 : Void IO.RealWorld} {X : Name}
    {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hq : QuietStrength L L' (envAt cref w₀)) (hA' : AdmCtx L'.O.quiet mctx cctx) (hS : Start L mctx cctx w₀)
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w₀ s w1),
    JQC L'.O 1 w1 ∧ ReadsAt (envAt cref w₀) cref w1

def MutQ10NoHA : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {mctx : Meta.Context} {cctx : Core.Context} {w₀ w1 : Void IO.RealWorld} {X : Name}
    {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hq : QuietStrength L L' (envAt cref w₀)) (hS : Start L mctx cctx w₀)
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w₀ s w1),
    JQC L'.O 1 w1 ∧ ReadsAt (envAt cref w₀) cref w1

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``QuietStrength ``ExpQuietStrength
  checkExpected ``AdmDown ``ExpAdmDown
  checkExpected ``quiet_down ``ExpQ1
  checkExpected ``readsAt_of_quiet ``ExpQ2
  checkExpected ``jq_down ``ExpQ3
  checkExpected ``realChildA_down ``ExpQ4
  checkExpected ``cacheInvA_down ``ExpQ5
  checkExpected ``jqc_down ``ExpQ6
  checkExpected ``closesA_up ``ExpQ7
  checkExpected ``t1HypND_up ``ExpQ8
  checkExpected ``jq_start ``ExpQ9
  checkExpected ``head_jqc_start ``ExpQ10
  checkMutant ``QuietStrength ``MutQuietStrengthImp
  checkMutant ``realChildA_down ``MutQ4NoHd
  checkMutant ``t1HypND_up ``MutQ8T1
  checkMutant ``jq_start ``MutQ9JQC
  checkMutant ``head_jqc_start ``MutQ10NoHA

/-! ## 2. Closure audit, three rules -/
def fieldsOf (s : Name) : MetaM (List Name) := do
  let fs := getStructureFields (← getEnv) s
  if fs.isEmpty then throwError "ENVQ AUDIT FAILED: {s} has no fields"
  return fs.toList.map (s ++ ·)

def recsOf (s : Name) : List Name := [s ++ `rec, s ++ `casesOn, s ++ `recOn]

structure Rule where
  name : String
  forbid : List Name
  /-- raw projections forbidden: (structure, allowed indices) -/
  rawAllow : List (Name × List Nat)

def ops := ``Tools.ShippingChildInvA.RefLawsAOps
def tele := ``Tools.ShippingChildInvA.RefLawsATele
def laws := ``Tools.ShippingGen2.Laws
def t1 := ``Tools.ShippingGen2.T1Hyp
def nd := ``Tools.ShippingGen2.T1HypND
def envBad : List Name :=
  [``Tools.ShippingEnvSnapshot.GetEnvFrame, ``Tools.ShippingStRefCorrespondence.ReadKeeps,
   ``Tools.ShippingEntryReadsLinked.EnvSnapshot]

def mkRules : MetaM (Rule × Rule × Rule) := do
  let opsF ← fieldsOf ops
  let teleF ← fieldsOf tele
  let t1F ← fieldsOf t1
  let ndF ← fieldsOf nd
  let opsNoQuiet := opsF.filter (· != ops ++ `quiet)
  let common := teleF ++ recsOf tele ++ [laws ++ `T] ++ t1F ++ recsOf t1 ++ envBad
  let ruleA : Rule := { name := "A", forbid := common ++ opsNoQuiet ++ recsOf ops ++ ndF ++ recsOf nd,
    rawAllow := [(ops, [0]), (laws, [0]), (tele, []), (t1, []), (nd, [])] }
  let ruleB : Rule := { name := "B", forbid := common ++ opsNoQuiet ++ recsOf ops,
    rawAllow := [(ops, [0]), (laws, [0]), (tele, []), (t1, []), (nd, [0, 1, 2, 3])] }
  let ruleC : Rule := { name := "C", forbid := common ++ ndF ++ recsOf nd,
    rawAllow := [(ops, (List.range 64)), (laws, [0]), (tele, []), (t1, []), (nd, [])] }
  return (ruleA, ruleB, ruleC)

def badProj (R : Rule) (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .proj s i _ => match R.rawAllow.find? (·.1 == s) with
      | some (_, ok) => !ok.contains i
      | none => false
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

def reach (R : Rule) (root : Name) (cap : Nat := 3000000) : MetaM AReach := do
  let env ← getEnv
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i : Nat := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "ENVQ AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | continue
    let body := body? ci
    if badProj R ci.type || (body.map (badProj R)).getD false then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if R.forbid.contains u then return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let (rA, rB, rC) ← mkRules
  -- raw projection controls
  unless badProj rA (.proj ops 1 (.bvar 0)) do throwError "ENVQ AUDIT FAILED: rule A misses raw RefLawsAOps.1"
  if badProj rA (.proj ops 0 (.bvar 0)) then throwError "ENVQ AUDIT FAILED: rule A flags raw quiet"
  unless badProj rA (.proj nd 1 (.bvar 0)) do throwError "ENVQ AUDIT FAILED: rule A misses raw T1HypND"
  if badProj rB (.proj nd 1 (.bvar 0)) then throwError "ENVQ AUDIT FAILED: rule B flags raw T1HypND"
  unless badProj rB (.proj t1 3 (.bvar 0)) do throwError "ENVQ AUDIT FAILED: rule B misses raw T1Hyp"
  if badProj rC (.proj ops 5 (.bvar 0)) then throwError "ENVQ AUDIT FAILED: rule C flags raw RefLawsAOps"
  unless badProj rC (.proj tele 0 (.bvar 0)) do throwError "ENVQ AUDIT FAILED: rule C misses raw RefLawsATele"
  unless badProj rC (.proj laws 1 (.bvar 0)) do throwError "ENVQ AUDIT FAILED: rule C misses raw Laws.T"
  logInfo "ENVQ CONTROL rawProj: A (ops.1, nd flagged; quiet not), B (nd not, T1Hyp flagged), C (ops not; tele, Laws.1 flagged)"
  let E := `Tests.Gen5.EnvFixture
  let Q := `Tests.Gen5.EnvQFixture
  -- (rule, control, intended forbidden constant or none = must NOT be flagged)
  let controls : List (Rule × Name × Option Name) :=
    [(rA, E ++ `badOps, some (ops ++ `frame)), (rA, E ++ `badND, some (nd ++ `defines)),
     (rA, E ++ `badTele2, some (tele ++ `telescope)), (rA, Q ++ `badLawsT, some (laws ++ `T)),
     (rA, E ++ `badGetEnvFrame, some ``Tools.ShippingEnvSnapshot.GetEnvFrame),
     (rA, Q ++ `okQuiet, none), (rA, Q ++ `okLawsO, none), (rA, E ++ `unrelated, none),
     (rB, Q ++ `badT1Dec, some (t1 ++ `dec)), (rB, E ++ `badOps, some (ops ++ `frame)),
     (rB, E ++ `badT1, some (t1 ++ `defines)),
     (rC, E ++ `badND, some (nd ++ `defines)), (rC, E ++ `badTele2, some (tele ++ `telescope)),
     (rC, Q ++ `badLawsT, some (laws ++ `T)), (rC, E ++ `badReadKeeps, some ``Tools.ShippingStRefCorrespondence.ReadKeeps),
     (rC, E ++ `badOps, none)]
  for (R, c, tgt) in controls do
    let r ← reach R c
    match tgt with
    | some t =>
      if r.hit.isNone then throwError "ENVQ AUDIT FAILED: rule {R.name} misses {c}"
      unless R.forbid.contains t do throwError "ENVQ AUDIT FAILED: intended {t} not in rule {R.name}"
      let rt ← reach { R with forbid := [t], rawAllow := [] } c
      unless rt.hit.map (·.getLast? == some t) == some true do
        throwError "ENVQ AUDIT FAILED: {c} does not reach its intended {t}"
      logInfo m!"ENVQ CONTROL rule {R.name} {c}: flagged {toString r.hit}; intended {t} alone {toString rt.hit}"
    | none =>
      if let some p := r.hit then throwError "ENVQ AUDIT FAILED: rule {R.name} flags allowed {c} via {p}"
      logInfo m!"ENVQ CONTROL rule {R.name} {c}: allowed, not flagged"
  let roots : List (Rule × Name × List Name) :=
    [(rA, ``quiet_down, [``QuietStrength]), (rA, ``readsAt_of_quiet, [``QuietStrength]),
     (rA, ``jq_down, [``quiet_down]), (rA, ``realChildA_down, [``AdmDown, ``quiet_down]),
     (rA, ``cacheInvA_down, [``realChildA_down]), (rA, ``jqc_down, [``jq_down, ``cacheInvA_down]),
     (rA, ``closesA_up, [``jqc_down, ``MachineClosesAtA]),
     (rB, ``t1HypND_up, [``closesA_up, nd ++ `defines, nd ++ `closes]),
     (rA, ``jq_start, [``Tools.ShippingGen5Env.readsAt_self, ``Start]),
     (rC, ``head_jqc_start, [``Tools.ShippingGen5RunReads.coreHead_jqcA, ``jq_start, ``readsAt_of_quiet])]
  for (R, c, req) in roots do
    let r ← reach R c
    if let some p := r.hit then throwError "ENVQ AUDIT FAILED {c} (rule {R.name}): forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "ENVQ AUDIT FAILED {c}: {t} not reached"
    logInfo m!"ENVQ REACH {c} (rule {R.name}): clean; reaches {req} (visited {r.visited})"

/-! ## 3. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``quiet_down, ``readsAt_of_quiet, ``jq_down, ``realChildA_down, ``cacheInvA_down, ``jqc_down,
      ``closesA_up, ``t1HypND_up, ``jq_start, ``head_jqc_start] do
    checkAxioms n

end Tests.Gen5.EnvQCheck
