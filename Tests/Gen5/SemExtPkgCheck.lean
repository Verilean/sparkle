import Tools.ShippingGen5SemExtPkg
import Tests.Gen5.SemExtCheck
set_option autoImplicit false
-- Pod build exit 0 (kjob lake build Tests.Gen5.SemExtPkgCheck, 749 jobs) ONLY with the one-line S1 pattern fix of `callField_at` in Tools/ShippingGen5T2Tie.lean (43977202) applied as an UNCOMMITTED local patch: at 1c300db6 Tools.ShippingGen5T2Tie itself does not elaborate. Clean build is the coder's. No sorry/axiom/native_decide.
/-! # DG-SEM U5E check (Tools/ShippingGen5SemExtPkg.lean; scripts/gen5/DG_SEM_FREEZE_P4E.md §5.2, §6)

* TYPE    — `genExtAtCall_of_genSem` against `ExpGenExt`, written here from the sentence of §5.2 (same reducible-first comparer `checkExpected`).
* DEFBODY — the target `Tools.ShippingGen2.GenExtAtCall` compared BY BODY with `ExpBodyGenExt`, written from §0 (so the identity of the target's text is checked, not assumed).
* MUTANT  — well-typed single-change mutants of the statement, rejected by the same comparer: signature/defeq rejection, NOT a semantic counterexample.
            The statement has no conjunctive conclusion, so "conjunct dropped" has 0 entries.
* AXIOMS / CLOSURE / REACH — as in `Tests/Gen5/SemExtCheck.lean`; the negative-control fixtures (`withFixtures`) are reused from it and live only inside `withoutModifyingEnv`. -/
namespace Tests.Gen5.SemExtPkgCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto

def ExpGenExt : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Lean.Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hq : P (p.d.shape.insts[k]'hk).1 = some q)
    (hord : (originOf p.d k).child? = none),
    Tools.ShippingGen2.GenExtAtCall p q k hk

/-- the target's body, from §0 of the freeze -/
noncomputable def ExpBodyGenExt := fun {ι : Type} {dom : ι → DomainConfig} (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) =>
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → Tools.ShippingGen2.CallField p q k o →
    (q.src i (Tools.ShippingGen2.decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f →
    Tools.ShippingGen2.SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
      (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD MixedGateBinder.domain) f

def MutNoHord : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Lean.Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hq : P (p.d.shape.insts[k]'hk).1 = some q),
    Tools.ShippingGen2.GenExtAtCall p q k hk
def MutNoHp : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hq : P (p.d.shape.insts[k]'hk).1 = some q)
    (hord : (originOf p.d k).child? = none),
    Tools.ShippingGen2.GenExtAtCall p q k hk
def MutNoHq : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Lean.Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hord : (originOf p.d k).child? = none),
    Tools.ShippingGen2.GenExtAtCall p q k hk
def MutOrdNext : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Lean.Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hq : P (p.d.shape.insts[k]'hk).1 = some q)
    (hord : (originOf p.d (k + 1)).child? = none),
    Tools.ShippingGen2.GenExtAtCall p q k hk
def MutOrdSome : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Lean.Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hq : P (p.d.shape.insts[k]'hk).1 = some q)
    (hord : (originOf p.d k).child?.isSome = true),
    Tools.ShippingGen2.GenExtAtCall p q k hk
def MutHpGenOnly : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Lean.Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = SemPkg.gen (genSemGen (semOf P) X g))
    (hq : P (p.d.shape.insts[k]'hk).1 = some q)
    (hord : (originOf p.d k).child? = none),
    Tools.ShippingGen2.GenExtAtCall p q k hk
def MutHqOther : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Lean.Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hq : P p.decl = some q)
    (hord : (originOf p.d k).child? = none),
    Tools.ShippingGen2.GenExtAtCall p q k hk
def MutConclCallTie : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Lean.Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hq : P (p.d.shape.insts[k]'hk).1 = some q)
    (hord : (originOf p.d k).child? = none),
    Tools.ShippingGen2.CallOutRange p q k hk

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``genExtAtCall_of_genSem ``ExpGenExt
  let a ← stmtOf ``Tools.ShippingGen2.GenExtAtCall
  let x ← stmtOf ``ExpBodyGenExt
  cmpTele "GenExtAtCall (body)" a x
  logInfo m!"GEN5 EXTPKG DEFBODY OK GenExtAtCall against ExpBodyGenExt (body compared)"
  let mutants : List (Name × Name) :=
    [(``genExtAtCall_of_genSem, ``MutNoHord), (``genExtAtCall_of_genSem, ``MutNoHp), (``genExtAtCall_of_genSem, ``MutNoHq),
     (``genExtAtCall_of_genSem, ``MutOrdNext), (``genExtAtCall_of_genSem, ``MutOrdSome), (``genExtAtCall_of_genSem, ``MutHpGenOnly),
     (``genExtAtCall_of_genSem, ``MutHqOther), (``genExtAtCall_of_genSem, ``MutConclCallTie)]
  for (t, m) in mutants do checkMutant t m
  logInfo m!"GEN5 EXTPKG COUNTS: TYPE 1 theorem; DEFBODY 1 (GenExtAtCall); MUTANT {mutants.length} theorem mutants \
    (conclusion-conjunct dropped 0 (no conjunctive conclusion), hypothesis dropped 3, one-place changes 5 (k→k+1, isSome, hp genSemI→genSemGen, hq callee→p.decl, conclusion→CallOutRange)); \
    signature/defeq rejections, NOT semantic counterexamples."

run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``genExtAtCall_of_genSem
  logInfo m!"GEN5 EXTPKG AXIOMS OK: 1 constant, standard axioms only"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name := [``genExtAtCall_of_genSem]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 EXTPKG CLOSURE FAILED: forbidden constants {f}"
  -- negative controls (fixtures only inside withoutModifyingEnv, reused from SemExtCheck)
  let t1 ← (do let _ ← closureRun [`Tests.Gen5.SemExtPkgCheck.NoSuchConstant]; pure false) <|> pure true
  unless t1 do throwError "GEN5 EXTPKG CONTROL FAILED: unknown root did not throw"
  for r in [``Lean.ofReduceBool, ``sorryAx] do
    let f ← detect [r]
    unless f.contains r do throwError "GEN5 EXTPKG CONTROL FAILED: forbidden root {r} not flagged (got {f})"
  Tests.Gen5.SemExtCheck.withFixtures fun r3 r4 rc mv mt hv4 => do
    let env ← getEnv
    let t3 ← (do let _ ← closureRun [r3]; pure false) <|> pure true
    unless t3 do throwError "GEN5 EXTPKG CONTROL FAILED: unknown helper value did not throw"
    let (_, c3) ← (closureOf env r3).run {}
    unless c3.missing == #[mv] do throwError "GEN5 EXTPKG CONTROL FAILED: helper-value case reported {c3.missing}, intended {mv}"
    let t4 ← (do let _ ← closureRun [r4]; pure false) <|> pure true
    unless t4 do throwError "GEN5 EXTPKG CONTROL FAILED: unknown helper type did not throw"
    let (_, c4) ← (closureOf env r4).run {}
    unless c4.missing == #[mt] do throwError "GEN5 EXTPKG CONTROL FAILED: helper-type case reported {c4.missing}, intended {mt}"
    unless c4.seen.contains hv4 do throwError "GEN5 EXTPKG CONTROL FAILED: helper-type path does not pass through Hv4"
    let cc ← closureRun [rc]
    unless cc.missing.isEmpty && (forbiddenIn cc).isEmpty do throwError "GEN5 EXTPKG CONTROL FAILED: clean fixture flagged"
  logInfo m!"GEN5 EXTPKG CLOSURE OK: {c.seen.toList.length} constants over 1 root, no forbidden constant; controls: unknown root throws, 2 forbidden roots flagged, \
    unknown helper VALUE names Mv, unknown helper TYPE names Mt via Hv4, clean fixture passes (fixtures inside withoutModifyingEnv)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let c ← closureRun [``genExtAtCall_of_genSem]
  let need : List Name := [``ext_call_final_bool, ``ext_call_final_bits, ``calleeOut_eq_src, ``selIdx_of_callField,
    ``Tools.ShippingGen2.t2r_ok_outNames_nodup, ``lsrcAt_genSemGen, ``Tools.ShippingGen2.GenExtAtCall]
  for n in need do
    unless c.seen.contains n do throwError "GEN5 EXTPKG REACH FAILED: genExtAtCall_of_genSem does not reach {n}"
  logInfo m!"GEN5 EXTPKG REACH OK: {need.length} required constants reached"

#print axioms genExtAtCall_of_genSem

end Tests.Gen5.SemExtPkgCheck
