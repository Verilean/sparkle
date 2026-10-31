import Lean
import Tools.ShippingGen5DCEntryW
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- NOT BUILT: checks of U-ENTRYW (freeze 38259f62 approved). Build is the coder's.

/-! # DC-CONNECT U-ENTRYW: checks (scripts/gen5/DC_CONNECT_NEXT_UNIT_FREEZE.md §3, §4)

TYPE: `ExpW1`/`ExpW2` written from the prose of §3 (a witness gives `Start` and either the default core run tied to the same-branch
`PostEntry`, or the parametrised run itself), not copied from the Lean statements; compared by `Tests.Gen3.ExpectedType.checkExpected`.
MUTANT: well-typed ONE-change variants rejected by the SAME comparator (`checkMutant`), both under `withReducible` -- signature/defeq
rejections, NOT semantic counterexamples. CONJ: variants dropping a conjunct/disjunct, counted separately (the `Start`-drop is counted
under CONJ only). A variant that is not well-typed is not counted. AXIOMS. CLOSURE: the `DeclConnectCheck` walker (root judged itself,
an unknown name FAILS), plus fixtures where ONLY a helper's TYPE, or ONLY a helper's VALUE, mentions an unknown name. -/
open Lean Meta Tests.Gen3.ExpectedType Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen5DCEntryW
open Tools.ShippingGen5DCEntryD (PostEntry)

namespace Tests.Gen5.DCEntryWCheck

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsg := Sparkle.IR.AST.Design

/-- EXPECTED (from the prose: Start, and either the default core run with the same-branch PostEntry, or the parametrised run itself). -/
def ExpW1 : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧
    ((∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D') ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w')

/-- MUTANT: `PostEntry` with `D` and `D'` swapped. -/
def MutW1SwapD : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧
    ((∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D' D) ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w')

/-- MUTANT: the two routes joined by `∧`. -/
def MutW1And : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧
    ((∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D') ∧
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w')

/-- MUTANT: the parametrised run with `[]` instead of `parameters`. -/
def MutW1ParamNil : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧
    ((∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D') ∨
     RunsTo (synthesizeCombinationalWithParameters declName []) mctx mref cctx cref w (b, D') w')

/-- MUTANT: the core run with `parameters`/`true`. -/
def MutW1CoreArgs : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧
    ((∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName parameters true) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D') ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w')

/-- MUTANT: the parametrised run ends at the start world `w`. -/
def MutW1WorldEnd : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧
    ((∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D') ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w)

/-- MUTANT: the core run starts at the end world. -/
def MutW1CoreWorld : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧
    ((∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w' (raw, D) w1 ∧ PostEntry b raw D D') ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w')

/-- CONJ: `Start` dropped. -/
def ConjW1NoStart : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    ((∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D') ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w')

/-- CONJ: only the default-route disjunct. -/
def ConjW1OnlyLeft : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧ (∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D')

/-- CONJ: only the parametrised disjunct. -/
def ConjW1OnlyParam : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧ RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w'

/-- CONJ: the `PostEntry` conjunct of the default disjunct dropped. -/
def ConjW1NoPE : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D'),
    Start L mctx cctx w ∧
    ((∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld), RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1) ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w')

/-- EXPECTED (from the prose: a witness whose default run is given yields Start and the core run with PostEntry). -/
def ExpW2 : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    Start L mctx cctx w ∧
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'

/-- MUTANT: `PostEntry` with `D` and `D'` swapped. -/
def MutW2SwapD : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    Start L mctx cctx w ∧
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D' D

/-- MUTANT: the core run with `parameters`/`true`. -/
def MutW2Flag : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    Start L mctx cctx w ∧
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName parameters true) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'

/-- MUTANT: the core run starts at the end world. -/
def MutW2CoreWorld : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    Start L mctx cctx w ∧
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w' (raw, D) w1 ∧ PostEntry b raw D D'

/-- MUTANT: `hl` stated for the parametrised route. -/
def MutW2HlParam : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D') w'),
    Start L mctx cctx w ∧
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'

/-- MUTANT: `hl` ends at the start world. -/
def MutW2HlWorld : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w),
    Start L mctx cctx w ∧
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'

/-- MUTANT: `∃ raw` -> `∀ raw`. -/
def MutW2Forall : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    Start L mctx cctx w ∧
    ∀ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'

/-- CONJ: `Start` dropped. -/
def ConjW2NoStart : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 ∧ PostEntry b raw D D'

/-- CONJ: only `Start`. -/
def ConjW2OnlyStart : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    Start L mctx cctx w

/-- CONJ: the `PostEntry` conjunct dropped. -/
def ConjW2NoPE : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    Start L mctx cctx w ∧
    ∃ (raw : Mod) (D : Dsg) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1

/-- CONJ: the core-run conjunct dropped. -/
def ConjW2NoCore : Prop := ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Mod} {D' : Dsg}
    (h : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D')
    (hl : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'),
    Start L mctx cctx w ∧
    ∃ (raw : Mod) (D : Dsg) (_w1 : Void IO.RealWorld), PostEntry b raw D D'

/-- (target, expected, mutants) -/
def table : List (Name × Name × List Name) :=
  [(``entryWitness_postEntry, ``ExpW1,
     [``MutW1SwapD, ``MutW1And, ``MutW1ParamNil, ``MutW1CoreArgs, ``MutW1WorldEnd, ``MutW1CoreWorld]),
   (``entryWitness_left_postEntry, ``ExpW2,
     [``MutW2SwapD, ``MutW2Flag, ``MutW2CoreWorld, ``MutW2HlParam, ``MutW2HlWorld, ``MutW2Forall])]

/-- conjunct/disjunct-drop variants, counted as category CONJ -/
def conjTable : List (Name × List Name) :=
  [(``entryWitness_postEntry, [``ConjW1NoStart, ``ConjW1OnlyLeft, ``ConjW1OnlyParam, ``ConjW1NoPE]),
   (``entryWitness_left_postEntry, [``ConjW2NoStart, ``ConjW2OnlyStart, ``ConjW2NoPE, ``ConjW2NoCore])]

/-! ## closure -/
open Tests.Gen5.DeclConnectCheck (reach reachRaw violations)

/-- per root: the constants the statement and proof must reach -/
def requiredOf : List (Name × List Name) :=
  [(``entryWitness_postEntry, [``EntryWitness, ``PostEntry, ``Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry,
      ``synthesizeCombinationalWithParameters]),
   (``entryWitness_left_postEntry, [``EntryWitness, ``PostEntry, ``Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry,
      ``synthesizeCombinationalCore])]

def missingOf (r : Tests.Gen5.DeclConnectCheck.Reach) (req : List Name) : List Name := req.filter (!r.seen.contains ·)

/-- negative control: mentions `EntryWitness` but never the entry lemma (the missing requirement must be detected) -/
def negNoLemma {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (R : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref) (n : Name) (ps : List (String × Nat))
    (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (b : Mod) (D : Dsg) : Prop :=
  EntryWitness R L n ps mctx cctx w w' b D
/-- clean control: the first theorem, through a helper -/
theorem cleanW {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {R : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref} {n : Name} {ps : List (String × Nat)}
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Mod} {D : Dsg}
    (h : EntryWitness R L n ps mctx cctx w w' b D) : Start L mctx cctx w := (entryWitness_postEntry h).1

/-- unknown-name fixtures: the helper's TYPE alone, resp. its VALUE alone, mentions a name known to no environment -/
def ghostTy : Name := `Tests.Gen5.DCEntryWCheck.ghost_unknown_in_type
def ghostVal : Name := `Tests.Gen5.DCEntryWCheck.ghost_unknown_in_value
def fixEnv (env : Environment) : MetaM Environment := do
  let add (env : Environment) (n : Name) (ty v : Lean.Expr) : MetaM Environment :=
    match env.addDeclCore 0 (.defnDecl { name := n, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe }) none (doCheck := false) with
    | .ok e => pure e
    | .error _ => throwError "fixture environment: could not add {n}"
  let nat := Lean.mkConst ``Nat
  let env ← add env `fixHelperTy (Lean.mkConst ghostTy) (Lean.mkConst ``Nat.zero)
  let env ← add env `fixHelperVal nat (Lean.mkConst ghostVal)
  let env ← add env `fixRootUsesTy nat (Lean.mkApp (Lean.mkConst ``id [1]) (Lean.mkConst `fixHelperTy))
  let env ← add env `fixRootUsesVal nat (Lean.mkApp (Lean.mkConst ``id [1]) (Lean.mkConst `fixHelperVal))
  add env `fixRootClean nat (Lean.mkConst ``Nat.zero)

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut nType : Nat := 0
  let mut nMut : Nat := 0
  let mut nConj : Nat := 0
  -- positive controls: the comparator accepts a copy of the expected statement
  withReducible <| checkExpected ``ExpW1 ``ExpW1
  withReducible <| checkExpected ``ExpW2 ``ExpW2
  for (thm, e, ms) in table do
    withReducible <| checkExpected thm e
    nType := nType + 1
    for m in ms do
      withReducible <| checkMutant thm m
      nMut := nMut + 1
  for (thm, ms) in conjTable do
    let some (_, e, _) := table.find? (·.1 == thm) | throwError "no expected for {thm}"
    withReducible <| checkExpected thm e
    for m in ms do
      withReducible <| checkMutant thm m
      nConj := nConj + 1
  let targets := [``entryWitness_postEntry, ``entryWitness_left_postEntry]
  for n in targets do checkAxioms n
  -- CLOSURE
  let mut nClosure : Nat := 0
  for (n, req) in requiredOf do
    let r ← reach env n
    unless r.axioms.isEmpty do throwError "CLOSURE FAILED {n}: axiom constants {r.axioms}"
    let v := violations env r
    unless v.isEmpty do throwError "CLOSURE FAILED {n}: forbidden {v}"
    let miss := missingOf r req
    unless miss.isEmpty do throwError "CLOSURE FAILED {n}: required constants not reached {miss}"
    nClosure := nClosure + 1
    logInfo m!"CLOSURE OK {n}: reached {r.seen.size}, opaque {r.opaques}, required {req}"
  let lemmaN := ``Tools.ShippingGen5DCEntryD.synthesizeCombinational_postEntry
  let rn ← reach env ``negNoLemma
  unless (missingOf rn [lemmaN]).contains lemmaN do
    throwError "CLOSURE CONTROL NOT DETECTED negNoLemma"
  logInfo m!"CLOSURE CONTROL DETECTED negNoLemma (entry lemma not reached)"
  let rc ← reach env ``cleanW
  unless (violations env rc).isEmpty && (missingOf rc [lemmaN, ``EntryWitness]).isEmpty do
    throwError "CLOSURE CLEAN CONTROL FAILED"
  logInfo m!"CLOSURE CLEAN CONTROL OK cleanW"
  unless (violations env (← reach env ``Tests.Gen5.DeclConnectCheck.negDirect)).isEmpty == false do
    throwError "CLOSURE CONTROL NOT DETECTED negDirect (forbidden mention)"
  logInfo m!"CLOSURE CONTROL DETECTED negDirect (forbidden mention)"
  -- unknown-name fixtures, in a scratch environment (the real one is restored by withoutModifyingEnv)
  withoutModifyingEnv do
    setEnv (← fixEnv env)
    let envF ← getEnv
    for (root, ghost, what) in [(`fixRootUsesTy, ghostTy, "TYPE"), (`fixRootUsesVal, ghostVal, "VALUE")] do
      let raw ← reachRaw envF root
      unless raw.unknown == #[ghost] do
        throwError "UNKNOWN-NAME FIXTURE: expected exactly {ghost} unknown (the helper's {what}), got {raw.unknown}"
      let failed ← try let _ ← reach envF root; pure false catch _ => pure true
      unless failed do throwError "UNKNOWN-NAME FIXTURE: `reach` did not fail for {root}"
      logInfo m!"UNKNOWN-NAME FIXTURE DETECTED {root} (only the helper's {what} is unknown: {raw.unknown}), reach fails"
    let rcl ← reach envF `fixRootClean
    unless rcl.unknown.isEmpty do throwError "UNKNOWN-NAME FIXTURE CLEAN CONTROL FAILED"
    logInfo m!"UNKNOWN-NAME FIXTURE CLEAN CONTROL OK fixRootClean"
  -- inspect the CURRENT environment (after `withoutModifyingEnv`), not the saved `env`
  let cur ← getEnv
  unless [`fixHelperTy, `fixHelperVal, `fixRootUsesTy, `fixRootUsesVal, `fixRootClean].all (cur.find? · |>.isNone) do
    throwError "fixture leaked into the environment"
  logInfo m!"COUNTS: TYPE {nType} (one per theorem; plus 2 positive-control self-comparisons not counted), MUTANT {nMut} (well-typed single change, signature/defeq rejection under withReducible, not semantic counterexamples), CONJ {nConj} (conjunct/disjunct drops, Start-drop included), AXIOMS {targets.length}, CLOSURE {nClosure} roots + 1 missing-requirement control + 1 forbidden-mention control + 1 clean control + unknown-name fixtures (2 detect: type-only, value-only; 1 clean)"
  logInfo m!"STATUS: NOT supplied by this unit: real EntryWitness, ReflectsAll, (a2.4) TopShips/ResetNk D->D' transport, (a3) post-processed top semantics, (b1) O3 arbitrary raw identification, (b2) O3 restatement, (c4 import), (c5) reader/core tie, (c6) hall/ReadsAt at later worlds, (c7) O2/DeclConnect rows, parametrised-route post-processing, Post adoption, FG"

end Tests.Gen5.DCEntryWCheck
