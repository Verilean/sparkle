import Sparkle.Compiler.Elab

/-! # A shadow checker of call kinds (findings A, A') — Tools side, no compiler edit

Pure functions over the EXISTING reader's output (`machineShape? … = some
shape`) and the callee constants of the environment. Nothing in the
compiler calls them; they change no route and reject nothing. They are a
MEASURING instrument (`Tests/Compiler/CallShadowCensusTest.lean`), not a
guarantee: there is no theorem in this file.

`shadowSig fields ci` — what a constant says about its own interface: its
output ports with their kinds (the choice the reader makes: one packed
`out` for a tuple result, else `machOuts?`) and the kinds of its hardware
binders (`mixedGatePeel` of its value, tuple inputs packed).

A call entry `k` of a parent shape is compared with the signatures of its
child `c`:

* `declared` — of `env.find? c`; `inlined` — of its unfolding
  (`inlinedConst (userInliner env)`); `selected` — of the constant the
  entry really hands the readers (`entryConst`). `selected` is one of the
  other two when it exists.
* NO signature (`selected = none`): the entry is UNKNOWN. An unknown entry
  is reported as unknown and counts as neither agreement nor disagreement;
  `agrees` is `true` for it only in the sense "nothing to compare" — never
  read it as "the child's types are guaranteed".
* against a known signature, separately: the field the entry reads is
  MISSING from the signature's outputs / occurs MORE THAN ONCE; the
  result KIND differs; the argument COUNT differs; the counts agree and an
  argument KIND differs.

`EntryReport.other*` say the same against the signature that is NOT the
selected one — what a rule "agree with both" would additionally refuse.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCallShadow
open Lean
open Sparkle.Compiler.Elab

/-- The interface kinds of a constant. -/
structure ShadowSig where
  outs : List (String × MixedGateBinder)
  ins : List MixedGateBinder
  deriving DecidableEq

/-- The signature of a constant (see the header). -/
def shadowSig (fields : Name → Option (Name × List (String × MixedGateBinder))) :
    ConstantInfo → Option ShadowSig
  | .defnInfo d => do
    let (bs, _) ← mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value)
    let outs ← match machTupleKinds? d.type with
      | some ks => some [("out", MixedGateBinder.bits (ks.map machWidth).sum)]
      | none => (machOuts? { proj := fun _ => none, fields := fields } d.type).map (·.2)
    some { outs := outs, ins := (bs.map (·.2)).filter (fun k => k != MixedGateBinder.domain) }
  | _ => none

/-- The three signatures of a declaration as a child: declared, inlined,
selected (of the entry constant). -/
structure ChildSigs where
  declared : Option ShadowSig := none
  inlined : Option ShadowSig := none
  selected : Option ShadowSig := none
  /-- The entry constant is the unfolded one. -/
  selInlined : Bool := false

def childSigs (env : Environment) (c : Name) : ChildSigs :=
  match env.find? c with
  | some ci =>
    let fields := userStructure? env
    let inl := inlinedConst (userInliner env) ci
    let ec := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
    { declared := shadowSig fields ci
      inlined := shadowSig fields inl
      selected := shadowSig fields ec
      selInlined := decide (shadowSig fields ec = shadowSig fields inl) &&
        !decide (shadowSig fields ec = shadowSig fields ci) }
  | none => {}

/-- One call entry against one signature, the ways of disagreeing apart. -/
structure SigDiff where
  fieldMissing : Bool := false
  fieldDup : Bool := false
  resKind : Bool := false
  argCount : Bool := false
  argKind : Bool := false

def SigDiff.any (d : SigDiff) : Bool :=
  d.fieldMissing || d.fieldDup || d.resKind || d.argCount || d.argKind

/-- `kinds`: the kinds of the transition's binders; `resPos`: the position
of the entry's result binder; `argBase + a`: the position of the `let`
`a`; `field`: the output the entry reads. -/
def sigDiff (kinds : List MixedGateBinder) (resPos argBase : Nat) (field : String)
    (args : List Nat) (s : ShadowSig) : SigDiff :=
  let named := s.outs.filter fun o => o.1 == field
  let argKs := args.map fun a => kinds[argBase + a]?
  { fieldMissing := named.isEmpty
    fieldDup := decide (1 < named.length)
    resKind := named.any fun o => !decide (kinds[resPos]? = some o.2)
    argCount := !decide (s.ins.length = args.length)
    argKind := decide (s.ins.length = args.length) && !decide (s.ins.map some = argKs) }

/-- The report of one entry. -/
structure EntryReport where
  /-- No selected signature: nothing was compared. -/
  unknown : Bool
  /-- Declared and inlined signatures both exist and differ. -/
  declInlDiffer : Bool
  /-- Against the selected signature. -/
  sel : SigDiff
  /-- Against the other signature (declared when the selected one is the
  inlined, and conversely), when it exists and differs from the selected. -/
  other : SigDiff

/-- Nothing compared, or the selected signature agrees. -/
def EntryReport.agrees (r : EntryReport) : Bool := !r.sel.any

/-- Only the signature that is NOT selected disagrees. -/
def EntryReport.overDecline (r : EntryReport) : Bool := !r.sel.any && r.other.any

def entryReport (kinds : List MixedGateBinder) (resPos argBase : Nat) (field : String)
    (args : List Nat) (cs : ChildSigs) : EntryReport :=
  let other : Option ShadowSig := if cs.selInlined then cs.declared else cs.inlined
  { unknown := cs.selected.isNone
    declInlDiffer := cs.declared.isSome && cs.inlined.isSome && !decide (cs.declared = cs.inlined)
    sel := match cs.selected with
      | some s => sigDiff kinds resPos argBase field args s
      | none => {}
    other := match other with
      | some s =>
        if decide (some s = cs.selected) then {} else sigDiff kinds resPos argBase field args s
      | none => {} }

/-- The declaration's own binders of a shape. -/
def declCount (shape : MachineShape) : Nat :=
  shape.binders.length - shape.insts.length - shape.layout.slots.length - shape.layout.lets

/-- The reports of a shape's call entries, in order, with the child. -/
def shadowReports (env : Environment) (shape : MachineShape) : List (Nat × Name × EntryReport) :=
  let kinds := shape.binders.map (·.2)
  let nDecl := declCount shape
  let argBase := nDecl + (shape.insts.length + shape.layout.slots.length)
  (List.range shape.insts.length).filterMap fun k =>
    (shape.insts[k]?).map fun e =>
      (k, e.1, entryReport kinds (nDecl + k) argBase (shape.instFields.getD k "out") e.2.1
        (childSigs env e.1))

/-- Every entry with a KNOWN selected signature agrees with it. Unknown
entries are not compared (see the header: this is not a guarantee about
them). -/
def shadowCallsAgree (env : Environment) (shape : MachineShape) : Bool :=
  (shadowReports env shape).all fun r => r.2.2.agrees

/-- The shape's own interface against its entry constant's signature:
`none` when the constant has no signature (unknown), else whether the
layout's outputs with their types and the kinds of the hardware binders
are the signature's. -/
def shadowOwnAgrees (env : Environment) (ec : ConstantInfo) (shape : MachineShape) :
    Option (Bool × Bool) :=
  (shadowSig (userStructure? env) ec).map fun s =>
    (decide (shape.layout.outs.map (fun o => (o.name, o.ty)) =
        s.outs.map (fun o => (o.1, machHWType o.2))),
     decide ((((shape.binders.take (declCount shape)).map (·.2)).filter
        (fun k => k != MixedGateBinder.domain)) = s.ins))

end Tools.ShippingCallShadow
