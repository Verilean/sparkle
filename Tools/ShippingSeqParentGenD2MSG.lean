import Tools.ShippingSeqParentGenD2M
import Tools.ShippingQuadHPoint
-- BUILT (unit SR18): h2 exit 0 (Tools.ShippingSeqParentGenD2MSG), h3 exit 0 (Tools.ShippingSeqParentGenD2MS) (dev runs); final-SHA rebuild in REPORT-SR18.md.
/-! # Text of the GENERIC-lemma path of the shared-leaf candidate (unit SR18, ledger L8ax)

Strings only (no elaborator): the declarations that `Tools/ShippingSeqParentGenD2MS.lean` (opt-in `sparkle.sharedLeafCandidate`, default `false`) emits, per accepted parent `P`, for the
class QUAD, in addition to the data facts of SR13:

* `epD2M_leafKid`, `epD2M{i}_calleeExtra`, `epD2M_parentExtra`, `epD2M_quadAll`: the decidable DATA facts (`decide`), bundled;
* `epD2M_genP`, `epD2M{i}_C_gen`: the `GenFacts` of the parent and of each callee, assembled from the generator's own `machine_*` theorems;
* `epD2M_leafRun := G.seq_child_runN` (the leaf's generated run theorem, a theorem of the machine route, not an input);
* `epD2M{i}_C_hextB` / `_hext`: the declared inputs are read by the generated `machineExtB` / `machineExt` (`unfold` + `extendBits_of_ne`);
* `epD2M{i}_C_hPoint{k}` / `epD2M_hPoint{k}`: the PER-CALL residue `HPointAt … k` of `CallFactF` (decoding equations = the generator's own `gfHb*`/`gfHv*`, output defeq by `rfl`), and
  `epD2M{i}_C_hF`, `epD2M_hFP` (`callFactF_of_hPointAt`);
* the bodies of `epD2M_hkid / ranA / runFacts / outsCheck / kidsMasked / designCheck / traceXA / soundLA / composedA` are the generic lemmas (`quad_hkid` … `quad_composed_split`); their
  STATEMENTS are the ones of the SR13 template (unchanged), so the endpoint statement is unchanged.
Each declaration is checked by the kernel when it is elaborated.  These are facts about the declarations the generator accepted (instance-specific, one proof per call / per declaration), NOT a
theorem over the whole class.  If a generated declaration fails to check, the generator logs which one and falls back to the SR13 path (nothing of the failed run is kept; no input is refused). -/
namespace Tools.ShippingSeqParentGenD2MSG
open Tools.ShippingSeqParentGenD2M

/-- facts read from the environment by the elaborator -/
structure GenInfo where
  /-- call instances of each callee -/
  mCs : List Nat
  /-- number of group-fact bundles (`gfHb{j}`) of each callee's old `hcalls` -/
  nGCs : List Nat
  /-- output fields of the leaf -/
  nOutsG : Nat
deriving Repr

/-- replace the BODY of the declaration that starts with `marker`: from its first `:=` up to the first blank line (the statement is kept) -/
def replaceBody (t marker body : String) : String :=
  match t.splitOn marker with
  | [pre, rest] =>
    match rest.splitOn ":=" with
    | stmt :: _ :: _ =>
      let after := (rest.drop (stmt.length + 2)).toString
      let tail := match after.splitOn "\n\n" with
        | _ :: tl@(_ :: _) => "\n\n" ++ "\n\n".intercalate tl
        | _ => ""
      pre ++ marker ++ stmt ++ ":=\n  " ++ body ++ tail
    | _ => panic! s!"replaceBody: no := after {marker}"
  | _ => panic! s!"replaceBody: marker {marker} not unique"

/-- the decidable data facts, bundled -/
def genATmpl : String := r#"
theorem _root_.@P@.epD2M_leafKid : Tools.ShippingQuadComposed.LeafKidData @G@.machineData := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel | exact fun h0 => absurd (congrArg List.length h0) (by decide)

theorem _root_.@P@.epD2M0_calleeExtra : Tools.ShippingQuadComposed.LeafCalleeExtra @C0@.machineData @G@.machineData @K0@ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | decide +kernel

theorem _root_.@P@.epD2M1_calleeExtra : Tools.ShippingQuadComposed.LeafCalleeExtra @C1@.machineData @G@.machineData @K1@ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | decide +kernel

theorem _root_.@P@.epD2M_parentExtra : Tools.ShippingQuadComposed.QuadParentExtra @P@.machineData @C0@.machineData @C1@.machineData ``@C0@ ``@C1@ @KP@ @K0@ @K1@ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel | exact fun h0 => absurd (congrArg List.length h0) (by decide)

theorem _root_.@P@.epD2M_quadAll : Tools.ShippingQuadComposed.QuadAll @P@.machineData @C0@.machineData @C1@.machineData @G@.machineData
    ``@P@ ``@C0@ ``@C1@ ``@G@ @KP@ @K0@ @K1@ :=
  ⟨@P@.epD2M_quadData, @P@.epD2M_parentExtra, @P@.epD2M_leafData, @P@.epD2M_leafKid, @P@.epD2M0_calleeData, @P@.epD2M0_calleeExtra,
   @P@.epD2M1_calleeData, @P@.epD2M1_calleeExtra⟩
"#

/-- `GenFacts`, `hextB`, `hext` of callee `@I@` and the leaf run (once) -/
def calleeGenTmpl : String := r#"
instance _root_.@P@.epD2M@I@_C_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys @C@.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys @C@.machineData.ss))) @C@.machine_composedNR1
    Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA

theorem _root_.@P@.epD2M@I@_C_gen : Tools.ShippingQuadComposed.GenFacts @C@.machineData (fun i : Sparkle.Core.Domain.DomainConfig => i) @C@.machineInits @C@.machineBody
    @C@.machineResult @C@.machineExt @C@.machineExtB @C@.machineSource :=
  ⟨@C@.machine_ok, @C@.machine_body, @C@.machine_inits, @C@.machine_writes, @C@.machine_result, @C@.machine_source,
   fun i bools bits S S' t h =>
    @C@.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

theorem _root_.@P@.epD2M@I@_C_hextB : ∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j : Nat), j < @KC@ →
    @C@.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)) j = bools j := by
  intro i bools bits j hj
  unfold @C@.machineExtB
  repeat rw [Tools.ShippingQuadCallFacts.extendBools_of_ne _ _ (by omega)]
  try rfl

theorem _root_.@P@.epD2M@I@_C_hext : ∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j n' : Nat), j < @KC@ →
    @C@.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)) j n' = bits j n' := by
  intro i bools bits j n' hj
  unfold @C@.machineExt
  repeat rw [Tools.ShippingQuadCallFacts.extendBits_of_ne _ _ (by omega)]
"#

def parentGenTmpl : String := r#"
theorem _root_.@P@.epD2M_genP : Tools.ShippingQuadComposed.GenFacts @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody
    @P@.machineResult @P@.machineExt @P@.machineExtB @P@.machineSource :=
  ⟨@P@.machine_ok, @P@.machine_body, @P@.machine_inits, @P@.machine_writes, @P@.machine_result, @P@.machine_source,
   fun i bools bits S S' t h =>
    @P@.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

theorem _root_.@P@.epD2M_leafRun : Tools.ShippingQuadCalls.LeafSeqRunN ``@G@ @G@.machineData @G@.machineSource := @G@.seq_child_runN
"#

/-- the families of a callee (leaf callee: `ι = DomainConfig`) in `HPointAt` / `CallFactF` -/
def calleeFam : String := r#"(Tools.ShippingMachineCausal.letObsB @C@.machineData (fun i : Sparkle.Core.Domain.DomainConfig => i) @C@.machineInits @C@.machineBody @C@.machineExt @C@.machineExtB)
    (fun i bools bits => @C@.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)))
    (fun i bools bits => @C@.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)))
    (Tools.ShippingQuadComposed.leafOutsC ``@G@ @G@.machineData)"#

def parentFam : String := r#"(Tools.ShippingMachineCausal.letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB)
    (fun i bools bits => @P@.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
    (fun i bools bits => @P@.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
    (Tools.ShippingQuadComposed.quadOutsOf ``@C0@ ``@C1@ @C0@.machineData @C1@.machineData)"#

/-- the `have Hb{j} Hv{j}` lines (the generator's own `gfHb*` / `gfHv*` of the old chain `thm`, extracted typed) -/
def hbhv (thm : String) (nG : Nat) : String :=
  "\n".intercalate ((List.range nG).map fun j =>
    s!"  have Hb{j} := oldGroupFact% (_) {thm} Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb{j}\n" ++
    s!"  have Hv{j} := oldGroupFact% (_) {thm} Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv{j}")

/-- `first | (refine …) | …` over the (group, output field) pairs -/
def pointAlts (groups : List (Nat × Nat)) : String :=
  "  first\n" ++ "\n".intercalate (groups.flatMap fun (j, nOut) =>
    (List.range nOut).map fun K => s!"    | (refine ⟨_, _, Hb{j}, Hv{j}, {K}, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)")

def calleePointTmpl : String := r#"
theorem _root_.@P@.epD2M@I@_C_hPoint@CK@ : Tools.ShippingQuadHPoint.HPointAt @C@.machineData @KC@ (ι := Sparkle.Core.Domain.DomainConfig) (dom := fun i => i)
    (fun i => i) @FAM@
    (fun _ => @G@.machineData.bsIn) (Tools.ShippingQuadCallFacts.leafSrcA ``@G@ @G@.machineSource) @CK@ := by
  intro i bools bits hk
@HBHV@
@ALTS@
"#

def parentPointTmpl : String := r#"
theorem _root_.@P@.epD2M_hPoint@CK@ : Tools.ShippingQuadHPoint.HPointAt @P@.machineData @KP@ (ι := Unit) (dom := fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
    (fun _ => Sparkle.Core.Domain.defaultDomain) @FAM@
    (Tools.ShippingQuadCallFacts.quadBsOf ``@C0@ ``@C1@ @C0@.machineData @C1@.machineData @K0@ @K1@)
    (Tools.ShippingQuadCallFacts.quadSrcA ``@C0@ ``@C1@ @C0@.machineSource @C1@.machineSource) @CK@ := by
  intro i bools bits hk
@HBHV@
@ALTS@
"#

def calleeHFTmpl : String := r#"
theorem _root_.@P@.epD2M@I@_C_hF : Tools.ShippingQuadCalls.CallFactF @C@.machineData @KC@
    @FAM@
    (Tools.ShippingQuadComposed.leafSrcC ``@G@ @G@.machineData @G@.machineSource) :=
  Tools.ShippingQuadHPoint.callFactF_of_hPointAt _ _ (fun i => i) (fun _ => @G@.machineData.bsIn)
    (Tools.ShippingQuadCallFacts.leafSrcA ``@G@ @G@.machineSource) (fun i n v => Tools.ShippingQuadCallFacts.leafSrcC_eq _ _ _ i n v)
    (fun k hk => by
      have hl : @C@.machineData.shape.insts.length = @MC@ := by decide
      rcases k with @MPAT@
      all_goals first
        | omega
@EXACTS@)
"#

def parentHFTmpl : String := r#"
theorem _root_.@P@.epD2M_hFP : Tools.ShippingQuadCalls.CallFactF @P@.machineData @KP@
    @FAM@
    (Tools.ShippingQuadComposed.quadSrcF ``@C0@ ``@C1@ @C0@.machineData @C1@.machineData @K0@ @K1@ @C0@.machineSource @C1@.machineSource) :=
  Tools.ShippingQuadHPoint.callFactF_of_hPointAt _ _ (fun _ => Sparkle.Core.Domain.defaultDomain)
    (Tools.ShippingQuadCallFacts.quadBsOf ``@C0@ ``@C1@ @C0@.machineData @C1@.machineData @K0@ @K1@)
    (Tools.ShippingQuadCallFacts.quadSrcA ``@C0@ ``@C1@ @C0@.machineSource @C1@.machineSource)
    (fun i n v => Tools.ShippingQuadCallFacts.quadSrcF_eq _ _ _ _ _ _ _ _ i n v)
    (fun k hk => by
      have hl : @P@.machineData.shape.insts.length = @MC@ := by decide
      rcases k with @MPAT@
      all_goals first
        | omega
@EXACTS@)
"#

private def pat (m : Nat) : String := "".intercalate ((List.range m).map fun _ => "_ | ") ++ "k"

/-- The data facts (placed before `epD2M_hkid`). -/
def genA (p : D2MParams) : String :=
  let t := genATmpl
  let t := t.replace "@C0@" (p.Cs.getD 0 .anonymous).toString |>.replace "@C1@" (p.Cs.getD 1 .anonymous).toString
  let t := t.replace "@G@" (p.Gs.getD 0 .anonymous).toString |>.replace "@K0@" (toString (p.kCs.getD 0 0)) |>.replace "@K1@" (toString (p.kCs.getD 1 0))
  t.replace "@KP@" (toString p.kP)

/-- GenFacts, hext/hextB, per-call `HPointAt`, `CallFactF` (placed after the `Inhabited` instance of the parent). -/
def genB (p : D2MParams) (g : GenInfo) : String := Id.run do
  let mut out := parentGenTmpl
  for i in rangeR p do
    out := out ++ sub1 p i calleeGenTmpl
    let mC := g.mCs.getD i 0
    let groupsC := (List.range (g.nGCs.getD i 0)).map fun j => (j, g.nOutsG)
    for k in List.range mC do
      out := out ++ (sub1 p i (calleePointTmpl.replace "@FAM@" calleeFam)).replace "@CK@" (toString k)
        |>.replace "@HBHV@" (hbhv s!"{(p.Cs.getD i .anonymous)}.machine_composedNR1" (g.nGCs.getD i 0))
        |>.replace "@ALTS@" (pointAlts groupsC)
    out := out ++ ((sub1 p i (calleeHFTmpl.replace "@FAM@" calleeFam)).replace "@MC@" (toString mC) |>.replace "@MPAT@" (pat mC)).replace "@EXACTS@"
      ("\n".intercalate ((List.range mC).map fun k => s!"        | exact @P@.epD2M@I@_C_hPoint{k}".replace "@I@" (toString i)))
  let groupsP := p.groups.zipIdx.map fun ((ci, _), j) => (j, p.nOutsCs.getD ci 0)
  for k in List.range p.mP do
    out := out ++ (parentPointTmpl.replace "@FAM@" parentFam).replace "@CK@" (toString k)
      |>.replace "@HBHV@" (hbhv s!"{p.P}.machine_composedNR2" p.groups.length)
      |>.replace "@ALTS@" (pointAlts groupsP)
  out := out ++ ((parentHFTmpl.replace "@FAM@" parentFam).replace "@MC@" (toString p.mP) |>.replace "@MPAT@" (pat p.mP)).replace "@EXACTS@"
    ("\n".intercalate ((List.range p.mP).map fun k => s!"        | exact @P@.epD2M_hPoint{k}"))
  let o2 := out.replace "@C0@" (p.Cs.getD 0 .anonymous).toString |>.replace "@C1@" (p.Cs.getD 1 .anonymous).toString
  let o3 := o2.replace "@G@" (p.Gs.getD 0 .anonymous).toString |>.replace "@K0@" (toString (p.kCs.getD 0 0)) |>.replace "@K1@" (toString (p.kCs.getD 1 0))
  return o3.replace "@KP@" (toString p.kP)

/-- The generic-lemma bodies of the template theorems (statements untouched): `(marker, body)`. -/
def bodies : List (String × String) :=
  let Q := "@P@.epD2M_quadAll"
  let HCL := "(fun mc cc => @G@.machine_closes mc _ cc _)"
  let Z := s!"{Q} hM0 hM1 hR0 {HCL}"
  [("theorem _root_.@P@.epD2M_hkid", s!"fun k hk => Tools.ShippingQuadComposed.quad_hkid O T {Z} n k hk"),
   ("theorem _root_.@P@.epD2M_ranA", s!"Tools.ShippingQuadComposed.quad_ranA O T hA {Z} hcore entry hw"),
   ("theorem _root_.@P@.epD2M_runFacts", s!"Tools.ShippingQuadComposed.quad_runFacts O T n hA {Z} hcore hpost entry hw"),
   ("theorem _root_.@P@.epD2M_outsCheck", s!"Tools.ShippingQuadComposed.quad_outsCheck O T n hA {Z} hcore hpost entry hw"),
   ("theorem _root_.@P@.epD2M_kidsMasked", s!"Tools.ShippingQuadComposed.quad_kidsMasked O T n hA {Z} hcore hpost entry hw"),
   ("theorem _root_.@P@.epD2M_designCheck", s!"Tools.ShippingQuadComposed.quad_designCheck O T n hA {Z} hcore hpost entry hw"),
   ("theorem _root_.@P@.epD2M_traceXA", s!"Tools.ShippingQuadComposed.quad_traceXA O T hA {Q} @P@.epD2M_genP entry hM0 hM1 hR0 {HCL} hw hcore"),
   ("theorem _root_.@P@.epD2M_soundLA", s!"Tools.ShippingQuadComposed.quad_soundLA O T hA {Q} @P@.epD2M_genP entry hM0 hM1 hR0 {HCL} hw hcore"),
   ("theorem _root_.@P@.epD2M_composedA",
     s!"Tools.ShippingQuadCalls.quad_composed_split {Q} @P@.epD2M_genP @P@.epD2M0_C_gen @P@.epD2M1_C_gen @P@.epD2M_leafRun @P@.epD2M0_C_hF @P@.epD2M1_C_hF @P@.epD2M_hFP @P@.epD2M0_C_hextB @P@.epD2M0_C_hext @P@.epD2M1_C_hextB @P@.epD2M1_C_hext {HCL} hcore entry ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩")]

end Tools.ShippingSeqParentGenD2MSG
