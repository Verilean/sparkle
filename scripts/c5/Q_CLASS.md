# C5 — class Q = `QSharedLeafParent` (SPECIFICATION, ELABORATED in Tests/Compiler/QDefTest.lean; built exit 0, audits ok)
A NEW separate structure (MemSharedLeafParent is untouched). Reuses `GenPkg` (+ extS/extBS/lsrc) from Tests/Compiler/CDefTest.lean.
Classification words: DATA (decide / rfl), GEN-SHAPE (a fact about the generated definitions, filled per member by uniform unfolding, as C4's wHext / wCallOut),
GENERATED (a theorem produced by a generator), STRUCTURAL CLASS ASSUMPTION (only `group`). **No field is a target Prop** (KidFactsNC, HCallsOf, CallFactF/CallFactFO,
MachineCloses, ComposedNW, closes, run of the top): QDefTest audits every constructor binder of the four structures against these constants.

## Design (what differs from MemSharedLeafParent)
* `leaf : QLeafPkg` (decl, d, src; no ext) + `leafData / leafKidData / leafLetsOk / leafNoMem / leafRun` — a PLAIN leaf.
* Per-wrapper data is bundled: `QWrapper L = ⟨pkg : GenPkg, dat : QWrapData L pkg⟩`; `dat.arity` IS wArity (no wArityN); `QSharedLeafParent.wArity := wrappers.map (·.dat.arity)`.
* Per-call kind inside each wrapper: ORDINARY call (`(originAt ..).child? = none`) ⇒ a call of the leaf; MEMORY call ⇒ memory tables / `memCalls`. The tables are per wrapper (`nameK nk outsK namesK names`).
* `tieCs : cs = wrappers.map (⟨decl, d, [], dat.names⟩)` — Gs = [] and per-wrapper `names` (csQ); `csNc / csCd` kept.
* EXTRA contract binder beyond C4: **none**. `hcl` is DERIVED (`leafLetsOk` ⇒ `closes_of_data`), checked by `P_Q_hcl`. Beyond C4's fields the class needs only the new data below.
* NEW vs the inventory: the port map `argPos` (see `argInOkQ`): wrapQ passes `x` (wrapper position 3) to leaf port 1, so C4's `wArgsIn` (same position) is false for Q.

## Exact Lean (verbatim from Tests/Compiler/QDefTest.lean)
```lean
/-- AMENDMENT-5-style decoding check with a PORT MAP: at leaf port `p` of the port list `bs`, the call argument `args[portIdx bs p]` is a
let of `d` whose term is `d`'s own input term at wrapper position `pos p` (`boolInput j` with `bpos j = pos p`, or `bitsInput n j` with
`vpos j = pos p`).  (`Tests.Compiler.CDef.argInOk` is the case `pos = id`, which does NOT hold for wrapQ: its `x` is at wrapper position 3 but
at leaf port 1.)  Domain ports and positions past the list are vacuous. -/
def argInOkQ (d : MachineData) (bs : List (Name × MixedGateBinder)) (args : List Nat) (pos : Nat → Nat) (p : Nat) : Bool :=
  match bs[p]? with
  | none => true
  | some b =>
    match b.2 with
    | .domain => true
    | .bool =>
      match args[Tools.ShippingMachineChild.portIdx bs p]? with
      | none => false
      | some a =>
        match d.ls[a]? with
        | some ⟨.bool, .boolInput j⟩ => d.bpos j == pos p
        | _ => false
    | .bits n =>
      match args[Tools.ShippingMachineChild.portIdx bs p]? with
      | none => false
      | some a =>
        match d.ls[a]? with
        | some ⟨.bits m, .bitsInput _ j⟩ => m == n && d.vpos j == pos p
        | _ => false

/-- the PLAIN shared leaf (no instances, no generated ext): the three things the class reads (AMENDMENT 2 of C4) -/
structure QLeafPkg where
  decl : Lean.Name
  d : MachineData
  src : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)

/-- everything the class records about ONE wrapper `w` (a generated callee, declared arity `arity`) of the plain leaf `L`.
Each of its calls is ORDINARY (`child? = none`; a call of `L`) or a MEMORY entry (`child? = some (memModule ..)`). -/
structure QWrapData (L : QLeafPkg) (w : GenPkg DomainConfig (fun i => i)) where
  arity : Nat                                                    -- DATA: declared-input count of this wrapper (P_Q: 3 and 5)
  -- per-call tables of MemCalleeData (per wrapper; the SAME record serves ordinary and memory calls)
  nameK : Nat → String                                           -- DATA
  nk : Nat → Nat                                                 -- DATA
  outsK : Nat → List String                                      -- DATA
  namesK : Nat → List String                                     -- DATA
  names : List String                                            -- DATA: this wrapper's `names` (namesP / namesQ; csQ's per-wrapper list)
  mem : MemCalleeData w.d w.decl arity nameK nk outsK namesK names                          -- DATA (decide)
  -- the kind of each call
  ordKid : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none → (w.d.shape.insts[k]).1 = L.decl  -- DATA: ordinary ⇒ leaf
  ordArgsN : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    (w.d.shape.insts[k]).2.1.length = (L.d.bsIn.filter Tools.ShippingPortWidthsPure.nonDom).length                          -- DATA
  ordT : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    nameK k = Sparkle.IR.ModuleName.ofDecl L.decl ∧ nk k = leafNk L.d ∧ outsK k = L.d.shape.layout.outs.map (·.name) ∧ namesK k = []  -- DATA: ordinary tables = the leaf's
  widths : Nat → List Nat                                        -- DATA: call widths (leaf widths at ordinary calls, memIns at memory calls)
  wid : Tools.ShippingPortsMatchRaw.callArgsOk w.d arity widths = true                                                   -- DATA
  ordW : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    widths k = (L.d.bsIn.filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth                              -- DATA
  kidOuts : Nat → List OutField                                  -- DATA: KidFactsNC tables (leaf outs at ordinary, memOuts at memory calls)
  kidIns : Nat → List Nat                                        -- DATA
  kidMemT : ∀ (k : Nat) (hk : k < w.d.shape.insts.length) (cb : Bool) (aw dw : Nat),
    (originAt w.d.shape k).child? = some (memModule cb aw dw) → kidOuts k = memOuts dw ∧ kidIns k = memIns aw dw          -- DATA
  kidOrdT : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    kidOuts k = L.d.shape.layout.outs ∧ kidIns k = Tools.ShippingPortWidthsPure.declWidths L.d                              -- DATA
  cw : Tools.ShippingCallWidths.callWidthsOk w.d arity kidOuts = true                                                     -- DATA
  outsClean : ∀ o ∈ w.d.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true                      -- DATA
  scalar : ∀ o ∈ w.d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true                                       -- DATA
  outOk : ∀ o ∈ w.d.shape.layout.outs, outNameOk o.name = true                                                              -- DATA
  -- CalleeNM data (every call is a leaf call or a memory entry of ONE memory shape (mcb, maw, mdw))
  mcb : Bool                                                     -- DATA: the memory shape of this wrapper's memory entries (unused when it has none)
  maw : Nat
  mdw : Nat
  tags : ∀ x ∈ w.d.shape.instTagged, x.1 = L.decl ∨ x.1 = memChildName mcb maw mdw                                         -- DATA
  agree : Tools.ShippingInstTagged.TagsAgree w.d.shape                                                                    -- DATA
  cne : ∀ k (hk : k < w.d.shape.insts.length), (w.d.shape.insts[k]).1 ≠ w.decl                                            -- DATA
  -- generated-shape facts (filled by the same uniform unfolding as hext / hextB / memcalls; NOT generator certificates)
  hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat),
    j < arity → w.extBS i bools bits j = bools j                                                                          -- GEN-SHAPE
  hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat),
    j < arity → w.extS i bools bits j n' = bits j n'                                                                      -- GEN-SHAPE
  memCalls : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (k : Nat) (c : Name),
    (w.d.shape.insts.map (·.1))[k]? = some c → (originAt w.d.shape k).child? ≠ none →
    MemFacts w.d.shape (w.lsrc i bools bits) w.d.ls.length (w.d.bsIn.drop arity) arity (w.extS i bools bits) k c         -- GEN-SHAPE (memory calls only)
  -- ordinary-call decoding and output (replace TqHcallsP's / TqFQ's CallFactF / CallFactFO inputs; ORDINARY calls only)
  argPos : Nat → Nat → Nat                                       -- DATA: call k, leaf port p ↦ the wrapper input position passed at that port
  argsIn : ∀ (k : Nat) (hk : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    ∀ p, p < L.d.bsIn.length → argInOkQ w.d L.d.bsIn (w.d.shape.insts[k]).2.1 (argPos k) p = true                         -- DATA
  callOut : ∀ (k : Nat) (_ : k < w.d.shape.insts.length), (originAt w.d.shape k).child? = none →
    ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
    ∃ (k' : Nat) (o : OutField), L.d.shape.layout.outs[k']? = some o ∧ o.name = w.d.shape.instFields.getD k "" ∧
      ∀ (bools' : Nat → Signal i Bool) (bits' : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
        (∀ p, L.d.bsIn[p]?.map (·.2) = some MixedGateBinder.bool → bools' p = bools (argPos k p)) →
        (∀ p n, L.d.bsIn[p]?.map (·.2) = some (MixedGateBinder.bits n) → bits' p n = bits (argPos k p) n) →
        ∃ f : Nat → Nat, (L.src i bools' bits')[k']? = some f ∧
          ∀ τ, posEnc (fun p => (w.extBS i bools bits p).val τ) (fun p n => (w.extS i bools bits p n).val τ)
            (arity + k) (((w.d.bsIn.drop arity)[k]?.map (·.2)).getD .domain) = f τ                                        -- GEN-SHAPE (ordinary calls only)

/-- a wrapper: its generated package and its Q data -/
structure QWrapper (L : QLeafPkg) where
  pkg : GenPkg DomainConfig (fun i => i)
  dat : QWrapData L pkg

abbrev QWrapper.decl {L : QLeafPkg} (w : QWrapper L) : Lean.Name := w.pkg.decl
abbrev QWrapper.d {L : QLeafPkg} (w : QWrapper L) : MachineData := w.pkg.d
abbrev QWrapper.arity {L : QLeafPkg} (w : QWrapper L) : Nat := w.dat.arity

/-- The class Q: parents of wrappers over ONE plain shared leaf; each wrapper has ordinary calls (of the leaf) and/or memory entries. -/
structure QSharedLeafParent where
  top : GenPkg Unit (fun _ => defaultDomain)
  nDecl : Nat
  cs : List NCal
  pdata : NmParentData top.d cs top.decl nDecl                                                    -- DATA (decide)
  outTy : ∀ o ∈ top.d.shape.layout.outs, o.ty.bitWidth = o.width                                  -- DATA
  noMem : ∀ x ∈ top.d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true  -- DATA
  slotsNe : top.d.shape.layout.slots ≠ []                                                         -- DATA
  outsOf : Nat → List OutField                                                                    -- DATA
  insOf : Nat → List Nat                                                                          -- DATA
  cw : Tools.ShippingCallWidths.callWidthsOk top.d nDecl outsOf = true                            -- DATA
  ca : Tools.ShippingPortsMatchRaw.callArgsOk top.d nDecl insOf = true                            -- DATA
  -- the plain leaf
  leaf : QLeafPkg
  leafData : LeafData leaf.d                                                                      -- DATA (machine_ok / machine_body + decide)
  leafKidData : LeafKidData leaf.d                                                                -- DATA (decide)
  leafLetsOk : leaf.d.letsOk = true                                                               -- DATA (decide): MachineCloses of the leaf is DERIVED from it
  leafNoMem : memChild? leaf.decl = none                                                          -- DATA (rfl / decide)
  leafRun : LeafSeqRunN leaf.decl leaf.d leaf.src                                                 -- GENERATED (leafP.seq_child_runN by generateSeqChildN)
  -- the wrappers (callees of the top)
  wrappers : List (QWrapper leaf)
  bsC : Lean.Name → List (Name × MixedGateBinder)                                                 -- DATA
  outsC : Lean.Name → List OutField                                                               -- DATA
  srcC : Unit → Lean.Name → (Nat → List Nat) → List (Nat → Nat)                                   -- DATA
  group : QuadGroupFacts top.d nDecl top.lsrc top.extS top.extBS bsC outsC srcC                   -- STRUCTURAL CLASS ASSUMPTION (= TqGrp)
  wOf : Nat → Nat                                                                                 -- DATA: call index ↦ wrapper index
  tieCallee : ∀ k, k < top.d.shape.insts.length →
    wOf k < wrappers.length ∧ (top.d.shape.insts.map (·.1))[k]? = (wrappers.map (·.pkg.decl))[wOf k]?       -- DATA
  tieOuts : ∀ k, k < top.d.shape.insts.length → outsOf k = (wrappers.map (·.pkg.d.shape.layout.outs)).getD (wOf k) []   -- DATA
  tieIns : ∀ k, k < top.d.shape.insts.length →
    insOf k = (wrappers.map (fun w => argWidths w.pkg.d w.dat.arity)).getD (wOf k) []                       -- DATA
  tieBsC : ∀ w ∈ wrappers, bsC w.pkg.decl = w.pkg.d.bsIn.take w.dat.arity                        -- DATA
  tieOutsC : ∀ w ∈ wrappers, outsC w.pkg.decl = w.pkg.d.shape.layout.outs                         -- DATA
  tieSrcC : ∀ w ∈ wrappers, srcC () w.pkg.decl = fun vals => w.pkg.src defaultDomain
    (Tools.ShippingMachineChild.boolsOf (w.pkg.d.bsIn.take w.dat.arity) vals) (Tools.ShippingMachineChild.bitsOf (w.pkg.d.bsIn.take w.dat.arity) vals)  -- STRUCTURAL (rfl-style)
  tieCs : cs = wrappers.map (fun w => (⟨w.pkg.decl, w.pkg.d, [], w.dat.names⟩ : NCal))            -- DATA (rfl): Gs = [], per-wrapper names
  csNc : ∀ e ∈ cs, ∀ e' ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs   -- DATA
  csCd : ∀ e ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ top.decl) ∧ top.decl ∉ e.Gs       -- DATA

/-- the per-wrapper arities (`wArity`) -/
abbrev QSharedLeafParent.wArity (P : QSharedLeafParent) : List Nat := P.wrappers.map (·.dat.arity)

```

## Field table (why each field exists; instance input it replaces)
| field | class | needed for / replaces |
|---|---|---|
| top, nDecl, cs, pdata, outTy, noMem, slotsNe, outsOf, insOf, cw, ca | DATA | = topshareQ_parentData (Tests/Compiler/SharedLeafMemKidEntryTest.lean:268), topshareQ_outTy/nomem/slotsNe/cw/ca, tqOuts/tqIns (Srm4ParentQTest.lean:41-54) |
| leaf (QLeafPkg) | DATA | decl/d/src of leafP; the leaf has no machineExt (CDef AMENDMENT 2), so no GenPkg |
| leafData : LeafData | DATA | leafP_data (SharedLeafMemKidRunTest.lean:145); input of leafKid_ifaceP / leafOK_of_data (Tools/ShippingQuadLeafGeneric.lean:51,~80), also `ok`/`body` of closes_of_data |
| leafKidData : LeafKidData | DATA | leafP_kidData (Srm4KidTest.lean:71) → leaf_kidFactsA (Tools/ShippingQuadComposed.lean:71) for Q-KID |
| leafLetsOk | DATA | `letsOk` of leafP; makes `hcl` (TqBnd, Srm9ComposedTest.lean:151) derivable via closes_of_data (Tools/ShippingMachineClosesData.lean:226) |
| leafNoMem | DATA | leafP_nomem (SharedLeafMemKidRunTest.lean:170): hcalls_of_names (Tools/ShippingMemLeafRun.lean:461) |
| leafRun : LeafSeqRunN | GENERATED | leafP.seq_child_runN via generateSeqChildN (= leafP_run, Srm4MixedTest.lean:36): `hrunPC` of ordCallee_hcalls (Tools/ShippingSrm4Mixed.lean:159) |
| wrappers, wOf, tieCallee/tieOuts/tieIns/tieBsC/tieOutsC/tieSrcC | DATA (tieSrcC structural rfl) | wrapper/callee ties as C4 AMENDMENT 1, with per-wrapper arity (topshareQ_name Srm4ParentQTest.lean:55, tqBsC/tqOutsC/tqSrcC Srm4ComposedQTest.lean:~60) |
| bsC outsC srcC | DATA | tqBsC tqOutsC tqSrcC |
| group | STRUCTURAL CLASS ASSUMPTION | TqGrp (Srm4ComposedQTest.lean:94), as TmGrp |
| tieCs, csNc, csCd | DATA | csQ (SharedLeafMemKidEntryTest.lean:215), csQ_nc / csQ_cd (:~262) feeding NmCallees |
| dat.arity | DATA | 3 / 5 (wrapP_calleeData n, wrapQ_memCallee n) |
| dat.nameK nk outsK namesK names, mem | DATA | MemCalleeData wrapQ (wqName.. Srm4Mixed/IfaceTest.lean:~190); wrapP gets the same record (mixed route, no LeafCalleeData) |
| dat.ordKid ordArgsN ordT widths wid ordW | DATA | wrapQ_ordKid, wrapQ_argsN, wqW/wrapQ_wid/wrapQ_hw (Srm4MixedTest.lean:~75-90): ordCallee_hcalls; ordT: leafKid_ifaceP for ordinary kids |
| dat.kidOuts kidIns kidMemT kidOrdT cw outsClean scalar outOk | DATA | wqKidOuts/wqKidIns, wrapQ_kidFactsNC (Srm4KidTest.lean:85), wrapQ_outOk; per-call kind dispatch of memCallee_kidFactsNC (Tools/ShippingSrm4Kid.lean:60) |
| dat.mcb maw mdw, tags, agree, cne | DATA | wrapQ_names/wrapQ_hcalls (SharedLeafMemKidRunTest.lean:~172), wrapQ_agree, wrapQ_cne: CalleeNM (wrapQ_calleeNM, EntryTest.lean:~256); memory shape of the wrapper's memory entries |
| dat.hextB, hext | GEN-SHAPE | wrapQ_hextB / wrapQ_hext / wrapP_hextB / wrapP_hext (Srm4MixedTest.lean:~40, Srm4ComposedQTest.lean:~35): callee_seqChildRunN2 |
| dat.memCalls | GEN-SHAPE | wrapQ_memcalls (Srm4MixedTest.lean:~100): `hmem` of ordCallee_hcalls (vacuous for wrapP) |
| dat.argPos, argsIn | DATA | decoding of ordinary-call arguments (replaces the CallFactF decode inputs); C4 wArgsIn + port map |
| dat.callOut | GEN-SHAPE | the ordinary-call OUTPUT fact: replaces TqFQ (CallFactFO wrapQ, Srm4ComposedQTest.lean:88) and the CallFactF behind TqHcallsP (:79); ordinary calls only |

## Member
`P_Q (hgrp : TqGrp) : QSharedLeafParent` (QDefTest): decide + generated theorems (leafP_run etc.) + the existing instance lemmas; defeq audits `P_Q_group_defeq … P_Q_soundL_defeq`, `P_Q_cs_defeq` (arity [3,5]), `P_Q_hcl` (hcl derived), `FrozenC5` (19 binders, no hcl).
