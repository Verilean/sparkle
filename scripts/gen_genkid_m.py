#!/usr/bin/env python3
"""Generate Tools/ShippingGenKidM.lean (round par/d-1) from three BUILT files:

  Tools/ShippingCallsPortsG.lean   core_calls_portsG   -> core_calls_portsGM
  Tools/ShippingChecksCore.lean    kids_run_kid        -> kids_run_kidM
  Tools/ShippingGenKid.lean        kids_designCheck_in -> kidsM_designCheck_in

Every replacement is asserted to occur exactly the stated number of times in
the segment it is applied to, and every segment is anchored on the built
file's lines; the script fails otherwise. The rest of the output (the short
theorems and the structure `GenKidM`) is written by hand, below. The script
reads and writes files only; it starts no build.

Run from the repository root:  python3 scripts/gen_genkid_m.py
"""
import sys

OUT = "Tools/ShippingGenKidM.lean"


def load(path):
    return open(path, encoding="utf-8").read().split("\n")


def seg(lines, first, last):
    return "\n".join(lines[first - 1:last])


def anchor(path, lines, lineno, text):
    if lines[lineno - 1] != text:
        sys.exit(f"{path}:{lineno} is not\n{text}\nbut\n{lines[lineno - 1]}")


def rep(text, old, new, count=1):
    n = text.count(old)
    if n != count:
        sys.exit(f"replacement expected {count} occurrence(s), found {n}:\n{old}")
    return text.replace(old, new)


HNOMEM = "    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)\n"

# ------------------------------------------------------------ core_calls_portsGM
P = "Tools/ShippingCallsPortsG.lean"
pl = load(P)
anchor(P, pl, 61, "theorem core_calls_portsG {c : Name} (d : MachineData) (ok : d.ok = true)")
anchor(P, pl, 87, "    CallsPorts c d kD b := by")
anchor(P, pl, 261, "      exact hw1")
anchor(P, pl, 262, "")
ports = seg(pl, 61, 261)
ports = rep(ports, "theorem core_calls_portsG {c : Name}", "theorem core_calls_portsGM {c : Name}")
ports = rep(ports, HNOMEM, "")
ports = rep(ports,
            "  have hkf := Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy\n"
            "    hnomem hB hcore hpost entry closes\n",
            "  have hkf := Tools.ShippingMemKid.core_kids_factsM d ok hbody hC hslots hdomB hins outTy\n"
            "    hfne hB hcore hpost entry closes\n")
if "hnomem" in ports:
    sys.exit("core_calls_portsGM still mentions hnomem")

# ------------------------------------------------------------ kids_run_kidM
Q = "Tools/ShippingChecksCore.lean"
ql = load(Q)
anchor(Q, ql, 287, "theorem kids_run_kid {c : Name} (d : MachineData) (ok : d.ok = true)")
anchor(Q, ql, 318, "      ∃ g2 ∈ design.modules, g2.name = mn) := by")
anchor(Q, ql, 356, "      exact ⟨g', by rw [hdes]; exact hg'D, hn'.trans hn2⟩")
anchor(Q, ql, 357, "")
runk = seg(ql, 287, 356)
runk = rep(runk, "theorem kids_run_kid {c : Name}", "theorem kids_run_kidM {c : Name}")
runk = rep(runk,
           "    (namesK : Nat → List String)\n" + HNOMEM,
           "    (hfne : d.shape.instFields ≠ [])\n"
           "    (nameK : Nat → String) (namesK : Nat → List String)\n")
runk = rep(runk,
           "      RealChild mref cref (d.shape.insts[k]).1 y →\n"
           "      KidNames (d.shape.insts[k]).1 (namesK k) y.1 y.2)\n",
           "      Tools.ShippingMemKid.Kid mref cref (d.shape.insts[k]).1 y →\n"
           "      Tools.ShippingKidsChildIfaceM.KidNamesP (nameK k) (namesK k) y.1 y.2)\n")
runk = rep(runk,
           "      RealChild mref cref (d.shape.insts[k]).1 y →\n",
           "      Tools.ShippingMemKid.Kid mref cref (d.shape.insts[k]).1 y →\n", count=2)
runk = rep(runk,
           "    (hself : (Sparkle.IR.ModuleName.ofDecl c) ∉ namesOf d namesK)\n",
           "    (hself : (Sparkle.IR.ModuleName.ofDecl c) ∉\n"
           "      Tools.ShippingKidsChildIfaceM.namesOfP d nameK namesK)\n")
runk = rep(runk,
           "    core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem (ChildBnd.of_invW mctx cctx hw) hcore hpost entry closes\n",
           "    Tools.ShippingMemKid.core_kids_factsM d ok hbody hC hslots hdomB hins outTy hfne\n"
           "      (ChildBnd.of_invW mctx cctx hw) hcore hpost entry closes\n")
runk = rep(runk,
           "    have hxn : x.name ∈ namesOf d namesK := by\n",
           "    have hxn : x.name ∈ Tools.ShippingKidsChildIfaceM.namesOfP d nameK namesK := by\n")
runk = rep(runk,
           "        exact List.mem_append_left _ (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩)\n",
           "        exact List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)\n")
for bad in ("hnomem", "RealChild", "KidNames ", "namesOf d"):
    if bad in runk:
        sys.exit(f"kids_run_kidM still mentions {bad!r}")

# ------------------------------------------------------------ kidsM_designCheck_in
G = "Tools/ShippingGenKid.lean"
gl = load(G)
anchor(G, gl, 109, "theorem kids_designCheck_in {c : Name} (d : MachineData) (ok : d.ok = true)")
anchor(G, gl, 137, "    Tools.ShippingDesignSV.designCheck (childMap ms) n b = true := by")
anchor(G, gl, 224, "    hkids")
anchor(G, gl, 225, "")
chk = seg(gl, 109, 224)
chk = rep(chk, "theorem kids_designCheck_in {c : Name}", "theorem kidsM_designCheck_in {c : Name}")
chk = rep(chk, HNOMEM, "")
chk = rep(chk,
          "      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)\n",
          "      Tools.ShippingMemKid.KidFactsM mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)\n")
chk = rep(chk,
          "  have hkidW := Tools.ShippingCallWidths.hkidW_of_data hcw\n",
          "  have hkidW := Tools.ShippingMemKid.hkidW_of_dataM hcw\n")
chk = rep(chk,
          "    Tools.ShippingKidFacts.kids_runFacts d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem\n",
          "    Tools.ShippingMemKid.kidsM_runFacts d ok hbody hC hslots hdomB hins hsl hfne outTy\n")
chk = rep(chk,
          "  have hwf := Tools.ShippingLinkedFresh.core_linkedWF d ok hbody hC hslots hdomB hins outTy\n"
          "    hnomem hB hcore hpost entry closes\n",
          "  have hwf := Tools.ShippingMemKid.core_linkedWFM d ok hbody hC hslots hdomB hins outTy\n"
          "    hfne hB hcore hpost entry closes\n")
chk = rep(chk,
          "  have hT := Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy\n"
          "    hnomem hB hcore hpost entry closes hon hoty\n",
          "  have hT := Tools.ShippingMemKid.core_closed_typedInM d ok hbody hC hslots hdomB hins outTy\n"
          "    hfne hB hcore hpost entry closes hon hoty\n")
chk = rep(chk,
          "    Tools.ShippingPortsMatchRaw.core_portsMatch_raw d ok hbody hC hslots hdomB hins hfne outTy\n"
          "      hnomem hkidW\n",
          "    Tools.ShippingMemKid.core_portsMatch_rawM d ok hbody hC hslots hdomB hins hfne outTy\n"
          "      hkidW\n")
chk = rep(chk,
          "      (Tools.ShippingCoreClk.core_clk d ok hbody hC hslots hdomB hins outTy hnomem hsl hB hcore\n"
          "        hpost entry closes)\n",
          "      (Tools.ShippingMemKid.core_clkM d ok hbody hC hslots hdomB hins outTy hfne hsl hB hcore\n"
          "        hpost entry closes)\n")
chk = rep(chk,
          "    Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB\n"
          "      hcore hpost entry closes\n",
          "    Tools.ShippingMemKid.core_kids_factsM d ok hbody hC hslots hdomB hins outTy hfne hB\n"
          "      hcore hpost entry closes\n")
chk = rep(chk,
          "  have hselfD := Tools.ShippingKidsSelf.core_kids_self d ok hbody hC hslots hdomB hins hnomem\n"
          "    hB hcore entry closes\n",
          "  have hselfD := Tools.ShippingMemKid.core_kids_selfM d ok hbody hC hslots hdomB hins hfne\n"
          "    hB hcore entry closes\n")
if "hnomem" in chk:
    sys.exit("kidsM_designCheck_in still mentions hnomem")

STD_OPENS = '''open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
'''

VARS = '''variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
'''

HEADER = '''import Tools.ShippingGenKid
import Tools.ShippingMemKidFacts
import Tools.ShippingKidsChildIfaceM
import Tools.ShippingKidFactsT

/-! # A general-closing callee whose own callees may be MEMORY placeholders, as a child (round par/d-1)

WRITTEN, NOT BUILT. The three long proofs are GENERATED by
`scripts/gen_genkid_m.py` from BUILT proofs (asserted single-occurrence
replacements, anchored on the built files' lines); the short theorems and
the structure are written by hand.

`Tools.ShippingGenKid.GenKid` is the interface of a callee whose own calls
are tied by the general closing, with the field
`nomem : ∀ c ∈ dk.shape.insts, memChild? c.1 = none`. A register machine
with a memory read (`memCounterH`) has a memory placeholder among its call
entries and fails it. `GenKidM` is `GenKid` without `nomem`, its callees
taken as the general closing takes them (`Tools.ShippingMemKid.Kid`: the
built memory module for a placeholder, a real child otherwise), described by
`KidNamesP` (the child module's name a parameter) and by
`Tools.ShippingMemKid.KidFactsM … n`, with NO `kidsHi`. Its conclusion is

    GenKidM.factsT : KidFactsT mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1)

— `Tools.ShippingKidFactsT.KidFactsT`, the check of the callee's OWN module
only: `KidFacts … (n + 1)` is FALSE of a callee with a memory module in its
design (`docs/parallel/C-mem-depth-free.md` §2).

## Per field: built `M` lemma, or the `M` form derived here

| field of `KidFactsT` | `GenKid` uses | here |
|---|---|---|
| (the bridge `core`) | `core_kids_facts`, `KidNames` | BUILT `Tools.ShippingMemKid.core_kids_factsM` (`Tools/ShippingChecksCore.lean` 449), `KidNamesP` / `namesOfP` (`Tools/ShippingKidsChildIfaceM.lean`) |
| `outsIn` | `kidsChild_of_real` | BUILT `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM` |
| `kidA`, `kidR` | `kids_real_kid` | DERIVED HERE: `kids_run_kidM`, `kids_real_kidM` (the built proof of `kids_run_kid`, by script, over `core_kids_factsM`) |
| `outTys`, `inW` | `core_calls_portsG` → `CallsPorts` | DERIVED HERE: `core_calls_portsGM` (the built proof, by script: its ONLY use of `hnomem` is the call of `core_kids_facts`). The built `core_callPorts_fromM` is another statement (the connections of the instances, not `CallsPorts`) |
| `portsIn` | `core_closed_typedIn` | BUILT `core_closed_typedInM` (`Tools/ShippingMemKidPorts.lean` 53) |
| `masked` | `outsMaskedN_of_callsG` + `core_conn_refsG` | `outsMaskedN_of_callsG` is PURE (no closing premise): used as built. `core_conn_refsGM` DERIVED HERE from the BUILT `core_callConnsM` (`Tools/ShippingMemKidPorts.lean` 430) |
| `clk` | `core_clk` | BUILT `core_clkM` (`Tools/ShippingMemKidPorts.lean` 300) |
| `check` (own module) | `kids_designCheck_in` | DERIVED HERE: `kidsM_designCheck_in` (the built proof, by script, over the BUILT `kidsM_runFacts`, `core_linkedWFM`, `core_closed_typedInM`, `core_portsMatch_rawM`, `core_clkM`, `core_kids_factsM`, `core_kids_selfM`, `hkidW_of_dataM`) |

`kidsM_designCheck_in` keeps BOTH conjuncts of `KidFactsM.check` for the
callee's callees (the uniform form): a memory placeholder has them at depth
0 (`memKid_facts`), where the module is its own design. So `GenKidM` at
`n = 0` covers "a register machine whose calls are memory placeholders and /
or leaf register machines"; at `n ≥ 1` its callees must have `KidFactsM … n`
(no memory at or below them).

SCOPE: a callee WITH a register (`slots`), with calls, the general closing in
the callee. No name separation is asked beyond `self` (the callee's own
module name is not a name below it), as `GenKid`. -/
namespace Tools.ShippingGenKidM

'''

SEC_PORTS = ('''section PortsG
''' + STD_OPENS + '''open Tools.ShippingPortWidthsPure
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)

''' + VARS + '''
set_option maxHeartbeats 4000000 in
/-- **The ports of the full entry's module of a machine with a register whose
calls are tied by the GENERAL closing, its callees possibly memory
placeholders**, from its core run: `core_calls_portsG`
(`Tools/ShippingCallsPortsG.lean` 61-261) without `hnomem` — its proof reads
`hnomem` only to call `core_kids_facts`, here `core_kids_factsM`. -/
''' + ports + '''

set_option maxHeartbeats 4000000 in
/-- **Every reference connection of an instance of the full entry's module is
the clock, the reset, or a wire of the module** (`core_conn_refsG` over the
built `core_callConnsM`). -/
theorem core_conn_refsGM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∀ cn ∈ conns, ∀ x, cn.2 = Sparkle.IR.AST.Expr.ref x →
        x = "clk" ∨ x = "rst" ∨ x ∈ b.wires.map (·.name) := by
  have hconn := Tools.ShippingMemKid.core_callConnsM d ok hbody hC hslots hdomB hins hfne
    outTy hB hcore hpost entry closes
  intro mn iname conns hst cn hcm x hc2
  obtain ⟨mc, -, -, hall⟩ := hconn mn iname conns hst
  have hcm' : (cn.1, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
    rw [← hc2]
    exact hcm
  rcases hall cn.1 x hcm' with ⟨-, h⟩ | ⟨hxw, -⟩
  · rcases h with ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr hxw)

end PortsG

''')

SEC_RUN = ('''section RunKid
''' + STD_OPENS + '''
''' + VARS + '''
set_option maxHeartbeats 4000000 in
/-- **`hkidA` and `hkidR` of a machine with calls that may be memory reads, at
its full entry**, from the same two facts of ITS kids: `kids_run_kid`
(`Tools/ShippingChecksCore.lean` 287-356) over `Kid`, `KidNamesP` and
`core_kids_factsM`. -/
''' + runk + '''

/-- **`hkidA` and `hkidR` of a real child WITH calls that may be memory
reads**, from its `RealChild` witness and the same facts of its own kids
(`kids_real_kid` over `kids_run_kidM`). -/
theorem kids_real_kidM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hfne : d.shape.instFields ≠ [])
    (nameK : Nat → String) (namesK : Nat → List String)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingMemKid.Kid mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingKidsChildIfaceM.KidNamesP (nameK k) (namesK k) y.1 y.2)
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingMemKid.Kid mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Tools.ShippingMemKid.Kid mref cref (d.shape.insts[k]).1 y →
      ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
        ∃ g2 ∈ y.2.modules, g2.name = mn)
    (hself : (Sparkle.IR.ModuleName.ofDecl c) ∉
      Tools.ShippingKidsChildIfaceM.namesOfP d nameK namesK)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineClosesAt mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChild mref cref c y) :
    (Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true) ∧
    (∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn) := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact kids_run_kidM d ok hbody hC hslots hdomB hins outTy hfne nameK namesK hkid hkidA hkidR
    hself hw hr (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

end RunKid

''')

SEC_CHECK = ('''section Check
''' + STD_OPENS + '''open Tools.ShippingChildMapCongr (AgreeOn)

''' + VARS + '''
set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth `n` of the UNOPTIMISED full-entry module of a
machine with a register tied by the general closing, its callees possibly
memory placeholders, against ANY module list that resolves the modules of
the run's design to themselves**, from `KidFactsM` at depth `n` of every
call entry's callee and the two width conditions. No check premise.
`kids_designCheck_in` (`Tools/ShippingGenKid.lean` 109-224) over the built
`M` lemmas. -/
''' + chk + '''

end Check

''')

SEC_IFACE = ('''section Iface
''' + STD_OPENS + '''open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingKidFactsT (KidFactsT)
open Tools.ShippingGenKid (kidCheck_succ)

''' + VARS + '''
/-- **A callee with a register whose own calls are tied by the general
closing and may be memory reads**: its data conditions, its reflection and
closing in every context, `KidNamesP` of its kids, and `KidFactsM` of its
call entries' callees at the depth `n`. `GenKid` without `nomem` and without
`kidsHi`. -/
structure GenKidM (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) (c : Name) (dk : MachineData) (nDecl : Nat)
    (nameK : Nat → String) (namesK : Nat → List String)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat) : Prop where
  ok : dk.ok = true
  body : dk.shape.body = quote dk.dom
    (fun j => inputExpr dk.shape.binders.length (dk.bpos j))
    (fun j => inputExpr dk.shape.binders.length (dk.vpos j)) dk.packed
  calls : dk.callsOk nDecl = true
  ss : dk.ss.length = dk.shape.layout.slots.length
  dom : ∀ b ∈ dk.shape.binders.drop nDecl, b.2 ≠ .domain
  insts : dk.shape.insts ≠ []
  general : dk.shape.instFields ≠ []
  slots : dk.shape.layout.slots ≠ []
  outTy : ∀ o ∈ dk.shape.layout.outs, o.ty.bitWidth = o.width
  outName : ∀ o ∈ dk.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name
  outScalar : ∀ o ∈ dk.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true
  -- the argument split at `nDecl` (the data conditions of `kidsChild_ifaceM`)
  hkD : nDecl ≤ dk.bsIn.length
  hIlen : (dk.bsIn.drop nDecl).length = dk.shape.insts.length
  hSL : ∀ b ∈ dk.slotBs ++ dk.letBs, b.2 ≠ .domain
  hSlen : dk.slotBs.length = dk.shape.layout.slots.length
  hLlen : dk.letBs.length = dk.shape.layout.lets
  hNIn : machNIn dk.shape = ((dk.bsIn.take nDecl).filter (fun b => b.2 != .domain)).length
  -- its own kids (the built memory module for a placeholder): names
  kid : ∀ (k : Nat) (hk : k < dk.shape.insts.length) (y : Res),
    Tools.ShippingMemKid.Kid mref cref (dk.shape.insts[k]).1 y →
    Tools.ShippingKidsChildIfaceM.KidNamesP (nameK k) (namesK k) y.1 y.2
  self : (Sparkle.IR.ModuleName.ofDecl c) ∉
    Tools.ShippingKidsChildIfaceM.namesOfP dk nameK namesK
  -- its own callees: the interface one level down, at the depth `n`
  kidsLo : ∀ (k : Nat) (hk : k < dk.shape.insts.length),
    Tools.ShippingMemKid.KidFactsM mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) n
  -- its two width conditions against its callees' tables
  callW : Tools.ShippingCallWidths.callWidthsOk dk nDecl kidOuts = true
  callA : Tools.ShippingPortsMatchRaw.callArgsOk dk nDecl kidIns = true
  -- its reflection and its closing, in every context
  entry : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
    MachineDefines mctx' mref cctx' cref c dk.shape
  closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
    MachineClosesAt mctx' mref cctx' cref c dk.shape

variable {c : Name} {dk : MachineData} {nDecl : Nat} {nameK : Nat → String}
  {namesK : Nat → List String} {kidOuts : Nat → List OutField} {kidIns : Nat → List Nat}
  {n : Nat}

set_option maxHeartbeats 4000000 in
/-- **THE BRIDGE: a real child of such a callee is the post-processing of a
core run of the callee, and its design is that run's** (`GenKid.core`, over
`core_kids_factsM` and `KidNamesP`). -/
theorem GenKidM.core (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) :
    ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (w w1 : Void IO.RealWorld)
      (M : Sparkle.IR.AST.Module) (D : Design),
      ChildBnd mref cref w ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx' mref cctx' cref w (M, D) w1 ∧
      (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      y.2.modules = D.modules := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := hy.inv
  obtain ⟨M, D, w1, hcore, hpost, hdesL⟩ :=
    synthesizeCombinational_designL (M' := y.1) (D' := y.2) hr
  have hB : ChildBnd mref cref w := ChildBnd.of_invW mctx' cctx' hw
  obtain ⟨hMn, -, -, -, hrealD, -⟩ :=
    Tools.ShippingMemKid.core_kids_factsM dk K.ok K.body K.calls K.ss K.dom K.insts K.outTy
      K.general hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx')
  refine ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, hdesL (fun x hx e => K.self ?_)⟩
  obtain ⟨k, hk, y', hre, hor, -⟩ := hrealD x hx
  have full := K.kid k hk y' hre
  have hxn : x.name ∈ Tools.ShippingKidsChildIfaceM.namesOfP dk nameK namesK := by
    rcases hor with heq | hin
    · rw [heq, full.name]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
    · exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, full.desNames x hin⟩)
  rw [← hMn, ← e]
  exact hxn

/-- `hkidP`: no output port of the served module is an argument port, the
clock or the reset (`kidsChild_of_realM`). -/
theorem GenKidM.outsIn (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) :
    ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
      p.name ≠ "rst" := by
  obtain ⟨mctx', cctx', _, _, _, _⟩ := hy.inv
  exact (Tools.ShippingKidsChildIfaceM.kidsChild_of_realM dk K.ok K.body K.calls K.ss K.dom
    K.insts K.slots K.outTy nDecl K.hkD K.hIlen K.hSL K.hSlen K.hLlen K.hNIn K.general
    nameK namesK K.kid K.self (K.entry mctx' cctx') (fun mc cc _ => K.closes mc cc) hy).outsIn

/-- `hkidA` and `hkidR` (`kids_real_kidM`, with the kids' from `kidsLo`). -/
theorem GenKidM.kidAR (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) :
    (Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true) ∧
    (∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn) := by
  obtain ⟨mctx', cctx', _, _, _, _⟩ := hy.inv
  exact kids_real_kidM dk K.ok K.body K.calls K.ss K.dom K.insts K.outTy K.general
    nameK namesK K.kid
    (fun k hk y' hy' => (K.kidsLo k hk).kidA y' hy')
    (fun k hk y' hy' => (K.kidsLo k hk).kidR y' hy')
    K.self (K.entry mctx' cctx') K.closes hy

/-- The ports of the served module (`core_calls_portsGM` at the callee's run). -/
theorem GenKidM.ports (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) : CallsPorts c dk nDecl y.1 := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact core_calls_portsGM dk K.ok K.body K.calls K.ss K.dom K.insts K.general K.outTy K.slots
    nDecl K.hkD K.hIlen K.hSL K.hSlen K.hLlen K.hNIn
    hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx')

/-- The served module is typed in its own wire table (`core_closed_typedInM`). -/
theorem GenKidM.typedIn (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n)
    {y : Res} (hy : RealChild mref cref c y) : Tools.ShippingTextTyped.TypedIn y.1 := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingMemKid.core_closed_typedInM dk K.ok K.body K.calls K.ss K.dom K.insts
    K.outTy K.general hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx') K.outName
    K.outScalar

/-- `hkidM` (the child's own module): its outputs are masked and no instance
connection names one. The module's memory is an INSTANCE of the memory
module, not a memory statement of its body. -/
theorem GenKidM.masked (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingCallsPortsG.outsMaskedN_of_callsG (K.ports hy) (K.typedIn hy)
    (fun p hp => (K.outsIn hy p hp).2)
    (core_conn_refsGM dk K.ok K.body K.calls K.ss K.dom K.insts K.general K.outTy
      hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx'))

/-- `hkidClk`: the clock and the reset are one bit in the emitted width map
(`core_clkM` at the callee's run: it has a register of its own). -/
theorem GenKidM.clk (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) :
    Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1 := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, -⟩ := K.core hy
  exact Tools.ShippingMemKid.core_clkM dk K.ok K.body K.calls K.ss K.dom K.insts K.outTy
    K.general K.slots hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx')

set_option maxHeartbeats 4000000 in
/-- **The check of the served module at depth `n`**, against every module
list that resolves the modules of the served design to themselves
(`kidsM_designCheck_in` at the callee's own core run). -/
theorem GenKidM.check (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.designCheck (childMap ms) n y.1 = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, hdes⟩ := K.core hy
  have entry := K.entry mctx' cctx'
  have closes := K.closes mctx' cctx'
  have hmsD : ∀ g ∈ D.modules, moduleByName ms g.name = some g := fun g hg =>
    hms g (by rw [hdes]; exact hg)
  exact kidsM_designCheck_in dk K.ok K.body K.calls K.ss K.dom K.insts K.slots K.general
    K.outTy kidOuts kidIns n K.kidsLo K.callW K.callA hB hcore hpost entry closes
    K.outName K.outScalar ms hmsD

/-- **`KidFactsT` of a callee with a register whose own calls are tied by the
general closing and may be memory reads, at depth `n + 1`**, from `KidFactsM`
of its call entries' callees at the depth `n`. -/
theorem GenKidM.factsT (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n) :
    KidFactsT mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1) :=
  { outsIn := fun _ hy => K.outsIn hy
    outTys := fun _ hy => ⟨(K.ports hy).outs⟩
    kidA := fun _ hy => (K.kidAR hy).1
    kidR := fun _ hy => (K.kidAR hy).2
    masked := fun _ hy => K.masked hy
    portsIn := fun _ hy => Tools.ShippingLeafTyped.PortsIn.of_typedIn (K.typedIn hy)
    inW := fun _ hy _ _ hq => (K.ports hy).inWidths (K.typedIn hy).wn hq
    clk := fun _ hy _ => K.clk hy
    check := fun y hy ms _ h2 =>
      (kidCheck_succ (childMap ms) n y.1).trans (K.check hy ms h2) }

end Iface

end Tools.ShippingGenKidM
''')

out = HEADER + SEC_PORTS + SEC_RUN + SEC_CHECK + SEC_IFACE
if "/-" in out.replace("/-!", "").replace("/--", ""):
    sys.exit("a nested comment opener in the generated text")
open(OUT, "w", encoding="utf-8").write(out)
print(f"wrote {OUT}: {out.count(chr(10))} lines")
