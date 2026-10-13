#!/usr/bin/env python3
"""Generate Tools/ShippingCallSelf.lean (round par/d-1) from two BUILT files:

  Tools/ShippingPortsMatchRaw.lean  core_callConns (lines 247-356)  -> core_callSelf
  Tools/ShippingKidFactsT.lean      core_kidsPass_top (statement)         -> core_kidsPass_own
                                    kidsT_designCheck                     -> kidsT_designCheckO

Every replacement is asserted to occur exactly once in the segment it is
applied to, and every segment is anchored on the built file's lines; the
script fails otherwise. It reads and writes files only; it starts no build.

Run from the repository root:  python3 scripts/gen_call_self.py
"""
import sys

OUT = "Tools/ShippingCallSelf.lean"


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


# ------------------------------------------------------------ core_callSelf
P = "Tools/ShippingPortsMatchRaw.lean"
pl = load(P)
anchor(P, pl, 247, "theorem core_callConns {c : Name} (d : MachineData) (ok : d.ok = true)")
anchor(P, pl, 264, "    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :")
anchor(P, pl, 265, "    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →")
anchor(P, pl, 282, "                  Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth))) := by")
anchor(P, pl, 283, "  have hbody' : b.body = M.body :=")
anchor(P, pl, 352, "  obtain ⟨hk0, y0, hre0, hmcy0⟩ := hrealE e0 he0")
anchor(P, pl, 356, "    exact hfind")
head = seg(pl, 247, 264)
head = rep(head, "theorem core_callConns {c : Name}", "theorem core_callSelf {c : Name}")
body = seg(pl, 283, 356)
body = rep(body,
           "  have hrealE : ∀ e ∈ outs, ∃ (hk : e.1 < d.shape.insts.length) (y : Res),\n"
           "      RealChild mref cref (d.shape.insts[e.1]).1 y ∧ mc = y.1 := by\n",
           "  have hrealE : ∀ e ∈ outs, ∃ (hk : e.1 < d.shape.insts.length) (y : Res),\n"
           "      RealChild mref cref (d.shape.insts[e.1]).1 y ∧ mc = y.1 ∧\n"
           "      moduleByName D.modules y.1.name = some y.1 ∧\n"
           "      ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 := by\n")
body = rep(body,
           "    · have hyfind :=\n"
           "        ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y\n"
           "          (List.mem_of_getElem? hy)).1\n"
           "      rw [hyn, hfind] at hyfind\n"
           "      exact ⟨hk0, y, hre, Option.some.inj hyfind⟩\n",
           "    · -- the closing's own check: the child, and every module of its design,\n"
           "      -- is found by its name in the merged design as itself\n"
           "      have hyS := (Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y\n"
           "        (List.mem_of_getElem? hy)\n"
           "      have hyfind := hyS.1\n"
           "      rw [hyn, hfind] at hyfind\n"
           "      exact ⟨hk0, y, hre, Option.some.inj hyfind, hyS.1, hyS.2⟩\n")
body = rep(body,
           "  obtain ⟨hk0, y0, hre0, hmcy0⟩ := hrealE e0 he0\n",
           "  obtain ⟨hk0, y0, hre0, hmcy0, hs1, hs2⟩ := hrealE e0 he0\n")
CONCL = (
    "    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →\n"
    "      ∃ mc, moduleByName D.modules mn = some mc ∧\n"
    "        ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),\n"
    "          RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧\n"
    "          moduleByName D.modules y.1.name = some y.1 ∧\n"
    "          ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2 := by\n")
callself = head + "\n" + CONCL + body + "\n  exact ⟨mc, hfind', e0.1, hk0, y0, hre0, hmcy0, hs1, hs2⟩"

# ------------------------------------------------------------ from ShippingKidFactsT
T = "Tools/ShippingKidFactsT.lean"
tl = load(T)
anchor(T, tl, 108, "theorem core_kidsPass_top {c : Name} (d : MachineData) (ok : d.ok = true)")
anchor(T, tl, 143, "      (checkedOptimize b).body = true := by")
anchor(T, tl, 279, "theorem kidsT_designCheck {c : Name} (d : MachineData) (ok : d.ok = true)")
anchor(T, tl, 340, "    hkidW hB hcore hpost entry closes hon hoty n hports hkids")
NAMES = (
    "    (namesK : Nat → List String)\n"
    "    (hname : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),\n"
    "      RealChild mref cref (d.shape.insts[k]).1 y →\n"
    "      y.1.name = Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1 ∧\n"
    "        ∀ g ∈ y.2.modules, g.name ∈ namesK k)\n"
    "    (hsep : ∀ (k : Nat) (_ : k < d.shape.insts.length) (k' : Nat)\n"
    "      (_ : k' < d.shape.insts.length),\n"
    "      Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1 ∉ namesK k')\n")
passS = seg(tl, 108, 143)
passS = rep(passS, "theorem core_kidsPass_top {c : Name}", "theorem core_kidsPass_own {c : Name}")
passS = rep(passS, NAMES, "")
PASS_PROOF = '''
  have hbody' : b.body = M.body :=
    (Tools.ShippingChecksCore.core_kids_facts d ok hbody hC hslots hdomB hins outTy hnomem hB
      hcore hpost entry closes).2.1
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingChecksWidths.core_hierGate d ok hbody hC hslots hdomB hins hfne outTy hnomem
      hB hcore hpost entry closes
  have hown := core_callSelf d ok hbody hC hslots hdomB hins hfne outTy hnomem hB hcore hpost
    entry closes
  unfold Tools.ShippingDesignSV.kidsPass
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    have hm : Stmt.inst mn iname conns ∈ b.body :=
      (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hgate mn iname conns).mp hst
    obtain ⟨mc, hmc, k, hk, y, hre, e, hs1, hs2⟩ := hown mn iname conns hm
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp only [hCm]
    rw [e]
    exact hkidK k hk y hre D.modules hs1 hs2
  | _ => rfl'''
dc = seg(tl, 279, 340)
dc = rep(dc, "theorem kidsT_designCheck {c : Name}", "theorem kidsT_designCheckO {c : Name}")
dc = rep(dc, NAMES, "")
dc = rep(dc,
         "  have hkids := core_kidsPass_top d ok hbody hC hslots hdomB hins hfne\n"
         "    outTy hnomem n\n"
         "    (fun k hk y hy ms h1 h2 => (hkid k hk).check y hy ms h1 h2)\n"
         "    namesK hname hsep\n"
         "    hB hcore hpost entry closes\n",
         "  have hkids := core_kidsPass_own d ok hbody hC hslots hdomB hins hfne\n"
         "    outTy hnomem n\n"
         "    (fun k hk y hy ms h1 h2 => (hkid k hk).check y hy ms h1 h2)\n"
         "    hB hcore hpost entry closes\n")
for t in (passS, dc):
    for bad in ("namesK", "hname", "hsep"):
        if bad in t:
            sys.exit(f"a name premise is left: {bad}")

HEADER = '''import Tools.ShippingKidFactsT

/-! # Every instance of a general-closing parent resolves to a real child's OWN module, which the design resolves with its design (round par/d-1)

WRITTEN, NOT BUILT. GENERATED by `scripts/gen_call_self.py` from BUILT proofs
(asserted single-occurrence replacements, anchored on the built files'
lines); the proof of `core_kidsPass_own` is written by hand.

`Tools.ShippingKidFactsT.core_kidsPass_top` (BUILT) derives the children's
check of a parent from the check of each real child's OWN module, under two
NAME premises (`hname`, `hsep`): it combines

* `core_callConns` — an instance resolves to `y₂.1` for SOME real child
  `y₂` of an entry `k₂`, with
* `core_kids_self` — the instance's module is `y.1` or a module of `y`'s
  design for SOME real child `y` of an entry `k`, and the design resolves
  `y.1` and the modules of `y`'s design to themselves,

and `y₂` need not be `y`; the names exclude the second case of the second
fact. `hsep` is asked of ALL pairs of entries and is FALSE when a callee is
also a descendant of another callee (`memGrand`: `cnt` is a callee, and a
callee of the callee `memParent`; the `mixDeep` shape).

Both facts are read off ONE list (the closing's `children`):
`core_callConns`'s proof finds the instance's child as `children[e.1]` and
already calls the closing's own check `closeInstsG_names … y` for it — and
keeps only its first half. `core_callSelf` is that proof's first 110 lines
with the second half kept:

    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        ∃ k hk y, RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
          moduleByName D.modules y.1.name = some y.1 ∧
          ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2

From it, with NO name premise:

* `core_kidsPass_own`: `core_kidsPass_top`'s statement without `namesK`,
  `hname`, `hsep`;
* `kidsT_designCheckO`: `kidsT_designCheck`'s statement without them (its
  built proof, `core_kidsPass_own` for `core_kidsPass_top`).

SCOPE, as the built theorems: a parent WITH a register under the general
closing, NO memory entry of its own (`hnomem`). Nothing of the built files
changes; the built `kidsT_designCheck` stays (the hand endpoint of
`memParent` uses it). -/
namespace Tools.ShippingCallSelf
open Lean Meta
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
open Tools.ShippingKidFactsT (KidFactsT)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **Every instance statement of the full entry's module of a parent tied by
the general closing resolves to a real child's OWN module, and the design
resolves that child's module and the modules of its design to themselves**
(`core_callConns`, `Tools/ShippingPortsMatchRaw.lean` 247-356, with the
second half of the closing's check `closeInstsG_names` kept). -/
'''

out = (HEADER + callself + "\n\n"
       "set_option maxHeartbeats 4000000 in\n"
       "/-- **The children's check of the shipped module, at depth `n`, from the\n"
       "check of each real child's OWN module only, with no name premise**\n"
       "(`core_callSelf`). -/\n"
       + passS + PASS_PROOF + "\n\n"
       "set_option maxHeartbeats 4000000 in\n"
       "/-- **`designCheck` of the shipped module at depth `n` with NO check premise\n"
       "and NO name premise**, from `KidFactsT` (`kidsT_designCheck`'s proof,\n"
       "`Tools/ShippingKidFactsT.lean` 279-340, with `core_kidsPass_own`). -/\n"
       + dc + "\n\nend Tools.ShippingCallSelf\n")
if "/-" in out.replace("/-!", "").replace("/--", ""):
    sys.exit("a nested comment opener in the generated text")
open(OUT, "w", encoding="utf-8").write(out)
print(f"wrote {OUT}: {out.count(chr(10))} lines")
