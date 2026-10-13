#!/usr/bin/env python3
"""Generate Tools/ShippingGenKidT.lean from the BUILT Tools/ShippingGenKid.lean
(round par/d-1). Every replacement is asserted to occur exactly once (or the
stated number of times) in the segment it is applied to; the script fails
otherwise. It reads and writes files only; it starts no build.

Run from the repository root:  python3 scripts/gen_genkid_t.py
"""
import sys

SRC = "Tools/ShippingGenKid.lean"
OUT = "Tools/ShippingGenKidT.lean"

lines = open(SRC, encoding="utf-8").read().split("\n")


def seg(first, last):
    """Lines first..last (1-based, inclusive) of the built file."""
    return "\n".join(lines[first - 1:last])


def rep(text, old, new, count=1):
    n = text.count(old)
    if n != count:
        sys.exit(f"replacement expected {count} occurrence(s), found {n}:\n{old}")
    return text.replace(old, new)


# anchors: the built file must be the one this script was written against
def anchor(lineno, text):
    if lines[lineno - 1] != text:
        sys.exit(f"{SRC}:{lineno} is not\n{text}\nbut\n{lines[lineno - 1]}")


anchor(103, "set_option maxHeartbeats 4000000 in")
anchor(109, "theorem kids_designCheck_in {c : Name} (d : MachineData) (ok : d.ok = true)")
anchor(224, "    hkids")
anchor(230, "structure GenKid (mref : ST.Ref IO.RealWorld Meta.State)")
anchor(272, "    MachineClosesAt mctx' mref cctx' cref c dk.shape")
anchor(274, "variable {c : Name} {dk : MachineData} {nDecl : Nat} {namesK : Nat → List String}")
anchor(277, "set_option maxHeartbeats 4000000 in")
anchor(368, "    K.slots hB hcore hpost (K.entry mctx' cctx') (K.closes mctx' cctx')")

# ---------------------------------------------------------------- (a) kids_designCheck_inT
a = seg(103, 224)
a = rep(a, "theorem kids_designCheck_in {c : Name}", "theorem kids_designCheck_inT {c : Name}")
a = rep(a,
        "/-- **`designCheck` at depth `n` of the UNOPTIMISED full-entry module of a\n"
        "machine with a register tied by the general closing, against ANY module list\n"
        "that resolves the modules of the run's design to themselves**, from\n"
        "`KidFacts` at depth `n` of every call entry's callee and the two width\n"
        "conditions. No check premise. -/",
        "/-- **`designCheck` at depth `n` of the UNOPTIMISED full-entry module of a\n"
        "machine with a register tied by the general closing, against ANY module list\n"
        "that resolves the modules of the run's design to themselves**, from\n"
        "`KidFactsT` at depth `n` of every call entry's callee (the check of each\n"
        "callee's OWN module only) and the two width conditions. No check premise,\n"
        "no name premise.\n\n"
        "`kids_designCheck_in`'s proof (`Tools/ShippingGenKid.lean` 109-224) with the\n"
        "children's check by `Tools.ShippingCallSelf.core_callSelf`: an instance of\n"
        "the module resolves to a real child's OWN module, and the run's design\n"
        "resolves that child's module and the modules of its design to themselves. -/")
a = rep(a,
        "      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)\n"
        "    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)\n"
        "    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)\n",
        "      KidFactsT mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)\n"
        "    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)\n"
        "    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)\n")
a = rep(a,
        "    Tools.ShippingKidFacts.kids_runFacts d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem\n",
        "    Tools.ShippingKidFactsT.kidsT_runFacts d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem\n")
a = rep(a,
        "  have hselfD := Tools.ShippingKidsSelf.core_kids_self d ok hbody hC hslots hdomB hins hnomem\n"
        "    hB hcore entry closes\n",
        "  have hown := Tools.ShippingCallSelf.core_callSelf d ok hbody hC hslots hdomB hins hfne\n"
        "    outTy hnomem hB hcore hpost entry closes\n")
a = rep(a,
        "  -- the children's check: each instance's module is a real child's module or\n"
        "  -- a module of a real child's design, and `ms` resolves that child's module\n"
        "  -- and the modules of its design to themselves\n",
        "  -- the children's check: each instance's module is a real child's OWN module\n"
        "  -- (`hown`), and `ms` resolves that child's module and the modules of its\n"
        "  -- design to themselves\n")
a = rep(a,
        "      obtain ⟨mc, hmem, hc⟩ := hCm mn iname conns hst\n"
        "      obtain ⟨k, hk, y, hre, hor, hs1, hs2⟩ := hselfD mc hmem\n",
        "      obtain ⟨mc, hD1, hM1⟩ := hres mn iname conns hst\n"
        "      have hc : childMap ms mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=\n"
        "        congrArg (fun o : Option Sparkle.IR.AST.Module =>\n"
        "          o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hM1\n"
        "      obtain ⟨mc2, hmc2, k, hk, y, hre, e2, hs1, hs2⟩ := hown mn iname conns hst\n"
        "      have e : mc2 = mc := Option.some.inj (hmc2.symm.trans hD1)\n")
a = rep(a,
        "      have hchk := (hkid k hk).check y hre ms hy1 hy2\n"
        "      simp only [hc]\n"
        "      rcases hor with heq | hin\n"
        "      · rw [heq]\n"
        "        exact hchk.1\n"
        "      · exact hchk.2 mc hin\n",
        "      have hchk := (hkid k hk).check y hre ms hy1 hy2\n"
        "      simp only [hc]\n"
        "      rw [← e, e2]\n"
        "      exact hchk\n")

# ---------------------------------------------------------------- (b) the structure
b = seg(226, 272)
b = rep(b,
        "/-- **A callee with a register whose own calls are tied by the general\n"
        "closing**: its data conditions, its reflection and closing in every context,\n"
        "`KidNames` of its callees, and `KidFacts` of its callees at the depths `n`\n"
        "and `n + 1`. No field `leaf`, no field about `RealChild mref cref c`. -/",
        "/-- **A callee with a register whose own calls are tied by the general\n"
        "closing, its callees' checks about their OWN modules only**: `GenKid`\n"
        "(`Tools/ShippingGenKid.lean` 230-272) with `kidsLo` over `KidFactsT` and NO\n"
        "`kidsHi`. No field about `RealChild mref cref c`. -/")
b = rep(b, "structure GenKid (mref : ST.Ref IO.RealWorld Meta.State)",
        "structure GenKidT (mref : ST.Ref IO.RealWorld Meta.State)")
b = rep(b,
        "  -- its own callees: the same interface one level down, at the two depths\n"
        "  kidsLo : ∀ (k : Nat) (hk : k < dk.shape.insts.length),\n"
        "    KidFacts mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) n\n"
        "  kidsHi : ∀ (k : Nat) (hk : k < dk.shape.insts.length),\n"
        "    KidFacts mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) (n + 1)\n",
        "  -- its own callees: the interface one level down, the check of their OWN\n"
        "  -- modules only, at the depth `n`\n"
        "  kidsLo : ∀ (k : Nat) (hk : k < dk.shape.insts.length),\n"
        "    KidFactsT mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) n\n")

# ---------------------------------------------------------------- (c) core … clk
c = seg(274, 368)
c = rep(c, "(K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n)",
        "(K : GenKidT mref cref c dk nDecl namesK kidOuts kidIns n)", count=7)
c = rep(c, "theorem GenKid.", "theorem GenKidT.", count=7)

HEADER = '''import Tools.ShippingGenKid
import Tools.ShippingKidFactsT
import Tools.ShippingCallSelf

/-! # A general-closing callee as a child, its callees checked on their OWN modules only (round par/d-1)

WRITTEN, NOT BUILT. GENERATED by `scripts/gen_genkid_t.py` from the BUILT
`Tools/ShippingGenKid.lean` (asserted single-occurrence replacements); the
last two theorems (`GenKidT.check`, `GenKidT.factsT`) are written by hand.

`Tools.ShippingGenKid.GenKid … n` gives `KidFacts … (n + 1)` and asks
`KidFacts` of the callee's own callees at the depths `n` AND `n + 1`
(`kidsLo`, `kidsHi`): `KidFacts.check` speaks of every module of a callee's
design at one depth index. A callee with a memory module below it has no
`KidFacts` at any index (`docs/parallel/C-mem-depth-free.md` §2; measured by
`Tests/Compiler/MemKidCheckProbe.lean`), only
`Tools.ShippingKidFactsT.KidFactsT`: the check of its OWN module.

* `kids_designCheck_inT`: `kids_designCheck_in` over `KidFactsT`, the
  children's check by `Tools.ShippingCallSelf.core_callSelf` (an instance
  resolves to a real child's OWN module, which the design resolves together
  with its design) — NO name premise.
* `GenKidT mref cref c dk nDecl namesK kidOuts kidIns n`: `GenKid` with
  `kidsLo : KidFactsT … n` and no `kidsHi`.
* `GenKidT.core`, `.outsIn`, `.kidAR`, `.ports`, `.typedIn`, `.masked`,
  `.clk`: `GenKid`'s statements and proofs (they read `kidsLo` only through
  its fields `kidA`, `kidR`, which `KidFactsT` has unchanged).
* `GenKidT.check`: `designCheck (childMap ms) n y.1 = true` (the served
  module only).
* `GenKidT.factsT : KidFactsT mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1)`.

SCOPE: as `GenKid` — a callee WITH a register, with calls, the general
closing in the callee, NO memory placeholder among the callee's own callees
(`nomem`; such a callee is `Tools.ShippingGenKidM.GenKidM`). Its callees may
have memories below them, and a callee may also be a descendant of another
callee (no separation of names is asked here; the field `self`, as in
`GenKid`, is about the callee's own module name only). -/
namespace Tools.ShippingGenKidT
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
open Tools.ShippingChildMapCongr (AgreeOn)
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingKidFactsT (KidFactsT)
open Tools.ShippingGenKid (kidCheck_succ)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

'''

TAIL = '''
set_option maxHeartbeats 4000000 in
/-- **The check of the served module at depth `n`**, against every module
list that resolves the modules of the served design to themselves
(`kids_designCheck_inT` at the callee's own core run). -/
theorem GenKidT.check (K : GenKidT mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
    (hy : RealChild mref cref c y) (ms : List Sparkle.IR.AST.Module)
    (hms : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
    Tools.ShippingDesignSV.designCheck (childMap ms) n y.1 = true := by
  obtain ⟨mctx', cctx', w, w1, M, D, hB, hcore, hpost, hdes⟩ := K.core hy
  have entry := K.entry mctx' cctx'
  have closes := K.closes mctx' cctx'
  have hmsD : ∀ g ∈ D.modules, moduleByName ms g.name = some g := fun g hg =>
    hms g (by rw [hdes]; exact hg)
  exact kids_designCheck_inT dk K.ok K.body K.calls K.ss K.dom K.insts K.slots K.general
    K.outTy K.nomem kidOuts kidIns n K.kidsLo K.callW K.callA
    hB hcore hpost entry closes K.outName K.outScalar ms hmsD

/-- **`KidFactsT` of a callee with a register whose own calls are tied by the
general closing, at depth `n + 1`**, from `KidFactsT` of its callees at the
depth `n`. -/
theorem GenKidT.factsT (K : GenKidT mref cref c dk nDecl namesK kidOuts kidIns n) :
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

end Tools.ShippingGenKidT
'''

out = HEADER + a + "\n\n" + b + "\n\n" + c + "\n" + TAIL
if "/-" in out.replace("/-!", "").replace("/--", ""):
    sys.exit("a nested comment opener in the generated text")
open(OUT, "w", encoding="utf-8").write(out)
print(f"wrote {OUT}: {out.count(chr(10))} lines")
