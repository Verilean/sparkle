import sys
import os
S=os.environ.get("SHAREW_OUT", os.path.dirname(os.path.abspath(__file__)))
TPLDIR=os.path.dirname(os.path.abspath(__file__))  # templates live next to this script
def emit(n, with_trace):
    W=n+1  # wires w0..wn
    body=["    let r ← Signal.reg (0#8)","    let a := (r : Signal defaultDomain (BitVec 8))","    let w0 := a + i"]
    for k in range(1,n+1): body.append(f"    let w{k} := (w{k-1} + w{k-1}) ^^^ i")
    body.append(f"    r <~ w{n} + w{n-1}"); body.append(f"    return w{n}")
    gw="["+", ".join(["8"]*W)+"]"
    names=['"r"','"i"']+[f'"w{k}"' for k in range(W)]
    nmArms="\n".join(f"    | ⟨{j}, _⟩ => {s}" for j,s in enumerate(names))
    def var(j): return f"(CExpr.var ⟨{j}, by decide⟩)"
    wireArms=[f"    | ⟨0, _⟩ => CExpr.add {var(0)} {var(1)}"]
    for k in range(1,W):
        wireArms.append(f"    | ⟨{k}, _⟩ => CExpr.xor (CExpr.add {var(2+k-1)} {var(2+k-1)}) {var(1)}")
    if os.environ.get("SHAREW_NMLIST")=="1":
        nmdef=("def nmL : List String := ["+", ".join(names)+"]\n"
               f"def nm : Fin (([8] ++ [8]) ++ {gw} : List Nat).length → String := fun i => nmL.getD i.val \"\"")
    else:
        nmdef=(f"def nm : Fin (([8] ++ [8]) ++ {gw} : List Nat).length → String := fun i =>\n  match i with\n{nmArms}")
    if os.environ.get("SHAREW_NMLIST")=="1":
        # width-tagged cone list + decidable width agreement + cast (K-reduces on closed widths)
        sig=[]
        for k in range(W):
            e=f"CExpr.add {var(0)} {var(1)}" if k==0 else f"CExpr.xor (CExpr.add {var(2+k-1)} {var(2+k-1)}) {var(1)}"
            sig.append(f"    ⟨8, {e}⟩")
        wl="[\n"+",\n".join(sig)+" ]"
        wiresdef=("fun j => (wlOk j) ▸ (wl.getD j.val ⟨0, CExpr.const 0 0⟩).2")
        wlpre=(f"def wl : List (Σ w : Nat, CExpr (([8] ++ [8]) ++ {gw} : List Nat) w) := {wl}\n"
               f"theorem wlOk : ∀ j : Fin ({gw} : List Nat).length, (wl.getD j.val ⟨0, CExpr.const 0 0⟩).1 = ({gw} : List Nat).get j := by decide\n")
    else:
        wiresdef="fun j => match j with\n"+chr(10).join(wireArms)
        wlpre=""
    L=[]
    L.append(f'''import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Tools.DeepElab
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core Tools.DeepElab
set_option maxRecDepth 65536
namespace Sparkle.Tests.ShareW
def shareX{n} (i : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
{chr(10).join(body)}

/-! hand-emitted SHARED deep route (prototype of the generator's output) -/
{nmdef}
def inp (i : Signal defaultDomain (BitVec 8)) :
    ∀ j : Fin ([8] : List Nat).length, Signal defaultDomain (BitVec (([8] : List Nat).get j)) :=
  fun j => match j with | ⟨0, _⟩ => i
theorem inp_at_0 (i : Signal defaultDomain (BitVec 8)) (tv : Nat) : (inp i 0).val tv = i.val tv := rfl
theorem inp_at_mk_0 (i : Signal defaultDomain (BitVec 8)) (tv : Nat) : (inp i ⟨0, by decide⟩).val tv = i.val tv := rfl

{wlpre}def deep : CdoW [8] [8] {gw} 8 where
  inits := fun i => match i with | ⟨0, _⟩ => 0#8
  wires := {wiresdef}
  next := fun i => match i with
    | ⟨0, _⟩ => CExpr.add {var(2+n)} {var(2+n-1)}
  out := {var(2+n)}

def ρ (i : Signal defaultDomain (BitVec 8)) (s : Nat) : CEnv ([8] ++ [8]) :=
  CEnv.join (CdoW.stateAt deep (fun t j => (inp i j).val t) s) (fun j => (inp i j).val s)
def rd0 (i : Signal defaultDomain (BitVec 8)) (s : Nat) : BitVec 8 :=
  CdoW.stateAt deep (fun t j => (inp i j).val t) s ⟨0, by decide⟩
''')
    for k in range(W):
        L.append(f"def rw{k} (i : Signal defaultDomain (BitVec 8)) (s : Nat) : BitVec 8 := CdoW.wenv deep (ρ i s) ⟨{k}, by decide⟩")
    L.append("theorem rw0_eq (i : Signal defaultDomain (BitVec 8)) (s : Nat) : rw0 i s = rd0 i s + i.val s := rfl")
    for k in range(1,W):
        L.append(f"theorem rw{k}_eq (i : Signal defaultDomain (BitVec 8)) (s : Nat) : rw{k} i s = (rw{k-1} i s + rw{k-1} i s) ^^^ i.val s := rfl")
    L.append("theorem rd0_zero (i : Signal defaultDomain (BitVec 8)) : rd0 i 0 = 0#8 := rfl")
    L.append(f"theorem rd0_succ (i : Signal defaultDomain (BitVec 8)) (s : Nat) : rd0 i (s+1) = rw{n} i s + rw{n-1} i s := rfl")
    L.append(f'''theorem outS (i : Signal defaultDomain (BitVec 8)) (s : Nat) :
    (CdoW.outSig deep (inp i)).val s = rw{n} i s := by
  show CExpr.denote _ _ = _
  rw [CdoW.stateSig_eq]
  rfl''')
    if with_trace:
        hb=os.environ.get("SHAREW_HB","1600000")
        tplname=os.environ.get("SHAREW_TPL","shareW_trace.tpl")
        tpl=open(f"{TPLDIR}/{tplname}").read().replace("{n}",str(n)).replace("{n1}",str(n-1)).replace("GW",gw).replace("HEARTBEATS",hb)
        hm="\n".join(f"      have f{k} := rw{k}_eq i m" for k in range(W))
        ht="\n".join(f"  have f{k} := rw{k}_eq i t" for k in range(W))
        # DSL-side per-wire `.val` equations on the extract_lets local defs
        # (names preserved: a, w0..wn); `a` is the register read, tied to
        # the reader by hpre
        dsl=["      have ea : a.val m = rd0 i m := by simp [a, mkRegList, Signal.map, hpre m (Nat.lt_succ_self m)]",
             "      have e0 : w0.val m = a.val m + i.val m := by simp only [w0, sigval_add]"]
        for k in range(1,W):
            dsl.append(f"      have e{k} : w{k}.val m = (w{k-1}.val m + w{k-1}.val m) ^^^ i.val m := by simp only [w{k}, sigval_add, sigval_xor]")
        names=" ".join(["a"]+[f"w{k}" for k in range(W)]+["p"])
        namesO=" ".join(["ao"]+[f"wo{k}" for k in range(W)])
        tpl=tpl.replace("EXTRACTNAMES_OUT",namesO).replace("EXTRACTNAMES",names)
        if os.environ.get("SHAREW_NMLIST")=="1":
            tpl=tpl.replace("rw [← CdoW.elab_general deep nm (by decide) (inp i) t]","rw [← CdoW.elab_general deep nm (by native_decide) (inp i) t]")
        dslT=["  have eao : ao.val t = rd0 i t := by simp [ao, Signal.map, hLt]",
              "  have eo0 : wo0.val t = ao.val t + i.val t := by simp only [wo0, sigval_add]"]
        for k in range(1,W):
            dslT.append(f"  have eo{k} : wo{k}.val t = (wo{k-1}.val t + wo{k-1}.val t) ^^^ i.val t := by simp only [wo{k}, sigval_add, sigval_xor]")
        tpl=tpl.replace("  DSLWIREEQS_T","\n".join(dslT))
        tpl=tpl.replace("      DSLWIREEQS_M","\n".join(dsl))
        tpl=tpl.replace("      WIREHYPS_M",hm).replace("  WIREHYPS_T",ht)
        L.append(tpl)
    L.append("end Sparkle.Tests.ShareW\n")
    open(f"{S}/shareW_{n}.lean","w").write("\n".join(L))
for n in map(int, sys.argv[2:]): emit(n, sys.argv[1]=="trace")
