import sys
import os
S=os.environ.get("SHAREW_OUT", os.path.dirname(os.path.abspath(__file__)))
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
def nm : Fin (([8] ++ [8]) ++ {gw} : List Nat).length → String := fun i =>
  match i with
{nmArms}
def inp (i : Signal defaultDomain (BitVec 8)) :
    ∀ j : Fin ([8] : List Nat).length, Signal defaultDomain (BitVec (([8] : List Nat).get j)) :=
  fun j => match j with | ⟨0, _⟩ => i
theorem inp_at_0 (i : Signal defaultDomain (BitVec 8)) (tv : Nat) : (inp i 0).val tv = i.val tv := rfl
theorem inp_at_mk_0 (i : Signal defaultDomain (BitVec 8)) (tv : Nat) : (inp i ⟨0, by decide⟩).val tv = i.val tv := rfl

def deep : CdoW [8] [8] {gw} 8 where
  inits := fun i => match i with | ⟨0, _⟩ => 0#8
  wires := fun j => match j with
{chr(10).join(wireArms)}
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
        tpl=open(f"{S}/shareW_trace.tpl").read().replace("{n}",str(n)).replace("{n1}",str(n-1)).replace("GW",gw)
        hm="\n".join(f"      have f{k} := rw{k}_eq i m" for k in range(W))
        ht="\n".join(f"  have f{k} := rw{k}_eq i t" for k in range(W))
        tpl=tpl.replace("      WIREHYPS_M",hm).replace("  WIREHYPS_T",ht)
        L.append(tpl)
    L.append("end Sparkle.Tests.ShareW\n")
    open(f"{S}/shareW_{n}.lean","w").write("\n".join(L))
for n in map(int, sys.argv[2:]): emit(n, sys.argv[1]=="trace")
