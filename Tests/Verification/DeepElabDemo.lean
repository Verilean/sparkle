/-
  `Cdo.elab_general` demo — the general Signal↔IR theorem, instanced.

  The two-register circuit below (a' = a + d; b' = a; out = b — the
  same cross-register shape `#verify_elab` needed a generated proof
  for) is written as a DEEP value, and its Signal↔IR theorem is one
  `exact`: the general theorem applies, with name injectivity the only
  obligation, discharged by `decide`.

  Run: `lake env lean Tests/Verification/DeepElabDemo.lean`
-/

import Tools.DeepElab
open Sparkle.Core.Domain

/- twoReg as a DEEP value: registers [4,4], input [4];
   a' = a + d ; b' = a ; out = b.  Indices in Γr ++ Γi = [4,4,4]:
   a = 0, b = 1, d = 2. -/
def twoRegDeep : Cdo [4,4] [4] 4 where
  inits := fun i =>
    match i with
    | ⟨0, _⟩ => 0#4
    | ⟨1, _⟩ => 0#4
  next := fun i =>
    match i with
    | ⟨0, _⟩ => .add (.var ⟨0, by decide⟩) (.var ⟨2, by decide⟩)
    | ⟨1, _⟩ => .var ⟨0, by decide⟩
  out := .var ⟨1, by decide⟩

def nm : Fin (([4,4] ++ [4] : List Nat).length) → String
  | ⟨0,_⟩ => "a" | ⟨1,_⟩ => "b" | ⟨2,_⟩ => "d"

/- THE INSTANCE: one `exact`, injectivity by decide. -/
theorem twoRegDeep_general (inpS) (t : Nat) :
    ((twoRegDeep.outSig (dom := defaultDomain) inpS).val t).toNat
      = (Sparkle.IR.Semantics.evalExpr
          (weOfC nm (fun j => ([4,4] ++ [4] : List Nat).get j))
          (envOfC nm (natJoin
            (twoRegDeep.irState nm (fun t j => (inpS j).val t) t)
            (fun j => ((inpS j).val t).toNat)))
          (twoRegDeep.out.compile nm)).getD 0 :=
  twoRegDeep.elab_general nm (by decide) inpS t

#print axioms twoRegDeep_general
