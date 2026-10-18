import Tools.ShippingCallWidthsDeclared
import Tools.ShippingR5Check

/-! # `callWidthsStrict` of a parent whose callee is a MACHINE-route child: what it reduces to

The data condition `callWidthsStrict d nDecl kidOuts = true`
(`Tools/ShippingCallWidthsStrict.lean`) is discharged today by ONE `decide`
on the two declarations' reflected data. This file states what the reader
lemmas of this line turn it into, with EVERY remaining obligation a named
hypothesis. It is an accounting, not a gain: see the table.

`callWidthsStrict_of_links` — for a parent `d` whose call entries all read
one machine-route child with shape `sc`:

| hypothesis | what it is | where it can come from |
|---|---|---|
| `LinkP` | `machineShape? … (.defnInfo dP) senvP … = some d.shape` — the reflected parent shape IS a reader result | `MachineDefines` of the parent + the three run facts (`link_of_defines`); `dP` is then the ENTRY constant |
| `LinkC` | the same for the child's shape `sc` | `MachineDefines` of the child + run facts; `dC` the child's ENTRY constant |
| `NIN` | `d.nIn = bs.length + insts.length` for the peel `bs` of `dP.value` | the generator's meta-level knowledge (`ShippingMachineCommand` 437–438); NO kernel statement gives it |
| `R5ok` | `d.r5Ok = true` | `decide` on the reflected parent |
| `ResC` | `machResultKind? dC.type = some res` — the type of the constant the child's shape was read from has the one-Signal result kind `res` | P1 (`resC_of_declared`) when `dC` is the DECLARED constant; for an unfolded entry constant (`inlinedConst (userInliner env) ci`, the normal case of a machine-route child — `entryConst`, 5248–5258) it is a fact about `userInliner` on a type: P5, `opaque` |
| `R1all` | every call entry's kind is `res` | `decide` on the reflected parent (as a general fact: R1, inside the `partial` `machInstance`) |
| `hkid` | `kidOuts k = sc.layout.outs` | the consumer's choice of `kidOuts` (`rfl`) |

One `decide` becomes two `decide`s (`R5ok`, `R1all`), two links derivable
from `MachineDefines` under run facts (`LinkP`, `LinkC`), and two
obligations nothing provides (`NIN`, `ResC` for an unfolded child). The
child's layout widths are derived instead of evaluated; nothing else is
gained. It would become a real reduction with: R1 as a theorem (then
`R1all` goes), `MachRead.LenOk` of the returned reader state (then `R5ok`
AND `NIN` go: `ShapeDecomp.r5_of_lengths` needs neither), and `ResC` for
the unfolded type (P5).

`entryStrict_of_child` isolates the only part where a lemma replaces an
evaluation: the CHILD side (the layout is one output `out` of
`machHWType res`). Its parent-side hypothesis `PB` is decidable on the
reflected parent directly, with no reader fact at all.

`R1At`, `r1k_of_R1At`, `resC_of_declared`, `entryStrict_of_links_declared`:
the form with the callee's DECLARED constant and R1 as the reader's
invariant. Its hypotheses say explicitly that the entry's callee is `c`
(`hcallee`) and that the parent's shape was read with the signature table
of the SAME environment `env` in which `c` is looked up (`LinkP` at
`structEnv env`).

Depends on `ShippingShapeDecomp`, `ShippingCallWidthsDeclared`,
`ShippingR5Check`. BUILT (as a dependency of runs `k1` / `cr1`, exit 0; header
corrected 2026-10-18). MEASURED axioms (run `ax18`): `callWidthsStrict_of_links`,
`entryStrict_of_links_declared`: [propext, Classical.choice, Quot.sound]. Nothing here is connected to an endpoint. -/
namespace Tools.ShippingCallWidthsEntry
open Lean
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingCallWidthsStrict
open Tools.ShippingReaderResultKind Tools.ShippingInstSignature
open Tools.ShippingMachineShapeUnfold Tools.ShippingShapeDecomp
open Tools.ShippingCallWidthsDeclared Tools.ShippingR5Check

/-- The `nDecl` the closing computes (`closeInstsM` 5199, `closeInstsGM`
5218). -/
abbrev closingNDecl (sp : MachineShape) : Nat :=
  sp.binders.length - sp.insts.length - sp.layout.slots.length - sp.layout.lets

/-! ## The reflection link, from `MachineDefines` -/

/-- A returned shape was read from a DEFINITION (`machineShape?` is `none`
on every other constant). -/
theorem machineShape?_defn {sym : Bool} {params : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {allow : Bool} {sp : MachineShape}
    (h : machineShape? sym params ci senv allow = some sp) :
    ∃ dE : DefinitionVal, ci = .defnInfo dE := by
  cases ci with
  | defnInfo dE => exact ⟨dE, rfl⟩
  | _ =>
    first
      | cases h
      | (unfold machineShape? at h; cases h)
      | (simp [machineShape?] at h; done)

/-- **`LinkP` / `LinkC` from `MachineDefines`**: under the three run facts
`MachineDefines` quantifies over, the shape is the reader's result on the
ENTRY constant, which is a definition. Nothing is said about WHICH
definition it is (`ci` itself or `inlinedConst (userInliner envR) ci`). -/
theorem link_of_defines {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {declName : Name}
    {shape : MachineShape}
    (hd : MachineDefines mctx mref cctx cref declName shape)
    {w1 w2 w5 w6 w7 w8 : Void IO.RealWorld} {ci : ConstantInfo} {envR envR' : Environment}
    (h1 : RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2)
    (h5 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6)
    (h7 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w7 envR' w8) :
    ∃ dE : DefinitionVal,
      entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR) = .defnInfo dE ∧
      machineShape? false [] (.defnInfo dE) (structEnv envR') = some shape := by
  have h := (hd w1 ci w2 w5 envR w6 w7 envR' w8 h1 h5 h7).2.2
  obtain ⟨dE, hE⟩ := machineShape?_defn h
  refine ⟨dE, hE, ?_⟩
  rw [hE] at h
  exact h

/-! ## The child side: the only part where a lemma replaces an evaluation -/

/-- **One conjunct from the child's reader result.** The child's layout is
the single output `out` of `machHWType res` (P2 + the decomposition), for
ANY constant `dC` the child's shape was read from whose type has the result
kind `res`. The parent side is the single hypothesis `PB`. -/
theorem entryStrict_of_child {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    {k : Nat} {res : MixedGateBinder} {dC : DefinitionVal}
    {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv} {allowC : Bool}
    {sc : MachineShape}
    (LinkC : machineShape? symC paramsC (.defnInfo dC) senvC allowC = some sc)
    (ResC : machResultKind? dC.type = some res)
    (hkid : kidOuts k = sc.layout.outs)
    (PB : (d.shape.binders[nDecl + k]?).map (fun bn => kindTy bn.2) = some (machHWType res)) :
    entryStrict d nDecl kidOuts k = true := by
  obtain ⟨_, _, _, _, _, _, _, _, DC⟩ := machineShape?_decomp LinkC
  have hout := hkid.trans (DC.single_out ResC)
  exact entryStrict_of_single hout PB

/-! ## Both sides -/

/-- **One conjunct at the closing's `nDecl`, every obligation named.** -/
theorem entryStrict_of_links {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal} {senvP : StructEnv}
    {allowP : Bool}
    (LinkP : machineShape? symP paramsP (.defnInfo dP) senvP allowP = some d.shape)
    (NIN : ∀ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs dP.value) = some (bs, e) →
      d.nIn = bs.length + d.shape.insts.length)
    (R5ok : d.r5Ok = true)
    {res : MixedGateBinder} {dC : DefinitionVal}
    {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv} {allowC : Bool}
    {sc : MachineShape}
    (LinkC : machineShape? symC paramsC (.defnInfo dC) senvC allowC = some sc)
    (ResC : machResultKind? dC.type = some res)
    (hkid : kidOuts k = sc.layout.outs)
    (hk : k < d.shape.insts.length)
    (R1k : (d.shape.insts.map (·.2.2))[k]? = some res) :
    entryStrict d (closingNDecl d.shape) kidOuts k = true := by
  obtain ⟨bs, e, ctor?, outs, names, kindsP, inits, letB, DP⟩ := machineShape?_decomp LinkP
  -- R5 of the parent: the reflected count, at the peel of the constant it was read from
  have R5 : (names.zip kindsP).length = d.shape.layout.slots.length :=
    r5_of_r5Ok DP (NIN bs e DP.peel) R5ok
  have hres : res ≠ .domain := machResultKind?_ne_domain _ res ResC
  -- the parent's binder at `nDecl + k` has the entry's kind (R5), which is `res` (R1k)
  have hkind := (DP.callBinder R5 hk).trans R1k
  exact entryStrict_of_child LinkC ResC hkid (r1_of_kind hkind hres)

theorem getElem?_of_forall_mem {α : Type} {l : List α} {a : α} (h : ∀ x ∈ l, x = a)
    {k : Nat} (hk : k < l.length) : l[k]? = some a := by
  rw [List.getElem?_eq_getElem hk]
  exact congrArg some (h _ (List.getElem_mem hk))

/-- **The whole condition, every obligation named** (all entries read one
child shape `sc`). See the table in the header. -/
theorem callWidthsStrict_of_links {d : MachineData} {kidOuts : Nat → List OutField}
    {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal} {senvP : StructEnv}
    {allowP : Bool}
    (LinkP : machineShape? symP paramsP (.defnInfo dP) senvP allowP = some d.shape)
    (NIN : ∀ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs dP.value) = some (bs, e) →
      d.nIn = bs.length + d.shape.insts.length)
    (R5ok : d.r5Ok = true)
    {res : MixedGateBinder} {dC : DefinitionVal}
    {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv} {allowC : Bool}
    {sc : MachineShape}
    (LinkC : machineShape? symC paramsC (.defnInfo dC) senvC allowC = some sc)
    (ResC : machResultKind? dC.type = some res)
    (hkid : ∀ k, k < d.shape.insts.length → kidOuts k = sc.layout.outs)
    (R1all : ∀ kd ∈ d.shape.insts.map (·.2.2), kd = res) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_entries fun k hk =>
    entryStrict_of_links LinkP NIN R5ok LinkC ResC (hkid k hk) hk
      (getElem?_of_forall_mem R1all (by rw [List.length_map]; exact hk))

/-! ## The declared-constant form, with R1 as the reader's invariant -/

/-- **R1 at entry `k`**, as a statement about a shape and an environment:
if the entry's callee has a one-Signal signature in `env`, the entry's kind
is that signature's result kind. (For a shape returned by the reader with
`structEnv env`: the result of the `partial` `machInstance`, 4068 — not
proved. For a memory child or a structure-result callee the premise
`(structEnv env).inst c = some _` does not hold and the statement is
empty.) -/
def R1At (env : Environment) (sp : MachineShape) (k : Nat) : Prop :=
  ∀ (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder),
    (sp.insts.map (·.1))[k]? = some c → (structEnv env).inst c = some (kinds, res) →
    (sp.insts.map (·.2.2))[k]? = some res

/-- R1 at the entry whose callee is `c`. -/
theorem r1k_of_R1At {env : Environment} {sp : MachineShape} {k : Nat} {c : Name}
    {kinds : List MixedGateBinder} {res : MixedGateBinder}
    (R1 : R1At env sp k)
    (hcallee : (sp.insts.map (·.1))[k]? = some c)
    (hinst : (structEnv env).inst c = some (kinds, res)) :
    (sp.insts.map (·.2.2))[k]? = some res :=
  R1 c kinds res hcallee hinst

/-- **`ResC` for a DECLARED constant** (P1): the signature's result kind is
read off the type of the constant `env` holds for `c`. -/
theorem resC_of_declared {env : Environment} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {dC : DefinitionVal}
    (hinst : (structEnv env).inst c = some (kinds, res))
    (hfind : env.find? c = some (.defnInfo dC)) :
    machResultKind? dC.type = some res := by
  rw [structEnv_inst] at hinst
  obtain ⟨_, ci, hci, _, hr⟩ := instSignature?_some hinst
  rw [hfind] at hci
  cases hci
  exact hr

/-- **One conjunct, declared callee.** Besides the reflection links, `NIN`
and `R5ok`: the entry's callee is `c` (`hcallee`); `c`'s signature and
constant are those of `env` (`hinst`, `hfind`), the SAME environment whose
signature table the parent's reader used (`LinkP` at `structEnv env`); the
child's shape was read from that declared constant (`LinkC` at `dC` — NOT
what `MachineDefines` gives when the entry constant is the unfolding); and
R1 at the entry. -/
theorem entryStrict_of_links_declared {env : Environment} {c : Name}
    {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal} {allowP : Bool}
    (LinkP : machineShape? symP paramsP (.defnInfo dP) (structEnv env) allowP = some d.shape)
    (NIN : ∀ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs dP.value) = some (bs, e) →
      d.nIn = bs.length + d.shape.insts.length)
    (R5ok : d.r5Ok = true)
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {dC : DefinitionVal}
    {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv} {allowC : Bool}
    {sc : MachineShape}
    (hcallee : (d.shape.insts.map (·.1))[k]? = some c)
    (hinst : (structEnv env).inst c = some (kinds, res))
    (hfind : env.find? c = some (.defnInfo dC))
    (LinkC : machineShape? symC paramsC (.defnInfo dC) senvC allowC = some sc)
    (hkid : kidOuts k = sc.layout.outs)
    (hk : k < d.shape.insts.length)
    (R1 : R1At env d.shape k) :
    entryStrict d (closingNDecl d.shape) kidOuts k = true :=
  entryStrict_of_links LinkP NIN R5ok LinkC (resC_of_declared hinst hfind) hkid hk
    (r1k_of_R1At R1 hcallee hinst)

end Tools.ShippingCallWidthsEntry
