import Tools.ShippingMemOnlyNames

/-! # Module names of a parent with memory AND declaration children (round par/b-30)

WRITTEN, NOT BUILT.

`#machine_no_ports_memseq` (`Tools/ShippingNoPortsMemSeqCommand.lean`) states
its name lemmas over the NAME FIELD of the built memory module,
`(memModule cb aw dw).1.name`, and over `ofDecl` of the leaf callees and of
the parent. With `Tools.ShippingMemOnlyNames.memModule_name` (BUILT at
812061e5: that field is `ofMem cb aw dw`) each of them is an instance of the
encoding's general lemmas:

| the generator's lemma | statement | here | condition left |
|---|---|---|---|
| `f.noPortsMemSeq_notinP{j}` | `ofDecl f ∉ [(memModule …).1.name]` | `decl_not_mem_memName` | none |
| `f.noPortsMemSeq_leafNotin{i}_{j}` | `ofDecl c ∉ [(memModule …).1.name]` | `decl_not_mem_memName` | none |
| `f.noPortsMemSeq_memNe{i}_{j}` | two memory modules' names differ | `memName_ne` | the parameters differ (`decide` on `Bool` / `Nat`) |
| `f.noPortsMemSeq_leafNeParent{i}`, `…_leafNe{i}_{j}` | `ofDecl c ≠ ofDecl c'` | `Tools.ShippingModuleName.ofDecl_ne` | `c ≠ c'` (`decide` on `Lean.Name`) |

No string is evaluated and no candidate rendering is enumerated. -/
namespace Tools.ShippingMemSeqNames
open Sparkle.Compiler.MachMemory (memModule)
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Tools.ShippingMemOnlyNames (memModule_name)

/-- No declaration's module has the name of a built memory module. -/
theorem decl_ne_memName (c : Lean.Name) (cb : Bool) (aw dw : Nat) :
    ofDecl c ≠ (memModule cb aw dw).1.name :=
  fun e => Tools.ShippingModuleName.ofDecl_ne_ofMem c cb aw dw
    (e.trans (memModule_name cb aw dw))

/-- … in the form the generators state it (a memory module's design is the
module itself). -/
theorem decl_not_mem_memName (c : Lean.Name) (cb : Bool) (aw dw : Nat) :
    ofDecl c ∉ [(memModule cb aw dw).1.name] :=
  fun h => decl_ne_memName c cb aw dw (List.mem_singleton.mp h)

/-- Built memory modules of different parameters have different names. -/
theorem memName_ne {cb cb' : Bool} {aw dw aw' dw' : Nat}
    (h : ¬ (cb = cb' ∧ aw = aw' ∧ dw = dw')) :
    (memModule cb aw dw).1.name ≠ (memModule cb' aw' dw').1.name :=
  fun e => h (Tools.ShippingModuleName.ofMem_injective
    ((memModule_name cb aw dw).symm.trans (e.trans (memModule_name cb' aw' dw'))))

end Tools.ShippingMemSeqNames
