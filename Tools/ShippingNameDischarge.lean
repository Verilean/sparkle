import Tools.ShippingModuleName

/-! # Name premises from the distinctness of declaration names (round par/b-29)

WRITTEN, NOT BUILT.

Since b7dc0ec4 a module's name is `Sparkle.IR.ModuleName.ofDecl declName`
(a declaration) or `ofMem combo aw dw` (a machine-route memory), and the
encoding is injective (`Tools.ShippingModuleName.ofDecl_injective`,
`ofMem_injective`, `ofDecl_ne_ofMem`). The closing theorems still ask their
name hypotheses about the STRINGS; the generators discharge them through
`Tools.ShippingNameSep` — a Boolean check on the candidate renderings of
`Name.toString`, which is no longer the name function — or leave them as
binders where that check fails.

This file states each hypothesis shape that follows from the distinctness
of the DECLARATION NAMES, with a hypothesis on `Lean.Name`s only (decidable
by `decide` on `Name`: `Name.beq` is structural, compares the last component
first, and enumerates nothing), or with no hypothesis at all:

| shape (in the closing theorems) | here | hypothesis left |
|---|---|---|
| `hsep` / `hnames`: `ofDecl c = ofDecl c' → c = c'` over the callees | `names_inj` | none |
| `hparent`: `ofDecl c.1 ≠ ofDecl parent` over the call entries | `parent_ne` | `c.1 ≠ parent` |
| `hparentD` / `hself`: `ofDecl c ∉ L.map ofDecl` | `not_mem_map` | `c ∉ L` |
| `hselfD`: `ofDecl insts[k].1 ∉ (declsK k).map ofDecl` | `selfD_of` | `insts[k].1 ∉ declsK k` |
| `hparentD` (indexed) | `parentD_of` | `parent ∉ declsK k` |
| `hdisjD`: a callee's name not among another's descendants, and the two descendant lists share no name | `disjD_of` | the same two statements about `Name`s |
| `(L.map ofDecl).Nodup` | `nodup_map` | `L.Nodup` |
| a declaration against a memory module | `decl_ne_mem`, `mem_ne_decl`, `not_mem_mems`, `mem_not_mem_decls`, `not_mem_append` | none |
| two memory modules | `mems_inj`, `mems_ne` | the parameters differ |

What does NOT follow, and is not attempted:

* `hdisjD` for two callees that SHARE a descendant declaration (`mixDeep`:
  `midH` is a callee and a descendant of the callee `mid2`). `disjD_of`
  moves the question from strings to `Name`s; its hypothesis is as FALSE
  there as the string form was. That is the cache-coherence question (one
  declaration, one module, whatever the path), not a naming question.
* `hfresh` (`o.name ≠ s!"inst{k}_{ofDecl c}"`): an OUTPUT PORT of the parent
  against an INSTANCE name. Two different name spaces (ports and instances
  of one module); nothing about declarations decides it. It stays the
  first-character test (`instName_ne_of_head`) or a binder.
* A declaration against an ARBITRARY string (`Enc.not_mem_of`,
  `Enc.fresh_of`): only by evaluating `ofDecl`.
* External / primitive module names (user strings).

The lemmas are pure: this file imports only the encoding's lemmas. -/
namespace Tools.ShippingNameDischarge
open Lean (Name)
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Tools.ShippingModuleName (ofDecl_injective ofDecl_ne ofMem_injective ofDecl_ne_ofMem)

/-! ## Declarations against declarations -/

/-- **`hsep` / `hnames`**: two declarations with one module name are one
declaration. No hypothesis (the list is only there to match the shape). -/
theorem names_inj (L : List Name) :
    ∀ c ∈ L, ∀ c' ∈ L, ofDecl c = ofDecl c' → c = c' :=
  fun _ _ _ _ heq => ofDecl_injective heq

/-- **`hparent`**: no call entry's module has the parent's name, when no call
entry is a call of the parent declaration. -/
theorem parent_ne {α : Type} (insts : List (Name × α)) (parent : Name)
    (h : ∀ c ∈ insts, c.1 ≠ parent) :
    ∀ c ∈ insts, ofDecl c.1 ≠ ofDecl parent :=
  fun c hc => ofDecl_ne (h c hc)

/-- **`hparentD` / `hself`**: a declaration that is not in a list does not
have the module name of a declaration of the list. -/
theorem not_mem_map {c : Name} {L : List Name} (h : c ∉ L) :
    ofDecl c ∉ L.map (fun n => ofDecl n) := by
  intro hm
  obtain ⟨c', hc', heq⟩ := List.mem_map.mp hm
  have h2 : ofDecl c' = ofDecl c := heq
  have e : c' = c := ofDecl_injective h2
  exact h (e ▸ hc')

/-- Two lists of declarations without a common declaration have no common
module name. -/
theorem disjoint_map {L L' : List Name} (h : ∀ a ∈ L, a ∉ L') :
    ∀ x ∈ L.map (fun n => ofDecl n), x ∉ L'.map (fun n => ofDecl n) := by
  intro x hx hx'
  obtain ⟨a, ha, e1⟩ := List.mem_map.mp hx
  obtain ⟨b, hb, e2⟩ := List.mem_map.mp hx'
  have h1 : ofDecl a = x := e1
  have h2 : ofDecl b = x := e2
  have e : b = a := ofDecl_injective (h2.trans h1.symm)
  exact h a ha (e ▸ hb)

/-- The module names of a duplicate-free list of declarations are
duplicate-free. -/
theorem nodup_map : ∀ (L : List Name), L.Nodup → (L.map (fun n => ofDecl n)).Nodup
  | [], _ => List.nodup_nil
  | a :: l, hnd => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, nodup_map l hl⟩
    exact not_mem_map ha

/-! ## The indexed shapes of the deep closings

`machineClosesAt_of_kidsD` asks its descendant hypotheses per call entry
`k`, over a table `namesK : Nat → List String`; the generators instantiate
`namesK k := (declsK k).map ofDecl`. -/

/-- **`hparentD`**: the parent is no descendant of a call entry. -/
theorem parentD_of (n : Nat) (parent : Name) (declsK : Nat → List Name)
    (h : ∀ (k : Nat), k < n → parent ∉ declsK k) :
    ∀ (k : Nat), k < n → ofDecl parent ∉ (declsK k).map (fun n => ofDecl n) :=
  fun k hk => not_mem_map (h k hk)

/-- **`hselfD`**: a callee is no descendant of itself. -/
theorem selfD_of {α : Type} (insts : List (Name × α)) (declsK : Nat → List Name)
    (h : ∀ (k : Nat) (hk : k < insts.length), (insts[k]).1 ∉ declsK k) :
    ∀ (k : Nat) (hk : k < insts.length),
      ofDecl (insts[k]).1 ∉ (declsK k).map (fun n => ofDecl n) :=
  fun k hk => not_mem_map (h k hk)

/-- **`hdisjD`**: two different callees — the first is no descendant of the
second, and their descendants are disjoint. The hypothesis is the SAME
statement about declarations: it is false where two callees share a
descendant (`mixDeep`), and this lemma does not change that. -/
theorem disjD_of {α : Type} (insts : List (Name × α)) (declsK : Nat → List Name)
    (h : ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length),
      (insts[k]).1 ≠ (insts[k']).1 →
      (insts[k]).1 ∉ declsK k' ∧ ∀ a ∈ declsK k, a ∉ declsK k') :
    ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length),
      (insts[k]).1 ≠ (insts[k']).1 →
      ofDecl (insts[k]).1 ∉ (declsK k').map (fun n => ofDecl n) ∧
        ∀ x ∈ (declsK k).map (fun n => ofDecl n), x ∉ (declsK k').map (fun n => ofDecl n) :=
  fun k hk k' hk' hne =>
    ⟨not_mem_map (h k hk k' hk' hne).1, disjoint_map (h k hk k' hk' hne).2⟩

/-! ## Declarations against memory modules -/

/-- No declaration has the name of a memory module. -/
theorem decl_ne_mem (c : Name) (cb : Bool) (aw dw : Nat) : ofDecl c ≠ ofMem cb aw dw :=
  ofDecl_ne_ofMem c cb aw dw

theorem mem_ne_decl (cb : Bool) (aw dw : Nat) (c : Name) : ofMem cb aw dw ≠ ofDecl c :=
  fun e => ofDecl_ne_ofMem c cb aw dw e.symm

/-- A declaration's module name is the name of no memory module of a list
of parameters. -/
theorem not_mem_mems (c : Name) (ms : List (Bool × Nat × Nat)) :
    ofDecl c ∉ ms.map (fun p => ofMem p.1 p.2.1 p.2.2) := by
  intro hm
  obtain ⟨p, _, e⟩ := List.mem_map.mp hm
  have h2 : ofMem p.1 p.2.1 p.2.2 = ofDecl c := e
  exact ofDecl_ne_ofMem c p.1 p.2.1 p.2.2 h2.symm

/-- A memory module's name is the module name of no declaration. -/
theorem mem_not_mem_decls (cb : Bool) (aw dw : Nat) (L : List Name) :
    ofMem cb aw dw ∉ L.map (fun n => ofDecl n) := by
  intro hm
  obtain ⟨c, _, e⟩ := List.mem_map.mp hm
  have h2 : ofDecl c = ofMem cb aw dw := e
  exact ofDecl_ne_ofMem c cb aw dw h2

/-- A declaration against a list of declarations' names followed by memory
modules' names (the design of a child with memories below it). -/
theorem not_mem_append {c : Name} {L : List Name} (h : c ∉ L) (ms : List (Bool × Nat × Nat)) :
    ofDecl c ∉ L.map (fun n => ofDecl n) ++ ms.map (fun p => ofMem p.1 p.2.1 p.2.2) := by
  intro hm
  rcases List.mem_append.mp hm with h1 | h1
  · exact not_mem_map h h1
  · exact not_mem_mems c ms h1

/-! ## Memory modules against memory modules -/

/-- Two memory modules with one name have the same parameters. -/
theorem mems_inj {cb cb' : Bool} {aw dw aw' dw' : Nat}
    (h : ofMem cb aw dw = ofMem cb' aw' dw') : cb = cb' ∧ aw = aw' ∧ dw = dw' :=
  ofMem_injective h

/-- Memory modules of different parameters have different names. -/
theorem mems_ne {cb cb' : Bool} {aw dw aw' dw' : Nat}
    (h : ¬ (cb = cb' ∧ aw = aw' ∧ dw = dw')) : ofMem cb aw dw ≠ ofMem cb' aw' dw' :=
  fun e => h (ofMem_injective e)

end Tools.ShippingNameDischarge
