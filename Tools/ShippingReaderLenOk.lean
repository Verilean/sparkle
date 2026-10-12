import Sparkle.Compiler.Elab

/-! # The length invariant of the reader state — the PURE part

`MachRead` (`Sparkle/Compiler/Elab.lean` 3559) has three `Array`s that
describe the slots: `kinds : Array MixedGateBinder`, `inits : Array Nat`,
`names : Array Name`. `MachRead.LenOk st` says they have one length.

It is what R5 of `docs/parallel/B-readerinv.md` needs
(`ShapeDecomp.r5_of_lengths`): the wrapper `machineShape?` zips `st.names`
with `st.kinds` for the slot binders (5168) and `st.kinds` with `st.inits`
for the layout's slots (5174).

This file proves the facts that need NO equation of a `partial` function:

* **(i)** the initial state `{}` (5092) satisfies it — `lenOk_init`;
* **(iii)** every expression in the reader that BUILDS a `MachRead` from
  one preserves it. There are 24 such expressions (23 record updates and
  the one literal `{}`); three of them write the three arrays, and each of
  the three writes ALL three:

  | lines | function | what it does to `kinds` / `inits` / `names` | lemma |
  |---|---|---|---|
  | 3705–3710 | `machReserve` (a `def`) | `++` a list to each | `lenOk_append` (+ the two list lengths, `Tools/ShippingReaderLenOkReserve.lean`) |
  | 3924–3927 | `machConv`, bare register | `push` one to each | `lenOk_bareRegister` |
  | 4216–4223 | `machLoopRoot` | `++` a list to each | `lenOk_loopRoot` |

  The other 20 updates do not mention the three fields:

  | lines | fields written | lemma |
  |---|---|---|
  | 3929, 4183, 4208, 4209, 5125 | `ws` | `lenOk_ws` |
  | 3953, 4051 | `instStruct` | `lenOk_instStruct` |
  | 4003, 4064, 4100, 4161, 4176, 5116 | `lets` | `lenOk_lets` |
  | 4033 | `inInner` | `lenOk_inInner` |
  | 4036 | `ws`, `inInner`, `nested` | `lenOk_nestedClose` |
  | 4061, 4096 | `dom` | `lenOk_dom` |
  | 4068 | `insts`, `instFields` | `lenOk_instPush` |
  | 4110–4113 | `insts`, `instFields`, `instStruct` | `lenOk_instS` |
  | 4228 | `loopWs`, `loopDepth` | `lenOk_loopClose` |

  NO site writes one or two of the three arrays: nowhere is the invariant
  false or temporarily broken. (Found by `grep` for `with` in 3871–4230 and
  5056–5186 and for `MachRead` in the whole file; no other file under
  `Sparkle/` mentions `MachRead`.)

**What this file does NOT prove** — the boundary: that the state
`machineShape?` ends with satisfies `LenOk`. Every path of the wrapper goes
through at least one `partial def` (the last step is always `machChain`,
5121, or `machConv`, 5127), and a `partial def` is, in the kernel, an
`opaque` constant whose hidden value is an arbitrary inhabitant
(`Lean/Elab/PreDefinition/Main.lean` 20–36: `kind := DefKind.opaque`, value
`mkInhabitantFor`): it has NO equation, not even an unfolding to its source
text. The obligation is `ReadersKeepLenOk` below, a `Prop` that nothing in
this line proves and nothing uses. See `docs/parallel/B-readerinv.md` §8.

Independent of the queued files (`ShippingMachineShapeUnfold` / `Tail`):
this file imports the compiler only. UNVERIFIED: written, not built. -/
namespace Tools.ShippingReaderLenOk
open Lean
open Sparkle.Compiler.Elab

/-- **The length invariant**: the three slot arrays of the reader state
have one length (`names.size = kinds.size ∧ inits.size = kinds.size`, as a
structure so that the two halves have names). -/
structure _root_.Sparkle.Compiler.Elab.MachRead.LenOk (st : MachRead) : Prop where
  names : st.names.size = st.kinds.size
  inits : st.inits.size = st.kinds.size

theorem lenOk_iff (st : MachRead) :
    st.LenOk ↔ st.names.size = st.kinds.size ∧ st.inits.size = st.kinds.size :=
  ⟨fun h => ⟨h.names, h.inits⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ## (i) The initial state -/

/-- The state `machineShape?` starts from (`let st : MachRead := {}`, 5092). -/
theorem lenOk_init : MachRead.LenOk ({} : MachRead) :=
  ⟨rfl, rfl⟩

/-! ## (iii) The three updates that write the slot arrays -/

/-- A state whose three arrays are the old ones (any other field changed). -/
theorem lenOk_frame {st st' : MachRead} (h : st.LenOk)
    (hk : st'.kinds = st.kinds) (hi : st'.inits = st.inits) (hn : st'.names = st.names) :
    st'.LenOk :=
  ⟨(by rw [hn, hk]; exact h.names), (by rw [hi, hk]; exact h.inits)⟩

/-- A state whose three arrays are the old ones with lists of ONE length
appended (the form of `machReserve` and of `machLoopRoot`). -/
theorem lenOk_append {st st' : MachRead} (h : st.LenOk)
    {ks : List MixedGateBinder} {is : List Nat} {ns : List Name}
    (hil : is.length = ks.length) (hnl : ns.length = ks.length)
    (hk : st'.kinds = st.kinds ++ ks.toArray) (hi : st'.inits = st.inits ++ is.toArray)
    (hn : st'.names = st.names ++ ns.toArray) :
    st'.LenOk := by
  have e1 : st'.kinds.size = st.kinds.size + ks.length := by
    rw [hk]
    rw [Array.size_append]
    rfl
  have e2 : st'.inits.size = st.inits.size + is.length := by
    rw [hi]
    rw [Array.size_append]
    rfl
  have e3 : st'.names.size = st.names.size + ns.length := by
    rw [hn]
    rw [Array.size_append]
    rfl
  have a := h.names
  have b := h.inits
  exact ⟨by omega, by omega⟩

/-- **3924–3927**, `machConv` on a bare `Signal.register`: one kind, one
reset value, one name pushed (and `dom`, `bareRegs` written). -/
theorem lenOk_bareRegister {st : MachRead} (h : st.LenOk) (kind : MixedGateBinder)
    (initN : Nat) (nm : Name) (dom' e : Lean.Expr) (base : Nat) :
    MachRead.LenOk { st with
      kinds := st.kinds.push kind, inits := st.inits.push initN
      names := st.names.push nm, dom := some dom'
      bareRegs := st.bareRegs.push (e, base) } := by
  have a := h.names
  have b := h.inits
  constructor
  · show (st.names.push nm).size = (st.kinds.push kind).size
    rw [Array.size_push, Array.size_push, a]
  · show (st.inits.push initN).size = (st.kinds.push kind).size
    rw [Array.size_push, Array.size_push, b]

/-- **4216–4223**, `machLoopRoot`: `kinds`, `inits` and the generated names
`loop{j}_r{i}` (one per kind) appended. The premise `hil` is a fact of the
two `mapM`s that produce `kinds` and `inits` (4199–4200):
`Tools/ShippingReaderLenOkReserve.lean`, `loopRoot_inits_length`. -/
theorem lenOk_loopRoot {st : MachRead} (h : st.LenOk) {kinds : List MixedGateBinder}
    {inits : List Nat} (hil : inits.length = kinds.length) (dom' : Lean.Expr) (depth : Nat) :
    MachRead.LenOk { st with
      kinds := st.kinds ++ kinds.toArray
      inits := st.inits ++ inits.toArray
      names := st.names ++ ((List.range kinds.length).map fun i =>
        Name.mkSimple s!"loop{st.loops.size}_r{i}").toArray
      dom := some dom'
      loops := st.loops.push (st.kinds.size, kinds.length)
      nestedLoops := if depth ≥ 1 then st.nestedLoops + 1 else st.nestedLoops
      loopDepth := depth + 1 } :=
  lenOk_append h hil
    (by first
      | rw [List.length_map, List.length_range]
      | simp)
    rfl rfl rfl

/-- The state `machReserve` (3705–3710) returns, as a function of the lists
it read (`machReserve_some`, `Tools/ShippingReaderLenOkReserve.lean`, says
the returned state is this one). -/
def reserved (st : MachRead) (dom' body : Lean.Expr) (kinds : List MixedGateBinder)
    (inits : List Nat) : MachRead :=
  { st with
    kinds := st.kinds ++ kinds.toArray
    inits := st.inits ++ inits.toArray
    names := st.names ++ (machSlotNames st.runs.size body kinds st.kinds.size).toArray
    dom := some dom'
    runs := st.runs.push (st.kinds.size, kinds.length) }

/-- **3705–3710**, `machReserve`'s update, given the lengths of the two
lists it appends. -/
theorem lenOk_reserved {st : MachRead} (h : st.LenOk) (dom' body : Lean.Expr)
    {kinds : List MixedGateBinder} {inits : List Nat}
    (hil : inits.length = kinds.length)
    (hnl : (machSlotNames st.runs.size body kinds st.kinds.size).length = kinds.length) :
    (reserved st dom' body kinds inits).LenOk :=
  lenOk_append h hil hnl rfl rfl rfl

/-! ## (iii) The updates that do not write the slot arrays -/

/-- 3929, 4183, 4208, 4209, 5125. -/
theorem lenOk_ws {st : MachRead} (h : st.LenOk) (ws : Array (Nat × Lean.Expr)) :
    MachRead.LenOk { st with ws := ws } :=
  ⟨h.names, h.inits⟩

/-- 3953, 4051. -/
theorem lenOk_instStruct {st : MachRead} (h : st.LenOk) (b : Bool) :
    MachRead.LenOk { st with instStruct := b } :=
  ⟨h.names, h.inits⟩

/-- 4003, 4064, 4100, 4161, 4176, 5116. -/
theorem lenOk_lets {st : MachRead} (h : st.LenOk) (lets : MachLets) :
    MachRead.LenOk { st with lets := lets } :=
  ⟨h.names, h.inits⟩

/-- 4033. -/
theorem lenOk_inInner {st : MachRead} (h : st.LenOk) (b : Bool) :
    MachRead.LenOk { st with inInner := b } :=
  ⟨h.names, h.inits⟩

/-- 4036. -/
theorem lenOk_nestedClose {st : MachRead} (h : st.LenOk) (ws : Array (Nat × Lean.Expr))
    (outer : Bool)
    (nested : Array (Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) ×
      Lean.Expr)) :
    MachRead.LenOk { st with ws := ws, inInner := outer, nested := nested } :=
  ⟨h.names, h.inits⟩

/-- 4061, 4096. -/
theorem lenOk_dom {st : MachRead} (h : st.LenOk) (dom : Option Lean.Expr) :
    MachRead.LenOk { st with dom := dom } :=
  ⟨h.names, h.inits⟩

/-- 4068. -/
theorem lenOk_instPush {st : MachRead} (h : st.LenOk)
    (insts : Array (Name × List Nat × MixedGateBinder)) (instFields : Array String) :
    MachRead.LenOk { st with insts := insts, instFields := instFields } :=
  ⟨h.names, h.inits⟩

/-- 4110–4113. -/
theorem lenOk_instS {st : MachRead} (h : st.LenOk)
    (insts : Array (Name × List Nat × MixedGateBinder)) (instFields : Array String) (b : Bool) :
    MachRead.LenOk { st with insts := insts, instFields := instFields, instStruct := b } :=
  ⟨h.names, h.inits⟩

/-- 4228. -/
theorem lenOk_loopClose {st : MachRead} (h : st.LenOk)
    (loopWs : Array (Nat × Nat × List (Nat × Lean.Expr))) (depth : Nat) :
    MachRead.LenOk { st with loopWs := loopWs, loopDepth := depth } :=
  ⟨h.names, h.inits⟩

/-! ## The boundary, as a statement

The readers the wrapper calls with a state and whose returned state it
keeps: `machConv` (5098, 5111, 5127), `machLoopRoot` (5106), `machChain`
(5121). (`machNested`, `machInstance`, `machInstanceS`, `machLoopBody` are
reached only from inside these.) All seven are `partial def`s of one
`mutual` block: seven `opaque` constants. An induction over the reader's
steps would prove the proposition below from the lemmas above and the two
length lemmas of `machReserve`; in the kernel there is no step to induct
on. It is neither provable nor refutable: the hidden value of each constant
is some inhabitant of its type, and the logic does not know which.

This is a DEFINITION, not an axiom and not a hypothesis of any theorem of
this line. -/
def ReadersKeepLenOk : Prop :=
  (∀ (senv : StructEnv) (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead)
      (r : Lean.Expr) (st' : MachRead),
      machConv senv env d e st = some (r, st') → st.LenOk → st'.LenOk) ∧
  (∀ (senv : StructEnv) (env : List MachVal) (e : Lean.Expr) (st : MachRead)
      (mv : MachVal) (st' : MachRead),
      machLoopRoot senv env e st = some (mv, st') → st.LenOk → st'.LenOk) ∧
  (∀ (senv : StructEnv) (env : List MachVal) (e : Lean.Expr) (st : MachRead)
      (ws : List (Nat × Lean.Expr)) (v : Lean.Expr) (st' : MachRead),
      machChain senv env e st = some (ws, v, st') → st.LenOk → st'.LenOk)

end Tools.ShippingReaderLenOk
