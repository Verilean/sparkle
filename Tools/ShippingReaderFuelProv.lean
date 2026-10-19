import Tools.ShippingReaderFuelR1

/-! # Call-entry PROVENANCE for the fuel CANDIDATE reader

STATUS 2026-10-19 (worker O, branch `par/o-cand`): BUILT (integration run ig4, exit 0) against
the patched compiler (explicit call-entry origin: `MachRead.instOrigins`,
`machInstance … (org : InstOrigin)`). Earlier text BUILT as `p1` (poc
6f216c4e). No `sorry`, no axiom, no `native_decide`. Nothing here is imported
by the compiler.

## 2026-10-19: provenance is the STORED tag

The reader now records an origin tag next to every call entry
(`InstOrigin := ord | field i | mem combo aw dw`). `InstProv` is restated over
the THREE arrays `insts` / `instFields` / `instOrigins` (one size) and says, per
index `k`, that the facts of the arm the STORED tag names hold (`OriginT`):

* tag `.ord` → `OrdOrigin senv c r ∧ nm = "out"`;
* tag `.field i` → `StructOriginI senv c r nm i ∧ instStruct = true` (field
  index `i` exactly: entry `k0 + i` of a structure call is its field `i`);
* tag `.mem combo aw dw` → `MemOriginI c r combo aw dw ∧ nm = "out"`
  (`c = memChildName combo aw dw`, `r = .bits dw`, `aw ≠ 0`, `dw ≠ 0`).

The call-site premise is now per tag (`InstPre`, inside `CallPreP`): the
ordinary arm calls `machInstance` with `.ord` and a signature, the memory arm
with `.mem combo aw dw` and that placeholder name, no arm with `.field _`.
The pre-tag statement (`Origin`, the three-way disjunction) is a corollary
(`origin_of_originT`, `InstProv.origin`: every entry HAS a tag). Section text
below that speaks of `Origin` describes the pre-tag form, kept as corollary.

SCOPE. A property of the NEW fuel functions (`readF`, …) only, by induction on
the fuel; the proof skeleton is copied arm by arm from
`Tools/ShippingReaderFuelR1.lean` (itself from the R5 file). It says nothing
about the old `partial` readers (O1/O2 outside).

## Why (reviewer finding)

`ChildLinkFD/FS` (`Tools/ShippingCallWidthsEntryFR1.lean`) require
`senv.inst c = some _` for EVERY entry. A memory placeholder has none, a
structure-field entry has `instS` but (for `structEnv env`) no `inst`. So R1
(`InstR1`) is a statement about ONE kind of entry. Here every entry is
classified by the arm that MADE it.

## The invariant

`Origin senv e nm b` for an entry `e = (c, js, r)` whose child port name (the
parallel `instFields` entry) is `nm`, in a state whose structure flag is `b`:

* `OrdOrigin senv c r ∧ nm = "out"` — an ordinary one-Signal call: `instStep`
  called from the `machInstCall?` arm; `senv.inst c = some (kinds, r)`;
* `StructOrigin senv c r nm ∧ b = true` — field `i` of a structure call:
  `instSStep` (called from the `machInstCallS?` arm,
  `senv.instS c = some (kinds, ty)`), `instRes ty args = some resTy`,
  `machOuts? senv resTy = some (some ctor, fields)` (exactly what `instSStep`
  computes), no field of kind `.domain` (its guard), and
  `fields[i]? = some (nm, r)` — field index, name and kind retained; the flag
  `instStruct` is set by the same update;
* `MemOrigin c r ∧ nm = "out"` — a synthetic memory call: `instStep` called
  from the memory arm, `c = memChildName combo aw dw`, `r = .bits dw`,
  `aw ≠ 0`, `dw ≠ 0` (`memCall?`'s guard).

`InstProv senv st`: `insts` and `instFields` have the same size and the
`k`-th pair of `insts.zip instFields` satisfies `Origin` at `st.instStruct`
(PER INDEX). It mentions `insts`, `instFields`, `instStruct` only;
`instStruct` is never reset (grep `instStruct :=`: only `:= true`), so updates
that leave the two arrays alone keep it (`instProv_congr`).

`insts`/`instFields` are written at exactly two places: `instStep` (push of
`(c, js, res)` / `"out"`) and `instSStep` (append of
`fields.map (c, js, ·.2)` / `fields.map (·.1)`).

## Premises

NONE beyond the run itself: no `MemR1`, no `SigDisj` (the invariant records
WHICH arm made the entry, not that the kinds agree with some other table).

* `step_goodP`, `readF_goodP` (every fuel);
* `machConvF_instProv`, `machChainF_instProv`, `machLoopRootF_instProv`. -/
namespace Tools.ShippingReaderFuelProv
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel
open Tools.ShippingReaderLenOk
open Tools.ShippingReaderFuelR1 (machInstCall?_inst machInstCallS?_instS)

/-! ## Origins of a call entry -/

/-- An ordinary one-Signal call (the `machInstCall?` arm). -/
def OrdOrigin (senv : StructEnv) (c : Name) (r : MixedGateBinder) : Prop :=
  ∃ kinds : List MixedGateBinder, senv.inst c = some (kinds, r)

/-- Field `i` (name `nm`, kind `r`) of a structure call, the index `i` EXPLICIT
(the `machInstCallS?` arm and `instSStep`'s own computation of the field
list). -/
def StructOriginI (senv : StructEnv) (c : Name) (r : MixedGateBinder) (nm : String) (i : Nat) :
    Prop :=
  ∃ (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (resTy : Lean.Expr)
    (ctor : Name) (fields : List (String × MixedGateBinder)),
    senv.instS c = some (kinds, ty) ∧ instRes ty args = some resTy ∧
    machOuts? senv resTy = some (some ctor, fields) ∧
    fields.any (fun f => f.2 == MixedGateBinder.domain) = false ∧
    fields[i]? = some (nm, r)

/-- Field `i` of a structure call, for SOME index (the pre-tag statement). -/
def StructOrigin (senv : StructEnv) (c : Name) (r : MixedGateBinder) (nm : String) : Prop :=
  ∃ (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (resTy : Lean.Expr)
    (ctor : Name) (fields : List (String × MixedGateBinder)) (i : Nat),
    senv.instS c = some (kinds, ty) ∧ instRes ty args = some resTy ∧
    machOuts? senv resTy = some (some ctor, fields) ∧
    fields.any (fun f => f.2 == MixedGateBinder.domain) = false ∧
    fields[i]? = some (nm, r)

theorem structOrigin_of_I {senv : StructEnv} {c : Name} {r : MixedGateBinder} {nm : String}
    {i : Nat} (h : StructOriginI senv c r nm i) : StructOrigin senv c r nm := by
  obtain ⟨kinds, ty, args, resTy, ctor, fields, h1, h2, h3, h4, h5⟩ := h
  exact ⟨kinds, ty, args, resTy, ctor, fields, i, h1, h2, h3, h4, h5⟩

/-- A synthetic memory call with EXACTLY these parameters (the memory arm). -/
def MemOriginI (c : Name) (r : MixedGateBinder) (combo : Bool) (aw dw : Nat) : Prop :=
  c = Sparkle.Compiler.MachMemory.memChildName combo aw dw ∧
    r = MixedGateBinder.bits dw ∧ aw ≠ 0 ∧ dw ≠ 0

/-- A synthetic memory call, for SOME parameters (the pre-tag statement). -/
def MemOrigin (c : Name) (r : MixedGateBinder) : Prop :=
  ∃ (combo : Bool) (aw dw : Nat), c = Sparkle.Compiler.MachMemory.memChildName combo aw dw ∧
    r = MixedGateBinder.bits dw ∧ aw ≠ 0 ∧ dw ≠ 0

theorem memOrigin_of_I {c : Name} {r : MixedGateBinder} {combo : Bool} {aw dw : Nat}
    (h : MemOriginI c r combo aw dw) : MemOrigin c r :=
  ⟨combo, aw, dw, h⟩

/-- **The origin of one call entry** `e`, with its port name `nm`, in a state
with structure flag `b` — the pre-tag disjunction (which arm made it, read
off the entry). -/
def Origin (senv : StructEnv) (e : Name × List Nat × MixedGateBinder) (nm : String)
    (b : Bool) : Prop :=
  (OrdOrigin senv e.1 e.2.2 ∧ nm = "out") ∨
  (StructOrigin senv e.1 e.2.2 nm ∧ b = true) ∨
  (MemOrigin e.1 e.2.2 ∧ nm = "out")

/-- **The origin of one call entry, by its STORED tag** `o`
(`MachRead.instOrigins`, patched compiler): the tag says which arm made the
entry, and that arm's facts hold —
`.ord`: an ordinary signature, port `out`;
`.field i`: field `i` of the callee's structure signature (index, name, kind),
structure flag set;
`.mem combo aw dw`: the memory placeholder of exactly these parameters, port
`out`. -/
def OriginT (senv : StructEnv) (e : Name × List Nat × MixedGateBinder) (nm : String)
    (b : Bool) : Sparkle.Compiler.MachInstOrigin.InstOrigin → Prop
  | .ord => OrdOrigin senv e.1 e.2.2 ∧ nm = "out"
  | .field i => StructOriginI senv e.1 e.2.2 nm i ∧ b = true
  | .mem combo aw dw => MemOriginI e.1 e.2.2 combo aw dw ∧ nm = "out"

/-- The tag's facts give the pre-tag disjunction. -/
theorem origin_of_originT {senv : StructEnv} {e : Name × List Nat × MixedGateBinder}
    {nm : String} {b : Bool} {o : Sparkle.Compiler.MachInstOrigin.InstOrigin}
    (h : OriginT senv e nm b o) : Origin senv e nm b := by
  cases o with
  | ord => exact Or.inl h
  | field i => exact Or.inr (Or.inl ⟨structOrigin_of_I h.1, h.2⟩)
  | mem combo aw dw => exact Or.inr (Or.inr ⟨memOrigin_of_I h.1, h.2⟩)

/-- **Provenance of a reader state**, per entry index, by the STORED tag:
`insts`, `instFields`, `instOrigins` have one size, and the `k`-th entry, its
port name and its tag satisfy `OriginT`. -/
def InstProv (senv : StructEnv) (st : MachRead) : Prop :=
  st.insts.size = st.instFields.size ∧ st.instOrigins.size = st.insts.size ∧
  ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder) (nm : String)
    (o : Sparkle.Compiler.MachInstOrigin.InstOrigin),
    (st.insts.toList.zip st.instFields.toList)[k]? = some (e, nm) →
      st.instOrigins.toList[k]? = some o → OriginT senv e nm st.instStruct o

/-- Every entry HAS a tag (alignment), so the pre-tag statement follows. -/
theorem InstProv.origin {senv : StructEnv} {st : MachRead} (H : InstProv senv st) :
    ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder) (nm : String),
      (st.insts.toList.zip st.instFields.toList)[k]? = some (e, nm) →
        Origin senv e nm st.instStruct := by
  obtain ⟨hsz, hosz, H⟩ := H
  intro k e nm hk
  have hlt : k < st.insts.size := by
    obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.mp hk
    rw [List.length_zip, Array.length_toList, Array.length_toList, ← hsz, Nat.min_self] at h1
    exact h1
  have hlt' : k < st.instOrigins.toList.length := by
    rw [Array.length_toList, hosz]
    exact hlt
  cases ho : st.instOrigins.toList[k]? with
  | none => exact absurd (List.getElem?_eq_none_iff.mp ho) (Nat.not_le.mpr hlt')
  | some o => exact origin_of_originT (H k e nm o hk ho)

/-! ## Update lemmas -/

section Upd
variable {senv : StructEnv}

theorem originT_mono {e : Name × List Nat × MixedGateBinder} {nm : String} {b b' : Bool}
    {o : Sparkle.Compiler.MachInstOrigin.InstOrigin}
    (h : OriginT senv e nm b o) (hb : b = true → b' = true) : OriginT senv e nm b' o := by
  cases o with
  | ord => exact h
  | field i => exact ⟨h.1, hb h.2⟩
  | mem combo aw dw => exact h

theorem origin_mono {e : Name × List Nat × MixedGateBinder} {nm : String} {b b' : Bool}
    (h : Origin senv e nm b) (hb : b = true → b' = true) : Origin senv e nm b' := by
  rcases h with h | ⟨h, hb0⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, hb hb0⟩)
  · exact Or.inr (Or.inr h)

theorem instProv_init : InstProv senv ({} : MachRead) := by
  refine ⟨rfl, rfl, ?_⟩
  intro k e nm o hk _
  first
    | (simp at hk)
    | cases hk
    | (have h0 : (none : Option ((Name × List Nat × MixedGateBinder) × String)) = some (e, nm) :=
         hk
       cases h0)

/-- Any update that leaves `insts`, `instFields`, `instOrigins` alone and does
not reset `instStruct`. -/
theorem instProv_congr {st st' : MachRead} (H : InstProv senv st)
    (he : st'.insts = st.insts) (hf : st'.instFields = st.instFields)
    (ho : st'.instOrigins = st.instOrigins)
    (hb : st.instStruct = true → st'.instStruct = true) : InstProv senv st' := by
  obtain ⟨hsz, hosz, H⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · rw [he, hf]
    exact hsz
  · rw [ho, he]
    exact hosz
  intro k e nm o hk hko
  rw [he, hf] at hk
  rw [ho] at hko
  exact originT_mono (H k e nm o hk hko) hb

/-- An update that leaves the four fields alone. -/
theorem instProv_same {st st' : MachRead} (H : InstProv senv st)
    (he : st'.insts = st.insts) (hf : st'.instFields = st.instFields)
    (ho : st'.instOrigins = st.instOrigins)
    (hb : st'.instStruct = st.instStruct) : InstProv senv st' :=
  instProv_congr H he hf ho (fun h => hb.trans h)

/-- An update that only sets `instStruct := true`. -/
theorem instProv_struct {st st' : MachRead} (H : InstProv senv st)
    (he : st'.insts = st.insts) (hf : st'.instFields = st.instFields)
    (ho : st'.instOrigins = st.instOrigins)
    (hb : st'.instStruct = true) : InstProv senv st' :=
  instProv_congr H he hf ho (fun _ => hb)

/-- What a `machInstance` call site guarantees of its parameters, per origin
tag: the ordinary arm passes `.ord` with the callee's signature; the memory
arm passes `.mem combo aw dw` with the placeholder name of exactly those
parameters; no site passes `.field _` to `machInstance`. -/
def InstPre (senv : StructEnv) (c : Name) (res : MixedGateBinder) :
    Sparkle.Compiler.MachInstOrigin.InstOrigin → Prop
  | .ord => OrdOrigin senv c res
  | .field _ => False
  | .mem combo aw dw => MemOriginI c res combo aw dw

/-- `instStep`'s push (an ordinary or a memory call): entry, port `"out"` and
the call's tag pushed together. -/
theorem instProv_push {st st' : MachRead} {c : Name} {js : List Nat} {res : MixedGateBinder}
    {o : Sparkle.Compiler.MachInstOrigin.InstOrigin}
    (H : InstProv senv st) (hc : InstPre senv c res o)
    (he : st'.insts = st.insts.push (c, js, res))
    (hf : st'.instFields = st.instFields.push "out")
    (ho : st'.instOrigins = st.instOrigins.push o)
    (hb : st'.instStruct = st.instStruct) : InstProv senv st' := by
  obtain ⟨hsz, hosz, H⟩ := H
  have hlen : st.insts.toList.length = st.instFields.toList.length := by
    rw [Array.length_toList, Array.length_toList]
    exact hsz
  have hzl : (st.insts.toList.zip st.instFields.toList).length = st.insts.size := by
    rw [List.length_zip, ← hlen, Nat.min_self, Array.length_toList]
  have hol : st.instOrigins.toList.length = st.insts.size := by
    rw [Array.length_toList]
    exact hosz
  refine ⟨?_, ?_, ?_⟩
  · rw [he, hf]
    simp only [Array.size_push, hsz]
  · rw [ho, he]
    simp only [Array.size_push, hosz]
  intro k e nm o' hk hko
  rw [he, hf, Array.toList_push, Array.toList_push, List.zip_append hlen] at hk
  rw [ho, Array.toList_push] at hko
  by_cases hlt : k < st.insts.size
  · have hz1 : k < (st.insts.toList.zip st.instFields.toList).length := by
      rw [hzl]
      exact hlt
    have ho1 : k < st.instOrigins.toList.length := by
      rw [hol]
      exact hlt
    rw [List.getElem?_append_left hz1] at hk
    rw [List.getElem?_append_left ho1] at hko
    rw [hb]
    exact H k e nm o' hk hko
  · have hge : st.insts.size ≤ k := Nat.le_of_not_lt hlt
    have hz2 : (st.insts.toList.zip st.instFields.toList).length ≤ k := by
      rw [hzl]
      exact hge
    have ho2 : st.instOrigins.toList.length ≤ k := by
      rw [hol]
      exact hge
    rw [List.getElem?_append_right hz2] at hk
    rw [List.getElem?_append_right ho2] at hko
    have hm := List.mem_of_getElem? hk
    have hm' : (e, nm) ∈ [((c, js, res), "out")] := hm
    have e1 : (e, nm) = ((c, js, res), "out") := List.mem_singleton.mp hm'
    have hmo : o' ∈ [o] := List.mem_of_getElem? hko
    have eo : o' = o := List.mem_singleton.mp hmo
    injection e1 with e2 e3
    subst e2
    subst e3
    rw [eo]
    cases o with
    | ord => exact ⟨hc, rfl⟩
    | field i => exact hc.elim
    | mem combo aw dw => exact ⟨hc, rfl⟩

/-- `instSStep`'s append (a structure call): entry `size + i` is field `i`,
its tag `.field i`. -/
theorem instProv_appendS {st st' : MachRead} {c : Name} {js : List Nat}
    {fields : List (String × MixedGateBinder)} (H : InstProv senv st)
    (horig : ∀ (i : Nat) (f : String × MixedGateBinder), fields[i]? = some f →
      StructOriginI senv c f.2 f.1 i)
    (he : st'.insts = st.insts ++ (fields.map fun f => (c, js, f.2)).toArray)
    (hf : st'.instFields = st.instFields ++ (fields.map (·.1)).toArray)
    (ho : st'.instOrigins = st.instOrigins ++
      ((List.range fields.length).map Sparkle.Compiler.MachInstOrigin.InstOrigin.field).toArray)
    (hb : st'.instStruct = true) : InstProv senv st' := by
  obtain ⟨hsz, hosz, H⟩ := H
  have hlen : st.insts.toList.length = st.instFields.toList.length := by
    rw [Array.length_toList, Array.length_toList]
    exact hsz
  have hzl : (st.insts.toList.zip st.instFields.toList).length = st.insts.size := by
    rw [List.length_zip, ← hlen, Nat.min_self, Array.length_toList]
  have hol : st.instOrigins.toList.length = st.insts.size := by
    rw [Array.length_toList]
    exact hosz
  refine ⟨?_, ?_, ?_⟩
  · rw [he, hf]
    simp only [Array.size_append, List.size_toArray, List.length_map, hsz]
  · rw [ho, he]
    simp only [Array.size_append, List.size_toArray, List.length_map, List.length_range, hosz]
  intro k e nm o' hk hko
  rw [he, hf, Array.toList_append, Array.toList_append] at hk
  simp only [List.toList_toArray] at hk
  rw [List.zip_append hlen, List.zip_map'] at hk
  rw [ho, Array.toList_append] at hko
  simp only [List.toList_toArray] at hko
  by_cases hlt : k < st.insts.size
  · have hz1 : k < (st.insts.toList.zip st.instFields.toList).length := by
      rw [hzl]
      exact hlt
    have ho1 : k < st.instOrigins.toList.length := by
      rw [hol]
      exact hlt
    rw [List.getElem?_append_left hz1] at hk
    rw [List.getElem?_append_left ho1] at hko
    exact originT_mono (H k e nm o' hk hko) (fun _ => hb)
  · have hge : st.insts.size ≤ k := Nat.le_of_not_lt hlt
    have hz2 : (st.insts.toList.zip st.instFields.toList).length ≤ k := by
      rw [hzl]
      exact hge
    have ho2 : st.instOrigins.toList.length ≤ k := by
      rw [hol]
      exact hge
    rw [List.getElem?_append_right hz2] at hk
    rw [List.getElem?_append_right ho2] at hko
    rw [hzl] at hk
    rw [hol] at hko
    rw [List.getElem?_map] at hk
    obtain ⟨f, hfi, hfe⟩ := Option.map_eq_some_iff.mp hk
    have hlt2 : k - st.insts.size < fields.length := by
      obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.mp hfi
      exact hl
    have hko2 : some (Sparkle.Compiler.MachInstOrigin.InstOrigin.field (k - st.insts.size)) =
        some o' := by
      rw [List.getElem?_map] at hko
      first
        | (rw [List.getElem?_range hlt2] at hko; exact hko)
        | (simp only [List.getElem?_range, hlt2] at hko; exact hko)
        | (simp [hlt2] at hko; rw [← hko])
    have eo := Option.some.inj hko2
    have hk3 : (((c, js, f.2), f.1) : (Name × List Nat × MixedGateBinder) × String) =
        (e, nm) := hfe
    injection hk3 with e2 e3
    subst e2
    subst e3
    rw [← eo]
    exact ⟨horig _ f hfi, hb⟩

theorem machReserve_instProv {natOf : Lean.Expr → Option Nat}
    {dom' αs initsE body : Lean.Expr} {st : MachRead} {base : Nat} {st' : MachRead}
    (H : InstProv senv st) (hr : machReserve natOf dom' αs initsE body st = some (base, st')) :
    InstProv senv st' := by
  obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hr
  subst hst
  exact instProv_same H (by rfl) (by rfl) (by rfl) (by rfl)

end Upd

/-! ## Where the call parameters come from -/

/-- `memCall?`'s guard: both widths are positive. -/
theorem memCall?_nz {natOf : Lean.Expr → Option Nat} {e : Lean.Expr} {combo : Bool}
    {aw dw : Nat} {dom : Lean.Expr} {ops : List Lean.Expr}
    (h : Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops)) :
    aw ≠ 0 ∧ dw ≠ 0 := by
  unfold Sparkle.Compiler.MachMemory.memCall? at h
  try dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨_, rfl, rfl, _, _⟩ := h
       constructor <;> intro hz <;> subst hz <;> simp_all)
    | (injection h with h1
       injection h1 with _ h2
       injection h2 with h3 h4
       injection h4 with h5 _
       subst h3
       subst h5
       constructor <;> intro hz <;> subst hz <;> simp_all)

/-- The parameters of a call, as the block's call sites make them (the
provenance version of R1's `CallPre`; for `machInstance`, per origin tag:
`InstPre`). -/
def CallPreP (senv : StructEnv) : Call → Prop
  | Call.conv _ _ _ _ => True
  | Call.nested _ _ _ _ _ _ => True
  | Call.inst _ c org _ res _ _ => InstPre senv c res org
  | Call.instS _ c kinds ty _ _ => senv.instS c = some (kinds, ty)
  | Call.chain _ _ _ => True
  | Call.loopBody _ _ _ _ => True
  | Call.loopRoot _ _ _ => True

theorem pre_of_instCallP {senv : StructEnv} {e : Lean.Expr} {c : Name}
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr}
    {env : List MachVal} {st : MachRead}
    (h : machInstCall? senv e = some (c, kinds, res, args)) :
    CallPreP senv (Call.inst env c .ord kinds res args st) := by
  show OrdOrigin senv c res
  exact ⟨kinds, machInstCall?_inst h⟩

theorem pre_of_instCallSP {senv : StructEnv} {e : Lean.Expr} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    {env : List MachVal} {st : MachRead}
    (h : machInstCallS? senv e = some (c, kinds, ty, args)) :
    CallPreP senv (Call.instS env c kinds ty args st) := by
  show senv.instS c = some (kinds, ty)
  exact machInstCallS?_instS h

theorem pre_of_memP {senv : StructEnv} {natOf : Lean.Expr → Option Nat} {e : Lean.Expr}
    {combo : Bool} {aw dw : Nat} {dom : Lean.Expr} {ops : List Lean.Expr}
    (hm : Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops))
    {kinds : List MixedGateBinder} {args : List Lean.Expr} {env : List MachVal}
    {st : MachRead} :
    CallPreP senv (Call.inst env (Sparkle.Compiler.MachMemory.memChildName combo aw dw)
      (.mem combo aw dw) kinds (MixedGateBinder.bits dw) args st) := by
  show MemOriginI _ _ combo aw dw
  obtain ⟨ha, hd⟩ := memCall?_nz hm
  exact ⟨rfl, rfl, ha, hd⟩

/-! ## Call tables that keep the invariant -/

/-- A call table that keeps provenance. -/
def GoodP (senv : StructEnv) (h : Hs) : Prop :=
  ∀ c, CallPreP senv c → InstProv senv (Call.inSt c) → ∀ v, h c = some (some v) →
    InstProv senv (Call.outSt c v)

/-- The result's state satisfies provenance. -/
abbrev StP {α : Type} [HasSt α] (senv : StructEnv) (a : α) : Prop := InstProv senv (HasSt.st a)

/-- Every OK result of `x` (against `h`) has a state satisfying provenance. -/
abbrev SatP {α : Type} [HasSt α] (senv : StructEnv) (h : Hs) (x : BM (Option α)) : Prop :=
  ∀ a, x.run h = some (some a) → StP senv a

/-! ## Combinators (as in the R5 file) -/

section Comb
variable {senv : StructEnv} {h : Hs} {α β : Type} [HasSt α]

theorem satP_pure {o : Option α} (ho : ∀ a, o = some a → StP senv a) :
    SatP senv h (FM.pure o) := by
  intro a ha
  rw [run_pure] at ha
  exact ho a (Option.some.inj ha)

theorem satP_okO {a : α} (ha : StP senv a) : SatP senv h (okO a) :=
  satP_pure fun b hb => by
    injection hb with hb1
    subst hb1
    exact ha

theorem satP_failO : SatP senv h (failO : BM (Option α)) :=
  satP_pure fun b hb => by cases hb

theorem satP_optK {o : Option β} {f : β → BM (Option α)}
    (hf : ∀ b, o = some b → SatP senv h (f b)) : SatP senv h (optK o f) := by
  cases o with
  | none => exact satP_failO
  | some b => exact hf b rfl

theorem satP_bindO [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} (hx : SatP senv h x)
    (hf : ∀ b, StP senv b → SatP senv h (f b)) : SatP senv h (bindO x f) := by
  intro a ha
  rw [run_bindO] at ha
  obtain ⟨o, ho, ha⟩ := Option.bind_eq_some_iff.mp ha
  cases o with
  | none =>
    have hn : (some none : Option (Option α)) = some (some a) := ha
    cases hn
  | some b => exact hf b (hx b ho) a ha

theorem satP_bind {x : BM β} {f : β → BM (Option α)}
    (hf : ∀ r, x.run h = some r → SatP senv h (f r)) : SatP senv h (FM.bind x f) := by
  intro a ha
  rw [run_bind] at ha
  obtain ⟨r, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  exact hf r hr a ha

theorem satP_ite {c : Prop} [Decidable c] {x y : BM (Option α)} (hx : SatP senv h x)
    (hy : SatP senv h y) : SatP senv h (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx
  · rw [if_neg hc]
    exact hy

/-- `satP_ite` keeping the negated condition for the `else` branch. -/
theorem satP_iteN {c : Prop} [Decidable c] {x y : BM (Option α)} (hx : SatP senv h x)
    (hy : ¬c → SatP senv h y) : SatP senv h (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact hx
  · rw [if_neg hc]
    exact hy hc

theorem satP_domGuard {o : Option Lean.Expr} {dom' : Lean.Expr} {k : BM (Option α)}
    (hk : SatP senv h k) : SatP senv h (domGuard o dom' k) := by
  cases o with
  | none => exact hk
  | some d0 =>
    first
      | exact satP_ite satP_failO hk
      | (simp only [domGuard]; exact satP_ite satP_failO hk)

theorem satP_pure_ite {c : Prop} [Decidable c] {a : α} (ha : StP senv a) :
    SatP senv h (FM.pure (if c then some a else none)) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact satP_okO ha
  · rw [if_neg hc]
    exact satP_failO

end Comb

theorem satP_foldO {senv : StructEnv} {σ α : Type} [HasSt σ] {h : Hs}
    {f : σ → α → BM (Option σ)} (hf : ∀ s a, StP senv s → SatP senv h (f s a)) :
    ∀ (l : List α) (s : σ), StP senv s → SatP senv h (foldO f s l)
  | [], _, hs => satP_okO hs
  | a :: l, s, hs => satP_bindO (hf s a hs) (fun s' hs' => satP_foldO hf l s' hs')

theorem satP_findSomeO {senv : StructEnv} {α β : Type} [HasSt β] {h : Hs}
    {f : α → BM (Option β)} (hf : ∀ a, SatP senv h (f a)) :
    ∀ (l : List α), SatP senv h (findSomeO f l)
  | [] => satP_failO
  | a :: l => by
    refine satP_bind ?_
    intro r hr
    cases r with
    | none => exact satP_findSomeO hf l
    | some b => exact satP_okO (hf a b hr)

/-! ## The answers of the calls, as `SatP` facts -/

section Out
variable {senv : StructEnv} {h : Hs}

theorem satP_cConv (hG : GoodP senv h) {env : List MachVal} {d : Nat} {e : Lean.Expr}
    {st : MachRead} (hst : InstProv senv st) : SatP senv h (cConv env d e st) :=
  fun p hp => hG (Call.conv env d e st) True.intro hst p hp

theorem satP_cNested (hG : GoodP senv h) {env : List MachVal} {dom αs initsE body : Lean.Expr}
    {st : MachRead} (hst : InstProv senv st) : SatP senv h (cNested env dom αs initsE body st) :=
  fun p hp => hG (Call.nested env dom αs initsE body st) True.intro hst p hp

theorem satP_cInst (hG : GoodP senv h) {env : List MachVal} {c : Name}
    {org : Sparkle.Compiler.MachInstOrigin.InstOrigin}
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr}
    {st : MachRead} (hpre : CallPreP senv (Call.inst env c org kinds res args st))
    (hst : InstProv senv st) : SatP senv h (cInst env c org kinds res args st) :=
  fun p hp => hG (Call.inst env c org kinds res args st) hpre hst p hp

theorem satP_cInstS (hG : GoodP senv h) {env : List MachVal} {c : Name}
    {kinds : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr} {st : MachRead}
    (hpre : CallPreP senv (Call.instS env c kinds ty args st))
    (hst : InstProv senv st) : SatP senv h (cInstS env c kinds ty args st) :=
  fun p hp => hG (Call.instS env c kinds ty args st) hpre hst p hp

theorem satP_cChain (hG : GoodP senv h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hst : InstProv senv st) : SatP senv h (cChain env e st) :=
  fun p hp => hG (Call.chain env e st) True.intro hst p hp

theorem satP_cLoopBody (hG : GoodP senv h) {base : Nat} {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} (hst : InstProv senv st) : SatP senv h (cLoopBody base env e st) :=
  fun p hp => hG (Call.loopBody base env e st) True.intro hst p hp

theorem satP_cLoopRoot (hG : GoodP senv h) {env : List MachVal} {e : Lean.Expr}
    {st : MachRead} (hst : InstProv senv st) : SatP senv h (cLoopRoot env e st) :=
  fun p hp => hG (Call.loopRoot env e st) True.intro hst p hp

end Out

/-! ## Pure fragments -/

/-- `machConv`'s `.bvar` arm returns its input state. -/
theorem convBvar_prov {senv : StructEnv} {env : List MachVal} {d j : Nat} {st : MachRead}
    {r : Lean.Expr × MachRead} (hr : convBvar env d j st = some r) (hst : InstProv senv st) :
    StP senv r := by
  unfold convBvar at hr
  split at hr
  · injection hr with hr1
    subst hr1
    exact hst
  · split at hr
    all_goals first
      | (cases hr; done)
      | (injection hr with hr1; subst hr1; exact hst)
      | (try simp only [Option.bind_eq_bind] at hr
         obtain ⟨_, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         obtain ⟨_, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         obtain ⟨⟨_, _⟩, _, hr⟩ := Option.bind_eq_some_iff.mp hr
         injection hr with hr1
         subst hr1
         exact hst)

theorem instEntry_prov {senv : StructEnv} {res : MixedGateBinder} {st st' : MachRead}
    (hr : instEntry res st = some st') (hst : InstProv senv st) : InstProv senv st' := by
  cases res with
  | bits w =>
    have hr' : some st = some st' := hr
    injection hr' with hr1
    subst hr1
    exact hst
  | bool =>
    have hr' : some { st with instStruct := true } = some st' := hr
    injection hr' with hr1
    subst hr1
    exact instProv_struct hst (by rfl) (by rfl) (by rfl) (by rfl)
  | domain =>
    have hr' : (none : Option MachRead) = some st' := hr
    cases hr'

/-- A leaf `hr : o = some r` whose state is the hypothesis' state or an update
of it that leaves `insts` alone. -/
macro "provleaf " hr:ident h1:ident : tactic => `(tactic| first
  | (cases $hr:ident; done)
  | (injection $hr:ident with hq; subst hq; exact $h1:ident)
  | (injection $hr:ident with hq; subst hq; exact instProv_same $h1:ident (by rfl) (by rfl) (by rfl) (by rfl))
  | (cases $hr:ident; exact $h1:ident)
  | (cases $hr:ident; exact instProv_same $h1:ident (by rfl) (by rfl) (by rfl) (by rfl)))

/-- A `let (x, y) := p; k` continuation (as `r5pair`). -/
macro "provpair " t:tactic : tactic => `(tactic| first
  | $t:tactic
  | (split <;> $t:tactic)
  | ((try dsimp only); split <;> $t:tactic)
  | ((try dsimp only); (repeat' split) <;> $t:tactic))

/-! ## The `foldlM` / `findSome?` functions -/

section Helpers
variable {senv : StructEnv} {h : Hs}

theorem instArg_satP (hG : GoodP senv h) (env : List MachVal) (k : Nat) :
    ∀ s a, StP senv s → SatP senv h (instArg env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hst : InstProv senv st)
  refine satP_bindO (satP_cConv hG hst) ?_
  rintro ⟨v', st1⟩ (h1 : InstProv senv st1)
  refine satP_pure ?_
  intro r hr
  repeat' split at hr
  all_goals provleaf hr h1

theorem instSArg_satP (hG : GoodP senv h) (env : List MachVal) :
    ∀ s a, StP senv s → SatP senv h (instSArg env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩ (hst : InstProv senv st)
  refine satP_bindO (satP_cConv hG hst) ?_
  rintro ⟨v', st1⟩ (h1 : InstProv senv st1)
  refine satP_pure ?_
  intro r hr
  repeat' split at hr
  all_goals provleaf hr h1

theorem instSParam_satP (hG : GoodP senv h) (env : List MachVal) :
    ∀ s a, StP senv s → SatP senv h (instSParam env s a) := by
  rintro ⟨ps, st⟩ p (hst : InstProv senv st)
  refine satP_bindO (satP_cConv hG hst) ?_
  rintro ⟨p', st1⟩ (h1 : InstProv senv st1)
  refine satP_okO ?_
  exact h1

theorem loopNext_satP (hG : GoodP senv h) (env : List MachVal) (base : Nat) :
    ∀ s a, StP senv s → SatP senv h (loopNext env base s a) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩ (hst : InstProv senv st)
  refine satP_bindO (satP_cConv hG hst) ?_
  rintro ⟨nx', st1⟩ (h1 : InstProv senv st1)
  refine satP_okO ?_
  exact h1

theorem nestedProbe_satP (hG : GoodP senv h) (env : List MachVal)
    (dom' αs initsE body : Lean.Expr) (st : MachRead) (hst : InstProv senv st) :
    ∀ a, SatP senv h (nestedProbe env dom' αs initsE body st a) := by
  rintro ⟨base, d, a, ini, ws, v⟩
  refine satP_ite ?_ satP_failO
  refine satP_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact satP_failO
  · have h' : InstProv senv st' := satP_cChain hG hst (ws', v', st') hr
    refine satP_pure_ite ?_
    exact h'

theorem loopProbe_satP (hG : GoodP senv h) (env : List MachVal) (body : Lean.Expr) (n : Nat)
    (st : MachRead) (hst : InstProv senv st) : ∀ a, SatP senv h (loopProbe env body n st a) := by
  rintro ⟨b0, n0, ws0⟩
  refine satP_ite satP_failO ?_
  refine satP_bind ?_
  intro r hr
  rcases r with _ | st'
  · exact satP_failO
  · have h' : InstProv senv st' := satP_cLoopBody hG (instProv_same hst (by rfl) (by rfl) (by rfl) (by rfl)) st' hr
    refine satP_pure_ite ?_
    exact instProv_same h' (by rfl) (by rfl) (by rfl) (by rfl)

end Helpers

/-! ## The seven bodies -/

section Arms
variable {h : Hs}

/-- `machConv`'s `.app` arm (as `conv_app_sat`; the two instance arms and the
memory arm discharge `CallPreP`). -/
theorem conv_app_satP (senv : StructEnv)
    (hG : GoodP senv h) (env : List MachVal) (d : Nat)
    (f a : Lean.Expr) (st : MachRead) (hst : InstProv senv st) :
    SatP senv h (convStep senv env d (.app f a) st) := by
  first
    | simp only [convStep]
    | (unfold convStep; dsimp only)
  split
  · -- a bare `Signal.register`
    refine satP_ite satP_failO ?_
    split
    · refine satP_okO ?_
      exact hst
    · refine satP_optK ?_
      intro kind _
      refine satP_optK ?_
      intro initN _
      refine satP_bindO (satP_cConv hG hst) ?_
      rintro ⟨dom', st1⟩ (h1 : InstProv senv st1)
      refine satP_domGuard ?_
      refine satP_bindO (satP_cConv hG (instProv_same h1 (by rfl) (by rfl) (by rfl) (by rfl))) ?_
      rintro ⟨x', st2⟩ (h2 : InstProv senv st2)
      refine satP_okO ?_
      exact instProv_same h2 (by rfl) (by rfl) (by rfl) (by rfl)
  · split
    · -- a loop read
      refine satP_pure_ite ?_
      exact hst
    · split
      · -- a nested machine
        exact satP_ite satP_failO (satP_cNested hG hst)
      · split
        · -- an instance: the parameters ARE the signature (`machInstCall?_inst`)
          refine satP_ite satP_failO (satP_cInst hG ?pre hst)
          case pre => exact pre_of_instCallP (by assumption)
        · split
          · -- a structure instance: its structure signature (`machInstCallS?_instS`)
            refine satP_ite satP_failO (satP_cInstS hG ?pre hst)
            case pre => exact pre_of_instCallSP (by assumption)
          · split
            · -- a memory: the placeholder name (`memCall?`)
              refine satP_ite satP_failO (satP_bindO (satP_cInst hG ?pre hst) ?k)
              case pre => exact pre_of_memP (by assumption)
              case k =>
                rintro ⟨v, st1⟩ (h1 : InstProv senv st1)
                refine satP_okO ?_
                exact instProv_struct h1 (by rfl) (by rfl) (by rfl) (by rfl)
            · split
              · -- a state read
                refine satP_pure_ite ?_
                exact hst
              · -- an application
                refine satP_bindO (satP_cConv hG hst) ?_
                rintro ⟨f', st1⟩ (h1 : InstProv senv st1)
                refine satP_bindO (satP_cConv hG h1) ?_
                rintro ⟨a', st2⟩ (h2 : InstProv senv st2)
                refine satP_okO ?_
                exact h2

/-- `machConv`'s `.letE` arm. -/
theorem conv_letE_satP (senv : StructEnv) (hG : GoodP senv h) (env : List MachVal) (d : Nat)
    (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead) (hst : InstProv senv st) :
    SatP senv h (convStep senv env d (.letE nm ty v b nd) st) := by
  refine satP_ite satP_failO ?_
  split
  · exact satP_cConv hG hst
  · refine satP_ite ?_ ?_
    · refine satP_bindO (satP_cLoopRoot hG hst) ?_
      rintro ⟨mv, st1⟩ (h1 : InstProv senv st1)
      exact satP_cConv hG h1
    · split
      · exact satP_cConv hG hst
      · split
        · exact satP_cConv hG hst
        · refine satP_bindO (satP_cConv hG hst) ?_
          rintro ⟨v', st1⟩ (h1 : InstProv senv st1)
          provpair (exact satP_cConv hG (instProv_same h1 (by rfl) (by rfl) (by rfl) (by rfl)))

/-- `machConv`. -/
theorem conv_satP (senv : StructEnv)
    (hG : GoodP senv h) (env : List MachVal) (d : Nat)
    (e : Lean.Expr) (st : MachRead) (hst : InstProv senv st) :
    SatP senv h (convStep senv env d e st) := by
  cases e
  case bvar j =>
    refine satP_pure ?_
    intro r hr
    exact convBvar_prov hr hst
  case app f a => exact conv_app_satP senv hG env d f a st hst
  case letE nm ty v b nd => exact conv_letE_satP senv hG env d nm ty v b nd st hst
  case lam nm t b bi =>
    refine satP_bindO (satP_cConv hG hst) ?_
    rintro ⟨t', st1⟩ (h1 : InstProv senv st1)
    refine satP_bindO (satP_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : InstProv senv st2)
    refine satP_okO ?_
    exact h2
  case forallE nm t b bi =>
    refine satP_bindO (satP_cConv hG hst) ?_
    rintro ⟨t', st1⟩ (h1 : InstProv senv st1)
    refine satP_bindO (satP_cConv hG h1) ?_
    rintro ⟨b', st2⟩ (h2 : InstProv senv st2)
    refine satP_okO ?_
    exact h2
  all_goals first
    | (refine satP_okO ?_; exact hst)
    | exact satP_failO

/-- `machNested`. -/
theorem nested_satP (senv : StructEnv) (hG : GoodP senv h) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) (hst : InstProv senv st) :
    SatP senv h (nestedStep senv env dom αs initsE body st) := by
  refine satP_ite satP_failO ?_
  refine satP_bindO (satP_cConv hG hst) ?_
  rintro ⟨dom', st1⟩ (h1 : InstProv senv st1)
  refine satP_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · refine satP_optK ?_
    rintro ⟨base, st2⟩ hres
    have h2 : InstProv senv st2 := machReserve_instProv h1 hres
    refine satP_bindO (satP_cChain hG (instProv_same h2 (by rfl) (by rfl) (by rfl) (by rfl))) ?_
    rintro ⟨ws, v, st3⟩ (h3 : InstProv senv st3)
    refine satP_okO ?_
    exact instProv_same h3 (by rfl) (by rfl) (by rfl) (by rfl)
  · refine satP_okO ?_
    exact satP_findSomeO (nestedProbe_satP hG _ _ _ _ _ _ h1) _ r hsh

/-- `machInstance`: the push carries the call's callee and `res`, whose origin
`CallPreP` records (an ordinary signature or a memory placeholder). -/
theorem inst_satP {senv : StructEnv} (hG : GoodP senv h) (env : List MachVal) (c : Name)
    (org : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr)
    (st : MachRead)
    (hpre : InstPre senv c res org)
    (hst : InstProv senv st) : SatP senv h (instStep env c org kinds res args st) := by
  refine satP_optK ?_
  intro st1 hst1
  have h1 : InstProv senv st1 := instEntry_prov hst1 hst
  refine satP_bindO (satP_foldO (instArg_satP hG env _) _ _ ?_) ?_
  · exact h1
  rintro ⟨js, st2⟩ (h2 : InstProv senv st2)
  refine satP_pure ?_
  intro r hr
  split at hr
  all_goals first
    | (cases hr; done)
    | (injection hr with hq; subst hq; exact h2)
    | (injection hr with hq; subst hq; exact instProv_push (js := js) h2 hpre (by rfl) (by rfl) (by rfl) (by rfl))
    | (cases hr; exact h2)
    | (cases hr; exact instProv_push (js := js) h2 hpre (by rfl) (by rfl) (by rfl) (by rfl))

/-- `machInstanceS`: the appended entries are the fields of the callee's
structure signature (`CallPreP`), each with its index, kind and name. -/
theorem instS_satP (senv : StructEnv) (hG : GoodP senv h) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead)
    (hpre : senv.instS c = some (kinds, ty))
    (hst : InstProv senv st) : SatP senv h (instSStep senv env c kinds ty args st) := by
  refine satP_ite satP_failO ?_
  refine satP_optK ?_
  intro resTy hres
  refine satP_optK ?_
  intro r hout
  obtain ⟨oc, fields⟩ := r
  cases oc with
  | none => exact satP_failO
  | some ctor =>
    refine satP_iteN satP_failO ?_
    intro hguard
    have hnd : fields.any (fun f => f.2 == MixedGateBinder.domain) = false := by
      cases h2 : fields.any (fun f => f.2 == MixedGateBinder.domain) with
      | false => rfl
      | true =>
        exfalso
        apply hguard
        first
          | (rw [h2, Bool.or_true])
          | (simp [h2])
    refine satP_bindO (satP_foldO (instSArg_satP hG env) _ _ ?_) ?_
    · exact hst
    rintro ⟨js, st1⟩ (h1 : InstProv senv st1)
    refine satP_bindO (satP_foldO (instSParam_satP hG env) _ _ ?_) ?_
    · exact h1
    rintro ⟨params, st2⟩ (h2 : InstProv senv st2)
    try dsimp only
    split
    · refine satP_okO ?_
      exact h2
    · refine satP_okO ?_
      exact instProv_appendS (js := js) (fields := fields) h2
        (fun i f hfi => ⟨kinds, ty, args, resTy, ctor, fields, hpre, hres, hout, hnd, hfi⟩)
        (by rfl) (by rfl) (by rfl) (by rfl)

/-- `machChain`. -/
theorem chain_satP (senv : StructEnv) (hG : GoodP senv h) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) (hst : InstProv senv st) : SatP senv h (chainStep senv env e st) := by
  revert hst
  unfold chainStep
  split
  · intro hst
    refine satP_bindO (satP_cConv hG hst) ?_
    rintro ⟨v', st1⟩ (h1 : InstProv senv st1)
    refine satP_okO ?_
    exact h1
  · intro hst
    refine satP_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → InstProv senv b := by
      intro a b he
      subst he
      exact satP_cConv hG hst (a, b) hr
    revert hr'
    split
    · intro hr'
      have h1 := hr' _ _ rfl
      refine satP_ite ?_ satP_failO
      refine satP_bindO (satP_cChain hG h1) ?_
      rintro ⟨ws, v, st2⟩ (h2 : InstProv senv st2)
      refine satP_okO ?_
      exact h2
    · intro _
      exact satP_failO
  · intro hst
    split
    · exact satP_cChain hG hst
    · refine satP_ite ?_ ?_
      · refine satP_bindO (satP_cLoopRoot hG hst) ?_
        rintro ⟨mv, st1⟩ (h1 : InstProv senv st1)
        exact satP_cChain hG h1
      · split
        · exact satP_cChain hG hst
        · split
          · exact satP_cChain hG hst
          · refine satP_bindO (satP_cConv hG hst) ?_
            rintro ⟨v', st1⟩ (h1 : InstProv senv st1)
            provpair (exact satP_cChain hG (instProv_same h1 (by rfl) (by rfl) (by rfl) (by rfl)))
  · intro _
    exact satP_failO

/-- `machLoopBody`. -/
theorem loopBody_satP {senv : StructEnv} (hG : GoodP senv h) (base : Nat) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : InstProv senv st) :
    SatP senv h (loopBodyStep base env e st) := by
  cases e
  case letE nm ty v b nd =>
    refine satP_bindO (satP_cConv hG hst) ?_
    rintro ⟨v', st1⟩ (h1 : InstProv senv st1)
    provpair (exact satP_cLoopBody hG (instProv_same h1 (by rfl) (by rfl) (by rfl) (by rfl)))
  all_goals
    unfold loopBodyStep
    try dsimp only
    refine satP_optK ?_
    intro regs _
    refine satP_bindO (satP_foldO (loopNext_satP hG _ _) _ _ ?_) ?_
    · exact hst
    rintro ⟨ws, st1⟩ (h1 : InstProv senv st1)
    refine satP_okO ?_
    exact instProv_same h1 (by rfl) (by rfl) (by rfl) (by rfl)

/-- `machLoopRoot`. -/
theorem loopRoot_satP (senv : StructEnv) (hG : GoodP senv h) (env : List MachVal)
    (e : Lean.Expr) (st : MachRead) (hst : InstProv senv st) :
    SatP senv h (loopRootStep senv env e st) := by
  unfold loopRootStep
  split
  · refine satP_ite satP_failO ?_
    refine satP_optK ?_
    intro regs _
    refine satP_ite satP_failO ?_
    refine satP_optK ?_
    intro kinds _
    refine satP_optK ?_
    intro inits _
    refine satP_bindO (satP_cConv hG hst) ?_
    rintro ⟨dom', st1⟩ (h1 : InstProv senv st1)
    refine satP_domGuard ?_
    refine satP_bind ?_
    intro shared hsh
    rcases shared with _ | ⟨b0, st2⟩
    · refine satP_bindO (satP_cLoopBody hG (instProv_same h1 (by rfl) (by rfl) (by rfl) (by rfl))) ?_
      rintro st3 (h3 : InstProv senv st3)
      refine satP_okO ?_
      exact instProv_same h3 (by rfl) (by rfl) (by rfl) (by rfl)
    · refine satP_okO ?_
      exact satP_findSomeO (loopProbe_satP hG _ _ _ _ h1) _ (b0, st2) hsh
  · exact satP_failO

end Arms

/-- **One step keeps provenance**: if the table keeps it, the body run against
the table keeps it (NO hypothesis on `senv`). -/
theorem step_goodP (senv : StructEnv) {h : Hs}
    (hG : GoodP senv h) : GoodP senv (fun c => (step senv c).run h) := by
  intro c hpre hin v hv
  cases c with
  | conv env d e st => exact conv_satP senv hG env d e st hin v hv
  | nested env dom αs initsE body st =>
    exact nested_satP senv hG env dom αs initsE body st hin v hv
  | inst env c org kinds res args st =>
    exact inst_satP hG env c org kinds res args st hpre hin v hv
  | instS env c kinds ty args st => exact instS_satP senv hG env c kinds ty args st hpre hin v hv
  | chain env e st => exact chain_satP senv hG env e st hin v hv
  | loopBody base env e st => exact loopBody_satP hG base env e st hin v hv
  | loopRoot env e st => exact loopRoot_satP senv hG env e st hin v hv

/-- **Provenance of the fuel reader, for ALL fuels** (induction on the fuel). -/
theorem readF_goodP (senv : StructEnv) :
    ∀ n, GoodP senv (readF senv n)
  | 0 => fun c _ _ v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => step_goodP senv (readF_goodP senv n)

theorem machConvF_instProv {n : Nat} {senv : StructEnv}
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead} {r : Lean.Expr}
    {st' : MachRead} (h : machConvF n senv env d e st = some (some (r, st')))
    (hst : InstProv senv st) : InstProv senv st' :=
  readF_goodP senv n (Call.conv env d e st) True.intro hst (r, st') h

theorem machChainF_instProv {n : Nat} {senv : StructEnv}
    {env : List MachVal} {e : Lean.Expr} {st : MachRead} {ws : List (Nat × Lean.Expr)}
    {v : Lean.Expr} {st' : MachRead} (h : machChainF n senv env e st = some (some (ws, v, st')))
    (hst : InstProv senv st) : InstProv senv st' :=
  readF_goodP senv n (Call.chain env e st) True.intro hst (ws, v, st') h

theorem machLoopRootF_instProv {n : Nat} {senv : StructEnv}
    {env : List MachVal} {e : Lean.Expr} {st : MachRead} {mv : MachVal}
    {st' : MachRead} (h : machLoopRootF n senv env e st = some (some (mv, st')))
    (hst : InstProv senv st) : InstProv senv st' :=
  readF_goodP senv n (Call.loopRoot env e st) True.intro hst (mv, st') h


end Tools.ShippingReaderFuelProv
