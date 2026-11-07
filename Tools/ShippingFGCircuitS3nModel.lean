import Tools.ShippingHeapModel
set_option autoImplicit false
-- FG circuit pilot S3n (E1, step 2): a minimal explicit-state model, built ON TOP OF the existing `Tools.ShippingHeapModel` (reused, not re-implemented): the three tracked cells and the typed ref constructors come from there; this file adds (i) the diagnostic-output and environment-variable component as the registry type `P`, (ii) the leaf actions `getStderr` / `getEnv` / `eprintln`, (iii) distinct locations for `mref` / `cref` / a side cell, (iv) one concrete initial state, a quiet that holds in it and is not `False`, and a short successful execution.  Everything here is a theorem about THIS model, not about `CellPrem` / `Laws` of the existing opaque IO types.  No sorry/axiom/native_decide/TRUSTED/law.  docs/FG-CIRCUIT-PILOT.md §64.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3n
open Tools.ShippingHeapModel

/-- the diagnostic component: what was written to standard error, and the environment variables -/
structure DiagEnv where
  stderr : List String
  env : List (String × String)

def DiagEnv.getEnv (d : DiagEnv) (k : String) : Option String :=
  (d.env.find? (fun p => p.1 == k)).map (fun p => p.2)

/-- the signature: the contents types of the cache `C` and the synthesis ref `S` are parameters (the depth is `Nat`); every OTHER cell (`mref`, `cref`, side cells) holds a `Nat` (one shared type: the reused `Sig` has a single `O`); `P` is the diagnostic/environment component; exceptions are strings -/
abbrev sigOf (C S : Type) : Sig := ⟨C, S, Nat, DiagEnv, String⟩

section Model
variable {C S : Type}

/-- the three tracked refs (typed: distinct types `C`, `S`, `Nat`, distinct constructors) -/
abbrev rCache : Ref (sigOf C S) C := Ref.cache
abbrev rSynth : Ref (sigOf C S) S := Ref.synth
abbrev rDepth : Ref (sigOf C S) Nat := Ref.depth
/-- the Meta-state ref, the Core-state ref and one side cell: three further, pairwise distinct locations (all of type `Nat` in this model) -/
abbrev rMref : Ref (sigOf C S) Nat := Ref.other 0
abbrev rCref : Ref (sigOf C S) Nat := Ref.other 1
abbrev rSide : Ref (sigOf C S) Nat := Ref.other 2

/-- `IO.getStderr`: the stream handle itself is NOT modelled (the action returns `Unit`); the heap is untouched -/
def getStderrM : M (sigOf C S) Unit := fun h => .ok () h
/-- `IO.getEnv k`: looks `k` up in the environment component; the heap is untouched -/
def getEnvM (k : String) : M (sigOf C S) (Option String) := fun h => .ok (h.reg.getEnv k) h
/-- `IO.eprintln s`: appends to the diagnostic output component only -/
def eprintlnM (s : String) : M (sigOf C S) Unit := fun h =>
  .ok () { h with reg := { h.reg with stderr := h.reg.stderr ++ [s] } }

/-- the concrete quiet: the environment variable `SPARKLE_DEBUG` is not set (a predicate on the environment component) -/
def quietM (h : Heap (sigOf C S)) : Prop := h.reg.getEnv "SPARKLE_DEBUG" = none

instance (h : Heap (sigOf C S)) : Decidable (quietM h) :=
  inferInstanceAs (Decidable (h.reg.getEnv "SPARKLE_DEBUG" = none))

/-! ## get / set: read-back and non-interference between the typed locations -/

theorem readback_depth (v : Nat) (h : Heap (sigOf C S)) : hget rDepth (hset rDepth v h) = v := get_set_same _ _ _
theorem readback_cache (v : C) (h : Heap (sigOf C S)) : hget rCache (hset rCache v h) = v := get_set_same _ _ _
theorem readback_mref (v : Nat) (h : Heap (sigOf C S)) : hget rMref (hset rMref v h) = v := get_set_same _ _ _

/-- a write of `mref` leaves `cref`, the side cell and the three tracked cells -/
theorem set_mref_frame (v : Nat) (h : Heap (sigOf C S)) :
    hget (rCref (C := C) (S := S)) (hset rMref v h) = hget rCref h ∧
    hget (rSide (C := C) (S := S)) (hset rMref v h) = hget rSide h ∧
    hget (rCache (S := S)) (hset (rMref (C := C)) v h) = hget rCache h ∧
    hget (rSynth (C := C)) (hset (rMref (S := S)) v h) = hget rSynth h ∧
    hget (rDepth (C := C) (S := S)) (hset rMref v h) = hget rDepth h :=
  ⟨get_set_other _ _ _ _ (by decide), get_set_other _ _ _ _ (by decide), get_set_other _ _ _ _ (by decide),
   get_set_other _ _ _ _ (by decide), get_set_other _ _ _ _ (by decide)⟩

/-- a write of the depth cell leaves the cache, the synthesis ref, `mref` and `cref` -/
theorem set_depth_frame (v : Nat) (h : Heap (sigOf C S)) :
    hget (rCache (S := S)) (hset (rDepth (C := C)) v h) = hget rCache h ∧
    hget (rSynth (C := C)) (hset (rDepth (S := S)) v h) = hget rSynth h ∧
    hget (rMref (C := C) (S := S)) (hset rDepth v h) = hget rMref h ∧
    hget (rCref (C := C) (S := S)) (hset rDepth v h) = hget rCref h :=
  ⟨get_set_other _ _ _ _ (by decide), get_set_other _ _ _ _ (by decide), get_set_other _ _ _ _ (by decide),
   get_set_other _ _ _ _ (by decide)⟩

/-! ## the diagnostic leaves keep the tracked heap -/

/-- `getStderr` ends in the same heap: the three tracked cells, the other cells, the diagnostic component, the quiet -/
theorem getStderr_keeps {h h' : Heap (sigOf C S)} {a : Unit} (hr : RunsTo getStderrM h a h') :
    h' = h ∧ cv h' = cv h ∧ sv h' = sv h ∧ dv h' = dv h ∧ (quietM h' ↔ quietM h) := by
  change Out.ok () h = Out.ok a h' at hr
  injection hr with _ h2
  subst h2
  exact ⟨rfl, rfl, rfl, rfl, Iff.rfl⟩

/-- `getEnv k` ends in the same heap and returns the environment lookup -/
theorem getEnv_keeps (k : String) {h h' : Heap (sigOf C S)} {a : Option String} (hr : RunsTo (getEnvM k) h a h') :
    a = h.reg.getEnv k ∧ h' = h ∧ cv h' = cv h ∧ sv h' = sv h ∧ dv h' = dv h ∧ (quietM h' ↔ quietM h) := by
  change Out.ok (h.reg.getEnv k) h = Out.ok a h' at hr
  injection hr with h1 h2
  subst h2
  exact ⟨h1.symm, rfl, rfl, rfl, rfl, Iff.rfl⟩

/-- `eprintln` changes only the output component: the tracked cells, the other cells and the environment (hence quiet) survive -/
theorem eprintln_keeps (s : String) {h h' : Heap (sigOf C S)} {u : Unit} (hr : RunsTo (eprintlnM s) h u h') :
    cv h' = cv h ∧ sv h' = sv h ∧ dv h' = dv h ∧ h'.other = h.other ∧ h'.reg.stderr = h.reg.stderr ++ [s] ∧
      h'.reg.env = h.reg.env ∧ (quietM h' ↔ quietM h) := by
  change Out.ok () { h with reg := { h.reg with stderr := h.reg.stderr ++ [s] } } = Out.ok u h' at hr
  injection hr with _ h2
  subst h2
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩

end Model

/-! ## a concrete model: initial state, a quiet that holds in it and is not `False`, a successful run -/

/-- cache = list of numbers, synthesis ref = optional number -/
abbrev exSig : Sig := sigOf (List Nat) (Option Nat)

def s0 : Heap exSig :=
  { cache := [10], synth := some 7, depth := 0, other := fun _ => 0, next := 3,
    reg := { stderr := [], env := [("HOME", "/root")] } }

/-- a state in which the quiet fails (`SPARKLE_DEBUG` is set) -/
def sLoud : Heap exSig := { s0 with reg := { stderr := [], env := [("SPARKLE_DEBUG", "1")] } }

theorem quiet_s0 : quietM s0 := by decide
theorem quiet_fails_sLoud : ¬ quietM sLoud := by decide
/-- the quiet is neither `False` nor `True` on the model -/
theorem quiet_nonconst : (∃ h : Heap exSig, quietM h) ∧ (∃ h : Heap exSig, ¬ quietM h) :=
  ⟨⟨s0, quiet_s0⟩, ⟨sLoud, quiet_fails_sLoud⟩⟩

/-- the existing ref-only law bundle of `ShippingHeapModel` (over the model, NOT `RefLawsCore`) is satisfied with THIS quiet, in this start state: `quiet` of that witness is `quietM` -/
theorem heapLaws_with_quietM :
    ∃ L : HeapLaws exSig (fun _ => True), (∀ h, L.quiet h ↔ quietM h) ∧ L.quiet s0 :=
  ⟨HeapLaws.model (fun d => d.getEnv "SPARKLE_DEBUG" = none) (fun _ => True), fun _ => Iff.rfl, quiet_s0⟩

/-- the short program: read the depth, write depth+1, push onto the cache, fetch stderr, write `mref`, read the environment, print a diagnostic, return (depth read, env value) -/
def prog : M exSig (Nat × Option String) :=
  bindM (getM rDepth) fun d =>
  bindM (setM rDepth (d + 1)) fun _ =>
  bindM (getM rCache) fun c =>
  bindM (setM rCache (20 :: c)) fun _ =>
  bindM getStderrM fun _ =>
  bindM (setM rMref 5) fun _ =>
  bindM (getEnvM "HOME") fun e =>
  bindM (eprintlnM "done") fun _ =>
  pureM (d, e)

/-- the run succeeds from `s0` with the returned pair `(0, some "/root")`; the end state has depth 1, cache `[20, 10]`, synthesis ref `some 7`, `mref` = 5, `cref` untouched (0), output `["done"]`, and quiet still holds.  Checked by the kernel (`rfl` / `decide` on closed data). -/
theorem exec_ok :
    ∃ h' : Heap exSig, RunsTo prog s0 (0, some "/root") h' ∧ cv h' = [20, 10] ∧ sv h' = some 7 ∧ dv h' = 1 ∧
      hget rMref h' = 5 ∧ hget rCref h' = 0 ∧ h'.reg.stderr = ["done"] ∧ quietM h' :=
  ⟨endW prog s0, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Tools.ShippingFGCircuitS3n
