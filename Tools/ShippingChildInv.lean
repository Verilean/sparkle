import Tools.ShippingMachineEntry

/-! # The child cache's invariant: definitions and the generic runtime laws

A machine-route parent's children come from `synthesizeChild` (read from
`sparkleChildSynth`), which memoises the real entry in `sparkleChildCache`.
Both are `IO.Ref`s: their contents are opaque in the logic, so what a read
returns is a property of the WORLD the read runs in. The invariant is stated
per world and proved to be kept by the real run — on EVERY outcome, a failing
run included — instead of assuming that every read in every world is sound.

This file holds the definitions; the proofs are in
`Tools/ShippingChildKeeps.lean` (every outcome, the recursion closed by
induction on the synthesis depth) and `Tools/ShippingChildRun.lean` (what a
successful run of the entry gives its closings).

* `RealChild c r` (inductive): `r` is returned by a run of the real entry
  `synthesizeCombinational c` that STARTS in a world satisfying the
  invariant. The induction is the order in which results enter the cache.
* `InvW w` / `StartW w`: the invariant, and the start condition of an entry
  run (the synthesis ref; and depth 0 or the cache invariant), by what reads
  in `w` return.
* Everything about the invariant depends on the two STATE REFERENCES only,
  not on the Meta and Core contexts: those change inside a run
  (`withLocalDecl`, …) and a child may be synthesised under a changed
  context. A `RealChild`'s run is in SOME contexts; the laws and the
  relative conditions are for EVERY context.
* `endW m … w`: the world a run of `m` from `w` ENDS in, whether it returns
  or throws. `Keeps I m`: from a world satisfying `I`, `m` ends in one.
* `RefLaws` — GENERIC runtime laws, a parameter. The three refs' values per
  world (cache, synthesis ref, synthesis depth); what a successful `get` /
  `set` / `modify` of each does; and the FRAME of the listed operations
  (`Framed`: on every outcome they leave the three values). Nothing about the
  compiler's invariant is in them. That a ref operation cannot fail is NOT a
  law: it is proved from the lift's definition (`refGet_runs` …).
* `BodyRel` — PROVED (`bodyRel`, `Tools/ShippingChildBody.lean`), no longer
  part of the boundary: `ChildLaws` is the generic laws alone. It is RELATIVE:
  `synthesizeFromConst` with the entry's own logger keeps the invariant at
  depth `D` on every outcome PROVIDED the memoised child entry does.
  (`LegacyRel`, the same about the legacy translator `Rec.*`, is PROVED —
  `legacyRel`, `Tools/ShippingChildLegacy.lean` — and no longer part of the
  boundary.) Proved around them: the
  machine route's harness (`harnessRel_of`), the translator's fuel induction,
  its step and every ordinary arm (`translateRel_of_legacy`). They do not presuppose that the entry keeps the
  invariant: that is a theorem (`entry_keeps`), by induction on the depth
  (the entry refuses to start at `sparkleSynthDepthLimit`, and every child
  synthesis runs one level deeper). What is inside them and opaque: the fuel
  fallback's `partial` handlers. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab

abbrev Res := Sparkle.IR.AST.Module × Sparkle.IR.AST.Design

/-- The entry's profile logger (`logProf`), as the entry writes it. -/
def profLogIO (profile : Bool) (msg : String) : IO Unit := do
  if profile then
    IO.eprintln msg
    Sparkle.Compiler.flushStderr
    let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
    h.putStrLn msg
    h.flush

/-- The entry's per-synthesis refs other than the three this file tracks. -/
inductive SideRef : {σ : Type} → IO.Ref σ → Prop
  | wireWidth : SideRef sparkleWireWidthCache
  | fvarValue : SideRef sparkleFvarValueMap
  | letWire : SideRef sparkleLetWireCache
  | loopWire : SideRef sparkleLoopWireCache
  | wireCanon : SideRef sparkleWireCanon
  | subModule : SideRef sparkleSubModuleCache
  | subInstOut : SideRef sparkleSubInstanceOutputs
  | singleOut : SideRef sparkleSingleOutInstanceCache
  | typeCache : SideRef sparkleTypeCache
  | typeHits : SideRef sparkleTypeCacheHits
  | typeMiss : SideRef sparkleTypeCacheMiss
  | callCounter : SideRef sparkleCallCounter
  | cacheHits : SideRef sparkleCacheHits
  | hwInferCalls : SideRef sparkleHWInferCalls
  | hwInferMs : SideRef sparkleHWInferMs
  | fvarZetaVisited : SideRef sparkleFvarZetaVisited
  | whnfCalls : SideRef sparkleWhnfCalls
  | inferCalls : SideRef sparkleInferCalls
  | unfoldDefCalls : SideRef sparkleUnfoldDefCalls
  | whnfMs : SideRef sparkleWhnfMs
  | inferMs : SideRef sparkleInferMs
  | unfoldDefMs : SideRef sparkleUnfoldDefMs
  | handlerCalls : SideRef sparkleHandlerCalls
  | handlerMs : SideRef sparkleHandlerMs

/-- The types of the refs a run creates for itself (a translation cache, a
handler's scratch cell): a ref of such a type is not one of the three tracked
refs, whose types are different. -/
inductive LocalRefType : Type → Prop
  | exprCache : LocalRefType (Lean.ExprStructMap String)

/-- What a read of the ref `r` returns in world `w`. -/
def readOf {σ : Type} (r : IO.Ref σ) (w : Void IO.RealWorld) : σ :=
  match (ST.Ref.get r : ST IO.RealWorld σ) w with
  | .mk a _ => a

/-- A `BaseIO` action (it cannot throw) leaves what the three tracked refs
read — from every world. -/
def Inert {α : Type} (x : BaseIO α) : Prop :=
  ∀ w, match x w with
    | .mk _ w' =>
      readOf sparkleChildCache w' = readOf sparkleChildCache w ∧
      readOf sparkleChildSynth w' = readOf sparkleChildSynth w ∧
      readOf sparkleSynthDepth w' = readOf sparkleSynthDepth w

/-- **An environment whose pretty-printers do not touch the tracked refs.** A
lazy message leaf under `withContext ctx` calls the printer functions stored
in `ctx.env` (`ppExt.getState ctx.env`) — the CAPTURED environment's, not the
current world's — which in turn run the delaborators / unexpanders registered
there. Stated by what those printers do: the two entry points a message of
the class reaches (`ppExprWithInfos`, `ppConstNameWithInfos`), in any printing
context over this environment. -/
def OkEnv (env : Environment) : Prop :=
  ∀ ctx : PPContext, ctx.env = env →
    (∀ e : Lean.Expr, Inert (ppExprWithInfos ctx e)) ∧
    (∀ n : Name, Inert (ppConstNameWithInfos ctx n))

/-- **The messages whose rendering the diagnostic law covers.** A message is
a tree; `MessageData.ofLazy` carries CODE (a thunk run when the message is
rendered), so a law "rendering any message leaves the refs" is false of the
runtime. This class has no arbitrary thunk: text, formats (a
`FormatWithInfos` contributes its format only), the structural constructors,
and two lazy leaves — `ofExpr e`, `ofConstName n`. WITHOUT a context a leaf
prints text and calls nothing; under `withContext c` it calls the printers of
`c.env`: so `withContext c` is in the class only for an environment whose
printers are inert (`OkEnv c.env`) — not for every captured context. A naming
context only shortens names. -/
inductive OkMsg : MessageData → Prop
  | str (s : String) : OkMsg (stringToMessageData s)
  | fmt (f : FormatWithInfos) : OkMsg (.ofFormatWithInfos f)
  | compose {a b : MessageData} : OkMsg a → OkMsg b → OkMsg (.compose a b)
  | nest (n : Nat) {a : MessageData} : OkMsg a → OkMsg (.nest n a)
  | group {a : MessageData} : OkMsg a → OkMsg (.group a)
  | tagged (n : Name) {a : MessageData} : OkMsg a → OkMsg (.tagged n a)
  | withContext (c : MessageDataContext) {a : MessageData} :
      OkEnv c.env → OkMsg a → OkMsg (.withContext c a)
  | withNamingContext (c : NamingContext) {a : MessageData} :
      OkMsg a → OkMsg (.withNamingContext c a)
  | ofSyntax (stx : Syntax) {a : MessageData} : OkMsg a → OkMsg (.ofOriginatingSyntax stx a)
  | ofExpr (e : Lean.Expr) : OkMsg (.ofExpr e)
  /- the same kind of lazy leaf: the environment's constant-name printer -/
  | ofConstName (n : Name) (full : Bool) : OkMsg (.ofConstName n full)

/-- An exception whose message is in the class. -/
def OkExc (e : Exception) : Prop := OkMsg e.toMessageData

/-- The content of an exception cell: none, or an exception in the class. -/
def OkOpt (v : Option Exception) : Prop := ∀ ex, v = some ex → OkExc ex

theorem OkOpt.none : OkOpt none := fun _ h => nomatch h

theorem OkOpt.some {e : Exception} (h : OkExc e) : OkOpt (some e) :=
  fun _ h' => by cases h'; exact h

/-- Close `OkMsg m` / `OkExc e` for a message built from text, formats,
printed expressions and the structural constructors. Fails on anything else
(a lazy message of unknown code). -/
macro "okmsg" : tactic => `(tactic|
  (first | (show OkMsg _) | skip
   repeat (first
    | assumption
    | exact OkMsg.str _
    | exact OkMsg.fmt _
    | exact OkMsg.ofExpr _
    | exact OkMsg.ofConstName _ _
    | refine OkMsg.compose ?_ ?_
    | refine OkMsg.nest _ ?_
    | refine OkMsg.group ?_
    | refine OkMsg.tagged _ ?_
    | refine OkMsg.withNamingContext _ ?_
    | refine OkMsg.ofSyntax _ ?_)))

/-- The operations whose frame is a law: reads of the three tracked refs,
any operation on the other per-synthesis refs, the environment-variable read,
the entry's logger (`profLog`: it NAMES the logger, a copy of the entry's closure —
the one constructor about a compiler-specific action), `getConstInfo`, `getEnv`,
building an error; and, for the
harness: a fresh free-variable id, the clock read, and creating or modifying
a translation cache (a ref of ANOTHER type than the three tracked ones). -/
inductive Framed : {α : Type} → MetaM α → Prop
  | cacheGet : Framed (sparkleChildCache.get : MetaM _)
  | synthGet : Framed (sparkleChildSynth.get : MetaM _)
  | depthGet : Framed (ST.Ref.get sparkleSynthDepth : MetaM Nat)
  | sideGet {σ : Type} {r : IO.Ref σ} : SideRef r → Framed (ST.Ref.get r : MetaM σ)
  | sideSet {σ : Type} {r : IO.Ref σ} (v : σ) : SideRef r → Framed (ST.Ref.set r v : MetaM Unit)
  | sideModify {σ : Type} {r : IO.Ref σ} (f : σ → σ) : SideRef r →
      Framed (ST.Ref.modify r f : MetaM Unit)
  | sideModifyGet {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) : SideRef r →
      Framed (ST.Ref.modifyGet r f : MetaM β)
  | sideModifyGetIO {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) : SideRef r →
      Framed (liftM (ST.Ref.modifyGet r f : IO β) : MetaM β)
  /- the same, written as an `IO` action and lifted -/
  | sideGetIO {σ : Type} {r : IO.Ref σ} : SideRef r → Framed (liftM (ST.Ref.get r : IO σ) : MetaM σ)
  | sideSetIO {σ : Type} {r : IO.Ref σ} (v : σ) : SideRef r →
      Framed (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit)
  | sideModifyIO {σ : Type} {r : IO.Ref σ} (f : σ → σ) : SideRef r →
      Framed (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit)
  | ioEnv (n : String) : Framed (liftM (IO.getEnv n) : MetaM _)
  | constInfo (n : Name) : Framed (getConstInfo n : MetaM _)
  | env : Framed (getEnv : MetaM Environment)
  | fvarThrowUnknown {α : Type} (id : FVarId) :
      Framed (liftM (id.throwUnknown : CoreM α) : MetaM α)
  /- Lean's own elaborator primitives (they read and write the Meta and Core
  states, not these refs) -/
  | whnf (e : Lean.Expr) : Framed (Lean.Meta.whnf e)
  | inferType (e : Lean.Expr) : Framed (Lean.Meta.inferType e)
  | isClass? (e : Lean.Expr) : Framed (Lean.Meta.isClass? e)
  | whnfUntil (e : Lean.Expr) (n : Name) : Framed (Lean.Meta.whnfUntil e n)
  | instantiateForall (e : Lean.Expr) (ps : Array Lean.Expr) :
      Framed (Lean.Meta.instantiateForall e ps)
  | mkLambdaFVars (xs : Array Lean.Expr) (e : Lean.Expr) (usedOnly usedLetOnly etaReduce
      generalizeNondepLet : Bool) (bi : BinderInfo) :
      Framed (Lean.Meta.mkLambdaFVars xs e usedOnly usedLetOnly etaReduce generalizeNondepLet bi)
  | mkAppM (c : Name) (xs : Array Lean.Expr) : Framed (Lean.Meta.mkAppM c xs)
  | unfoldDefinition? (e : Lean.Expr) : Framed (Lean.Meta.unfoldDefinition? e)
  | reduce (e : Lean.Expr) (explicitOnly skipTypes skipProofs : Bool) :
      Framed (Lean.Meta.reduce e explicitOnly skipTypes skipProofs)
  | metaGet : Framed (get : MetaM Meta.State)
  | coreModifyTrace (f : TraceState → TraceState) :
      Framed (liftM (modifyTraceState f : CoreM Unit) : MetaM Unit)
  | metaModify (f : Meta.State → Meta.State) : Framed (modify f : MetaM Unit)
  | freshFVar : Framed (mkFreshFVarId : MetaM FVarId)
  | monoMs : Framed (liftM IO.monoMsNow : MetaM Nat)
  | mkExprCache (v : Lean.ExprStructMap String) :
      Framed (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
  | exprCacheGet (r : IO.Ref (Lean.ExprStructMap String)) :
      Framed (ST.Ref.get r : MetaM (Lean.ExprStructMap String))
  | exprCacheGetIO (r : IO.Ref (Lean.ExprStructMap String)) :
      Framed (liftM (ST.Ref.get r : IO (Lean.ExprStructMap String)) : MetaM _)
  /- a ref of a run-local type: created, read, written -/
  | localMk {σ : Type} (v : σ) : LocalRefType σ → Framed (liftM (IO.mkRef v) : MetaM (IO.Ref σ))
  | localGet {σ : Type} (r : IO.Ref σ) : LocalRefType σ → Framed (ST.Ref.get r : MetaM σ)
  | localSet {σ : Type} (r : IO.Ref σ) (v : σ) : LocalRefType σ →
      Framed (ST.Ref.set r v : MetaM Unit)
  | localModify {σ : Type} (r : IO.Ref σ) (f : σ → σ) : LocalRefType σ →
      Framed (ST.Ref.modify r f : MetaM Unit)
  | localGetIO {σ : Type} (r : IO.Ref σ) : LocalRefType σ →
      Framed (liftM (ST.Ref.get r : IO σ) : MetaM σ)
  | localSetIO {σ : Type} (r : IO.Ref σ) (v : σ) : LocalRefType σ →
      Framed (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit)
  | localModifyIO {σ : Type} (r : IO.Ref σ) (f : σ → σ) : LocalRefType σ →
      Framed (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit)
  | exprCacheModify (r : IO.Ref (Lean.ExprStructMap String))
      (f : Lean.ExprStructMap String → Lean.ExprStructMap String) :
      Framed (ST.Ref.modify r f : MetaM Unit)

/-- **The diagnostic operations**: printing an expression, rendering a
message, writing to the process's standard error or to a file handle, the
entry's profile logger. Their ARGUMENTS are data; what they run is the
environment's — registered pretty-printers, the installed standard-error
stream. That they leave the three tracked values is NOT a generic law of ref
operations: it is asked only in worlds the laws call `quiet`
(`RefLaws.diag`). `msgToString` takes a message, which can carry code of its
own: its law is for the class `OkMsg` only. -/
inductive Diag : {α : Type} → MetaM α → Prop
  | profLog (b : Bool) (msg : String) : Diag (liftM (profLogIO b msg) : MetaM Unit)
  | ppExpr (e : Lean.Expr) : Diag (Lean.Meta.ppExpr e)
  | ioEprintln (s : String) : Diag (liftM (IO.eprintln s) : MetaM Unit)
  /- rendering a message OF THE CLASS — not any message -/
  | msgToString (m : MessageData) : OkMsg m → Diag (liftM m.toString : MetaM String)
  | ioGetStderr : Diag (liftM IO.getStderr : MetaM IO.FS.Stream)
  /- the flush of the process's standard error — NOT of an arbitrary stream:
  `IO.FS.Stream` is a structure of closures, and a frame law for `h.flush` of
  any `h` contradicts the cache laws (a stream whose `flush` writes the cache) -/
  | stderrFlush : Diag (liftM Sparkle.Compiler.flushStderr : MetaM Unit)
  | ioHandleMk (p : System.FilePath) (m : IO.FS.Mode) :
      Diag (liftM (IO.FS.Handle.mk p m) : MetaM IO.FS.Handle)
  | ioHandlePutStrLn (h : IO.FS.Handle) (s : String) : Diag (liftM (h.putStrLn s) : MetaM Unit)
  | ioHandleFlush (h : IO.FS.Handle) : Diag (liftM h.flush : MetaM Unit)

/-- Building and throwing an error (any message): the frame is generic. -/
inductive Throws : {α : Type} → MetaM α → Prop
  | err {α : Type} (msg : MessageData) : Throws (throwError msg : MetaM α)
  | coreErr {α : Type} (msg : MessageData) : Throws (liftM (throwError msg : CoreM α) : MetaM α)

/-- An operation the invariant is kept by, AND whose exceptions are in the
class: a generic one, a diagnostic, or a `throwError` of a message in the
class. -/
inductive Op : {α : Type} → MetaM α → Prop
  | framed {α : Type} {p : MetaM α} : Framed p → Op p
  | diag {α : Type} {p : MetaM α} : Diag p → Op p
  | throwErr {α : Type} (msg : MessageData) : OkMsg msg → Op (throwError msg : MetaM α)
  | coreThrowErr {α : Type} (msg : MessageData) :
      OkMsg msg → Op (liftM (throwError msg : CoreM α) : MetaM α)

section Runs
variable (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
  (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)

/-- The world a run of `m` from `w` ends in, whatever its outcome. -/
def endW {α : Type} (m : MetaM α) (w : Void IO.RealWorld) : Void IO.RealWorld :=
  match m mctx mref cctx cref w with
  | .ok _ w' => w'
  | .error _ w' => w'

/-- If `m` throws from `w`, the exception's message is in the class. -/
def ErrOk {α : Type} (m : MetaM α) (w : Void IO.RealWorld) : Prop :=
  match m mctx mref cctx cref w with
  | .ok _ _ => True
  | .error e _ => OkExc e

/-- From a world satisfying `I`, `m` ends in one — returning or throwing —
and an exception it throws has a message in the class (`OkExc`): what a
`catch` hands its handler, and what a failed-and-recovered run leaves in an
exception cell, is tracked. -/
def Keeps {α : Type} (I : Void IO.RealWorld → Prop) (m : MetaM α) : Prop :=
  ∀ w, I w → I (endW mctx mref cctx cref m w) ∧ ErrOk mctx mref cctx cref m w

end Runs

section Defs
/- The invariant depends on the two STATE REFERENCES only. The Meta and Core
contexts (local context, options, …) change inside a run (`withLocalDecl` and
the like), and a child may be synthesised under such a changed context: a
statement tied to the endpoint's own contexts would not survive that. -/
variable (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)

/-- **Generic runtime laws** (a parameter, never proved), for runs over these
state references in EVERY Meta and Core context. The values of the cache, of
the synthesis ref and of the synthesis depth in each world; what a SUCCESSFUL
`get` / `set` / `modify` of each returns or does to the three values; and the
frame of the operations listed in `Framed` — on EVERY outcome they leave the
three values. -/
structure RefLaws where
  val : Void IO.RealWorld → Std.HashMap Name Res
  sval : Void IO.RealWorld → Option (Name → MetaM Res)
  dval : Void IO.RealWorld → Nat
  /-- NOT a law of the runtime: a proof parameter riding in the bundle. An
  auxiliary predicate of the cache's map that the invariant `J` carries, with
  the one closure condition the memoised entry needs (`auxInsert`: a MISS
  inserts under a key the map did not have). Any witness can be given any
  such predicate (`RefLaws.withAux`; `True` costs nothing), so it adds no
  assumption. Used to pin an existing entry through a child's synthesis. -/
  aux : Std.HashMap Name Res → Prop
  auxInsert : ∀ (m0 m1 : Std.HashMap Name Res) (n : Name) (r : Res),
    aux m0 → m0.get? n = none → aux m1 → aux (m1.insert n r)
  /-- The worlds in which the diagnostic operations do not touch the three
  refs: no registered printer and not the installed standard error writes
  them. A condition on the diagnostic ENVIRONMENT only (nothing about other
  heap cells), asked of the run's start world (`ChildBnd`) and carried by the
  invariant. -/
  quiet : Void IO.RealWorld → Prop
  /-- A diagnostic operation, in a quiet world: the three values are left,
  and the world it ends in is quiet — on every outcome. -/
  diag : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Diag p → ∀ w,
    quiet w →
    (val (endW mctx mref cctx cref p w) = val w ∧ sval (endW mctx mref cctx cref p w) = sval w ∧
      dval (endW mctx mref cctx cref p w) = dval w) ∧ quiet (endW mctx mref cctx cref p w)
  /-- Building and throwing an error leaves the values and quietness. -/
  frameT : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Throws p → ∀ w,
    (val (endW mctx mref cctx cref p w) = val w ∧ sval (endW mctx mref cctx cref p w) = sval w ∧
      dval (endW mctx mref cctx cref p w) = dval w) ∧
    (quiet w → quiet (endW mctx mref cctx cref p w))
  /-- TRUSTED (T3): an exception one of these operations throws from a quiet
  world has a message in the class — Lean's own error messages are text,
  formats and lazily printed expressions; a `throwError msg` of a message in
  the class adds only context wrappers. This INCLUDES: the context such an
  error captures (the run's current environment) has inert printers
  (`OkEnv`) — an assumption about the environments the compile runs in, not
  implied by anything about the current world's stderr. -/
  excOk : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Op p →
    ∀ w e w', quiet w → p mctx mref cctx cref w = .error e w' → OkExc e
  /-- The generic operations and the tracked refs' writes do not make a
  quiet world unquiet (the compile registers no printer and does not replace
  standard error). -/
  frameQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Framed p → ∀ w,
    quiet w → quiet (endW mctx mref cctx cref p w)
  cacheSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → quiet w → quiet w'
  cacheModifyQ : ∀ {mctx : Meta.Context} {cctx : Core.Context}
    (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → quiet w → quiet w'
  depthSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    quiet w → quiet w'
  depthModifyQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} (f : Nat → Nat) w u w',
    RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w' →
    quiet w → quiet w'
  frame : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type} (p : MetaM α), Framed p → ∀ w,
    val (endW mctx mref cctx cref p w) = val w ∧ sval (endW mctx mref cctx cref p w) = sval w ∧
      dval (endW mctx mref cctx cref p w) = dval w
  cacheGet : ∀ {mctx : Meta.Context} {cctx : Core.Context} w m w',
    RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w' → m = val w
  cacheSet : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = v ∧ sval w' = sval w ∧ dval w' = dval w
  cacheModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}
    (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = f (val w) ∧ sval w' = sval w ∧ dval w' = dval w
  synthGet : ∀ {mctx : Meta.Context} {cctx : Core.Context} w s w',
    RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w' → s = sval w
  depthGet : ∀ {mctx : Meta.Context} {cctx : Core.Context} w d w',
    RunsTo (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref w d w' → d = dval w
  depthSet : ∀ {mctx : Meta.Context} {cctx : Core.Context} v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = val w ∧ sval w' = sval w ∧ dval w' = v
  depthModify : ∀ {mctx : Meta.Context} {cctx : Core.Context} (f : Nat → Nat) w u w',
    RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = val w ∧ sval w' = sval w ∧ dval w' = f (dval w)
  /- Lean's continuation-passing combinators: the combinator itself leaves the
  three values, and runs its continuation — possibly in other Meta and Core
  contexts. For every predicate `I` of the three values. -/
  telescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop),
    (∀ w w', val w' = val w → sval w' = sval w → dval w' = dval w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b,
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
  lamTelescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop),
    (∀ w w', val w' = val w → sval w' = sval w → dval w' = dval w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b,
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup)
  localDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop),
    (∀ w w', val w' = val w → sval w' = sval w → dval w' = dval w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)
  letDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop),
    (∀ w w', val w' = val w → sval w' = sval w → dval w' = dval w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)

/-- In world `w`, a read of the synthesis ref returns `synthesizeChild`. -/
def SynthAt (w : Void IO.RealWorld) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) s w1,
    RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w1 → s = some synthesizeChild

/-- `r` is returned by a run of the real entry on `c` — in SOME Meta and Core
contexts, over these state references — starting in a world where the
cache's entries are `RealChild` and the synthesis ref reads
`synthesizeChild`. -/
inductive RealChild : Name → Res → Prop
  | run {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld)
      (cache : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) m w1,
        RunsTo (sparkleChildCache.get : MetaM _) mctx' mref cctx' cref w m w1 →
        ∀ c' r', m.get? c' = some r' → RealChild c' r')
      (synth : SynthAt mref cref w)
      (quiet : ∃ L : RefLaws mref cref, L.quiet w)
      (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChild c r

/-- Every entry of the map is a `RealChild`. -/
def CacheInv (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → RealChild mref cref c r

/-- The cache's entries read in `w` are `RealChild`s. -/
def CacheAt (w : Void IO.RealWorld) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) m w1,
    RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1 → CacheInv mref cref m

/-- `w` is a quiet world of SOME law witness. -/
def QuietAt (w : Void IO.RealWorld) : Prop :=
  ∃ L : RefLaws mref cref, L.quiet w

/-- The invariant in world `w`, by what reads in `w` return — and `w` is a
quiet world of a law witness (the laws used from `w` on are that witness's:
`invV_of_invW`). -/
def InvW (w : Void IO.RealWorld) : Prop :=
  CacheAt mref cref w ∧ SynthAt mref cref w ∧ QuietAt mref cref w

/-- **The start condition of an entry run** in world `w`: the synthesis ref
reads `synthesizeChild`, and EITHER the synthesis depth reads 0 (an outermost
run: the entry clears the cache, whatever it holds) OR the cache's entries
are `RealChild`s (a nested run inherits the invariant). -/
def StartW (w : Void IO.RealWorld) : Prop :=
  SynthAt mref cref w ∧
    ((∀ (mctx : Meta.Context) (cctx : Core.Context) d w1,
        RunsTo (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref w d w1 → d = 0) ∨
     CacheAt mref cref w)

/-- The children of a shape's calls, call by call: the built memory module
for a memory call, a `RealChild` of the call's declaration otherwise. -/
def ChildrenReal (shape : MachineShape) (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    (Sparkle.Compiler.MachMemory.memChild? (shape.insts[k]).1 = some y ∨
      RealChild mref cref (shape.insts[k]).1 y)

end Defs

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The invariant by the values (the laws' view). -/
def InvV (L : RefLaws mref cref) (w : Void IO.RealWorld) : Prop :=
  CacheInv mref cref (L.val w) ∧ L.sval w = some synthesizeChild ∧ L.quiet w

/-- The start condition by the values. -/
def StartV (L : RefLaws mref cref) (w : Void IO.RealWorld) : Prop :=
  L.sval w = some synthesizeChild ∧ (L.dval w = 0 ∨ CacheInv mref cref (L.val w))

/-- The invariant at synthesis depth `D` (with the witness's auxiliary
predicate of the cache's map). -/
def J (L : RefLaws mref cref) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  InvV L w ∧ L.dval w = D ∧ L.aux (L.val w)

/-- The same laws with another auxiliary predicate. -/
def RefLaws.withAux (L : RefLaws mref cref) (A : Std.HashMap Name Res → Prop)
    (hA : ∀ (m0 m1 : Std.HashMap Name Res) (n : Name) (r : Res),
      A m0 → m0.get? n = none → A m1 → A (m1.insert n r)) : RefLaws mref cref :=
  { L with aux := A, auxInsert := hA }

/-- The trivial auxiliary predicate. -/
def RefLaws.plain (L : RefLaws mref cref) : RefLaws mref cref :=
  L.withAux (fun _ => True) (fun _ _ _ _ _ _ _ => trivial)

/-- A `CompilerM` action keeps `I`, from every compiler and circuit state. -/
def KeepsC (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) {α : Type} (I : Void IO.RealWorld → Prop)
    (c : CompilerM α) : Prop :=
  ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState),
    Keeps mctx mref cctx cref I (c ctx st)

/-- The memoised child entry keeps the invariant at depth `D`, on every
outcome, in every Meta and Core context. -/
def ChildKeeps (L : RefLaws mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) c,
    Keeps mctx mref cctx cref (J L D) (synthesizeChild c)

/-- **The body, relative to the child entry** (PROVED: `bodyRel`,
`Tools/ShippingChildBody.lean`; not part of `ChildLaws`): at any depth, IF
the memoised child entry keeps the invariant there, a run of
`synthesizeFromConst` with the entry's own logger keeps it — on every
outcome, in every Meta and Core context. -/
def BodyRel (L : RefLaws mref cref) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ D, ChildKeeps L D → ∀ (mctx : Meta.Context) (cctx : Core.Context) (b : Bool) declName ci isInst,
    Keeps mctx mref cctx cref (J L D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst)

/-- **The legacy translator, relative to the child entry and to its
recursive argument** (PROVED: `legacyRel`, `Tools/ShippingChildLegacy.lean`;
not part of `ChildLaws`): at any depth, in any contexts, IF the
memoised child entry keeps the invariant and the translator handed in as
`rec` does (in every context: the handlers call it under changed ones), the
two entry points of the block `Rec.*` keep it — on
every outcome, from every compiler state. -/
def LegacyRel (L : RefLaws mref cref) : Prop :=
  ∀ D, ChildKeeps L D → ∀ (rec : TranslateFn),
    (∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (rec e hint top named)) →
    ∀ (mctx : Meta.Context) (cctx : Core.Context),
    (∀ e hint top named, KeepsC mctx mref cctx cref (J L D)
      (Rec.translateExprToWireCached (fun e h t n => rec e h t n) e hint top named)) ∧
    (∀ e hint top named, KeepsC mctx mref cctx cref (J L D)
      (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e hint top named))

/-- The translator, relative to the child entry: at any depth, IF the
memoised child entry keeps the invariant there, a run of the translator
`translateExprToWire` keeps it — on every outcome, from every compiler state,
in every Meta and Core context. PROVED (`translateRel`,
`Tools/ShippingChildLegacy.lean`). -/
def TranslateRel (L : RefLaws mref cref) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ D, ChildKeeps L D → ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
    KeepsC mctx mref cctx cref (J L D) (translateExprToWire tenv e hint top named)

/-- The machine route's harness, relative to the child entry: the same for
`synthesizeMixedCertified` with the entry's own logger. PROVED from
`TranslateRel` (`harnessRel_of`, `Tools/ShippingChildHarness.lean`). -/
def HarnessRel (L : RefLaws mref cref) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ D, ChildKeeps L D → ∀ (mctx : Meta.Context) (cctx : Core.Context) (b : Bool) declName bs body,
    Keeps mctx mref cctx cref (J L D)
      (synthesizeMixedCertified (fun e hint top named => translateExprToWire tenv e hint top named)
        (profLogIO b) declName bs body)

section Bnd
variable (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)

/-- The context-level part of the child boundary: the GENERIC laws of the
three refs and of Lean's primitives (`RefLaws`) — nothing about the compiler.
Both compiler-specific conditions that used to stand here are proved under
them (`bodyRel`, `legacyRel`). The world-level part is `StartW` at the run's
start. -/
def ChildLaws : Prop :=
  Nonempty (RefLaws mref cref)

/-- **The child boundary of a run starting in `w`**: ONE law witness `L`
with the start condition by `L`'s values and `w` quiet for `L`. The laws and
the world are tied: the witness whose diagnostic law is used is the one the
start world is quiet for. -/
def ChildBnd (w : Void IO.RealWorld) : Prop :=
  ∃ L : RefLaws mref cref, StartV L w ∧ L.quiet w

end Bnd

/-! ## Runs and end worlds -/

theorem endW_of_runs {α : Type} {m : MetaM α} {w a w'}
    (h : RunsTo m mctx mref cctx cref w a w') : endW mctx mref cctx cref m w = w' := by
  unfold RunsTo at h; unfold endW; rw [h]

theorem endW_of_error {α : Type} {m : MetaM α} {w e w'}
    (h : m mctx mref cctx cref w = .error e w') : endW mctx mref cctx cref m w = w' := by
  unfold endW; rw [h]

/-- A ref read cannot fail (the lift of an `ST` action returns). -/
theorem refGet_runs {σ : Type} (r : IO.Ref σ) (w : Void IO.RealWorld) :
    ∃ a w', RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w a w' := by
  unfold RunsTo
  cases h : (ST.Ref.get r : ST IO.RealWorld σ) w with
  | mk a w' =>
    refine ⟨a, w', ?_⟩
    change (match (ST.Ref.get r : ST IO.RealWorld σ) w with | .mk a s => EST.Out.ok a s) = _
    rw [h]

theorem refSet_runs {σ : Type} (r : IO.Ref σ) (v : σ) (w : Void IO.RealWorld) :
    ∃ a w', RunsTo (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref w a w' := by
  unfold RunsTo
  cases h : (ST.Ref.set r v : ST IO.RealWorld Unit) w with
  | mk a w' =>
    refine ⟨a, w', ?_⟩
    change (match (ST.Ref.set r v : ST IO.RealWorld Unit) w with | .mk a s => EST.Out.ok a s) = _
    rw [h]

theorem refModify_runs {σ : Type} (r : IO.Ref σ) (f : σ → σ) (w : Void IO.RealWorld) :
    ∃ a w', RunsTo (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref w a w' := by
  unfold RunsTo
  cases h : (ST.Ref.modify r f : ST IO.RealWorld Unit) w with
  | mk a w' =>
    refine ⟨a, w', ?_⟩
    change (match (ST.Ref.modify r f : ST IO.RealWorld Unit) w with | .mk a s => EST.Out.ok a s) = _
    rw [h]

/-- A run that returns does not throw. -/
theorem not_error_of_runs {α : Type} {m : MetaM α} {w a w1 e w2}
    (h : RunsTo m mctx mref cctx cref w a w1) (hf : m mctx mref cctx cref w = .error e w2) :
    False := by
  unfold RunsTo at h; rw [h] at hf; cases hf

/-- A ref read does not depend on the Meta and Core contexts or state refs. -/
theorem refGet_ctx {σ : Type} (r : IO.Ref σ) {mctx' : Meta.Context}
    {mref' : ST.Ref IO.RealWorld Meta.State} {cctx' : Core.Context}
    {cref' : ST.Ref IO.RealWorld Core.State} {w a w'}
    (h : RunsTo (ST.Ref.get r : MetaM σ) mctx mref cctx cref w a w') :
    RunsTo (ST.Ref.get r : MetaM σ) mctx' mref' cctx' cref' w a w' := h

/-! ## The laws on a successful run -/

namespace RefLaws
variable (L : RefLaws mref cref)

/-- A framed operation's successful run leaves the three values. -/
theorem same {α : Type} {p : MetaM α} (hp : Framed p) {w a w'}
    (h : RunsTo p mctx mref cctx cref w a w') :
    L.val w' = L.val w ∧ L.sval w' = L.sval w ∧ L.dval w' = L.dval w := by
  have := L.frame (mctx := mctx) (cctx := cctx) p hp w
  rwa [endW_of_runs h] at this

/-- A generic operation's successful run stays quiet. -/
theorem sameQ {α : Type} {p : MetaM α} (hp : Framed p) {w a w'}
    (h : RunsTo p mctx mref cctx cref w a w') (hq : L.quiet w) : L.quiet w' := by
  have := L.frameQ (mctx := mctx) (cctx := cctx) p hp w hq
  rwa [endW_of_runs h] at this

/-- A diagnostic operation's successful run from a quiet world. -/
theorem sameD {α : Type} {p : MetaM α} (hp : Diag p) {w a w'}
    (h : RunsTo p mctx mref cctx cref w a w') (hq : L.quiet w) :
    (L.val w' = L.val w ∧ L.sval w' = L.sval w ∧ L.dval w' = L.dval w) ∧ L.quiet w' := by
  have := L.diag (mctx := mctx) (cctx := cctx) p hp w hq
  rwa [endW_of_runs h] at this

/-- An operation's successful run from a quiet world: the values, and quiet. -/
theorem sameOp {α : Type} {p : MetaM α} (hp : Op p) {w a w'}
    (h : RunsTo p mctx mref cctx cref w a w') (hq : L.quiet w) :
    (L.val w' = L.val w ∧ L.sval w' = L.sval w ∧ L.dval w' = L.dval w) ∧ L.quiet w' := by
  cases hp with
  | framed hf => exact ⟨L.same hf h, L.sameQ hf h hq⟩
  | diag hd => exact L.sameD hd h hq
  | throwErr msg _ =>
    have := L.frameT (mctx := mctx) (cctx := cctx) _ (Throws.err (α := α) msg) w
    rw [endW_of_runs h] at this
    exact ⟨this.1, this.2 hq⟩
  | coreThrowErr msg _ =>
    have := L.frameT (mctx := mctx) (cctx := cctx) _ (Throws.coreErr (α := α) msg) w
    rw [endW_of_runs h] at this
    exact ⟨this.1, this.2 hq⟩


theorem get {w m w'} (h : RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w') :
    m = L.val w ∧ L.val w' = L.val w ∧ L.sval w' = L.sval w :=
  ⟨L.cacheGet _ _ _ h, (L.same .cacheGet h).1, (L.same .cacheGet h).2.1⟩

end RefLaws

/-! ## The invariant by the values -/

theorem invW_of_invV (L : RefLaws mref cref) {w} (h : InvV L w) : InvW mref cref w := by
  refine ⟨fun mctx cctx m w1 hg => ?_, fun mctx cctx s w1 hs => ?_, L, h.2.2⟩
  · rw [L.cacheGet _ _ _ hg]; exact h.1
  · rw [L.synthGet _ _ _ hs]; exact h.2.1

/-- The invariant by the values of the witness `w` is quiet for. (The
contexts only serve to run a read; any will do.) -/
theorem invV_of_invW (mctx : Meta.Context) (cctx : Core.Context) {w}
    (h : InvW mref cref w) : ∃ L : RefLaws mref cref, InvV L w := by
  obtain ⟨hc, hsy, L, hq⟩ := h
  obtain ⟨m, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleChildCache w
  obtain ⟨s, w2, hs⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleChildSynth w
  refine ⟨L, ?_, ?_, hq⟩
  · have := hc mctx cctx m w1 hg; rwa [L.cacheGet _ _ _ hg] at this
  · have := hsy mctx cctx s w2 hs; rwa [L.synthGet _ _ _ hs] at this

theorem startV_of_invV (L : RefLaws mref cref) {w} (h : InvV L w) : StartV L w :=
  ⟨h.2.1, Or.inr h.1⟩

/-- An invariant world is a start world of the boundary, for the witness it
is quiet for. -/
theorem ChildBnd.of_invW (mctx : Meta.Context) (cctx : Core.Context) {w}
    (h : InvW mref cref w) : ChildBnd mref cref w := by
  obtain ⟨L, hv⟩ := invV_of_invW mctx cctx h
  exact ⟨L, startV_of_invV L hv, hv.2.2⟩

theorem cacheInv_empty : CacheInv mref cref {} := by
  intro c r h; simp at h

theorem cacheInv_insert {m : Std.HashMap Name Res} {c : Name} {r : Res}
    (h : CacheInv mref cref m) (hr : RealChild mref cref c r) :
    CacheInv mref cref (m.insert c r) := by
  intro c' r' h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i heq
    have : c = c' := by simpa using heq
    subst this
    cases h'
    exact hr
  · exact h c' r' h'

/-- A run of the real entry from an invariant world is a `RealChild`. -/
theorem RealChild.of_inv {c : Name} {r : Res} {w w' : Void IO.RealWorld}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') :
    RealChild mref cref c r :=
  RealChild.run mctx cctx w w' (fun mctx' cctx' m w1 h => hw.1 mctx' cctx' m w1 h) hw.2.1 hw.2.2 hr

/-- A `RealChild`'s run — in some Meta and Core contexts — with the
invariant at its start. -/
theorem RealChild.inv {c : Name} {r : Res} (h : RealChild mref cref c r) :
    ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld),
      InvW mref cref w ∧ RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' := by
  cases h with
  | run mctx cctx w w' cache synth quiet hr =>
    exact ⟨mctx, cctx, w, w', ⟨fun mctx' cctx' m w1 h => cache mctx' cctx' m w1 h, synth, quiet⟩, hr⟩

/-- **The contexts a child is synthesised in**: `c`'s entry has a successful
run in the Meta and Core contexts `mctx`, `cctx` (over these state
references) starting in a world satisfying the invariant. Defined by the
runs of the entry — not by what one wants of the contexts — and every
`RealChild` of `c` gives one (`RealChild.ranIn`): the child-side premises of
the composed endpoints are asked in these contexts only. -/
def ChildRanIn (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (c : Name) (mctx : Meta.Context) (cctx : Core.Context) : Prop :=
  ∃ (w : Void IO.RealWorld) (r : Res) (w' : Void IO.RealWorld),
    InvW mref cref w ∧ RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w'

theorem ChildRanIn.of_run {c : Name} {r : Res} {w w' : Void IO.RealWorld}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') :
    ChildRanIn mref cref c mctx cctx := ⟨w, r, w', hw, hr⟩

/-- A `RealChild`'s run, with the contexts it ran in. -/
theorem RealChild.ranIn {c : Name} {r : Res} (h : RealChild mref cref c r) :
    ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld),
      ChildRanIn mref cref c mctx cctx ∧ InvW mref cref w ∧
        RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' := by
  obtain ⟨mctx, cctx, w, w', hw, hr⟩ := h.inv
  exact ⟨mctx, cctx, w, w', ⟨w, r, w', hw, hr⟩, hw, hr⟩

/-- A `RealChild`'s run: it starts in a world where the boundary holds. -/
theorem RealChild.bnd {c : Name} {r : Res} (h : RealChild mref cref c r) :
    ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld),
      ChildBnd mref cref w ∧ RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' := by
  obtain ⟨mctx, cctx, w, w', hw, hr⟩ := h.inv
  exact ⟨mctx, cctx, w, w', ChildBnd.of_invW mctx cctx hw, hr⟩

theorem ChildBnd.laws {w : Void IO.RealWorld} (h : ChildBnd mref cref w) :
    ChildLaws mref cref := ⟨h.choose⟩

theorem RunsTo.pure_world {α : Type} {a b : α} {w w' : Void IO.RealWorld}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') : b = a ∧ w' = w := by
  unfold RunsTo at h
  change EST.Out.ok a w = _ at h
  cases h; exact ⟨rfl, rfl⟩

end Tools.ShippingChildInv
