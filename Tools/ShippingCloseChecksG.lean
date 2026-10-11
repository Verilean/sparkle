import Tools.ShippingCloseChecks
import Tools.ShippingTopoLinkedG
import Tools.ShippingRankG
import Sparkle.IR.MachineInstG

/-! # The reordering and the checks of `closeInstsG`, from facts about the body

`closeInstsG`'s checks (`closeChecksG`: `closeInsts`'s without the
combinational-children check, with distinct instance names, no instance
feeding itself and a memory child found as itself) hold of `topoBody`'s
result, given facts about the closed module's body `mb` and the instance
statements `stmts` that do not mention the reordered body. An instance may
drive several wires and be connected to wires no assignment drives that are
no outputs of its child (`clk`, `rst`): the linked order is
`linkedOk_ordered_G`'s. Pure. -/
namespace Tools.ShippingCloseChecksG
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingTopoBody Tools.ShippingTopoChecks Tools.ShippingTopoLinked
open Tools.ShippingCloseInstsSome Tools.ShippingCloseChecks Tools.ShippingTopoLinkedG

/-- The checks of `closeInstsG` (its `if`). -/
def closeChecksG (portNames : List String) (children : List (Module × Design)) (mname : String)
    (d' : Design) (stmts body0 body : List Stmt) : Bool :=
  stmts.all isInst && decide portNames.Nodup && woCheck [] body0 &&
    woCheck [] body && isPermOf body0 body &&
    decide (seqOf body0 = seqOf body) &&
    decide (nextKeys body0).Nodup &&
    decide (body0.filterMap stmtMemName).Nodup &&
    linkedOk (moduleByName d'.modules) body &&
    decide (body.filterMap instNameOf).Nodup && noSelfFeed (moduleByName d'.modules) body &&
    children.all (fun c => Sparkle.Compiler.MachMemory.memSelf (moduleByName d'.modules) c.1) &&
    children.all (fun c => decide (moduleByName d'.modules c.1.name = some c.1) &&
      c.2.modules.all (fun m => decide (moduleByName d'.modules m.name = some m))) &&
    noInstOfB mname body && d'.modules.all (fun g => noInstOfB mname g.body)

/-- **`closeInstsG` returns a module when its steps succeed.** -/
theorem closeInstsG_some_of {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String} {children : List (Module × Design)} {m0 : Module} {d : Design}
    {stmts : List Stmt} {outWs : List String} {body : List Stmt}
    (hst : stmtsG nIn kI n portNames insts fields children (withClockFor children m0)
      (designWith children d) = some stmts)
    (hout : (List.range insts.length).mapM (fun k => portNames[nIn + k]?) = some outWs)
    (htopo : topoBody (m0.body ++ stmts) = some body)
    (hchk : closeChecksG portNames children m0.name (designWith children d) stmts
      (m0.body ++ stmts) body = true) :
    (closeInstsG nIn kI n portNames insts fields children (m0, d)).isSome = true := by
  unfold closeChecksG at hchk
  unfold closeInstsG
  simp only [Option.bind_eq_bind, hst, hout, Option.bind_some, (withClockFor_same children m0).2.2.2,
    htopo, hchk, if_true]
  rfl

/-- **`topoBody` succeeds and the checks of `closeInstsG` hold**, from facts
about the closed body `mb` and the instance statements `stmts`. -/
theorem closeChecksG_of {portNames : List String} {children : List (Module × Design)}
    {mname : String} {d' : Design} {mb stmts : List Stmt}
    (hinst : stmts.all isInst = true) (hpn : portNames.Nodup)
    (hwo : woCheck [] mb = true)
    (rank : Stmt → Nat)
    (hrank : ∀ st ∈ combOf (mb ++ stmts), ∀ r ∈ combReads (byAssignOf (mb ++ stmts)) st,
      r ∈ drivenOf (mb ++ stmts) →
      ∃ st' ∈ combOf (mb ++ stmts), r ∈ combWrites (byAssignOf (mb ++ stmts)) st' ∧
        rank st' < rank st)
    (hreg : ∀ st ∈ othersOf (mb ++ stmts), isReg st = true)
    (hwn : (writesOf (combOf (mb ++ stmts))).Nodup)
    (hkeys : (nextKeys mb).Nodup)
    (hlw : (bodyWrites (moduleByName d'.modules) (combOf (mb ++ stmts))).Nodup)
    (hlD : ∀ n ∈ bodyWrites (moduleByName d'.modules) (combOf (mb ++ stmts)),
      n ∈ drivenOf (mb ++ stmts))
    (hagree : ∀ mn i conns, Stmt.inst mn i conns ∈ mb ++ stmts →
      ∃ child, moduleByName d'.modules mn = some child ∧
        (∀ w ∈ instOuts child.outputs conns,
          w ∈ combWrites (byAssignOf (mb ++ stmts)) (.inst mn i conns)) ∧
        (∀ w ∈ combWrites (byAssignOf (mb ++ stmts)) (.inst mn i conns),
          w ∉ instOuts child.outputs conns →
          w ∉ bodyWrites (moduleByName d'.modules) (combOf (mb ++ stmts))) ∧
        ∀ c ∈ conns, ∃ w, c.2 = Expr.ref w)
    (hinames : ((mb ++ stmts).filterMap instNameOf).Nodup)
    (hself : noSelfFeed (moduleByName d'.modules) (mb ++ stmts) = true)
    (hmem : children.all (fun c =>
      Sparkle.Compiler.MachMemory.memSelf (moduleByName d'.modules) c.1) = true)
    (hnames : children.all (fun c => decide (moduleByName d'.modules c.1.name = some c.1) &&
      c.2.modules.all (fun g => decide (moduleByName d'.modules g.name = some g))) = true)
    (hno : noInstOfB mname (mb ++ stmts) = true)
    (hnoD : d'.modules.all (fun g => noInstOfB mname g.body) = true) :
    ∃ body, topoBody (mb ++ stmts) = some body ∧
      closeChecksG portNames children mname d' stmts (mb ++ stmts) body = true := by
  obtain ⟨sorted, htopo, hperm, hord⟩ := topoBody_some_rank rank hrank
  refine ⟨_, htopo, ?_⟩
  have hcs : ∀ st ∈ sorted, isComb st = true := by
    intro st hs
    have := hperm.subset hs
    rw [combOf_eq] at this
    exact (List.mem_filter.mp this).2
  have hAD : ∀ n, n ∈ byAssignOf (mb ++ stmts) → n ∈ drivenOf (mb ++ stmts) :=
    fun n h => List.mem_append_left _ h
  have hbperm : (mb ++ stmts).Perm (sorted ++ othersOf (mb ++ stmts)) :=
    (perm_split _).trans (hperm.symm.append_right _)
  have hwperm : (writesOf sorted).Perm (writesOf (combOf (mb ++ stmts))) :=
    hperm.flatMap_right _
  unfold closeChecksG
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hinst, hpn⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hmem⟩, hnames⟩, ?_⟩,
    hnoD⟩
  · exact woCheck_append_insts stmts hinst mb [] hwo
  · exact woCheck_ordered _ _ hAD _ hreg sorted [] [] hcs hord (hwperm.nodup_iff.mpr hwn)
      (fun n hn => hwperm.subset hn) (fun n hn => by simp at hn) (fun n hn => by simp at hn)
  · exact isPermOf_complete hbperm
  · exact seqOf_sorted hperm
  · rw [nextKeys_append_insts mb stmts hinst]
    exact hkeys
  · rw [noMem_of hreg]
    exact List.nodup_nil
  · refine linkedOk_ordered_G _ _ _ hAD _ hreg sorted sorted [] (fun _ h => h) hcs hord
      ((bodyWrites_perm _ hperm).nodup_iff.mpr hlw)
      (fun n hn => hlD n ((bodyWrites_perm _ hperm).subset hn)) (fun n hn => by simp at hn) ?_
      (fun _ h => h)
    intro mn i conns hm
    have := hperm.subset hm
    rw [combOf_eq] at this
    obtain ⟨child, h1, h2, h3, h4⟩ := hagree mn i conns (List.mem_filter.mp this).1
    exact ⟨child, h1, h2,
      fun w hw hn hb => h3 w hw hn ((bodyWrites_perm _ hperm).subset hb), h4⟩
  · exact (hbperm.filterMap instNameOf).nodup_iff.mp hinames
  · unfold noSelfFeed at hself ⊢
    rw [List.all_eq_true] at hself ⊢
    exact fun st hs => hself st (hbperm.symm.subset hs)
  · unfold noInstOfB at hno ⊢
    rw [List.all_eq_true] at hno ⊢
    exact fun st hs => hno st (hbperm.symm.subset hs)

end Tools.ShippingCloseChecksG
