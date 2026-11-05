import Tools.ShippingGen5Cover3
import Tools.ShippingMachineAuto
set_option autoImplicit false
-- Built in g5cv-r9 at d75f5b18 (Pod `kjob lake build Tools.ShippingGen5Cover4`, exit 0). Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # DG-COVER rev5 unit U-E1: `hb` / `hv` of `rowC_of_reader` from `MachineData.ok`

`bpos_lt_of_ok` / `vpos_lt_of_ok` read the `kb` / `kv` rows (16, 17) of `MachineData.ok`; `rowC_of_reader_ok` is `rowC_of_reader` with `hb`/`hv` replaced by
the premise `d.ok = true`. `d.ok = true`, `ShapeAgree`, `FullInv`, `LetQuoteEq`, `LetsNoLoose` stay premises: not supplied here.
Not supplied: any run, `dataOf`, R-trace/R-in/R-nl/R-dom/B3, real reader connection, `ShapeFuelBridge`, M5, FG. -/

namespace Tools.ShippingGen5Cover4
open Lean Sparkle.Compiler.Elab Tools.ShippingMachineAuto Tools.ShippingGen5Cover3 Tools.ShippingGen5Sem

/-- Row 16 of `MachineData.ok`. -/
theorem ok_row_kb {d : MachineData} (hok : d.ok = true) :
    ∀ j, j < d.kb → d.K (d.bpos j) = some .bool ∧ d.bpos j < d.nIn + d.ss.length + d.ls.length := by
  unfold MachineData.ok at hok
  simp only [Bool.and_eq_true] at hok
  exact of_decide_eq_true hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Row 17 of `MachineData.ok`. -/
theorem ok_row_kv {d : MachineData} (hok : d.ok = true) :
    ∀ j, j < d.kv → d.K (d.vpos j) = some (.bits (d.vw j)) ∧ d.vpos j < d.nIn + d.ss.length + d.ls.length := by
  unfold MachineData.ok at hok
  simp only [Bool.and_eq_true] at hok
  exact of_decide_eq_true hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- O10: every Bool-binder position of `d` is below the total binder count of `rowC_of_reader`'s `hb`; `hpos` covers `j ≥ d.kb` where `bpos j` is the default `0`. -/
theorem bpos_lt_of_ok {d : MachineData} (hok : d.ok = true) (hpos : 0 < d.nIn + d.ss.length + d.ls.length) :
    ∀ j, d.bpos j < d.nIn + d.ss.length + d.ls.length := by
  intro j
  by_cases hj : j < d.kb
  · exact (ok_row_kb hok j hj).2
  · have h0 : d.bpos j = 0 := by
      unfold MachineData.bpos
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by unfold MachineData.kb at hj; omega)]
      rfl
    omega

/-- O11, for the BitVec positions. -/
theorem vpos_lt_of_ok {d : MachineData} (hok : d.ok = true) (hpos : 0 < d.nIn + d.ss.length + d.ls.length) :
    ∀ j, d.vpos j < d.nIn + d.ss.length + d.ls.length := by
  intro j
  by_cases hj : j < d.kv
  · exact (ok_row_kv hok j hj).2
  · have h0 : d.vpos j = 0 := by
      unfold MachineData.vpos
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by unfold MachineData.kv at hj; omega)]
      rfl
    omega

/-- `rowC_of_reader` with `hb`/`hv` discharged from `d.ok`: when the total is `0`, `ShapeAgree.nIn` gives `d.shape.insts.length = 0`, so the statement is vacuous. -/
theorem rowC_of_reader_ok {d : MachineData} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv (kDOf d) st)
    (hq : LetQuoteEq d st) (hnl : LetsNoLoose st) (hok : d.ok = true) :
    ∀ k, k < d.shape.insts.length → ∀ l ∈ callArgs d k, (cleanLets d k)[l]? = some true := by
  intro k hk
  by_cases h0 : d.nIn + d.ss.length + d.ls.length = 0
  · have := hag.nIn
    exfalso
    omega
  · exact rowC_of_reader hag hi hq hnl (bpos_lt_of_ok hok (Nat.pos_of_ne_zero h0))
      (vpos_lt_of_ok hok (Nat.pos_of_ne_zero h0)) k hk

end Tools.ShippingGen5Cover4
