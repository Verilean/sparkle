# B.F-4 `hS` → B.G-9 `hQ` の橋: scratch elaborate 結果（文書のみ）

対象: base b5a4c681（par/fb-hsq）。Lean ソースツリーは編集していない。scratch は Pod の scratchpad（ソースツリー外）に置き、`kjob lake env lean` で elaborate した。必要な target（`Tools.ShippingGen4FbFragRun` 705 jobs、`Tools.ShippingGen4FirstLeafR` 709 jobs）だけ `kjob lake build` した（どちらも exit 0）。これは clean build ではない。

## 1. 結果（要約）
- **通った**。`hS` を仮説に持たず、追加の仮説なしで、FB-22 の結論（`ChildRunN … b (firstBs …) [out] S`）が `S := f.ifaceOf.S i` で出る。橋は `RealChildA O f.decl y` を `cases` して得る実 run `hr`（`RunsTo (synthesizeCombinational c) … r w'`、`r = y`）をそのまま FB-22 の `hr` に渡すだけで、`y.1` と FB-22 の post-processed `b` は同じ run の同じ結果（`r` の第 1 成分）。別の同一性補題は要らなかった。
- 要った仮説は `RealChildA O f.decl y`（`firstLeaf_childShips` が既に持つもの）と `EntryDefines`（`FirstLeaf` の `entry`）。FB-22 に無かった `adm/cache/synth/quiet` は `RealChildA` の constructor の中身で、`cases` で取り出して捨てる（使わない）。**新しい仮説は無い**。
- `hS` の内容は `gateS_get0`（既存）+ `rfl` で払える（`hS_ifaceOf`）。公理は `propext, Quot.sound` のみ。
- sorry: なし（最終 scratch）。途中で試した「`hr` だけから `ChildShipsI` を出す」補題は未証明の骨組み（`sorry`）のまま捨てた。結果には含めない。`RealChildA` を経由する橋は完成している。
- 追加の前提（`hQ` 以外の行）は増えない。台帳側: B.F-4 の `hS` は `hQ : Q f.decl = some f.ifaceOf`（B.G-9、既存行）に付け替わる。

## 2. `#print axioms`
- `hS_ifaceOf`: `[propext, Quot.sound]`
- `bridge`: `[propext, Classical.choice, Quot.sound]`
- `firstLeaf_childShips`: `[propext, Classical.choice, Quot.sound]`
- `synthesizeCombinational_fragment_childRunN`（FB-22）: `[propext, Classical.choice, Quot.sound]`

## 3. elaborate した型（freeze 用の完全な型）
```lean
theorem hS_ifaceOf {ι : Type} (f : FirstLeaf ι) (i : ι) :
    ∀ (vals : Nat → List Nat) (g : Nat → Nat), ((f.ifaceOf.S i) vals)[0]? = some g →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n).filter fun x => x.2 != .domain) →
        g j = Tools.ShippingFirstGateChild.firstFn f.dn f.names f.n f.fe (vals j)

theorem bridge {ι : Type} {mctx mref cctx cref} (O : RefLawsAOps MkRefd mref cref) (f : FirstLeaf ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe))
    {y : Res} (h : RealChildA O f.decl y) (n : Nat) (i : ι) (dsn : Sparkle.IR.AST.Design) :
    ChildRunN (Tools.ShippingMachineLinked.childMap dsn.modules) dsn n y.1
      (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
      [({ name := "out", lo := 0, width := f.n, ty := .bitVector f.n } : Sparkle.IR.Machine.OutField)]
      (f.ifaceOf.S i)
```
証明（elaborate 済み）: `hS_ifaceOf` は `gateS_get0` で `g` を同定して `rfl`。`bridge` は `cases h` で `run` 腕を取り、`EntryDefines.ctx` で `entry` を `mctx' cctx'` に移して `synthesizeCombinational_fragment_childRunN hr entry' f.hwf f.hn (hS_ifaceOf f i)`。完全なソースは §5。

## 4. 読み取りと限界
- `ChildShipsI f.ifaceOf n y.1 y.2` の形は、既存の `firstLeaf_childShips`（`hS` なし）が既に与える。橋 `bridge` は、FB-22 の `ChildRunN` がその `S` 位置（`f.ifaceOf.S i`）で成り立つことを `hS` なしで示し、両者が同じ run `hr` に由来することを型で示す。
- この橋は first-gate fragment の `FirstLeaf` についてのみ。非 fragment（`Pkg` の `q.S`、legacy/memo）は扱わない（FB_RESUME_STUDY §1.3）。`T1Hyp.pkg` の `q.S` と `firstFn` の対応は、この橋では供給していない（interface に `ifaceOf` を選ぶ `hQ` に移る）。
- 台帳: B.F-4 は条件付き −1 の見込みのまま（受入 0）。freeze が承認され、FB-22 の呼び出し側が `hS` ではなく `hQ`（B.G-9、既存行）を使う形になるまで減算しない。`hQ` が増えないこと: 今回の橋は `hQ` を使っておらず、`Q` は登場しない（`hQ` は `firstLeaf_shipsResI` 側にだけ残る）。RefLawsM・ofDecl 単射・shim 変更は扱っていない。
- 結果は elaborate での通過であり、mutant 検査は未実施（freeze 後の実装単位で行う）。

## 5. scratch ソース（そのまま）
```lean
import Tools.ShippingGen4FbFragRun
import Tools.ShippingGen4FirstLeafR
set_option autoImplicit false
namespace Tools.ShippingGen2
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingChildInv (Res)
open Tools.ShippingEntrySoundness (RunsTo quoteDecl)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInvA (RefLawsAOps)
open Tools.ShippingChildFresh (MkRefd)
variable {ι : Type}
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

-- (A) hS is discharged by the gate-side S (definitional)
theorem hS_ifaceOf (f : FirstLeaf ι) (i : ι) :
    ∀ (vals : Nat → List Nat) (g : Nat → Nat), ((f.ifaceOf.S i) vals)[0]? = some g →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n).filter fun x => x.2 != .domain) →
        g j = Tools.ShippingFirstGateChild.firstFn f.dn f.names f.n f.fe (vals j) := by
  intro vals g hg j _
  have h0 := gateS_get0 (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
    (Tools.ShippingUnifiedSource.ofF f.n f.fe) (fun _ => 0) (fun j => j + 1) vals
  have : g = _ := (Option.some.inj (hg.symm.trans h0))
  subst this
  rfl

-- (B) the bridge: RealChildA y  +  FB-22 shape
theorem bridge (O : RefLawsAOps MkRefd mref cref) (f : FirstLeaf ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe))
    {y : Res} (h : RealChildA O f.decl y) (n : Nat) (i : ι)
    (dsn : Sparkle.IR.AST.Design) :
    ChildRunN (Tools.ShippingMachineLinked.childMap dsn.modules) dsn n y.1
      (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
      [({ name := "out", lo := 0, width := f.n, ty := .bitVector f.n } : Sparkle.IR.Machine.OutField)]
      (f.ifaceOf.S i) := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    have entry' := Tools.ShippingReflectCtx.EntryDefines.ctx (mctx' := mctx') (cctx' := cctx') entry
    exact Tools.ShippingGen4FbFragRun.synthesizeCombinational_fragment_childRunN hr entry' f.hwf f.hn
      (hS_ifaceOf f i)

#print axioms hS_ifaceOf
#print axioms bridge
#print axioms firstLeaf_childShips
#print axioms Tools.ShippingGen4FbFragRun.synthesizeCombinational_fragment_childRunN
#check @bridge
#check @hS_ifaceOf
end Tools.ShippingGen2
```
