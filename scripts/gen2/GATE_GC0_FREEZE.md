# U-GC0 freeze: 旧 g6 の gate 系 Lean を base へ移送（U-G1R / U-G2R）

Issue: `sparkle-gate-gc0`（親 `sparkle-gen4-gate-supply`、束 B-GATE）。base: `par/gate-carrier` 15cd9d1f（= 628f30c5 + GATE_CARRIER_FREEZE、reviewer 承認）。source: `kjob/g4gate-g6` 0fb0d739。docs only（この文書の時点で Lean は未編集）。
根拠: `scripts/gen2/GATE_CARRIER_FREEZE.md` §1 と §6 の U-GC0。承認の条件: 旧 g6 の U-G1 / U-G2 / FirstLeaf / InstParent の受理を base 上で有効と扱わない。U-GC0 は別の freeze と build で受理する。
「見つからなかった」はこの調査では供給元・経路が見つからなかったという意味。mutant は signature / defeq での棄却であって意味的反例ではない。
台帳: FG 94 / T1 56（今回 FG -0 +0 / T1 -0 +0）。前提を増やさない移送のため、共通ルールの分担により reviewer には出さない（§5）。

## 1. 対象ファイルごとの直し（新規ファイル。旧名と区別するため全て R を付ける）
| 新ファイル | 旧（g6） | 直し |
|---|---|---|
| `Tools/ShippingGen4IfaceR.lean` | `Iface`（63 行） | `ChildPortWidthsI` を GatePortW から移す。`ChildShipsI` に第 1 連言 `ChildPortWidthsI I mc` を足す。`ShipsResI` に第 3 連言 `InstClosed r` を足す。`childShipsI_ofPkg` は `Iff.rfl` のまま（`ChildPortWidthsI (ofPkg q) mc` が `ChildPortWidths q mc` と defeq）。`shipsResI_iface` は第 3 連言を `and_congr_left`/`Iff.rfl` で扱う。`childPortWidthsI_ofPkg`（旧 GatePortW）も移す |
| `Tools/ShippingGen4GateLeafR.lean` | `GateLeaf`（381 行） | 変更なし（内容は旧と同一、`ChildShips` を使わない）。モジュール名だけ R |
| `Tools/ShippingGen4GateIfaceR.lean` | `GateIface`（97 行） | `import` を R に。`gateLeaf_childPortWidthsI`（旧 GatePortW の本体）を `gateLeaf_childShips` の前に置き、`gateLeaf_childShips` の `ChildShipsI` の第 1 連言に使う。`gateLeaf_shipsResI` に `(hinst : InstClosed y)` を引数で足す。`_of_real` は `hm : y.2.modules = []` から補題 `instClosed_of_nil` で払う。約 30 行の変更 |
| `Tools/ShippingGen4GatePortW.lean` | `GatePortW`（44 行） | 作らない（定義は IfaceR、定理は GateIfaceR へ移動。空になる） |
| `Tools/ShippingGen4GateOutTyR.lean` | `GateOutTy`（30 行） | `import` を R に。本体は同一 |
| `Tools/ShippingGen4FirstLeafR.lean` | `FirstLeaf`（199 行） | `import` を R に。`firstLeaf_childPortWidthsI` を `firstLeaf_childShips` の前に移し、`ChildShipsI` の第 1 連言に使う。`firstLeaf_shipsResI` / `_of_real` は `InstClosed y` を引数で取る（`_of_real` は `hm` から払う）。約 45 行の変更 |
| `Tools/ShippingGen4InstParent.lean` | `InstParent` | **対象外**（U-GC5。T2 は新しい入力 `ChildPortWidthsI J m` が要る） |
宣言名は旧 g6 と同一（namespace `Tools.ShippingGen2`）。旧モジュールと同時に import しない（旧は base に無い）。lakefile.lean には lean_lib の追加のみ（`Tools.ShippingGen4{Iface,GateLeaf,GateIface,GateOutTy,FirstLeaf}R` と `Tests.Gen4.GateGC0Check`）。共有定義（Defs / T1Hyp / T1HypND / Elab*）は編集しない。

## 2. 型の変化と、旧文 / 新文の並び
変わる宣言（他は旧と同一の文）:
| 宣言 | 旧文 | 新文 |
|---|---|---|
| `ChildShipsI I n mc Dc` | `∀ dsn, … → ∀ i, ChildRunN …` | `ChildPortWidthsI I mc ∧ ∀ dsn, … → ∀ i, ChildRunN …`（base の `ChildShips` と同じ形） |
| `ShipsResI L Q c r` | `RealChildA L.O c r ∧ ∃ I n, Q c = some I ∧ I.decl = c ∧ ChildShipsI I n r.1 r.2` | `RealChildA L.O c r ∧ (∃ I n, Q c = some I ∧ I.decl = c ∧ ChildShipsI I n r.1 r.2) ∧ InstClosed r`（base の `ShipsRes` と同じ形） |
| `gateLeaf_childShips` | `… ∀ n, ChildShipsI (g.ifaceOf ty) n y.1 y.2`（同じ文） | 文は同一。証明の中で `gateLeaf_childPortWidthsI` を使う |
| `gateLeaf_shipsResI` | 引数 `hQ h hchild` | 引数 `hQ h hchild (hinst : InstClosed y)` を追加 |
| `gateLeaf_shipsResI_of_real` | 同じ引数 | 同じ引数（`InstClosed` は `hm` から払うので増えない） |
| `firstLeaf_shipsResI` | 引数 `hQ h hchild` | 引数 `(hinst : InstClosed y)` を追加 |
| `firstLeaf_shipsResI_of_real` | 同じ | 同じ引数（`hm` から払う） |
| `shipsResI_iface` | `ShipsResI L P.iface c r ↔ ShipsRes L P c r` | 同じ文（新しい `ShipsRes` に対して） |
| `childShipsI_ofPkg` | `ChildShipsI (ofPkg q) n mc Dc ↔ ChildShips q n mc Dc` | 同じ文（新しい `ChildShips` に対して） |
| `gateLeaf_childPortWidthsI` / `ChildPortWidthsI` / `childPortWidthsI_ofPkg` | GatePortW にあった | 同じ文で、IfaceR / GateIfaceR へ置き場所だけ移動 |
`GateLeaf` / `FirstLeaf` / `ChildIface` / `IfaceMap` / `Pkgs.iface` / `gate_combChildRunN` / `gateLeaf_outTy` / `firstLeaf_childShips` の型は変えない。

## 3. 前提の増減 0 の根拠
- `InstClosed r`: `r.2.modules = []` のとき `∀ g ∈ [], …` で空から自明（`instClosed_of_nil`）。`hm` は `gate_combChildRunN` / `first_child_fullFacts` が既に出す。
- `ChildPortWidthsI`: 旧 GatePortW の既存の証明（`childFull_of_realA` の `tys` と `inPortsOf_of_alloc`）を移動しただけ。新しい仮説なし。
- 新しい定義・仮説・TRUSTED 境界・law・FG は無い。`sorry` / `axiom` / `native_decide` を使わない。ShipsResI の 3 つ目の連言は `_of_real` 形では `hm` から作るので、台帳の前提は増えない。
- `_shipsResI` の `hinst` 引数は仮説として一見増えるが、台帳の前提ではなく定理の引数で、`_of_real` 形が払う。
- この移送が払わないもの: instance 親の T2 の `ChildPortWidthsI J m`（U-GC5）、`GateCovers`、`Pkg` 接続。

## 4. Check（`Tests/Gen4/GateGC0Check.lean`）
- TYPE: 主要定理の Expected を、この文書の §2 から独立に書き `checkExpected`（`Tests.Gen3.ExpectedType`）。
- binder 集合: 型の binder を完全修飾名で照合し、decoy（似た名前の別宣言）を入れて、照合が名前一致であることを確かめる。
- AXIOMS は標準 3 つのみ。CLOSURE（`Laws.T` / `T1Hyp` / `T1HypND` / `RefLawsATele` に到達しない）。COUNTS 行。mutant は signature / defeq での棄却のみ。

## 5. review の要否
文が変わるのは `ChildShipsI` / `ShipsResI`（base の `ChildShips` / `ShipsRes` に合わせて型を揃える）と、`*_shipsResI` の引数 `hinst` の追加。いずれも GATE_CARRIER_FREEZE §1 で reviewer が承認した範囲（直しの内容と前提 0）の実装で、新しい前提・law・境界はない。共通ルールの分担により、この freeze は review に出さない。台帳の差分は 0/0。build 中に前提 delta の増加や型の食い違いが出たら、止めて coder に報告する。

## 6. build 計画
1 つずつ: `Tools.ShippingGen4IfaceR` → `GateLeafR` → `GateIfaceR` → `GateOutTyR` → `FirstLeafR` → `Tests.Gen4.GateGC0Check`。clean build は coder。
