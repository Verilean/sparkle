# GATE P1 提案（T1 / FG 側の `ShipsRes L P` と gate の `ShipsResI L Q` をつなぐ案）— 事前レビュー用

Issue: `sparkle-gate-gc1`（束 B-GATE）。根拠: `scripts/gen2/GATE_CARRIER_FREEZE.md` §8 P1、§7、§0-3。base: U-GC1 実装（`Tools/ShippingGen4GateCarrier.lean`、`gateReflects_shipsResI` は `GateReflects` と `RealChildA` から `ShipsResI L (gateQ ι GT) c y` を出す）。
この文書は **提案だけ**。共有定義（`Tools/ShippingGen2Defs.lean`、`T1Hyp`、`T1HypND`、`Elab*.lean`）は編集していない。どの案も build していない（数字は `git grep` と Defs の読みだけ）。台帳: FG 94 / T1 56（今回 0/0。B.G-9 の −1 は P1 の承認と接続の後）。
「見つからなかった」は、この調査では供給元・経路が見つからなかったという意味で、不可能の主張ではない。

## 1. 何がつながっていないか（前提知識なしの説明）
- T1 の帰納法の仮説 `IHAt L P Reach D`（Defs:171）と、キャッシュの不変条件 `CacheShips L P Reach m`（Defs:154）は、結論 `ShipsRes L P c r`（Defs:148）で終わる。`ShipsRes` は `∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2`、つまり **パッケージ `Pkg`（`MachineData` を含む）が `P c` にあること** を要求する。
- gate の宣言（`GateRec`）には `MachineData` が無いので、`P c` に `Pkg` を置けない。gate 側の結果は `ShipsResI L Q c y`（`Q : IfaceMap ι`。`ChildIface` はパッケージから 4 項目だけ読んだ記録）で出る。
- 既存の橋は `shipsResI_iface : ShipsResI L P.iface c r ↔ ShipsRes L P c r`（`Tools/ShippingGen4IfaceR.lean`）だけで、`Q = P.iface` の場合にしか使えない。`gateQ ι GT` を含む `Q` から `Pkgs` は作れない。
- さらに `T1Hyp.pkg : ∀ c, Reach c → ∃ q, P c = some q ∧ …`（Defs:210）は、到達した全宣言にパッケージを要求する。gate 宣言が `Reach` に入ると `pkg` が成り立たない。これは P3（FREEZE §8）と同じ問題で、**どの案でも別に解く必要がある**（§4）。

## 2. 影響の数え方（`git grep`、base = 現 HEAD、R ファイルを除く）
| 名前 | Tools の出現（行） | Tools のファイル数 | Tests の出現 | Tests のファイル数 |
|---|---|---|---|---|
| `ShipsRes` | 80 | 24 | 83 | 14 |
| `CacheShips` | 29 | 8 | 19 | 4 |
| `IHAt` | 37 | 9 | 42 | 5 |
| `ShipsAt` | 17 | 6 | 20 | 5 |
| `InvAt`（`CacheShips` を含む） | — | 12 | — | 5 |
| `T1Hyp.pkg` の使用（`.pkg` / `pkg :=`） | 7 行 | 6（Served, T1, ClosingRun, ClosingRun2, EnvQ, T1ND） | — | — |
定理の数ではなく出現行の数。1 つの定理に複数出現するものがあり、定理数はこれ以下。定理単位の数は案を選んだ後に build で数える。
`ShipsRes` の出現ファイル（Tools）: Connect, Defs, FitChain, GroupServed, Keep, KeepChild, OneOut, OneOutTop, OneOutTopO, PostFacts, PostFactsProof, Served, ServedRun, SlotlessParentRun, SlotlessTop, T1, Gen3Arity, Gen3ChildPortWidths, Gen3GroupPortWidths, Gen3SlotlessPortWidths, Gen5ClosingRun, Gen5ClosingRun2, Gen5T1ND, Gen5T2Conn, Gen5T2OutTy, Gen5T2Tie（R ファイル 2 つを除く）。

## 3. 案
記号: `merge P Q : IfaceMap ι := fun c => match P c with | some q => some (ChildIface.ofPkg q) | none => Q c`（P 優先）。

### 案 A: IH 全体を `IfaceMap` で書き直す（`ShipsRes` を `ShipsResI` に置き換える）
- 変える共有定義: `ShipsRes`（`:= ShipsResI L P.iface` に再定義、または本体を `IfaceMap` 版にする）、`CacheShips`、`ShipsAt`、`IHAt`、`InvAt`、`BodyKeepsInv`、`ChildKeepsInv`、`KeepBodyStmt`、`KeepChildStmt` の引数 `P : Pkgs` を `Q : IfaceMap` に（T1 の結論側は `Q := merge P (gateQ ι GT)`）。`T1Hyp` 自体は変えない（§4 を除く）。
- 影響: 上の表の全部（Tools 24 ファイル、Tests 14 ファイル）。`hT.pkg` から `q` を取る箇所（6 ファイル）は `P c = some q → ShipsResI L (merge P Q) c r → ShipsRes L P c r` の補題（新規、機械的）で払える見込み。`ShipsAt` の `∃ q` を使う消費側が `q.d` などパッケージの中身を読むときは、`ChildIface` に無い項目（`MachineData`）を読めない。そのような箇所の有無はこの調査では数えていない。
- B.G-9 の −1 が成り立つ条件: (1) A の共有定義の変更が事前レビューで承認される、(2) 変更後に T1 / FG の鎖（24 ファイル）が clean build で通る、(3) FG 側の消費定理が `Q` と `hQ` を引数に取るのをやめ、`gateQ ι GT` と `gateReflects_shipsResI` に置き換わる。
- 利点: 接続が 1 箇所（型の一本化）。欠点: 変更量が最大。`ShipsRes` を再定義すると 80 行規模の再 build と、キャッシュの無効化がある。

### 案 B: `ShipsRes` を残し、IH の結論だけを選言にする（`ShipsRes L P c r ∨ ShipsResI L Q c r`）
- 変える共有定義: `IHAt` と `CacheShips`（`Q : IfaceMap ι` の引数を足し、結論 / 述語を `ShipsRes L P c r ∨ (P c = none ∧ ShipsResI L Q c r)` にする）。`ShipsRes`、`ShipsAt`、`ChildShips`、`T1Hyp` の他の項目は変えない。`InvAt` は `CacheShips` を含むので引数が増える。
- 影響: `IHAt` 37 行 / 9 ファイル、`CacheShips` 29 行 / 8 ファイル、`InvAt` 12 ファイル。T1 の生産側は左の枝（`Or.inl`）で既存の証明をそのまま使う見込み。消費側（Keep / KeepChild / Served）は右の枝の場合分けが増える。右の枝を実際に使う箇所は、gate 宣言のキャッシュへの挿入と、親が gate 子を呼ぶ箇所。後者は `CallDec p q k`（Defs:112 付近）が `Pkg q` を取るため、`ChildIface` 版の `CallDecI` が別に要る。この調査では `CallDecI` に当たる既存の定義は見つからなかった。
- B.G-9 の −1 が成り立つ条件: A の (1)〜(3) と同じ形（(2) は 8〜9 ファイル）。
- 利点: 既存の P 側の証明がほぼそのまま残る。欠点: 選言が IH の全消費者に出る。右の枝の中身（親が gate 子を呼ぶ側の `CallDecI`）は P1 の範囲外で、別の単位が要る。

### 案 C: 共有定義を触らず、新規ファイルに `IfaceMap` 版を並置する（橋の補題つき）
- 変える共有定義: なし（`CacheShipsI` / `IHAtI` / `ShipsAtI` / `InvAtI` を新規ファイルに追加し、`CacheShips L P ↔ CacheShipsI L P.iface`、`IHAt L P ↔ IHAtI L P.iface` などの同値を示す）。
- 影響: 既存の定理は 0 本変更。ただし接続のために必要な T1 の鎖（Keep、KeepChild、Served、ClosingRun 等）の `I` 版の複製が要る。複製の本数はこの調査では数えていない（A の影響範囲を上限と見る）。
- B.G-9 の −1 が成り立つ条件: `IHAtI L (merge P (gateQ ι GT))` を消費する FG の接続定理が新規に書かれ、その鎖が通ること。`P.iface` との橋は `Q = P.iface` にしか使えないので、`merge` を使う接続は複製した鎖の上でしか成り立たない。
- 利点: 共有定義の変更なし（ユーザー承認が要る範囲が最小）。欠点: 同じ鎖が二重になり、保守が 2 倍。

## 4. P3（`T1Hyp.pkg`）との関係（案に依らない）
A / B / C のどれでも、gate 宣言が `Reach` に入るなら `T1Hyp.pkg` は `Reach c ∧ gate に属さない` に弱める（または `P c = none` の枝を足す）必要がある。これは `T1Hyp` / `T1HypND` の変更で、FREEZE §8 の P3。`pkg` の使用は 7 行 / 6 ファイル。ここで `GateCovers`（到達した gate 宣言は表に載る、P2）の型が必要になるので、P1 の承認だけでは B.G-9 の接続は閉じない。P1 / P2 / P3 は 1 つの束として reviewer に諮るのが整合的、と考える（決めない）。

## 5. 推奨と理由
**案 B を第一候補、案 A を第二候補**とする。
- B は変更する共有定義が 2 つ（`IHAt`、`CacheShips`）で、既存の生産側の証明を `Or.inl` で再利用できる見込みがあり、A より影響が小さい。
- A は型としては一番きれいだが、`ShipsRes` 80 行 / 24 ファイルの再 build になり、パッケージの中身を読む消費側の有無も未確認。
- C は共有定義を触らない点が利点だが、鎖の複製が A に近い規模になる可能性があり、複製後の整合（T1 の更新に追随すること）を保つ費用が残る。ユーザー承認の範囲を最小にしたい場合の退避案。
- どの案も、B.G-9 の −1 は **接続が build で通ってから** 数える。いまは台帳を変えない。

## 6. この調査で確かめていないこと
- 3 案とも build していない。影響の数は `git grep` の出現数で、定理の本数ではない。
- `ShipsAt` の消費側がパッケージの中身（`MachineData`）を読む箇所の有無。
- `CallDec` の `ChildIface` 版（親が gate 子を呼ぶ側）の既存定義 — 見つからなかった。
- `T1HypND`（Gen5T1ND:35）で同じ `pkg` の弱め方がそのまま使えるか。

## 7. 判断の要点（reviewer へ）
1. 案 A / B / C のどれで進めるか（または P3・P2 を束ねた別案）。
2. P1 は共有定義の変更を含むため、承認後に別 freeze（型の完全な差分）を出す。この文書は freeze ではない。
3. 判断されない場合: U-GC1 の carrier と主定理は単独で有効（`gateQ` / `gateReflects_shipsResI`）。B.G-9 の −1 は計上されず、FG 側の `Q` / `hQ` は前提のまま残る。
