# VED 階層（複数 module）U1 の設計相談 v1（sparkle-ved-hier）

前提: main 6c29b9b8。U1 は返却 IR に対する strict（reset=0、order-free）。基準文書 §2（階層を分母から除かない）、§3、§5、§7。

## 1. いまの事実
- `synthesizeCombinational decl` は `(m, d)` を返す。`m` が top、`d : Design` は子 module の列。
  - 子は `@[hardware_module]` 呼び出しから `Stmt.inst modName instName conns` で参照される。
  - 実装: Sparkle/Compiler/Elab.lean:4062。
- main の IR 意味論は **open-module** である（Sparkle/IR/Semantics.lean:185-198, 227）。
  - instance の出力は、親の自由入力として扱う。
  - 子の振る舞いはすべて量化される。
  - 閉じた階層意味論は「future work」と明記されている。
- U1 の `ShapeStmt` は v1 範囲として instance を持つ module を拒否する（Tools/VedU1Contract.lean:311-315）。
- 測定（a18ab/cdc41 の u1_deep）: prep で「single-module designs only」が 36 行。
  - ファイルは IPv4/ARP/ICMP/HTTP/TCPHeader、AESHW、Keccak、SHA256/512、ECDSA/Policy/P256/Fido2、PCIe、MultiInstanceTest、MultiOutputSubModuleHangRepro など。
  - u1 経路では、それより前の段（table/proof/checker）で止まる行が多い。

## 2. 決めてほしいこと
1. **階層の意味（statement が何を保証するか）**
2. **証明の構成（何を信頼し、何を kernel が検査するか）**
3. **最初の代表と範囲**

## 3. 選択肢

### A. 閉じた設計意味論を定義し、子ごとの U1 を合成する（推奨）
`DesignStep d top` を新しく定義する。
- 親の 1 cycle を評価するとき、各 `.inst modName instName conns` の出力に、`d` 内の `modName` の module を conns の入力で評価した値を入れる。
- 組合せの子は同じ cycle の関数になる。
- 順序の子は、状態を親の状態の積に加える。

statement は `U1HStmt c d m stmt` とする。中身は U1Stmt と同じ形で、OutputsStmt を閉じた意味で読む。

証明は次の 3 つから組み立てる。
1. 子ごとの U1 定理（子の宣言 = 子 module、既存の生成器を流用）
2. 親の open-module U1。instance 出力は自由入力として扱う（既存の生成器を流用）。
3. 一般補題 1 本：「open で成り立つ親の式に、子の定理の値を代入すると、閉じた意味で成り立つ」。
   - これは module に依存しない定理として 1 回だけ証明する。

| 項目 | 内容 |
|---|---|
| 新しい信頼 | `DesignStep` の定義（reviewer が承認する定義）。生成器と証明は信頼しない（kernel） |
| 利用者に見える影響 | なし（compiler 出力は不変、検査の追加だけ） |
| 費用 | 意味論の定義と合成補題 1 本（組合せの子：中、順序の子：大）、生成器の結線 |
| 後から変えられるか | 変えられる。DesignStep を変えると statement が変わるので、版を上げて再測定する |

### B. 平坦化した 1 module に対して既存の U1 を使う
`flatten (m, d)` を Tools に新しく作り、平坦 module に対して U1 を証明する。

| 項目 | 内容 |
|---|---|
| 新しい信頼 | flatten の正しさ（証明するなら、結局 A と同じ設計意味論が要る）。証明しないなら、保証は「返却 IR」ではなく「flatten した IR」についてになり、§4 の段が 1 つ増える |
| 利点 | 生成器をそのまま使える。規模が大きいと proof/checker の費用が親子の積で増える（測定上、checker の heartbeat がすでに 56 行） |
| 推奨しない理由 | 返却 artifact は階層のままである。保証と出力の対応が間接になる |

### C. 未対応として数え続ける（現状）
- 分母から除かずに「未対応（instance）」と報告する。
- 費用 0。階層を含む行は永久に strict にならない。

## 4. 推奨する最初の範囲（A を選んだ場合）
- **H1:** 組合せの子だけ（子に register/memory なし）、子は単一出力、親は既存の生成器の範囲。
  - 子の重複呼び出し（同じ子の instance が複数）を含む。
  - 一般補題と DesignStep をここで固める。
- **H2:** 順序の子（register 1 個の遅延など、既存スクリプトの範囲）。状態の積。
- **H3:** 複数出力の子（2b の port 命名の結果を使う）。
- 代表:
  - inventory の MultiInstanceTest（PE は register 2 個・structure 出力なので H2+H3）。
  - H1 では、まず inventory 外の小さな対照（組合せの子 1 個、2 回呼び出し）で縦断し、inventory 行は 36 行の中から register-free の子を持つものを探して報告する。件数は約束しない。
- **拒否の対照:**
  - 子 module の名前の入れ替え
  - conns の入れ替え
  - 子の本体の改変
  - design から子が欠落
  - 同じ名前の子が 2 つ
  - いずれも拒否され、定理は残らない。

## 5. 判断しないとどうなるか
- 階層の Issue（5 番目）は着手できない。
- 36 行と、それより前の段で止まっている階層行は未対応のまま残る。
- 他の Issue（front end、2b、性能、gate）は止まらない。

## 6. 根拠
- 測定: ~/git/workspaces/ved-u1-results/full-231d5ee7/final-cdc41/results.tsv（u1_deep の prep_error に "single-module"）
- コード: Sparkle/IR/Semantics.lean:185-198, 227、Tools/VedU1Contract.lean:311-315、Sparkle/Compiler/Elab.lean:4062
