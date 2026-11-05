## §RootShard 訂正（Issue `sparkle-ledger-dd4-shard`、changes_requested への対応。§RootShard 本文は書き換えず、この節が優先）

新ファイル: `Tools/ShippingGen5PTRootShardNamed.lean`、`Tests/Gen5/PTRootShardNamedCheck.lean`。既存の定義・Check は変えていない。TRUSTED・axiom・sorry・native_decide なし（axiom は propext / Classical.choice / Quot.sound のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。段階は条件付きのまま。

### 1. root 名を文に入れた
- `FGLedgerPremisesStmtEntryAt PT declName`: `RootAt PT` の文で `∀ declName` を引数にしたもの。`FGLedgerPremisesStmtRootEntry root Ss := EntryAt (rootPT Ss) root`（root 名が文の中にある）。
  `FGLedgerPremisesStmtRootBy tab := ∀ declName, EntryAt (rootPT (tab declName)) declName`（`∀ declName` の内側で declName から shard 一覧を選ぶ）。
- Check（meta、kernel の証明ではない）: 8 root について `stmtXxx := RootEntry <root> ssXxx` の定数を読み、文中の名前が `rootTable` の root 名と一致、環境の定数であること、shard 一覧が `ssXxx`、
  展開した文が `FGLedgerPremisesStmtPTC` の `PTcorpus := rootPT Ss`、`∀ declName` を root 名で具体化したものと式として一致（`==`）、root 名が文に現れること。
- 負対照: 56 組（root i の shard 一覧 × root j の名前、i≠j）すべてで、文は i の文と一致しない。shard 一覧が同じ組（空の 2 root）も含む。

### 2. 橋の言い方
- `CV` / `H` からの橋は**特殊化**（`fgLedgerPremisesStmtRootEntry_of_CV` など）。`CV` / `H` は未証明の文なので、実 root の存在・shard が要るものと一致すること・意味保存の証明ではない。
- `Root Ss ↔ PTC` は `Ss = []`（または空 shard）の場合だけ。一般の `Ss` への `PTC` からの橋は無い。root 名固定の文では `PTC → RootEntry root []` の一方向（`fgLedgerPremisesStmtRootEntry_nil_of_PTC`）。
- 旧 Check の出力にある「`stmt_*`（`CV` / `H` からの橋）」はこの意味（特殊化）で読む。「PTC からの橋」は誤り。

### 3. shard の選択は名前に基づく候補
- 旧 `shardKeyNames` / `seen` は Name だけを使い、level を捨て、型由来の到達を含まない。これは**名前に基づく候補の選択**であり、必要な key の全被覆でも最小性でもない。旧 §RootShard §3 の「最小性」はこの意味に限る。
- 新 Check は 3 つを数える: (a) 名前のみ、(b) Name×levels（定義本体）、(c) Name×levels + 型由来（到達した各定数の型の binder 型と結果型に現れる定数、本体も続けてたどる）。
- 結果（代表 8 root）: shard key の当たりは (a) 20 / (b) 20 / (c) 20、選ばれる shard 一覧は 8 root とも同じ、名前は届くが level が違う key は 0。型由来で到達ノードは 5〜8 個増えるが shard key は増えない。
  これは 8 root での観測で、全 root の被覆の保証ではない。S1 で採る root ごとに同じ照合を回して示す必要がある（未実施）。

### 4. core の行の前提は移せない
- `CoreRowTypedV (rootPT Ss)` / `CoreRowTeleEv (rootPT Ss)` は合成後の表の上の述語。Q-C の `PTcorpus` の上の証明をそのまま使えるとは言わない。
- 移すのに要る補題の形（未証明）: 表の単調性。`(∀ c ls r, A.tms c ls = some r → B.tms c ls = some r) ∧ (tys も同様)` なら、`RowTypedAtV A env c ls → RowTypedAtV B env c ls`、`RowTeleEvAt` も同様。
  これと `rootPT_keeps_core_tms/tys` があれば `PTcorpus` の行から `CoreRowTypedV (rootPT Ss)` が出る。今回は作らない。
