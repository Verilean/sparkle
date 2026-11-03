# FRAMEDA_CASES: `FramedA → FramedNM ∨ MemoAccess` (proved, rt163)

状態: 証明済み・ビルド済み（`kjob lake build Tools.Assume.FramedACases` exit 0、313 jobs）。`#print axioms` は propext / Classical.choice / Quot.sound のみ。sorry / axiom / native_decide なし。
場所: `Tools/Assume/FramedACases.lean`（新規、lakefile に lean_lib 追加）。`MemoFamily` を仮説に取らない純粋な補題（`FramedNM` の定義を得るため `Tools.Assume.MemoFamily` を import するだけ）。

- `sideRef_cases : SideRef r → SideRefNM r ∨ MemoRef r`
- `framedA_cases : FramedA Fresh p → FramedNM Fresh p ∨ MemoAccess p`
- `MemoRef` / `MemoAccess` は本ファイルで新規に定義した（freeze 済み家族の一部ではない）。`MemoAccess` はメモ cell の get / set / modify / modifyGet（MetaM と IO 持ち上げ）の 8 constructor。
- 以前の試み（PROPOSAL §0.3）が詰まった原因は `cases` の一括適用で `constructor` が重い isDefEq を試したこと。今回は 40 constructor を `case` で個別に扱い、`apply FramedNM.<name>` で閉じた。

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。この補題は新しい前提を足さない。K walk、outer_miss の述べ直し、最終保証への接続は未着手。
