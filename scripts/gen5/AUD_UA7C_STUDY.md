# U-A7c 調査: hsep(b)（子の design の module 名が `ofDecl declName` でない）の供給元

- Issue: sparkle-aud-ua7c（親 sparkle-ledger-shorten）。base: par/aud-ua7b 810f56b3（AUD_UA7B_STUDY.md）。文書のみ（Lean のソースは編集していない）。
- 種別: 調査（freeze ではない）。台帳: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
- 用語: (b) = UA7B §1-(b)「calls 枝の子の design の module 名が `ofDecl declName` でない」（`ChildIfaceP` では `ofDecl declName ∉ nms`）。「親が自分の callee の鍵集合に無い」= 旧 `entryOk_machine` の `hc : ¬ K c`。

## 0. 結論（先に）

1. **非巡回（`¬ K c` に当たる部分）は、現行の枠で既に在る事実から出る**（§2）。D.E-8（`InClass`）+ `GraphAgrees` + `ReachSpans`（`hself_all_reached` と同じ入力）から、「reached な `c` は、自分から 1 歩以上の OrdPath で自分に戻らない」`strictDesc_irrefl` を scratch で証明した（§4、axiom は標準 3 つのみ）。新しい前提は 0。depth（`dv`）は、この調査では使い道が見つからなかった（§2）。
2. **しかし (b) 全体の供給元は、この調査では見つからなかった。** 欠けているのは非巡回ではなく、**「子の結果の design の module 名は、メモリ module か、親の strict descendant の `ofDecl` である」という名前の事実（`DescProv`、§4）そのもの**。`Prov`/`Fresh`/`EntryOk` はこの事実を cache の不変条件として運ぶが、現行の `Laws`/`InvAt`/`CacheShips`/`RealChildA` はどの field もこれを運ばない（§1 の表）。`DescProv` と `strictDesc_irrefl` から (b) を出す補題 `hsepB_of_descProv` は scratch で通した。
3. 旧枠（`RefLaws`/`InvV`/`J`）の `Prov` は、現行の枠に**そのままは移せない**。旧 `RefLaws` を使う Gen2/Gen3/Gen5 のファイルは、この調査では見つからなかった（§1）。`Prov` を現行の枠に載せるには、`InvAt` に conjunct を足すか（共有定義 `Tools/ShippingGen2Defs.lean` の変更: 禁止事項）、新ファイルで `InvAtP := InvAt ∧ Prov…` を定義して `KeepBodyStmt`/`KeepChildStmt` 相当を作り直す（新しい statement）かの、どちらかになる。どちらも新しい前提（または既存の文の変更）で、**数はこの調査では確定していない**（§5）。
4. **E-12 は未解消。** 台帳は動かさない（FG 94 / T1 54、今回 0 / 0）。(b) を新しい前提として足した扱いにはしていない。

## 1. Prov / Fresh / EntryOk を現行の枠に移せるか（field ごとの表）

旧枠: `RefLaws`（Tools/ShippingChildInv.lean:333）、`InvV`（:578）、`J`（:587）、`EntryOk`（Tools/ShippingCacheCoherentCert.lean:190）。現行枠: `Laws`（Tools/ShippingGen2Defs.lean:46）= `RefLawsAOps` + `RefLawsATele`（Tools/ShippingChildInvA.lean:263, :340）、`InvAt`（Gen2Defs:164）、`CacheInvA`（Tools/ShippingChildCacheA.lean:115）、`RealChildA`（:105）、`ShipsRes`/`CacheShips`（Gen2Defs 付近）。

| 旧枠の field / 述語 | 内容 | 現行枠の対応 | 差分 |
|---|---|---|---|
| `Prov m`（Run.lean:96）の名前 field `y.1.name = ofDecl c` | cache の entry の module は key の名前 | `RealChildA` は名前 field を持たない（ChildCacheA.lean:105）。名前は経路ごと（UA7B §1-(ii)） | **無い**。`CacheShips`（reached のみ）の `ShipsRes` も `ChildShips`（`moduleByName dsn.modules mc.name = some mc` で名前を引くだけ）と `InstClosed` で、名前の形（`ofDecl c`）は言わない |
| `Prov m` の design field `∀ a ∈ y.2.modules, IsMem a ∨ IsTop m a` | design の module はメモリ module か cache の entry の module | 無い。`InstClosed`（Gen2Defs:129）は「各 module をどれかが instantiate する」だけ | **無い**（UA7B §1-(b) と同じ。後入りの閉路は排除できない: §3） |
| `Fresh m c r`（Run.lean:102）の `m.get? c = none` | 挿入する key は cache に無い | `synthesizeChild` の miss 分岐（Tools/ShippingCacheCoherentCert.lean `synthesizeChild_ok`）は旧枠。現行枠側では `cacheInvA_insert`（ChildCacheA.lean:130 付近）が `RealChildA` を挿入で保つだけ | 現行枠に cache 欠落の言明は無い |
| `RefLaws.aux` / `auxInsert`（ChildInv.lean:343-345） | 「miss は map に無い key への挿入」を満たす proof 用 predicate。`Prov` は運べない（Run.lean 冒頭: `auxInsert` は任意の挿入値で成り立つ必要がある） | `RefLawsAOps` に `aux` は無い（ChildInvA.lean:263 以降の field 列挙）。現行の cache 不変条件は `InvAt` の `CacheShips` と `Keeps`（`BodyKeepsInv`/`ChildKeepsInv`）で運ぶ | 同じ制約（挿入値の条件）は `KeepChildStmt`（G-KEEP-CHILD）が負う。`Prov` 相当を載せるなら、この文の再証明が要る |
| `EntryOk L c K`（Cert.lean:190） | 返る run の `Prov` 維持・`Fresh`・`KeysIn`（追加された key は `K`） | `IHAt`（Gen2Defs）は `ShipsRes` のみ。`KeysIn` に当たる言明は見つからなかった | **無い** |
| `entryOk_machine` の `hvia : CoreVia`, `hstill : HarnessStill`, `hout` | 旧枠の `L : RefLaws` を引数に取る（Cert.lean:498 以降） | `ClosingRun`（Tools/ShippingGen5ClosingRun.lean:48）が運ぶ `RunReadsAt`/`MReturns`/`CloseCalls` は `Laws` 側 | `CoreVia` に当たるものは `ClosingRun.shared` の `RunReadsAt` + `RunReadsAt.machineRun`（ClosingRun.lean:74）。ただし両者の対応は、この調査では確認していない |
| `hc : ¬ K c` | 親は自分の callee の鍵集合に無い | **§2: 出せる** | 差分 0（`strictDesc_irrefl`） |
| `hR : ∀ c', K c' → EntryOk L c' K` | 子の `EntryOk` | `ChildrenShipsI`（Tools/ShippingGen2ServedRun.lean:342）が子の `RealChildA` + `ShipsRes` を渡す | `EntryOk` に当たる中身（名前・design の provenance）が `ShipsRes` に無い |

付記: Gen2 / Gen3 / Gen5 の `Tools/ShippingGen*.lean` で `RefLaws` を引数に取るものは、`grep -l "RefLaws "` では見つからなかった。`Prov`/`EntryOk` を使うファイルは、旧枠側（ShippingCacheCoherent*、ShippingGate*、ShippingEntryOk*、ShippingOutermost など）に限られる。旧枠の `EntryOk` を現行の `Laws` から作る橋（`Laws → RefLaws`）は、この調査では見つからなかった（逆向きの `RefLawsCore.toAOps` は在る: ChildInvA.lean:347）。

## 2. 非巡回（親が自分の callee の鍵集合に無い）を現行の事実から出す経路

| 候補 | 結果 |
|---|---|
| **D.E-8 / E-9 の rank（`InClass`, `rank_of_reach`, `rank_of_ordEdge`）** | **出せる**。`ReachSpans` で `c` は top から OrdPath、よって `declRank c = some r`（`rank_of_reach`）。`c → x`（OrdEdge）で rank が真に下がり（`rank_of_ordEdge`）、`x ⇝ c` の OrdPath で rank が下がらない（`rank_of_reach`）から矛盾。これが `strictDesc_irrefl`（§4）。入力は `hself_all_reached`（NameKids3.lean:99）と同じ `InClass`/`GraphAgrees`/`ReachSpans` のみ（D.E-6〜E-9 の既存の行。新しい前提 0） |
| 鍵集合 `K` の取り方 | `K_c := {c' | StrictDesc g c c'}` とすれば、`c' ∈ K_c` なら `K_{c'} ⊆ K_c`（`strictDesc_trans_left`、§4、`OrdPath c c'` と `StrictDesc c' b` から `StrictDesc c b`）。`entryOk_machine` を `K_{c'}` で使って `EntryOk.mono`（Cert.lean:197）で `K_c` に上げられる |
| depth（`dv`） | この調査では使い道が見つからなかった。理由: `dv` は run の入れ子の深さ（`sparkleSynthDepthLimit` で打ち切り）で、「同じ名前の入れ子 run が無い」を言うには「同じ名前の run は cache に入るまで再入されない」と静的な呼び出しグラフの対応（G-REACH）が要る。rank の方が静的で、既に在る |
| cache に入る前に子を合成する順序 | 旧 `EntryOk` の `KeysIn` が「追加された key は子孫の key」を運ぶ形で、これは `Prov` を運ぶ枠と一体。現行枠に `KeysIn` は見つからなかった（§1 の表） |

## 3. (b) が非巡回だけでは出ない理由（UA7B §1-(b) の補足）

`ShipsRes`（= `CacheShips` が reached な entry に持つもの）の `InstClosed` は、design の各 module が `y.1 :: design` のどれかに instantiate されている、という incoming-edge の事実。`ModCorr`/`DesignCorr`（Tools/ShippingSrm12Corr.lean:56, :62）と合わせると、design の module `g` の名前は「`y.1 :: design` のある module `h` の graph の callee」になる。しかし、この incoming の鎖は `y.1` で終わるとは限らない: design の中で `h2 ⇄ h3` が互いに instantiate し合い、`h1 → declName` の辺を持つ閉路が（graph に reached でない閉路があれば）矛盾なく成り立つ。D.E-8 の rank は reached な宣言にしか定義されないので、これを排除しない。
排除に要るのは「design の module はすべて `y.1` から前向きに到達できる」（または `Prov` / `DescProv`）で、これは `RealChildA` の run の構造（`designWith` の `children`）を再帰的に降りる帰納法になる。しかし `RealChildA.run`（ChildCacheA.lean:105）は run の結果だけを持ち、入れ子の `CloseCalls` を持たない。`ClosingRun` は `InvAt`（`CacheShips` つき）の start world を要求するのに対し、`RealChildA` の start world は `CacheInvA`（`RealChildA` だけ）なので、`RealChildA` の子に直接 `ClosingRun` を当てることはできない（この調査では橋が見つからなかった）。

## 4. scratch での elaborate（`set_option autoImplicit false`、`kjob lake env lean`）

ソースツリーには入れていない（scratchpad）。import は `Tools.ShippingGen5NameKids3`, `Tools.ShippingCacheCoherentRun`（`kjob lake build` 済み、exit 0、約 14 分）。`sorry` なし。`#print axioms`: `strictDesc_irrefl` / `hsepB_of_descProv` は `[propext, Classical.choice, Quot.sound]`、`strictDesc_trans_left` は axiom なし。

- `strictDesc_irrefl`: 非巡回（§2）。
- `strictDesc_trans_left`, `ordPath_cons`: `K` の単調性。
- `DescProv`: 現行の枠に**無い**事実を言明として切り出したもの（定義であって仮定の追加はしていない）。
- `hsepB_of_descProv`: `DescProv` + `strictDesc_irrefl` + `ofDecl_ne_ofMem` + `ofDecl_injective` から (b) の形 `∀ a ∈ y.2.modules, a.name ≠ ofDecl declName`。

```lean
import Tools.ShippingGen5NameKids3
import Tools.ShippingCacheCoherentRun
set_option autoImplicit false
open Lean (Name)
open Tools.ShippingSrm7Rank (CallGraph callees declRank InClass)
open Tools.ShippingGen5NameKids3
open Sparkle.IR.ModuleName (ofDecl ofMem)

/-- a strict (≥ 1 step) ordinary path -/
def StrictDesc (g : CallGraph) (a b : Name) : Prop := ∃ x, OrdEdge g a x ∧ OrdPath g x b

theorem strictDesc_irrefl {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach)
    {c : Name} (hc : Reach c) : ¬ StrictDesc g c c := by
  rintro ⟨x, he, hp⟩
  obtain ⟨r0, h0, -, -⟩ := Tools.ShippingSrm7Rank.inClass_rank hin
  obtain ⟨r, hr, -⟩ := rank_of_reach h0 (hsp c hc)
  obtain ⟨r1, h1, hlt⟩ := rank_of_ordEdge hr he
  obtain ⟨r2, h2, hle⟩ := rank_of_reach h1 hp
  rw [hr] at h2
  have := Option.some.inj h2
  omega

theorem ordPath_cons {g : CallGraph} {x y b : Name} (he : OrdEdge g x y) (hp : OrdPath g y b) :
    OrdPath g x b := by
  induction hp with
  | refl => exact OrdPath.step OrdPath.refl he
  | step _ e ih => exact OrdPath.step ih e

theorem strictDesc_trans_left {g : CallGraph} {a x b : Name} (h1 : OrdPath g a x) (h2 : StrictDesc g x b) :
    StrictDesc g a b := by
  induction h1 with
  | refl => exact h2
  | @step x' x'' _ e ih =>
    obtain ⟨y, he, hp⟩ := h2
    exact ih ⟨x'', e, ordPath_cons he hp⟩

/-- the provenance fact the current frame does not carry: design modules of a child result are
memory modules or named after a strict descendant of the parent -/
def DescProv (g : CallGraph) (declName : Name) (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) : Prop :=
  ∀ a ∈ y.2.modules, Tools.ShippingCacheCoherentRun.IsMem a ∨ ∃ c', StrictDesc g declName c' ∧ a.name = ofDecl c'

theorem hsepB_of_descProv {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach)
    {declName : Name} (hr : Reach declName)
    {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design} (hp : DescProv g declName y) :
    ∀ a ∈ y.2.modules, a.name ≠ ofDecl declName := by
  intro a ha e
  rcases hp a ha with ⟨cb, aw, dw, ea⟩ | ⟨c', hd, hn⟩
  · rw [ea, Tools.ShippingCacheCoherentRun.memModule_name] at e
    exact Tools.ShippingModuleName.ofDecl_ne_ofMem declName cb aw dw e.symm
  · rw [hn] at e
    have := Tools.ShippingModuleName.ofDecl_injective e
    subst this
    exact strictDesc_irrefl hin hsp hr hd
```

注: scratch の結果。mutant は扱っていない（棄却の検査はしていない）。台帳の行を消す根拠にはならない。

## 5. 新しい前提が要る場合の数と文（相殺しない）

- 今回の調査が増やした前提: **0**。減らしたものも 0。
- (b) を払うには `DescProv` 相当（「子の結果の design の module は、メモリ module か、親の strict descendant の `ofDecl` 名」）が要る。この調査では、既存の行から導く経路は見つからなかった。入れ方の候補（どちらも未実施。reviewer 承認とユーザー判断が要る台帳の変更）:
  - (P1) `ShipsRes`/`InvAt` に名前の conjunct を足す: 共有定義（Gen2Defs.lean）の変更。禁止事項に当たるため、ここでは行っていない。
  - (P2) 新ファイルで `InvAtP := InvAt ∧ DescProv…` と `KeepBodyStmt`/`KeepChildStmt` の `InvAtP` 版を作る: G-KEEP-BODY は U0 で証明済み（GENERAL_SPEC.md:374）だが、`InvAtP` 版は新しい文。G-KEEP-CHILD 側が open（G-EXC）である点は変わらない。
  - 増える前提の数は、この調査では確定していない（P2 は最低でも G-KEEP-CHILD の `InvAtP` 版 1 件の見込みだが、未確認）。
- (b) が `ChildIfaceP` の `own ∉ nms` 以外の形（`MemCalleeData.parentD`、宣言ごとのデータ: UA7B §1-(iv)）で既に宣言ごとに払われている範囲は、UA7B の通り。一般の補題は見つからなかった。

## 6. 台帳

- 受入済み: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
- 条件付き台帳: E-12 の −1 は主張しない。−1 になる条件: (b) に供給元ができる（既存の行で払えるなら 0、新前提なら +k）、`AuditE12` の経路の扱い（UA7B §5）が決まる。

## 7. 次

- reviewer: §1 の表（旧枠 → 現行枠の field 対応、特に `CoreVia` と `RunReadsAt` の対応が未確認である点）、§2 の `strictDesc_irrefl`、§3 の「非巡回だけでは出ない」の読み。
- ユーザー判断が要る点: §5 の P1 / P2（共有定義の変更または新しい文）。決まる前に Lean へは進まない。
- 続く調査の候補: `RealChildA` の子から `ClosingRun` 相当の分解（入れ子の `CloseCalls`）を得る橋が在るか（`IHAt` の run からではなく、cache 内の entry の生成 run について）。
