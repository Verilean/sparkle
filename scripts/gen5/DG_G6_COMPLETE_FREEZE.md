# G6 `dataOfFrom_complete_of_quote` の型（freeze。Lean 実装前の完全な型）

Issue `sparkle-gd-g6`（agent gd6）。設計は `scripts/gen5/GENDATA_ROADMAP.md`（kjob/gdrm2 7c223331）§2.1 / §4 G6。base は par/gd-int f18eb040。置く: `Tools/ShippingGen5DataOfComplete.lean`（新規）、Check は `Tests/Gen5/DataOfCompleteCheck.lean`（新規）。lakefile.lean に lean_lib 2 本を追加するだけ。
**台帳: FG 102 / T1 54（今回 FG -0 +0 / T1 -0 +0）。** FG・T1・law・TRUSTED・共有定義・GenWF・FG の範囲は変えない。A4 / SigTyPh / G7 / G8 / G10 の前提解消・減算、W1 / W3 の減算、T1L-51 / §7 の監査には触れない（候補は「条件付き・未計上」のまま）。この文書は未 elaborate の案で、以下の型は Lean で通ることをまだ確認していない。

**最初の確認（済）**: base で `Tools.ShippingGen5ReadKinds` と `Tools.ShippingGen5DataOfDims` を import する空のファイル `Tools.ShippingGen5DataOfComplete` は `kjob lake build` で exit 0（371 jobs）。

## 1. 主定理（ロードマップ §2.1 の型を、読んだ定義に合わせて完全にしたもの）

namespace `Tools.ShippingGen5DataOf`（`dataOfFrom` と同じ）。`open` は `ShippingGen5DataOfDims` と同じ + `Tools.ShippingGen5ReadKinds`。

```lean
theorem dataOfFrom_complete_of_quote (lvl : Lean.Expr → Nat)
    {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    -- 条件 1,2,3
    (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom))
    (hshape : d.shape = shape)
    -- 条件 8（`d.ok` の行 `packed.WF` 等は hok から射影する。hwf は別仮定にしない）
    (hok : d.ok = true)
    -- 条件 4（readTot_of_quote_body と同じ 3 本 + 本体が quote）
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    -- 条件 4 の level 側（readN_quote の `liftDepth t ≤ k`）
    (hlvl : liftDepth d.packed ≤ lvl shape.body)
    -- 条件 5,6 の寸法（`dataOfFrom_dims` の結論と同じ 2 本）
    (hss : d.ss.length = shape.layout.slots.length)
    (hls : d.ls.length = shape.layout.lets)
    -- 条件 6 の出力側の sort（下の注 N1）
    (houts : List.Forall₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs) :
    dataOfFrom lvl E senv shape tin fl = some d
```

読んだ定義: `dataOfFrom`/`dataOfCore`/`dataOfTail`/`checked`/`mkData`（Tools/ShippingGen5DataOf.lean）、`splitLets`/`splitFields`/`unField`（ShippingMachineCommand.lean:250-）、`packLets`（ShippingMachineEntry.lean:415）、`packAll`・`MachineData.ok`（ShippingMachineAuto.lean）、`readN_quote`・`kindsCfg_complete'`・`kindsCfg_quote_args`・`packed_wf_cfg`（ShippingGen5ReadKinds.lean）。

### 条件ごとの供給元（この調査での読み取り）
- 条件 4: `readN_quote (kindsCfg_complete' …) d.packed (lvl shape.body) hlvl hwf`、`hwf` は `hok` の `packed.WF` 行 + `packed_wf_cfg`。`readTot_of_quote_body` は `exprSize` 固定の級なので、`lvl shape.body` では `readN_quote` を直接使う（readTot_of_quote_body は `readN_quote` のラッパで、同じ補題 `kindsCfg_quote_args` / `packed_wf_cfg` を使う）。
- 条件 5: `splitLets_pack`、`splitFields_pack`（下）。`splitFields` は n=0 で none なので、`!d.fields.isEmpty`（`hok` の最後の行）から `0 < nOuts + nSlots` を出す。`nOuts = d.outs.length`（houts の長さ）、`nSlots = d.ss.length`（hss）。
- 条件 6: `typedFields_of_quote_fields`（下）。`ls` の sort は `hok` の `LetsTyped`（`ok_letsTyped`）、`nexts` の sort は `ok_K_nexts`、`outs` の sort は `houts`。
- 条件 7: `bitsBeq_refl`（`mkData … = d` は構造体の eta + `bposL/vposL/vwL = posB/posV/widV`（hb hv hw）+ `nexts = termsOfAny nl`）。
- 構造体の再構成: `d = mkData shape d.nIn d.dom d.ls d.outs nl`（`nl` は `d.nexts` の各項を `Σ` に詰めたもの。補助 `anyTerms`、下）。
- 寸法 `shape.binders.length = nIn + nSlots + nLets` は `dataOfFront_some`（hfront から）。

### 注
- **N1（houts）**: `outsFitB`（`hok` の行）は出力の幅だけを比べ、`outKind o = .bool` のとき `outs[k]` の sort が `.bool` であること（`.bits 1` でない）は `hok` から出ない。この調査では `hok` からこれを導く経路が見つからなかった（導けないとは書かない）。そのため `houts` を仮定に置く。これは定理の仮定であって台帳の前提ではない。G8（reader の出力が quote の像で各 field に sort が付く）が払う対象で、G6 は払わない。仮定が不要と分かればこの仮定は外れるだけで、増えることはない。
- `hss` `hls` は `dataOfFrom_dims` の結論と同じ形（G8 が `d` を組むときに持つ寸法）。
- 「hok に含まれる行」と「仮定として残す行」の境界はこの 1 本で固定する。変える場合は新しい freeze にする。

## 2. 補助定理（全て外部仮定なし）

```lean
-- splitLets_pack: packLets の逆
theorem splitLets_pack (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)) :
    splitLets fs.length (packLets fs core) = some (fs, ⟨c, core⟩)

-- splitFields_pack: packAll の逆（空は none なので 0 < length が要る）
theorem splitFields_pack (fs : List (Σ w : Nat, Term (.bits w))) (h : 0 < fs.length) :
    splitFields fs.length (packAll fs) = some fs

-- unField_toField: 1 つの field
theorem unField_toField {k : MixedGateBinder} {s : SType} (t : Term s) (h : sortOf k = some s) :
    unField k (toField s t) = some ⟨s, t⟩

-- typedFields_of_quote_fields: sort が揃えば typedFields は fields の逆
theorem typedFields_of_quote_fields {ks : List MixedGateBinder} {ts : List (Σ s : SType, Term s)}
    (h : List.Forall₂ (fun k t => sortOf k = some t.1) ks ts) :
    typedFields ks (ts.map fun t => toField t.1 t.2) = some ts

-- anyTerms: Terms ss の各項を Σ に詰める（termsOfAny の逆）
def anyTerms : {ss : List SType} → Terms ss → List (Σ s : SType, Term s)
theorem anyTerms_spec {ss : List SType} (ts : Terms ss) :
    ∃ h : (anyTerms ts).map (·.1) = ss, HEq (termsOfAny (anyTerms ts)) ts
```

実装中に補助の個数や名前が変わる場合（型が同じ意味の補助の追加を除く）、この md を更新する。主定理の型を変える必要が出たら止めて note と md に書き、review にする。

## 3. Check（他の単位と同じ形、`Tests/Gen5/DataOfCompleteCheck.lean`）
- 独立の Expected TYPE（`Tests.Gen3.ExpectedType.checkExpected`）: 主定理と 4 本の補助。Prop は Lean の定理文からコピーせず、この md の型から書く。
- 正対照: 主定理を `dataOfFrom_sound` と合成した往復の型（`dataOfFrom … = some d ↔` ではなく、`sound` の結論と `complete` の仮定が同じ `d` で繋がる）が通ること。負対照: 仮定を 1 つ落とした文（hfront / hok / hq / hlvl / hss / hls / houts それぞれ）が `checkMutant` で棄却されること。
- mutant は **signature / defeq での棄却**であって、意味的な反例ではない。
- closure: `reach`（T1Hyp / T1HypND / Expr.equal / Expr.eqv / ofReduceBool が無い）。AXIOMS は標準 3 本のみ（`checkAxioms`）。COUNTS 行を他の Check と同じ形で出す。
- sorry / axiom / native_decide なし。
