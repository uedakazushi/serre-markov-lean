# 完成確認状況

2026-10-04の再開時に標準ビルドと公理監査を再確認した。結果: exit 0、3470 jobs、8286 compiled theorem declarations、1232 definition/opaque/axiom declarations。追加の分類仮定・`sorry`・`admit`・追加公理・`native_decide` を使わない。

| 原稿の結論 | 最終API | 状況 |
|---|---|---|
| 定理A、全三型の一意な代表系 | `FullClassification.full_classification`, `canonical_orbit_map_bijective` | 無条件で検証済み |
| 正側の五軌道 | `PositiveClassificationFull.positive_classification` | 高さ・係数・下降仮説なし |
| 定理B、全ファイバー有限かつ大きさ非有界 | `FullClassification.finite_fibers_and_unbounded` | 真の解軌道忘却写像で検証済み |
| 素数平方冪の個数と明示代表 | `prime_square_power_fiber_card`, `prime_square_power_unique_representative` | 前向き写像の明示式と逆式も検証済み |
| 奇数法の一般積公式 | `NegativeFamilyOrbitFibers.odd_fullFiber_explicit_card` | 全負側ファイバーで検証済み |
| 一般の族の格子同型判定 | `family_positive_isometry_iff` | 偶数法の同時合同も保持 |
| 停止する変異同値・格子同型判定 | `mutationEquivalentTest_correct`, `latticeEquivalentTest_correct` | `Solution` 型を入力、実語の正しさも検証済み |

実行例では、変異された族から逆変異語が返り、`F(9,0)` と `F(6,3)` に対して変異同値=false、格子同型=true が得られた。効率・計算量上界は主張しない。

`isSolution` は原稿と同じ二方程式であり、`Reachable` は三変異・逆変異・四符号変更だけの実語である。原稿の反対同値や任意置換を追加していない。最終定理の依存閉包に循環や未証明の完成仮定がないことも静的レビューした。

原稿の全補題の形式化は完成範囲外。詳しい境界は `GAPS.md`、主定理の各依存は `STATUS_ja.md` と `PLAN_ja.md`。

## Lean Blueprint

`blueprint/src` に、基本定義と内在的不変量、負側・退化型・族の一意性、正側の完全分類、ファイバーと停止算法、原稿対応と検証範囲を解説する日本語Blueprintを追加した。標準 `\lean`・`\leanok`・`\uses` を使い、対応宣言の実在と推移的公理依存を独立に監査する。生成PDFとHTML、依存グラフ、同梱ソース行リンク、再生成スクリプトは `blueprint/README.md` を参照。Lean数学ソースの変更はない。
