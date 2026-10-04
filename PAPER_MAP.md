# 原稿 v4 と形式化の対応

添付 serre_markov_lean_with_blueprint.zip の確認記録に基づく対応です。この公開準備環境では Lean を再実行していません。現在の commit の再検証は GitHub Actions の verify が担当します。結論の形式化と原稿の証明経路の形式化を区別します。

| 原稿 | 最終 Lean API | 添付版の確認記録 |
|---|---|---|
| 方程式と N⁴=0 | solution_iff_fourth_power_zero | 検証済み |
| 負側分類 | NegativeClassificationFull.negative_classification | 無条件で検証済み |
| 族の分離 | FamilyUniqueness.normalized_positive_totals_reachable_iff | 検証済み |
| 退化分類 | degenerate_classification | 無条件で検証済み |
| 正側五分類 | PositiveClassificationFull.positive_classification | 無条件で検証済み、標準 import に包含 |
| 定理A | FullClassification.full_classification / canonical_orbit_map_bijective | 無条件で検証済み、標準 import に包含 |
| 格子同型 | family_positive_isometry_iff | 偶数法の同時合同を含め検証済み |
| 積公式 | NegativeFamilyOrbitFibers.odd_fullFiber_explicit_card | 奇数法の真の全負側ファイバーで検証済み |
| 定理B | FullClassification.finite_fibers_and_unbounded | 全ファイバーについて検証済み |
| 決定可能性 | FullClassification.mutationEquivalentTest_correct / latticeEquivalentTest_correct | Solution 入力の無条件 wrapper で検証済み |
| 正側幾何、指数12への大域的帰着、楕円拡大、群からの幾何的復元 | GAPS.md の幾何 API | 未形式化。完成した数値的分類の仮定ではない |
| dg / 射影幾何実現 | 該当実装なし | 未形式化 |

定理・定義の詳細、補助結果と依存関係は STATUS_ja.md および Blueprint を参照してください。Blueprint の完成印は対応する Lean 宣言を指し、本文全体を機械検証したという意味ではありません。
