# 原稿 v4 と形式化の対応

原稿の番号変更に強いように LaTeX label で照合する。証明手法の一致と結論の形式化は区別する。

| 原稿 | 対応 | 現在確認できた範囲 |
|---|---|---|
| 方程式と N⁴=0 | solution_iff_fourth_power_zero | 標準ビルドで検証済み |
| 負側分類 thm:mainnegative / thm:negativesurj | NegativeClassificationFull.negative_classification | 無条件で検証済み。幾何証明ではなく整数下降 |
| 族の分離 prop:familyseparation | FamilyUniqueness.normalized_positive_totals_reachable_iff | 検証済み |
| 退化分類 thm:degclassification | degenerate_classification | 無条件で検証済み |
| 退化 Jordan 型 | DegenerateJordan.degenerate_classification_with_rank | 検証済み |
| 正側幾何 thm:positivegeometry / prop:positivedegree | 幾何 API の資料 | 完全な形式化は確認できない |
| 整数化 prop:directmodular | PositiveIntegral / PositiveGroups | 共通整数化は検証済み。指数12の一般帰着は含まない |
| 有限表 prop:index12census | IndexTwelve / ModularPSLCensus | 指数・剰余類条件を仮定する完全分類は検証済み |
| 群から復元 prop:positivegramrecovery / lem:ellipticextension | 未接続 | 形式化未完 |
| 正側五分類 thm:positivefive | PositiveClassificationFull.positive_classification | ソースあり。標準 import 外。追加ビルドの完了確認が必要 |
| 定理A cor:full | FullClassification.full_classification | ソースあり。標準 import 外。追加ビルドの完了確認が必要 |
| 格子同型 prop:familyiso | family_positive_isometry_iff / family_isometry_iff_odd_square | 検証済み。偶数法の同時合同も保持 |
| 積公式 thm:fibercount | NegativeFamilyOrbitFibers / RootProductFormula | 真の負側全ファイバーについて検証済み |
| 非有界性 cor:unboundedfibers | unbounded_solutionForgetfulMap_fibers | 無条件で検証済み |
| 定理B thm:fiberintro / prop:finitefibers | 全負側と退化は完成。全体は FullClassification | 全体有限性の無条件化は追加ビルド確認待ち |
| 決定可能性 cor:decidability | ClassificationDecision / CanonicalLatticeDecision | 正側完全性を明示引数とする実装は検証済み。FullClassification の無条件 wrapper は確認待ち |
| dg / 射影幾何実現 prop:dgrealization / cor:geometricembedding | 該当実装未確認 | 未形式化 |

古い STATUS_ja.md / README.md は追加ファイルの存在を反映していない。本回収資料を現在の確認結果とする。
