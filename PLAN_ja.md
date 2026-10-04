# Serre–Markov 論文の Lean 形式化計画

対象は `serre_markov_20261004_v4_public_bundle.zip` の日本語原稿である。
主目標は、整数六つ組の解集合に対する変異・符号変更の全分類と、格子同型類への忘却写像のファイバー定理を、Lean 4 と mathlib のカーネルが検証できる形にすることである。

## 証明の基準

原稿の主定理を追加公理として置かない。`sorry`、`admit`、`sorryAx` に依存する定理を完成品に含めない。計算の正しさを Lean の外部評価に委ねる `native_decide` は使わない。`ring`、`norm_num`、`omega`、`decide` が生成する証明項をカーネルで検査する。

有界探索の成功、代表元の検査、列挙プログラムの出力、幾何的帰着の証明を区別する。五つの置換対の検査を「指数十二部分群の全分類」と呼ばない。

## 依存順序と実装

| 段階 | 対象 | 実装先 | 完成の判定 |
|---|---|---|---|
| 1 | 六成分、変異と逆変異、符号変更、組み紐関係、`q1`・`q2` | `Mutations.lean` | 任意の整数成分に対する恒等式と有限操作列の定理 |
| 2 | Gram 行列、整数逆行列、Serre 作用素、反射積、特性多項式 | `Matrix.lean`, `Basis.lean` | 方程式と四乗零の同値、実際の整数基底変更との一致 |
| 3 | 族の普遍変異語と全整数パラメータの正規化 | `Normalize.lean` | 有限の実操作列が正規化を実現する存在定理 |
| 4 | 明示的格子同型、合同不変条件による軌道分離 | `Fibers.lean`, `Isometry.lean`, `Arithmetic.lean` | 主分類を使わない階数四の具体的反例と算術補題 |
| 5 | 正側の半回転行列と Clifford 関係 | `HalfTurns.lean` | 有理行列の恒等式と整数トレースの導出 |
| 6 | 五つの指数十二代表置換対 | `IndexTwelve.lean` | 真の置換、推移性、互いに素な二巡回と全頂点の被覆 |
| 7 | 正則型の原始的旗と内在的不変量 | `Intrinsic`, `IntrinsicFrame`, `IntrinsicUnique`, `IntrinsicSignature`等 | 完成：原始旗・適合整数基底・`A,κ`選択独立性と格子不変性・cube・content・RR・実対角合同と対角の正負成分数 |
| 8 | 負側の全射性 | `NegativeClassificationFull`, `ZeroUnitConic`, `NegativeSingleUnitTwo`, `NegativeDoubleUnitReduction`等 | 完成：全abs≥2、全零辺、孤立単位辺、全二単位辺の網羅分割から実family到達または厳密下降。無制限実語による強帰納で全射性・正規化一意性・全適合基底不変量まで接続 |
| 9 | Coxeter 群の Hurwitz 簡約・推移性 | `ReflectionHurwitz`、幾何的簡約は未実装 | 実基底変異とHurwitz操作の対応は完成。Wegener–Yahiatene の必要な二結果が残る |
| 10 | 退化型の一般的な二乗零と完全分類 | `DegenerateAlgebra`, `DegenerateClassification`等 | 完成：多項式余因子、Markov三成分降下、第二小行列式不変量による存在・一意性 |
| 11 | 正側の一般解から有限分類への帰着 | `PositiveBoundedSigned`, `PositiveReduction`, `PositiveTriangleLower`、一般帰着は未完 | 正符号正規化、任意長の領域保存、全四三角形defect≤−7、L1≤37の全23解・五軌道は完成。全解の有界帰着を証明するか、原稿の固有写像・周辺次数・面積経路を実装する |
| 12 | 有限生成整数 Clifford 環と不変格子 | `CliffordOrder`, `NormedClifford`, `RationalLattice`等 | 完成：RRデータから正向きの共通有理共役で偶語を`SL₂(ℤ)`へ整数化 |
| 13 | 指数十二の有限置換分類 | `CensusComplete`, `ArbitraryBetaCensus` | 完成：全対合を覆う10395行の列挙、任意三次置換への正規化、五同時共役類の存在・一意性。`ModularCosets`で抽象提示群の部分群五共役類まで接続。`ModularPingPong`で実PSL₂(ℤ)の提示同型、`ModularPSLCensus`で実部分群の五共役類まで完成。任意正側解から剰余類条件への帰着は別工程 |
| 14 | 穴あき楕円曲線からの拡大と Gram 行列の復元 | 未実装部分 | 対合の一意性、群の共役から実変異への持ち上げ |
| 15 | 格子同型判定の必要性と一般ファイバー公式 | `IsometryNecessary`, `FamilyUniqueness`, `RootProductFormula`, `NegativeFamilyOrbitFibers`等 | 完成：familyの一般変異一意性、格子同型判定、全奇数法の局所根数・積公式・符号商、全負側実ファイバーの有限性・厳密個数を無条件に証明 |
| 16 | 全分類と有限・非有界ファイバー定理 | `Unbounded`, `LatticeQuotient`, `NegativeFamilyOrbitFibers`、正側全分類は未完 | 負側・退化側の全分類、負側有限性・正確な個数、退化個数1、全解の商写像とファイバー非有界性は完成。正側一般存在を閉じて全三型へ接続する |

未完の段階は、単に定理を仮定した条件付き「全分類定理」で置き換えない。
既存ライブラリに必要な定理がなければ、その定理を別モジュールに実装するか、同じ結論を得る代数的証明を構成する。

## 検証の手順

1. Lean と mathlib のバージョンを固定し、実行環境を準備する。
2. 各モジュールを実際にコンパイルして、エラーを修正する。
3. 主要な成果について `#print axioms` を実行し、標準の Lean 公理以外に依存していないことを調べる。
4. プロジェクト全体を `lake build` で検証する。
5. 証明済み・計算証明済み・未形式化を対応表で明示して保存する。

## 数学的精査

原稿の負側・退化側と正側を独立に読み直し、元の Python 検査とも照合した。今回の精査では具体的な反例や、修正不能と確定した数学的誤りは見つかっていない。これは主定理の形式検証や第三者の査読を意味しない。

Lean での実行状況と残る証明義務は `STATUS_ja.md` を正本とする。
