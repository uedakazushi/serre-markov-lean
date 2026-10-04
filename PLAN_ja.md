# Serre–Markov 論文の Lean 形式化計画

対象は `serre_markov_20261004_v4_public_bundle.zip` の日本語原稿である。主目標は、整数六つ組の解集合に対する変異・符号変更の全三型分類、格子同型類への忘却写像のファイバー定理、変異同値と整数 Euler 格子同型の決定手続きを Lean 4 と mathlib のカーネルが検証できる形にすることである。

最終集約は `FullClassification.lean` に置いた。以下の主分類経路は、正側の最小高さ・順序帰着と普遍多項式証明書による代数証明で閉じた。原稿の全補題、双曲幾何による元の証明、dg 付録の形式化は主目標の完成範囲に含めない。

## 証明の基準

原稿の主定理を追加公理として置かない。`sorry`、`admit`、`sorryAx` に依存する定理を完成品に含めない。計算の正しさを Lean の外部評価に委ねる `native_decide` は使わない。`ring`、`norm_num`、`omega`、`decide` が生成する証明項をカーネルで検査する。

有界探索の成功、有限列挙の網羅性、普遍多項式証明書、幾何的帰着を区別する。五つの置換対の検査だけを「任意の正側解の分類」や「指数十二部分群の全分類」と呼ばない。

## 依存順序と実装

段階9・14および段階13の幾何的帰着は原稿の元の証明経路であり、完成した主分類の前提ではない。

| 段階 | 対象 | 実装先 | 完成の判定・範囲 |
|---|---|---|---|
| 1 | 六成分、変異・逆変異・符号変更、組み紐関係、`q1`・`q2` | `Mutations.lean` | 任意整数成分に対する恒等式と実際の有限操作列 |
| 2 | Gram 行列、整数逆行列、Serre 作用素、反射積、特性多項式 | `Matrix.lean`, `Basis.lean` | 方程式と四乗零の同値、整数基底変更との一致 |
| 3 | 族の普遍変異語と全整数パラメータの正規化 | `Normalize.lean` | 有限の実操作列による正規化 |
| 4 | 明示的格子同型、合同不変条件による軌道分離 | `Fibers.lean`, `Isometry.lean`, `Arithmetic.lean` | 主分類を使わない階数四の反例と算術補題 |
| 5 | 半回転行列と Clifford 関係 | `HalfTurns.lean` | 有理行列の恒等式と整数トレース |
| 6 | 五つの指数十二代表置換対 | `IndexTwelve.lean` | 真の置換、推移性、二巡回と全頂点の被覆 |
| 7 | 原始的旗と内在的不変量 | `Intrinsic`, `IntrinsicFrame`, `IntrinsicUnique`, `IntrinsicSignature`等 | 原始旗、適合整数基底、`A,κ` の選択独立性・格子不変性、cube・content・RR、実対角合同 |
| 8 | 負側の全分類 | `NegativeClassificationFull`等 | 全座標・全符号の網羅分割、実 family 到達または厳密下降、無制限実語による強帰納、正規化代表の存在・一意性 |
| 9 | 原稿の Coxeter/Hurwitz 幾何経路 | `ReflectionHurwitz`、幾何的簡約は未実装 | 実基底変異と Hurwitz 操作の対応は完成。Wegener–Yahiatene の簡約等は未形式化だが主分類には不要 |
| 10 | 退化型の二乗零と全分類 | `DegenerateAlgebra`, `DegenerateClassification`等 | 多項式余因子、Markov 三成分降下、第二小行列式不変量による存在・一意性 |
| 11 | 正側の無条件全分類 | `PositiveSortedTerminal`, `PositiveSortedThreeLarge`, `PositiveSortedFour`, `PositiveSortedFiveLarge`, `PositiveSortedLarge`, `PositiveClassificationFull`等 | 正符号正規化、実際の最小高さと順序帰着、普遍証明書による無界領域排除、有限終端断面の網羅分類から五実軌道の存在・一意性。`positive_reaches_bounded`も仮定なしに接続 |
| 12 | 有限生成整数 Clifford 環と不変格子 | `CliffordOrder`, `NormedClifford`, `RationalLattice`等 | RR データから正向きの共通有理共役による全偶語の `SL₂(ℤ)` への整数化 |
| 13 | 指数十二の有限置換・部分群分類 | `CensusComplete`, `ArbitraryBetaCensus`, `ModularCosets`, `ModularPingPong`, `ModularPSLCensus` | 全10395対合、任意三次置換との五同時共役類、実 PSL₂(ℤ) の提示同型、明示条件下の部分群五共役類。任意正側解の群の指数・カスプ条件への幾何的帰着は未形式化 |
| 14 | 原稿の楕円曲線拡大と Gram 復元 | 未実装部分 | 対合の一意性、群の共役から実変異への持ち上げは元の幾何経路の未形式化部分。段階11の主分類はこれを仮定しない |
| 15 | 格子同型判定と全負側ファイバー | `IsometryNecessary`, `FamilyUniqueness`, `RootProductFormula`, `NegativeFamilyOrbitFibers`等 | 全正総量の family 変異一意性と格子同型判定、全負側ファイバーの有限候補との全単射。奇数法の局所根数・CRT積公式・符号商による厳密個数 |
| 16 | 全三型分類と有限・非有界ファイバー | `FullClassification`, `FullClassificationPipeline`, `Unbounded`, `LatticeQuotient`等 | 全解に一意の canonical 代表、実軌道商との全単射、全忘却ファイバー有限、正側・退化側の個数1、個数の非有界性、奇素数平方冪の明示完全代表列 |
| 17 | 停止する分類と同値判定 | `ClassificationDecision`, `CanonicalLatticeDecision`, `FullClassification` | `Solution` 型を入力に、代表と実到達語を返す探索の停止、変異同値・格子同型の Boolean 判定の正しさ、同値時の実接続語 |

旧来の条件付き helper API を完成した主定理と取り違えない。最終 `FullClassification` は必要な正側・負側完成命題を証明済みの定理で供給し、未証明の分類仮定を置かない。未形式化の幾何補題を仮定として追加することもない。

偶数総量を含む負側の有限候補記述と、奇数総量の素因数積による閉形式は区別する。決定手続きは方程式を満たす証明付きの `Solution` を入力とし、停止と正しさを主張するが計算量の上界は主張しない。

## 検証の手順

1. Lean 4.24.0 と mathlib v4.24.0 を固定する。`lean-toolchain` と `lake-manifest.json` の revision を保存する。
2. 各モジュールを実際にコンパイルして、エラーを修正する。
3. `./scripts/verify.sh` により大きな有限計算 leaf と普遍証明書を直列に検査し、`FullClassification` と全体の `lake build` を実行する。
4. default target の `AxiomAudit` で全公開定理・定義の推移的な公理依存を検査する。許可するのは `propext`, `Classical.choice`, `Quot.sound` のみ。
5. 最終ビルド・監査の成功ログ、固定 revision、ソースを一緒に保存し、証明済みの主結果と未形式化の原稿補題を対応表で明示する。

Python の有限列挙・多項式証明書生成器は信頼境界の外にある。配布済み Lean ソースの検査に Python は不要であり、任意の再生成にはプロジェクト直下で Python 3.9 以上と SymPy 1.14.0 を用いる。

## 数学的精査と残る範囲

原稿の負側・退化側と正側を独立に読み直し、元の Python 検査とも照合した。今回の精査では具体的な反例や、修正不能と確定した数学的誤りは見つかっていない。独立精査はカーネルによる主分類・ファイバー・決定手続きの検証と区別し、原稿全体への第三者の査読を意味しない。

原稿の固有写像、正の写像度、符号付き面積、反射基本領域、指数12への幾何的橋、楕円曲線拡大、Wegener–Yahiatene の簡約、dg 付録は未形式化として明示する。これらは `FullClassification` の仮定でも、代数的主分類を完成するために残る証明義務でもない。

Lean での最終検証状況と詳しい範囲は `STATUS_ja.md` を正本とする。
