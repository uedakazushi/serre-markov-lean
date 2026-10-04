# 正側の写像度の実装調査

調査対象は固定された Mathlib v4.24.0。論文 v4 の「正の写像度と符号付き面積」命題について、2026-10-04 にローカルのソースを調べた結果を記す。数学的な反例や矛盾は見つかっていない。この文書は未実装箇所を既証明とみなすための仮定ではない。

| 本文で必要な機能 | 現在の Mathlib の基礎 | 接続に必要な新しい証明 |
|---|---|---|
| 上半平面、Möbius 作用 | `Analysis/Complex/UpperHalfPlane/Basic.lean`, `MoebiusAction.lean` | 本文の四つの半回転と cusp 固定点の具体的な接続 |
| 双曲距離 | `UpperHalfPlane/Metric.lean`: `UpperHalfPlane.dist_eq`, `sinh_half_dist`, 等 | 理想多角形、ホロ球、離散 Fuchs 群の商の幾何 |
| 上半平面の滑らかな構造 | `UpperHalfPlane/Manifold.lean`: `ChartedSpace ℂ ℍ`, `IsManifold`, `contMDiff_smul` | 商曲面の atlas と向き付け、区分的に滑らかな同変写像 |
| 固有写像 | `Topology/Maps/Proper/Basic.lean`: `IsProperMap`, `isCompact_preimage`, `isClosed_range`; `Proper/CompactlyGenerated.lean`: `isProperMap_iff_isCompact_preimage`, `isProperMap_iff_tendsto_cocompact` | source/target cusp の分解、Precisely invariant horoball、高さの上下界から商写像の固有性 |
| 特異ホモロジー | `AlgebraicTopology/SingularHomology/Basic.lean`: `singularChainComplexFunctor`, `singularHomologyFunctor` | 非コンパクト向き付け曲面の基本類、相対または局所有限 homology、写像度、cusp 周辺次数との同一性 |
| 微分形式の外微分 | `Analysis/Calculus/DifferentialForm/Basic.lean`: `extDeriv`, `extDeriv_extDeriv` | 曲面上の積分、pullback と積分の写像度公式 |
| Stokes 型計算 | `MeasureTheory/Integral/DivergenceTheorem.lean`: `integral_divergence_of_hasFDerivWithinAt_off_countable` は Euclidean rectangular box 上の発散定理 | 曲線辺の理想四角形への拡張、horocycle 境界項の極限、理想三角形の符号付き面積 |
| 基本領域の測度 | `MeasureTheory/Group/FundamentalDomain.lean`: `IsFundamentalDomain`, `HasFundamentalDomain`, covolume | 実際の四角形の被覆・交差条件、双曲面積測度、有限被覆による面積の指数公式 |

Mathlib 全体で `Brouwer`, `localDegree`, `mappingDegree`, `topologicalDegree`, `fundamental class`, `Borel–Moore`, `Poincaré polygon`, `Fuchsian`, `ideal triangle`, `Gauss–Bonnet` および関連語を検索したが、本命題へ直接適用できる写像度理論や Fuchs 群の多角形定理は見つからなかった。通常の singular homology の定義の存在だけから、非コンパクト曲面の写像度・正値性・全射性・積分公式を使用することはできない。

実装方針は二通りある。一般の相対または局所有限 homology と向き付け曲面の写像度理論を構築するか、この特定の cusp 付き曲面を円板と帯の有限貼り合わせとして構成し、cusp compactification 上で直接次数と面積を証明する。後者でも周辺円の次数、degree の加法性と内部への延長、非零 degree から全射性、符号付き面積との一致が必要である。

したがって、有限置換問題の完全 census はこの幾何命題の代替ではない。正側の格子から index-12 置換問題へ到達するには、固有写像・正の次数・面積・基本領域と指数の橋を別途証明する必要がある。

## 整数化で得られる群と得られない結論

`PositiveIntegral.positive_solution_even_words_integral_SL2` は、任意の正側正則解から実際の `IntrinsicFrame.Frame` を取り出し、その四つの半回転の**すべての偶語**を同一の正向き有理共役で determinant-one 整数行列にする。ここで対象は偶語の像の群 `Δ` であり、四つの個別半回転が生成する群 `Γ` 全体ではない。

半回転は `Jᵢ = Bᵢ/√A` で、`det Bᵢ = A` である。`Bᵢ` の有理射影類は `PGL₂⁺(ℚ)` に属するが、`A` が有理数の平方でない場合、この代表を有理数でスカラー倍して determinant-one にすることはできない。さらに有理射影共役は determinant の平方類を変えない。したがって、偶語の整数化から個別の `Jᵢ` が `PSL₂(ℤ)` に入るとは結論できない。以前検討した「`Γ` 全体を `PSL₂(ℤ) ≅ C₂ * C₃` の中で四つの order-two 元として扱う」という代替案は、この区別を飛ばしており、その形では使用できない。個別半回転の整数化を新たな仮定として追加していない。

現時点で正側の一般解について形式化できていない切れ目は次の通りである。

1. 半回転群 `Γ` の四角形を基本領域とし、`Γ ≅ C₂ * C₂ * C₂ * C₂`、面積 `2π`、signature `(0;2,2,2,2;1 cusp)` を得る本文の幾何命題。
2. 偶語群 `Δ` が指数 `2`、ねじれ無し、種数 `1`、二カスプ、面積 `4π` となり、整数化済み `Δ` の `PSL₂(ℤ)` 内の指数が `12` となる接続。
3. 幾何のねじれ・二カスプ条件と剰余類作用の固定点・`st` の軌道条件との対応。抽象提示群と実PSL₂(ℤ)の同型自体は`ModularPingPong.presentationPSLEquiv`で完成した。
4. 五つの `Δ` の共役類から `Γ` の拡大を一意に復元する楕円曲線の議論と、その共役から格子の mutation 軌道へ戻る Coxeter/Hurwitz と算術正規化の接続。

これは本文の幾何が不可能であるという主張ではない。既存 Mathlib の基礎から上記の特定命題を証明するために必要な新規理論が、この形式化ではまだ構築されていないという実装上の到達点である。

## 完成した抽象提示群の剰余類の橋

`ModularCosets.lean` では実際の `PresentedGroup` を用い、`s²=t³=1` の提示群 `AbstractGroup` を定義した。置換対から群準同型と群作用を構成し、実際の語による推移性から stabilizer の指数 `12` と剰余類空間との同変な同値を証明した。逆に指数 `12` の任意の部分群から十二点の推移的置換対を作り、単位元の剰余類に対応する stabilizer が元の部分群に**等しい**ことを証明した。同時置換共役と stabilizer の群内共役との同値も証明済みである。

`coset_generator_fixed_point_free_iff` は、任意の群元 `h` の剰余類作用の固定点無しと、すべての `g` に対する `g⁻¹ h g ∉ H` との同値を与える。したがって census の二つの固定点無し仮定は、`s` と `t` の共役元を `H` が含まないという、群の内部の条件としても表せる。実PSL₂(ℤ)への同型と具体的な剰余類作用への移送は完成したが、任意正側解の群がこれらの条件を満たすことは未証明である。

主定理 `ModularCosets.abstract_subgroup_census_unique` は、この抽象提示群の任意の部分群 `H` に対し、`H.index = 12`、`s,t` の剰余類作用の固定点無し、`st` の高々二つの実際の前向き軌道、を仮定すると、五つの具体的な `representativeSubgroup` のちょうど一つと共役であることを述べる。各代表のこれらの性質と、代表同士が共役であることと添字が等しいことの同値も証明した。この結果は有限 census を抽象部分群分類に接続するが、正側格子から `H` やその仮定を構成する定理ではない。

## 自由積の語による代替案の残義務

`C₂ * C₃` の reduced-word 正規形と Hurwitz cancellation で幾何を置き換える可能性は検討できる。ただし整数化されているのは `Δ` であり、四つの `Jᵢ` をこの自由積の order-two 元とする分類を直接適用することはできない。実際に代替するには、整数行列である偶語群 `Δ` と、それを正規化する有理射影半回転の拡大 `Γ`、Riemann–Roch の算術条件を同時に扱う新たな剛性または factorization 定理が必要になる。

整数行列であること、有限生成であること、parabolic 元を含むことだけでは有限指数は従わない。たとえば parabolic 元一つが生成する巡回部分群は `PSL₂(ℤ)` の無限指数部分群である。この例は本文の全仮定を満たす反例ではなく、既証明の整数化だけから指数を推論できないことを示す。RR と四半回転の積の条件を用いて必ず指数 `12`・二カスプになるという代数的定理を新しく証明できれば、幾何命題の代替となる。その定理は現時点で未証明であり、有限 census や `ModularCosets` の剰余類の橋そのものからは得られない。

## 実PSL₂(ℤ)への完成した接続と直接の有界帰着

`ModularPresentation`は整数EuclidによるS,T生成・中心±I・PSLへの全射を証明し、`ModularFreeProduct`と`ModularPingPong`はC₂*C₃の正規形とping-pongで単射を証明する。`ModularPSLCensus.subgroup_census_unique`は、実PSL₂(ℤ)の任意の部分群に対する指数・固定点・カスプ軌道の明示条件から五共役類を分類する。`PositiveGroups`は任意の正側解の実偶語群Δを、共通共役の後で実PSL₂(ℤ)の部分群として構成する。ここでもΓ全体を整数化してはいない。

主分類についての別の経路として、`PositiveNormalization`による正rank・正座標≥3への符号正規化、`PositiveChamber`による任意長braid語でのこの領域の保存、`PositiveBoundedSigned`による高さ37以下の23整数解と五実変異軌道の完全分類も完成した。任意正側解がこの有界領域に実変異で到達することは未証明であり、`PositiveReduction.positive_classification_iff_bounded_reduction`がその残義務を必要十分条件として記述する。この直接帰着を完成できれば、主分類を得るために上記の一般写像度理論を実装する必要はなくなる。
