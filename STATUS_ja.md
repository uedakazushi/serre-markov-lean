# Serre–Markov v4 の形式化状況

対象は2026年10月4日のv4原稿。負側・退化側の一般分類と全負側ファイバー公式は完成した。正側の一般分類は未完である。本プロジェクトでは、以下の数学的成果を実際にLeanで検証した。原稿の主定理を公理として仮定してはいない。

## 検証済みの主要成果

| 対象 | Leanの公開定理・モジュール | 証明の範囲 |
|---|---|---|
| 六成分と変異 | `Mutations`, `Basis` | 逆操作、組み紐関係、符号変更、方程式保存、任意の有限語と整数基底変更の一致 |
| Serre作用素 | `solution_iff_fourth_power_zero` | 任意の整数六つ組について、二方程式と四乗零の同値 |
| 行列・反射 | `Matrix` | 整数逆行列、特性多項式、等長性、交代形式の行列式、四反射の積 |
| 族の全整数正規化 | `family_normalize`, `family_normalize_degenerate` | 具体的な有限操作列の存在、符号と境界を含む |
| 二Kronecker断面 | `kronecker_slice_reachable_family` | 両方の`q2`符号について、断面の全整数解から族への帰着 |
| 二面体ラベル | `Dihedral`, `DihedralFinite` | 積が恒等の四反射ラベルのEuclid簡約、整数・合同の場合 |
| 変異不変量 | `family_divisibility_invariant` | 族から族への任意の有限変異・符号語で同時整除性が保存され、中間点ではmatching supportが保存される |
| 族の格子同型 | `family_positive_isometry_iff` | 正の総量が等しいことと同時合同式が、任意の整数格子同型の必要十分条件 |
| 格子同型の有限判定 | `familyIsometryTest_correct` | 正の任意の法で有限計算が真の整数格子同型の存在を判定。偶数の場合も同時合同式を保持 |
| 奇数法への簡約 | `family_isometry_iff_odd_square` | 奇数法ではパラメータの二乗合同との完全な同値 |
| 偶数法の注意 | `family_even_square_counterexample` | 法4では二乗合同だけで格子同型を判定できない具体例 |
| GK型の具体的反例 | `Fibers.regular_integral_isometry_distinct_mutation_orbits` | `F(9,0)`と`F(6,3)`は同じ整数格子であり、別の符号付き変異軌道 |
| 合成数総量の分離例 | `CompositeFamily.composite_lattice_and_gcd_do_not_determine_mutation_orbit` | `F(14,1)`と`F(11,4)`は同一格子・同一gcdだが別軌道。法15の閉集合を全生成子で検証 |
| familyの一般変異一意性 | `FamilyUniqueness.normalized_positive_totals_reachable_iff` | 任意の正の総量について、正規化した二つのfamilyが変異同値であることと、総量・パラメータの一致が同値。素数・合成数・偶数を含み、全分類の仮定は不要 |
| family内の有限候補数 | `FamilyFiberFinite` | 正規化した同一格子のfamily候補は一般に有限で個数`≤m/2+1`。奇数法では実平方根の符号商と全単射、`2#候補=#根+ε` |
| family由来の実ファイバー部分 | `FamilyOrbitFibers` | 全解の真の忘却ファイバー内で、正規化familyを持つ軌道の部分集合を候補集合と全単射にし、候補数と同数の相異なる実軌道が存在することを証明 |
| 奇素数冪の正確な個数と下界 | `FamilyOrbitFibers.primePower_zero_familyPart_card`, `primePower_zero_solution_forgetful_fiber_injection` | 法`p^(2e)`の平方零格子でfamily由来部分は厳密に`(p^e+1)/2`。全解のファイバーへ同じ個数の単射を構成。`NegativeFamilyOrbitFibers`で全体との同一視も無条件に完成 |
| ファイバーの非有界性 | `Unbounded.unbounded_isometry_fibers` | 任意の自然数`n`に対し、同じ階数4整数格子に属する`n+1`個の相異なる正則変異軌道 |
| 忘却写像自体 | `unbounded_solutionForgetfulMap_fibers` | 解集合上の真の商と忘却写像を定義し、そのファイバーへ`Fin(n+1)`が単射で入る |
| 正則型の核旗 | `solution_regular_flag`, `solution_regular_integral_flag` | 任意の正則解の整数・有理核次元1,2,3、像次元3,2,1、核の飽和性・直和分裂 |
| 原始的な適合旗 | `solution_regular_primitive_coordinates` | 任意の正則解で原始的な`p,ℓ`と正の`κ`を選び、`(r,d)`の全射性を証明 |
| 適合整数基底と内在式 | `IntrinsicFrame` | 任意の正則解で整数基底・整数`A≠0`を構成。`N³=2Aκ²p⊗r`、`δ=2|A|κ²`、普遍RR公式を証明 |
| 内在的不変量の一意性 | `IntrinsicUnique` | 全正則解の`(A,κ)`が旗・基底選択に依存せず、任意の整数Euler格子同型・変異で保存 |
| 実対角合同 | `IntrinsicSignature` | 有理・実の可逆行列によって`H`を`diag(2,-2,-2A,0)`へ合同。対角の正・負・零成分数を検証 |
| 三型の内在的分離 | `latticeEquivalent_intrinsicKind` | 方程式の解集合上で、退化・正・負の整数判定が任意の格子同型と変異で保存 |
| familyの内在量 | `FamilyIntrinsic.family_frame_invariants` | 総量`m>0`の族の全ての適合基底で`A=-1`, `κ=m`。具体的な原始旗も構成 |
| 内在的な正負判定 | `IntrinsicSigns` | `adj(H)=2Aκ²ppᵀ`、第三主小行列式の和と`A`の符号の同値、符号の基底選択独立性 |
| 旗上の線形形式 | `Intrinsic` | `Np=0`, `Nℓ=-κp`を満たすデータから、Euler対による`r,d`とSerre変換式を導出 |
| 半回転とClifford関係 | `HalfTurns` | 有理2×2行列の行列式・平方・反交換子・整数トレースの式 |
| 有限整数環の不変格子 | `IntegralOrder` | `M₂(ℚ)`内の有限生成整数部分代数から、階数2の不変な整数格子と共通の有理整数化基底を構成 |
| 退化型の完全分類 | `degenerate_classification`, `degenerate_latticeEquivalent_iff_reachable` | 任意の退化解が唯一の`F(k,-k)`, `k≥0`へ到達し、退化型では変異同値と整数格子同型が一致 |
| 退化格子上の全ファイバー | `DegenerateFibers.degenerate_fiber_card` | 任意の退化解の格子について、全解の真の忘却ファイバーが一元集合で、個数が厳密に1 |
| 退化型の二つのJordan階数 | `DegenerateJordan.degenerate_classification_with_rank` | 任意退化解の唯一の正規化パラメータに対し、有理Serre階数はk=2で1、他で2。二乗零と合わせて[2,1,1]・[2,2]を区別 |
| 偶Clifford環 | `CliffordOrder.even_word_eq_sum` | 任意の非可換環の四生成子でClifford関係から偶語を8単項式の整数線形結合へ帰着し、有限生成環の積閉性を証明 |
| 正向きの共通整数化 | `RationalClifford.normalized_even_words_integral_SL2_positive_conjugation` | `NormedClifford.Data`または正の有理数`A`と、`rᵢ≠0`・整数pairingを含むRRデータから、全偶語を共通の正行列式有理共役で`SL₂(ℤ)`へ移す |
| 有限置換の完全分類 | `IndexTwelve.arbitrary_beta_census_unique` | 任意の固定点なし対合・三次置換対で、語による推移性と、高々二つの巡回軌道による全12頂点の被覆から、五つの同時共役類の存在と一意性 |
| 生成反射群の共役不変性 | `ReflectionGroup.reachable_reflectionGroup_isometric_conjugate` | 変異同値なら、四つの実整数鏡映が生成する真の部分群は整数Euler等長共役。反射群を単なる形式ラベルとして扱わない |
| 基底変異と実鏡映 | `basisWord_reflection_hurwitz` | 全生成子・任意の有限語で、実際の整数基底変異と反射のHurwitz操作が対応 |
| 正側の実整数部分群 | `PositiveGroups.positive_solution_integer_projective_subgroup` | 任意正側解の実偶語群Δを、共通共役の後で実PSL₂(ℤ)部分群と同一視。個別半回転を整数化せず、指数12は主張しない |
| 正側の正符号正規化 | `PositiveNormalization`, `PositiveHeightNormalization` | actual適合基底のrankを正にする明示符号語で、全六辺≥3へ正規化しL1高さを保持。任意二根のpairing≥3も幾何仮定なしに証明 |
| 正側の有界完全分類 | `PositiveBounded.positive_solution_bounded_classification` | 任意符号の正側解でL1≤37なら、五代表の唯一の実変異軌道へ到達。正符号23点の網羅性、210ブロックのkernel計算、実語を全て証明 |
| 正側の整数三角形制約 | `PositiveTriangleLower.chamber_all_triangle_bounds` | 任意正側の整数正符号解で、全四三角形の平方和−積は−7以下。二辺3のmod27排除と実変異による三角形高さの強帰納法を使用。短語局所最小の仮定なし |
| 全長の正符号領域保存 | `PositiveChamber` | 任意正側解は正則で全辺の絶対値が3以上。正符号領域は任意長のbraid語で保存され、L1高さは六辺の和に一致 |
| 正側の短語不下降の代数式 | `PositiveShortWord` | 任意短語の不下降と具体的な高さ多項式の同値、二手不下降から八つのbalance不等式を導出。全称の高さ上界はまだ結論しない |
| 正側の小辺断面の完全分類 | `PositiveSmallThreeTerminal`, `PositiveFourFourChecks`, `PositiveFourFiveChecks`, `PositiveFiveFiveCensus` | 正符号領域と二手不下降から、隣接辺3/4・3/5・4/4・4/5・5/5の全整数係数を有限に抑え、実際の五代表へ到達。初期高さ上界なし |
| 先頭辺3の追加断面 | `PositiveThreeTerminalUpToEight` | a=3またはf=3、d≤8の全二手終端点を五代表へ一意分類。d=6,7の全有限候補とd=8の不存在を網羅的に検証。d≤8は明示的な地域制限 |
| 順序付き先頭辺4の完全分類 | `PositiveSortedFour` | a=4,d≤c,f≥4の三手不下降点はd≤5。d≥4なら既存4/4・4/5の完全列挙を通して五代表へ一意分類。巨大有理係数の非負恒等式をLeanで検証 |
| 順序付き先頭辺5の境界排除 | `PositiveSortedFiveBoundary` | 最小外辺がa=5の二手不下降点ではd,f≥6。d=5は5/5列挙、f=5は反対辺の全列挙と23点表で排除。残る無界領域の不存在はまだ未証明 |
| 五代表の内在的な表 | `PositiveRepresentativeInvariants` | 各代表に実原始旗と整数frameを明示構成し、任意frameでA=[2,3,5,11,1],κ=[4,3,2,1,6]を証明。contentだけから推測しない |
| 正側の小さい反対辺の完全分類 | `PositiveEndpointBounds`, `PositiveSmallEndpointCensus` | 反対辺a,fが各3〜5で一手不下降なら、他四辺の和は配置別35,36,40,48,63以下。全9配置・468有限証明書と網羅性を検証し、二手不下降から総和≤37と五軌道の一意分類へ接続 |
| 正側の順序付き最小点への帰着 | `PositiveSortedTerminal.positive_solution_sorted_terminal_reduction`, `PositiveReverseOrbits` | 任意正側解の五代表への到達性を保持し、任意長不下降・最小外辺が先頭・次辺≤他隣接辺を満たす点へ帰着。反転点への到達仮定は置かず、五反転代表の実語を証明して移送 |
| 任意負側二格子の完全判定 | `NegativeLatticeCriterion.negative_orbit_and_lattice_criteria` | 任意の負側二解から正規化代表を構成し、変異同値とパラメータ等号、整数Euler格子同型と同時合同式の必要十分条件を無条件に移送 |
| 正側の実放物元 | `PositiveParabolicTrace.actual_even_group_parabolic` | 正側の実半回転四つの積のtrace²=4・det1・射影的非自明性と、真の偶語群への所属を無条件に証明。有限指数値は結論しない |
| 正側の階数・次数制約 | `PositiveRankDescent` | 正階数frameの原始核符号交代、endpoint wedge平方一致、整数零欠陥排除、実q2とのpfaffian等式とendpoint和・差の公式を全称に証明。全称下降は結論しない |
| 正側の整数欠損とpfaffian制約 | `PositivePfaffianSign` | 正の整数RR対の欠損からpairing上界を導き、q2=+4ならκ+1≤|C01|とAκ²+Aκ≤|a−f|。一般の+4排除は結論しない |
| 全分類の統合と停止する探索 | `FullClassificationPipeline`, `ClassificationDecision` | 正側の一般存在を明示引数として、三型の正規形と商の全単射・全ファイバー有限性へ接続。全10生成子の有限語探索をNat.findで停止させ、正規形と実語、同値判定Bool、接続語Optionを実装。正側引数はまだ無条件に供給していない |
| 正側一手下降の無限障害と二手下降 | `PositiveLocalMinima` | 任意高さを超える正側一手局所最小の無限族を証明し、その族には二手の普遍下降語も構成 |
| 正側基底から整数化まで | `PositiveIntegral.positive_frame_even_words_integral_SL2` | `A>0`の任意の実際の適合基底から、追加の整数環仮定なしに全偶語の共通正向き整数化を証明 |
| 正側解から半回転データ | `IntrinsicFrame.positiveHalfTurnData` | 任意の適合整数基底で`A>0`なら全基底rankが非零となり、実際のpairingから`NormedClifford.Data`を構成 |
| 負側の局所下降への帰着 | `NegativeDescent` | 全称の`LocalDescentProperty`を259語と有限符号選択による多項式命題へ厳密帰着し、それを仮定すれば真の整礎帰納法で負側全射性を証明。局所命題自体は未証明 |
| 負側の無条件完全分類 | `NegativeClassificationFull.negative_classification`, `negative_classification_with_invariants` | 任意負側整数解について、正規化familyへの実到達と一意性、全適合基底で`A=-1,κ=x+y`を無条件に証明。全座標分割と無制限の実語による高さ強帰納を使用 |
| 全負側ファイバー公式 | `NegativeFamilyOrbitFibers` | 真の全解の忘却ファイバーと有限候補集合の全単射、全正法の有限性と個数上界、奇数法の完全積公式、素数平方冪の厳密個数を無条件に証明 |
| 負側の全大辺下降 | `NegativeLargeDescent.negative_all_large_word_descent` | 任意の負側解で全六辺の絶対値が3以上なら、符号正規化・全符号chamber・全最大辺位置を通し、二手以内の実braid語による厳密L1下降を無条件に証明 |
| 負側の三境界への全称帰着 | `NegativeSmallReduction`, `NegativeAdjacentReduction` | genuine強帰納法と実braidで、任意負側解を第一辺が0・1・2のいずれかの負側解へ移す。LocalDescentPropertyの仮定なし |
| 負側の境界部分証明 | `NegativeBoundary` | 零辺二つの全15配置からfamilyへ到達。第一辺0・他五辺abs≥3なら二手下降。第一辺±2で隣接係数が等しい／反対ならEuclid型変異でfamilyへ到達 |
| 負側の全abs≥2帰着 | `NegativeAtLeastTwoReduction.negative_atLeastTwo_reduction` | 全六辺の絶対値が2以上なら、全符号・全位置でfamilyへの実到達、または元のL1高さからの厳密下降。全分類の仮定なし |
| 負側の零・単位境界への強帰納 | `NegativeTinyReduction.negative_reachable_tiny_or_family` | 任意負側解はfamilyへ到達するか、元以下の高さで零辺または単位辺を持つ実負側解へ到達 |
| 負側の四位置の零辺完全帰着 | `NegativeZeroOffdiagonal.offdiagonal_zero_family_or_drop` | `a,c,d,f`のいずれかが零なら、他五係数に制限なくfamilyへ到達、または元のL1高さから厳密下降。反対辺abs0・1・2・≥3の全分岐を証明 |
| 負側の全零辺帰着 | `ZeroUnitConic.zero_edge_family_or_drop` | 六位置の任意の零辺から、他五整数係数に条件なく実family到達または元の全高さからの厳密下降。Pell型の二次方程式は真の変異語と強帰納で解決 |
| 単位辺を持つ全境界 | `NegativeSingleUnitTwo`, `NegativeDoubleUnitReduction`, `BoundaryPatterns` | 孤立単位辺の全六位置、二単位辺の全15組、零辺との重なりを全て無条件に帰着。整数六つ組の網羅分割を証明 |
| 負側の孤立単位辺下降 | `NegativeUnitEdge.unit_edge_word_drop` | 第一辺abs1、他五辺abs≥3なら、全符号で二手以内の厳密L1下降 |
| 小さい単位三角形 | `NegativeUnitSmall` | 全四位置のsigned単位境界三角形からfamilyへ到達。第一三角形の二辺abs1・第三辺abs≤2ならfamily到達または厳密下降。残り三係数に制限なし |
| 実変異による巡回置換 | `CyclicMutation` | 三手のbraid語が純粋な座標置換となり、L1高さ・解・内在符号を保存。位置を移す際の高さ増加を避ける実操作を構成 |
| 全位置のsigned affine三角形 | `AffineTriangles.affine_triangle_reachable_family` | 三辺abs2・積8の任意の実三角形からfamilyへ到達。他三係数と内在符号に条件なし |
| 各三角形の原始的制約 | `TriangleDivisors` | 解の各三角形に共通する任意の整数約数は4を割る。無界の整除定理 |
| 負側の三角形不等式 | `NegativeTriangles` | 全負側解で各主三次小行列式が非正、各三角形の`平方和−積≥4`を証明。正の積と最大辺条件の下で符号付きVieta更新が厳密に縮む。全六辺を同時に下げる変異の存在は別の命題 |
| 鏡の代数式 | `NegativeMirror` | 階数零の例外ベクトルがあれば`A=-1`・次数`±1`。ノルム条件から鏡の円方程式、非零整数rankの高さ上界を証明 |
| PSL₂(ℤ)の真正の提示同型 | `ModularPingPong.presentationPSLEquiv` | 整数EuclidによるS,T生成、中心±I、自由積正規形とping-pongから、提示群と実際のPSL₂(ℤ)の群同型を無条件に証明 |
| 実PSL₂(ℤ)の部分群分類 | `ModularPSLCensus.subgroup_census_unique` | 任意の実PSL₂(ℤ)部分群について、指数12・S,R固定点なし・T高々二巡回軌道を明示条件として五共役類へ一意分類。各実代表の条件充足と非共役も証明 |
| 重複列からの帰着 | `coincident_columns_reachable_family` | 対称Gram行列の任意の二列が等しいか符号反対なら、実際の変異語で族へ帰着 |
| 五つの整数Gram代表の分離 | `PositiveRepresentatives` | 原稿の五代表の方程式・正則性・cube content `64,54,40,22,72`を検証し、格子同型・変異の非同値を証明 |
| 三型を合わせた代表の一意性 | `CanonicalRepresentatives.representatives_reachable_iff` | 退化・正規化負族・五正代表を合わせた代表集合で、実到達とラベルの等号が同値。真の解軌道集合への単射を構成。一般全射性は主張しない |
| CRTの根数積公式 | `ChineseRoots.squareRoots_card_mul` | 互いに素な法の実際の平方根集合に全単射を構成し、根数の積公式を証明 |
| 単位平方の素数冪根 | `UnitPrimePowerRoots` | 奇素数`p`、指数`e>0`、`p∤y`なら法`p^e`の根はちょうど`±y`、個数2 |
| 素数冪の全局所根数 | `LocalRootFormula`, `PrimePowerZeroGeneral`, `PrimePowerNonzeroRoots` | 任意の奇素数・非負指数・整数パラメータについて、零・高付値・非零非単位・単位の全分岐を証明。平方零は素数2も含む |
| 奇数法の一般積公式 | `RootProductFormula`, `FamilyOrbitFibers.odd_familyPart_card` | 任意の正の奇数法と整数パラメータについて、素因数分解の局所根数の積、符号商、family由来実軌道数の完全な式を証明 |
| 五つの置換代表 | `IndexTwelve` | 対合・三巡回、実際の語による推移性、二カスプの巡回分解と幅 |

## 非有界性の構成

`m=3^(2n)`を取り、`y=0`および`y=3^(n+j)`（`0≤j<n`）の`n+1`個の解`F(m-y,y)`を使う。二乗の合同と明示的な行列から、すべて同じ格子であることを示す。一方、3の異なる冪による整除性と、変異で保存されるmatching supportで、全ての組の非到達性を示す。全分類、双曲幾何、反射基本領域の定理は使わない。

`n=1`では原稿の`F(9,0)`と`F(6,3)`を再現する。`n=2`では総量81の三軌道を保証する。原稿の正確なファイバー個数公式を仮定した証明ではない。

## 全分類に残る証明義務

負側の一般存在と一意性は`NegativeClassificationFull`で完成し、任意負側解の格子上の全ファイバーの有限性も`NegativeFiberFiniteGeneral`で証明した。全負側ファイバーの有限性と正確な式も`NegativeFamilyOrbitFibers`へ無条件に接続した。主分類に残る中心的な証明義務は**正側を有界領域へ移すこと**である。任意正側解が実変異語でL1≤37の正符号領域に到達することを証明する必要がある。`PositiveReduction.positive_classification_iff_bounded_reduction`は、これが五軌道の一般分類と同値であることを証明するが、どちら側も未証明の仮定として採用していない。正符号正規化、任意長の領域保存、有界23解の網羅性と実語、五代表の非同値は完成している。

`PositiveMinimalOrbit`は全ての正側軌道に実際の最小高さの正符号解が存在し、任意長のbraid語に対して不下降であることを証明する。ただし最小高さの数値上界は結論していない。`PositiveSmallThreeTerminal`、`PositiveFourFourChecks`、`PositiveFiveFiveCensus`では、短語の不下降と特定の小辺配置から、残りの全係数の有限上界と当該断面の五軌道分類を追加の高さ仮定なしに証明した。`PositiveEndpointBounds`では反対辺が各3〜5の全配置に、四つの一手guardの積による普遍多項式証明書から有限上界を与え、`PositiveSmallEndpointCensus`で全9配置を五軌道へ一意分類した。`PositiveSortedTerminal`は五代表への到達性を保持しつつ、外辺の順序を整えた全長不下降点へ問題を帰着する。これら特定断面の分類と順序帰着だけでは、任意の正側解の一般分類は完成しない。

正側では原稿の固有写像・正の次数・面積・凸四角形から指数12へ進む幾何的経路も残る。偶語群Δの実PSL₂(ℤ)部分群への整数化、PSL₂(ℤ)の提示同型と五部分群分類は完成したが、任意正側解のΔが指数12・固定点なし・二カスプ条件を満たすことと、拡大Γから実変異を復元する部分は未証明である。直接の有界帰着を完成できれば主分類についてこの幾何的経路を置き換えられる。

familyの一般変異一意性、全奇数法の局所根数・CRT積公式・符号商とfamily由来実軌道数、偶数法も含む候補有限性は証明済みである。`NegativeFamilyOrbitFibers`では一般全射性を使い、明示的な下降仮定を除いて全ファイバーの有限性・正確な式へ接続した。退化格子の全ファイバー個数1と、全解のファイバーの非有界性は既に無条件に証明済みである。

単純な一手L1高さ下降法には、全生成子で高さが下がらない負側正則解が存在する。`DescentTrap.lean`でその具体例と到達語を証明した。三手下降の一般仮説には有限探索の根拠があるが、これは普遍定理として採用していない。`NegativeDescent.LocalDescentProperty`として正確な未証明命題を定義した。重複・反対列の全てがない負側解について、259通りの長さ3以下のbraid語のどれかがL1高さを下げる、という全称の整数多項式不等式と同値である。`local_descent_implies_negative_family_surjectivity`はこの命題を仮定する帰着補題であり、その旧API自体は仮定のない負側全射性の定理ではない。無条件の主分類は、別の`NegativeClassificationFull`で、語長を制限しない実下降の全座標分割によって完成した。

合成数の族で`y`を法`m=x+y`から符号を除いて復元する別案も、一般には失敗する。`CompositeFamily.mod25_parameter_change`と`mod35_parameter_change`は、`y′≢±y`なのに同じ法上で変異語が到達する具体例を検証する。これは整数上の到達性を主張せず、当該の合同不変量だけでは一般一意性を証明できないことを示す。一般一意性自体は、三次元の実整数反射表現・自由積の語の一意性・反射根の復元を使う別の代数証明で完成した（`UniversalWord`, `UniversalReflection`, `ReflectionRoots`, `FamilyReflectionBridge`, `FamilyReflectionWords`, `FamilyUniqueness`）。したがって原稿のfamily一意性の幾何的議論を形式化の前提にしていない。

このリストは単なる記述上の未完成ではなく、全分類を結論するLean定理に必要な未証明箇所である。有限表の完全列挙だけから、任意の正側の解の分類は結論していない。

## 実行と信頼境界

Lean4.24.0・mathlib v4.24.0を固定。公開モジュールを実際にコンパイルし、`AxiomAudit.lean`で定理・定義と推移的な依存の公理を監査する。許可するのはLeanの標準公理`propext`, `Classical.choice`, `Quot.sound`のみ。`sorry`、原稿の定理を追加した公理、`native_decide`には依存しない。

有限列挙のPythonコードは証明書の生成器であり、信頼境界に入らない。Leanが有限計算の正しさと列挙の網羅性をそれぞれ証明する。

原稿の独立精査では具体的な反例や修正不能と確定した数学的誤りは見つかっていない。これは全分類の形式化完了を意味しない。残る普遍的下降命題と幾何的証明を「克服不能」と断定する根拠も現時点ではない。
