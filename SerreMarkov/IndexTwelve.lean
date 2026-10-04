import Mathlib.Data.Fintype.Basic

/-!
# Exact certificates for the five index-twelve representative pairs

Vertices are numbered 0 through 11.  Each representative is exactly the pair
in Table 2 of the v4 manuscript after subtracting 1 from its printed labels.
The proofs below are kernel reductions (`decide`), not native evaluation.

Scope: the five stated pairs are transitive and have the asserted two cusp
cycles.  This module does not assert completeness of the 10,395-matchings census,
the modular-subgroup classification, or the global Serre–Markov classification.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace SerreMarkov.IndexTwelve

abbrev Vertex := Fin 12
abbrev VertexMap := Vertex → Vertex

/-- The fixed permutation `(0 1 2)(3 4 5)(6 7 8)(9 10 11)`. -/
def beta (i : Vertex) : Vertex :=
  match i.val with
  | 0 => 1 | 1 => 2 | 2 => 0
  | 3 => 4 | 4 => 5 | 5 => 3
  | 6 => 7 | 7 => 8 | 8 => 6
  | 9 => 10 | 10 => 11 | _ => 9

/-- The cusp permutation is alpha composed with beta. -/
def cusp (alpha : VertexMap) (i : Vertex) : Vertex := alpha (beta i)

/-- A word acts from left to right; false applies alpha, true applies beta. -/
def evalWord (alpha : VertexMap) (word : List Bool) (start : Vertex) : Vertex :=
  word.foldl (fun current bit => if bit then beta current else alpha current) start

/-- An actual generator word joining two vertices. -/
def Reachable (alpha : VertexMap) (x y : Vertex) : Prop :=
  ∃ word : List Bool, evalWord alpha word x = y

/-- Positive words for inverse actions; beta inverse is beta squared. -/
def inverseWord (word : List Bool) : List Bool :=
  word.reverse.flatMap (fun bit => if bit then [true, true] else [false])

/-- Every ordered pair of vertices is joined by an actual generator word. -/
def TransitivePair (alpha : VertexMap) : Prop :=
  ∀ x y : Vertex, Reachable alpha x y

/-- Consecutive edges of a finite list, including the closing edge. -/
def cycleEdges (points : List Vertex) : List (Vertex × Vertex) :=
  points.zip (points.drop 1 ++ points.take 1)

/-- A nonempty simple cycle with the stated cyclic order. -/
def FormsCycle (p : VertexMap) (points : List Vertex) : Prop :=
  points ≠ [] ∧ points.Nodup ∧
  ∀ edge ∈ cycleEdges points, p edge.1 = edge.2

/-- Two disjoint simple cycles exhausting all twelve vertices. -/
def TwoCycleDecomposition (p : VertexMap) (left right : List Vertex) : Prop :=
  FormsCycle p left ∧ FormsCycle p right ∧ (left ++ right).Nodup ∧
  ∀ i : Vertex, i ∈ left ++ right

theorem beta_order_three : ∀ i : Vertex, beta (beta (beta i)) = i := by decide

theorem beta_fixed_point_free : ∀ i : Vertex, beta i ≠ i := by decide

/-- A function with a proved involution law is an actual permutation. -/
def involutionPerm (a : VertexMap) (h : ∀ i, a (a i) = i) : Equiv.Perm Vertex :=
  { toFun := a, invFun := a, left_inv := h, right_inv := h }

/-- The fixed three-cycle permutation, with its inverse proved in the kernel. -/
def betaPerm : Equiv.Perm Vertex :=
  { toFun := beta
    invFun := fun i => beta (beta i)
    left_inv := beta_order_three
    right_inv := beta_order_three }

def alphaOneEleven (i : Vertex) : Vertex :=
  match i.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 6
  | 5 => 9
  | 6 => 4
  | 7 => 10
  | 8 => 11
  | 9 => 5
  | 10 => 7
  | _ => 8

def alphaOneElevenPath (i : Vertex) : List Bool :=
  match i.val with
  | 0 => []
  | 1 => [false]
  | 2 => [false, true]
  | 3 => [false, true, false]
  | 4 => [false, true, false, true]
  | 5 => [false, true, false, true, true]
  | 6 => [false, true, false, true, false]
  | 7 => [false, true, false, true, false, true]
  | 8 => [false, true, false, true, false, true, true]
  | 9 => [false, true, false, true, true, false]
  | 10 => [false, true, false, true, false, true, false]
  | _ => [false, true, false, true, false, true, false, true]

def alphaOneElevenCycleLeft : List Vertex := [0]
def alphaOneElevenCycleRight : List Vertex := [1, 3, 6, 10, 8, 4, 9, 7, 11, 5, 2]

theorem alphaOneEleven_involutive : ∀ i : Vertex, alphaOneEleven (alphaOneEleven i) = i := by decide

theorem alphaOneEleven_fixed_point_free : ∀ i : Vertex, alphaOneEleven i ≠ i := by decide

theorem alphaOneEleven_path_certificate :
    ∀ i : Vertex, evalWord alphaOneEleven (alphaOneElevenPath i) 0 = i := by decide

theorem alphaOneEleven_all_paths_certificate :
    ∀ x y : Vertex,
      evalWord alphaOneEleven (inverseWord (alphaOneElevenPath x) ++ alphaOneElevenPath y) x = y := by
  decide

theorem alphaOneEleven_transitive : TransitivePair alphaOneEleven := by
  intro x y
  exact ⟨inverseWord (alphaOneElevenPath x) ++ alphaOneElevenPath y,
    alphaOneEleven_all_paths_certificate x y⟩

theorem alphaOneEleven_cusp_decomposition :
    TwoCycleDecomposition (cusp alphaOneEleven) alphaOneElevenCycleLeft alphaOneElevenCycleRight := by
  unfold TwoCycleDecomposition FormsCycle
  decide

theorem alphaOneEleven_cusp_widths :
    alphaOneElevenCycleLeft.length = 1 ∧ alphaOneElevenCycleRight.length = 11 := by decide

def alphaTwoTen (i : Vertex) : Vertex :=
  match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 6
  | 3 => 0
  | 4 => 1
  | 5 => 9
  | 6 => 2
  | 7 => 11
  | 8 => 10
  | 9 => 5
  | 10 => 8
  | _ => 7

def alphaTwoTenPath (i : Vertex) : List Bool :=
  match i.val with
  | 0 => []
  | 1 => [true]
  | 2 => [true, true]
  | 3 => [false]
  | 4 => [false, true]
  | 5 => [false, true, true]
  | 6 => [true, true, false]
  | 7 => [true, true, false, true]
  | 8 => [true, true, false, true, true]
  | 9 => [false, true, true, false]
  | 10 => [false, true, true, false, true]
  | _ => [true, true, false, true, false]

def alphaTwoTenCycleLeft : List Vertex := [0, 4, 9, 8, 2, 3, 1, 6, 11, 5]
def alphaTwoTenCycleRight : List Vertex := [7, 10]

theorem alphaTwoTen_involutive : ∀ i : Vertex, alphaTwoTen (alphaTwoTen i) = i := by decide

theorem alphaTwoTen_fixed_point_free : ∀ i : Vertex, alphaTwoTen i ≠ i := by decide

theorem alphaTwoTen_path_certificate :
    ∀ i : Vertex, evalWord alphaTwoTen (alphaTwoTenPath i) 0 = i := by decide

theorem alphaTwoTen_all_paths_certificate :
    ∀ x y : Vertex,
      evalWord alphaTwoTen (inverseWord (alphaTwoTenPath x) ++ alphaTwoTenPath y) x = y := by
  decide

theorem alphaTwoTen_transitive : TransitivePair alphaTwoTen := by
  intro x y
  exact ⟨inverseWord (alphaTwoTenPath x) ++ alphaTwoTenPath y,
    alphaTwoTen_all_paths_certificate x y⟩

theorem alphaTwoTen_cusp_decomposition :
    TwoCycleDecomposition (cusp alphaTwoTen) alphaTwoTenCycleLeft alphaTwoTenCycleRight := by
  unfold TwoCycleDecomposition FormsCycle
  decide

theorem alphaTwoTen_cusp_widths :
    alphaTwoTenCycleLeft.length = 10 ∧ alphaTwoTenCycleRight.length = 2 := by decide

def alphaThreeNine (i : Vertex) : Vertex :=
  match i.val with
  | 0 => 3
  | 1 => 6
  | 2 => 9
  | 3 => 0
  | 4 => 7
  | 5 => 11
  | 6 => 1
  | 7 => 4
  | 8 => 10
  | 9 => 2
  | 10 => 8
  | _ => 5

def alphaThreeNinePath (i : Vertex) : List Bool :=
  match i.val with
  | 0 => []
  | 1 => [true]
  | 2 => [true, true]
  | 3 => [false]
  | 4 => [false, true]
  | 5 => [false, true, true]
  | 6 => [true, false]
  | 7 => [false, true, false]
  | 8 => [false, true, false, true]
  | 9 => [true, true, false]
  | 10 => [true, true, false, true]
  | _ => [false, true, true, false]

def alphaThreeNineCycleLeft : List Vertex := [0, 6, 4, 11, 2, 3, 7, 10, 5]
def alphaThreeNineCycleRight : List Vertex := [1, 9, 8]

theorem alphaThreeNine_involutive : ∀ i : Vertex, alphaThreeNine (alphaThreeNine i) = i := by decide

theorem alphaThreeNine_fixed_point_free : ∀ i : Vertex, alphaThreeNine i ≠ i := by decide

theorem alphaThreeNine_path_certificate :
    ∀ i : Vertex, evalWord alphaThreeNine (alphaThreeNinePath i) 0 = i := by decide

theorem alphaThreeNine_all_paths_certificate :
    ∀ x y : Vertex,
      evalWord alphaThreeNine (inverseWord (alphaThreeNinePath x) ++ alphaThreeNinePath y) x = y := by
  decide

theorem alphaThreeNine_transitive : TransitivePair alphaThreeNine := by
  intro x y
  exact ⟨inverseWord (alphaThreeNinePath x) ++ alphaThreeNinePath y,
    alphaThreeNine_all_paths_certificate x y⟩

theorem alphaThreeNine_cusp_decomposition :
    TwoCycleDecomposition (cusp alphaThreeNine) alphaThreeNineCycleLeft alphaThreeNineCycleRight := by
  unfold TwoCycleDecomposition FormsCycle
  decide

theorem alphaThreeNine_cusp_widths :
    alphaThreeNineCycleLeft.length = 9 ∧ alphaThreeNineCycleRight.length = 3 := by decide

def alphaFourEight (i : Vertex) : Vertex :=
  match i.val with
  | 0 => 3
  | 1 => 6
  | 2 => 9
  | 3 => 0
  | 4 => 7
  | 5 => 10
  | 6 => 1
  | 7 => 4
  | 8 => 11
  | 9 => 2
  | 10 => 5
  | _ => 8

def alphaFourEightPath (i : Vertex) : List Bool :=
  match i.val with
  | 0 => []
  | 1 => [true]
  | 2 => [true, true]
  | 3 => [false]
  | 4 => [false, true]
  | 5 => [false, true, true]
  | 6 => [true, false]
  | 7 => [false, true, false]
  | 8 => [false, true, false, true]
  | 9 => [true, true, false]
  | 10 => [false, true, true, false]
  | _ => [false, true, false, true, false]

def alphaFourEightCycleLeft : List Vertex := [0, 6, 4, 10, 8, 1, 9, 5]
def alphaFourEightCycleRight : List Vertex := [2, 3, 7, 11]

theorem alphaFourEight_involutive : ∀ i : Vertex, alphaFourEight (alphaFourEight i) = i := by decide

theorem alphaFourEight_fixed_point_free : ∀ i : Vertex, alphaFourEight i ≠ i := by decide

theorem alphaFourEight_path_certificate :
    ∀ i : Vertex, evalWord alphaFourEight (alphaFourEightPath i) 0 = i := by decide

theorem alphaFourEight_all_paths_certificate :
    ∀ x y : Vertex,
      evalWord alphaFourEight (inverseWord (alphaFourEightPath x) ++ alphaFourEightPath y) x = y := by
  decide

theorem alphaFourEight_transitive : TransitivePair alphaFourEight := by
  intro x y
  exact ⟨inverseWord (alphaFourEightPath x) ++ alphaFourEightPath y,
    alphaFourEight_all_paths_certificate x y⟩

theorem alphaFourEight_cusp_decomposition :
    TwoCycleDecomposition (cusp alphaFourEight) alphaFourEightCycleLeft alphaFourEightCycleRight := by
  unfold TwoCycleDecomposition FormsCycle
  decide

theorem alphaFourEight_cusp_widths :
    alphaFourEightCycleLeft.length = 8 ∧ alphaFourEightCycleRight.length = 4 := by decide

def alphaSixSix (i : Vertex) : Vertex :=
  match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 6
  | 3 => 0
  | 4 => 1
  | 5 => 9
  | 6 => 2
  | 7 => 10
  | 8 => 11
  | 9 => 5
  | 10 => 7
  | _ => 8

def alphaSixSixPath (i : Vertex) : List Bool :=
  match i.val with
  | 0 => []
  | 1 => [true]
  | 2 => [true, true]
  | 3 => [false]
  | 4 => [false, true]
  | 5 => [false, true, true]
  | 6 => [true, true, false]
  | 7 => [true, true, false, true]
  | 8 => [true, true, false, true, true]
  | 9 => [false, true, true, false]
  | 10 => [false, true, true, false, true]
  | _ => [false, true, true, false, true, true]

def alphaSixSixCycleLeft : List Vertex := [0, 4, 9, 7, 11, 5]
def alphaSixSixCycleRight : List Vertex := [1, 6, 10, 8, 2, 3]

theorem alphaSixSix_involutive : ∀ i : Vertex, alphaSixSix (alphaSixSix i) = i := by decide

theorem alphaSixSix_fixed_point_free : ∀ i : Vertex, alphaSixSix i ≠ i := by decide

theorem alphaSixSix_path_certificate :
    ∀ i : Vertex, evalWord alphaSixSix (alphaSixSixPath i) 0 = i := by decide

theorem alphaSixSix_all_paths_certificate :
    ∀ x y : Vertex,
      evalWord alphaSixSix (inverseWord (alphaSixSixPath x) ++ alphaSixSixPath y) x = y := by
  decide

theorem alphaSixSix_transitive : TransitivePair alphaSixSix := by
  intro x y
  exact ⟨inverseWord (alphaSixSixPath x) ++ alphaSixSixPath y,
    alphaSixSix_all_paths_certificate x y⟩

theorem alphaSixSix_cusp_decomposition :
    TwoCycleDecomposition (cusp alphaSixSix) alphaSixSixCycleLeft alphaSixSixCycleRight := by
  unfold TwoCycleDecomposition FormsCycle
  decide

theorem alphaSixSix_cusp_widths :
    alphaSixSixCycleLeft.length = 6 ∧ alphaSixSixCycleRight.length = 6 := by decide

/-- The five *certified representatives* have five different unordered width pairs.
This is a statement about this finite table, not an exhaustive census theorem. -/
theorem width_pairs_distinct :
    ([([1, 11] : List Nat), [2, 10], [3, 9], [4, 8], [6, 6]]).Nodup := by decide

def alphaOneElevenPerm : Equiv.Perm Vertex :=
  involutionPerm alphaOneEleven alphaOneEleven_involutive

def alphaTwoTenPerm : Equiv.Perm Vertex :=
  involutionPerm alphaTwoTen alphaTwoTen_involutive

def alphaThreeNinePerm : Equiv.Perm Vertex :=
  involutionPerm alphaThreeNine alphaThreeNine_involutive

def alphaFourEightPerm : Equiv.Perm Vertex :=
  involutionPerm alphaFourEight alphaFourEight_involutive

def alphaSixSixPerm : Equiv.Perm Vertex :=
  involutionPerm alphaSixSix alphaSixSix_involutive

end SerreMarkov.IndexTwelve
