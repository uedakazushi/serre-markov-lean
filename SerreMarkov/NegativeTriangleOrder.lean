import SerreMarkov.NegativeTriangles

/-! # Separation of the largest edge in negative Cayley triangles

The estimates hold for arbitrary integers satisfying the triangle defect
inequality. They supply strict ordering information for simultaneous
six-coordinate descent, without assuming that such a descent exists.
-/

namespace SerreMarkov.NegativeTriangleOrder

open NegativeTriangles

theorem sorted_triangle_max_gap (u v w : ℤ)
    (hu : 3 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hc : 4 ≤ cayleyDefect u v w) : 3*v < 2*w := by
  have hp := cayley_sorted_product_lt_twice u v w hu huv hvw hc
  have hv : 0 ≤ v := by omega
  have hm : 3*v ≤ u*v := mul_le_mul_of_nonneg_right hu hv
  omega

theorem sorted_triangle_max_separated (u v w : ℤ)
    (hu : 3 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hc : 4 ≤ cayleyDefect u v w) : v+2 ≤ w := by
  have hg := sorted_triangle_max_gap u v w hu huv hvw hc
  omega

theorem positive_triangle_max_gap (u v w : ℤ)
    (hu : 3 ≤ u) (hv : 3 ≤ v) (hmax : u ≤ w ∧ v ≤ w)
    (hc : 4 ≤ cayleyDefect u v w) : 3*max u v < 2*w := by
  rcases le_total u v with huv | hvu
  · simpa [max_eq_right huv] using sorted_triangle_max_gap u v w hu huv hmax.2 hc
  · have hc' : 4 ≤ cayleyDefect v u w := by
      simpa [cayleyDefect, mul_comm, add_comm] using hc
    simpa [max_eq_left hvu] using sorted_triangle_max_gap v u w hv hvu hmax.1 hc'

theorem positive_triangle_max_unique (u v w : ℤ)
    (hu : 3 ≤ u) (hv : 3 ≤ v) (hmax : u ≤ w ∧ v ≤ w)
    (hc : 4 ≤ cayleyDefect u v w) : u < w ∧ v < w := by
  have hg := positive_triangle_max_gap u v w hu hv hmax hc
  have hm1 := le_max_left u v
  have hm2 := le_max_right u v
  omega

theorem signed_triangle_max_gap (u v w : ℤ)
    (hu : 3 ≤ |u|) (hv : 3 ≤ |v|)
    (hmax : |u| ≤ |w| ∧ |v| ≤ |w|) (hprod : 0 ≤ u*v*w)
    (hc : 4 ≤ cayleyDefect u v w) : 3*max |u| |v| < 2*|w| := by
  have hc' : 4 ≤ cayleyDefect |u| |v| |w| := by
    rw [cayleyDefect_abs_of_product_nonneg u v w hprod]
    exact hc
  exact positive_triangle_max_gap |u| |v| |w| hu hv hmax hc'

end SerreMarkov.NegativeTriangleOrder
