import SerreMarkov.Mutations

/-! # Primitive restrictions on every pairing triangle

The quadratic Pfaffian equation forces every common integer divisor of
the three edges of any triangle to divide four. This is an unbounded
arithmetic statement, independent of mutation classification.
-/

namespace SerreMarkov.TriangleDivisors

private theorem divisor_of_q2 (z : Six) (hz : isSolution z) (n : ℤ)
    (hn : n ∣ q2 z) : n ∣ 4 := by
  have hq : q2 z=4 ∨ q2 z= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  rcases hq with hq | hq
  · simpa only [hq] using hn
  · simpa only [hq, dvd_neg] using hn

theorem triangle_abd_divisor (z : Six) (hz : isSolution z) (n : ℤ)
    (ha : n ∣ z.a) (hb : n ∣ z.b) (hd : n ∣ z.d) : n ∣ 4 := by
  apply divisor_of_q2 z hz n
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_left ha z.f) (dvd_mul_of_dvd_left hb z.e))
    (dvd_mul_of_dvd_right hd z.c)

theorem triangle_ace_divisor (z : Six) (hz : isSolution z) (n : ℤ)
    (ha : n ∣ z.a) (hc : n ∣ z.c) (he : n ∣ z.e) : n ∣ 4 := by
  apply divisor_of_q2 z hz n
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_left ha z.f) (dvd_mul_of_dvd_right he z.b))
    (dvd_mul_of_dvd_left hc z.d)

theorem triangle_bcf_divisor (z : Six) (hz : isSolution z) (n : ℤ)
    (hb : n ∣ z.b) (hc : n ∣ z.c) (hf : n ∣ z.f) : n ∣ 4 := by
  apply divisor_of_q2 z hz n
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hf z.a) (dvd_mul_of_dvd_left hb z.e))
    (dvd_mul_of_dvd_left hc z.d)

theorem triangle_def_divisor (z : Six) (hz : isSolution z) (n : ℤ)
    (hd : n ∣ z.d) (he : n ∣ z.e) (hf : n ∣ z.f) : n ∣ 4 := by
  apply divisor_of_q2 z hz n
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hf z.a) (dvd_mul_of_dvd_right he z.b))
    (dvd_mul_of_dvd_right hd z.c)

end SerreMarkov.TriangleDivisors
