import SerreMarkov.NegativePositiveChamber
import SerreMarkov.NegativeDiagonalDescent

/-! # Complete large-edge descent in the all-positive sign chamber

All six possible positions of a largest edge are covered. This theorem
does not assume the universal local-descent property.
-/

namespace SerreMarkov.NegativePositiveDescent

open NegativePositiveChamber NegativeDescent

theorem positive_chamber_descent (z : Six) (hz : isSolution z)
    (hp : LargePositive z) (ht : NegativePositiveChamber.NegativeTriangles z) :
    OneStepDrop z := by
  let m := max z.a (max z.b (max z.c (max z.d (max z.e z.f))))
  have hm : IsMaximum z m := by
    simp only [IsMaximum, m, max_def]
    split_ifs <;> omega
  have heq : m=z.a ∨ m=z.b ∨ m=z.c ∨ m=z.d ∨ m=z.e ∨ m=z.f := by
    simp only [m, max_def]
    split_ifs <;> omega
  rcases heq with h | h | h | h | h | h
  · rw [h] at hm
    exact max_a_descent z hz hp ht hm
  · rw [h] at hm
    obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
    exact NegativeDiagonalDescent.b_max_drop z ha hb hc hd he hf hz.2 ht
      ⟨hm.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2.1,hm.2.2.2.2.2⟩
  · rw [h] at hm
    exact max_c_descent z hz hp ht hm
  · rw [h] at hm
    exact max_d_descent z hz hp ht hm
  · rw [h] at hm
    obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
    exact NegativeDiagonalDescent.e_max_drop z ha hb hc hd he hf hz.2 ht
      ⟨hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2.2⟩
  · rw [h] at hm
    exact max_f_descent z hz hp ht hm

theorem negative_large_positive_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hp : LargePositive z) :
    OneStepDrop z :=
  positive_chamber_descent z hz hp
    (NegativeTriangles.negative_triangle_inequalities z hz hneg)

end SerreMarkov.NegativePositiveDescent
