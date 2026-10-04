import SerreMarkov.NegativePairDescent
import SerreMarkov.NegativePositiveDescent
import SerreMarkov.SignGaugeDescent

/-! # Unconditional descent when all six coefficients have absolute value at least three -/

namespace SerreMarkov.NegativeLargeDescent

open NegativeDescent

theorem first_row_positive_word_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ |z.d|) (he : 3 ≤ |z.e|) (hf : 3 ≤ |z.f|) :
    ∃ word : List Generator, word.length ≤ 2 ∧
      (∀ g ∈ word, g ∈ braidMoves) ∧ l1 (applyWord z word) < l1 z := by
  by_cases ht : 0 ≤ z.d ∧ 0 ≤ z.e ∧ 0 ≤ z.f
  · have hp : NegativePositiveChamber.LargePositive z := by
      exact ⟨ha,hb,hc,by simpa only [abs_of_nonneg ht.1] using hd,
        by simpa only [abs_of_nonneg ht.2.1] using he,
        by simpa only [abs_of_nonneg ht.2.2] using hf⟩
    have hdrop := NegativePositiveDescent.negative_large_positive_descent z hz hneg hp
    rcases hdrop with h | h | h | h | h | h
    · exact ⟨[.m1],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.i1],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.m2],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.i2],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.m3],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.i3],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
  · exact NegativePairDescent.nonpositive_tail_large_word_drop z hz hneg ha hb hc hd he hf
      (by omega)

theorem negative_all_large_word_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 3 ≤ |z.a|) (hb : 3 ≤ |z.b|) (hc : 3 ≤ |z.c|)
    (hd : 3 ≤ |z.d|) (he : 3 ≤ |z.e|) (hf : 3 ≤ |z.f|) :
    ∃ word : List Generator, word.length ≤ 2 ∧
      (∀ g ∈ word, g ∈ braidMoves) ∧ l1 (applyWord z word) < l1 z := by
  obtain ⟨s,hs,hsa,hsb,hsc,hr,hheight⟩ := SignGaugeDescent.first_row_abs_sign_gauge z
  have hz' := reachable_preserves_solution hr hz
  have hneg' : IntrinsicSigns.thirdMinorSum (PositiveNormalization.signedSix z s) < 0 := by
    have heq := SignGaugeDescent.negativeMarker_signedSix z s hs
    change negativeMarker (PositiveNormalization.signedSix z s) < 0
    rw [heq]
    exact hneg
  obtain ⟨habsa,habsb,habsc,habsd,habse,habsf⟩ := SignGaugeDescent.signedSix_abs z s hs
  obtain ⟨word,hlen,hbraid,hdrop⟩ := first_row_positive_word_descent
    (PositiveNormalization.signedSix z s) hz' hneg'
    (by simpa only [hsa] using ha) (by simpa only [hsb] using hb) (by simpa only [hsc] using hc)
    (by simpa only [habsd] using hd) (by simpa only [habse] using he) (by simpa only [habsf] using hf)
  exact ⟨word,hlen,hbraid,SignGaugeDescent.descent_transfer z s hs word hdrop⟩

end SerreMarkov.NegativeLargeDescent
