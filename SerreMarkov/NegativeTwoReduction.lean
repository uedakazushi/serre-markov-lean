import SerreMarkov.NegativeTwoPositive

/-! # Complete sign-chamber reduction at a first edge of absolute value two

The other five edges may also have absolute value two. The conclusion gives
an actual mutation path to the family, or an actual strictly decreasing word.
-/

namespace SerreMarkov.NegativeTwoReduction

open NegativeDescent NegativeTwoEdge

theorem normalized_two_edge_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : z.a=2) (hb : 2≤z.b) (hc : 2≤z.c)
    (hd : 2≤|z.d|) (he : 2≤|z.e|) (hf : 2≤|z.f|) : FamilyOrDrop z := by
  by_cases hminus : z.d<0 ∨ z.e<0 ∨ z.f<0
  · exact nonpositive_tail_two_reduction z hz hneg ha hb hc hd he hf hminus
  · have hd0 : 0≤z.d := by omega
    have he0 : 0≤z.e := by omega
    have hf0 : 0≤z.f := by omega
    have hd2 : 2≤z.d := by simpa only [abs_of_nonneg hd0] using hd
    have he2 : 2≤z.e := by simpa only [abs_of_nonneg he0] using he
    have hf2 : 2≤z.f := by simpa only [abs_of_nonneg hf0] using hf
    exact NegativeTwoPositive.positive_two_edge_reduction z hz hneg ha hb hc hd2 he2 hf2

/-- No sign-chamber hypothesis remains: the height-preserving diagonal
gauge is explicit, and the decreasing word transfers to the original tuple. -/
theorem absolute_two_edge_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : |z.a|=2)
    (hb : 2≤|z.b|) (hc : 2≤|z.c|) (hd : 2≤|z.d|)
    (he : 2≤|z.e|) (hf : 2≤|z.f|) : FamilyOrDrop z := by
  obtain ⟨w,hr,hw,hwneg,hwa,hwb,hwc,hwd,hwe,hwf,hl1,htransfer⟩ :=
    first_row_two_normalization z hz hneg ha hb hc hd he hf
  exact htransfer (normalized_two_edge_reduction w hw hwneg hwa hwb hwc hwd hwe hwf)

end SerreMarkov.NegativeTwoReduction
