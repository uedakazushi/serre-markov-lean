import SerreMarkov.NegativeUnitEdge
import SerreMarkov.NegativeDiagonalDescent
import SerreMarkov.CyclicMutation

/-! # Strict descent at a unit edge in any basis position

The transport formulas compare the height of the actual original mutation
word; no height increase from moving the unit edge is ignored.
-/

namespace SerreMarkov.NegativeSingleUnitDescent

open NegativeDescent NegativeDiagonalDescent

/-- Reverse the basis order and reverse each adjacent braid orientation. -/
def mirrorGenerator : Generator → Generator
  | .m1 => .i3 | .i1 => .m3 | .m2 => .i2 | .i2 => .m2 | .m3 => .i1 | .i3 => .m1
  | .s1 => .s4 | .s2 => .s3 | .s3 => .s2 | .s4 => .s1

@[simp] theorem mirrorGenerator_twice (g : Generator) : mirrorGenerator (mirrorGenerator g)=g := by
  cases g <;> rfl

theorem mirror_step (g : Generator) (z : Six) :
    reverse (step g z)=step (mirrorGenerator g) (reverse z) := by
  cases g <;> ext <;> simp [step,mirrorGenerator,reverse,mu1,inv1,mu2,inv2,mu3,inv3,
    eps1,eps2,eps3,eps4] <;> ring

theorem mirror_word (z : Six) (word : List Generator) :
    reverse (applyWord z word)=applyWord (reverse z) (word.map mirrorGenerator) := by
  induction word generalizing z with
  | nil => rfl
  | cons g word ih =>
    simp only [applyWord,List.map_cons]
    rw [ih,mirror_step]

theorem mirror_word_height (z : Six) (word : List Generator) :
    l1 (applyWord z (word.map mirrorGenerator))=l1 (applyWord (reverse z) word) := by
  have h := congrArg l1 (mirror_word (reverse z) word)
  simpa only [reverse_reverse,reverse_l1] using h.symm

private theorem reverse_solution (z : Six) (hz : isSolution z) : isSolution (reverse z) := by
  have hq : q1 (reverse z)=q1 z := by dsimp [reverse,q1]; ring
  exact ⟨hq.trans hz.1,by rw [reverse_q2]; exact hz.2⟩

private theorem reverse_marker (z : Six) :
    IntrinsicSigns.thirdMinorSum (reverse z)=IntrinsicSigns.thirdMinorSum z := by
  dsimp [reverse,IntrinsicSigns.thirdMinorSum]
  ring

theorem unit_f_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hf : |z.f|=1)
    (ha : 3≤|z.a|) (hb : 3≤|z.b|) (hc : 3≤|z.c|) (hd : 3≤|z.d|) (he : 3≤|z.e|) :
    ∃ word : List Generator, word ∈ braidWords 2 ∧ l1 (applyWord z word)<l1 z := by
  have hr := reverse_solution z hz
  have hn : IntrinsicSigns.thirdMinorSum (reverse z)<0 := by rw [reverse_marker]; exact hneg
  obtain ⟨word,hword,hbraid,hdrop⟩ := NegativeUnitEdge.unit_edge_word_drop (reverse z) hr hn
    (by simpa [reverse] using hf) (by simpa [reverse] using he)
    (by simpa [reverse] using hc) (by simpa [reverse] using hd)
    (by simpa [reverse] using hb) (by simpa [reverse] using ha)
  refine ⟨word.map mirrorGenerator,(mem_braidWords_iff _ _).mpr ⟨?_,?_⟩,?_⟩
  · simpa using hword
  · intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    have hb := hbraid g' hg'
    simp only [braidMoves,List.mem_cons,List.mem_nil_iff,false_or,or_false] at hb ⊢
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mirrorGenerator]
  · rw [mirror_word_height,← reverse_l1 z]
    exact hdrop

/-- The middle adjacent unit edge is moved by a height-preserving actual
cyclic word, then descended by the first-edge theorem. -/
theorem unit_d_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hd : |z.d|=1)
    (ha : 3≤|z.a|) (hb : 3≤|z.b|) (hc : 3≤|z.c|) (he : 3≤|z.e|) (hf : 3≤|z.f|) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  have hm := CyclicMutation.cyclePower_solution z hz 1
  have hn := CyclicMutation.cyclePower_negative z hneg 1
  obtain ⟨word,hlen,hbraid,hdrop⟩ := NegativeUnitEdge.unit_edge_word_drop
    (CyclicMutation.cyclePower z 1) hm hn
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hd)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using he)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using ha)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hf)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hb)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hc)
  exact ⟨CyclicMutation.cycleWord 1 ++ word,CyclicMutation.word_descent_transfer z 1 word hdrop⟩

/-- The long adjacent unit edge is treated by three such cycles; every cycle
preserves the full six-coordinate height exactly. -/
theorem unit_c_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hc : |z.c|=1)
    (ha : 3≤|z.a|) (hb : 3≤|z.b|) (hd : 3≤|z.d|) (he : 3≤|z.e|) (hf : 3≤|z.f|) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  have hm := CyclicMutation.cyclePower_solution z hz 3
  have hn := CyclicMutation.cyclePower_negative z hneg 3
  obtain ⟨word,hlen,hbraid,hdrop⟩ := NegativeUnitEdge.unit_edge_word_drop
    (CyclicMutation.cyclePower z 3) hm hn
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hc)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using he)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hf)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using ha)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hb)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hd)
  exact ⟨CyclicMutation.cycleWord 3 ++ word,CyclicMutation.word_descent_transfer z 3 word hdrop⟩

private theorem phaseCertificate_neg_minus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+3)*(C+4)-2*(E+3)) (hk : q2 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩=(-4)) : q1 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩<8 := by
  have hrel : q2 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩-(-4)=0 := by omega
  have hcert : 378*(8-q1 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩) =
      (378 + 1830*E + 2004*F + 94*F*E + 234*D + 378*D^2 + 3764*C + 1024*C*E + 3969*C*D + 147*C*D*E + 693*C*D^2 + 993*C^2 + 898*C^2*D + 147*C^2*D^2 + 210*A*E + 1666*A*F + 126*A*F^2 + 126*A*D*F + 189*A*C*E + 84*A*C*D + 42*A*C*D*F + 126*A^2 + 168*A^2*F) + (2661 + 189*E + 677*F + 441*D + 189*D*F)*((A+3)*(C+4)-2*(E+3)) + (-90 - 126*F + 252*D + 457*C + 147*C*D - 168*A)*(q2 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩-(-4)) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(378 + 1830*E + 2004*F + 94*F*E + 234*D + 378*D^2 + 3764*C + 1024*C*E + 3969*C*D + 147*C*D*E + 693*C*D^2 + 993*C^2 + 898*C^2*D + 147*C^2*D^2 + 210*A*E + 1666*A*F + 126*A*F^2 + 126*A*D*F + 189*A*C*E + 84*A*C*D + 42*A*C*D*F + 126*A^2 + 168*A^2*F) := by positivity
  have hnn : 0≤(2661 + 189*E + 677*F + 441*D + 189*D*F)*((A+3)*(C+4)-2*(E+3)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_neg_plus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+3)*(C+4)-2*(E+3)) (hk : q2 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩=4) : q1 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩<8 := by
  have hrel : q2 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩-4=0 := by omega
  have hcert : 2346*(8-q1 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩) =
      (2346 + 910*E^2 + 2272*F*E + 2262*F^2 + 84*D^2 + 34592*C + 1784*C*E + 1389*C*F + 15256*C*D + 1215*C*D*F + 1578*C*D^2 + 1550*C^2*D + 256*C^2*D^2 + 6992*A + 9844*A*F + 256*A*F*E + 1536*A*F^2 + 1536*A*D*F + 9292*A*C + 590*A*C*E + 1217*A*C*F + 1990*A*C*D + 917*A*C*D*F + 782*A^2*F) + (14168 + 1756*E + 5039*F + 3498*D + 1173*D*F)*((A+3)*(C+4)-2*(E+3)) + (-1932 - 256*E - 1536*F + 810*D + 782*C + 256*C*D - 782*A)*(q2 ⟨A+3,1,C+3,-(D+3),E+3,F+3⟩-4) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(2346 + 910*E^2 + 2272*F*E + 2262*F^2 + 84*D^2 + 34592*C + 1784*C*E + 1389*C*F + 15256*C*D + 1215*C*D*F + 1578*C*D^2 + 1550*C^2*D + 256*C^2*D^2 + 6992*A + 9844*A*F + 256*A*F*E + 1536*A*F^2 + 1536*A*D*F + 9292*A*C + 590*A*C*E + 1217*A*C*F + 1990*A*C*D + 917*A*C*D*F + 782*A^2*F) := by positivity
  have hnn : 0≤(14168 + 1756*E + 5039*F + 3498*D + 1173*D*F)*((A+3)*(C+4)-2*(E+3)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_le_minus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+3)*(C+2)-2*(E+3)) (hk : q2 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩=(-4)) : q1 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩<8 := by
  have hrel : q2 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩-(-4)=0 := by omega
  have hcert : 288*(8-q1 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩) =
      (13104 + 4256*E + 1008*F^2 + 6576*D + 1680*D*E + 144*D*F + 360*C*E + 96*C*D^2 + 120*C^2*D + 7318*A + 1818*A*E + 2430*A*F + 864*A*F^2 + 258*A*D + 48*A*D*F + 560*A*C + 150*A*C*F + 393*A*C^2 + 54*A*C^2*D + 522*A^2*F + 144*A^2*F^2 + 18*A^2*C*F + 99*A^2*C^2) + (3397 + 99*E + 81*F + 1455*D + 144*D*F + 159*C + 45*C*D + 1152*A + 27*A*F)*((A+3)*(C+2)-2*(E+3)) + (-720 + 90*E + 432*F - 96*D - 255*C - 288*A + 144*A*F - 99*A*C)*(q2 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩-(-4)) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(13104 + 4256*E + 1008*F^2 + 6576*D + 1680*D*E + 144*D*F + 360*C*E + 96*C*D^2 + 120*C^2*D + 7318*A + 1818*A*E + 2430*A*F + 864*A*F^2 + 258*A*D + 48*A*D*F + 560*A*C + 150*A*C*F + 393*A*C^2 + 54*A*C^2*D + 522*A^2*F + 144*A^2*F^2 + 18*A^2*C*F + 99*A^2*C^2) := by positivity
  have hnn : 0≤(3397 + 99*E + 81*F + 1455*D + 144*D*F + 159*C + 45*C*D + 1152*A + 27*A*F)*((A+3)*(C+2)-2*(E+3)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_le_plus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+3)*(C+2)-2*(E+3)) (hk : q2 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩=4) : q1 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩<8 := by
  have hrel : q2 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩-4=0 := by omega
  have hcert : 126*(8-q1 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩) =
      (9142 + 560*E + 3024*F + 504*D*F + 195*C*E + 108*C*F + 25*C*D + 109*C*D*E + 189*C*D^2 + 49*C^2*D^2 + 6636*A + 70*A*E + 2674*A*F + 42*A*F^2 + 210*A*D*F + 597*A*C + 78*A*C*F + 45*A*C*D + 14*A*C*D*F + 231*A*C^2 + 33*A*C^2*D + 1008*A^2 + 448*A^2*F + 182*A^2*C + 63*A^2*C^2) + (7*E + 378*D + 63*D*F + 216*C + 135*C*D + 7*A*F + 56*A*C)*((A+3)*(C+2)-2*(E+3)) + (532 + 112*E + 42*F - 42*D - 258*C - 49*C*D + 84*A - 119*A*C)*(q2 ⟨A+3,1,C+3,A+3+D,E+3,-(F+3)⟩-4) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(9142 + 560*E + 3024*F + 504*D*F + 195*C*E + 108*C*F + 25*C*D + 109*C*D*E + 189*C*D^2 + 49*C^2*D^2 + 6636*A + 70*A*E + 2674*A*F + 42*A*F^2 + 210*A*D*F + 597*A*C + 78*A*C*F + 45*A*C*D + 14*A*C*D*F + 231*A*C^2 + 33*A*C^2*D + 1008*A^2 + 448*A^2*F + 182*A^2*C + 63*A^2*C^2) := by positivity
  have hnn : 0≤(7*E + 378*D + 63*D*F + 216*C + 135*C*D + 7*A*F + 56*A*C)*((A+3)*(C+2)-2*(E+3)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_ge_minus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(D+3+A)*(C+4)-2*(D+3)-2*(E+3)) (hk : q2 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩=(-4)) : q1 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩<8 := by
  have hrel : q2 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩-(-4)=0 := by omega
  have hcert : 8190*(8-q1 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩) =
      (347750 + 96520*E + 3360*E^2 + 84240*F + 8400*F*E + 260868*D + 70066*D*F + 2730*D*F^2 + 44982*D^2 + 7392*D^2*F + 5775*C*E + 93842*C*D + 5250*C*D*F + 22449*C*D^2 + 840*C*D^2*F + 11235*C^2*D + 2835*C^2*D^2 + 28150*A*F + 5250*A*F^2 + 1092*A*D*F + 840*A*D*F^2 + 11700*A*C + 1995*A*C*E + 2940*A*C*F + 3066*A*C*D + 5250*A^2*F + 840*A^2*F^2) + (70200 + 6195*E + 16380*F + 10269*D + 4515*D*F)*((D+3+A)*(C+4)-2*(D+3)-2*(E+3)) + (4420 - 840*E + 2730*F - 8148*D - 2730*C - 2835*C*D + 2730*A + 840*A*F)*(q2 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩-(-4)) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(347750 + 96520*E + 3360*E^2 + 84240*F + 8400*F*E + 260868*D + 70066*D*F + 2730*D*F^2 + 44982*D^2 + 7392*D^2*F + 5775*C*E + 93842*C*D + 5250*C*D*F + 22449*C*D^2 + 840*C*D^2*F + 11235*C^2*D + 2835*C^2*D^2 + 28150*A*F + 5250*A*F^2 + 1092*A*D*F + 840*A*D*F^2 + 11700*A*C + 1995*A*C*E + 2940*A*C*F + 3066*A*C*D + 5250*A^2*F + 840*A^2*F^2) := by positivity
  have hnn : 0≤(70200 + 6195*E + 16380*F + 10269*D + 4515*D*F)*((D+3+A)*(C+4)-2*(D+3)-2*(E+3)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_ge_plus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(D+3+A)*(C+4)-2*(D+3)-2*(E+3)) (hk : q2 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩=4) : q1 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩<8 := by
  have hrel : q2 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩-4=0 := by omega
  have hcert : 8820*(8-q1 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩) =
      (335650 + 97160*E + 7030*E^2 + 81270*F + 11250*F*E + 211932*D + 67678*D*F + 2940*D*F^2 + 46836*D^2 + 9766*D^2*F + 100226*C*D + 980*C*D*E + 15915*C*D*F + 22302*C*D^2 + 4325*C*D^2*F + 2940*C^2*D + 43400*A*F + 1790*A*F*E + 8820*A*F^2 + 6866*A*D*F + 1960*A*D*F^2 + 810*A*C*E + 8508*A*C*D + 2365*A*C*D*F + 9450*A^2 + 11970*A^2*F + 1960*A^2*F^2) + (78750 + 8010*E + 17640*F + 11862*D + 4495*D*F)*((D+3+A)*(C+4)-2*(D+3)-2*(E+3)) + (-6230 - 170*E + 2940*F - 7704*D - 2940*C + 6090*A + 1960*A*F)*(q2 ⟨D+3+A,1,C+3,D+3,E+3,-(F+3)⟩-4) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(335650 + 97160*E + 7030*E^2 + 81270*F + 11250*F*E + 211932*D + 67678*D*F + 2940*D*F^2 + 46836*D^2 + 9766*D^2*F + 100226*C*D + 980*C*D*E + 15915*C*D*F + 22302*C*D^2 + 4325*C*D^2*F + 2940*C^2*D + 43400*A*F + 1790*A*F*E + 8820*A*F^2 + 6866*A*D*F + 1960*A*D*F^2 + 810*A*C*E + 8508*A*C*D + 2365*A*C*D*F + 9450*A^2 + 11970*A^2*F + 1960*A^2*F^2) := by positivity
  have hnn : 0≤(78750 + 8010*E + 17640*F + 11862*D + 4495*D*F)*((D+3+A)*(C+4)-2*(D+3)-2*(E+3)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem solution_q2_cases (z : Six) (hz : isSolution z) : q2 z=4 ∨ q2 z=-4 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  norm_num
  exact hz.2

private theorem phase_forbidden_neg (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 3≤z.a) (hc : 3≤z.c) (he : 3≤z.e)
    (hd : z.d≤-3) (hf : 3≤z.f) (hg : 0≤z.a*(z.c+1)-2*z.e) : False := by
  have hmodel : (⟨z.a-3+3,1,z.c-3+3,-(-z.d-3+3),z.e-3+3,z.f-3+3⟩ : Six)=z := by ext <;> simp [hb] <;> ring
  have hgap : 0≤(z.a-3+3)*(z.c-3+4)-2*(z.e-3+3) := by nlinarith [hg]
  rcases solution_q2_cases z hz with hk | hk
  · have hh := phaseCertificate_neg_plus (z.a-3) (z.c-3) (-z.d-3) (z.f-3) (z.e-3)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega
  · have hh := phaseCertificate_neg_minus (z.a-3) (z.c-3) (-z.d-3) (z.f-3) (z.e-3)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega

private theorem phase_forbidden_le (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 3≤z.a) (hc : 3≤z.c) (he : 3≤z.e)
    (hd : z.a≤z.d) (hf : z.f≤-3) (hg : 0≤z.a*(z.c-1)-2*z.e) : False := by
  have hmodel : (⟨z.a-3+3,1,z.c-3+3,z.a-3+3+(z.d-z.a),z.e-3+3,-(-z.f-3+3)⟩ : Six)=z := by ext <;> simp [hb] <;> ring
  have hgap : 0≤(z.a-3+3)*(z.c-3+2)-2*(z.e-3+3) := by nlinarith [hg]
  rcases solution_q2_cases z hz with hk | hk
  · have hh := phaseCertificate_le_plus (z.a-3) (z.c-3) (z.d-z.a) (-z.f-3) (z.e-3)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega
  · have hh := phaseCertificate_le_minus (z.a-3) (z.c-3) (z.d-z.a) (-z.f-3) (z.e-3)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega

private theorem phase_forbidden_ge (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 3≤z.a) (hc : 3≤z.c) (he : 3≤z.e)
    (hd : 3≤z.d) (hda : z.d≤z.a) (hf : z.f≤-3) (hg : 0≤z.a*(z.c+1)-2*z.d-2*z.e) : False := by
  have hmodel : (⟨z.d-3+3+(z.a-z.d),1,z.c-3+3,z.d-3+3,z.e-3+3,-(-z.f-3+3)⟩ : Six)=z := by ext <;> simp [hb] <;> ring
  have hgap : 0≤(z.d-3+3+(z.a-z.d))*(z.c-3+4)-2*(z.d-3+3)-2*(z.e-3+3) := by nlinarith [hg]
  rcases solution_q2_cases z hz with hk | hk
  · have hh := phaseCertificate_ge_plus (z.a-z.d) (z.c-3) (z.d-3) (-z.f-3) (z.e-3)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega
  · have hh := phaseCertificate_ge_minus (z.a-z.d) (z.c-3) (z.d-3) (-z.f-3) (z.e-3)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega

private theorem positive_product_nine (a b : ℤ) (ha : 3≤a) (hb : 3≤b) : 9≤a*b := by
  have h := mul_nonneg (by omega : 0≤a-3) (by omega : 0≤b-3)
  nlinarith

/-- A positive crossing coefficient at a unit diagonal admits strict descent
by one of the two actual moves toward an adjacent unit pair. -/
theorem unit_b_positive_phase (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 3≤z.a) (hc : 3≤z.c) (he : 3≤z.e)
    (hd : 3≤|z.d|) (hf : 3≤|z.f|) :
    l1 (mu1 z)<l1 z ∨ l1 (inv2 z)<l1 z := by
  have hd' : 3≤z.d ∨ z.d≤-3 := by rcases le_abs.mp hd with h|h <;> omega
  have hf' : 3≤z.f ∨ z.f≤-3 := by rcases le_abs.mp hf with h|h <;> omega
  have hac9 := positive_product_nine z.a z.c ha hc
  have hL : |z.a-z.d|≤z.a+|z.d| := by
    simpa [abs_of_nonneg (by omega : 0≤z.a)] using abs_sub_le z.a 0 z.d
  rcases hd' with hd | hd <;> rcases hf' with hf | hf
  · have haf := positive_product_nine z.a z.f ha hf
    have hcd := positive_product_nine z.c z.d hc hd
    rcases le_total z.a z.d with had | hda
    · left
      rw [mu1_drop_iff]
      simp only [hb,mul_one,abs_of_nonneg (by omega : 0≤z.d),
        abs_of_nonneg (by omega : 0≤z.e),abs_of_nonpos (by omega : z.a-z.d≤0)]
      have hmul := mul_nonneg (by omega : 0≤z.d-z.a) (by omega : 0≤z.c)
      have hq : z.a*z.f+z.c*z.d-z.e≤4 := by
        rcases solution_q2_cases z hz with h|h <;> simp only [q2,hb,one_mul] at h <;> omega
      have hh : |z.a*z.c-z.e|<z.a+z.e := by
        apply abs_lt.mpr
        constructor <;> nlinarith
      linarith
    · right
      rw [inv2_drop_iff]
      simp only [hb,one_mul,abs_of_nonneg (by omega : 0≤z.a),
        abs_of_nonneg (by omega : 0≤z.e),abs_of_nonpos (by omega : z.d-z.a≤0)]
      have hmul := mul_nonneg (by omega : 0≤z.a-z.d) (by omega : 0≤z.f)
      have hq : z.a*z.f+z.c*z.d-z.e≤4 := by
        rcases solution_q2_cases z hz with h|h <;> simp only [q2,hb,one_mul] at h <;> omega
      have hh : |z.d*z.f-z.e|<z.d+z.e := by
        apply abs_lt.mpr
        constructor <;> nlinarith
      have heq : |z.d-z.a|=z.a-z.d := by rw [abs_of_nonpos (by omega : z.d-z.a≤0)]; ring
      linarith
  · left
    by_contra hm
    rw [mu1_drop_iff] at hm
    simp only [hb,mul_one,abs_of_nonneg (by omega : 0≤z.d),
      abs_of_nonneg (by omega : 0≤z.e)] at hm
    have hac : 0≤z.a*z.c-z.e := by
      by_contra hh
      rw [abs_of_nonpos (by omega : z.a*z.c-z.e≤0)] at hm
      rw [abs_of_nonneg (by omega : 0≤z.d)] at hL
      have hh := mul_nonneg (by omega : 0≤z.a) (by omega : 0≤z.c-1)
      nlinarith
    rw [abs_of_nonneg hac] at hm
    rcases le_total z.a z.d with had | hda
    · rw [abs_of_nonpos (by omega : z.a-z.d≤0)] at hm
      exact phase_forbidden_le z hz hb ha hc he had hf (by linarith)
    · rw [abs_of_nonneg (by omega : 0≤z.a-z.d)] at hm
      exact phase_forbidden_ge z hz hb ha hc he hd hda hf (by linarith)
  · left
    by_contra hm
    rw [mu1_drop_iff] at hm
    simp only [hb,mul_one,abs_of_nonpos (by omega : z.d≤0),
      abs_of_nonneg (by omega : 0≤z.e),abs_of_nonneg (by omega : 0≤z.a-z.d)] at hm
    have hac : 0≤z.a*z.c-z.e := by
      by_contra hh
      rw [abs_of_nonpos (by omega : z.a*z.c-z.e≤0)] at hm
      have hh := mul_nonneg (by omega : 0≤z.a) (by omega : 0≤z.c-1)
      nlinarith
    rw [abs_of_nonneg hac] at hm
    exact phase_forbidden_neg z hz hb ha hc he hd hf (by linarith)
  · have haf := positive_product_nine z.a (-z.f) ha (by omega)
    have hcd := positive_product_nine z.c (-z.d) hc (by omega)
    rcases solution_q2_cases z hz with h|h <;> simp only [q2,hb,one_mul] at h <;> nlinarith

private theorem positive_phase_word (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 3≤z.a) (hc : 3≤z.c) (he : 3≤z.e)
    (hd : 3≤|z.d|) (hf : 3≤|z.f|) :
    ∃ word : List Generator, word∈braidWords 1 ∧ l1 (applyWord z word)<l1 z := by
  rcases unit_b_positive_phase z hz hb ha hc he hd hf with h|h
  · exact ⟨[.m1],by decide,by simpa [applyWord,step] using h⟩
  · exact ⟨[.i2],by decide,by simpa [applyWord,step] using h⟩

private theorem cycle_two_prefix_descent (z : Six) (word : List Generator)
    (hw : word∈braidWords 1)
    (h : l1 (applyWord (CyclicMutation.cyclePower z 2) word)<
      l1 (CyclicMutation.cyclePower z 2)) :
    ∃ actual : List Generator, actual∈braidWords 7 ∧ l1 (applyWord z actual)<l1 z := by
  obtain ⟨hlen,hletters⟩ := (mem_braidWords_iff 1 word).mp hw
  refine ⟨CyclicMutation.cycleWord 2 ++ word,(mem_braidWords_iff _ _).mpr ⟨?_,?_⟩,
    CyclicMutation.word_descent_transfer z 2 word h⟩
  · simp [CyclicMutation.cycleWord]
    omega
  · intro g hg
    rcases List.mem_append.mp hg with hg|hg
    · simp [CyclicMutation.cycleWord] at hg
      aesop (add simp [braidMoves])
    · exact hletters g hg

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

/-- Normalize the unit diagonal and both first-row signs. A negative crossing
coefficient is handled by two exact height-preserving cycles and a vertex gauge. -/
theorem unit_b_normalized_descent (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 3≤z.a) (hc : 3≤z.c)
    (hd : 3≤|z.d|) (he : 3≤|z.e|) (hf : 3≤|z.f|) :
    ∃ word : List Generator, word∈braidWords 7 ∧ l1 (applyWord z word)<l1 z := by
  have hd' : 3≤z.d ∨ z.d≤-3 := by rcases le_abs.mp hd with h|h <;> omega
  have he' : 3≤z.e ∨ z.e≤-3 := by rcases le_abs.mp he with h|h <;> omega
  have hf' : 3≤z.f ∨ z.f≤-3 := by rcases le_abs.mp hf with h|h <;> omega
  rcases he' with he|he
  · obtain ⟨word,hw,hdrop⟩ := positive_phase_word z hz hb ha hc he hd hf
    obtain ⟨hlen,hletters⟩ := (mem_braidWords_iff 1 word).mp hw
    exact ⟨word,(mem_braidWords_iff 7 word).mpr ⟨by omega,hletters⟩,hdrop⟩
  · rcases hd' with hd|hd <;> rcases hf' with hf|hf
    · have haf := positive_product_nine z.a z.f ha hf
      have hcd := positive_product_nine z.c z.d hc hd
      rcases solution_q2_cases z hz with h|h <;> simp only [q2,hb,one_mul] at h <;> nlinarith
    · let w := CyclicMutation.cyclePower z 2
      let v := eps2 w
      have hwsol : isSolution w := CyclicMutation.cyclePower_solution z hz 2
      have hvsol : isSolution v := reachable_preserves_solution ⟨[.s2],rfl⟩ hwsol
      obtain ⟨word,hword,hdrop⟩ := positive_phase_word v hvsol
        (by simp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle,hb])
        (by dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by
          dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]
          simpa [abs_of_nonneg (by omega : 0≤z.c)] using hc)
        (by
          dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]
          simpa [abs_of_nonneg (by omega : 0≤z.a)] using ha)
      let t : Fin 4 → ℤ := ![1,-1,1,1]
      have ht : ∀ i,(t i)^2=1 := by intro i; fin_cases i <;> simp [t]
      have htv : PositiveNormalization.signedSix w t=v := by
        ext <;> simp [PositiveNormalization.signedSix,v,eps2,t]
      have hwDrop : l1 (applyWord w word)<l1 w :=
        SignGaugeDescent.descent_transfer w t ht word (by simpa only [htv] using hdrop)
      exact cycle_two_prefix_descent z word hword hwDrop
    · let w := CyclicMutation.cyclePower z 2
      let v := eps4 w
      have hwsol : isSolution w := CyclicMutation.cyclePower_solution z hz 2
      have hvsol : isSolution v := reachable_preserves_solution ⟨[.s4],rfl⟩ hwsol
      obtain ⟨word,hword,hdrop⟩ := positive_phase_word v hvsol
        (by simp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle,hb])
        (by dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by
          dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]
          simpa [abs_of_nonneg (by omega : 0≤z.c)] using hc)
        (by
          dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]
          simpa [abs_of_nonneg (by omega : 0≤z.a)] using ha)
      let t : Fin 4 → ℤ := ![1,1,1,-1]
      have ht : ∀ i,(t i)^2=1 := by intro i; fin_cases i <;> simp [t]
      have htv : PositiveNormalization.signedSix w t=v := by
        ext <;> simp [PositiveNormalization.signedSix,v,eps4,t]
      have hwDrop : l1 (applyWord w word)<l1 w :=
        SignGaugeDescent.descent_transfer w t ht word (by simpa only [htv] using hdrop)
      exact cycle_two_prefix_descent z word hword hwDrop
    · have hsum := SignChambers.q1_ge_square_sum_of_negative_tail z
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hz.1] at hsum
      nlinarith [sq_nonneg (z.a-3),sq_nonneg z.b,sq_nonneg z.c,
        sq_nonneg z.d,sq_nonneg z.e,sq_nonneg z.f]

/-- A unit in the crossing position has strict original-height descent,
without any initial height-increasing transport. -/
theorem unit_b_large_descent (z : Six) (hz : isSolution z)
    (hb : |z.b|=1) (ha : 3≤|z.a|) (hc : 3≤|z.c|)
    (hd : 3≤|z.d|) (he : 3≤|z.e|) (hf : 3≤|z.f|) :
    ∃ word : List Generator, word∈braidWords 7 ∧ l1 (applyWord z word)<l1 z := by
  obtain ⟨s,hs,ha',hb',hc',hr,hl⟩ := SignGaugeDescent.first_row_abs_sign_gauge z
  obtain ⟨habsA,habsB,habsC,habsD,habsE,habsF⟩ := SignGaugeDescent.signedSix_abs z s hs
  obtain ⟨word,hw,hdrop⟩ := unit_b_normalized_descent (PositiveNormalization.signedSix z s)
    (reachable_preserves_solution hr hz) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  exact ⟨word,hw,SignGaugeDescent.descent_transfer z s hs word hdrop⟩

/-- The other crossing position is brought to `b` by one height-preserving
actual cycle. -/
theorem unit_e_large_descent (z : Six) (hz : isSolution z)
    (he : |z.e|=1) (ha : 3≤|z.a|) (hb : 3≤|z.b|)
    (hc : 3≤|z.c|) (hd : 3≤|z.d|) (hf : 3≤|z.f|) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  obtain ⟨word,hw,hdrop⟩ := unit_b_large_descent (CyclicMutation.cyclePower z 1)
    (CyclicMutation.cyclePower_solution z hz 1)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using he)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hd)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using ha)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hf)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hb)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hc)
  exact ⟨CyclicMutation.cycleWord 1 ++ word,CyclicMutation.word_descent_transfer z 1 word hdrop⟩

/-- Exactly one edge has absolute value one and the other five are large. -/
def SingleUnitLarge (z : Six) : Prop :=
  (|z.a|=1 ∧ 3≤|z.b| ∧ 3≤|z.c| ∧ 3≤|z.d| ∧ 3≤|z.e| ∧ 3≤|z.f|) ∨
  (|z.b|=1 ∧ 3≤|z.a| ∧ 3≤|z.c| ∧ 3≤|z.d| ∧ 3≤|z.e| ∧ 3≤|z.f|) ∨
  (|z.c|=1 ∧ 3≤|z.a| ∧ 3≤|z.b| ∧ 3≤|z.d| ∧ 3≤|z.e| ∧ 3≤|z.f|) ∨
  (|z.d|=1 ∧ 3≤|z.a| ∧ 3≤|z.b| ∧ 3≤|z.c| ∧ 3≤|z.e| ∧ 3≤|z.f|) ∨
  (|z.e|=1 ∧ 3≤|z.a| ∧ 3≤|z.b| ∧ 3≤|z.c| ∧ 3≤|z.d| ∧ 3≤|z.f|) ∨
  (|z.f|=1 ∧ 3≤|z.a| ∧ 3≤|z.b| ∧ 3≤|z.c| ∧ 3≤|z.d| ∧ 3≤|z.e|)

/-- Unconditional strict L1 descent for a unit edge in every position.
The six cases all compare the final actual word with the original tuple. -/
theorem unit_single_edge_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hunit : SingleUnitLarge z) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  rcases hunit with ⟨h0,h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h2,h3,h4,h5⟩ |
    ⟨h0,h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h2,h3,h4,h5⟩ |
    ⟨h0,h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h2,h3,h4,h5⟩
  · obtain ⟨word,hw,hbraid,hdrop⟩ := NegativeUnitEdge.unit_edge_word_drop z hz hneg h0 h1 h2 h3 h4 h5
    exact ⟨word,hdrop⟩
  · obtain ⟨word,hw,hdrop⟩ := unit_b_large_descent z hz h0 h1 h2 h3 h4 h5
    exact ⟨word,hdrop⟩
  · exact unit_c_large_descent z hz hneg h0 h1 h2 h3 h4 h5
  · exact unit_d_large_descent z hz hneg h0 h1 h2 h3 h4 h5
  · exact unit_e_large_descent z hz h0 h1 h2 h3 h4 h5
  · obtain ⟨word,hw,hdrop⟩ := unit_f_large_descent z hz hneg h0 h1 h2 h3 h4 h5
    exact ⟨word,hdrop⟩

end SerreMarkov.NegativeSingleUnitDescent
