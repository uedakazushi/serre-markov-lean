import SerreMarkov.NegativeDescent
import SerreMarkov.NegativeTriangles

/-! # Descent in the positive sign chamber on the negative locus

This module treats the four off-diagonal positions of a largest edge.
Only the solution equation and the four negative Cayley inequalities are
used. The two remaining diagonal positions are handled separately.
-/

namespace SerreMarkov.NegativePositiveChamber

open NegativeDescent NegativeTriangles

def IsMaximum (z : Six) (m : ℤ) : Prop :=
  z.a ≤ m ∧ z.b ≤ m ∧ z.c ≤ m ∧ z.d ≤ m ∧ z.e ≤ m ∧ z.f ≤ m

def LargePositive (z : Six) : Prop :=
  3 ≤ z.a ∧ 3 ≤ z.b ∧ 3 ≤ z.c ∧ 3 ≤ z.d ∧ 3 ≤ z.e ∧ 3 ≤ z.f

def NegativeTriangles (z : Six) : Prop :=
  4 ≤ cayleyDefect z.a z.b z.d ∧ 4 ≤ cayleyDefect z.a z.c z.e ∧
  4 ≤ cayleyDefect z.b z.c z.f ∧ 4 ≤ cayleyDefect z.d z.e z.f

theorem cross_products_lt (z : Six) (hz : isSolution z) (hp : LargePositive z) :
    z.a*z.f < z.b*z.e ∧ z.c*z.d < z.b*z.e := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  have haf : 9 ≤ z.a*z.f := by
    nlinarith [mul_nonneg (by omega : 0 ≤ z.a-3) (by omega : 0 ≤ z.f-3)]
  have hcd : 9 ≤ z.c*z.d := by
    nlinarith [mul_nonneg (by omega : 0 ≤ z.c-3) (by omega : 0 ≤ z.d-3)]
  have hq : q2 z ≤ 4 := by nlinarith [hz.2]
  dsimp [q2] at hq
  constructor <;> linarith

private theorem cross_small (b e w s : ℤ) (hb : 0 < b) (he : 0 < e)
    (hw : 0 < w) (hbw : b ≤ w) (hew : e ≤ w) (hp : w*s < b*e) :
    s < b ∧ s < e := by
  constructor
  · by_contra hn
    have hs : b ≤ s := le_of_not_gt hn
    have h1 := mul_nonneg hw.le (sub_nonneg.mpr hs)
    have h2 := mul_nonneg hb.le (sub_nonneg.mpr hew)
    nlinarith
  · by_contra hn
    have hs : e ≤ s := le_of_not_gt hn
    have h1 := mul_nonneg hw.le (sub_nonneg.mpr hs)
    have h2 := mul_nonneg he.le (sub_nonneg.mpr hbw)
    nlinarith

private theorem ordered_product_lt (b c e d : ℤ) (_hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (hbc : b < c) (hed : e < d) : b*e < c*d :=
  (mul_lt_mul_of_pos_right hbc he).trans (mul_lt_mul_of_pos_left hed hc)

private theorem triangle_descent (u v w : ℤ) (hu : 3 ≤ u) (hv : 3 ≤ v)
    (hw : 3 ≤ w) (hum : u ≤ w) (hvm : v ≤ w)
    (ht : 4 ≤ cayleyDefect u v w) : |u*v-w| < |w| := by
  simpa only [abs_of_nonneg (by omega : 0 ≤ w)] using
    cayley_positive_abs_descent u v w hu hv hw ⟨hum,hvm⟩ ht

private theorem mu1_of_max (z : Six) (hp : LargePositive z) (ht : NegativeTriangles z)
    (had : z.a ≤ z.d) (hbd : z.b ≤ z.d) (hae : z.a ≤ z.e) (hce : z.c ≤ z.e) :
    OneStepDrop z := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  have h1 := triangle_descent z.a z.b z.d ha hb hd had hbd ht.1
  have h2 := triangle_descent z.a z.c z.e ha hc he hae hce ht.2.1
  have h := (mu1_drop_iff z).mpr (add_lt_add h1 h2)
  exact Or.inl h

private theorem inv1_of_max (z : Six) (hp : LargePositive z) (ht : NegativeTriangles z)
    (hab : z.a ≤ z.b) (hdb : z.d ≤ z.b) (hac : z.a ≤ z.c) (hec : z.e ≤ z.c) :
    OneStepDrop z := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  have ht1 : 4 ≤ cayleyDefect z.a z.d z.b := by
    simpa [cayleyDefect, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using ht.1
  have ht2 : 4 ≤ cayleyDefect z.a z.e z.c := by
    simpa [cayleyDefect, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using ht.2.1
  have h1 := triangle_descent z.a z.d z.b ha hd hb hab hdb ht1
  have h2 := triangle_descent z.a z.e z.c ha he hc hac hec ht2
  have h := (inv1_drop_iff z).mpr (add_lt_add h1 h2)
  exact Or.inr (Or.inl h)

private theorem mu2_of_max (z : Six) (hp : LargePositive z) (ht : NegativeTriangles z)
    (hab : z.a ≤ z.b) (hdb : z.d ≤ z.b) (hdf : z.d ≤ z.f) (hef : z.e ≤ z.f) :
    OneStepDrop z := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  have ht1 : 4 ≤ cayleyDefect z.a z.d z.b := by
    simpa [cayleyDefect, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using ht.1
  have h1 := triangle_descent z.a z.d z.b ha hd hb hab hdb ht1
  have h2 := triangle_descent z.d z.e z.f hd he hf hdf hef ht.2.2.2
  have h := (mu2_drop_iff z).mpr (add_lt_add h1 h2)
  exact Or.inr (Or.inr (Or.inl h))

private theorem inv2_of_max (z : Six) (hp : LargePositive z) (ht : NegativeTriangles z)
    (hba : z.b ≤ z.a) (hda : z.d ≤ z.a) (hde : z.d ≤ z.e) (hfe : z.f ≤ z.e) :
    OneStepDrop z := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  have ht1 : 4 ≤ cayleyDefect z.b z.d z.a := by
    simpa [cayleyDefect, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using ht.1
  have ht2 : 4 ≤ cayleyDefect z.d z.f z.e := by
    simpa [cayleyDefect, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using ht.2.2.2
  have h1 := triangle_descent z.b z.d z.a hb hd ha hba hda ht1
  have h2 := triangle_descent z.d z.f z.e hd hf he hde hfe ht2
  have h := (inv2_drop_iff z).mpr (add_lt_add h1 h2)
  exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem inv3_of_max (z : Six) (hp : LargePositive z) (ht : NegativeTriangles z)
    (hcb : z.c ≤ z.b) (hfb : z.f ≤ z.b) (hed : z.e ≤ z.d) (hfd : z.f ≤ z.d) :
    OneStepDrop z := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  have ht1 : 4 ≤ cayleyDefect z.f z.c z.b := by
    simpa [cayleyDefect, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using ht.2.2.1
  have ht2 : 4 ≤ cayleyDefect z.f z.e z.d := by
    simpa [cayleyDefect, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using ht.2.2.2
  have h1 := triangle_descent z.f z.c z.b hf hc hb hfb hcb ht1
  have h2 := triangle_descent z.f z.e z.d hf he hd hfd hed ht2
  have h := (inv3_drop_iff z).mpr (add_lt_add h1 h2)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem max_a_descent (z : Six) (hz : isSolution z) (hp : LargePositive z)
    (ht : NegativeTriangles z) (hm : IsMaximum z z.a) : OneStepDrop z := by
  have hpos := hp
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  obtain ⟨haa,hba,hca,hda,hea,hfa⟩ := hm
  obtain ⟨haf,hcd⟩ := cross_products_lt z hz hpos
  obtain ⟨hfb,hfe⟩ := cross_small z.b z.e z.a z.f (by omega) (by omega)
    (by omega) hba hea haf
  by_cases hde : z.d ≤ z.e
  · exact inv2_of_max z hpos ht hba hda hde hfe.le
  · have hed : z.e < z.d := lt_of_not_ge hde
    by_cases hcb : z.c ≤ z.b
    · exact inv3_of_max z hpos ht hcb hfb.le hed.le (hfe.trans hed).le
    · have hbc : z.b < z.c := lt_of_not_ge hcb
      exact False.elim ((not_lt_of_gt hcd)
        (ordered_product_lt z.b z.c z.e z.d (by omega) (by omega) (by omega) hbc hed))

theorem max_d_descent (z : Six) (hz : isSolution z) (hp : LargePositive z)
    (ht : NegativeTriangles z) (hm : IsMaximum z z.d) : OneStepDrop z := by
  have hpos := hp
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  obtain ⟨had,hbd,hcd0,hdd,hed,hfd⟩ := hm
  obtain ⟨haf,hcd⟩ := cross_products_lt z hz hpos
  have hcd' : z.d*z.c < z.b*z.e := by simpa [mul_comm] using hcd
  obtain ⟨hcb,hce⟩ := cross_small z.b z.e z.d z.c (by omega) (by omega)
    (by omega) hbd hed hcd'
  by_cases hae : z.a ≤ z.e
  · exact mu1_of_max z hpos ht had hbd hae hce.le
  · have hea : z.e < z.a := lt_of_not_ge hae
    by_cases hfb : z.f ≤ z.b
    · exact inv3_of_max z hpos ht hcb.le hfb hed hfd
    · have hbf : z.b < z.f := lt_of_not_ge hfb
      have hprod := ordered_product_lt z.e z.a z.b z.f (by omega) (by omega)
        (by omega) hea hbf
      have hprod' : z.b*z.e < z.a*z.f := by simpa [mul_comm] using hprod
      exact False.elim ((not_lt_of_gt haf) hprod')

theorem max_c_descent (z : Six) (hz : isSolution z) (hp : LargePositive z)
    (ht : NegativeTriangles z) (hm : IsMaximum z z.c) : OneStepDrop z := by
  have hpos := hp
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  obtain ⟨hac,hbc,hcc,hdc,hec,hfc⟩ := hm
  obtain ⟨haf,hcd⟩ := cross_products_lt z hz hpos
  obtain ⟨hdb,hde⟩ := cross_small z.b z.e z.c z.d (by omega) (by omega)
    (by omega) hbc hec hcd
  by_cases hab : z.a ≤ z.b
  · exact inv1_of_max z hpos ht hab hdb.le hac hec
  · have hba : z.b < z.a := lt_of_not_ge hab
    by_cases hfe : z.f ≤ z.e
    · exact inv2_of_max z hpos ht hba.le (hdb.trans hba).le hde.le hfe
    · have hef : z.e < z.f := lt_of_not_ge hfe
      exact False.elim ((not_lt_of_gt haf)
        (ordered_product_lt z.b z.a z.e z.f (by omega) (by omega) (by omega) hba hef))

theorem max_f_descent (z : Six) (hz : isSolution z) (hp : LargePositive z)
    (ht : NegativeTriangles z) (hm : IsMaximum z z.f) : OneStepDrop z := by
  have hpos := hp
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  obtain ⟨haf0,hbf,hcf,hdf,hef,hff⟩ := hm
  obtain ⟨haf,hcd⟩ := cross_products_lt z hz hpos
  have haf' : z.f*z.a < z.b*z.e := by simpa [mul_comm] using haf
  obtain ⟨hab,hae⟩ := cross_small z.b z.e z.f z.a (by omega) (by omega)
    (by omega) hbf hef haf'
  by_cases hdb : z.d ≤ z.b
  · exact mu2_of_max z hpos ht hab.le hdb hdf hef
  · have hbd : z.b < z.d := lt_of_not_ge hdb
    by_cases hce : z.c ≤ z.e
    · exact mu1_of_max z hpos ht (hab.trans hbd).le hbd.le hae.le hce
    · have hec : z.e < z.c := lt_of_not_ge hce
      have hprod := ordered_product_lt z.e z.c z.b z.d (by omega) (by omega)
        (by omega) hec hbd
      have hprod' : z.b*z.e < z.c*z.d := by simpa [mul_comm] using hprod
      exact False.elim ((not_lt_of_gt hcd) hprod')

end SerreMarkov.NegativePositiveChamber
