import SerreMarkov.PositiveThreeFiveBase

/-! Exact reconstruction and completeness of the finite conic encoding. -/
namespace SerreMarkov.PositiveThreeFive
open PositiveChamber PositiveThreeFourBounds PositiveShortWord NegativeDescent

theorem encoded_census
    (hchecks : ∀ b j : ℕ, 4 ≤ b → b ≤ 11 → 10*j ≤ cBound b → blockCheck b j=true)
    (b c f : ℕ) (q : Bool) (hb : 4 ≤ b) (hb' : b ≤ 11)
    (hc : c ≤ cBound b) (hf : f ≤ fBound b)
    (hz : Chamber (candidate b c f q)) (hguard : guardCheck (candidate b c f q)=true)
    (hconic : binaryConic b c f (if q then 4 else -4)=0) :
    candidate b c f q=first ∨ candidate b c f q=second := by
  have hj : 10*(c/10) ≤ cBound b := by omega
  have hr : c%10 < 10 := Nat.mod_lt _ (by decide)
  have heq : 10*(c/10)+c%10=c := Nat.div_add_mod c 10
  have heqI : (10:ℤ)*((c/10:ℕ):ℤ)+((c%10:ℕ):ℤ)=(c:ℤ) := by exact_mod_cast heq
  have h := blockCheck_correct b (c/10) (hchecks b (c/10) hb hb' hj)
    (c%10) f hr (by omega) q (by simpa only [heq] using hz)
      (by simpa only [heq] using hguard) (by simpa only [heqI] using hconic)
  simpa only [heq] using h

theorem chamber_census
    (hchecks : ∀ b j : ℕ, 4 ≤ b → b ≤ 11 → 10*j ≤ cBound b → blockCheck b j=true)
    (z : Six) (hz : Chamber z) (ha : z.a=3) (hd : z.d=5)
    (ht : ShortTerminal z 2) : z=first ∨ z=second := by
  obtain ⟨hb,hb',hc,hf⟩ := a_three_d_five_bounds z hz ha hd ht
  have hcb : (z.b.toNat : ℤ)=z.b := Int.toNat_of_nonneg (by omega)
  have hcc : (z.c.toNat : ℤ)=z.c := Int.toNat_of_nonneg (by have := hz.2.2.2.2.1; omega)
  have hcf : (z.f.toNat : ℤ)=z.f := Int.toNat_of_nonneg (by have := hz.2.2.2.2.2.2.2; omega)
  have hbN : 4 ≤ z.b.toNat := by omega
  have hbN' : z.b.toNat ≤ 11 := by omega
  have hcN : z.c.toNat ≤ cBound z.b.toNat := by omega
  have hfN : z.f.toNat ≤ fBound z.b.toNat := by omega
  have hguard := shortTerminal_guardCheck z ht
  have hq : q2 z=4 ∨ q2 z= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.1.2)
  have hdiv : (3*z.f+5*z.c-q2 z)/z.b=z.e := by
    have heq : 3*z.f+5*z.c-q2 z=z.b*z.e := by dsimp [q2]; rw [ha,hd]; ring
    rw [heq]
    exact Int.mul_ediv_cancel_left _ (by omega)
  have hzslice : isSolution ⟨3,z.b,z.c,5,z.e,z.f⟩ := by
    have heq : z=⟨3,z.b,z.c,5,z.e,z.f⟩ := by ext <;> simp [ha,hd]
    exact heq ▸ hz.1
  have hconic : binaryConic z.b z.c z.f (q2 z)=0 := by
    have h := binaryConic_solution z.b z.c z.e z.f hzslice
    simpa only [q2,ha,hd] using h
  rcases hq with hq|hq
  · rw [hq] at hdiv hconic
    have heq : candidate z.b.toNat z.c.toNat z.f.toNat true=z := by
      ext <;> simp only [candidate,ite_true,hcb,hcc,hcf,hdiv,ha,hd]
    have h := encoded_census hchecks _ _ _ true hbN hbN' hcN hfN
      (heq.symm ▸ hz) (heq.symm ▸ hguard)
      (by simpa only [ite_true,hcb,hcc,hcf] using hconic)
    simpa only [heq] using h
  · rw [hq] at hdiv hconic
    have heq : candidate z.b.toNat z.c.toNat z.f.toNat false=z := by
      ext <;> simp only [candidate,Bool.false_eq_true,ite_false,hcb,hcc,hcf,hdiv,ha,hd]
    have h := encoded_census hchecks _ _ _ false hbN hbN' hcN hfN
      (heq.symm ▸ hz) (heq.symm ▸ hguard)
      (by simpa only [Bool.false_eq_true,ite_false,hcb,hcc,hcf] using hconic)
    simpa only [heq] using h

end SerreMarkov.PositiveThreeFive
