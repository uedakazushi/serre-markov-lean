import SerreMarkov.PositiveThreeFourBase

/-! Structural completeness of the finite conic enumeration. -/
namespace SerreMarkov.PositiveThreeFour

open PositiveChamber PositiveThreeFourBounds NegativeDescent PositiveShortWord

theorem encoded_census
    (hchecks : ∀ b k j : ℕ, 4 ≤ b → b ≤ 8 → k < 4 → j < 11 → blockCheck b k j=true)
    (b c f : ℕ) (q : Bool) (hb : 4 ≤ b) (hb' : b ≤ 8)
    (hc : c < 165) (hf : f < 182)
    (hz : Chamber (candidate b c f q)) (hone : oneStepCheck (candidate b c f q)=true)
    (hconic : binaryConic b c f (if q then 4 else -4)=0) :
    candidate b c f q=first ∨ candidate b c f q=extra := by
  have hk : f/46 < 4 := by omega
  have hr : f%46 < 46 := Nat.mod_lt _ (by decide)
  have heq : 46*(f/46)+f%46=f := Nat.div_add_mod f 46
  have hj : c/15 < 11 := by omega
  have hs : c%15 < 15 := Nat.mod_lt _ (by decide)
  have heqc : 15*(c/15)+c%15=c := Nat.div_add_mod c 15
  have heqcI : (15:ℤ)*((c/15:ℕ):ℤ)+((c%15:ℕ):ℤ)=(c:ℤ) := by exact_mod_cast heqc
  have heqI : (46:ℤ)*((f/46:ℕ):ℤ)+((f%46:ℕ):ℤ)=(f:ℤ) := by exact_mod_cast heq
  have h := blockCheck_correct b (f/46) (c/15) (hchecks b (f/46) (c/15) hb hb' hk hj)
    (c%15) (f%46) hs hr q (by simpa only [heq,heqc] using hz)
      (by simpa only [heq,heqc] using hone) (by simpa only [heqI,heqcI] using hconic)
  simpa only [heq,heqc] using h

theorem chamber_census
    (hchecks : ∀ b k j : ℕ, 4 ≤ b → b ≤ 8 → k < 4 → j < 11 → blockCheck b k j=true)
    (z : Six) (hz : Chamber z) (ha : z.a=3) (hd : z.d=4)
    (hone : oneStepCheck z=true) : z=first ∨ z=extra := by
  obtain ⟨hb,hb',hc,hf⟩ := a_three_d_four_bounds z hz ha hd hone
  have hcb : (z.b.toNat : ℤ)=z.b := Int.toNat_of_nonneg (by omega)
  have hcc : (z.c.toNat : ℤ)=z.c := Int.toNat_of_nonneg (by have := hz.2.2.2.2.1; omega)
  have hcf : (z.f.toNat : ℤ)=z.f := Int.toNat_of_nonneg (by have := hz.2.2.2.2.2.2.2; omega)
  have hbN : 4 ≤ z.b.toNat := by omega
  have hbN' : z.b.toNat ≤ 8 := by omega
  have hcN : z.c.toNat < 165 := by omega
  have hfN : z.f.toNat < 182 := by omega
  have hq : q2 z=4 ∨ q2 z= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.1.2)
  have hdiv : (3*z.f+4*z.c-q2 z)/z.b=z.e := by
    have heq : 3*z.f+4*z.c-q2 z=z.b*z.e := by dsimp [q2]; rw [ha,hd]; ring
    rw [heq]
    exact Int.mul_ediv_cancel_left _ (by omega)
  have hzslice : isSolution ⟨3,z.b,z.c,4,z.e,z.f⟩ := by
    have heq : z=⟨3,z.b,z.c,4,z.e,z.f⟩ := by ext <;> simp [ha,hd]
    exact heq ▸ hz.1
  have hconic : binaryConic z.b z.c z.f (q2 z)=0 := by
    have h := binaryConic_solution z.b z.c z.e z.f hzslice
    simpa only [q2,ha,hd] using h
  rcases hq with hq|hq
  · rw [hq] at hdiv hconic
    have heq : candidate z.b.toNat z.c.toNat z.f.toNat true=z := by
      ext <;> simp only [candidate,ite_true,hcb,hcc,hcf,hdiv,ha,hd]
    have h := encoded_census hchecks _ _ _ true hbN hbN' hcN hfN
      (heq.symm ▸ hz) (heq.symm ▸ hone)
      (by simpa only [ite_true,hcb,hcc,hcf] using hconic)
    simpa only [heq] using h
  · rw [hq] at hdiv hconic
    have heq : candidate z.b.toNat z.c.toNat z.f.toNat false=z := by
      ext <;> simp only [candidate,Bool.false_eq_true,ite_false,hcb,hcc,hcf,hdiv,ha,hd]
    have h := encoded_census hchecks _ _ _ false hbN hbN' hcN hfN
      (heq.symm ▸ hz) (heq.symm ▸ hone)
      (by simpa only [Bool.false_eq_true,ite_false,hcb,hcc,hcf] using hconic)
    simpa only [heq] using h

theorem shortTerminal_oneStepCheck (z : Six) (h : ShortTerminal z 2) : oneStepCheck z=true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply decide_eq_true
  have hm : [g] ∈ braidWords 2 :=
    (mem_braidWords_iff 2 [g]).mpr ⟨by simp,by simpa using hg⟩
  simpa only [applyWord] using h [g] hm

theorem extra_short_descent : l1 (applyWord extra [.m2,.m1]) < l1 extra := by decide +kernel

end SerreMarkov.PositiveThreeFour
