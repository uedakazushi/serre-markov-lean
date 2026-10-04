import SerreMarkov.Mutations

/-! An arithmetic descent showing that the zero-unit conic has no integer
points when its third edge is at least three. -/

namespace SerreMarkov.ZeroUnitConicImpossible

def conic (d c e : ℤ) : ℤ :=
  c^2 + e^2 + (d^2-1)*c*e - 4*d*(c+e) + d^2 + 9

theorem conic_swap (d c e : ℤ) : conic d c e = conic d e c := by
  dsimp [conic]; ring

theorem conic_vieta (d c e : ℤ) :
    conic d (4*d-(d^2-1)*e-c) e = conic d c e := by
  dsimp [conic]; ring

private theorem positive_shift (D C E : ℤ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hE : 0 ≤ E) :
    0 < conic (D+4) (C+1) (E+1) := by
  dsimp [conic]; ring_nf; positivity

private theorem negative_shift (D C E : ℤ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hE : 0 ≤ E) :
    0 < conic (D+3) (-(C+1)) (-(E+1)) := by
  dsimp [conic]; ring_nf; positivity

theorem conic_positive_positive (d c e : ℤ)
    (hd : 3 ≤ d) (hc : 1 ≤ c) (he : 1 ≤ e) : 0 < conic d c e := by
  by_cases hd3 : d=3
  · rw [hd3]
    have h : conic 3 c e =
        (c-2)^2+(e-2)^2+8*(c-1)*(e-1)+2 := by dsimp [conic]; ring
    rw [h]
    have hp := mul_nonneg (show 0 ≤ c-1 by omega) (show 0 ≤ e-1 by omega)
    nlinarith [sq_nonneg (c-2),sq_nonneg (e-2)]
  · have h := positive_shift (d-4) (c-1) (e-1) (by omega) (by omega) (by omega)
    convert h using 1 <;> dsimp [conic] <;> ring

theorem conic_negative_negative (d c e : ℤ)
    (hd : 3 ≤ d) (hc : c ≤ -1) (he : e ≤ -1) : 0 < conic d c e := by
  have h := negative_shift (d-3) (-c-1) (-e-1) (by omega) (by omega) (by omega)
  convert h using 1 <;> dsimp [conic] <;> ring

private theorem zero_mod27 :
    ∀ c d : ZMod 27, c^2-4*c*d+d^2+9 ≠ 0 := by decide

theorem conic_zero (d c : ℤ) : conic d c 0 ≠ 0 := by
  intro h
  have hz : (c : ZMod 27)^2-4*(c : ZMod 27)*(d : ZMod 27)+(d : ZMod 27)^2+9=0 := by
    have h' := congrArg (fun n : ℤ => (n : ZMod 27)) h
    simpa [conic,mul_comm,mul_left_comm,mul_assoc] using h'
  exact zero_mod27 (c : ZMod 27) (d : ZMod 27) hz

private theorem root_factor_bound (P B : ℤ) (hP : 1 ≤ P) (hB : -4 ≤ B)
    (h : P^2-B*P+B+11=0) : B ≤ 15 ∧ P ≤ 13 := by
  let Q := B-P
  have hpq : P*Q=B+11 := by dsimp [Q]; nlinarith
  have hQ : 1 ≤ Q := by
    have hp : 0 < P := by omega
    have hprod : 0 < P*Q := by omega
    have hq := (mul_pos_iff.mp hprod)
    rcases hq with hq | hq <;> omega
  have hfac : (P-1)*(Q-1)=12 := by dsimp [Q]; nlinarith
  have hP2 : 2 ≤ P := by
    by_contra hb
    have hP1 : P=1 := by omega
    rw [hP1] at hfac
    norm_num at hfac
  have hQ2 : 2 ≤ Q := by
    by_contra hb
    have hQ1 : Q=1 := by omega
    rw [hQ1] at hfac
    norm_num at hfac
  have hp := mul_nonneg (show 0 ≤ P-2 by omega) (show 0 ≤ Q-2 by omega)
  have hsum : P+Q ≤ 15 := by nlinarith
  dsimp [Q] at hsum hQ2
  omega

theorem conic_negative_one (d P : ℤ) (hd : 3 ≤ d) (hP : 1 ≤ P) :
    conic d P (-1) ≠ 0 := by
  intro h
  have hf : P^2-(d^2+4*d-1)*P+(d^2+4*d-1)+11=0 := by
    dsimp [conic] at h
    nlinarith
  have hB : 20 ≤ d^2+4*d-1 := by nlinarith [sq_nonneg (d-3)]
  obtain ⟨hb,_⟩ := root_factor_bound P (d^2+4*d-1) hP (by omega) hf
  omega

theorem conic_positive_one (d N : ℤ) (hd : 3 ≤ d) (hN : 1 ≤ N) :
    conic d 1 (-N) ≠ 0 := by
  intro h
  have hf : N^2-(d^2-4*d-1)*N+(d^2-4*d-1)+11=0 := by
    dsimp [conic] at h
    nlinarith
  have hB : -4 ≤ d^2-4*d-1 := by
    nlinarith [mul_nonneg (show 0 ≤ d-3 by omega) (show 0 ≤ d-1 by omega)]
  obtain ⟨hb,hn⟩ := root_factor_bound N (d^2-4*d-1) hN hB hf
  have hd6 : d ≤ 6 := by
    by_contra hh
    have hp := mul_nonneg (show 0 ≤ d-7 by omega) (show 0 ≤ d+3 by omega)
    nlinarith
  interval_cases d <;> interval_cases N <;> norm_num [conic] at h

private theorem diagonal_shift (D T : ℤ) (hD : 0 ≤ D) (hT : 0 ≤ T) :
    conic (D+3) (T+2) (-(T+2)) < 0 := by
  apply neg_pos.mp
  dsimp [conic]; ring_nf; positivity

theorem conic_mixed_diagonal (d P : ℤ) (hd : 3 ≤ d) (hP : 2 ≤ P) :
    conic d P (-P) < 0 := by
  have h := diagonal_shift (d-3) (P-2) (by omega) (by omega)
  convert h using 1 <;> dsimp [conic] <;> ring

private theorem mixed_positive_descent (d P N : ℤ) (hd : 3 ≤ d)
    (hP : 2 ≤ P) (hN : 2 ≤ N) (hmax : N ≤ P)
    (h : conic d P (-N)=0) :
    ∃ P' : ℤ, 2 ≤ P' ∧ P' < N ∧ conic d P' (-N)=0 := by
  let P' := 4*d+(d^2-1)*N-P
  have hroot : conic d P' (-N)=0 := by
    have heq : P'=4*d-(d^2-1)*(-N)-P := by dsimp [P']; ring
    rw [heq]
    exact (conic_vieta d P (-N)).trans h
  have hprod : P*P'=N^2+4*d*N+d^2+9 := by
    dsimp [P',conic] at *
    nlinarith
  have hP' : 1 ≤ P' := by
    have hpos : 0 < P*P' := by
      rw [hprod]
      have hp := mul_nonneg (show 0 ≤ d by omega) (show 0 ≤ N by omega)
      nlinarith [sq_nonneg d,sq_nonneg N]
    rcases mul_pos_iff.mp hpos with hh | hh <;> omega
  have hP'2 : 2 ≤ P' := by
    by_contra hb
    have h1 : P'=1 := by omega
    rw [h1] at hroot
    exact conic_positive_one d N hd (by omega) hroot
  have hid : (P-N)*(P'-N)=conic d N (-N) := by
    dsimp [P',conic] at *
    nlinarith
  have hdiag := conic_mixed_diagonal d N hd hN
  have hsmall : P' < N := by
    by_contra hb
    have hh := mul_nonneg (show 0 ≤ P-N by omega) (show 0 ≤ P'-N by omega)
    nlinarith
  exact ⟨P',hP'2,hsmall,hroot⟩

private theorem mixed_negative_descent (d P N : ℤ) (hd : 3 ≤ d)
    (hP : 2 ≤ P) (hN : 2 ≤ N) (hmax : P ≤ N)
    (h : conic d P (-N)=0) :
    ∃ N' : ℤ, 2 ≤ N' ∧ N' < P ∧ conic d P (-N')=0 := by
  let N' := (d^2-1)*P-4*d-N
  have hroot : conic d P (-N')=0 := by
    have heq : -N'=4*d-(d^2-1)*P-(-N) := by dsimp [N']; ring
    rw [heq,conic_swap]
    exact (conic_vieta d (-N) P).trans ((conic_swap d P (-N)).symm.trans h)
  have hN' : 1 ≤ N' := by
    by_contra hb
    by_cases h0 : N'=0
    · rw [h0] at hroot
      simp only [neg_zero] at hroot
      exact conic_zero d P hroot
    · have hp := conic_positive_positive d P (-N') hd (by omega) (by omega)
      omega
  have hN'2 : 2 ≤ N' := by
    by_contra hb
    have h1 : N'=1 := by omega
    rw [h1] at hroot
    exact conic_negative_one d P hd (by omega) hroot
  have hid : (N-P)*(N'-P)=conic d P (-P) := by
    dsimp [N',conic] at *
    nlinarith
  have hdiag := conic_mixed_diagonal d P hd hP
  have hsmall : N' < P := by
    by_contra hb
    have hp := mul_nonneg (show 0 ≤ N-P by omega) (show 0 ≤ N'-P by omega)
    nlinarith
  exact ⟨N',hN'2,hsmall,hroot⟩

theorem conic_positive_negative (d P N : ℤ) (hd : 3 ≤ d)
    (hP : 1 ≤ P) (hN : 1 ≤ N) : conic d P (-N) ≠ 0 := by
  suffices hh : ∀ n : ℕ, ∀ P N : ℤ, P.natAbs+N.natAbs=n →
      1 ≤ P → 1 ≤ N → conic d P (-N) ≠ 0 from
    hh (P.natAbs+N.natAbs) P N rfl hP hN
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P N hsize hP hN hroot
    have hP2 : 2 ≤ P := by
      by_contra hb
      have h1 : P=1 := by omega
      rw [h1] at hroot
      exact conic_positive_one d N hd hN hroot
    have hN2 : 2 ≤ N := by
      by_contra hb
      have h1 : N=1 := by omega
      rw [h1] at hroot
      exact conic_negative_one d P hd hP hroot
    by_cases hmax : N ≤ P
    · obtain ⟨P',hp',hsmall,hnew⟩ := mixed_positive_descent d P N hd hP2 hN2 hmax hroot
      have habs : P'.natAbs < P.natAbs :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
      exact ih (P'.natAbs+N.natAbs) (by omega) P' N rfl (by omega) hN hnew
    · obtain ⟨N',hn',hsmall,hnew⟩ := mixed_negative_descent d P N hd hP2 hN2 (by omega) hroot
      have habs : N'.natAbs < N.natAbs :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
      exact ih (P.natAbs+N'.natAbs) (by omega) P N' rfl hP (by omega) hnew

/-- The integer zero-unit conic has no roots once the third edge is at least three. -/
theorem conic_no_integer_root (d c e : ℤ) (hd : 3 ≤ d)
    (h : conic d c e=0) : False := by
  by_cases hc0 : c=0
  · rw [hc0,conic_swap] at h
    exact conic_zero d e h
  by_cases he0 : e=0
  · rw [he0] at h
    exact conic_zero d c h
  by_cases hc : 0 < c
  · by_cases he : 0 < e
    · have hp := conic_positive_positive d c e hd (by omega) (by omega)
      omega
    · have hh := conic_positive_negative d c (-e) hd (by omega) (by omega)
      exact hh (by simpa only [neg_neg] using h)
  · by_cases he : 0 < e
    · have hh := conic_positive_negative d e (-c) hd (by omega) (by omega)
      apply hh
      simpa only [neg_neg] using (conic_swap d c e).symm.trans h
    · have hp := conic_negative_negative d c e hd (by omega) (by omega)
      omega

end SerreMarkov.ZeroUnitConicImpossible
