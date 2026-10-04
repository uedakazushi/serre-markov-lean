import SerreMarkov.DegenerateNormalForm
import SerreMarkov.Normalize
import SerreMarkov.MarkovDescent

/-! # Direct Markov reduction for degenerate Serre matrices

The cofactor reduction turns the degenerate classification into the integral
Cayley cubic `a²+b²+d²-abd=4`. Restricted braid moves and even sign changes
preserve the displayed three-parameter matrix exactly.
-/

namespace SerreMarkov

def MarkovFour (a b d : ℤ) : Prop := a^2+b^2+d^2-a*b*d=4

theorem reducedDegenerate_q2 (a b d : ℤ) :
    q2 (reducedDegenerate a b d)=-(a^2+b^2+d^2-a*b*d) := by
  simp [q2,reducedDegenerate]
  ring

theorem reducedDegenerate_q1 (a b d : ℤ) :
    q1 (reducedDegenerate a b d)=2*(a^2+b^2+d^2-a*b*d) := by
  simp [q1,reducedDegenerate]
  ring

theorem reducedDegenerate_mutation1 (a b d : ℤ) :
    mu1 (reducedDegenerate a b d)=reducedDegenerate a (a*b-d) b := by
  ext <;> simp [mu1,reducedDegenerate]
  ring

theorem reducedDegenerate_mutation2 (a b d : ℤ) :
    mu2 (reducedDegenerate a b d)=reducedDegenerate (a*d-b) a d := by
  ext <;> simp [mu2,reducedDegenerate]
  ring

theorem reducedDegenerate_cycle (a b d : ℤ) :
    applyWord (reducedDegenerate a b d) [.m1,.m2]=reducedDegenerate d a b := by
  ext <;> simp [applyWord,step,mu1,mu2,reducedDegenerate] <;> ring

theorem reducedDegenerate_flipad (a b d : ℤ) :
    applyWord (reducedDegenerate a b d) [.s2,.s4]=reducedDegenerate (-a) b (-d) := by
  ext <;> simp [applyWord,step,eps2,eps4,reducedDegenerate]

theorem reducedDegenerate_flipbd (a b d : ℤ) :
    applyWord (reducedDegenerate a b d) [.s3,.s4]=reducedDegenerate a (-b) (-d) := by
  ext <;> simp [applyWord,step,eps3,eps4,reducedDegenerate]
  ring

theorem reducedDegenerate_cycle_reachable (a b d : ℤ) :
    Reachable (reducedDegenerate a b d) (reducedDegenerate d a b) :=
  ⟨[.m1,.m2],reducedDegenerate_cycle a b d⟩

theorem reducedDegenerate_cycle_twice_reachable (a b d : ℤ) :
    Reachable (reducedDegenerate a b d) (reducedDegenerate b d a) :=
  reachable_trans (reducedDegenerate_cycle_reachable a b d)
    (reducedDegenerate_cycle_reachable d a b)

theorem reducedDegenerate_flipad_reachable (a b d : ℤ) :
    Reachable (reducedDegenerate a b d) (reducedDegenerate (-a) b (-d)) :=
  ⟨[.s2,.s4],reducedDegenerate_flipad a b d⟩

theorem reducedDegenerate_flipbd_reachable (a b d : ℤ) :
    Reachable (reducedDegenerate a b d) (reducedDegenerate a (-b) (-d)) :=
  ⟨[.s3,.s4],reducedDegenerate_flipbd a b d⟩

theorem reducedDegenerate_at_two (a b : ℤ) (h : MarkovFour a b 2) :
    ∃ k : ℤ, 0≤k ∧ Reachable (reducedDegenerate a b 2) (family k (-k)) := by
  have hab : a=b := by
    dsimp [MarkovFour] at h
    nlinarith [sq_nonneg (a-b)]
  subst b
  have heq : reducedDegenerate a a 2=family (-a) a := by
    ext <;> simp [reducedDegenerate,family]
    ring
  rw [heq]
  exact family_normalize_degenerate (-a) a (by omega)

theorem reducedDegenerate_entry_two (a b d : ℤ) (h : MarkovFour a b d)
    (hentry : a=2 ∨ a= -2 ∨ b=2 ∨ b= -2 ∨ d=2 ∨ d= -2) :
    ∃ k : ℤ, 0≤k ∧ Reachable (reducedDegenerate a b d) (family k (-k)) := by
  dsimp [MarkovFour] at h
  rcases hentry with ha | ha | hb | hb | hd | hd
  · subst a
    obtain ⟨k,hk,hr⟩ := reducedDegenerate_at_two b d (by dsimp [MarkovFour]; nlinarith [h])
    exact ⟨k,hk,reachable_trans (reducedDegenerate_cycle_twice_reachable 2 b d) hr⟩
  · subst a
    obtain ⟨k,hk,hr⟩ := reducedDegenerate_at_two b (-d) (by dsimp [MarkovFour]; nlinarith [h])
    exact ⟨k,hk,reachable_trans (reducedDegenerate_flipad_reachable (-2) b d)
      (reachable_trans (reducedDegenerate_cycle_twice_reachable 2 b (-d)) hr)⟩
  · subst b
    obtain ⟨k,hk,hr⟩ := reducedDegenerate_at_two d a (by dsimp [MarkovFour]; nlinarith [h])
    exact ⟨k,hk,reachable_trans (reducedDegenerate_cycle_reachable a 2 d) hr⟩
  · subst b
    obtain ⟨k,hk,hr⟩ := reducedDegenerate_at_two (-d) a (by dsimp [MarkovFour]; nlinarith [h])
    exact ⟨k,hk,reachable_trans (reducedDegenerate_flipbd_reachable a (-2) d)
      (reachable_trans (reducedDegenerate_cycle_reachable a 2 (-d)) hr)⟩
  · subst d
    exact reducedDegenerate_at_two a b h
  · subst d
    obtain ⟨k,hk,hr⟩ := reducedDegenerate_at_two a (-b) (by dsimp [MarkovFour]; nlinarith [h])
    exact ⟨k,hk,reachable_trans (reducedDegenerate_flipbd_reachable a b (-2)) hr⟩

def markovSize (a b d : ℤ) : ℕ := a.natAbs+b.natAbs+d.natAbs

theorem reducedDegenerate_normalize_signs (a b d : ℤ) (h : MarkovFour a b d) :
    ∃ a' b' d' : ℤ, 0≤a' ∧ 0≤b' ∧ MarkovFour a' b' d' ∧
      markovSize a' b' d'=markovSize a b d ∧
      Reachable (reducedDegenerate a b d) (reducedDegenerate a' b' d') := by
  by_cases ha : 0≤a <;> by_cases hb : 0≤b
  · exact ⟨a,b,d,ha,hb,h,rfl,reachable_refl _⟩
  · refine ⟨a,-b,-d,ha,by omega,?_,?_,reducedDegenerate_flipbd_reachable a b d⟩
    · dsimp [MarkovFour] at *; nlinarith [h]
    · simp [markovSize,Int.natAbs_neg]
  · refine ⟨-a,b,-d,by omega,hb,?_,?_,reducedDegenerate_flipad_reachable a b d⟩
    · dsimp [MarkovFour] at *; nlinarith [h]
    · simp [markovSize,Int.natAbs_neg]
  · refine ⟨-a,-b,d,by omega,by omega,?_,?_,?_⟩
    · dsimp [MarkovFour] at *; nlinarith [h]
    · simp [markovSize,Int.natAbs_neg]
    · simpa using reachable_trans (reducedDegenerate_flipad_reachable a b d)
        (reducedDegenerate_flipbd_reachable (-a) b (-d))

theorem reducedDegenerate_rotate_max (a b d : ℤ) (h : MarkovFour a b d)
    (ha : 3≤a) (hb : 3≤b) (hd : 3≤d) :
    ∃ a' b' d' : ℤ, 3≤a' ∧ 3≤b' ∧ 3≤d' ∧ MarkovFour a' b' d' ∧
      (a'≤d' ∧ b'≤d') ∧ markovSize a' b' d'=markovSize a b d ∧
      Reachable (reducedDegenerate a b d) (reducedDegenerate a' b' d') := by
  by_cases had : a≤d
  · by_cases hbd : b≤d
    · exact ⟨a,b,d,ha,hb,hd,h,⟨had,hbd⟩,rfl,reachable_refl _⟩
    · refine ⟨d,a,b,hd,ha,hb,?_,⟨by omega,by omega⟩,?_,
        reducedDegenerate_cycle_reachable a b d⟩
      · dsimp [MarkovFour] at *; nlinarith [h]
      · dsimp [markovSize]; omega
  · by_cases hba : b≤a
    · refine ⟨b,d,a,hb,hd,ha,?_,⟨hba,by omega⟩,?_,
        reducedDegenerate_cycle_twice_reachable a b d⟩
      · dsimp [MarkovFour] at *; nlinarith [h]
      · dsimp [markovSize]; omega
    · refine ⟨d,a,b,hd,ha,hb,?_,⟨by omega,by omega⟩,?_,
        reducedDegenerate_cycle_reachable a b d⟩
      · dsimp [MarkovFour] at *; nlinarith [h]
      · dsimp [markovSize]; omega

/-- Terminating integral descent gives the entire degenerate parameter family. -/
theorem reducedDegenerate_reachable_family (a b d : ℤ) (h : MarkovFour a b d) :
    ∃ k : ℤ, 0≤k ∧ Reachable (reducedDegenerate a b d) (family k (-k)) := by
  have hmain : ∀ n : ℕ, ∀ a b d : ℤ, MarkovFour a b d → markovSize a b d=n →
      ∃ k : ℤ, 0≤k ∧ Reachable (reducedDegenerate a b d) (family k (-k)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b d hM hsize
      obtain ⟨a',b',d',ha,hb,hM',hsize',hreach⟩ :=
        reducedDegenerate_normalize_signs a b d hM
      have hn : markovSize a' b' d'=n := hsize'.trans hsize
      rcases markov_sign_normalized_cases a' b' d' ha hb hM' with
        hentry | hsmall | hlarge
      · obtain ⟨k,hk,hkreach⟩ := reducedDegenerate_entry_two a' b' d' hM' hentry
        exact ⟨k,hk,reachable_trans hreach hkreach⟩
      · rcases hsmall with ⟨rfl,rfl,rfl⟩
        have hm : Reachable (reducedDegenerate 1 1 (-1)) (reducedDegenerate 1 2 1) :=
          ⟨[.m1],reducedDegenerate_mutation1 1 1 (-1)⟩
        obtain ⟨k,hk,hkreach⟩ := reducedDegenerate_entry_two 1 2 1 (by norm_num [MarkovFour])
          (Or.inr (Or.inr (Or.inl rfl)))
        exact ⟨k,hk,reachable_trans hreach (reachable_trans hm hkreach)⟩
      · obtain ⟨ha3,hb3,hd3⟩ := hlarge
        obtain ⟨a0,b0,d0,ha0,hb0,hd0,hM0,hmax,hsize0,hrot⟩ :=
          reducedDegenerate_rotate_max a' b' d' hM' ha3 hb3 hd3
        have hn0 : markovSize a0 b0 d0=n := hsize0.trans hn
        obtain ⟨hpos,hdrop⟩ := markov_positive_descent a0 b0 d0 ha0 hb0 hd0 hM0 hmax
        have hnew : MarkovFour a0 (a0*b0-d0) b0 := by
          dsimp [MarkovFour] at *
          have heq : a0^2+(a0*b0-d0)^2+b0^2-a0*(a0*b0-d0)*b0 =
              a0^2+b0^2+d0^2-a0*b0*d0 := by ring
          exact heq.trans hM0
        have hsizeNew : markovSize a0 (a0*b0-d0) b0<n := by
          have haabs := Int.natAbs_of_nonneg (by omega : 0≤a0)
          have hbabs := Int.natAbs_of_nonneg (by omega : 0≤b0)
          have hdabs := Int.natAbs_of_nonneg (by omega : 0≤d0)
          have habs := Int.natAbs_of_nonneg (by omega : 0≤a0*b0-d0)
          dsimp [markovSize] at *
          omega
        obtain ⟨k,hk,hkreach⟩ := ih (markovSize a0 (a0*b0-d0) b0) hsizeNew
          a0 (a0*b0-d0) b0 hnew rfl
        have hmu : Reachable (reducedDegenerate a0 b0 d0)
            (reducedDegenerate a0 (a0*b0-d0) b0) :=
          ⟨[.m1],reducedDegenerate_mutation1 a0 b0 d0⟩
        exact ⟨k,hk,reachable_trans hreach
          (reachable_trans hrot (reachable_trans hmu hkreach))⟩
  exact hmain (markovSize a b d) a b d h rfl

end SerreMarkov
